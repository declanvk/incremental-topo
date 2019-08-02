extern crate failure;
extern crate incremental_topo;
extern crate ordered_float;

use failure::Fail;
use incremental_topo::{self as topo, IncrementalTopo};
use ordered_float::OrderedFloat;
use std::{
    collections::{HashMap, HashSet},
    fmt,
    rc::Rc,
};

type InnerValue = f64;
#[derive(Debug, Copy, Clone, PartialEq, PartialOrd, Ord, Eq, Hash)]
struct Value(OrderedFloat<InnerValue>);

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<topo::Error> for Error {
    fn from(src: topo::Error) -> Self {
        Error::Topo(src)
    }
}

impl From<InnerValue> for Value {
    fn from(src: InnerValue) -> Self {
        Value((src as InnerValue).into())
    }
}

impl From<f32> for Value {
    fn from(src: f32) -> Self {
        Value((src as InnerValue).into())
    }
}

impl From<i64> for Value {
    fn from(src: i64) -> Self {
        Value((src as InnerValue).into())
    }
}

impl From<i32> for Value {
    fn from(src: i32) -> Self {
        Value((src as InnerValue).into())
    }
}

impl From<u64> for Value {
    fn from(src: u64) -> Self {
        Value((src as InnerValue).into())
    }
}

impl From<u32> for Value {
    fn from(src: u32) -> Self {
        Value((src as InnerValue).into())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
struct Symbol(usize);

impl Default for Symbol {
    fn default() -> Self {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static SYMBOL_COUNT: AtomicUsize = AtomicUsize::new(0);

        Symbol(SYMBOL_COUNT.fetch_add(1, Ordering::Relaxed))
    }
}

#[derive(Debug, Clone, Default)]
struct Assignments {
    bindings: HashMap<Symbol, Rc<Expr>>,
    ordering: IncrementalTopo<Symbol>,
    values: HashMap<Symbol, Value>,
}

impl Assignments {
    fn add(&mut self, target: Symbol, expr: Rc<Expr>) -> Result<Value, Error> {
        if self.bindings.contains_key(&target) {
            return Err(Error::DuplicateBinding)?;
        }

        let free_vars = expr.find_free_vars();

        // Perform early check for recursive definition
        if free_vars.contains(&target) {
            return Err(Error::RecursiveDependence)?;
        }

        // Perform separate check before to reduce the number of rollback operations
        // that might occur.
        for var in &free_vars {
            if !self.bindings.contains_key(var) {
                return Err(Error::MissingBinding(*var))?;
            }
        }

        self.ordering.add_node(target);

        // List of symbols a dependence was successfully added to
        // If an error occurs, then all of these must be deleted
        let mut added_deps = Vec::<Symbol>::new();

        for var in free_vars.into_iter() {
            if let Err(err) = self.ordering.add_dependency(&var, &target) {
                for added in added_deps {
                    self.ordering.delete_dependency(&added, &target);
                }

                return Err(err)?;
            } else {
                added_deps.push(var);
            }
        }

        // If everything succeeded
        self.bindings.insert(target, expr);

        // Get just inserted expression
        let expr = self.bindings.get(&target).unwrap();

        // Because this was only just inserted, we don't need to run any descendants
        let value = expr.evaluate(&self.values)?;

        // Update the top expr's value
        self.values.insert(target, value);

        Ok(value)
    }

    fn update(&mut self, target: Symbol, new_expr: Rc<Expr>) -> Result<Value, Error> {
        let old_vars = if let Some(old_expr) = self.bindings.get(&target) {
            old_expr.find_free_vars()
        } else {
            return Err(Error::MissingBinding(target))?;
        };

        let new_vars = new_expr.find_free_vars();

        let vars_to_delete = old_vars.difference(&new_vars);
        let vars_to_add = new_vars.difference(&old_vars);

        // Perform check for existance before updating graph to reduce amount of
        // rollback that might occur.
        for var in vars_to_add.clone() {
            if !self.bindings.contains_key(var) {
                return Err(Error::MissingBinding(*var))?;
            }
        }

        for var in vars_to_delete {
            // This must succeed, deletion is trivial
            self.ordering.delete_dependency(var, &target);
        }

        let mut added_deps = Vec::new();
        for var in vars_to_add {
            if let Err(err) = self.ordering.add_dependency(var, &target) {
                // Undo those relations that were added
                for added in added_deps {
                    self.ordering.delete_dependency(&added, &target);
                }

                // Undo those relations that were deleted
                for deleted in old_vars.difference(&new_vars) {
                    // This must succeed?
                    self.ordering.add_dependency(deleted, &target)?;
                }

                return Err(err)?;
            } else {
                added_deps.push(*var);
            }
        }

        // If everything succeeded
        self.bindings.insert(target, new_expr);

        // Get just inserted expression
        let top_expr = self.bindings.get(&target).unwrap();

        // Because this was only just inserted, we don't need to run any descendants
        let top_value = top_expr.evaluate(&self.values)?;

        // Update the top expr's value
        self.values.insert(target, top_value);

        // Get all descendants of current target + target
        for descendant in self.ordering.descendants(&target)? {
            let descendant_expr = self.bindings.get(&descendant).unwrap();
            let new_value = descendant_expr.evaluate(&self.values)?;
            self.values.insert(*descendant, new_value).unwrap();
        }

        Ok(top_value)
    }

    fn read(&self, sym: &Symbol) -> Option<Value> {
        self.values.get(&sym).cloned()
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum BinopType {
    Add,
    Mult,
    Sub,
    Div,
}

impl BinopType {
    fn evaluate(&self, left: Value, right: Value) -> Value {
        use BinopType::*;
        let inner: InnerValue = match self {
            Add => (left.0).0 + (right.0).0,
            Mult => (left.0).0 * (right.0).0,
            Sub => (left.0).0 - (right.0).0,
            Div => (left.0).0 / (right.0).0,
        };

        inner.into()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Expr {
    Binop(BinopType, Rc<Expr>, Rc<Expr>), // a + b, a * b, a - b, a / b
    Unop(fn(Value) -> Value, Rc<Expr>),   // sin cos sqrt
    Lit(Value),                           // 20
    Var(Symbol),                          // a
}

impl Expr {
    // Constructors
    fn literal<V: Into<Value>>(v: V) -> (Symbol, Rc<Self>) {
        (Symbol::default(), v.into().into())
    }

    fn add<L: Into<Rc<Self>>, R: Into<Rc<Self>>>(left: L, right: R) -> (Symbol, Rc<Self>) {
        use BinopType::*;
        use Expr::*;

        (
            Symbol::default(),
            Rc::new(Binop(Add, left.into(), right.into())),
        )
    }

    #[allow(dead_code)]
    fn subtract<L: Into<Rc<Self>>, R: Into<Rc<Self>>>(left: L, right: R) -> (Symbol, Rc<Self>) {
        use BinopType::*;
        use Expr::*;

        (
            Symbol::default(),
            Rc::new(Binop(Sub, left.into(), right.into())),
        )
    }

    fn multiply<L: Into<Rc<Self>>, R: Into<Rc<Self>>>(left: L, right: R) -> (Symbol, Rc<Self>) {
        use BinopType::*;
        use Expr::*;

        (
            Symbol::default(),
            Rc::new(Binop(Mult, left.into(), right.into())),
        )
    }

    #[allow(dead_code)]
    fn divide<L: Into<Rc<Self>>, R: Into<Rc<Self>>>(left: L, right: R) -> (Symbol, Rc<Self>) {
        use BinopType::*;
        use Expr::*;

        (
            Symbol::default(),
            Rc::new(Binop(Div, left.into(), right.into())),
        )
    }

    fn unary_func<E: Into<Rc<Self>>>(func: fn(Value) -> Value, expr: E) -> (Symbol, Rc<Self>) {
        use Expr::*;

        (Symbol::default(), Rc::new(Unop(func, expr.into())))
    }

    fn find_free_vars(&self) -> HashSet<Symbol> {
        let mut free_vars = HashSet::new();
        let mut expr_stack = Vec::<&Expr>::new();

        expr_stack.push(self);

        // DFS search for variable nodes
        while let Some(next) = expr_stack.pop() {
            use Expr::*;
            match next {
                Binop(_, a, b) => {
                    expr_stack.push(a);
                    expr_stack.push(b);
                },
                Lit(_) => continue,
                Var(a) => {
                    free_vars.insert(*a);
                    continue;
                },
                Unop(_, e) => {
                    expr_stack.push(e);
                },
            }
        }

        free_vars
    }

    // TODO: Make into iterative function
    fn evaluate(&self, subs: &HashMap<Symbol, Value>) -> Result<Value, Error> {
        use Expr::*;

        match self {
            Binop(t, l, r) => {
                let left_value = l.evaluate(subs)?;
                let right_value = r.evaluate(subs)?;

                Ok(t.evaluate(left_value, right_value))
            },
            Lit(v) => Ok(*v),
            Var(sym) => subs.get(&sym).cloned().ok_or(Error::UnsubstitutedVar(*sym)),
            Unop(f, expr) => {
                let value = expr.evaluate(subs)?;

                Ok(f(value))
            },
        }
    }
}

impl From<Symbol> for Rc<Expr> {
    fn from(src: Symbol) -> Self {
        Rc::new(Expr::Var(src))
    }
}

impl From<Value> for Rc<Expr> {
    fn from(src: Value) -> Self {
        Rc::new(Expr::Lit(src))
    }
}

#[derive(Fail, Debug)]
enum Error {
    #[fail(display = "Binding already found in assignments")]
    DuplicateBinding,
    #[fail(display = "Binding not found for {:?}", _0)]
    MissingBinding(Symbol),
    #[fail(display = "Binding depends on its own value")]
    RecursiveDependence,
    #[fail(display = "Unable to substitute variable ({:?}) in evaluation", _0)]
    UnsubstitutedVar(Symbol),
    #[fail(display = "{}", _0)]
    Topo(#[cause] topo::Error),
}

fn main() {
    use BinopType::*;
    use Expr::*;

    // Create symbolic vectors
    let (x1_s, x1) = Expr::literal(1);
    let (x2_s, x2) = Expr::literal(2);
    let (x3_s, x3) = Expr::literal(3);

    let (y1_s, y1) = Expr::literal(4);
    let (y2_s, y2) = Expr::literal(5);
    let (y3_s, y3) = Expr::literal(6);

    // Create dependent expressions that compute the dot product
    let (v1_s, v1) = Expr::multiply(x1_s, y1_s);
    let (v2_s, v2) = Expr::multiply(x2_s, y2_s);
    let (v3_s, v3) = Expr::multiply(x3_s, y3_s);

    // The final dot product value
    let (v_s, v) = Expr::add(v1_s, Rc::new(Binop(Add, v2_s.into(), v3_s.into())));

    // Compute magnitude
    let (mx_s, mx) = Expr::unary_func(
        sqrt,
        Binop(
            Add,
            x1_s.into(),
            Rc::new(Binop(Add, x2_s.into(), x3_s.into())),
        ),
    );

    let (my_s, my) = Expr::unary_func(
        sqrt,
        Binop(
            Add,
            y1_s.into(),
            Rc::new(Binop(Add, y2_s.into(), y3_s.into())),
        ),
    );

    let mut asgns = Assignments::default();

    // Assign values to vector components
    asgns.add(x1_s, x1).unwrap();
    asgns.add(x2_s, x2).unwrap();
    asgns.add(x3_s, x3).unwrap();

    asgns.add(y1_s, y1).unwrap();
    asgns.add(y2_s, y2).unwrap();
    asgns.add(y3_s, y3).unwrap();

    // Setup pairwise multiplications
    asgns.add(v1_s, v1).unwrap();
    asgns.add(v2_s, v2).unwrap();
    asgns.add(v3_s, v3).unwrap();

    // Add final summation
    let dot_product = asgns.add(v_s, v).unwrap();

    // Add magnitudes
    let mag_x = asgns.add(mx_s, mx).unwrap();
    let mag_y = asgns.add(my_s, my).unwrap();

    println!(
        "The dot product of x = <{}, {}, {}> and y = <{}, {}, {}> is {}.\nThe magnitude of x is \
         {}, and y is {}.",
        1, 2, 3, 4, 5, 6, dot_product, mag_x, mag_y
    );

    // Change initial value
    asgns.update(x1_s, Value(10.0.into()).into()).unwrap();

    // Read new value of dot product
    let dot_product = asgns.read(&v_s).unwrap();

    // Read new magnitudes
    let mag_x = asgns.read(&mx_s).unwrap();
    let mag_y = asgns.read(&my_s).unwrap();

    println!(
        "Changing the value of x1 to {} changes the dot product to {}.\n Also changes the \
         magnitude of x to {}, and y to {}.",
        10, dot_product, mag_x, mag_y
    );
}

fn sqrt(v: Value) -> Value {
    v.0.sqrt().into()
}
