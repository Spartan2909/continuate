use crate::low_level_ir::BinaryOp;
use crate::low_level_ir::Block;
use crate::low_level_ir::BlockId;
use crate::low_level_ir::Expr;
use crate::low_level_ir::FuncRef;
use crate::low_level_ir::Function;
use crate::low_level_ir::Ident;
use crate::low_level_ir::Literal;
use crate::low_level_ir::Program;
use crate::low_level_ir::Type;
use crate::low_level_ir::TypeConstructor;
use crate::low_level_ir::UnaryOp;
use crate::low_level_ir::UserDefinedType;

use std::cell::RefCell;
use std::collections::HashMap;
use std::iter;
use std::mem;
use std::ops;
use std::rc::Rc;

use continuate_arena::Arena;

#[derive(Debug)]
pub enum Value<'arena> {
    Int(i64),
    Float(f64),
    String(String),
    Array(RefCell<Vec<ValueRef<'arena>>>),
    Tuple(RefCell<Vec<ValueRef<'arena>>>),
    Function(FuncRef),
    ContinuedFunction(ValueRef<'arena>, HashMap<Ident, ValueRef<'arena>>),
    Closure {
        func_ref: FuncRef,
        environment: SharedEnvironment<'arena>,
    },
    UserDefined {
        discriminant: Option<usize>,
        fields: RefCell<Vec<ValueRef<'arena>>>,
    },
}

impl<'arena> Value<'arena> {
    fn discriminant(&self) -> i64 {
        match self {
            Value::UserDefined {
                discriminant,
                fields: _,
            } => discriminant.unwrap_or(0) as i64,
            _ => 0,
        }
    }

    fn get(&self, index: usize) -> Option<ValueRef<'arena>> {
        match self {
            Value::Array(values)
            | Value::Tuple(values)
            | Value::UserDefined {
                discriminant: _,
                fields: values,
            } => values.borrow().get(index).copied(),
            _ => None,
        }
    }

    fn set(&self, index: usize, value: ValueRef<'arena>) {
        match self {
            Value::Array(values)
            | Value::Tuple(values)
            | Value::UserDefined {
                discriminant: _,
                fields: values,
            } => {
                *values.borrow_mut().get_mut(index).unwrap() = value;
            }
            _ => unreachable!(),
        }
    }

    const fn as_int(&self) -> Option<i64> {
        if let Value::Int(n) = self {
            Some(*n)
        } else {
            None
        }
    }

    const fn as_fn(&self) -> Option<FuncRef> {
        if let Value::Function(fn_ref) = self {
            Some(*fn_ref)
        } else {
            None
        }
    }

    fn call(
        &self,
        params: Vec<ValueRef<'arena>>,
        mut bound_params: HashMap<Ident, ValueRef<'arena>>,
        executor: &Executor<'arena>,
    ) -> ControlFlow<ValueRef<'arena>> {
        match self {
            Value::Function(func_ref) => {
                let function = *executor.program.functions.get(func_ref).unwrap();
                bound_params.extend(function.params.keys().copied().zip(params));
                executor.function(function, bound_params, None)
            }
            Value::ContinuedFunction(callee, continuations) => {
                bound_params.extend(continuations);
                callee.call(params, bound_params, executor)
            }
            Value::Closure { func_ref, environment } => {
                let function = *executor.program.functions.get(func_ref).unwrap();
                bound_params.extend(function.params.keys().copied().zip(params));
                executor.function(function, bound_params, Some(Rc::clone(environment)))
            }
            _ => unreachable!(),
        }
    }

    fn apply_continuations<I: IntoIterator<Item = (Ident, ValueRef<'arena>)>>(
        &'arena self,
        continuations: I,
    ) -> Value<'arena> {
        match self {
            Value::Function(_) | Value::Closure { .. } => {
                Value::ContinuedFunction(self, continuations.into_iter().collect())
            }
            Value::ContinuedFunction(callee, existing_continuations) => {
                let mut new_continuations = existing_continuations.clone();
                new_continuations.extend(continuations);
                Value::ContinuedFunction(callee, new_continuations)
            }
            _ => unreachable!(),
        }
    }

    const fn array(values: Vec<ValueRef<'arena>>) -> Value {
        Value::Array(RefCell::new(values))
    }

    const fn tuple(values: Vec<ValueRef<'arena>>) -> Value {
        Value::Tuple(RefCell::new(values))
    }

    const fn user_defined(discriminant: Option<usize>, fields: Vec<ValueRef<'arena>>) -> Value {
        Value::UserDefined {
            discriminant,
            fields: RefCell::new(fields),
        }
    }
}

impl<'arena> ops::Add for &Value<'arena> {
    type Output = Option<Value<'arena>>;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 + n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 + n2)),
            (Value::String(s1), Value::String(s2)) => {
                let mut result = String::with_capacity(s1.len() + s2.len());
                result.push_str(s1);
                result.push_str(s2);
                Some(Value::String(result))
            }
            _ => None,
        }
    }
}

impl<'arena> ops::Sub for &Value<'arena> {
    type Output = Option<Value<'arena>>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 - n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 - n2)),
            _ => None,
        }
    }
}

impl<'arena> ops::Mul for &Value<'arena> {
    type Output = Option<Value<'arena>>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 * n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 * n2)),
            _ => None,
        }
    }
}

impl<'arena> ops::Div for &Value<'arena> {
    type Output = Option<Value<'arena>>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 / n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 / n2)),
            _ => None,
        }
    }
}

impl<'arena> ops::Rem for &Value<'arena> {
    type Output = Option<Value<'arena>>;

    fn rem(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 % n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 % n2)),
            _ => None,
        }
    }
}

impl<'arena> From<Literal> for Value<'arena> {
    fn from(value: Literal) -> Self {
        match value {
            Literal::Int(n) => Value::Int(n),
            Literal::Float(n) => Value::Float(n),
            Literal::String(s) => Value::String(s),
        }
    }
}

type ValueRef<'arena> = &'arena Value<'arena>;

#[derive(Debug)]
enum ControlFlow<T> {
    Goto(BlockId),
    Terminate(i64),
    Value(T),
}

macro_rules! value {
    ($ctrl:expr) => {
        match ($ctrl) {
            ControlFlow::Value(value) => value,
            ctrl => return ctrl.try_cast().unwrap(),
        }
    };
}

impl<T> ControlFlow<T> {
    fn unwrap_termination(self) -> i64 {
        match self {
            ControlFlow::Terminate(n) => n,
            _ => unreachable!(),
        }
    }

    fn try_cast<U>(self) -> Option<ControlFlow<U>> {
        match self {
            ControlFlow::Goto(id) => Some(ControlFlow::Goto(id)),
            ControlFlow::Terminate(n) => Some(ControlFlow::Terminate(n)),
            ControlFlow::Value(_) => None,
        }
    }
}

impl<'arena> ControlFlow<ValueRef<'arena>> {
    fn value(value: Value<'arena>, arena: &'arena Arena<'arena>) -> ControlFlow<ValueRef<'arena>> {
        ControlFlow::Value(arena.allocate(value))
    }
}

#[derive(Debug)]
pub struct Environment<'arena> {
    enclosing: Option<SharedEnvironment<'arena>>,
    values: HashMap<Ident, ValueRef<'arena>>,
}

impl<'arena> Environment<'arena> {
    fn new() -> Environment<'arena> {
        Environment {
            enclosing: None,
            values: HashMap::new(),
        }
    }

    fn get(&self, ident: Ident) -> Option<ValueRef<'arena>> {
        self.values
            .get(&ident)
            .copied()
            .or_else(|| self.enclosing.as_ref()?.borrow().get(ident))
    }

    fn set(&mut self, ident: Ident, value: ValueRef<'arena>) {
        if let Some(place) = self.values.get_mut(&ident) {
            *place = value;
        } else if let Some(enclosing) = &self.enclosing {
            enclosing.borrow_mut().set(ident, value);
        } else {
            panic!("set unassigned value")
        }
    }

    const fn from_map(map: HashMap<Ident, ValueRef<'arena>>) -> Environment<'arena> {
        Environment {
            enclosing: None,
            values: map,
        }
    }
}

type SharedEnvironment<'arena> = Rc<RefCell<Environment<'arena>>>;

struct Executor<'arena> {
    program: Program<'arena>,
    arena: &'arena Arena<'arena>,
    environment: SharedEnvironment<'arena>,
}

impl<'arena> Executor<'arena> {
    fn new(program: Program<'arena>, arena: &'arena Arena<'arena>) -> Executor<'arena> {
        Executor {
            program,
            arena,
            environment: Rc::new(RefCell::new(Environment::new())),
        }
    }

    fn expr_list(&self, exprs: &[&Expr<'arena>]) -> ControlFlow<Vec<ValueRef<'arena>>> {
        let mut values = Vec::with_capacity(exprs.len());
        for &expr in exprs {
            values.push(value!(self.expr(expr)));
        }
        ControlFlow::Value(values)
    }

    fn binary_op(
        &self,
        left: &Expr<'arena>,
        right: &Expr<'arena>,
        op: BinaryOp,
    ) -> ControlFlow<ValueRef<'arena>> {
        let left = value!(self.expr(left));
        let right = value!(self.expr(right));
        let result = match op {
            BinaryOp::Add => left + right,
            BinaryOp::Sub => left - right,
            BinaryOp::Mul => left * right,
            BinaryOp::Div => left / right,
            BinaryOp::Rem => left % right,
            BinaryOp::Eq
            | BinaryOp::Ne
            | BinaryOp::Lt
            | BinaryOp::Le
            | BinaryOp::Gt
            | BinaryOp::Ge => todo!(),
        };
        ControlFlow::value(result.unwrap(), self.arena)
    }

    fn closure(&self, func: &Expr<'arena>) -> ControlFlow<ValueRef<'arena>> {
        let func_ref = value!(self.expr(func)).as_fn().unwrap();
        let mut new_env = Environment::new();
        new_env.enclosing = Some(Rc::clone(&self.environment));
        let old_env = mem::replace(&mut *self.environment.borrow_mut(), new_env);
        ControlFlow::value(
            Value::Closure {
                func_ref,
                environment: Rc::new(RefCell::new(old_env)),
            },
            self.arena,
        )
    }

    fn expr(&self, expr: &Expr<'arena>) -> ControlFlow<ValueRef<'arena>> {
        match expr {
            Expr::Literal(lit) => ControlFlow::value(lit.clone().into(), self.arena),
            Expr::Ident(ident) => {
                ControlFlow::Value(self.environment.borrow().get(*ident).unwrap())
            }
            Expr::Function(func_ref) => ControlFlow::value(Value::Function(*func_ref), self.arena),
            Expr::Block(block) => {
                let (&last, block) = block.split_last().unwrap();
                for &expr in block {
                    value!(self.expr(expr));
                }
                self.expr(last)
            }
            Expr::Tuple(tuple) => {
                ControlFlow::value(Value::tuple(value!(self.expr_list(tuple))), self.arena)
            }
            Expr::Constructor {
                ty: _,
                index,
                fields,
            } => ControlFlow::value(
                Value::user_defined(*index, value!(self.expr_list(fields))),
                self.arena,
            ),
            Expr::Array(arr) => {
                ControlFlow::value(Value::array(value!(self.expr_list(arr))), self.arena)
            }
            Expr::Discriminant(expr) => ControlFlow::value(
                Value::Int(value!(self.expr(expr)).discriminant()),
                self.arena,
            ),
            Expr::Get(object, index) => {
                let object = value!(self.expr(object));
                ControlFlow::Value(object.get(*index).unwrap())
            }
            Expr::Set(object, index, value) => {
                let object = value!(self.expr(object));
                let value = value!(self.expr(value));
                object.set(*index, value);
                ControlFlow::Value(value)
            }
            Expr::Call(callee, params) => {
                let callee = value!(self.expr(callee));
                let params = value!(self.expr_list(params));
                callee.call(params, HashMap::new(), self)
            }
            Expr::ContApplication(func, continuations) => {
                let func = value!(self.expr(func));
                let mut evaluated_continuations = HashMap::with_capacity(continuations.len());
                for (index, continuation) in continuations {
                    evaluated_continuations.insert(*index, value!(self.expr(continuation)));
                }
                ControlFlow::value(
                    func.apply_continuations(evaluated_continuations),
                    self.arena,
                )
            }
            Expr::Unary(op, operand) => {
                let value = value!(self.expr(operand));
                match *op {
                    UnaryOp::Neg => {
                        ControlFlow::value(Value::Int(-value.as_int().unwrap()), self.arena)
                    }
                }
            }
            Expr::Binary(left, op, right) => self.binary_op(left, right, *op),
            Expr::Declare { ident, expr } => {
                let value = value!(self.expr(expr));
                self.environment.borrow_mut().values.insert(*ident, value);
                ControlFlow::Value(value)
            }
            Expr::Assign { ident, expr } => {
                let value = value!(self.expr(expr));
                self.environment.borrow_mut().set(*ident, value);
                ControlFlow::Value(value)
            }
            Expr::Switch {
                scrutinee,
                arms,
                otherwise,
            } => {
                let scrutinee = value!(self.expr(scrutinee)).as_int().unwrap();
                let block_id = arms.get(&scrutinee).copied().unwrap_or(*otherwise);
                ControlFlow::Goto(block_id)
            }
            Expr::Goto(block_id) => ControlFlow::Goto(*block_id),
            Expr::Closure { func } => {
                self.closure(func)
            }
            Expr::Terminate(exit_code) => {
                let exit_code = value!(self.expr(exit_code)).as_int().unwrap();
                ControlFlow::Terminate(exit_code)
            }
            Expr::Unreachable => unreachable!(),
        }
    }

    fn function(
        &self,
        function: &Function<'arena>,
        params: HashMap<Ident, ValueRef<'arena>>,
        enclosing_environment: Option<SharedEnvironment<'arena>>,
    ) -> ControlFlow<ValueRef<'arena>> {
        let mut env = self.environment.borrow_mut();
        *env = Environment::from_map(params);
        env.enclosing = enclosing_environment;
        drop(env);
        let mut block = function.blocks.get(&function.entry_point()).unwrap();
        loop {
            match self.expr(block.expr) {
                ControlFlow::Goto(block_id) => block = function.blocks.get(&block_id).unwrap(),
                ctrl => return ctrl,
            }
        }
    }

    fn run(self, termination_param: Ident, termination_fn: ValueRef<'arena>) -> i64 {
        let entry_point = self
            .program
            .functions
            .get(&self.program.entry_point())
            .unwrap();
        self.function(
            entry_point,
            iter::once((termination_param, termination_fn)).collect(),
            None,
        )
        .unwrap_termination()
    }
}

pub fn run<'arena>(
    program: Program<'arena>,
    termination_param: Ident,
    termination_fn: ValueRef<'arena>,
    arena: &'arena Arena<'arena>,
) -> i64 {
    Executor::new(program, arena).run(termination_param, termination_fn)
}

#[non_exhaustive]
pub struct StdLib<'arena> {
    pub ty_bool: &'arena Type<'arena>,
    pub ty_int: &'arena Type<'arena>,

    pub b_true: ValueRef<'arena>,
    pub b_false: ValueRef<'arena>,

    pub fn_termination: ValueRef<'arena>,
}

pub fn standard_library<'arena>(
    arena: &'arena Arena<'arena>,
    program: &mut Program<'arena>,
) -> StdLib<'arena> {
    let ty_bool = arena.allocate(UserDefinedType {
        constructor: TypeConstructor::Sum(vec![vec![], vec![]]),
    });
    let ty_bool = arena.allocate(Type::UserDefined(ty_bool));
    let ty_int = arena.allocate(Type::Int);

    let b_true = arena.allocate(Value::user_defined(Some(1), vec![]));
    let b_false = arena.allocate(Value::user_defined(Some(0), vec![]));

    let fn_termination = arena.allocate(Function::new());
    let param = fn_termination.ident();
    fn_termination.params.insert(param, ty_int);

    let exit_code = arena.allocate(Expr::Ident(param));
    let termiation_body = arena.allocate(Expr::Terminate(exit_code));

    let block = Block {
        expr: termiation_body,
    };
    let block_id = fn_termination.entry_point();
    fn_termination.blocks.insert(block_id, block);

    let fn_termination_ref = program.function();
    program.functions.insert(fn_termination_ref, fn_termination);

    let fn_termination = arena.allocate(Value::Function(fn_termination_ref));

    StdLib {
        ty_bool,
        ty_int,
        b_true,
        b_false,
        fn_termination,
    }
}
