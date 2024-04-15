use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::UnaryOp;
use crate::low_level_ir::BlockId;
use crate::low_level_ir::Expr;
use crate::low_level_ir::Function;
use crate::low_level_ir::Program;

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter;
use std::mem;
use std::ops;
use std::rc::Rc;

use continuate_arena::Arena;
use continuate_arena::ArenaSafe;

#[derive(Debug, PartialEq)]
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
    pub(crate) fn discriminant(&self) -> i64 {
        match self {
            Value::UserDefined {
                discriminant,
                fields: _,
            } => discriminant.unwrap_or(0) as i64,
            _ => 0,
        }
    }

    /// ## Panics
    ///
    /// Panics if `self` is `Value::Closure`.
    pub(crate) fn clone_to<'a>(&self, arena: &'a Arena<'a>) -> Value<'a> {
        match *self {
            Value::Int(i) => Value::Int(i),
            Value::Float(f) => Value::Float(f),
            Value::String(ref s) => Value::String(s.clone()),
            Value::Array(ref array) => Value::Array(RefCell::new(
                array
                    .borrow()
                    .iter()
                    .map(|value| &*arena.allocate(value.clone_to(arena)))
                    .collect(),
            )),
            Value::Tuple(ref tuple) => Value::Tuple(RefCell::new(
                tuple
                    .borrow()
                    .iter()
                    .map(|value| &*arena.allocate(value.clone_to(arena)))
                    .collect(),
            )),
            Value::Function(func) => Value::Function(func),
            Value::ContinuedFunction(func, ref continuations) => Value::ContinuedFunction(
                arena.allocate(func.clone_to(arena)),
                continuations
                    .iter()
                    .map(|(&ident, value)| (ident, &*arena.allocate(value.clone_to(arena))))
                    .collect(),
            ),
            Value::Closure { .. } => unimplemented!(),
            Value::UserDefined {
                discriminant,
                ref fields,
            } => Value::UserDefined {
                discriminant,
                fields: RefCell::new(
                    fields
                        .borrow()
                        .iter()
                        .map(|value| &*arena.allocate(value.clone_to(arena)))
                        .collect(),
                ),
            },
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

    pub const fn as_int(&self) -> Option<i64> {
        if let Value::Int(n) = self {
            Some(*n)
        } else {
            None
        }
    }

    pub const fn as_fn(&self) -> Option<FuncRef> {
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
        executor: &mut Executor<'arena>,
    ) -> ControlFlow<Void> {
        match *self {
            Value::Function(func_ref) => {
                let function = *executor.program.functions.get(&func_ref).unwrap();
                bound_params.extend(function.params.iter().map(|(ident, _)| *ident).zip(params));
                executor.function(function, func_ref, bound_params, None)
            }
            Value::ContinuedFunction(callee, ref continuations) => {
                bound_params.extend(continuations);
                callee.call(params, bound_params, executor)
            }
            Value::Closure {
                func_ref,
                ref environment,
            } => {
                let function = *executor.program.functions.get(&func_ref).unwrap();
                bound_params.extend(function.params.iter().map(|(ident, _)| *ident).zip(params));
                executor.function(
                    function,
                    func_ref,
                    bound_params,
                    Some(Rc::clone(environment)),
                )
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

    pub const fn array(values: Vec<ValueRef<'arena>>) -> Value {
        Value::Array(RefCell::new(values))
    }

    pub const fn tuple(values: Vec<ValueRef<'arena>>) -> Value {
        Value::Tuple(RefCell::new(values))
    }

    pub const fn user_defined(discriminant: Option<usize>, fields: Vec<ValueRef<'arena>>) -> Value {
        Value::UserDefined {
            discriminant,
            fields: RefCell::new(fields),
        }
    }
}

impl<'arena> PartialOrd for Value<'arena> {
    /// ## Panics
    /// 
    /// May panic if any [`RefCell`]s in `self` or `other` are mutably borrowed.
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Value::Int(i1), Value::Int(i2)) => i1.partial_cmp(i2),
            (Value::Float(f1), Value::Float(f2)) => f1.partial_cmp(f2),
            (Value::String(s1), Value::String(s2)) => s1.partial_cmp(s2),
            (Value::Array(arr1), Value::Array(arr2)) => arr1.partial_cmp(arr2),
            (Value::Tuple(t1), Value::Tuple(t2)) => t1.partial_cmp(t2),
            _ => None,
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

impl<'arena> From<Void> for &Value<'arena> {
    fn from(value: Void) -> Self {
        match value {}
    }
}

// SAFETY: `Value` is not `Drop`.
unsafe impl<'arena> ArenaSafe for Value<'arena> {}

pub type ValueRef<'arena> = &'arena Value<'arena>;

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

    fn cast<U>(self) -> ControlFlow<U>
    where
        T: Into<U>,
    {
        if let ControlFlow::Value(value) = self {
            ControlFlow::Value(value.into())
        } else {
            // SAFETY: `self` is not `ControlFlow::Value`.
            unsafe { self.cast_unchecked() }
        }
    }

    fn try_cast<U>(self) -> Option<ControlFlow<U>> {
        if matches!(self, ControlFlow::Value(_)) {
            None
        } else {
            // SAFETY: `self` is not `ControlFlow::Value`.
            let ctrl = unsafe { self.cast_unchecked() };
            Some(ctrl)
        }
    }

    /// ## Safety
    ///
    /// If `self` is `ControlFlow::Value`, it must be valid to reinterpret values of `T` as `U`.
    unsafe fn cast_unchecked<U>(self) -> ControlFlow<U> {
        match self {
            ControlFlow::Goto(id) => ControlFlow::Goto(id),
            ControlFlow::Terminate(n) => ControlFlow::Terminate(n),
            ControlFlow::Value(value) => {
                // SAFETY: Must be ensured by caller.
                let output_value = unsafe { mem::transmute_copy(&value) };
                mem::forget(value);
                ControlFlow::Value(output_value)
            }
        }
    }
}

impl<'arena> ControlFlow<ValueRef<'arena>> {
    fn value(value: Value<'arena>, arena: &'arena Arena<'arena>) -> ControlFlow<ValueRef<'arena>> {
        ControlFlow::Value(arena.allocate(value))
    }
}

#[derive(Debug, PartialEq)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Void {}

struct Executor<'arena> {
    program: Program<'arena>,
    arena: &'arena Arena<'arena>,
    environment: SharedEnvironment<'arena>,
    func_ref: FuncRef,
}

impl<'arena> Executor<'arena> {
    fn new(
        program: Program<'arena>,
        arena: &'arena Arena<'arena>,
        func_ref: FuncRef,
    ) -> Executor<'arena> {
        Executor {
            program,
            arena,
            environment: Rc::new(RefCell::new(Environment::new())),
            func_ref,
        }
    }

    fn expr_list(&mut self, exprs: &[&Expr<'arena>]) -> ControlFlow<Vec<ValueRef<'arena>>> {
        let mut values = Vec::with_capacity(exprs.len());
        for &expr in exprs {
            values.push(value!(self.expr(expr)));
        }
        ControlFlow::Value(values)
    }

    fn binary_op(
        &mut self,
        left: &Expr<'arena>,
        right: &Expr<'arena>,
        op: BinaryOp,
    ) -> ControlFlow<ValueRef<'arena>> {
        let left = value!(self.expr(left));
        let right = value!(self.expr(right));
        let result = if op.is_arithmetic() {
            let result = match op {
                BinaryOp::Add => left + right,
                BinaryOp::Sub => left - right,
                BinaryOp::Mul => left * right,
                BinaryOp::Div => left / right,
                BinaryOp::Rem => left % right,
                _ => unreachable!(),
            };

            &*self.arena.allocate(result.unwrap())
        } else {
            let ord = left.partial_cmp(right);
            let cmp = match op {
                BinaryOp::Eq => Ordering::is_eq,
                BinaryOp::Ne => Ordering::is_ne,
                BinaryOp::Lt => Ordering::is_lt,
                BinaryOp::Le => Ordering::is_le,
                BinaryOp::Gt => Ordering::is_gt,
                BinaryOp::Ge => Ordering::is_ge,
                _ => unreachable!(),
            };
            let result = ord.map_or(false, cmp);

            if result {
                self.program.lib_std.b_true
            } else {
                self.program.lib_std.b_false
            }
        };
        ControlFlow::Value(result)
    }

    fn closure(&mut self, func_ref: FuncRef) -> ControlFlow<ValueRef<'arena>> {
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

    fn expr(&mut self, expr: &Expr<'arena>) -> ControlFlow<ValueRef<'arena>> {
        match *expr {
            Expr::Literal(ref lit) => ControlFlow::value(lit.clone().into(), self.arena),
            Expr::Ident(ident) => ControlFlow::Value(self.environment.borrow().get(ident).unwrap()),
            Expr::Function(func_ref) => ControlFlow::value(Value::Function(func_ref), self.arena),
            Expr::Tuple(ref tuple) => {
                ControlFlow::value(Value::tuple(value!(self.expr_list(tuple))), self.arena)
            }
            Expr::Constructor {
                ty: _,
                index,
                ref fields,
            } => ControlFlow::value(
                Value::user_defined(index, value!(self.expr_list(fields))),
                self.arena,
            ),
            Expr::Array(ref arr) => {
                ControlFlow::value(Value::array(value!(self.expr_list(arr))), self.arena)
            }
            Expr::Get {
                object,
                object_variant: _,
                field,
            } => {
                let object = value!(self.expr(object));
                ControlFlow::Value(object.get(field).unwrap())
            }
            Expr::Set {
                object,
                object_variant: _,
                field,
                value,
            } => {
                let object = value!(self.expr(object));
                let value = value!(self.expr(value));
                object.set(field, value);
                ControlFlow::Value(value)
            }
            Expr::Call(callee, ref params) => {
                let callee = value!(self.expr(callee));
                let params = value!(self.expr_list(params));
                callee.call(params, HashMap::new(), self).cast()
            }
            Expr::ContApplication(func, ref continuations) => {
                let func = value!(self.expr(func));
                let mut evaluated_continuations = HashMap::with_capacity(continuations.len());
                for (&index, &continuation) in continuations {
                    evaluated_continuations.insert(index, value!(self.expr(continuation)));
                }
                ControlFlow::value(
                    func.apply_continuations(evaluated_continuations),
                    self.arena,
                )
            }
            Expr::Unary(op, operand) => {
                let value = value!(self.expr(operand));
                match op {
                    UnaryOp::Neg => {
                        ControlFlow::value(Value::Int(-value.as_int().unwrap()), self.arena)
                    }
                }
            }
            Expr::Binary(left, op, right) => self.binary_op(left, right, op),
            Expr::Assign { ident, expr } => {
                let value = value!(self.expr(expr));
                self.environment.borrow_mut().set(ident, value);
                ControlFlow::Value(value)
            }
            Expr::Switch {
                scrutinee,
                ref arms,
                otherwise,
            } => {
                let scrutinee = value!(self.expr(scrutinee)).as_int().unwrap();
                let block_id = arms.get(&scrutinee).copied().unwrap_or(otherwise);
                ControlFlow::Goto(block_id)
            }
            Expr::Goto(block_id) => ControlFlow::Goto(block_id),
            Expr::Closure {
                func_ref,
                captures: _,
            } => self.closure(func_ref),
            Expr::Unreachable => unreachable!(),
        }
    }

    fn intrinsic(
        &mut self,
        intrinsic: Intrinsic,
        params: &HashMap<Ident, ValueRef<'arena>>,
    ) -> ControlFlow<Void> {
        match intrinsic {
            Intrinsic::Discriminant => {
                let discriminant = params[&Ident(0)].discriminant();
                let continuation = params[&Ident(1)];
                continuation
                    .call(
                        vec![self.arena.allocate(Value::Int(discriminant))],
                        HashMap::new(),
                        self,
                    )
                    .try_cast()
                    .unwrap()
            }
            Intrinsic::Terminate => {
                let exit_code = params[&Ident(0)].as_int().unwrap();
                ControlFlow::Terminate(exit_code)
            }
        }
    }

    fn function(
        &mut self,
        function: &Function<'arena>,
        func_ref: FuncRef,
        params: HashMap<Ident, ValueRef<'arena>>,
        enclosing_environment: Option<SharedEnvironment<'arena>>,
    ) -> ControlFlow<Void> {
        if let Some(intrinsic) = function.intrinsic {
            return self.intrinsic(intrinsic, &params);
        }

        self.func_ref = func_ref;

        let mut env = self.environment.borrow_mut();
        *env = Environment::from_map(params);
        env.enclosing = enclosing_environment;
        for (&declaration, (_, initialiser)) in &function.declarations {
            let value = initialiser.clone().map_or(Value::Int(0), Into::into);
            env.values.insert(declaration, self.arena.allocate(value));
        }
        drop(env);
        let mut block = function.blocks.get(&Function::entry_point()).unwrap();
        loop {
            for &expr in &block.exprs {
                match self.expr(expr) {
                    ControlFlow::Goto(block_id) => block = function.blocks.get(&block_id).unwrap(),
                    ctrl => return ctrl.try_cast().unwrap(),
                }
            }
        }
    }

    fn run(mut self) -> i64 {
        let entry_point = self
            .program
            .functions
            .get(&self.program.entry_point())
            .unwrap();
        let termination_param = *entry_point.continuations.keys().next().unwrap();
        let termination_fn = &*self
            .arena
            .allocate(Value::Function(self.program.lib_std.fn_termination));
        self.function(
            entry_point,
            self.program.entry_point(),
            iter::once((termination_param, termination_fn)).collect(),
            None,
        )
        .unwrap_termination()
    }
}

pub fn run<'arena>(program: Program<'arena>, arena: &'arena Arena<'arena>) -> i64 {
    let func_ref = program.entry_point();
    Executor::new(program, arena, func_ref).run()
}
