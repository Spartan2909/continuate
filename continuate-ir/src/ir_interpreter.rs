use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::UnaryOp;
use crate::mid_level_ir::BlockId;
use crate::mid_level_ir::Expr;
use crate::mid_level_ir::Function;
use crate::mid_level_ir::Program;
use crate::HashMap;
use crate::Vec;

use std::cell::RefCell;
use std::cmp::Ordering;
use std::mem;
use std::ops;
use std::rc::Rc;

use bumpalo::Bump;

#[derive(Debug, PartialEq)]
pub enum Value<'arena> {
    Int(i64),
    Float(f64),
    String(String),
    Array(RefCell<Vec<'arena, &'arena Value<'arena>>>),
    Tuple(RefCell<Vec<'arena, &'arena Value<'arena>>>),
    Function(FuncRef),
    ContinuedFunction(
        &'arena Value<'arena>,
        HashMap<'arena, Ident, &'arena Value<'arena>>,
    ),
    Closure {
        func_ref: FuncRef,
        environment: SharedEnvironment<'arena>,
    },
    UserDefined {
        discriminant: Option<usize>,
        fields: RefCell<Vec<'arena, &'arena Value<'arena>>>,
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

    pub const fn as_user_defined(
        &self,
    ) -> Option<(Option<usize>, &RefCell<Vec<'arena, ValueRef<'arena>>>)> {
        if let Value::UserDefined {
            discriminant,
            ref fields,
        } = *self
        {
            Some((discriminant, fields))
        } else {
            None
        }
    }

    fn call(
        &self,
        params: Vec<ValueRef<'arena>>,
        mut bound_params: HashMap<'arena, Ident, ValueRef<'arena>>,
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

    fn apply_continuations<I>(&'arena self, continuations: I, arena: &'arena Bump) -> Value<'arena>
    where
        I: IntoIterator<Item = (Ident, ValueRef<'arena>)>,
        I::IntoIter: ExactSizeIterator,
    {
        match self {
            Value::Function(_) | Value::Closure { .. } => {
                let iter = continuations.into_iter();
                let mut new_continuations = HashMap::with_capacity_in(iter.len(), arena);
                new_continuations.extend(iter);
                Value::ContinuedFunction(self, new_continuations)
            }
            Value::ContinuedFunction(callee, existing_continuations) => {
                let mut new_continuations = existing_continuations.clone();
                new_continuations.extend(continuations);
                Value::ContinuedFunction(callee, new_continuations)
            }
            _ => unreachable!(),
        }
    }

    pub const fn array(values: Vec<'arena, ValueRef<'arena>>) -> Value<'arena> {
        Value::Array(RefCell::new(values))
    }

    pub const fn tuple(values: Vec<'arena, ValueRef<'arena>>) -> Value<'arena> {
        Value::Tuple(RefCell::new(values))
    }

    pub const fn user_defined(
        discriminant: Option<usize>,
        fields: Vec<'arena, ValueRef<'arena>>,
    ) -> Value<'arena> {
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
        match self {
            ControlFlow::Goto(id) => ControlFlow::Goto(id),
            ControlFlow::Terminate(n) => ControlFlow::Terminate(n),
            ControlFlow::Value(value) => ControlFlow::Value(value.into()),
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
    fn value(value: Value<'arena>, arena: &'arena Bump) -> ControlFlow<ValueRef<'arena>> {
        ControlFlow::Value(arena.alloc(value))
    }
}

#[derive(Debug, PartialEq)]
pub struct Environment<'arena> {
    enclosing: Option<SharedEnvironment<'arena>>,
    values: HashMap<'arena, Ident, ValueRef<'arena>>,
}

impl<'arena> Environment<'arena> {
    fn new(arena: &'arena Bump) -> Environment<'arena> {
        Environment {
            enclosing: None,
            values: HashMap::new_in(arena),
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

    const fn from_map(map: HashMap<'arena, Ident, ValueRef<'arena>>) -> Environment<'arena> {
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
    arena: &'arena Bump,
    environment: SharedEnvironment<'arena>,
    func_ref: FuncRef,
    b_true: ValueRef<'arena>,
    b_false: ValueRef<'arena>,
}

impl<'arena> Executor<'arena> {
    fn new(program: Program<'arena>, arena: &'arena Bump, func_ref: FuncRef) -> Executor<'arena> {
        Executor {
            program,
            arena,
            environment: Rc::new(RefCell::new(Environment::new(arena))),
            func_ref,
            b_true: arena.alloc(Value::UserDefined {
                discriminant: Some(1),
                fields: RefCell::new(Vec::new_in(arena)),
            }),
            b_false: arena.alloc(Value::UserDefined {
                discriminant: Some(0),
                fields: RefCell::new(Vec::new_in(arena)),
            }),
        }
    }

    fn expr_list(&mut self, exprs: &[Expr<'arena>]) -> ControlFlow<Vec<'arena, ValueRef<'arena>>> {
        let mut values = Vec::with_capacity_in(exprs.len(), self.arena);
        for expr in exprs {
            values.push(value!(self.expr(expr)));
        }
        ControlFlow::Value(values)
    }

    fn cont_application(
        &mut self,
        func: &Expr<'arena>,
        continuations: &HashMap<Ident, Expr<'arena>>,
    ) -> ControlFlow<ValueRef<'arena>> {
        let func = value!(self.expr(func));
        let mut evaluated_continuations =
            HashMap::with_capacity_in(continuations.len(), self.arena);
        for (&index, continuation) in continuations {
            evaluated_continuations.insert(index, value!(self.expr(continuation)));
        }
        ControlFlow::value(
            func.apply_continuations(evaluated_continuations, self.arena),
            self.arena,
        )
    }

    fn unary_op(
        &mut self,
        operator: UnaryOp,
        operand: &Expr<'arena>,
    ) -> ControlFlow<ValueRef<'arena>> {
        let value = value!(self.expr(operand));
        match operator {
            UnaryOp::Neg => ControlFlow::value(Value::Int(-value.as_int().unwrap()), self.arena),
            UnaryOp::Not => {
                let (discriminant, fields) = value.as_user_defined().unwrap();
                let value =
                    Value::user_defined(Some(discriminant.unwrap() ^ 1), fields.borrow().clone());
                ControlFlow::value(value, self.arena)
            }
        }
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

            self.arena.alloc(result.unwrap())
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
                self.b_true
            } else {
                self.b_false
            }
        };
        ControlFlow::Value(result)
    }

    fn closure(&self, func_ref: FuncRef) -> ControlFlow<ValueRef<'arena>> {
        let mut new_env = Environment::new(self.arena);
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
            Expr::Tuple { ty: _, ref values } => {
                ControlFlow::value(Value::tuple(value!(self.expr_list(values))), self.arena)
            }
            Expr::Constructor {
                ty: _,
                index,
                ref fields,
            } => ControlFlow::value(
                Value::user_defined(index, value!(self.expr_list(fields))),
                self.arena,
            ),
            Expr::Array {
                ty: _,
                ref values,
                value_ty: _,
            } => ControlFlow::value(Value::array(value!(self.expr_list(values))), self.arena),
            Expr::Get {
                object,
                object_ty: _,
                object_variant: _,
                field,
            } => {
                let object = value!(self.expr(object));
                ControlFlow::Value(object.get(field).unwrap())
            }
            Expr::Set {
                object,
                object_ty: _,
                object_variant: _,
                field,
                value,
            } => {
                let object = value!(self.expr(object));
                let value = value!(self.expr(value));
                object.set(field, value);
                ControlFlow::Value(value)
            }
            Expr::Call {
                callee,
                callee_ty: _,
                ref args,
            } => {
                let callee = value!(self.expr(callee));
                let params = value!(self.expr_list(args));
                callee
                    .call(params, HashMap::new_in(self.arena), self)
                    .cast()
            }
            Expr::ContApplication(func, ref continuations) => {
                self.cont_application(func, continuations)
            }
            Expr::Unary {
                operator,
                operand,
                operand_ty: _,
            } => self.unary_op(operator, operand),
            Expr::Binary {
                left,
                left_ty: _,
                operator,
                right,
                right_ty: _,
            } => self.binary_op(left, right, operator),
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
            Expr::Intrinsic {
                intrinsic,
                value,
                value_ty: _,
            } => {
                let value = value!(self.expr(value));
                self.intrinsic(intrinsic, value)
            }
            Expr::Unreachable => unreachable!(),
        }
    }

    fn intrinsic(
        &self,
        intrinsic: Intrinsic,
        value: ValueRef<'arena>,
    ) -> ControlFlow<ValueRef<'arena>> {
        match intrinsic {
            Intrinsic::Discriminant => {
                let discriminant = value.discriminant();
                ControlFlow::value(Value::Int(discriminant), self.arena)
            }
            Intrinsic::Terminate => {
                let exit_code = value.as_int().unwrap();
                ControlFlow::Terminate(exit_code)
            }
        }
    }

    fn function(
        &mut self,
        function: &Function<'arena>,
        func_ref: FuncRef,
        params: HashMap<'arena, Ident, ValueRef<'arena>>,
        enclosing_environment: Option<SharedEnvironment<'arena>>,
    ) -> ControlFlow<Void> {
        self.func_ref = func_ref;

        let mut env = self.environment.borrow_mut();
        *env = Environment::from_map(params);
        env.enclosing = enclosing_environment;
        for (&declaration, (_, initialiser)) in &function.declarations {
            let value = initialiser.clone().map_or(Value::Int(0), Into::into);
            env.values.insert(declaration, self.arena.alloc(value));
        }
        drop(env);
        let mut block = function.blocks.get(&Function::entry_point()).unwrap();
        loop {
            for expr in &block.exprs {
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
        let termination_fn = self
            .arena
            .alloc(Value::Function(self.program.lib_std.fn_termination));
        let mut params = HashMap::with_capacity_in(1, self.arena);
        params.insert(termination_param, &*termination_fn);
        self.function(entry_point, self.program.entry_point(), params, None)
            .unwrap_termination()
    }
}

pub fn run<'arena>(program: Program<'arena>, arena: &'arena Bump) -> i64 {
    let func_ref = program.entry_point();
    Executor::new(program, arena, func_ref).run()
}
