use crate::common::BinaryOp;
use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::UnaryOp;
use crate::mid_level_ir::BlockId;
use crate::mid_level_ir::Expr;
use crate::mid_level_ir::ExprArray;
use crate::mid_level_ir::ExprAssign;
use crate::mid_level_ir::ExprBinary;
use crate::mid_level_ir::ExprCall;
use crate::mid_level_ir::ExprClosure;
use crate::mid_level_ir::ExprConstructor;
use crate::mid_level_ir::ExprContApplication;
use crate::mid_level_ir::ExprGet;
use crate::mid_level_ir::ExprIntrinsic;
use crate::mid_level_ir::ExprSet;
use crate::mid_level_ir::ExprSwitch;
use crate::mid_level_ir::ExprTuple;
use crate::mid_level_ir::ExprUnary;
use crate::mid_level_ir::Function;
use crate::mid_level_ir::Program;

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter;
use std::mem;
use std::ops;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub struct UserDefinedValue {
    discriminant: Option<usize>,
    fields: RefCell<Vec<Rc<Value>>>,
}

#[derive(Debug, PartialEq)]
pub enum Value {
    Bool(bool),
    Int(i64),
    Float(f64),
    String(String),
    Array(RefCell<Vec<Rc<Value>>>),
    Tuple(RefCell<Vec<Rc<Value>>>),
    Function(FuncRef),
    ContinuedFunction(Rc<Value>, HashMap<Ident, Rc<Value>>),
    Closure {
        func_ref: FuncRef,
        environment: SharedEnvironment,
    },
    UserDefined(UserDefinedValue),
}

impl Value {
    pub(crate) fn discriminant(&self) -> i64 {
        match self {
            Value::UserDefined(UserDefinedValue {
                discriminant,
                fields: _,
            }) => discriminant.unwrap_or(0) as i64,
            _ => 0,
        }
    }

    fn get(&self, index: usize) -> Option<Rc<Value>> {
        match self {
            Value::Array(values)
            | Value::Tuple(values)
            | Value::UserDefined(UserDefinedValue {
                discriminant: _,
                fields: values,
            }) => values.borrow().get(index).cloned(),
            _ => None,
        }
    }

    fn set(&self, index: usize, value: Rc<Value>) {
        match self {
            Value::Array(values)
            | Value::Tuple(values)
            | Value::UserDefined(UserDefinedValue {
                discriminant: _,
                fields: values,
            }) => {
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

    pub const fn as_user_defined(&self) -> Option<&UserDefinedValue> {
        if let Value::UserDefined(value) = self {
            Some(value)
        } else {
            None
        }
    }

    fn call(
        &self,
        params: Vec<Rc<Value>>,
        mut bound_params: HashMap<Ident, Rc<Value>>,
        executor: &mut Executor,
        program: &Program,
    ) -> ControlFlow<Void> {
        match *self {
            Value::Function(func_ref) => {
                let function = program.functions.get(&func_ref).unwrap();
                bound_params.extend(function.params.iter().map(|(ident, _)| *ident).zip(params));
                executor.function(function, func_ref, bound_params, None, program)
            }
            Value::ContinuedFunction(ref callee, ref continuations) => {
                bound_params.extend(
                    continuations
                        .iter()
                        .map(|(ident, value)| (*ident, Rc::clone(value))),
                );
                callee.call(params, bound_params, executor, program)
            }
            Value::Closure {
                func_ref,
                ref environment,
            } => {
                let function = program.functions.get(&func_ref).unwrap();
                bound_params.extend(function.params.iter().map(|(ident, _)| *ident).zip(params));
                executor.function(
                    function,
                    func_ref,
                    bound_params,
                    Some(Rc::clone(environment)),
                    program,
                )
            }
            _ => unreachable!(),
        }
    }

    fn apply_continuations<I>(self: &Rc<Self>, continuations: I) -> Value
    where
        I: IntoIterator<Item = (Ident, Rc<Value>)>,
        I::IntoIter: ExactSizeIterator,
    {
        match &**self {
            Value::Function(_) | Value::Closure { .. } => {
                Value::ContinuedFunction(Rc::clone(self), continuations.into_iter().collect())
            }
            Value::ContinuedFunction(callee, existing_continuations) => {
                let mut new_continuations = existing_continuations.clone();
                new_continuations.extend(continuations);
                Value::ContinuedFunction(Rc::clone(callee), new_continuations)
            }
            _ => unreachable!(),
        }
    }

    pub const fn array(values: Vec<Rc<Value>>) -> Value {
        Value::Array(RefCell::new(values))
    }

    pub const fn tuple(values: Vec<Rc<Value>>) -> Value {
        Value::Tuple(RefCell::new(values))
    }

    pub const fn user_defined(discriminant: Option<usize>, fields: Vec<Rc<Value>>) -> Value {
        Value::UserDefined(UserDefinedValue {
            discriminant,
            fields: RefCell::new(fields),
        })
    }
}

impl PartialOrd for Value {
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

impl ops::Add for &Value {
    type Output = Option<Value>;

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

impl ops::Sub for &Value {
    type Output = Option<Value>;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 - n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 - n2)),
            _ => None,
        }
    }
}

impl ops::Mul for &Value {
    type Output = Option<Value>;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 * n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 * n2)),
            _ => None,
        }
    }
}

impl ops::Div for &Value {
    type Output = Option<Value>;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 / n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 / n2)),
            _ => None,
        }
    }
}

impl ops::Rem for &Value {
    type Output = Option<Value>;

    fn rem(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::Int(n1), Value::Int(n2)) => Some(Value::Int(n1 % n2)),
            (Value::Float(n1), Value::Float(n2)) => Some(Value::Float(n1 % n2)),
            _ => None,
        }
    }
}

impl From<Literal> for Value {
    fn from(value: Literal) -> Self {
        match value {
            Literal::Int(n) => Value::Int(n),
            Literal::Float(n) => Value::Float(n),
            Literal::String(s) => Value::String(s),
        }
    }
}

impl From<Void> for Value {
    fn from(value: Void) -> Self {
        match value {}
    }
}

impl From<Void> for Rc<Value> {
    fn from(value: Void) -> Self {
        match value {}
    }
}

#[derive(Debug)]
enum ControlFlow<T> {
    Goto(BlockId),
    Terminate(i64),
    Value(T),
}

macro_rules! value {
    ($ctrl:expr) => {
        match ($ctrl) {
            ControlFlow::Goto(block) => return ControlFlow::Goto(block),
            ControlFlow::Terminate(n) => return ControlFlow::Terminate(n),
            ControlFlow::Value(value) => value,
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

#[derive(Debug, PartialEq)]
pub struct Environment {
    enclosing: Option<SharedEnvironment>,
    values: HashMap<Ident, Rc<Value>>,
}

impl Environment {
    fn new() -> Environment {
        Environment {
            enclosing: None,
            values: HashMap::new(),
        }
    }

    fn get(&self, ident: Ident) -> Option<Rc<Value>> {
        self.values
            .get(&ident)
            .cloned()
            .or_else(|| self.enclosing.as_ref()?.borrow().get(ident))
    }

    fn set(&mut self, ident: Ident, value: Rc<Value>) {
        if let Some(place) = self.values.get_mut(&ident) {
            *place = value;
        } else if let Some(enclosing) = &self.enclosing {
            enclosing.borrow_mut().set(ident, value);
        } else {
            panic!("set unassigned value")
        }
    }

    const fn from_map(map: HashMap<Ident, Rc<Value>>) -> Environment {
        Environment {
            enclosing: None,
            values: map,
        }
    }
}

type SharedEnvironment = Rc<RefCell<Environment>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Void {}

struct Executor {
    environment: SharedEnvironment,
    func_ref: FuncRef,
}

fn interpret_intrinsic(intrinsic: Intrinsic, values: &[Rc<Value>]) -> ControlFlow<Rc<Value>> {
    match intrinsic {
        Intrinsic::Discriminant => {
            assert_eq!(values.len(), 1);
            let discriminant = values[0].discriminant();
            ControlFlow::Value(Rc::new(Value::Int(discriminant)))
        }
        Intrinsic::Terminate => {
            assert_eq!(values.len(), 1);
            let exit_code = values[0].as_int().unwrap();
            ControlFlow::Terminate(exit_code)
        }
        Intrinsic::Unreachable => unreachable!(),
    }
}

impl Executor {
    fn new(func_ref: FuncRef) -> Executor {
        Executor {
            environment: Rc::new(RefCell::new(Environment::new())),
            func_ref,
        }
    }

    fn expr_list<'a>(
        &mut self,
        exprs: impl IntoIterator<Item = &'a Expr>,
        program: &Program,
    ) -> ControlFlow<Vec<Rc<Value>>> {
        let mut values = Vec::new();
        for expr in exprs {
            values.push(value!(self.expr(expr, program)));
        }
        ControlFlow::Value(values)
    }

    fn call(
        &mut self,
        func: &Expr,
        params: &[(Option<Ident>, Expr)],
        program: &Program,
    ) -> ControlFlow<Rc<Value>> {
        let func = value!(self.expr(func, program));
        let mut args = Vec::new();
        let mut continuations = HashMap::new();
        for &(ident, ref param) in params {
            let param = value!(self.expr(param, program));
            if let Some(ident) = ident {
                continuations.insert(ident, param);
            } else {
                args.push(param);
            }
        }
        func.call(args, continuations, self, program).cast()
    }

    fn cont_application(
        &mut self,
        func: &Expr,
        continuations: &Vec<(Ident, Expr)>,
        program: &Program,
    ) -> ControlFlow<Rc<Value>> {
        let func = value!(self.expr(func, program));
        let mut evaluated_continuations = Vec::with_capacity(continuations.len());
        for (index, continuation) in continuations {
            evaluated_continuations.push((*index, value!(self.expr(continuation, program))));
        }
        ControlFlow::Value(Rc::new(func.apply_continuations(evaluated_continuations)))
    }

    fn unary_op(
        &mut self,
        operator: UnaryOp,
        operand: &Expr,
        program: &Program,
    ) -> ControlFlow<Rc<Value>> {
        let value = value!(self.expr(operand, program));
        match operator {
            UnaryOp::Neg => ControlFlow::Value(Rc::new(Value::Int(-value.as_int().unwrap()))),
            UnaryOp::Not => {
                let UserDefinedValue {
                    discriminant,
                    fields,
                } = value.as_user_defined().unwrap();
                let value =
                    Value::user_defined(Some(discriminant.unwrap() ^ 1), fields.borrow().clone());
                ControlFlow::Value(Rc::new(value))
            }
        }
    }

    fn binary_op(
        &mut self,
        left: &Expr,
        right: &Expr,
        op: BinaryOp,
        program: &Program,
    ) -> ControlFlow<Rc<Value>> {
        let left = value!(self.expr(left, program));
        let right = value!(self.expr(right, program));
        let result = if op.is_arithmetic() {
            let result = match op {
                BinaryOp::Add => &*left + &*right,
                BinaryOp::Sub => &*left - &*right,
                BinaryOp::Mul => &*left * &*right,
                BinaryOp::Div => &*left / &*right,
                BinaryOp::Rem => &*left % &*right,
                _ => unreachable!(),
            };
            result.unwrap()
        } else {
            let ord = left.partial_cmp(&right);
            let cmp = match op {
                BinaryOp::Eq => Ordering::is_eq,
                BinaryOp::Ne => Ordering::is_ne,
                BinaryOp::Lt => Ordering::is_lt,
                BinaryOp::Le => Ordering::is_le,
                BinaryOp::Gt => Ordering::is_gt,
                BinaryOp::Ge => Ordering::is_ge,
                _ => unreachable!(),
            };
            let result = ord.is_some_and(cmp);

            Value::Bool(result)
        };
        ControlFlow::Value(Rc::new(result))
    }

    fn closure(&self, func_ref: FuncRef) -> ControlFlow<Rc<Value>> {
        let mut new_env = Environment::new();
        new_env.enclosing = Some(Rc::clone(&self.environment));
        let old_env = mem::replace(&mut *self.environment.borrow_mut(), new_env);
        ControlFlow::Value(Rc::new(Value::Closure {
            func_ref,
            environment: Rc::new(RefCell::new(old_env)),
        }))
    }

    fn expr(&mut self, expr: &Expr, program: &Program) -> ControlFlow<Rc<Value>> {
        match *expr {
            Expr::Literal(ref expr) => ControlFlow::Value(Rc::new(expr.literal.clone().into())),
            Expr::Ident(ref expr) => {
                ControlFlow::Value(self.environment.borrow().get(expr.ident).unwrap())
            }
            Expr::Function(ref expr) => ControlFlow::Value(Rc::new(Value::Function(expr.function))),
            Expr::Tuple(ExprTuple { ty: _, ref values }) => ControlFlow::Value(Rc::new(
                Value::tuple(value!(self.expr_list(values, program))),
            )),
            Expr::Constructor(ExprConstructor {
                ty: _,
                index,
                ref fields,
            }) => ControlFlow::Value(Rc::new(Value::user_defined(
                index,
                value!(self.expr_list(fields, program)),
            ))),
            Expr::Array(ExprArray {
                ty: _,
                ref values,
                value_ty: _,
            }) => ControlFlow::Value(Rc::new(Value::array(value!(
                self.expr_list(values, program)
            )))),
            Expr::Get(ExprGet {
                ref object,
                object_ty: _,
                object_variant: _,
                field,
            }) => {
                let object = value!(self.expr(object, program));
                ControlFlow::Value(object.get(field).unwrap())
            }
            Expr::Set(ExprSet {
                ref object,
                object_ty: _,
                object_variant: _,
                field,
                ref value,
            }) => {
                let object = value!(self.expr(object, program));
                let value = value!(self.expr(value, program));
                object.set(field, Rc::clone(&value));
                ControlFlow::Value(value)
            }
            Expr::Call(ExprCall {
                ref callee,
                callee_ty: _,
                ref args,
            }) => self.call(callee, args, program),
            Expr::ContApplication(ExprContApplication {
                ref callee,
                callee_ty: _,
                ref continuations,
                result_ty: _,
                storage_ty: _,
            }) => self.cont_application(callee, continuations, program),
            Expr::Unary(ExprUnary {
                operator,
                ref operand,
                operand_ty: _,
            }) => self.unary_op(operator, operand, program),
            Expr::Binary(ExprBinary {
                ref left,
                left_ty: _,
                operator,
                ref right,
                right_ty: _,
            }) => self.binary_op(left, right, operator, program),
            Expr::Assign(ExprAssign { ident, ref expr }) => {
                let value = value!(self.expr(expr, program));
                self.environment.borrow_mut().set(ident, Rc::clone(&value));
                ControlFlow::Value(value)
            }
            Expr::Switch(ExprSwitch {
                ref scrutinee,
                ref arms,
                otherwise,
            }) => {
                let scrutinee = value!(self.expr(scrutinee, program)).as_int().unwrap();
                let block_id = arms.get(&scrutinee).copied().unwrap_or(otherwise);
                ControlFlow::Goto(block_id)
            }
            Expr::Goto(ref expr) => ControlFlow::Goto(expr.block),
            Expr::Closure(ExprClosure {
                func_ref,
                captures: _,
                storage_ty: _,
            }) => self.closure(func_ref),
            Expr::Intrinsic(ExprIntrinsic {
                intrinsic,
                ref values,
            }) => {
                let values = value!(self.expr_list(values.iter().map(|(expr, _)| expr), program));
                interpret_intrinsic(intrinsic, &values)
            }
        }
    }

    fn function(
        &mut self,
        function: &Function,
        func_ref: FuncRef,
        params: HashMap<Ident, Rc<Value>>,
        enclosing_environment: Option<SharedEnvironment>,
        program: &Program,
    ) -> ControlFlow<Void> {
        self.func_ref = func_ref;

        let mut env = self.environment.borrow_mut();
        *env = Environment::from_map(params);
        env.enclosing = enclosing_environment;
        for (&declaration, (_, initialiser)) in &function.declarations {
            let value = initialiser.clone().map_or(Value::Int(0), Into::into);
            env.values.insert(declaration, Rc::new(value));
        }
        drop(env);
        let mut block = function.blocks.get(&Function::entry_point()).unwrap();
        loop {
            for expr in &block.exprs {
                match self.expr(expr, program) {
                    ControlFlow::Goto(block_id) => block = function.blocks.get(&block_id).unwrap(),
                    ctrl => return ctrl.try_cast().unwrap(),
                }
            }
        }
    }

    fn run(mut self, program: &Program) -> i64 {
        let entry_point = program.functions.get(&FuncRef::ENTRY_POINT).unwrap();
        let termination_param = *entry_point.continuations.keys().next().unwrap();
        let termination_fn = Rc::new(Value::Function(program.lib_std.fn_termination));
        self.function(
            entry_point,
            FuncRef::ENTRY_POINT,
            iter::once((termination_param, termination_fn)).collect(),
            None,
            program,
        )
        .unwrap_termination()
    }
}

pub fn run(program: &Program) -> i64 {
    Executor::new(FuncRef::ENTRY_POINT).run(program)
}
