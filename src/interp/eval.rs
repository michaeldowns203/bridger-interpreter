//! The evaluator — YOUR file.  \[student\]
//!
//! [`eval_expr`](Interpreter::eval_expr) turns one [`Expr`] into a [`Value`], or
//! leaves evaluation early through [`Control`] (a stuck `Raise`, or a `Return`).
//! It is the heart of the interpreter and the one method you grow across the
//! milestones. Every `Expr` variant already has an arm; a variant you have not
//! reached yet is a milestone-tagged hole. To list a milestone's holes:
//!
//! ```text
//! grep -rn 'todo_m3!' src
//! ```
//!
//! To fill one in, replace its `todo_mN!(..)` with the rule's implementation,
//! destructuring the arm's `..` into the fields you need — for example
//! `Expr::Lit(lit, span) => …`. A block is just `Expr::Block`, so statement and
//! block evaluation live inside this one method; factor out a helper if you
//! like — the grader only ever calls `eval_expr`.
//!
//! Two contracts these arms must keep. A Bridger call — a function or method
//! body, and the `from` a `?` runs — is entered through
//! `Interpreter::enter_call` and left through `Interpreter::leave_call`,
//! balanced, so runaway recursion becomes a clean `RuntimeError::StackOverflow`
//! rather than aborting the process; this is the run-time call depth, separate
//! from the static nesting bound the checker enforces. And the `?` and
//! method-dispatch arms (M7, M8) read the type checker's choices from
//! `self.conversions`, keyed by an expression's span: look one up at the same
//! span the checker recorded it at (`Checker::record_conversion`), or a `?`
//! quietly passes its payload through unconverted.

use super::{type_of, Interpreter, RuntimeError};
use super::{Control, Env, Value};
use crate::ast::{BinOp, Expr, Lit, Span, Ty, UnOp};
use crate::interp::value::List;
use std::rc::Rc;

impl Interpreter {
    /// Evaluate `e` in environment `env`.
    pub fn eval_expr(&mut self, e: &Expr, env: &Env) -> Result<Value, Control> {
        match e {
            // ---- M1: expressions ----
            Expr::Lit(lit, _) => match lit {
                Lit::Int(lit) => Ok(Value::Int(*lit)),
                Lit::Bool(lit) => Ok(Value::Bool(*lit)),
                Lit::Str(lit) => Ok(Value::Str(Rc::from(lit.as_str()))),
                Lit::Unit => Ok(Value::Unit),
            },
            Expr::Unary(un_op, expr, span) => match un_op {
                UnOp::Neg => Ok(Value::Int(
                    expect_int(self.eval_expr(expr, env)?, *span)?.wrapping_neg(),
                )),
                UnOp::Not => Ok(Value::Bool(!expect_bool(
                    self.eval_expr(expr, env)?,
                    *span,
                )?)),
                UnOp::Ref => todo_m3!("E-Ref"),
                UnOp::Deref => todo_m3!("E-Deref"),
            },
            Expr::Binary(bin_op, expr1, expr2, span) => {
                let left = self.eval_expr(expr1, env)?;
                match bin_op {
                    // Keep the right expression unevaluated until it is needed.
                    BinOp::And => {
                        let left = expect_bool(left, *span)?;
                        Ok(Value::Bool(
                            left && expect_bool(self.eval_expr(expr2, env)?, *span)?,
                        ))
                    }
                    BinOp::Or => {
                        let left = expect_bool(left, *span)?;
                        Ok(Value::Bool(
                            left || expect_bool(self.eval_expr(expr2, env)?, *span)?,
                        ))
                    }
                    _ => {
                        let right = self.eval_expr(expr2, env)?;
                        eval_binary(*bin_op, left, right, *span)
                    }
                }
            }
            Expr::Tuple(elements, _) => {
                Ok(Value::Tuple(Rc::from(self.eval_elements(elements, env)?)))
            }
            Expr::List(elements, _) => {
                Ok(Value::List(List::from(self.eval_elements(elements, env)?)))
            }
            Expr::Proj(expr, index, span) => {
                let value = self.eval_expr(expr, env)?;
                let field = match &value {
                    Value::Tuple(values) => values.get(*index as usize).cloned(),
                    _ => None,
                };
                field.ok_or_else(|| {
                    Control::Raise(RuntimeError::NoSuchField {
                        field: index.to_string(),
                        span: *span,
                    })
                })
            }

            // ---- M2: binding ----
            Expr::Var(..) => todo_m2!("E-Var"),
            Expr::Block(..) => todo_m2!("E-Block / E-Let / E-Seq"),

            // ---- M3: state & control ----
            Expr::If(..) => todo_m3!("E-If"),
            Expr::While(..) => todo_m3!("E-While"),
            Expr::For(..) => todo_m3!("E-For"),
            Expr::Assign(..) => todo_m3!("E-Assign"),
            Expr::Return(..) => todo_m3!("E-Return"),

            // ---- M4: functions ----
            Expr::Lambda(..) => todo_m4!("E-Lam"),
            Expr::Call(..) => todo_m4!("E-App (dispatch Bridger vs. Native closure)"),

            // ---- M6: relations (queries go through `self.solutions`, engine.rs) ----
            Expr::Relation(..) => todo_m6!("E-Add / E-Clear / E-Solutions / E-Query"),
            Expr::ForQuery(..) => todo_m6!("E-ForQuery (iterate a query's solutions)"),

            // ---- M7: algebraic data types ----
            Expr::Ctor(..) => todo_m7!("E-Ctor"),
            Expr::Match(..) => todo_m7!("E-Match"),
            Expr::Try(..) => todo_m7!("E-Try (`?`: match + return)"),

            // ---- M8: objects ----
            Expr::Struct(..) => todo_m8!("E-Struct"),
            Expr::Field(..) => todo_m8!("E-Field (struct field access)"),
            Expr::Method(..) => todo_m8!("E-Method (head-type dispatch)"),
        }
    }

    /// Evaluate collection elements left to right, preserving child errors.
    fn eval_elements(&mut self, elements: &[Expr], env: &Env) -> Result<Vec<Value>, Control> {
        let mut values = Vec::with_capacity(elements.len());
        for element in elements {
            values.push(self.eval_expr(element, env)?);
        }
        Ok(values)
    }
}

fn type_error(expected: Ty, found: &Value, span: Span) -> Control {
    Control::Raise(RuntimeError::TypeError {
        expected,
        found: type_of(found),
        span,
    })
}

fn expect_int(value: Value, span: Span) -> Result<i64, Control> {
    match value {
        Value::Int(number) => Ok(number),
        bad => Err(type_error(Ty::int(), &bad, span)),
    }
}

fn expect_bool(value: Value, span: Span) -> Result<bool, Control> {
    match value {
        Value::Bool(boolean) => Ok(boolean),
        bad => Err(type_error(Ty::bool(), &bad, span)),
    }
}

/// Apply an eager operator after both operands have evaluated successfully.
fn eval_binary(op: BinOp, left: Value, right: Value, span: Span) -> Result<Value, Control> {
    match op {
        BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Div
        | BinOp::Mod
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Gt
        | BinOp::Ge => {
            let left = expect_int(left, span)?;
            let right = expect_int(right, span)?;
            if matches!(op, BinOp::Div | BinOp::Mod) && right == 0 {
                return Err(Control::Raise(RuntimeError::DivByZero { span }));
            }
            Ok(match op {
                BinOp::Add => Value::Int(left.wrapping_add(right)),
                BinOp::Sub => Value::Int(left.wrapping_sub(right)),
                BinOp::Mul => Value::Int(left.wrapping_mul(right)),
                BinOp::Div => Value::Int(left.wrapping_div(right)),
                BinOp::Mod => Value::Int(left.wrapping_rem(right)),
                BinOp::Lt => Value::Bool(left < right),
                BinOp::Le => Value::Bool(left <= right),
                BinOp::Gt => Value::Bool(left > right),
                BinOp::Ge => Value::Bool(left >= right),
                _ => unreachable!("integer operators are matched above"),
            })
        }
        BinOp::Eq => Ok(Value::Bool(left == right)),
        BinOp::Ne => Ok(Value::Bool(left != right)),
        BinOp::Concat => match (left, right) {
            (Value::Str(left), Value::Str(right)) => {
                Ok(Value::Str(Rc::from(format!("{left}{right}"))))
            }
            (Value::List(left), Value::List(right)) => Ok(Value::List(left.concat(&right))),
            (Value::Str(_), bad) => Err(type_error(Ty::str(), &bad, span)),
            (Value::List(_), bad) => Err(type_error(Ty::list(Ty::unit()), &bad, span)),
            (bad, _) => Err(type_error(Ty::str(), &bad, span)),
        },
        BinOp::Cons => match right {
            Value::List(tail) => Ok(Value::List(List::cons(left, tail))),
            bad => Err(type_error(Ty::list(Ty::unit()), &bad, span)),
        },
        BinOp::And | BinOp::Or => unreachable!("short-circuit operators are handled in eval_expr"),
    }
}
