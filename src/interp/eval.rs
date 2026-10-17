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

use super::{type_of, Closure, Interpreter, RuntimeError};
use super::{Control, Env, Loc, Value};
use crate::ast::{BinOp, Expr, Lit, Span, Stmt, Ty, UnOp};
use crate::interp::value::{uncomparable, List};
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
                UnOp::Ref => {
                    let value = self.eval_expr(expr, env)?;
                    Ok(Value::Ref(self.store.alloc(value)))
                }
                UnOp::Deref => {
                    let loc = expect_ref(self.eval_expr(expr, env)?, *span)?;
                    Ok(self.store.read(loc))
                }
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
            Expr::Var(name, span) => env.lookup(name).ok_or_else(|| {
                Control::Raise(RuntimeError::UnboundVariable {
                    name: name.clone(),
                    span: *span,
                })
            }),
            Expr::Block(stmts, tail, _) => {
                let mut local_env = env.clone();

                for stmt in stmts {
                    match stmt {
                        Stmt::Let(name, _, expr, _) => {
                            local_env =
                                local_env.extend(name.clone(), self.eval_expr(expr, &local_env)?);
                        }
                        Stmt::Expr(expr) => {
                            self.eval_expr(expr, &local_env)?;
                        }
                    };
                }

                match tail {
                    Some(tail) => self.eval_expr(tail, &local_env),
                    None => Ok(Value::Unit),
                }
            }

            // ---- M3: state & control ----
            Expr::If(cond, then_br, else_br, span) => {
                let cond_value = expect_bool(self.eval_expr(cond, env)?, *span)?;
                if cond_value {
                    self.eval_expr(then_br, env)
                } else {
                    match else_br {
                        Some(else_br) => self.eval_expr(else_br, env),
                        None => Ok(Value::Unit),
                    }
                }
            }
            Expr::While(cond, body, span) => loop {
                let cond_value = expect_bool(self.eval_expr(cond, env)?, *span)?;
                if !cond_value {
                    break Ok(Value::Unit);
                }
                self.eval_expr(body, env)?;
            },
            Expr::For(name, itr, body, span) => {
                let itr_value = expect_list(self.eval_expr(itr, env)?, *span)?;
                for item in &itr_value {
                    let local_env = env.extend(name.clone(), item.clone());
                    self.eval_expr(body, &local_env)?;
                }
                Ok(Value::Unit)
            }
            Expr::Assign(target, expr, span) => {
                let loc = expect_ref(self.eval_expr(target, env)?, *span)?;
                let value = self.eval_expr(expr, env)?;
                self.store.write(loc, value);
                Ok(Value::Unit)
            }
            Expr::Return(expr, _) => Err(Control::Return(self.eval_expr(expr, env)?)),

            // ---- M4: functions ----
            Expr::Lambda(params, body, _) => Ok(Value::Closure(Rc::from(Closure::Bridger {
                params: params.iter().map(|param| param.name.clone()).collect(),
                body: body.as_ref().clone(),
                env: env.clone(),
            }))),
            Expr::Call(operator, args, span) => match self.eval_expr(operator, env)? {
                Value::Closure(closure) => {
                    let arg_values = self.eval_elements(args, env)?;
                    match closure.as_ref() {
                        Closure::Native(builtin_id) => self
                            .eval_prelude(*builtin_id, arg_values, *span)
                            .map_err(Control::Raise),
                        Closure::Bridger {
                            params,
                            body,
                            env: captured_env,
                        } => {
                            if arg_values.len() != params.len() {
                                return Err(Control::Raise(RuntimeError::ArityMismatch {
                                    expected: params.len(),
                                    found: arg_values.len(),
                                    span: *span,
                                }));
                            }

                            let mut local_env = captured_env.clone();
                            for (param, arg_value) in params.iter().zip(arg_values) {
                                local_env = local_env.extend(param.clone(), arg_value);
                            }

                            self.enter_call(*span).map_err(Control::Raise)?;
                            let outcome = self.eval_expr(body, &local_env);
                            self.leave_call();
                            match outcome {
                                Ok(value) => Ok(value),
                                Err(control) => match control {
                                    Control::Return(value) => Ok(value),
                                    Control::Raise(error) => Err(Control::from(error)),
                                },
                            }
                        }
                    }
                }
                bad => Err(Control::Raise(RuntimeError::NotAFunction {
                    found: type_of(&bad),
                    span: *span,
                })),
            },

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

fn expect_list(value: Value, span: Span) -> Result<List, Control> {
    match value {
        Value::List(list) => Ok(list),
        bad => Err(type_error(Ty::list(Ty::unit()), &bad, span)),
    }
}

fn expect_ref(value: Value, span: Span) -> Result<Loc, Control> {
    match value {
        Value::Ref(loc) => Ok(loc),
        bad => Err(type_error(Ty::reference(Ty::unit()), &bad, span)),
    }
}

fn expect_comparable(value: &Value, span: Span) -> Result<(), Control> {
    match uncomparable(value) {
        Some(found) => Err(Control::Raise(RuntimeError::NotComparable { found, span })),
        None => Ok(()),
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
        BinOp::Eq | BinOp::Ne => {
            expect_comparable(&left, span)?;
            expect_comparable(&right, span)?;
            Ok(match op {
                BinOp::Eq => Value::Bool(left == right),
                BinOp::Ne => Value::Bool(left != right),
                _ => unreachable!("equality operators are matched above"),
            })
        }
        BinOp::Concat => match (left, right) {
            (Value::Str(left), Value::Str(right)) => {
                Ok(Value::Str(Rc::from(format!("{left}{right}"))))
            }
            (Value::List(left), Value::List(right)) => Ok(Value::List(left.concat(&right))),
            (Value::Str(_), bad) => Err(type_error(Ty::str(), &bad, span)),
            (Value::List(_), bad) => Err(type_error(Ty::list(Ty::unit()), &bad, span)),
            (bad, _) => Err(type_error(Ty::str(), &bad, span)),
        },
        BinOp::Cons => {
            let tail = expect_list(right, span)?;
            Ok(Value::List(List::cons(left, tail)))
        }
        BinOp::And | BinOp::Or => unreachable!("short-circuit operators are handled in eval_expr"),
    }
}
