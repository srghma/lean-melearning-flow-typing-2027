use std::{
    collections::{BTreeMap, VecDeque},
    fmt::{Debug, Display},
};

use logos::Span;

use crate::{
    error::{Diagnostic, Errors},
    out_of_scope::out_of_scope,
    parse::{self, Flow, Literal, PrimOp, PrimTy},
    rename::{self, Decl, TType, Type},
};

pub fn infer<'src>(
    errors: &mut Errors,
    decls: &[Decl<'src>],
    defs: Vec<rename::Def<'src>>,
) -> Vec<Def<'src>> {
    let mut output = Vec::new();
    for def in defs {
        let mut ctx = Ctx::default();
        let expected = decls
            .iter()
            .find(|decl| decl.name == def.name)
            .map(|decl| decl.ty.clone().into())
            .unwrap_or_else(|| ctx.gen_mvar(def.span.clone()));
        let mut unify_errors = Vec::new();
        let body = infer_expr(
            decls,
            errors,
            &mut unify_errors,
            &mut ctx,
            rename::Expr::Lambda {
                patterns: def.patterns,
                body: Box::new(def.expr),
                span: def.span.clone(),
            },
            expected,
        );

        // Unification errors are not emitted until we have the most information possible
        // to print the best error message possible.
        for error in unify_errors {
            errors.push(Diagnostic::error(
                error.span,
                format!(
                    "could not unify {} with {}",
                    ctx.tsubst(error.expected),
                    ctx.tsubst(error.actual)
                ),
            ));
        }

        if let Some(body) = body.and_then(|body| ctx.esubst(errors, body)) {
            output.push(Def {
                name: def.name,
                span: def.span,
                expr: body,
            });
        }
    }

    output
}

/// Extracts the outermost '~' from this expression.
fn expr_to_expr_or_lens<'src>(expr: rename::Expr<'src>) -> (Flow, rename::Expr<'src>) {
    match expr {
        rename::Expr::Tilde(expr, _) => (Flow::Flow, *expr),
        expr => (Flow::Plain, expr),
    }
}

fn literal_ty<'src>(literal: &Literal, span: Span) -> IType<'src> {
    match literal {
        Literal::Integer(_) => IType::Prim(PrimTy::Int, span),
        Literal::Bool(_) => IType::Prim(PrimTy::Bool, span),
        Literal::Char(_) => IType::Prim(PrimTy::Char, span),
    }
}

fn infer_expr<'src>(
    decls: &[Decl<'src>],
    errors: &mut Errors,
    unify_errors: &mut Vec<UnifyError<'src>>,
    ctx: &mut Ctx<'src>,
    expr: rename::Expr<'src>,
    expected: IType<'src>,
) -> Option<IExpr<'src>> {
    match expr {
        rename::Expr::Var(index, span) => {
            match ctx
                .vars
                .get_mut(index)
                .expect("de Bruijn indexing failed")
                .1
                .take()
            {
                Some(ty) => {
                    ctx.unify(unify_errors, span.clone(), expected, ty);
                }
                None => errors.push(Diagnostic::error(
                    span.clone(),
                    "variable used twice".to_owned(),
                )),
            }
            Some(IExpr::Var(index, span))
        }
        rename::Expr::Inst(name, span) => match decls.iter().find(|decl| decl.name == name) {
            Some(decl) => {
                let subst = decl
                    .ty_vars()
                    .into_iter()
                    .map(|var| (var, ctx.gen_mvar(span.clone())))
                    .collect();
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    expected,
                    IType::from(decl.ty.clone()).subst(&subst),
                );
                Some(IExpr::Inst { name, subst, span })
            }
            None => {
                errors.push(Diagnostic::error(
                    span,
                    "could not find definition".to_owned(),
                ));
                None
            }
        },
        rename::Expr::Tilde(_, span) => {
            errors.push(Diagnostic::error(span, "'~' not allowed here".to_owned()));
            None
        }
        rename::Expr::App(left, right, span) => {
            let (flow, right) = expr_to_expr_or_lens(*right);
            let arg = ctx.gen_mvars(right.span(), flow);
            let left = infer_expr(
                decls,
                errors,
                unify_errors,
                ctx,
                *left,
                IType::Arrow(
                    Box::new(arg.clone()),
                    Box::new(ITType::Plain(expected)),
                    span.clone(),
                ),
            )?;
            let right = match arg {
                ITType::Plain(arg) => {
                    IExprOrLens::Expr(infer_expr(decls, errors, unify_errors, ctx, right, arg)?)
                }
                ITType::Flow(arg1, arg2) => IExprOrLens::Lens(infer_lens(
                    decls,
                    errors,
                    unify_errors,
                    ctx,
                    right,
                    arg1,
                    arg2,
                )?),
            };
            Some(IExpr::App(Box::new(left), Box::new(right), span))
        }
        rename::Expr::Assign(left, right, span) => {
            let ty = ctx.gen_mvar(right.span());
            let right = infer_expr(decls, errors, unify_errors, ctx, *right, ty.clone())?;
            let left = infer_lens(decls, errors, unify_errors, ctx, *left, expected, ty)?;
            Some(IExpr::Assign(Box::new(left), Box::new(right), span))
        }
        rename::Expr::Literal(literal, span) => {
            ctx.unify(
                unify_errors,
                span.clone(),
                expected,
                literal_ty(&literal, span.clone()),
            );
            Some(IExpr::Literal(literal, span))
        }
        rename::Expr::PrimOp(left, right, prim_op, span) => {
            let (left_ty, right_ty) = match prim_op {
                PrimOp::Add | PrimOp::Sub | PrimOp::Mul | PrimOp::Div => {
                    ctx.unify(
                        unify_errors,
                        span.clone(),
                        expected,
                        IType::Prim(PrimTy::Int, span.clone()),
                    );
                    (
                        IType::Prim(PrimTy::Int, span.clone()),
                        IType::Prim(PrimTy::Int, span.clone()),
                    )
                }
                PrimOp::Eq => {
                    // We don't check to see if the left and right sides are actually comparable.
                    let ty = ctx.gen_mvar(left.span());
                    ctx.unify(
                        unify_errors,
                        span.clone(),
                        expected,
                        IType::Prim(PrimTy::Bool, span.clone()),
                    );
                    (ty.clone(), ty)
                }
                PrimOp::Seq => (IType::Tuple(Vec::new(), span.clone()), expected),
            };
            let left = infer_expr(decls, errors, unify_errors, ctx, *left, left_ty)?;
            let right = infer_expr(decls, errors, unify_errors, ctx, *right, right_ty)?;
            Some(IExpr::PrimOp(
                Box::new(left),
                Box::new(right),
                prim_op,
                span,
            ))
        }
        rename::Expr::Tuple(exprs, span) => {
            let tys = exprs
                .iter()
                .map(|expr| ctx.gen_mvar(expr.span()))
                .collect::<Vec<_>>();
            ctx.unify(
                unify_errors,
                span.clone(),
                expected,
                IType::Tuple(tys.clone(), span.clone()),
            );
            let exprs = exprs
                .into_iter()
                .zip(tys)
                .filter_map(|(expr, ty)| infer_expr(decls, errors, unify_errors, ctx, expr, ty))
                .collect();
            Some(IExpr::Tuple(exprs, span))
        }
        rename::Expr::EmptyList(span) => {
            let mvar = ctx.gen_mvar(span.clone());
            ctx.unify(
                unify_errors,
                span.clone(),
                expected,
                IType::List(Box::new(mvar), span.clone()),
            );
            Some(IExpr::EmptyList(span))
        }
        rename::Expr::Cons(head, tail, span) => {
            let mvar = ctx.gen_mvar(span.clone());
            ctx.unify(
                unify_errors,
                span.clone(),
                expected,
                IType::List(Box::new(mvar.clone()), span.clone()),
            );
            let head = infer_expr(decls, errors, unify_errors, ctx, *head, mvar.clone())?;
            let tail = infer_expr(
                decls,
                errors,
                unify_errors,
                ctx,
                *tail,
                IType::List(Box::new(mvar.clone()), span.clone()),
            )?;
            Some(IExpr::Cons(Box::new(head), Box::new(tail), span))
        }
        rename::Expr::Let {
            flow,
            pattern,
            value,
            body,
            span,
        } => {
            let ty = ctx.gen_mvars(span.clone(), flow);
            let value = match ty.clone() {
                ITType::Plain(ty) => {
                    IExprOrLens::Expr(infer_expr(decls, errors, unify_errors, ctx, *value, ty)?)
                }
                ITType::Flow(ty1, ty2) => IExprOrLens::Lens(infer_lens(
                    decls,
                    errors,
                    unify_errors,
                    ctx,
                    *value,
                    ty1,
                    ty2,
                )?),
            };
            let pattern = elaborate_pat(unify_errors, ctx, ty, pattern);
            ctx.extend(&pattern);
            let body = infer_expr(decls, errors, unify_errors, ctx, *body, expected)?;
            ctx.retract(errors, unify_errors, &pattern);
            if let IExprOrLens::Lens(lens) = &value {
                let body_vars = body
                    .fvars()
                    .into_iter()
                    .filter_map(|x| x.checked_sub(pattern.vars()));
                check_scrutinee_split(errors, ctx, lens, body_vars);
            }

            Some(IExpr::Let {
                pattern,
                value: Box::new(value),
                body: Box::new(body),
                span,
            })
        }
        rename::Expr::Case {
            flow,
            scrutinee,
            branches,
            span,
        } => {
            let ty = ctx.gen_mvars(span.clone(), flow);
            let scrutinee = match ty.clone() {
                ITType::Plain(ty) => IExprOrLens::Expr(infer_expr(
                    decls,
                    errors,
                    unify_errors,
                    ctx,
                    *scrutinee,
                    ty,
                )?),
                ITType::Flow(ty1, ty2) => IExprOrLens::Lens(infer_lens(
                    decls,
                    errors,
                    unify_errors,
                    ctx,
                    *scrutinee,
                    ty1,
                    ty2,
                )?),
            };

            let mut new_branches = Vec::new();
            let mut after_vars = None::<VecDeque<(Span, Option<IType>)>>;
            for (pat, branch) in branches {
                let vars = ctx.vars.clone();
                let pat = elaborate_pat(unify_errors, ctx, ty.clone(), pat);
                ctx.extend(&pat);
                let branch =
                    infer_expr(decls, errors, unify_errors, ctx, branch, expected.clone())?;
                ctx.retract(errors, unify_errors, &pat);

                for ((left_span, left_ty), (_, right_ty)) in
                    ctx.vars.clone().iter().zip(after_vars.iter().flatten())
                {
                    match (left_ty, right_ty) {
                        (None, None) => {}
                        (Some(left), Some(right)) => {
                            ctx.unify(unify_errors, span.clone(), left.clone(), right.clone());
                        }
                        _ => {
                            errors.push(Diagnostic::error(
                                left_span.clone(),
                                "variable not used consistently across branches".to_owned(),
                            ));
                        }
                    }
                }
                after_vars = Some(std::mem::replace(&mut ctx.vars, vars));
                new_branches.push((pat, branch))
            }
            ctx.vars = after_vars.expect("empty case not allowed");
            if let IExprOrLens::Lens(lens) = &scrutinee {
                let body_vars = new_branches
                    .iter()
                    .flat_map(|(pat, branch): &(IPattern, IExpr)| {
                        branch
                            .fvars()
                            .into_iter()
                            .filter_map(|x| x.checked_sub(pat.vars()))
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>();
                check_scrutinee_split(errors, ctx, lens, body_vars);
            }

            Some(IExpr::Case {
                scrutinee: Box::new(scrutinee),
                branches: new_branches,
                span,
            })
        }
        rename::Expr::Lambda {
            patterns,
            body,
            span,
        } => {
            for (flow, pattern) in &patterns[..patterns.len().saturating_sub(1)] {
                if *flow == Flow::Flow {
                    errors.push(Diagnostic::error(
                        pattern.span(),
                        "only the last parameter can use a flow pattern".to_string(),
                    ));
                }
            }
            let (flow_body, body) = expr_to_expr_or_lens(*body);
            let body_ty = ctx.gen_mvars(body.span(), flow_body);
            let mut lambda_ty = body_ty.clone();
            let mut elab_patterns = Vec::new();
            for (flow, pattern) in patterns.into_iter().rev() {
                match flow {
                    Flow::Plain => {
                        let arg_ty = ctx.gen_mvar(span.clone());
                        elab_patterns.push((
                            Flow::Plain,
                            elaborate_pat(
                                unify_errors,
                                ctx,
                                ITType::Plain(arg_ty.clone()),
                                pattern,
                            ),
                        ));
                        lambda_ty = ITType::Plain(IType::Arrow(
                            Box::new(ITType::Plain(arg_ty)),
                            Box::new(lambda_ty),
                            span.clone(),
                        ));
                    }
                    Flow::Flow => {
                        let arg_ty1 = ctx.gen_mvar(span.clone());
                        let arg_ty2 = ctx.gen_mvar(span.clone());
                        elab_patterns.push((
                            Flow::Flow,
                            elaborate_pat(
                                unify_errors,
                                ctx,
                                ITType::Flow(arg_ty1.clone(), arg_ty2.clone()),
                                pattern,
                            ),
                        ));
                        lambda_ty = ITType::Plain(IType::Arrow(
                            Box::new(ITType::Flow(arg_ty1, arg_ty2)),
                            Box::new(lambda_ty),
                            span.clone(),
                        ));
                    }
                }
            }
            ctx.tunify(
                unify_errors,
                span.clone(),
                ITType::Plain(expected),
                lambda_ty,
            );

            elab_patterns.reverse();

            for (_, pattern) in &elab_patterns {
                ctx.extend(pattern);
            }

            let body = match body_ty {
                ITType::Plain(body_ty) => {
                    IExprOrLens::Expr(infer_expr(decls, errors, unify_errors, ctx, body, body_ty)?)
                }
                ITType::Flow(body_ty1, body_ty2) => IExprOrLens::Lens(infer_lens(
                    decls,
                    errors,
                    unify_errors,
                    ctx,
                    body,
                    body_ty1,
                    body_ty2,
                )?),
            };

            for (_, pattern) in elab_patterns.iter().rev() {
                ctx.retract(errors, unify_errors, pattern);
            }

            // Rules (-o)-I and ~(-o)-I: the variables captured by a lambda (plain or flow)
            // are handed over to the closure and must be dead at the end of its body.
            let pattern_vars = elab_patterns
                .iter()
                .map(|(_, pattern)| pattern.vars())
                .sum::<usize>();
            let mut captured = body
                .fvars()
                .into_iter()
                .filter_map(|x| x.checked_sub(pattern_vars))
                .collect::<Vec<_>>();
            captured.sort();
            captured.dedup();
            for var in captured {
                if let (var_span, Some(ty)) = &ctx.vars[var] {
                    errors.push(Diagnostic::error(
                        var_span.clone(),
                        format!(
                            "this variable is captured by a lambda, but still has type {} at the end of the lambda's body; variables captured by a lambda must be used up inside it",
                            ctx.subst(ty.clone())
                        ),
                    ));
                }
            }

            let result = elab_patterns
                .into_iter()
                .rev()
                .fold(body, |body, (flow, pattern)| {
                    IExprOrLens::Expr(IExpr::Lambda {
                        flow,
                        pattern,
                        body: Box::new(body),
                        span: span.clone(),
                    })
                });

            match result {
                IExprOrLens::Expr(expr) => Some(expr),
                IExprOrLens::Lens(_) => {
                    errors.push(Diagnostic::error(
                        span,
                        "empty lambdas are not allowed".to_owned(),
                    ));
                    None
                }
            }
        }
        rename::Expr::Left(expr, span) => {
            let mvar = ctx.gen_mvar(span.clone());
            let other_mvar = ctx.gen_mvar(span.clone());
            ctx.unify(
                unify_errors,
                span.clone(),
                expected,
                IType::Either(
                    Box::new(mvar.clone()),
                    Box::new(other_mvar.clone()),
                    span.clone(),
                ),
            );
            let expr = infer_expr(decls, errors, unify_errors, ctx, *expr, mvar.clone())?;
            Some(IExpr::Left(Box::new(expr), span))
        }
        rename::Expr::Right(expr, span) => {
            let mvar = ctx.gen_mvar(span.clone());
            let other_mvar = ctx.gen_mvar(span.clone());
            ctx.unify(
                unify_errors,
                span.clone(),
                expected,
                IType::Either(
                    Box::new(other_mvar.clone()),
                    Box::new(mvar.clone()),
                    span.clone(),
                ),
            );
            let expr = infer_expr(decls, errors, unify_errors, ctx, *expr, mvar.clone())?;
            Some(IExpr::Right(Box::new(expr), span))
        }
    }
}

fn infer_lens<'src>(
    decls: &[Decl<'src>],
    errors: &mut Errors,
    unify_errors: &mut Vec<UnifyError<'src>>,
    ctx: &mut Ctx<'src>,
    lens: rename::Expr<'src>,
    expected1: IType<'src>,
    expected2: IType<'src>,
) -> Option<ILens<'src>> {
    match lens {
        rename::Expr::Var(index, span) => {
            match &mut ctx
                .vars
                .get_mut(index)
                .expect("de Bruijn indexing failed")
                .1
            {
                Some(ty) => {
                    let ty = std::mem::replace(ty, expected2.clone());
                    ctx.unify(unify_errors, span.clone(), expected1, ty);
                    Some(ILens::Var(index, expected2, span))
                }
                ty @ None => {
                    *ty = Some(expected2.clone());
                    ctx.unify(
                        unify_errors,
                        span.clone(),
                        expected1,
                        IType::Tuple(Vec::new(), span.clone()),
                    );
                    Some(ILens::Var(index, expected2, span))
                }
            }
        }
        rename::Expr::Inst(..) => out_of_scope!(),
        rename::Expr::Tilde(_, span) => {
            errors.push(Diagnostic::error(span, "'~' not allowed here".to_owned()));
            None
        }
        rename::Expr::App(left, right, span) => {
            let (flow, right) = expr_to_expr_or_lens(*right);
            let arg = ctx.gen_mvars(right.span(), flow);
            let left = infer_expr(
                decls,
                errors,
                unify_errors,
                ctx,
                *left,
                IType::Arrow(
                    Box::new(arg.clone()),
                    Box::new(ITType::Flow(expected1, expected2)),
                    span.clone(),
                ),
            )?;
            let right = match arg {
                ITType::Plain(arg) => {
                    IExprOrLens::Expr(infer_expr(decls, errors, unify_errors, ctx, right, arg)?)
                }
                ITType::Flow(arg1, arg2) => IExprOrLens::Lens(infer_lens(
                    decls,
                    errors,
                    unify_errors,
                    ctx,
                    right,
                    arg1,
                    arg2,
                )?),
            };
            Some(ILens::App(Box::new(left), Box::new(right), span))
        }
        rename::Expr::Assign(..) => out_of_scope!(),
        rename::Expr::Literal(_, span) => {
            // A literal is not a lens term: there is nowhere to put the value written back
            // through it, so the paper's type system has no rule for it.
            errors.push(Diagnostic::error(
                span,
                "a literal cannot be used as a lens term ('~' needs a variable, tuple or application)"
                    .to_owned(),
            ));
            None
        }
        rename::Expr::PrimOp(..) => out_of_scope!(),
        rename::Expr::Tuple(exprs, span) => {
            let tys1 = exprs
                .iter()
                .map(|expr| ctx.gen_mvar(expr.span()))
                .collect::<Vec<_>>();
            let tys2 = exprs
                .iter()
                .map(|expr| ctx.gen_mvar(expr.span()))
                .collect::<Vec<_>>();
            ctx.unify(
                unify_errors,
                span.clone(),
                expected1,
                IType::Tuple(tys1.clone(), span.clone()),
            );
            ctx.unify(
                unify_errors,
                span.clone(),
                expected2,
                IType::Tuple(tys2.clone(), span.clone()),
            );
            let exprs = exprs
                .into_iter()
                .zip(tys1.into_iter().zip(tys2))
                .filter_map(|(expr, (ty1, ty2))| {
                    infer_lens(decls, errors, unify_errors, ctx, expr, ty1, ty2)
                })
                .collect::<Vec<_>>();
            // The rule ~(x)-I splits the context between the components of a lens tuple,
            // so no variable may be mentioned by more than one component.
            let mut seen = Vec::<usize>::new();
            for item in &exprs {
                let mut vars = item.fvars();
                vars.sort();
                vars.dedup();
                for var in vars {
                    if seen.contains(&var) {
                        errors.push(Diagnostic::error(
                            item.span(),
                            "variable used in more than one component of a lens tuple".to_owned(),
                        ));
                    } else {
                        seen.push(var);
                    }
                }
            }
            Some(ILens::Tuple(exprs, span))
        }
        rename::Expr::EmptyList(_) => out_of_scope!(),
        rename::Expr::Cons(..) => out_of_scope!(),
        rename::Expr::Let { .. } => out_of_scope!(),
        rename::Expr::Case { .. } => out_of_scope!(),
        rename::Expr::Lambda { .. } => out_of_scope!(),
        rename::Expr::Left(..) => out_of_scope!(),
        rename::Expr::Right(..) => out_of_scope!(),
    }
}

fn elaborate_pat<'src>(
    unify_errors: &mut Vec<UnifyError<'src>>,
    ctx: &mut Ctx<'src>,
    ty: ITType<'src>,
    pat: parse::Pattern<'src>,
) -> IPattern<'src> {
    match pat {
        parse::Pattern::Literal(literal, span) => {
            ctx.tunify(
                unify_errors,
                span.clone(),
                ty,
                ITType::Plain(literal_ty(&literal, span.clone())),
            );
            IPattern::Literal(literal, span)
        }
        parse::Pattern::Var(name, span) => IPattern::Var(name, ty, span),
        parse::Pattern::Tuple(pats, span) => match ty {
            ITType::Plain(ty) => {
                let (tys, pats) = pats
                    .into_iter()
                    .map(|pat| {
                        let pat_ty = ctx.gen_mvar(span.clone());
                        (
                            pat_ty.clone(),
                            elaborate_pat(unify_errors, ctx, ITType::Plain(pat_ty), pat),
                        )
                    })
                    .unzip();
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty,
                    IType::Tuple(tys, span.clone()),
                );
                IPattern::Tuple(pats, span)
            }
            ITType::Flow(ty1, ty2) => {
                let mut tys1 = Vec::new();
                let mut tys2 = Vec::new();
                let pats = pats
                    .into_iter()
                    .map(|pat| {
                        let pat_ty1 = ctx.gen_mvar(span.clone());
                        let pat_ty2 = ctx.gen_mvar(span.clone());
                        tys1.push(pat_ty1.clone());
                        tys2.push(pat_ty2.clone());
                        elaborate_pat(unify_errors, ctx, ITType::Flow(pat_ty1, pat_ty2), pat)
                    })
                    .collect();
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty1,
                    IType::Tuple(tys1, span.clone()),
                );
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty2,
                    IType::Tuple(tys2, span.clone()),
                );
                IPattern::Tuple(pats, span)
            }
        },
        parse::Pattern::EmptyList(span) => {
            match ty {
                ITType::Plain(ty) => {
                    let mvar = ctx.gen_mvar(span.clone());
                    ctx.unify(
                        unify_errors,
                        span.clone(),
                        ty,
                        IType::List(Box::new(mvar), span.clone()),
                    );
                }
                ITType::Flow(ty1, ty2) => {
                    let mvar1 = ctx.gen_mvar(span.clone());
                    let mvar2 = ctx.gen_mvar(span.clone());
                    ctx.unify(
                        unify_errors,
                        span.clone(),
                        ty1,
                        IType::List(Box::new(mvar1), span.clone()),
                    );
                    ctx.unify(
                        unify_errors,
                        span.clone(),
                        ty2,
                        IType::List(Box::new(mvar2), span.clone()),
                    );
                }
            }
            IPattern::EmptyList(span)
        }
        parse::Pattern::Cons(head, tail, span) => match ty {
            ITType::Plain(ty) => {
                let mvar = ctx.gen_mvar(span.clone());
                let head = elaborate_pat(unify_errors, ctx, ITType::Plain(mvar.clone()), *head);
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty.clone(),
                    IType::List(Box::new(mvar), span.clone()),
                );
                let tail = elaborate_pat(unify_errors, ctx, ITType::Plain(ty), *tail);
                IPattern::Cons(Box::new(head), Box::new(tail), span)
            }
            ITType::Flow(ty1, ty2) => {
                let mvar1 = ctx.gen_mvar(span.clone());
                let mvar2 = ctx.gen_mvar(span.clone());
                let head = elaborate_pat(
                    unify_errors,
                    ctx,
                    ITType::Flow(mvar1.clone(), mvar2.clone()),
                    *head,
                );
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty1.clone(),
                    IType::List(Box::new(mvar1), span.clone()),
                );
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty2.clone(),
                    IType::List(Box::new(mvar2), span.clone()),
                );
                let tail = elaborate_pat(unify_errors, ctx, ITType::Flow(ty1, ty2), *tail);
                IPattern::Cons(Box::new(head), Box::new(tail), span)
            }
        },
        parse::Pattern::Left(pat, span) => match ty {
            ITType::Plain(ty) => {
                let left_mvar = ctx.gen_mvar(span.clone());
                let right_mvar = ctx.gen_mvar(span.clone());
                let pat = elaborate_pat(unify_errors, ctx, ITType::Plain(left_mvar.clone()), *pat);
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty.clone(),
                    IType::Either(Box::new(left_mvar), Box::new(right_mvar), span.clone()),
                );
                IPattern::Left(Box::new(pat), span)
            }
            ITType::Flow(ty1, ty2) => {
                let left_mvar1 = ctx.gen_mvar(span.clone());
                let left_mvar2 = ctx.gen_mvar(span.clone());
                let right_mvar1 = ctx.gen_mvar(span.clone());
                let right_mvar2 = ctx.gen_mvar(span.clone());
                let pat = elaborate_pat(
                    unify_errors,
                    ctx,
                    ITType::Flow(left_mvar1.clone(), left_mvar2.clone()),
                    *pat,
                );
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty1.clone(),
                    IType::Either(Box::new(left_mvar1), Box::new(right_mvar1), span.clone()),
                );
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty2.clone(),
                    IType::Either(Box::new(left_mvar2), Box::new(right_mvar2), span.clone()),
                );
                IPattern::Left(Box::new(pat), span)
            }
        },
        parse::Pattern::Right(pat, span) => match ty {
            ITType::Plain(ty) => {
                let left_mvar = ctx.gen_mvar(span.clone());
                let right_mvar = ctx.gen_mvar(span.clone());
                let pat = elaborate_pat(unify_errors, ctx, ITType::Plain(right_mvar.clone()), *pat);
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty.clone(),
                    IType::Either(Box::new(left_mvar), Box::new(right_mvar), span.clone()),
                );
                IPattern::Right(Box::new(pat), span)
            }
            ITType::Flow(ty1, ty2) => {
                let left_mvar1 = ctx.gen_mvar(span.clone());
                let left_mvar2 = ctx.gen_mvar(span.clone());
                let right_mvar1 = ctx.gen_mvar(span.clone());
                let right_mvar2 = ctx.gen_mvar(span.clone());
                let pat = elaborate_pat(
                    unify_errors,
                    ctx,
                    ITType::Flow(right_mvar1.clone(), right_mvar2.clone()),
                    *pat,
                );
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty1.clone(),
                    IType::Either(Box::new(left_mvar1), Box::new(right_mvar1), span.clone()),
                );
                ctx.unify(
                    unify_errors,
                    span.clone(),
                    ty2.clone(),
                    IType::Either(Box::new(left_mvar2), Box::new(right_mvar2), span.clone()),
                );
                IPattern::Right(Box::new(pat), span)
            }
        },
    }
}

#[derive(Debug, Clone)]
pub struct Def<'src> {
    pub name: &'src str,
    pub span: Span,
    pub expr: Expr<'src>,
}

#[derive(Debug, Clone)]
pub enum ExprOrLens<'src> {
    Expr(Expr<'src>),
    Lens(Lens<'src>),
}

impl<'src> ExprOrLens<'src> {
    /// Possibly contains duplicates. A list of free variables.
    pub fn fvars(&self) -> Vec<usize> {
        match self {
            ExprOrLens::Expr(expr) => expr.fvars(),
            ExprOrLens::Lens(lens) => lens.fvars(),
        }
    }
}

#[derive(Debug, Clone)]
enum IExprOrLens<'src> {
    Expr(IExpr<'src>),
    Lens(ILens<'src>),
}

impl<'src> IExprOrLens<'src> {
    /// Possibly contains duplicates. A list of free variables.
    fn fvars(&self) -> Vec<usize> {
        match self {
            IExprOrLens::Expr(expr) => expr.fvars(),
            IExprOrLens::Lens(lens) => lens.fvars(),
        }
    }
}

impl<'src> IExpr<'src> {
    /// Possibly contains duplicates. A list of free variables.
    fn fvars(&self) -> Vec<usize> {
        match self {
            IExpr::Var(i, _) => vec![*i],
            IExpr::Inst { .. } => Vec::new(),
            IExpr::App(left, right, _) => left.fvars().into_iter().chain(right.fvars()).collect(),
            IExpr::Assign(left, right, _) => {
                left.fvars().into_iter().chain(right.fvars()).collect()
            }
            IExpr::Literal(_, _) => Vec::new(),
            IExpr::PrimOp(left, right, _, _) => {
                left.fvars().into_iter().chain(right.fvars()).collect()
            }
            IExpr::Tuple(exprs, _) => exprs.iter().flat_map(|expr| expr.fvars()).collect(),
            IExpr::EmptyList(_) => Vec::new(),
            IExpr::Cons(head, tail, _) => head.fvars().into_iter().chain(tail.fvars()).collect(),
            IExpr::Case {
                scrutinee,
                branches,
                ..
            } => scrutinee
                .fvars()
                .into_iter()
                .chain(branches.iter().flat_map(|(pat, branch)| {
                    branch
                        .fvars()
                        .into_iter()
                        .filter_map(|x| x.checked_sub(pat.vars()))
                }))
                .collect(),
            IExpr::Let {
                pattern,
                value,
                body,
                ..
            } => value
                .fvars()
                .into_iter()
                .chain(
                    body.fvars()
                        .into_iter()
                        .filter_map(|x| x.checked_sub(pattern.vars())),
                )
                .collect(),
            IExpr::Lambda { pattern, body, .. } => body
                .fvars()
                .into_iter()
                .filter_map(|x| x.checked_sub(pattern.vars()))
                .collect(),
            IExpr::Left(expr, _) => expr.fvars(),
            IExpr::Right(expr, _) => expr.fvars(),
        }
    }
}

impl<'src> ILens<'src> {
    /// Possibly contains duplicates. A list of free variables.
    fn fvars(&self) -> Vec<usize> {
        match self {
            ILens::Var(n, _, _) => vec![*n],
            ILens::Tuple(items, _) => items.iter().flat_map(|x| x.fvars()).collect(),
            ILens::App(left, right, _) => left.fvars().into_iter().chain(right.fvars()).collect(),
            ILens::Literal(_, _) => Vec::new(),
        }
    }

    fn span(&self) -> Span {
        match self {
            ILens::Var(_, _, span) => span.clone(),
            ILens::Tuple(_, span) => span.clone(),
            ILens::App(_, _, span) => span.clone(),
            ILens::Literal(_, span) => span.clone(),
        }
    }
}

/// Flow typing splits the context between a lens scrutinee `~u` and the body of the
/// `let` or `case` that binds it (rules ~Let, ~(x)-E and ~(+)-E): the body may not mention
/// any variable that the scrutinee mentions. `body_vars` are the free variables of the
/// body(ies), already shifted out of the scope of the pattern variables.
fn check_scrutinee_split<'src>(
    errors: &mut Errors,
    ctx: &Ctx<'src>,
    scrutinee: &ILens<'src>,
    body_vars: impl IntoIterator<Item = usize>,
) {
    let mut scrutinee_vars = scrutinee.fvars();
    scrutinee_vars.sort();
    scrutinee_vars.dedup();
    let mut body_vars = body_vars.into_iter().collect::<Vec<_>>();
    body_vars.sort();
    body_vars.dedup();
    for var in scrutinee_vars {
        if body_vars.contains(&var) {
            errors.push(Diagnostic::error(
                ctx.vars[var].0.clone(),
                "this variable is used in a '~' scrutinee, so it cannot also be used in the body \
                 that the scrutinee's pattern scopes over"
                    .to_owned(),
            ));
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<'src> {
    /// De Bruijn indexed.
    Var(usize, Span),
    Inst {
        name: &'src str,
        subst: BTreeMap<&'src str, Type<'src>>,
        span: Span,
    },
    App(Box<Expr<'src>>, Box<ExprOrLens<'src>>, Span),
    Assign(Box<Lens<'src>>, Box<Expr<'src>>, Span),
    Literal(Literal, Span),
    PrimOp(Box<Expr<'src>>, Box<Expr<'src>>, PrimOp, Span),
    Tuple(Vec<Expr<'src>>, Span),
    EmptyList(Span),
    Cons(Box<Expr<'src>>, Box<Expr<'src>>, Span),
    Left(Box<Expr<'src>>, Span),
    Right(Box<Expr<'src>>, Span),
    Let {
        pattern: Pattern<'src>,
        value: Box<ExprOrLens<'src>>,
        body: Box<Expr<'src>>,
        span: Span,
    },
    Case {
        scrutinee: Box<ExprOrLens<'src>>,
        branches: Vec<(Pattern<'src>, Expr<'src>)>,
        span: Span,
    },
    Lambda {
        flow: Flow,
        pattern: Pattern<'src>,
        body: Box<ExprOrLens<'src>>,
        span: Span,
    },
}

impl<'src> Expr<'src> {
    /// Possibly contains duplicates. A list of free variables.
    pub fn fvars(&self) -> Vec<usize> {
        match self {
            Expr::Var(i, _) => vec![*i],
            Expr::Inst { .. } => Vec::new(),
            Expr::App(left, right, _) => left.fvars().into_iter().chain(right.fvars()).collect(),
            Expr::Assign(left, right, _) => left.fvars().into_iter().chain(right.fvars()).collect(),
            Expr::Literal(_, _) => Vec::new(),
            Expr::PrimOp(left, right, _, _) => {
                left.fvars().into_iter().chain(right.fvars()).collect()
            }
            Expr::Tuple(exprs, _) => exprs.iter().flat_map(|expr| expr.fvars()).collect(),
            Expr::EmptyList(_) => Vec::new(),
            Expr::Cons(head, tail, _) => head.fvars().into_iter().chain(tail.fvars()).collect(),
            Expr::Case {
                scrutinee,
                branches,
                ..
            } => scrutinee
                .fvars()
                .into_iter()
                .chain(branches.iter().flat_map(|(pat, branch)| {
                    branch
                        .fvars()
                        .into_iter()
                        .filter_map(|x| x.checked_sub(pat.vars()))
                }))
                .collect(),
            Expr::Let {
                pattern,
                value,
                body,
                ..
            } => value
                .fvars()
                .into_iter()
                .chain(
                    body.fvars()
                        .into_iter()
                        .filter_map(|x| x.checked_sub(pattern.vars())),
                )
                .collect(),
            Expr::Lambda { pattern, body, .. } => body
                .fvars()
                .into_iter()
                .filter_map(|x| x.checked_sub(pattern.vars()))
                .collect(),
            Expr::Left(expr, _) => expr.fvars(),
            Expr::Right(expr, _) => expr.fvars(),
        }
    }
}

/// Expression during inference.
#[derive(Debug, Clone)]
enum IExpr<'src> {
    /// De Bruijn indexed.
    Var(usize, Span),
    Inst {
        name: &'src str,
        subst: BTreeMap<&'src str, IType<'src>>,
        span: Span,
    },
    App(Box<IExpr<'src>>, Box<IExprOrLens<'src>>, Span),
    Assign(Box<ILens<'src>>, Box<IExpr<'src>>, Span),
    Literal(Literal, Span),
    PrimOp(Box<IExpr<'src>>, Box<IExpr<'src>>, PrimOp, Span),
    Tuple(Vec<IExpr<'src>>, Span),
    EmptyList(Span),
    Cons(Box<IExpr<'src>>, Box<IExpr<'src>>, Span),
    Left(Box<IExpr<'src>>, Span),
    Right(Box<IExpr<'src>>, Span),
    Let {
        pattern: IPattern<'src>,
        value: Box<IExprOrLens<'src>>,
        body: Box<IExpr<'src>>,
        span: Span,
    },
    Case {
        scrutinee: Box<IExprOrLens<'src>>,
        branches: Vec<(IPattern<'src>, IExpr<'src>)>,
        span: Span,
    },
    Lambda {
        flow: Flow,
        pattern: IPattern<'src>,
        body: Box<IExprOrLens<'src>>,
        span: Span,
    },
}

#[derive(Debug, Clone)]
pub enum Lens<'src> {
    /// Contains the updated type.
    Var(usize, Type<'src>, Span),
    Tuple(Vec<Lens<'src>>, Span),
    App(Box<Expr<'src>>, Box<ExprOrLens<'src>>, Span),
    Literal(Literal, Span),
}

impl<'src> Lens<'src> {
    /// Possibly contains duplicates. A list of free variables.
    pub fn fvars(&self) -> Vec<usize> {
        match self {
            Lens::Var(n, _, _) => vec![*n],
            Lens::Tuple(items, _) => items.iter().flat_map(|x| x.fvars()).collect(),
            Lens::App(left, right, _) => left.fvars().into_iter().chain(right.fvars()).collect(),
            Lens::Literal(_, _) => Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
enum ILens<'src> {
    /// Contains the updated type.
    Var(usize, IType<'src>, Span),
    Tuple(Vec<ILens<'src>>, Span),
    App(Box<IExpr<'src>>, Box<IExprOrLens<'src>>, Span),
    Literal(Literal, Span),
}

#[derive(Debug, Clone)]
pub enum Pattern<'src> {
    Var(&'src str, TType<'src>, Span),
    Literal(Literal, Span),
    Tuple(Vec<Pattern<'src>>, Span),
    EmptyList(Span),
    Cons(Box<Pattern<'src>>, Box<Pattern<'src>>, Span),
    Left(Box<Pattern<'src>>, Span),
    Right(Box<Pattern<'src>>, Span),
}

impl<'src> Pattern<'src> {
    pub fn vars(&self) -> usize {
        match self {
            Pattern::Var(_, _, _) => 1,
            Pattern::Literal(_, _) => 0,
            Pattern::Tuple(pats, _) => pats.iter().map(|pat| pat.vars()).sum(),
            Pattern::EmptyList(_) => 0,
            Pattern::Cons(head, tail, _) => head.vars() + tail.vars(),
            Pattern::Left(pat, _) => pat.vars(),
            Pattern::Right(pat, _) => pat.vars(),
        }
    }
}

#[derive(Debug, Clone)]
enum IPattern<'src> {
    Var(&'src str, ITType<'src>, Span),
    Literal(Literal, Span),
    Tuple(Vec<IPattern<'src>>, Span),
    EmptyList(Span),
    Cons(Box<IPattern<'src>>, Box<IPattern<'src>>, Span),
    Left(Box<IPattern<'src>>, Span),
    Right(Box<IPattern<'src>>, Span),
}

impl<'src> IPattern<'src> {
    fn vars(&self) -> usize {
        match self {
            IPattern::Var(_, _, _) => 1,
            IPattern::Literal(_, _) => 0,
            IPattern::Tuple(pats, _) => pats.iter().map(|pat| pat.vars()).sum(),
            IPattern::EmptyList(_) => 0,
            IPattern::Cons(head, tail, _) => head.vars() + tail.vars(),
            IPattern::Left(pat, _) => pat.vars(),
            IPattern::Right(pat, _) => pat.vars(),
        }
    }

    fn span(&self) -> Span {
        match self {
            IPattern::Var(_, _, span) => span.clone(),
            IPattern::Literal(_, span) => span.clone(),
            IPattern::Tuple(_, span) => span.clone(),
            IPattern::EmptyList(span) => span.clone(),
            IPattern::Cons(_, _, span) => span.clone(),
            IPattern::Left(_, span) => span.clone(),
            IPattern::Right(_, span) => span.clone(),
        }
    }
}

#[derive(Clone)]
enum IType<'src> {
    /// Unification metavariables.
    MVar(u32, Span),
    Var(&'src str, Span),
    Prim(PrimTy, Span),
    Arrow(Box<ITType<'src>>, Box<ITType<'src>>, Span),
    Tuple(Vec<IType<'src>>, Span),
    Either(Box<IType<'src>>, Box<IType<'src>>, Span),
    List(Box<IType<'src>>, Span),
    Tree(Box<IType<'src>>, Span),
}

impl<'src> IType<'src> {
    fn span(&self) -> Span {
        match self {
            IType::MVar(_, span) => span.clone(),
            IType::Prim(_, span) => span.clone(),
            IType::Var(_, span) => span.clone(),
            IType::Arrow(_, _, span) => span.clone(),
            IType::Tuple(_, span) => span.clone(),
            IType::Either(_, _, span) => span.clone(),
            IType::List(_, span) => span.clone(),
            IType::Tree(_, span) => span.clone(),
        }
    }

    fn fmt_prec(&self, f: &mut std::fmt::Formatter<'_>, prec: u32) -> std::fmt::Result {
        match self {
            IType::MVar(n, _) => write!(f, "?{n}"),
            IType::Prim(prim_ty, _) => write!(f, "{prim_ty:?}"),
            IType::Var(name, _) => write!(f, "{name}"),
            IType::Arrow(left, right, _) => {
                if prec > 1 {
                    write!(f, "(")?;
                }
                left.fmt_prec(f, 2)?;
                write!(f, " -> ")?;
                right.fmt_prec(f, 1)?;
                if prec > 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            IType::Tuple(items, _) => {
                write!(f, "(")?;
                match items.len() {
                    0 => {}
                    1 => {
                        items.first().unwrap().fmt_prec(f, 0)?;
                        write!(f, ",")?;
                    }
                    _ => {
                        for (i, item) in items.iter().enumerate() {
                            if i != 0 {
                                write!(f, ", ")?;
                            }
                            item.fmt_prec(f, 0)?;
                        }
                    }
                }
                write!(f, ")")
            }
            IType::Either(left, right, _) => {
                if prec > 10 {
                    write!(f, "(")?;
                }
                write!(f, "Either ")?;
                left.fmt_prec(f, 11)?;
                write!(f, " ")?;
                right.fmt_prec(f, 10)?;
                if prec > 10 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            IType::List(t, _) => {
                if prec > 10 {
                    write!(f, "(")?;
                }
                write!(f, "List ")?;
                t.fmt_prec(f, 11)?;
                if prec > 10 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            IType::Tree(t, _) => {
                if prec > 10 {
                    write!(f, "(")?;
                }
                write!(f, "Tree ")?;
                t.fmt_prec(f, 11)?;
                if prec > 10 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }

    fn subst(self, subst: &BTreeMap<&str, Self>) -> Self {
        match self {
            IType::MVar(n, span) => IType::MVar(n, span),
            IType::Prim(prim_ty, span) => IType::Prim(prim_ty, span),
            IType::Var(name, span) => subst.get(name).cloned().unwrap_or(IType::Var(name, span)),
            IType::Arrow(l, r, span) => {
                IType::Arrow(Box::new(l.subst(subst)), Box::new(r.subst(subst)), span)
            }
            IType::Tuple(tys, span) => {
                IType::Tuple(tys.into_iter().map(|ty| ty.subst(subst)).collect(), span)
            }
            IType::Either(l, r, span) => {
                IType::Either(Box::new(l.subst(subst)), Box::new(r.subst(subst)), span)
            }
            IType::List(t, span) => IType::List(Box::new(t.subst(subst)), span),
            IType::Tree(t, span) => IType::Tree(Box::new(t.subst(subst)), span),
        }
    }
}

impl<'src> ITType<'src> {
    fn fmt_prec(&self, f: &mut std::fmt::Formatter<'_>, prec: u32) -> std::fmt::Result {
        match self {
            ITType::Plain(ty) => ty.fmt_prec(f, prec),
            ITType::Flow(ty1, ty2) => {
                if prec > 2 {
                    write!(f, "(")?;
                }
                ty1.fmt_prec(f, 3)?;
                write!(f, "/")?;
                ty2.fmt_prec(f, 3)?;
                if prec > 2 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }

    fn subst(self, subst: &BTreeMap<&str, IType<'src>>) -> Self {
        match self {
            ITType::Plain(ty) => ITType::Plain(ty.subst(subst)),
            ITType::Flow(ty1, ty2) => ITType::Flow(ty1.subst(subst), ty2.subst(subst)),
        }
    }
}

impl<'src> Debug for IType<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, 0)
    }
}

impl<'src> Debug for ITType<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, 0)
    }
}

impl<'src> Display for IType<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, 0)
    }
}

impl<'src> Display for ITType<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, 0)
    }
}

impl<'src> From<rename::Type<'src>> for IType<'src> {
    fn from(value: rename::Type<'src>) -> Self {
        match value {
            rename::Type::Var(name, span) => IType::Var(name, span),
            rename::Type::Prim(prim_ty, span) => IType::Prim(prim_ty, span),
            rename::Type::Arrow(l, r, span) => {
                IType::Arrow(Box::new((*l).into()), Box::new((*r).into()), span)
            }
            rename::Type::Tuple(tys, span) => {
                IType::Tuple(tys.into_iter().map(|ty| ty.into()).collect(), span)
            }
            rename::Type::Either(l, r, span) => {
                IType::Either(Box::new((*l).into()), Box::new((*r).into()), span)
            }
            rename::Type::List(t, span) => IType::List(Box::new((*t).into()), span),
            rename::Type::Tree(t, span) => IType::Tree(Box::new((*t).into()), span),
        }
    }
}

#[derive(Clone)]
enum ITType<'src> {
    Plain(IType<'src>),
    Flow(IType<'src>, IType<'src>),
}

impl<'src> ITType<'src> {
    fn span(&self) -> Span {
        match self {
            ITType::Plain(ty) => ty.span(),
            ITType::Flow(l, r) => l.span().start..r.span().end,
        }
    }
}

impl<'src> From<rename::TType<'src>> for ITType<'src> {
    fn from(value: rename::TType<'src>) -> Self {
        match value {
            rename::TType::Plain(ty) => ITType::Plain(ty.into()),
            rename::TType::Flow(l, r) => ITType::Flow(l.into(), r.into()),
        }
    }
}

#[derive(Default, Clone)]
struct Ctx<'src> {
    next_mvar: u32,
    /// We keep track of the source of the variable also.
    /// Option is used to distinguish between dead and live variables.
    vars: VecDeque<(Span, Option<IType<'src>>)>,
    /// The current idempotent substitution.
    subst: BTreeMap<u32, IType<'src>>,
}

impl<'src> Ctx<'src> {
    fn gen_mvar(&mut self, span: Span) -> IType<'src> {
        let v = self.next_mvar;
        self.next_mvar += 1;
        IType::MVar(v, span)
    }

    fn gen_mvars(&mut self, span: Span, flow: Flow) -> ITType<'src> {
        match flow {
            Flow::Plain => ITType::Plain(self.gen_mvar(span)),
            Flow::Flow => ITType::Flow(self.gen_mvar(span.clone()), self.gen_mvar(span)),
        }
    }

    fn extend(&mut self, pattern: &IPattern<'src>) {
        match pattern {
            IPattern::Var(_, ITType::Plain(ty), span) => {
                self.vars.push_front((span.clone(), Some(ty.clone())));
            }
            IPattern::Var(_, ITType::Flow(ty, _), span) => {
                self.vars.push_front((span.clone(), Some(ty.clone())));
            }
            IPattern::Literal(_, _) => {}
            IPattern::Tuple(patterns, _) => {
                for pat in patterns {
                    self.extend(pat);
                }
            }
            IPattern::EmptyList(_) => {}
            IPattern::Cons(head, tail, _) => {
                self.extend(head);
                self.extend(tail);
            }
            IPattern::Left(pat, _) => self.extend(pat),
            IPattern::Right(pat, _) => self.extend(pat),
        }
    }

    fn retract(
        &mut self,
        errors: &mut Errors,
        unify_errors: &mut Vec<UnifyError<'src>>,
        pattern: &IPattern<'src>,
    ) {
        match pattern {
            IPattern::Var(name, ITType::Plain(_), span) => {
                if let (_, Some(ty)) = self.vars.pop_front().expect("de Bruijn indexing failure") {
                    errors.push(Diagnostic::error(
                        span.clone(),
                        format!("variable {name} had type {} at the end of its scope, but should have been used up", self.subst(ty)),
                    ));
                }
            }
            IPattern::Var(name, ITType::Flow(_, expected), span) => {
                match self.vars.pop_front().expect("de Bruijn indexing failure") {
                    (_, Some(actual)) => {
                        self.unify(unify_errors, span.clone(), expected.clone(), actual);
                    }
                    (_, None) => {
                        errors.push(Diagnostic::error(
                            span.clone(),
                            format!("variable {name} was not present at the end of its scope, but should have type {}", self.subst(expected.clone())),
                        ));
                    }
                }
            }
            IPattern::Literal(_, _) => {}
            IPattern::Tuple(patterns, _) => {
                for pat in patterns.iter().rev() {
                    self.retract(errors, unify_errors, pat);
                }
            }
            IPattern::EmptyList(_) => {}
            IPattern::Cons(head, tail, _) => {
                self.retract(errors, unify_errors, tail);
                self.retract(errors, unify_errors, head);
            }
            IPattern::Left(pat, _) => self.retract(errors, unify_errors, pat),
            IPattern::Right(pat, _) => self.retract(errors, unify_errors, pat),
        }
    }

    fn psubst(&self, errors: &mut Errors, pat: IPattern<'src>) -> Option<Pattern<'src>> {
        match pat {
            IPattern::Var(name, ty, span) => {
                Some(Pattern::Var(name, self.tsubst_complete(errors, ty)?, span))
            }
            IPattern::Literal(literal, span) => Some(Pattern::Literal(literal, span)),
            IPattern::Tuple(pats, span) => Some(Pattern::Tuple(
                pats.into_iter()
                    .filter_map(|pat| self.psubst(errors, pat))
                    .collect(),
                span,
            )),
            IPattern::EmptyList(span) => Some(Pattern::EmptyList(span)),
            IPattern::Cons(head, tail, span) => Some(Pattern::Cons(
                Box::new(self.psubst(errors, *head)?),
                Box::new(self.psubst(errors, *tail)?),
                span,
            )),
            IPattern::Left(pat, span) => {
                Some(Pattern::Left(Box::new(self.psubst(errors, *pat)?), span))
            }
            IPattern::Right(pat, span) => {
                Some(Pattern::Right(Box::new(self.psubst(errors, *pat)?), span))
            }
        }
    }

    fn eolsubst(&self, errors: &mut Errors, eol: IExprOrLens<'src>) -> Option<ExprOrLens<'src>> {
        match eol {
            IExprOrLens::Expr(iexpr) => self.esubst(errors, iexpr).map(ExprOrLens::Expr),
            IExprOrLens::Lens(ilens) => self.lsubst(errors, ilens).map(ExprOrLens::Lens),
        }
    }

    fn esubst(&self, errors: &mut Errors, expr: IExpr<'src>) -> Option<Expr<'src>> {
        match expr {
            IExpr::Var(name, span) => Some(Expr::Var(name, span)),
            IExpr::Inst { name, subst, span } => Some(Expr::Inst {
                name,
                subst: subst
                    .into_iter()
                    .filter_map(|(k, v)| self.subst_complete(errors, v).map(|v| (k, v)))
                    .collect(),
                span,
            }),
            IExpr::App(l, r, span) => Some(Expr::App(
                Box::new(self.esubst(errors, *l)?),
                Box::new(self.eolsubst(errors, *r)?),
                span,
            )),
            IExpr::Assign(left, right, span) => Some(Expr::Assign(
                Box::new(self.lsubst(errors, *left)?),
                Box::new(self.esubst(errors, *right)?),
                span,
            )),
            IExpr::Literal(literal, span) => Some(Expr::Literal(literal, span)),
            IExpr::PrimOp(left, right, prim_op, span) => Some(Expr::PrimOp(
                Box::new(self.esubst(errors, *left)?),
                Box::new(self.esubst(errors, *right)?),
                prim_op,
                span,
            )),
            IExpr::Tuple(exprs, span) => Some(Expr::Tuple(
                exprs
                    .into_iter()
                    .filter_map(|expr| self.esubst(errors, expr))
                    .collect(),
                span,
            )),
            IExpr::EmptyList(span) => Some(Expr::EmptyList(span)),
            IExpr::Cons(head, tail, span) => Some(Expr::Cons(
                Box::new(self.esubst(errors, *head)?),
                Box::new(self.esubst(errors, *tail)?),
                span,
            )),
            IExpr::Let {
                pattern,
                value,
                body,
                span,
            } => Some(Expr::Let {
                pattern: self.psubst(errors, pattern)?,
                value: Box::new(self.eolsubst(errors, *value)?),
                body: Box::new(self.esubst(errors, *body)?),
                span,
            }),
            IExpr::Case {
                scrutinee,
                branches,
                span,
            } => Some(Expr::Case {
                scrutinee: Box::new(self.eolsubst(errors, *scrutinee)?),
                branches: branches
                    .into_iter()
                    .filter_map(|(pat, expr)| {
                        self.psubst(errors, pat).zip(self.esubst(errors, expr))
                    })
                    .collect(),
                span,
            }),
            IExpr::Lambda {
                flow,
                pattern,
                body,
                span,
            } => Some(Expr::Lambda {
                flow,
                pattern: self.psubst(errors, pattern)?,
                body: Box::new(self.eolsubst(errors, *body)?),
                span,
            }),
            IExpr::Left(expr, span) => {
                Some(Expr::Left(Box::new(self.esubst(errors, *expr)?), span))
            }
            IExpr::Right(expr, span) => {
                Some(Expr::Right(Box::new(self.esubst(errors, *expr)?), span))
            }
        }
    }

    fn lsubst(&self, errors: &mut Errors, lens: ILens<'src>) -> Option<Lens<'src>> {
        match lens {
            ILens::Var(index, ty, span) => {
                Some(Lens::Var(index, self.subst_complete(errors, ty)?, span))
            }
            ILens::Tuple(items, span) => Some(Lens::Tuple(
                items
                    .into_iter()
                    .filter_map(|lens| self.lsubst(errors, lens))
                    .collect(),
                span,
            )),
            ILens::App(left, right, span) => Some(Lens::App(
                Box::new(self.esubst(errors, *left)?),
                Box::new(self.eolsubst(errors, *right)?),
                span,
            )),
            ILens::Literal(literal, span) => Some(Lens::Literal(literal, span)),
        }
    }

    fn tsubst(&self, ty: ITType<'src>) -> ITType<'src> {
        match ty {
            ITType::Plain(ty) => ITType::Plain(self.subst(ty)),
            ITType::Flow(ty1, ty2) => ITType::Flow(self.subst(ty1), self.subst(ty2)),
        }
    }

    fn tsubst_complete(&self, errors: &mut Errors, ty: ITType<'src>) -> Option<TType<'src>> {
        match ty {
            ITType::Plain(ty) => self.subst_complete(errors, ty).map(TType::Plain),
            ITType::Flow(ty1, ty2) => Some(TType::Flow(
                self.subst_complete(errors, ty1)?,
                self.subst_complete(errors, ty2)?,
            )),
        }
    }

    fn subst(&self, ty: IType<'src>) -> IType<'src> {
        match ty {
            IType::MVar(n, span) => self.subst.get(&n).cloned().unwrap_or(IType::MVar(n, span)),
            IType::Prim(prim_ty, span) => IType::Prim(prim_ty, span),
            IType::Var(name, span) => IType::Var(name, span),
            IType::Arrow(left, right, span) => IType::Arrow(
                Box::new(self.tsubst(*left)),
                Box::new(self.tsubst(*right)),
                span,
            ),
            IType::Tuple(tys, span) => {
                IType::Tuple(tys.into_iter().map(|ty| self.subst(ty)).collect(), span)
            }
            IType::Either(l, r, span) => {
                IType::Either(Box::new(self.subst(*l)), Box::new(self.subst(*r)), span)
            }
            IType::List(t, span) => IType::List(Box::new(self.subst(*t)), span),
            IType::Tree(t, span) => IType::Tree(Box::new(self.subst(*t)), span),
        }
    }

    fn subst_complete(&self, errors: &mut Errors, ty: IType<'src>) -> Option<Type<'src>> {
        match ty {
            IType::MVar(n, span) => match self.subst.get(&n) {
                // This will terminate since the substitution is idempotent.
                Some(ty) => self.subst_complete(errors, ty.clone()),
                None => {
                    errors.push(Diagnostic::error(span, "could not deduce type".to_owned()));
                    None
                }
            },
            IType::Prim(prim_ty, span) => Some(Type::Prim(prim_ty, span)),
            IType::Var(name, span) => Some(Type::Var(name, span)),
            IType::Arrow(left, right, span) => Some(Type::Arrow(
                Box::new(self.tsubst_complete(errors, *left)?),
                Box::new(self.tsubst_complete(errors, *right)?),
                span,
            )),
            IType::Tuple(tys, span) => Some(Type::Tuple(
                tys.into_iter()
                    .filter_map(|ty| self.subst_complete(errors, ty))
                    .collect(),
                span,
            )),
            IType::Either(l, r, span) => Some(Type::Either(
                Box::new(self.subst_complete(errors, *l)?),
                Box::new(self.subst_complete(errors, *r)?),
                span,
            )),
            IType::List(t, span) => {
                Some(Type::List(Box::new(self.subst_complete(errors, *t)?), span))
            }
            IType::Tree(t, span) => {
                Some(Type::Tree(Box::new(self.subst_complete(errors, *t)?), span))
            }
        }
    }

    fn tunify(
        &mut self,
        errors: &mut Vec<UnifyError<'src>>,
        span: Span,
        expected: ITType<'src>,
        actual: ITType<'src>,
    ) {
        match self.tunify_core(self.tsubst(expected.clone()), self.tsubst(actual.clone())) {
            UnificationResult::Ok => {}
            _ => {
                errors.push(UnifyError {
                    span,
                    expected,
                    actual,
                });
            }
        }
    }

    fn unify(
        &mut self,
        errors: &mut Vec<UnifyError<'src>>,
        span: Span,
        expected: IType<'src>,
        actual: IType<'src>,
    ) {
        match self.unify_core(self.subst(expected.clone()), self.subst(actual.clone())) {
            UnificationResult::Ok => {}
            _ => {
                errors.push(UnifyError {
                    span,
                    expected: ITType::Plain(expected),
                    actual: ITType::Plain(actual),
                });
            }
        }
    }

    fn tunify_core(&mut self, expected: ITType<'src>, actual: ITType<'src>) -> UnificationResult {
        match (expected, actual) {
            (ITType::Plain(expected), ITType::Plain(actual)) => self.unify_core(expected, actual),
            (ITType::Flow(e1, e2), ITType::Flow(a1, a2)) => {
                self.unify_core(e1, a1).then(self.unify_core(e2, a2))
            }
            _ => UnificationResult::Clash,
        }
    }

    fn unify_core(&mut self, expected: IType<'src>, actual: IType<'src>) -> UnificationResult {
        match (expected, actual) {
            (IType::MVar(mvar, _), ty) | (ty, IType::MVar(mvar, _))
                if !self.subst.contains_key(&mvar) =>
            {
                let ty = self.subst(ty);
                if occurs(mvar, &ty) {
                    UnificationResult::OccursCheck
                } else {
                    self.add_subst(mvar, ty);
                    UnificationResult::Ok
                }
            }
            (IType::Var(expected, _), IType::Var(actual, _)) => {
                if expected == actual {
                    UnificationResult::Ok
                } else {
                    UnificationResult::Clash
                }
            }
            (IType::Prim(expected, _), IType::Prim(actual, _)) => {
                if expected == actual {
                    UnificationResult::Ok
                } else {
                    UnificationResult::Clash
                }
            }
            (IType::Arrow(el, er, _), IType::Arrow(al, ar, _)) => {
                self.tunify_core(*el, *al).then(self.tunify_core(*er, *ar))
            }
            (IType::Either(el, er, _), IType::Either(al, ar, _)) => {
                self.unify_core(*el, *al).then(self.unify_core(*er, *ar))
            }
            (IType::List(expected, _), IType::List(actual, _)) => {
                self.unify_core(*expected, *actual)
            }
            (IType::Tree(expected, _), IType::Tree(actual, _)) => {
                self.unify_core(*expected, *actual)
            }
            (IType::Tuple(tys1, _), IType::Tuple(tys2, _)) if tys1.len() == tys2.len() => tys1
                .into_iter()
                .zip(tys2)
                .map(|(ty1, ty2)| self.unify_core(ty1, ty2))
                .fold(UnificationResult::Ok, UnificationResult::then),
            _ => UnificationResult::Clash,
        }
    }

    fn add_subst(&mut self, mvar: u32, ty: IType<'src>) {
        self.subst.insert(mvar, ty);
        // Update the substitution to preserve idempotence.
        // This is obviously an inefficient implementation.
        for entry in self.subst.keys().copied().collect::<Vec<_>>() {
            self.subst
                .insert(entry, self.subst(self.subst.get(&entry).unwrap().clone()));
        }
    }
}

struct UnifyError<'src> {
    span: Span,
    expected: ITType<'src>,
    actual: ITType<'src>,
}

enum UnificationResult {
    Ok,
    /// Could not unify types.
    Clash,
    /// Occurs check failed.
    OccursCheck,
}

impl UnificationResult {
    fn then(self, other: UnificationResult) -> UnificationResult {
        match self {
            UnificationResult::Ok => other,
            _ => self,
        }
    }
}

fn occurs<'src>(mvar: u32, ty: &IType<'src>) -> bool {
    match ty {
        IType::MVar(n, _) => *n == mvar,
        IType::Prim(_, _) => false,
        IType::Var(_, _) => false,
        IType::Arrow(l, r, _) => toccurs(mvar, l) || toccurs(mvar, r),
        IType::Tuple(tys, _) => tys.iter().any(|ty| occurs(mvar, ty)),
        IType::Either(l, r, _) => occurs(mvar, l) || occurs(mvar, r),
        IType::List(t, _) => occurs(mvar, t),
        IType::Tree(t, _) => occurs(mvar, t),
    }
}

fn toccurs<'src>(mvar: u32, ty: &ITType<'src>) -> bool {
    match ty {
        ITType::Plain(ty) => occurs(mvar, ty),
        ITType::Flow(l, r) => occurs(mvar, l) || occurs(mvar, r),
    }
}
