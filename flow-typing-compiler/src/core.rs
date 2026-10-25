use std::{
    collections::{BTreeMap, VecDeque},
    fmt::{Debug, Display},
};

use logos::Span;

use crate::{
    error::{Diagnostic, Errors},
    infer,
    out_of_scope::out_of_scope,
    parse::{Flow, Literal, PrimOp, PrimTy},
    rename,
};

/// Run the flow typing translation from the paper, converting typechecked lambda_F expressions into
/// expressions in the linear lambda calculus.
pub fn translate<'src>(
    errors: &mut Errors,
    decls: Vec<rename::Decl<'src>>,
    defs: Vec<infer::Def<'src>>,
) -> (Vec<Decl<'src>>, Vec<Def<'src>>) {
    let decls = decls
        .into_iter()
        .map(|decl| Decl {
            name: decl.name,
            span: decl.span,
            ty: decl.ty.into(),
        })
        .collect::<Vec<_>>();

    let defs = defs
        .into_iter()
        .map(|def| {
            let mut ctx = Ctx::default();
            let mut ng = CoreNameGen(0);
            let expr = translate_expr(errors, &mut ctx, &mut ng, def.expr);
            if !ctx.vars.is_empty() {
                panic!("compiler error: ctx was {ctx:?} in {expr:#?}");
            };
            let core = ng.generate();
            let mut result = Def {
                name: def.name,
                span: def.span.clone(),
                // Extract the value `B` from the form `B * 1`.
                expr: Expr::Let {
                    pattern: Pattern::Tuple(
                        vec![
                            Pattern::Var(core, "result".to_owned(), def.span.clone()),
                            Pattern::Tuple(Vec::new(), def.span.clone()),
                        ],
                        def.span.clone(),
                    ),
                    value: Box::new(expr),
                    body: Box::new(Expr::Var(core, def.span.clone())),
                    span: def.span,
                },
            };
            result.expr.optimise(&mut ng);
            println!("TRANSLATED: {result:#?}");
            result
        })
        .collect::<Vec<_>>();

    (decls, defs)
}

/// Translates an expression `Gamma_1 |- expr : A -| Gamma_2`
/// into an LLC expression `Gamma_1^o |- expr' : A^o * Gamma_2^o`.
///
/// Here, ctx tracks the flow typing context, not the LLC context.
/// The names in the LLC are called CoreNames, and they don't use de Bruijn indexing.
fn translate_expr<'src>(
    errors: &mut Errors,
    ctx: &mut Ctx,
    ng: &mut CoreNameGen,
    expr: infer::Expr<'src>,
) -> Expr<'src> {
    match expr {
        infer::Expr::Var(i, span) => {
            // Convert this de Bruijn index into a core name.
            let core = &mut ctx.vars[i];
            let name = core.expect("variable not live!");
            *core = None;
            ctx.pack(span.clone(), Expr::Var(name, span))
        }
        infer::Expr::Inst { name, subst, span } => ctx.pack(
            span.clone(),
            Expr::Inst {
                name,
                subst: subst.into_iter().map(|(k, v)| (k, v.into())).collect(),
                span,
            },
        ),
        infer::Expr::App(left, right, span) => {
            let left = translate_expr(errors, ctx, ng, *left);
            match *right {
                infer::ExprOrLens::Expr(right) => {
                    ctx.unpack(ng, span.clone(), "al", left, |ctx, ng, left_core| {
                        let right = translate_expr(errors, ctx, ng, right);
                        ctx.unpack(ng, span.clone(), "ar", right, |ctx, _, right_core| {
                            ctx.pack(
                                span.clone(),
                                Expr::App(
                                    Box::new(Expr::Var(left_core, span.clone())),
                                    Box::new(Expr::Var(right_core, span.clone())),
                                    span,
                                ),
                            )
                        })
                    })
                }
                infer::ExprOrLens::Lens(right) => {
                    // Gamma_1 |- left : A/A' -> B -| Gamma_2
                    // Gamma_2 |- right : A/A' -| Gamma_3
                    // Want to get:
                    // Gamma_1 |- u : (B, Gamma_3)

                    ctx.unpack(ng, span.clone(), "all", left, |ctx, ng, left_core| {
                        let right = translate_lens(errors, ctx, ng, right);
                        // left: A -> (B, A')
                        // right: (A, A' -> Gamma_3)

                        let a = ng.generate(); // type A
                        let res = ng.generate(); // type (A' -> Gamma_3)
                        let b = ng.generate(); // type B
                        let res2 = ng.generate(); // type A'
                        Expr::Let {
                            pattern: Pattern::Tuple(
                                vec![
                                    Pattern::Var(a, "a".to_owned(), span.clone()),
                                    Pattern::Var(res, "res".to_owned(), span.clone()),
                                ],
                                span.clone(),
                            ),
                            value: Box::new(right),
                            body: Box::new(Expr::Let {
                                pattern: Pattern::Tuple(
                                    vec![
                                        Pattern::Var(b, "b".to_owned(), span.clone()),
                                        Pattern::Var(res2, "res2".to_owned(), span.clone()),
                                    ],
                                    span.clone(),
                                ),
                                value: Box::new(Expr::App(
                                    Box::new(Expr::Var(left_core, span.clone())),
                                    Box::new(Expr::Var(a, span.clone())),
                                    span.clone(),
                                )),
                                body: Box::new(Expr::Tuple(
                                    vec![
                                        Expr::Var(b, span.clone()),
                                        Expr::App(
                                            Box::new(Expr::Var(res, span.clone())),
                                            Box::new(Expr::Var(res2, span.clone())),
                                            span.clone(),
                                        ),
                                    ],
                                    span.clone(),
                                )),
                                span: span.clone(),
                            }),
                            span,
                        }
                    })
                }
            }
        }
        infer::Expr::Assign(lens, expr, span) => {
            let expr = translate_expr(errors, ctx, ng, *expr);
            ctx.unpack(ng, span.clone(), "pl", expr, |ctx, ng, expr_core| {
                let lens = translate_lens(errors, ctx, ng, *lens);
                // expr_core: A
                // lens: (A', A -> ctx)
                // goal: (A', ctx)
                let aprime = ng.generate(); // A'
                let res = ng.generate(); // A -> ctx
                Expr::Let {
                    pattern: Pattern::Tuple(
                        vec![
                            Pattern::Var(aprime, "ap".to_owned(), span.clone()),
                            Pattern::Var(res, "res".to_owned(), span.clone()),
                        ],
                        span.clone(),
                    ),
                    value: Box::new(lens),
                    body: Box::new(Expr::Tuple(
                        vec![
                            Expr::Var(aprime, span.clone()),
                            Expr::App(
                                Box::new(Expr::Var(res, span.clone())),
                                Box::new(Expr::Var(expr_core, span.clone())),
                                span.clone(),
                            ),
                        ],
                        span.clone(),
                    )),
                    span,
                }
            })
        }
        infer::Expr::Literal(literal, span) => ctx.pack(span.clone(), Expr::Literal(literal, span)),
        infer::Expr::PrimOp(left, right, op, span) => {
            let left = translate_expr(errors, ctx, ng, *left);
            ctx.unpack(ng, span.clone(), "pl", left, |ctx, ng, left_core| {
                let right = translate_expr(errors, ctx, ng, *right);
                ctx.unpack(ng, span.clone(), "pr", right, |ctx, _, right_core| {
                    ctx.pack(
                        span.clone(),
                        Expr::PrimOp(
                            Box::new(Expr::Var(left_core, span.clone())),
                            Box::new(Expr::Var(right_core, span.clone())),
                            op,
                            span,
                        ),
                    )
                })
            })
        }
        infer::Expr::Tuple(exprs, span) => ctx.unpack_chain(
            errors,
            ng,
            span.clone(),
            "tuple",
            exprs.into(),
            Box::new(move |ctx, _ng, names| {
                ctx.pack(
                    span.clone(),
                    Expr::Tuple(
                        names
                            .into_iter()
                            .map(|name| Expr::Var(name, span.clone()))
                            .collect(),
                        span,
                    ),
                )
            }),
        ),
        infer::Expr::EmptyList(span) => ctx.pack(span.clone(), Expr::EmptyList(span)),
        infer::Expr::Cons(head, tail, span) => {
            let head = translate_expr(errors, ctx, ng, *head);
            ctx.unpack(ng, span.clone(), "head", head, |ctx, ng, head_core| {
                let tail = translate_expr(errors, ctx, ng, *tail);
                ctx.unpack(ng, span.clone(), "tail", tail, |ctx, _, tail_core| {
                    ctx.pack(
                        span.clone(),
                        Expr::Cons(
                            Box::new(Expr::Var(head_core, span.clone())),
                            Box::new(Expr::Var(tail_core, span.clone())),
                            span.clone(),
                        ),
                    )
                })
            })
        }
        infer::Expr::Let {
            pattern,
            value,
            body,
            span,
        } => match *value {
            infer::ExprOrLens::Expr(value) => {
                let value = translate_expr(errors, ctx, ng, value);
                ctx.unpack(ng, span.clone(), "var", value, |ctx, ng, value_core| {
                    let pattern_tr = ctx.extend(ng, &pattern);
                    let body_tr = translate_expr(errors, ctx, ng, *body);

                    Expr::Let {
                        pattern: pattern_tr,
                        value: Box::new(Expr::Var(value_core, span.clone())),
                        body: Box::new(ctx.unpack(
                            ng,
                            span.clone(),
                            "pat",
                            body_tr,
                            |ctx, _, core| {
                                ctx.retract(&pattern);
                                ctx.pack(span.clone(), Expr::Var(core, span.clone()))
                            },
                        )),
                        span,
                    }
                })
            }
            infer::ExprOrLens::Lens(value) => {
                // `let p = ~u in t` is a `case ~u of p -> t` with a single branch
                // (rules ~Let and ~(x)-E), so reuse the translation of rule ~(+)-E.
                translate_expr(
                    errors,
                    ctx,
                    ng,
                    infer::Expr::Case {
                        scrutinee: Box::new(infer::ExprOrLens::Lens(value)),
                        branches: vec![(pattern, *body)],
                        span,
                    },
                )
            }
        },
        infer::Expr::Case {
            scrutinee,
            branches,
            span,
        } => match *scrutinee {
            infer::ExprOrLens::Expr(scrutinee) => {
                let scrutinee = translate_expr(errors, ctx, ng, scrutinee);
                ctx.unpack(
                    ng,
                    span.clone(),
                    "scr",
                    scrutinee,
                    |ctx, ng, scrutinee_core| {
                        let mut new_branches = Vec::new();
                        let mut final_ctx = None::<Ctx>;
                        for (pattern, body) in branches {
                            let mut ctx2 = ctx.clone();
                            let pattern_tr = ctx2.extend(ng, &pattern);
                            let body_tr = translate_expr(errors, &mut ctx2, ng, body);
                            let body_real = ctx2.unpack(
                                ng,
                                span.clone(),
                                "branch",
                                body_tr,
                                |ctx2, ng, core| {
                                    ctx2.retract(&pattern);
                                    if final_ctx.is_none() {
                                        final_ctx = Some(ctx2.freshen(ng));
                                    }
                                    ctx2.pack(span.clone(), Expr::Var(core, span.clone()))
                                },
                            );
                            new_branches.push((pattern_tr, body_real));
                        }
                        *ctx = final_ctx.expect("empty case not allowed");

                        Expr::Case {
                            scrutinee: Box::new(Expr::Var(scrutinee_core, span.clone())),
                            branches: new_branches,
                            span,
                        }
                    },
                )
            }
            infer::ExprOrLens::Lens(scrutinee) => {
                let mut fvars = scrutinee.fvars();
                fvars.sort();
                fvars.dedup();

                let mut scrutinee_ctx = ctx.corestrict(&fvars);

                // Gamma_1 |- A^o * (B^o -> Gamma_2^o)
                let scrutinee = translate_lens(errors, &mut scrutinee_ctx, ng, scrutinee);

                // A^o
                let scrl = ng.generate();
                // Residual: B^o -> Gamma_2^o
                let res = ng.generate();

                // Result of the inner case expression.
                let ans = ng.generate();
                // Reconstructed pattern B^o.
                let b = ng.generate();
                // Rest of context ctx.
                let ctxrest = ng.generate();

                Expr::Let {
                    pattern: Pattern::Tuple(
                        vec![
                            Pattern::Var(scrl, "scrl".to_owned(), span.clone()),
                            Pattern::Var(res, "res".to_owned(), span.clone()),
                        ],
                        span.clone(),
                    ),
                    value: Box::new(scrutinee),
                    body: Box::new(Expr::Let {
                        pattern: Pattern::Tuple(
                            vec![
                                Pattern::Tuple(
                                    vec![
                                        Pattern::Var(ans, "ans".to_owned(), span.clone()),
                                        Pattern::Var(b, "b".to_owned(), span.clone()),
                                    ],
                                    span.clone(),
                                ),
                                Pattern::Var(ctxrest, "rest".to_owned(), span.clone()),
                            ],
                            span.clone(),
                        ),
                        value: Box::new(Expr::Case {
                            scrutinee: Box::new(Expr::Var(scrl, span.clone())),
                            branches: {
                                let mut new_branches = Vec::new();
                                let mut final_ctx = None::<Ctx>;
                                for (pattern, body) in branches {
                                    // Use the rest of ctx on the body.
                                    let mut ctx2 = ctx.clone();
                                    let pattern_tr = ctx2.extend(ng, &pattern);
                                    let body_tr = translate_expr(errors, &mut ctx2, ng, body);
                                    let body_real = ctx2.unpack(
                                        ng,
                                        span.clone(),
                                        "branch",
                                        body_tr,
                                        |ctx2, ng, core| {
                                            let result = Expr::Tuple(
                                                vec![
                                                    Expr::Var(core, span.clone()),
                                                    reconstruct_pattern(ctx2, &pattern),
                                                ],
                                                span.clone(),
                                            );
                                            ctx2.retract(&pattern);
                                            if final_ctx.is_none() {
                                                final_ctx = Some(ctx2.freshen(ng));
                                            }
                                            ctx2.pack(span.clone(), result)
                                        },
                                    );
                                    new_branches.push((pattern_tr, body_real));
                                }
                                *ctx = final_ctx.expect("empty case not allowed");
                                new_branches
                            },
                            span: span.clone(),
                        }),
                        body: {
                            Box::new(Expr::Let {
                                pattern: Pattern::Tuple(
                                    vec![
                                        ctx.unpack_pattern(ng, span.clone()),
                                        scrutinee_ctx.unpack_pattern(ng, span.clone()),
                                    ],
                                    span.clone(),
                                ),
                                value: Box::new(Expr::Tuple(
                                    vec![
                                        Expr::Var(ctxrest, span.clone()),
                                        Expr::App(
                                            Box::new(Expr::Var(res, span.clone())),
                                            Box::new(Expr::Var(b, span.clone())),
                                            span.clone(),
                                        ),
                                    ],
                                    span.clone(),
                                )),
                                body: {
                                    ctx.combine(scrutinee_ctx);
                                    Box::new(ctx.pack(span.clone(), Expr::Var(ans, span.clone())))
                                },
                                span: span.clone(),
                            })
                        },
                        span: span.clone(),
                    }),
                    span,
                }
            }
        },
        infer::Expr::Lambda {
            flow,
            pattern,
            body,
            span,
        } => {
            let mut fvars = body.fvars();
            // Pretend that all of the pattern's variables are free.
            fvars.extend(0..pattern.vars());
            fvars.sort();
            fvars.dedup();

            match (flow, *body) {
                (Flow::Plain, infer::ExprOrLens::Expr(body)) => {
                    // Gamma_1, Gamma_2 |- (\pattern. body) : A -> B -| Gamma_1^+, Gamma_2

                    let pattern_tr = ctx.extend(ng, &pattern);
                    let residual = ctx.restrict(&fvars);
                    // Gamma_1, pattern |- body_tr: B * 1
                    let body_tr = translate_expr(errors, ctx, ng, body);
                    // The trailing context should have exactly no live variables.
                    for var in &ctx.vars {
                        if var.is_some() {
                            errors.push(Diagnostic::error(
                                span.clone(),
                                "lambda had unused variables at end of body".to_owned(),
                            ));
                        }
                    }
                    let result = Expr::Lambda {
                        pattern: pattern_tr,
                        body: Box::new(ctx.unpack(
                            ng,
                            span.clone(),
                            "lam",
                            body_tr,
                            |_, _, core| Expr::Var(core, span.clone()),
                        )),
                        span: span.clone(),
                    };
                    ctx.combine(residual);
                    ctx.retract(&pattern);
                    ctx.pack(span, result)
                }
                (Flow::Plain, infer::ExprOrLens::Lens(body)) => {
                    // Gamma_1, Gamma_2 |- (\pattern. body) : A -> B/B' -| Gamma_1^+, Gamma_2
                    // which becomes
                    // Gamma_1, Gamma_2 |- t : A -> (B * (B' -> I)) -| Gamma_1^+, Gamma_2

                    let pattern_tr = ctx.extend(ng, &pattern);
                    let residual = ctx.restrict(&fvars);
                    // Gamma_1, pattern |- body_tr: B * 1
                    let body_tr = translate_lens(errors, ctx, ng, body);
                    // The trailing context should have exactly no live variables.
                    for var in &ctx.vars {
                        if var.is_some() {
                            errors.push(Diagnostic::error(
                                span.clone(),
                                "lambda had unused variables at end of body".to_owned(),
                            ));
                        }
                    }
                    let result = Expr::Lambda {
                        pattern: pattern_tr,
                        body: Box::new(body_tr),
                        span: span.clone(),
                    };
                    ctx.combine(residual);
                    ctx.retract(&pattern);
                    ctx.pack(span, result)
                }
                (Flow::Flow, infer::ExprOrLens::Expr(body)) => {
                    // Gamma_1, Gamma_2 |- (\pattern. body) : A/A' -> B -| Gamma_1^+, Gamma_2

                    let pattern_tr = ctx.extend(ng, &pattern);
                    let residual = ctx.restrict(&fvars);
                    // Gamma_1, pattern_L |- body_tr: B * pattern_R
                    let body_tr = translate_expr(errors, ctx, ng, body);
                    let result = Expr::Lambda {
                        pattern: pattern_tr,
                        body: Box::new(ctx.unpack(
                            ng,
                            span.clone(),
                            "lam",
                            body_tr,
                            // Get (B * A') here.
                            |ctx, _, core| {
                                Expr::Tuple(
                                    vec![
                                        Expr::Var(core, span.clone()),
                                        reconstruct_pattern(ctx, &pattern),
                                    ],
                                    span.clone(),
                                )
                            },
                        )),
                        span: span.clone(),
                    };
                    ctx.combine(residual);
                    ctx.retract(&pattern);
                    ctx.pack(span, result)
                }
                (Flow::Flow, infer::ExprOrLens::Lens(body)) => {
                    // Gamma_1, Gamma_2 |- (\pattern. body) : A/A' -> B/B' -| Gamma_1^+, Gamma_2
                    // which becomes
                    // Gamma_1, Gamma_2 |- t : A -> (B * (B' -> A')) -| Gamma_1^+, Gamma_2

                    let pattern_tr = ctx.extend(ng, &pattern);
                    let residual = ctx.restrict(&fvars);
                    // Gamma_1, pattern_L |- body_tr: B * (B' -> pattern_R)
                    let body_tr = translate_lens(errors, ctx, ng, body);

                    let result_core = ng.generate();
                    let residual_core = ng.generate();
                    let residual_value_core = ng.generate();

                    let result = Expr::Lambda {
                        pattern: pattern_tr,
                        body: Box::new(Expr::Let {
                            pattern: Pattern::Tuple(
                                vec![
                                    Pattern::Var(result_core, "r".to_owned(), span.clone()),
                                    Pattern::Var(residual_core, "res".to_owned(), span.clone()),
                                ],
                                span.clone(),
                            ),
                            value: Box::new(body_tr),
                            body: Box::new(Expr::Tuple(
                                vec![
                                    Expr::Var(result_core, span.clone()),
                                    Expr::Lambda {
                                        pattern: Pattern::Var(
                                            residual_value_core,
                                            "resv".to_owned(),
                                            span.clone(),
                                        ),
                                        body: Box::new(ctx.unpack_simple(
                                            ng,
                                            span.clone(),
                                            Expr::App(
                                                Box::new(Expr::Var(residual_core, span.clone())),
                                                Box::new(Expr::Var(
                                                    residual_value_core,
                                                    span.clone(),
                                                )),
                                                span.clone(),
                                            ),
                                            |ctx, _| reconstruct_pattern(ctx, &pattern),
                                        )),
                                        span: span.clone(),
                                    },
                                ],
                                span.clone(),
                            )),
                            span: span.clone(),
                        }),
                        span: span.clone(),
                    };
                    ctx.combine(residual);
                    ctx.retract(&pattern);
                    ctx.pack(span, result)
                }
            }
        }
        infer::Expr::Left(expr, span) => {
            let value = translate_expr(errors, ctx, ng, *expr);
            ctx.unpack(ng, span.clone(), "inl", value, |ctx, _, value_core| {
                ctx.pack(
                    span.clone(),
                    Expr::Left(Box::new(Expr::Var(value_core, span.clone())), span.clone()),
                )
            })
        }
        infer::Expr::Right(expr, span) => {
            let value = translate_expr(errors, ctx, ng, *expr);
            ctx.unpack(ng, span.clone(), "inr", value, |ctx, _, value_core| {
                ctx.pack(
                    span.clone(),
                    Expr::Right(Box::new(Expr::Var(value_core, span.clone())), span.clone()),
                )
            })
        }
    }
}

/// Translates a lens term `Gamma_1 |- lens : A/B -| Gamma_2`
/// into an LLC expression `Gamma_1^o |- lens' : A^o * (B^o -> Gamma_2^o)`.
fn translate_lens<'src>(
    errors: &mut Errors,
    ctx: &mut Ctx,
    ng: &mut CoreNameGen,
    lens: infer::Lens<'src>,
) -> Expr<'src> {
    match lens {
        infer::Lens::Var(i, _, span) => {
            // This lens is a variable with the given de Bruijn index.
            // Gamma, x: A (or x dead) |- x : A/A' -| Gamma, x: A'
            let old = ctx.vars[i].take();
            let new = ng.generate();
            ctx.vars[i] = Some(new);
            Expr::Tuple(
                vec![
                    match old {
                        Some(old) => Expr::Var(old, span.clone()),
                        None => Expr::Tuple(Vec::new(), span.clone()),
                    },
                    Expr::Lambda {
                        pattern: Pattern::Var(new, "x".to_string(), span.clone()),
                        body: Box::new(Expr::Tuple(
                            ctx.vars
                                .iter()
                                .filter_map(|core| core.as_ref())
                                .map(|core| Expr::Var(*core, span.clone()))
                                .collect(),
                            span.clone(),
                        )),
                        span: span.clone(),
                    },
                ],
                span,
            )
        }
        infer::Lens::Tuple(lenses, span) => {
            // Each item has Gamma_i |- u_i : A_i/A_i' -| Gamma_i'; we need:
            // Gamma_1, ..., Gamma_n |- (u_1, ..., u_n) : (A_1, ..., A_n)/(A_1', ..., A_n') -| Gamma_1', ..., Gamma_n'.

            let mut translations = Vec::new();
            let mut restrictions = Vec::new();
            for lens in lenses {
                let mut fvars = lens.fvars();
                fvars.sort();
                fvars.dedup();

                let mut restriction = ctx.corestrict(&fvars);
                let tr = translate_lens(errors, &mut restriction, ng, lens);
                translations.push(tr);
                restrictions.push(restriction);
            }

            // Each translated expression has type `A_i * (A_i' -> Gamma_i')`.
            // Unpack each of them.
            let names = translations
                .iter()
                .map(|_| (ng.generate(), ng.generate(), ng.generate()))
                .collect::<Vec<_>>();
            Expr::Let {
                pattern: Pattern::Tuple(
                    names
                        .iter()
                        .map(|(left_name, right_name, _)| {
                            Pattern::Tuple(
                                vec![
                                    Pattern::Var(*left_name, "tl".to_owned(), span.clone()),
                                    Pattern::Var(*right_name, "tr".to_owned(), span.clone()),
                                ],
                                span.clone(),
                            )
                        })
                        .collect(),
                    span.clone(),
                ),
                value: Box::new(Expr::Tuple(translations, span.clone())),
                body: Box::new(Expr::Tuple(
                    vec![
                        Expr::Tuple(
                            names
                                .iter()
                                .map(|(left_name, _, _)| Expr::Var(*left_name, span.clone()))
                                .collect(),
                            span.clone(),
                        ),
                        Expr::Lambda {
                            pattern: Pattern::Tuple(
                                names
                                    .iter()
                                    .map(|(_, _, res_name)| {
                                        Pattern::Var(*res_name, "tres".to_owned(), span.clone())
                                    })
                                    .collect(),
                                span.clone(),
                            ),
                            body: {
                                // Given each x_i': A_i', unpack the Gamma_i'.
                                let pats = restrictions
                                    .into_iter()
                                    .map(|mut res| {
                                        let pat = res.unpack_pattern(ng, span.clone());
                                        ctx.combine(res);
                                        pat
                                    })
                                    .collect();
                                Box::new(Expr::Let {
                                    pattern: Pattern::Tuple(pats, span.clone()),
                                    value: Box::new(Expr::Tuple(
                                        names
                                            .iter()
                                            .map(|(_, right_name, res_name)| {
                                                Expr::App(
                                                    Box::new(Expr::Var(*right_name, span.clone())),
                                                    Box::new(Expr::Var(*res_name, span.clone())),
                                                    span.clone(),
                                                )
                                            })
                                            .collect(),
                                        span.clone(),
                                    )),
                                    body: Box::new(ctx.pack_simple(span.clone())),
                                    span: span.clone(),
                                })
                            },
                            span: span.clone(),
                        },
                    ],
                    span.clone(),
                )),
                span: span.clone(),
            }
        }
        infer::Lens::App(left, right, span) => {
            let left = translate_expr(errors, ctx, ng, *left);
            match *right {
                infer::ExprOrLens::Expr(right) => {
                    // Gamma_1 |- left : A -> B/B' -| Gamma_2
                    // Gamma_2 |- right : A -| Gamma_3
                    // Want to get:
                    // Gamma_1 |- u : (B, B' -> Gamma_3)
                    ctx.unpack(ng, span.clone(), "all", left, |ctx, ng, left_core| {
                        let right = translate_expr(errors, ctx, ng, right);
                        ctx.unpack(ng, span.clone(), "alr", right, |ctx, ng, right_core| {
                            // Here:
                            // al : A -> (B, B' -> ())
                            // ar : A
                            let ab = ng.generate(); // type B
                            let ares = ng.generate(); // residual, type B' -> ()
                            let bprime = ng.generate(); // type B'
                            // The residual of the result must take the B' that is written
                            // back, pass it on to `ares`, and then return Gamma_3.
                            Expr::Let {
                                pattern: Pattern::Tuple(
                                    vec![
                                        Pattern::Var(ab, "ab".to_owned(), span.clone()),
                                        Pattern::Var(ares, "ares".to_owned(), span.clone()),
                                    ],
                                    span.clone(),
                                ),
                                value: Box::new(Expr::App(
                                    Box::new(Expr::Var(left_core, span.clone())),
                                    Box::new(Expr::Var(right_core, span.clone())),
                                    span.clone(),
                                )),
                                body: Box::new(Expr::Tuple(
                                    vec![
                                        Expr::Var(ab, span.clone()),
                                        Expr::Lambda {
                                            pattern: Pattern::Var(
                                                bprime,
                                                "bp".to_owned(),
                                                span.clone(),
                                            ),
                                            body: Box::new(Expr::PrimOp(
                                                Box::new(Expr::App(
                                                    Box::new(Expr::Var(ares, span.clone())),
                                                    Box::new(Expr::Var(bprime, span.clone())),
                                                    span.clone(),
                                                )),
                                                Box::new(ctx.pack_simple(span.clone())),
                                                PrimOp::Seq,
                                                span.clone(),
                                            )),
                                            span: span.clone(),
                                        },
                                    ],
                                    span.clone(),
                                )),
                                span,
                            }
                        })
                    })
                }
                infer::ExprOrLens::Lens(right) => {
                    // Gamma_1 |- left : A/A' -> B/B' -| Gamma_2
                    // Gamma_2 |- right : A/A' -| Gamma_3
                    // Want to get:
                    // Gamma_1 |- u : (B, B' -> Gamma_3)

                    ctx.unpack(ng, span.clone(), "all", left, |ctx, ng, left_core| {
                        let right = translate_lens(errors, ctx, ng, right);
                        // left: A -> (B, B' -> A')
                        // right: (A, A' -> Gamma_3)

                        let a = ng.generate(); // type A
                        let res = ng.generate(); // type (A' -> Gamma_3)
                        let b = ng.generate(); // type B
                        let res2 = ng.generate(); // type (B' -> A')
                        let bprime = ng.generate(); // type B'
                        Expr::Let {
                            pattern: Pattern::Tuple(
                                vec![
                                    Pattern::Var(a, "a".to_owned(), span.clone()),
                                    Pattern::Var(res, "res".to_owned(), span.clone()),
                                ],
                                span.clone(),
                            ),
                            value: Box::new(right),
                            body: Box::new(Expr::Let {
                                pattern: Pattern::Tuple(
                                    vec![
                                        Pattern::Var(b, "b".to_owned(), span.clone()),
                                        Pattern::Var(res2, "res2".to_owned(), span.clone()),
                                    ],
                                    span.clone(),
                                ),
                                value: Box::new(Expr::App(
                                    Box::new(Expr::Var(left_core, span.clone())),
                                    Box::new(Expr::Var(a, span.clone())),
                                    span.clone(),
                                )),
                                body: Box::new(Expr::Tuple(
                                    vec![
                                        Expr::Var(b, span.clone()),
                                        Expr::Lambda {
                                            pattern: Pattern::Var(
                                                bprime,
                                                "bp".to_owned(),
                                                span.clone(),
                                            ),
                                            body: Box::new(Expr::App(
                                                Box::new(Expr::Var(res, span.clone())),
                                                Box::new(Expr::App(
                                                    Box::new(Expr::Var(res2, span.clone())),
                                                    Box::new(Expr::Var(bprime, span.clone())),
                                                    span.clone(),
                                                )),
                                                span.clone(),
                                            )),
                                            span: span.clone(),
                                        },
                                    ],
                                    span.clone(),
                                )),
                                span: span.clone(),
                            }),
                            span,
                        }
                    })
                }
            }
        }
        infer::Lens::Literal(_, _) => {
            unreachable!("literal lenses are rejected by the type checker")
        }
    }
}

#[derive(Debug, Default, Clone)]
struct Ctx {
    /// Stores the name that this variable currently has in the *linear* context
    /// (which doesn't use de Bruijn indexing).
    /// If this is None, the variable is dead.
    vars: VecDeque<Option<CoreName>>,
}

impl Ctx {
    fn extend<'src>(&mut self, ng: &mut CoreNameGen, pattern: &infer::Pattern<'src>) -> Pattern {
        match pattern {
            infer::Pattern::Var(name, _, span) => {
                let core = ng.generate();
                self.vars.push_front(Some(core));
                Pattern::Var(core, name.to_string(), span.clone())
            }
            infer::Pattern::Literal(literal, span) => {
                Pattern::Literal(literal.clone().clone(), span.clone())
            }
            infer::Pattern::Tuple(patterns, span) => Pattern::Tuple(
                patterns.iter().map(|pat| self.extend(ng, pat)).collect(),
                span.clone(),
            ),
            infer::Pattern::EmptyList(span) => Pattern::EmptyList(span.clone()),
            infer::Pattern::Cons(head, tail, span) => Pattern::Cons(
                Box::new(self.extend(ng, head)),
                Box::new(self.extend(ng, tail)),
                span.clone(),
            ),
            infer::Pattern::Left(pat, span) => {
                Pattern::Left(Box::new(self.extend(ng, pat)), span.clone())
            }
            infer::Pattern::Right(pat, span) => {
                Pattern::Right(Box::new(self.extend(ng, pat)), span.clone())
            }
        }
    }

    fn retract<'src>(&mut self, pattern: &infer::Pattern<'src>) {
        match pattern {
            infer::Pattern::Var(_, _, _) => {
                self.vars.pop_front();
            }
            infer::Pattern::Literal(_, _) => {}
            infer::Pattern::Tuple(patterns, _) => {
                patterns.iter().rev().for_each(|pat| self.retract(pat))
            }
            infer::Pattern::EmptyList(_) => {}
            infer::Pattern::Cons(head, tail, _) => {
                self.retract(tail);
                self.retract(head);
            }
            infer::Pattern::Left(pat, _) => self.retract(pat),
            infer::Pattern::Right(pat, _) => self.retract(pat),
        }
    }

    /// Return the pair `A * Gamma` where `expr : A`.
    fn pack<'src>(&self, span: Span, expr: Expr<'src>) -> Expr<'src> {
        Expr::Tuple(
            vec![
                expr,
                Expr::Tuple(
                    self.vars
                        .iter()
                        .filter_map(|core| core.as_ref())
                        .map(|core| Expr::Var(*core, span.clone()))
                        .collect(),
                    span.clone(),
                ),
            ],
            span,
        )
    }

    fn pack_simple<'src>(&self, span: Span) -> Expr<'src> {
        Expr::Tuple(
            self.vars
                .iter()
                .filter_map(|core| core.as_ref())
                .map(|core| Expr::Var(*core, span.clone()))
                .collect(),
            span.clone(),
        )
    }

    /// Return a single expression that unpacks this context from `from : A * Gamma`, then evaluates `A, Gamma |- tail : B`.
    /// The continuation is given the context, as well as the core name for the variable of type `A`.
    fn unpack<'src>(
        &mut self,
        ng: &mut CoreNameGen,
        span: Span,
        name: &str,
        from: Expr<'src>,
        tail: impl FnOnce(&mut Self, &mut CoreNameGen, CoreName) -> Expr<'src>,
    ) -> Expr<'src> {
        let new = ng.generate();
        let pattern = Pattern::Tuple(
            vec![
                Pattern::Var(new, name.to_owned(), span.clone()),
                self.unpack_pattern(ng, span.clone()),
            ],
            span.clone(),
        );
        Expr::Let {
            pattern,
            value: Box::new(from),
            body: Box::new(tail(self, ng, new)),
            span,
        }
    }

    /// Return a single expression that unpacks this context from `from : Gamma`, then evaluates `Gamma |- tail : B`.
    /// The continuation is given the context.
    fn unpack_simple<'src>(
        &mut self,
        ng: &mut CoreNameGen,
        span: Span,
        from: Expr<'src>,
        tail: impl FnOnce(&mut Self, &mut CoreNameGen) -> Expr<'src>,
    ) -> Expr<'src> {
        let pattern = self.unpack_pattern(ng, span.clone());
        Expr::Let {
            pattern,
            value: Box::new(from),
            body: Box::new(tail(self, ng)),
            span,
        }
    }

    fn unpack_pattern(&mut self, ng: &mut CoreNameGen, span: Span) -> Pattern {
        Pattern::Tuple(
            self.vars
                .iter_mut()
                .filter_map(|core| core.as_mut())
                .map(|core| {
                    let new_name = ng.generate();
                    *core = new_name;
                    Pattern::Var(new_name, "v".to_owned(), span.clone())
                })
                .collect(),
            span,
        )
    }

    #[allow(clippy::type_complexity)]
    fn unpack_chain<'src>(
        &mut self,
        errors: &mut Errors,
        ng: &mut CoreNameGen,
        span: Span,
        name: &str,
        mut from: VecDeque<infer::Expr<'src>>,
        tail: Box<dyn FnOnce(&mut Self, &mut CoreNameGen, VecDeque<CoreName>) -> Expr<'src> + 'src>,
    ) -> Expr<'src> {
        match from.pop_front() {
            Some(front) => {
                let front = translate_expr(errors, self, ng, front);
                self.unpack(ng, span.clone(), name, front, |ctx, ng, core| {
                    ctx.unpack_chain(
                        errors,
                        ng,
                        span,
                        name,
                        from,
                        Box::new(move |ctx, ng, mut names| {
                            names.push_front(core);
                            tail(ctx, ng, names)
                        }),
                    )
                })
            }
            None => tail(self, ng, VecDeque::new()),
        }
    }

    /// Restricts to only have the given list of variables.
    /// The rest of the variables are returned as a context of the same length.
    fn restrict(&mut self, vars: &[usize]) -> Ctx {
        Ctx {
            vars: self
                .vars
                .iter_mut()
                .enumerate()
                .map(
                    |(i, core)| {
                        if vars.contains(&i) { None } else { core.take() }
                    },
                )
                .collect(),
        }
    }

    fn corestrict(&mut self, vars: &[usize]) -> Ctx {
        Ctx {
            vars: self
                .vars
                .iter_mut()
                .enumerate()
                .map(
                    |(i, core)| {
                        if vars.contains(&i) { core.take() } else { None }
                    },
                )
                .collect(),
        }
    }

    /// Combine with another context of the same length.
    fn combine(&mut self, other: Ctx) {
        for (core, other_core) in self.vars.iter_mut().zip(other.vars) {
            if let Some(other_core) = other_core {
                *core = Some(other_core);
            }
        }
    }

    /// Convert all of the names to fresh names.
    fn freshen(&self, ng: &mut CoreNameGen) -> Ctx {
        Ctx {
            vars: self
                .vars
                .iter()
                .map(|name| name.map(|_| ng.generate()))
                .collect(),
        }
    }
}

fn reconstruct_pattern<'src>(ctx: &Ctx, pattern: &infer::Pattern<'src>) -> Expr<'src> {
    fn go<'src>(
        ctx: &Ctx,
        mut offset: usize,
        pattern: &infer::Pattern<'src>,
    ) -> (usize, Expr<'src>) {
        match pattern {
            infer::Pattern::Var(_, _, span) => (
                offset + 1,
                Expr::Var(
                    ctx.vars[offset].expect("var not present in context"),
                    span.clone(),
                ),
            ),
            infer::Pattern::Literal(literal, span) => {
                (offset, Expr::Literal(literal.clone(), span.clone()))
            }
            infer::Pattern::Tuple(patterns, span) => {
                let mut patterns = patterns
                    .iter()
                    .rev()
                    .map(|pat| {
                        let (o, e) = go(ctx, offset, pat);
                        offset = o;
                        e
                    })
                    .collect::<Vec<_>>();
                patterns.reverse();
                (offset, Expr::Tuple(patterns, span.clone()))
            }
            infer::Pattern::EmptyList(span) => (offset, Expr::EmptyList(span.clone())),
            infer::Pattern::Cons(head, tail, span) => {
                let (o, tail) = go(ctx, offset, tail);
                offset = o;
                let (o, head) = go(ctx, offset, head);
                (o, Expr::Cons(Box::new(head), Box::new(tail), span.clone()))
            }
            infer::Pattern::Left(pat, span) => {
                let (o, e) = go(ctx, offset, pat);
                (o, Expr::Left(Box::new(e), span.clone()))
            }
            infer::Pattern::Right(pat, span) => {
                let (o, e) = go(ctx, offset, pat);
                (o, Expr::Right(Box::new(e), span.clone()))
            }
        }
    }

    go(ctx, 0, pattern).1
}

#[derive(Debug, Clone)]
pub struct Decl<'src> {
    pub name: &'src str,
    pub span: Span,
    pub ty: Type<'src>,
}

#[derive(Debug, Clone)]
pub struct Def<'src> {
    pub name: &'src str,
    pub span: Span,
    pub expr: Expr<'src>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct CoreName(usize);

pub struct CoreNameGen(usize);

impl CoreNameGen {
    pub fn generate(&mut self) -> CoreName {
        let result = self.0;
        self.0 += 1;
        CoreName(result)
    }
}

impl Debug for CoreName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

impl Display for CoreName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

#[derive(Clone)]
pub enum Expr<'src> {
    /// Numerically named. Names are never duplicated.
    Var(CoreName, Span),
    Inst {
        name: &'src str,
        subst: BTreeMap<&'src str, Type<'src>>,
        span: Span,
    },
    App(Box<Expr<'src>>, Box<Expr<'src>>, Span),
    Literal(Literal, Span),
    PrimOp(Box<Expr<'src>>, Box<Expr<'src>>, PrimOp, Span),
    Tuple(Vec<Expr<'src>>, Span),
    EmptyList(Span),
    Cons(Box<Expr<'src>>, Box<Expr<'src>>, Span),
    Left(Box<Expr<'src>>, Span),
    Right(Box<Expr<'src>>, Span),
    Let {
        pattern: Pattern,
        value: Box<Expr<'src>>,
        body: Box<Expr<'src>>,
        span: Span,
    },
    Case {
        scrutinee: Box<Expr<'src>>,
        branches: Vec<(Pattern, Expr<'src>)>,
        span: Span,
    },
    Lambda {
        pattern: Pattern,
        body: Box<Expr<'src>>,
        span: Span,
    },
}

impl<'src> Expr<'src> {
    fn fmt_prec(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        ctx: &BTreeMap<CoreName, String>,
        prec: u32,
        haskell: bool,
    ) -> std::fmt::Result {
        match self {
            Expr::Var(name, _) => match ctx.get(name) {
                Some(name) => write!(f, "{name}"),
                None => write!(f, "{name}"),
            },
            Expr::Inst { name, .. } => write!(f, "{name}"),
            Expr::App(left, right, _) => {
                if prec > 15 {
                    write!(f, "(")?;
                }
                left.fmt_prec(f, ctx, 15, haskell)?;
                write!(f, " ")?;
                right.fmt_prec(f, ctx, 16, haskell)?;
                if prec > 15 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Literal(Literal::Integer(n), _) if haskell => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                write!(f, "{n} :: Int")?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Literal(literal, _) => write!(f, "{literal}"),
            Expr::PrimOp(left, right, prim_op, _) => {
                let (op_prec, left_prec, right_prec) = match *prim_op {
                    PrimOp::Mul => (10, 10, 11),
                    PrimOp::Div => {
                        if haskell {
                            (15, 16, 16)
                        } else {
                            (10, 10, 11)
                        }
                    }
                    PrimOp::Add => (8, 8, 9),
                    PrimOp::Sub => (8, 8, 9),
                    PrimOp::Eq => (5, 5, 6),
                    PrimOp::Seq => {
                        if prec > 0 {
                            write!(f, "(")?;
                        }
                        if haskell {
                            write!(f, "case ")?;
                            left.fmt_prec(f, ctx, 1, haskell)?;
                            write!(f, " of () -> ")?;
                            right.fmt_prec(f, ctx, 0, haskell)?;
                        } else {
                            write!(f, "let () = ")?;
                            left.fmt_prec(f, ctx, 1, haskell)?;
                            write!(f, " in ")?;
                            right.fmt_prec(f, ctx, 0, haskell)?;
                        }
                        if prec > 0 {
                            write!(f, ")")?;
                        }
                        return Ok(());
                    }
                };

                if prec > op_prec {
                    write!(f, "(")?;
                }
                left.fmt_prec(f, ctx, left_prec, haskell)?;
                if *prim_op == PrimOp::Div && haskell {
                    write!(f, " `div` ")?;
                } else {
                    write!(f, " {prim_op} ")?;
                }
                right.fmt_prec(f, ctx, right_prec, haskell)?;
                if prec > op_prec {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Tuple(exprs, _) => {
                if exprs.len() == 1 {
                    // Visually flatten 1-tuples.
                    exprs[0].fmt_prec(f, ctx, prec, haskell)
                } else {
                    write!(f, "(")?;
                    match exprs.len() {
                        0 => {}
                        1 => {
                            exprs.first().unwrap().fmt_prec(f, ctx, 0, haskell)?;
                            write!(f, ",")?;
                        }
                        _ => {
                            for (i, item) in exprs.iter().enumerate() {
                                if i != 0 {
                                    write!(f, ", ")?;
                                }
                                item.fmt_prec(f, ctx, 0, haskell)?;
                            }
                        }
                    }
                    write!(f, ")")
                }
            }
            Expr::EmptyList(_) => write!(f, "[]"),
            Expr::Cons(head, tail, _) => {
                if let Expr::Literal(Literal::Char(c), _) = **head {
                    // Check if this is a string, and if so, print it prettier.
                    // This is a silly O(n) check.
                    let mut string = String::from(c);
                    let mut recursive_tail = tail;
                    loop {
                        match &**recursive_tail {
                            Expr::Cons(left, right, _) => {
                                if let Expr::Literal(Literal::Char(c), _) = &**left {
                                    string.push(*c);
                                    recursive_tail = right;
                                } else {
                                    // This isn't a string. Fall back to the default procedure.
                                    break;
                                }
                            }
                            Expr::EmptyList(_) => {
                                // This is a string, so just print it.
                                return write!(f, "{string:?}");
                            }
                            _ => {
                                // This isn't a string. Fall back to the default procedure.
                                break;
                            }
                        }
                    }
                }

                if prec > 6 {
                    write!(f, "(")?;
                }
                head.fmt_prec(f, ctx, 7, haskell)?;
                write!(f, ":")?;
                tail.fmt_prec(f, ctx, 6, haskell)?;
                if prec > 6 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Let {
                pattern,
                value,
                body,
                ..
            } => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                let mut new_ctx = ctx.clone();
                if haskell {
                    write!(f, "case ")?;
                    value.fmt_prec(f, ctx, 1, haskell)?;
                    write!(f, " of ")?;
                    pattern.fmt_prec(f, &mut new_ctx, 0, haskell)?;
                    write!(f, " -> ")?;
                    body.fmt_prec(f, &new_ctx, 0, haskell)?;
                } else {
                    write!(f, "let ")?;
                    pattern.fmt_prec(f, &mut new_ctx, 0, haskell)?;
                    write!(f, " = ")?;
                    value.fmt_prec(f, ctx, 1, haskell)?;
                    write!(f, " in ")?;
                    body.fmt_prec(f, &new_ctx, 0, haskell)?;
                }
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Case {
                scrutinee,
                branches,
                ..
            } => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                write!(f, "case ")?;
                scrutinee.fmt_prec(f, ctx, 1, haskell)?;
                write!(f, " of {{ ")?;
                for (pattern, body) in branches {
                    let mut new_ctx = ctx.clone();
                    pattern.fmt_prec(f, &mut new_ctx, 0, haskell)?;
                    write!(f, " -> ")?;
                    body.fmt_prec(f, &new_ctx, 1, haskell)?;
                    write!(f, "; ")?;
                }
                write!(f, " }}")?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Lambda { pattern, body, .. } => {
                if prec > 0 {
                    write!(f, "(")?;
                }
                let mut ctx = ctx.clone();
                write!(f, "\\")?;
                pattern.fmt_prec(f, &mut ctx, 0, haskell)?;
                write!(f, " -> ")?;
                body.fmt_prec(f, &ctx, 0, haskell)?;
                if prec > 0 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Left(pat, _) => {
                if prec > 15 {
                    write!(f, "(")?;
                }
                write!(f, "Left ")?;
                pat.fmt_prec(f, ctx, 16, haskell)?;
                if prec > 15 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Expr::Right(pat, _) => {
                if prec > 15 {
                    write!(f, "(")?;
                }
                write!(f, "Right ")?;
                pat.fmt_prec(f, ctx, 16, haskell)?;
                if prec > 15 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl<'src> Debug for Expr<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, &Default::default(), 0, false)
    }
}

impl<'src> Display for Expr<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, &Default::default(), 0, false)
    }
}

pub struct HaskellExpr<'a, 'src>(pub &'a Expr<'src>);

impl<'a, 'src> Display for HaskellExpr<'a, 'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_prec(f, &Default::default(), 0, true)
    }
}

#[derive(Clone)]
pub enum Pattern {
    /// The string here is just for printing.
    Var(CoreName, String, Span),
    Literal(Literal, Span),
    Tuple(Vec<Pattern>, Span),
    EmptyList(Span),
    Cons(Box<Pattern>, Box<Pattern>, Span),
    Left(Box<Pattern>, Span),
    Right(Box<Pattern>, Span),
}

impl Pattern {
    fn fmt_prec(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        ctx: &mut BTreeMap<CoreName, String>,
        prec: u32,
        haskell: bool,
    ) -> std::fmt::Result {
        match self {
            Pattern::Var(index, name, _) => {
                let mut suffix = None::<i32>;
                loop {
                    let new_name = match &suffix {
                        Some(suffix) => format!("{name}{suffix}"),
                        None => name.to_string(),
                    };
                    if ctx.iter().any(|(_, name)| *name == new_name) {
                        suffix = Some(suffix.map(|x| x + 1).unwrap_or_default());
                    } else {
                        ctx.insert(*index, new_name.clone());
                        return write!(f, "{new_name}");
                    }
                }
            }
            Pattern::Literal(literal, _) => write!(f, "{literal}"),
            Pattern::Tuple(patterns, _) => {
                if patterns.len() == 1 {
                    // Visually flatten 1-tuples.
                    patterns[0].fmt_prec(f, ctx, prec, haskell)
                } else {
                    write!(f, "(")?;
                    match patterns.len() {
                        0 => {}
                        1 => {
                            patterns.first().unwrap().fmt_prec(f, ctx, 0, haskell)?;
                            write!(f, ",")?;
                        }
                        _ => {
                            for (i, item) in patterns.iter().enumerate() {
                                if i != 0 {
                                    write!(f, ", ")?;
                                }
                                item.fmt_prec(f, ctx, 0, haskell)?;
                            }
                        }
                    }
                    write!(f, ")")
                }
            }
            Pattern::EmptyList(_) => write!(f, "[]"),
            Pattern::Cons(head, tail, _) => {
                if prec > 6 {
                    write!(f, "(")?;
                }
                head.fmt_prec(f, ctx, 7, haskell)?;
                write!(f, ":")?;
                tail.fmt_prec(f, ctx, 6, haskell)?;
                if prec > 6 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Pattern::Left(pat, _) => {
                if prec > 15 {
                    write!(f, "(")?;
                }
                write!(f, "Left ")?;
                pat.fmt_prec(f, ctx, 16, haskell)?;
                if prec > 15 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Pattern::Right(pat, _) => {
                if prec > 15 {
                    write!(f, "(")?;
                }
                write!(f, "Right ")?;
                pat.fmt_prec(f, ctx, 16, haskell)?;
                if prec > 15 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl Debug for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, &mut Default::default(), 0, false)
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, &mut Default::default(), 0, false)
    }
}

#[derive(Clone)]
pub enum Type<'src> {
    Var(&'src str, Span),
    Prim(PrimTy, Span),
    Arrow(Box<Type<'src>>, Box<Type<'src>>, Span),
    Tuple(Vec<Type<'src>>, Span),
    Either(Box<Type<'src>>, Box<Type<'src>>, Span),
    List(Box<Type<'src>>, Span),
    Tree(Box<Type<'src>>, Span),
}

impl<'src> Type<'src> {
    fn span(&self) -> Span {
        match self {
            Type::Prim(_, span) => span.clone(),
            Type::Var(_, span) => span.clone(),
            Type::Arrow(_, _, span) => span.clone(),
            Type::Tuple(_, span) => span.clone(),
            Type::Either(_, _, span) => span.clone(),
            Type::List(_, span) => span.clone(),
            Type::Tree(_, span) => span.clone(),
        }
    }

    fn fmt_prec(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        prec: u32,
        haskell: bool,
    ) -> std::fmt::Result {
        match self {
            Type::Prim(prim_ty, _) => write!(f, "{prim_ty:?}"),
            Type::Var(name, _) => write!(f, "{name}"),
            Type::Arrow(left, right, _) => {
                if prec > 1 {
                    write!(f, "(")?;
                }
                left.fmt_prec(f, 2, haskell)?;
                if haskell {
                    write!(f, " %1 -> ")?;
                } else {
                    write!(f, " -> ")?;
                }
                right.fmt_prec(f, 1, haskell)?;
                if prec > 1 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::Tuple(items, _) => {
                match items.len() {
                    0 => {
                        write!(f, "()")
                    }
                    1 => {
                        // Visually flatten 1-tuples.
                        items.first().unwrap().fmt_prec(f, prec, haskell)
                    }
                    _ => {
                        write!(f, "(")?;
                        for (i, item) in items.iter().enumerate() {
                            if i != 0 {
                                write!(f, ", ")?;
                            }
                            item.fmt_prec(f, 0, haskell)?;
                        }
                        write!(f, ")")
                    }
                }
            }
            Type::Either(left, right, _) => {
                if prec > 10 {
                    write!(f, "(")?;
                }
                write!(f, "Either ")?;
                left.fmt_prec(f, 11, haskell)?;
                write!(f, " ")?;
                right.fmt_prec(f, 10, haskell)?;
                if prec > 10 {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Type::List(t, _) => {
                if haskell {
                    write!(f, "[")?;
                    t.fmt_prec(f, 0, haskell)?;
                    write!(f, "]")
                } else {
                    if prec > 10 {
                        write!(f, "(")?;
                    }
                    write!(f, "List ")?;
                    t.fmt_prec(f, 11, haskell)?;
                    if prec > 10 {
                        write!(f, ")")?;
                    }
                    Ok(())
                }
            }
            Type::Tree(t, _) => {
                if prec > 10 {
                    write!(f, "(")?;
                }
                write!(f, "Tree ")?;
                t.fmt_prec(f, 11, haskell)?;
                if prec > 10 {
                    write!(f, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl<'src> Debug for Type<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, 0, false)
    }
}

impl<'src> Display for Type<'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_prec(f, 0, false)
    }
}

pub struct HaskellType<'a, 'src>(pub &'a Type<'src>);

impl<'a, 'src> Display for HaskellType<'a, 'src> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_prec(f, 0, true)
    }
}

impl<'src> From<rename::Type<'src>> for Type<'src> {
    fn from(value: rename::Type<'src>) -> Self {
        match value {
            rename::Type::Var(name, span) => Type::Var(name, span),
            rename::Type::Prim(prim_ty, span) => Type::Prim(prim_ty, span),
            rename::Type::Arrow(left, right, span) => match (*left, *right) {
                (rename::TType::Plain(left), rename::TType::Plain(right)) => {
                    Type::Arrow(Box::new(left.into()), Box::new(right.into()), span)
                }
                (rename::TType::Plain(left), rename::TType::Flow(right1, right2)) => Type::Arrow(
                    Box::new(left.into()),
                    Box::new(Type::Tuple(
                        vec![
                            right1.into(),
                            Type::Arrow(
                                Box::new(right2.into()),
                                Box::new(Type::Tuple(Vec::new(), span.clone())),
                                span.clone(),
                            ),
                        ],
                        span.clone(),
                    )),
                    span,
                ),
                (rename::TType::Flow(left1, left2), rename::TType::Plain(right)) => Type::Arrow(
                    Box::new(left1.into()),
                    Box::new(Type::Tuple(vec![right.into(), left2.into()], span.clone())),
                    span,
                ),
                (rename::TType::Flow(left1, left2), rename::TType::Flow(right1, right2)) => {
                    Type::Arrow(
                        Box::new(left1.into()),
                        Box::new(Type::Tuple(
                            vec![
                                right1.into(),
                                Type::Arrow(
                                    Box::new(right2.into()),
                                    Box::new(left2.into()),
                                    span.clone(),
                                ),
                            ],
                            span.clone(),
                        )),
                        span,
                    )
                }
            },
            rename::Type::Tuple(items, span) => {
                Type::Tuple(items.into_iter().map(|x| x.into()).collect(), span)
            }
            rename::Type::Either(l, r, span) => {
                Type::Either(Box::new((*l).into()), Box::new((*r).into()), span)
            }
            rename::Type::List(t, span) => Type::List(Box::new((*t).into()), span),
            rename::Type::Tree(t, span) => Type::Tree(Box::new((*t).into()), span),
        }
    }
}

impl<'src> Expr<'src> {
    fn subst(&mut self, name: CoreName, subst: &Expr<'src>) {
        match self {
            Expr::Var(var_name, _) => {
                if name == *var_name {
                    *self = subst.clone();
                }
            }
            Expr::Inst { .. } => {}
            Expr::App(left, right, _) => {
                left.subst(name, subst);
                right.subst(name, subst);
            }
            Expr::Literal(_, _) => {}
            Expr::PrimOp(left, right, _, _) => {
                left.subst(name, subst);
                right.subst(name, subst);
            }
            Expr::Tuple(exprs, _) => {
                for expr in exprs {
                    expr.subst(name, subst);
                }
            }
            Expr::EmptyList(_) => {}
            Expr::Cons(left, right, _) => {
                left.subst(name, subst);
                right.subst(name, subst);
            }
            Expr::Left(expr, _) => {
                expr.subst(name, subst);
            }
            Expr::Right(expr, _) => {
                expr.subst(name, subst);
            }
            Expr::Let { value, body, .. } => {
                value.subst(name, subst);
                body.subst(name, subst);
            }
            Expr::Case {
                scrutinee,
                branches,
                ..
            } => {
                scrutinee.subst(name, subst);
                for branch in branches {
                    branch.1.subst(name, subst);
                }
            }
            Expr::Lambda { body, .. } => {
                body.subst(name, subst);
            }
        }
    }

    fn optimise(&mut self, ng: &mut CoreNameGen) {
        match self {
            Expr::Var(_, _) => {}
            Expr::Inst { .. } => {}
            Expr::App(left, right, _) => {
                left.optimise(ng);
                right.optimise(ng);
                if let Expr::Lambda {
                    pattern,
                    body,
                    span,
                } = &mut **left
                {
                    *self = Expr::Let {
                        pattern: std::mem::replace(pattern, Pattern::EmptyList(0..0)),
                        value: Box::new(std::mem::replace(&mut **right, Expr::EmptyList(0..0))),
                        body: Box::new(std::mem::replace(&mut **body, Expr::EmptyList(0..0))),
                        span: span.clone(),
                    };
                    self.optimise(ng);
                }
            }
            Expr::Literal(_, _) => {}
            Expr::PrimOp(left, right, prim_op, span) => {
                if *prim_op == PrimOp::Seq {
                    *self = Expr::Let {
                        pattern: Pattern::Tuple(Vec::new(), span.clone()),
                        value: Box::new(std::mem::replace(left, Expr::EmptyList(0..0))),
                        body: Box::new(std::mem::replace(right, Expr::EmptyList(0..0))),
                        span: span.clone(),
                    };
                    self.optimise(ng);
                } else {
                    left.optimise(ng);
                    right.optimise(ng);
                }
            }
            Expr::Tuple(exprs, _) => {
                for expr in exprs {
                    expr.optimise(ng);
                }
            }
            Expr::EmptyList(_) => {}
            Expr::Cons(left, right, _) => {
                left.optimise(ng);
                right.optimise(ng);
            }
            Expr::Left(expr, _) => {
                expr.optimise(ng);
            }
            Expr::Right(expr, _) => {
                expr.optimise(ng);
            }
            Expr::Let {
                pattern,
                value,
                body,
                span,
            } => {
                value.optimise(ng);
                body.optimise(ng);
                match (&mut *pattern, &mut **value) {
                    (Pattern::Tuple(patterns, _), Expr::Tuple(exprs, _))
                        if patterns.len() == exprs.len() =>
                    {
                        // Case-of-known-constructor.
                        let patterns = std::mem::take(patterns);
                        let exprs = std::mem::take(exprs);
                        *self = patterns
                            .into_iter()
                            .rev()
                            .zip(exprs.into_iter().rev())
                            .fold(
                                std::mem::replace(&mut **body, Expr::EmptyList(0..0)),
                                |body, (pattern, expr)| Expr::Let {
                                    pattern,
                                    value: Box::new(expr),
                                    body: Box::new(body),
                                    span: span.clone(),
                                },
                            );
                        // There are more efficient ways to do this recursive call without work duplication.
                        self.optimise(ng);
                    }
                    (
                        _,
                        Expr::Let {
                            pattern: inner_pattern,
                            value: inner_value,
                            body: inner_body,
                            ..
                        },
                    ) => {
                        // Case-of-case.
                        // let p1 = (let p2 = e1 in e2) in e3
                        // -->
                        // let p2 = e1 in (let p1 = e2 in e3)
                        *self = Expr::Let {
                            pattern: std::mem::replace(inner_pattern, Pattern::EmptyList(0..0)),
                            value: Box::new(std::mem::replace(inner_value, Expr::EmptyList(0..0))),
                            body: Box::new(Expr::Let {
                                pattern: std::mem::replace(pattern, Pattern::EmptyList(0..0)),
                                value: Box::new(std::mem::replace(
                                    inner_body,
                                    Expr::EmptyList(0..0),
                                )),
                                body: Box::new(std::mem::replace(body, Expr::EmptyList(0..0))),
                                span: span.clone(),
                            }),
                            span: span.clone(),
                        };
                        self.optimise(ng);
                    }
                    (Pattern::Var(pat_name, _, _), e) => {
                        // Let-binding a single variable.
                        // This is always a valid optimisation by linearity.
                        body.subst(*pat_name, e);
                        *self = std::mem::replace(body, Expr::EmptyList(0..0));
                        self.optimise(ng);
                    }
                    (
                        outer_pattern,
                        Expr::Case {
                            scrutinee,
                            branches,
                            ..
                        },
                    ) => {
                        // Case-of-case.
                        // let p = (case e of { pi -> ei }) in e'
                        // -->
                        // case e of { pi -> let p = ei in e' }
                        *self = Expr::Case {
                            scrutinee: Box::new(std::mem::replace(
                                scrutinee,
                                Expr::EmptyList(0..0),
                            )),
                            branches: std::mem::take(branches)
                                .into_iter()
                                .map(|(pat, expr)| {
                                    (
                                        pat,
                                        Expr::Let {
                                            pattern: outer_pattern.clone(),
                                            value: Box::new(expr),
                                            body: body.clone(),
                                            span: span.clone(),
                                        },
                                    )
                                })
                                .collect(),
                            span: span.clone(),
                        };
                        self.optimise(ng);
                    }
                    _ => {}
                }
            }
            Expr::Case {
                scrutinee,
                branches,
                ..
            } => {
                scrutinee.optimise(ng);
                for branch in branches {
                    branch.1.optimise(ng);
                }
                match scrutinee {
                    _ => {}
                }
            }
            Expr::Lambda { body, .. } => {
                body.optimise(ng);
            }
        }
    }
}
