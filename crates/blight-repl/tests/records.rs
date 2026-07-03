//! Records (`defrecord`) — v0.1 roadmap arc E, milestone E4. Named-field record sugar lowering
//! to a **single-constructor `defdata`** (nominal type + `mk-<Name>` constructor + match-based
//! projection `deftotal`s + a `(<Name>-with r (field v))` functional-update rewrite). The design
//! was re-verified against the codebase before implementation (see the roadmap's E4 section):
//! records-as-Sigma would lose dependent-index refinement, nominality, and codegen unboxing —
//! these tests pin the *behavioral* contract, which is encoding-agnostic at the surface.

use blight_elab::{ElabError, Outcome, Program};

/// Run `src` in a fresh env on a large stack and hand the result to `check` on the worker
/// thread (post-S3, `Term` holds `Rc`s, so `Outcome`/`ElabError` cannot cross `join`).
fn run_with<R: Send + 'static>(
    src: String,
    check: impl FnOnce(Result<Vec<Outcome>, ElabError>) -> R + Send + 'static,
) -> R {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let mut env = blight_elab::ElabEnv::new();
            let mut prog = Program::new(&mut env);
            let result = prog.run(&src);
            check(result)
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

/// Like [`run_with`] but also hands the closure the resulting env (for global/constructor
/// assertions), still on the worker thread.
fn run_with_env<R: Send + 'static>(
    src: String,
    check: impl FnOnce(Result<Vec<Outcome>, ElabError>, &blight_elab::ElabEnv) -> R + Send + 'static,
) -> R {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            let mut env = blight_elab::ElabEnv::new();
            let result = {
                let mut prog = Program::new(&mut env);
                prog.run(&src)
            };
            check(result, &env)
        })
        .expect("spawn")
        .join()
        .expect("thread panicked")
}

const NAT: &str = "(defdata Nat () (Zero) (Succ (n Nat)))\n\
    (define-rec plus (Pi ((a Nat) (b Nat)) Nat)\n\
      (lam (a b) (match a [(Zero) b] [(Succ n) (Succ (plus n b))])))\n";

const POINT: &str = "(defrecord Point ((x Nat) (y Nat)))\n";

/// `(defrecord Point ((x Nat) (y Nat)))` registers `Point` as a single-constructor datatype
/// (constructor `mk-Point`) with projection globals `Point-x`/`Point-y` that compute: the
/// kernel accepts `refl`-style paths projecting from a literal record.
#[test]
fn defrecord_declares_type_ctor_and_projections() {
    run_with_env(
        format!(
            "{NAT}{POINT}\
             (the (Path Nat (Point-x (mk-Point 3 4)) 3) (plam (i) 3))\n\
             (the (Path Nat (Point-y (mk-Point 3 4)) 4) (plam (i) 4))"
        ),
        |r, env| {
            let outcomes = r.expect("defrecord + projections type-check");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "every form accepted: {outcomes:?}"
            );
            let ctors = env
                .data_constructors("Point")
                .expect("Point is a registered datatype");
            assert_eq!(ctors, vec!["mk-Point".to_string()], "single constructor mk-Point");
            for g in ["Point-x", "Point-y"] {
                assert!(env.global_term(g).is_some(), "projection `{g}` is a global");
            }
        },
    );
}

/// `(Point-with p (y 5))` rewrites to a rebuilt constructor application — projections of the
/// updated record compute to the new value on the updated field and the old value elsewhere.
#[test]
fn field_update_rebuilds_constructor_application() {
    run_with(
        format!(
            "{NAT}{POINT}\
             (define p Point (mk-Point 3 4))\n\
             (define q Point (Point-with p (y 5)))\n\
             (the (Path Nat (Point-y q) 5) (plam (i) 5))\n\
             (the (Path Nat (Point-x q) 3) (plam (i) 3))"
        ),
        |r| {
            let outcomes = r.expect("functional update type-checks and computes");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "every form accepted: {outcomes:?}"
            );
        },
    );
}

/// `(Point-with p (z 5))` fails with a dedicated diagnostic that names the unknown field —
/// never a generic no-rule/macro error.
#[test]
fn unknown_field_in_update_rejected() {
    run_with(
        format!(
            "{NAT}{POINT}\
             (define p Point (mk-Point 3 4))\n\
             (define q Point (Point-with p (z 5)))"
        ),
        |r| {
            let err = r.expect_err("unknown field must be rejected");
            let ElabError::BadForm(m) = &err else {
                panic!("expected a BadForm diagnostic, got {err:?}")
            };
            assert!(
                m.contains('z') && m.contains("field"),
                "diagnostic names the unknown field `z`: {m}"
            );
        },
    );
}

/// A record type works in dependent positions: as a `Pi`-domain whose body matches on the
/// record, and as a `defdata` field — with per-arm refinement (the `Con`-refinement property
/// that drove the defdata lowering; a Sigma encoding goes stuck here).
#[test]
fn record_in_dependent_position_checks() {
    run_with(
        format!(
            "{NAT}{POINT}\
             (deftotal norm (Pi ((p Point)) Nat)\n\
               (lam (p) (match p [(mk-Point a b) (plus a b)])))\n\
             (the (Path Nat (norm (mk-Point 2 3)) 5) (plam (i) 5))\n\
             (defdata Tagged () (tag (pt Point) (n Nat)))\n\
             (deftotal untag (Pi ((t Tagged)) Nat)\n\
               (lam (t) (match t [(tag pt n) (plus (Point-x pt) n)])))\n\
             (the (Path Nat (untag (tag (mk-Point 1 2) 3)) 4) (plam (i) 4))"
        ),
        |r| {
            let outcomes = r.expect("records in dependent positions check and compute");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "every form accepted: {outcomes:?}"
            );
        },
    );
}

/// Malformed shapes each fail with a shape diagnostic (the measure.rs/defn.rs cheap-check
/// pattern): wrong arity, a non-`(name Ty)` field entry, and duplicate field names.
#[test]
fn defrecord_rejects_malformed_shape() {
    for (label, src) in [
        ("wrong arity (2 items)", "(defrecord Point)"),
        (
            "wrong arity (4 items)",
            "(defrecord Point ((x Nat)) extra)",
        ),
        ("non-binder field entry", "(defrecord Point (x))"),
        (
            "duplicate field names",
            "(defrecord Point ((x Nat) (x Nat)))",
        ),
    ] {
        run_with(format!("{NAT}{src}"), move |r| {
            let err = r.expect_err(label);
            assert!(
                matches!(&err, ElabError::BadForm(m) if m.contains("defrecord")),
                "{label}: shape diagnostic mentions defrecord, got {err:?}"
            );
        });
    }
}

/// A pre-existing global or constructor colliding with a generated name (`mk-Point`,
/// `Point-x`, `Point-with`) fails cleanly and atomically — no partial environment state.
#[test]
fn generated_name_collision_rejected() {
    run_with_env(
        format!(
            "{NAT}\
             (define Point-x Nat Zero)\n\
             (defrecord Point ((x Nat) (y Nat)))"
        ),
        |r, env| {
            assert!(r.is_err(), "generated-name collision must be rejected");
            assert!(
                env.data_constructors("Point").is_none(),
                "atomic failure: no partial Point registration"
            );
        },
    );
}

/// Records are ordinary inductives to the rest of the tower: a user `match` on the `mk-Point`
/// pattern type-checks, E3 reports the single-constructor match exhaustive, and an E5 `defn`
/// with a `mk-Point` pattern column compiles.
#[test]
fn record_constructor_match_and_coverage() {
    run_with(
        format!(
            "{NAT}{POINT}\
             (defn swap (Pi ((p Point)) Point)\n\
               [((mk-Point a b)) (mk-Point b a)])\n\
             (the (Path Nat (Point-x (swap (mk-Point 1 2))) 2) (plam (i) 2))"
        ),
        |r| {
            let outcomes = r.expect("defn over a record pattern compiles and computes");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "every form accepted: {outcomes:?}"
            );
        },
    );
}

/// Dependent field types: a later field's type may mention earlier fields (defdata telescopes
/// already elaborate this — Sigma-telescope parity under the defdata lowering).
#[test]
fn dependent_field_types_check() {
    run_with(
        format!(
            "{NAT}\
             (defdata Vec ((n Nat)) (vnil) (vcons (m Nat) (tl (Vec m))))\n\
             (defrecord Sized ((len Nat) (items (Vec len))))\n\
             (define s Sized (mk-Sized Zero vnil))\n\
             (the (Path Nat (Sized-len s) Zero) (plam (i) Zero))"
        ),
        |r| {
            let outcomes = r.expect("dependent field types elaborate and check");
            assert!(
                outcomes
                    .iter()
                    .all(|o| matches!(o, Outcome::Declared | Outcome::Checked(_))),
                "every form accepted: {outcomes:?}"
            );
        },
    );
}
