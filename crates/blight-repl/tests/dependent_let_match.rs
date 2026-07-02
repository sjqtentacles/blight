//! Regression tests for two elaborator de-Bruijn/substitution bugs found while implementing
//! `std/map.bl` (roadmap Wave 2 / L1): both silently corrupted a term's indices whenever a `let`
//! (including one implicitly introduced by lowering a `match` whose scrutinee is not a bare
//! variable) sat under a function parameter that the enclosing type depended on. Black-box: the
//! `blight-elab` public `Program` driver only.
//!
//! Bug 1 — `Surface::Let`/`Surface::Region` reused the *unweakened* `expected` type to check the
//! let-body under a scope with one extra binder (the let-bound variable), mixing de Bruijn
//! baselines. Any polymorphic function whose result type mentions an earlier parameter (e.g.
//! `Pi ((A (Type 0)) (x A)) A`) and whose body contains a `let` (or an auto-lowered `match` on a
//! non-variable scrutinee) hit a spurious kernel rejection.
//!
//! Bug 2 — `subst0_closed` (used by `synth_type`'s `App` case, among others) substituted its
//! argument verbatim regardless of how many binders the substitution site sat under, silently
//! corrupting the synthesized type of any call to a polymorphic function whose declared type
//! mentions its type parameter at more than one nesting depth (e.g. `Pi (A) (Pi (x A) A)`, where
//! the codomain's occurrence of `A` sits one binder deeper than the domain's).
//!
//! A third, narrower gap surfaced once both were fixed: constructor field types were only ever
//! "read off" for *param-free* families, so a `match` on a *parametric* type (e.g. `Maybe`) whose
//! scrutinee came from a non-variable expression (again triggering the `let`-lowering path) could
//! still fail to type — fixed by substituting the scrutinee's actual parameters into the
//! constructor's declared field type.

use blight_elab::{ElabEnv, Outcome, Program};

#[path = "support/mod.rs"]
mod support;
use support::prelude_resolver;

/// Elaborate `src` (no prelude needed) and assert every form was accepted.
fn run_ok(src: &str) {
    let mut env = ElabEnv::new();
    let mut prog = Program::with_resolver(&mut env, prelude_resolver);
    let outcomes = prog
        .run(src)
        .unwrap_or_else(|e| panic!("expected `{src}` to elaborate cleanly, got: {e:?}"));
    assert!(
        outcomes.iter().all(|o| matches!(o, Outcome::Declared)),
        "every form in `{src}` is a well-typed declaration: {outcomes:?}"
    );
}

/// Bug 1, minimal case: a `let` under a dependent return type (`A`, the function's own first
/// parameter) used to corrupt the expected type's de Bruijn indices.
#[test]
fn let_under_dependent_return_type_typechecks() {
    run_ok(
        r#"
(defdata Unit () (tt))
(define foo
  (Pi ((A (Type 0)) (key A)) A)
  (lam (A key)
    (let ((y tt)) key)))
"#,
    );
}

/// Bug 1, via `match`'s implicit `let`-lowering: a `match` whose scrutinee is *not* a bare
/// variable (here, an application of `compare`) is desugared to a `let` internally; the same
/// dependent-return-type corruption applied there too.
#[test]
fn match_on_nonvar_scrutinee_under_dependent_return_type_typechecks() {
    run_ok(
        r#"
(defdata Ordering () (LT) (EQ) (GT))
(define foo
  (Pi ((A (Type 0)) (compare (Pi ((x A) (y A)) Ordering)) (key A) (x A)) A)
  (lam (A compare key x)
    (let ((s (compare key x)))
      (match s
        [(LT) key]
        [(EQ) key]
        [(GT) key]))))
"#,
    );
}

/// Bug 2, minimal case: calling a polymorphic function (`id-poly`) whose declared type mentions
/// its type parameter at two different nesting depths (`Pi (A) (Pi (x A) A)`) used to synthesize a
/// corrupted type for the call, because `subst0_closed` substituted the (non-closed) type argument
/// without shifting it as the substitution descended under the codomain's own binder.
#[test]
fn polymorphic_call_type_synthesis_is_capture_avoiding() {
    run_ok(
        r#"
(define id-poly (Pi ((A (Type 0)) (x A)) A) (lam (A x) x))
(define foo
  (Pi ((A (Type 0)) (x A)) A)
  (lam (A x) (let ((y (id-poly A x))) y)))
"#,
    );
}

/// Bug 2 combined with the field-type gap: `map-member`'s exact shape — a `match` on a call to a
/// polymorphic function (`Maybe`-returning) whose result is not a bare variable, with a
/// constructor clause (`just v`) binding a field of the (parametric) scrutinee's own type — must
/// typecheck. This is the shape that motivated both fixes; loading the real `std/map.bl` module
/// is covered separately by `stdlib.rs`'s `std_map_loads_in_isolation`.
#[test]
fn match_on_polymorphic_function_call_with_constructor_field_binder_typechecks() {
    run_ok(
        r#"
(defdata Maybe1 ((a (Type 0))) (nothing1) (just1 (x a)))
(defdata Bool1 () (false1) (true1))
(define id-maybe (Pi ((V (Type 0)) (mv (Maybe1 V))) (Maybe1 V)) (lam (V mv) mv))
(define foo
  (Pi ((V (Type 0)) (mv (Maybe1 V))) Bool1)
  (lam (V mv) (match (id-maybe V mv)
    [(nothing1) false1]
    [(just1 v)  true1])))
"#,
    );
}

/// Bug 3 (Wave 2 / P4, found implementing `spore_reader.bl`'s `BSexp -> BSurf` transcoder): a
/// recursive function's **own self-call** used to be untypeable under `synth_type` — the
/// structural-recursion IH binder `elab_flat_match` introduces for each recursive constructor
/// field was pushed with no type at all (`Scope::push_var`, not `push_var_ty`). `synth_type` on
/// that variable (and thus on any `App`/self-call built from it) therefore always returned `None`.
/// That's invisible for a self-call used directly as a checked value (the common case), but the
/// moment its *result* needs to flow through inference — e.g. immediately `match`ed, or `let`-bound
/// — `Surface::Let`'s "ascribe the continuation lambda when both sides are known" fast path
/// silently degraded to a bare, unascribed `Lam`, and the kernel later rejected the whole
/// definition with "cannot infer a type: lambda/pair need a type ascription to infer".
///
/// Minimal case: `down`'s `(Succ k)` arm immediately matches its own recursive call's `Maybe`
/// result (rather than just returning it), which is exactly what `resolve-ty`/`resolve-term` do
/// throughout `spore_reader.bl`.
#[test]
fn match_on_own_recursive_call_result_typechecks() {
    run_ok(
        r#"
(defdata Nat1 () (Zero1) (Succ1 (n Nat1)))
(defdata Maybe1 ((a (Type 0))) (nothing1) (just1 (x a)))
(define-rec down
  (Pi ((n Nat1)) (Maybe1 Nat1))
  (lam (n) (match n
    [(Zero1) (just1 Zero1)]
    [(Succ1 k) (match (down k)
       [(nothing1) nothing1]
       [(just1 j)  (just1 j)])])))
"#,
    );
}

/// Bug 4, the fix's own pitfall: giving the IH binder a real type must not make it eligible for
/// `elab_flat_match`'s *trailing-binder* generalization (the mechanism that re-quantifies a
/// function parameter bound before the current match's scrutinee, e.g. a fold accumulator curried
/// in one `match` arm at a time — see `map-from-list-acc`). That mechanism gates on "is every
/// candidate binder typed", and an IH binder was always untyped before, so it was always excluded;
/// naively fixing bug 3 flips that gate to "included" and wraps unrelated *inner* matches in a
/// spurious Pi-telescope over the (function-typed) induction hypothesis. Minimal case: a `List`
/// fold with a curried accumulator, where the recursive step also has a *nested* match (on the
/// pair head) below the outer recursive-field/IH binders in scope.
#[test]
fn nested_match_below_ih_binder_does_not_spuriously_generalize() {
    run_ok(
        r#"
(defdata Nat1 () (Zero1) (Succ1 (n Nat1)))
(defdata Pair1 ((a (Type 0)) (b (Type 0))) (mk-pair1 (x a) (y b)))
(defdata List1 ((a (Type 0))) (nil1) (cons1 (x a) (xs (List1 a))))
(define-rec fold-fst
  (Pi ((xs (List1 (Pair1 Nat1 Nat1))) (acc Nat1)) Nat1)
  (lam (xs) (match xs
    [(nil1) (lam (acc) acc)]
    [(cons1 p rest) (lam (acc) (match p
       [(mk-pair1 k v) (fold-fst rest k)]))])))
"#,
    );
}
