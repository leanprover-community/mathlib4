/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis

! This file was ported from Lean 3 source module ring_theory.witt_vector.is_poly
! leanprover-community/mathlib commit 168ad7fc5d8173ad38be9767a22d50b8ecf1cd00
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Ring.ULift
import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Data.MvPolynomial.Funext
import Mathlib.RingTheory.WittVector.WittAttributes
/-!
# The `is_poly` predicate

`WittVector.IsPoly` is a (type-valued) predicate on functions `f : Π R, 𝕎 R → 𝕎 R`.
It asserts that there is a family of polynomials `φ : ℕ → MvPolynomial ℕ ℤ`,
such that the `n`th coefficient of `f x` is equal to `φ n` evaluated on the coefficients of `x`.
Many operations on Witt vectors satisfy this predicate (or an analogue for higher arity functions).
We say that such a function `f` is a *polynomial function*.

The power of satisfying this predicate comes from `WittVector.IsPoly.ext`.
It shows that if `φ` and `ψ` witness that `f` and `g` are polynomial functions,
then `f = g` not merely when `φ = ψ`, but in fact it suffices to prove
```
∀ n, bind₁ φ (wittPolynomial p _ n) = bind₁ ψ (wittPolynomial p _ n)
```
(in other words, when evaluating the Witt polynomials on `φ` and `ψ`, we get the same values)
which will then imply `φ = ψ` and hence `f = g`.

Even though this sufficient condition looks somewhat intimidating,
it is rather pleasant to check in practice;
more so than direct checking of `φ = ψ`.

In practice, we apply this technique to show that the composition of `WittVector.frobenius`
and `WittVector.verschiebung` is equal to multiplication by `p`.

## Main declarations

* `WittVector.IsPoly`, `WittVector.IsPoly₂`:
  two predicates that assert that a unary/binary function on Witt vectors
  is polynomial in the coefficients of the input values.
* `WittVector.IsPoly.ext`, `WittVector.IsPoly₂.ext`:
  two polynomial functions are equal if their families of polynomials are equal
  after evaluating the Witt polynomials on them.
* `WittVector.IsPoly.comp` (+ many variants) show that unary/binary compositions
  of polynomial functions are polynomial.
* `WittVector.idIsPoly`, `WittVector.negIsPoly`,
  `WittVector.addIsPoly₂`, `WittVector.mulIsPoly₂`:
  several well-known operations are polynomial functions
  (for Verschiebung, Frobenius, and multiplication by `p`, see their respective files).

## On higher arity analogues

Ideally, there should be a predicate `IsPolyₙ` for functions of higher arity,
together with `IsPolyₙ.comp` that shows how such functions compose.
Since mathlib does not have a library on composition of higher arity functions,
we have only implemented the unary and binary variants so far.
Nullary functions (a.k.a. constants) are treated
as constant functions and fall under the unary case.

## Tactics

There are important metaprograms defined in this file:
the tactics `ghost_simp` and `ghost_calc` and the attributes `@[is_poly]` and `@[ghost_simps]`.
These are used in combination to discharge proofs of identities between polynomial functions.

Any atomic proof of `IsPoly` or `IsPoly₂` (i.e. not taking additional `IsPoly` arguments)
should be tagged as `@[is_poly]`.

Any lemma doing "ring equation rewriting" with polynomial functions should be tagged
`@[ghost_simps]`, e.g.
```lean
@[ghost_simps]
lemma bind₁_frobenius_poly_wittPolynomial (n : ℕ) :
  bind₁ (frobenius_poly p) (wittPolynomial p ℤ n) = (wittPolynomial p ℤ (n+1))
```

Proofs of identities between polynomial functions will often follow the pattern
```lean
begin
  ghost_calc _,
  <minor preprocessing>,
  ghost_simp
end
```

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


/- failed to parenthesize: unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
[PrettyPrinter.parenthesize.input] (Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr
     [(Command.docComment "/--" "Simplification rules for ghost equations -/")]
     "register_simp_attr"
     `ghost_simps)-/-- unknown constant 'Lean.Meta._root_.Lean.Parser.Command.registerSimpAttr'
--/-- Simplification rules for ghost equations -/ register_simp_attr ghost_simps

/-  --  porting note: todo later
namespace Tactic

namespace Interactive

/-- A macro for a common simplification when rewriting with ghost component equations. -/
unsafe def ghost_simp (lems : parse simp_arg_list) : tactic Unit := do
  tactic.try tactic.intro1
  simp none none tt (lems ++ [simp_arg_type.symm_expr ``(sub_eq_add_neg)]) [`ghost_simps]
      (loc.ns [none])
#align tactic.interactive.ghost_simp tactic.interactive.ghost_simp

/-- `ghost_calc` is a tactic for proving identities between polynomial functions.
Typically, when faced with a goal like
```lean
∀ (x y : 𝕎 R), verschiebung (x * frobenius y) = verschiebung x * y
```
you can
1. call `ghost_calc`
2. do a small amount of manual work -- maybe nothing, maybe `rintro`, etc
3. call `ghost_simp`

and this will close the goal.

`ghost_calc` cannot detect whether you are dealing with unary or binary polynomial functions.
You must give it arguments to determine this.
If you are proving a universally quantified goal like the above,
call `ghost_calc _ _`.
If the variables are introduced already, call `ghost_calc x y`.
In the unary case, use `ghost_calc _` or `ghost_calc x`.

`ghost_calc` is a light wrapper around type class inference.
All it does is apply the appropriate extensionality lemma and try to infer the resulting goals.
This is subtle and Lean's elaborator doesn't like it because of the HO unification involved,
so it is easier (and prettier) to put it in a tactic script.
-/
unsafe def ghost_calc (ids' : parse ident_*) : tactic Unit := do
  let ids ← ids'.mapM fun n => get_local n <|> tactic.intro n
  let q(@Eq (WittVector _ $(R)) _ _) ← target
  match ids with
    | [x] => refine `(is_poly.ext _ _ _ _ $(x))
    | [x, y] => refine `(is_poly₂.ext _ _ _ _ $(x) $(y))
    | _ => fail "ghost_calc takes one or two arguments"
  let nm ←
    match R with
      | expr.local_const _ nm _ _ => return nm
      | _ => get_unused_name `R
  iterate_exactly 2 apply_instance
  unfreezingI (tactic.clear' tt [R])
  introsI <| [nm, .str nm "_inst"] ++ ids'
  skip
#align tactic.interactive.ghost_calc tactic.interactive.ghost_calc

end Interactive

end Tactic
-/

namespace WittVector

universe u

variable {p : ℕ} {R S : Type u} {σ idx : Type _} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p

-- type as `\bbW`
open MvPolynomial

open Function (uncurry)

variable (p)

noncomputable section

/-!
### The `IsPoly` predicate
-/


theorem poly_eq_of_wittPolynomial_bind_eq' [Fact p.Prime] (f g : ℕ → MvPolynomial (idx × ℕ) ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← Function.funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h
#align witt_vector.poly_eq_of_witt_polynomial_bind_eq' WittVector.poly_eq_of_wittPolynomial_bind_eq'

theorem poly_eq_of_wittPolynomial_bind_eq [Fact p.Prime] (f g : ℕ → MvPolynomial ℕ ℤ)
    (h : ∀ n, bind₁ f (wittPolynomial p _ n) = bind₁ g (wittPolynomial p _ n)) : f = g := by
  ext1 n
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← Function.funext_iff] at h
  replace h :=
    congr_arg (fun fam => bind₁ (MvPolynomial.map (Int.castRingHom ℚ) ∘ fam) (xInTermsOfW p ℚ n)) h
  simpa only [Function.comp, map_bind₁, map_wittPolynomial, ← bind₁_bind₁,
    bind₁_wittPolynomial_xInTermsOfW, bind₁_X_right] using h
#align witt_vector.poly_eq_of_witt_polynomial_bind_eq WittVector.poly_eq_of_wittPolynomial_bind_eq

-- Ideally, we would generalise this to n-ary functions
-- But we don't have a good theory of n-ary compositions in mathlib
/--
A function `f : Π R, 𝕎 R → 𝕎 R` that maps Witt vectors to Witt vectors over arbitrary base rings
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x` is given by evaluating `φₙ` at the coefficients of `x`.

See also `WittVector.IsPoly₂` for the binary variant.

The `ghost_calc` tactic treats `IsPoly` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `IsPoly f`.
For the most part, users are not expected to treat `IsPoly` as a class.
-/
class IsPoly (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial ℕ ℤ,
      ∀ ⦃R⦄ [CommRing R] (x : 𝕎 R), (f x).coeff = fun n => aeval x.coeff (φ n)
#align witt_vector.is_poly WittVector.IsPoly

/-- The identity function on Witt vectors is a polynomial function. -/
instance idIsPoly : IsPoly p fun _ _ => id :=
  ⟨⟨X, by intros; simp only [aeval_X, id]⟩⟩
#align witt_vector.id_is_poly WittVector.idIsPoly

instance idIsPolyI' : IsPoly p fun _ _ a => a :=
  WittVector.idIsPoly _
#align witt_vector.id_is_poly_i' WittVector.idIsPolyI'

namespace IsPoly

instance : Inhabited (IsPoly p fun _ _ => id) :=
  ⟨WittVector.idIsPoly p⟩

variable {p}

theorem ext [Fact p.Prime] {f g} (hf : IsPoly p f) (hg : IsPoly p g)
    (h :
      ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R) (n : ℕ),
        ghostComponent n (f x) = ghostComponent n (g x)) :
    ∀ (R : Type u) [_Rcr : CommRing R] (x : 𝕎 R), f x = g x := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq p φ ψ]
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift ℤ) (mk p fun i => ⟨x i⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  convert h using 1
  all_goals
    --  porting note: this proof started with `funext i`
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    simp only [coeff_mk]; rfl
#align witt_vector.is_poly.ext WittVector.IsPoly.ext

/-- The composition of polynomial functions is polynomial. -/
theorem comp {g f} (hg : IsPoly p g) (hf : IsPoly p f) :
    IsPoly p fun R _Rcr => @g R _Rcr ∘ @f R _Rcr := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [aeval_bind₁, Function.comp, hg, hf]
#align witt_vector.is_poly.comp WittVector.IsPoly.comp

end IsPoly

/-- A binary function `f : Π R, 𝕎 R → 𝕎 R → 𝕎 R` on Witt vectors
is said to be *polynomial* if there is a family of polynomials `φₙ` over `ℤ` such that the `n`th
coefficient of `f x y` is given by evaluating `φₙ` at the coefficients of `x` and `y`.

See also `WittVector.IsPoly` for the unary variant.

The `ghost_calc` tactic treats `IsPoly₂` as a type class,
and the `@[is_poly]` attribute derives certain specialized composition instances
for declarations of type `IsPoly₂ f`.
For the most part, users are not expected to treat `IsPoly₂` as a class.
-/
class IsPoly₂ (f : ∀ ⦃R⦄ [CommRing R], WittVector p R → 𝕎 R → 𝕎 R) : Prop where mk' ::
  poly :
    ∃ φ : ℕ → MvPolynomial (Fin 2 × ℕ) ℤ,
      ∀ ⦃R⦄ [CommRing R] (x y : 𝕎 R), (f x y).coeff = fun n => peval (φ n) ![x.coeff, y.coeff]
#align witt_vector.is_poly₂ WittVector.IsPoly₂

variable {p}

/-- The composition of polynomial functions is polynomial. -/
theorem IsPoly₂.comp {h f g} (hh : IsPoly₂ p h) (hf : IsPoly p f) (hg : IsPoly p g) :
    IsPoly₂ p fun R _Rcr x y => h (f x) (g y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  obtain ⟨χ, hh⟩ := hh
  refine'
    ⟨⟨fun n =>
        bind₁
          (uncurry <|
            ![fun k => rename (Prod.mk (0 : Fin 2)) (φ k), fun k =>
              rename (Prod.mk (1 : Fin 2)) (ψ k)])
          (χ n),
        _⟩⟩
  intros
  funext n
  simp only [peval, aeval_bind₁, Function.comp, hh, hf, hg, uncurry]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, n⟩
  fin_cases i <;>
    simp only [aeval_eq_eval₂Hom, eval₂Hom_rename, Function.comp, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
    -- porting note: added the rest of the proof.
    <;>
    open Matrix in
    simp only [algebraMap_int_eq, coe_eval₂Hom, Fin.mk_zero, Fin.mk_one, cons_val', empty_val',
      cons_val_fin_one, cons_val_zero, cons_val_one, eval₂Hom_rename, Function.comp, head_fin_const]

#align witt_vector.is_poly₂.comp WittVector.IsPoly₂.comp

/-- The composition of a polynomial function with a binary polynomial function is polynomial. -/
theorem IsPoly.comp₂ {g f} (hg : IsPoly p g) (hf : IsPoly₂ p f) :
    IsPoly₂ p fun R _Rcr x y => g (f x y) := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  use fun n => bind₁ φ (ψ n)
  intros
  simp only [peval, aeval_bind₁, Function.comp, hg, hf]
#align witt_vector.is_poly.comp₂ WittVector.IsPoly.comp₂

/-- The diagonal `fun x ↦ f x x` of a polynomial function `f` is polynomial. -/
theorem IsPoly₂.diag {f} (hf : IsPoly₂ p f) : IsPoly p fun R _Rcr x => f x x := by
  obtain ⟨φ, hf⟩ := hf
  refine' ⟨⟨fun n => bind₁ (uncurry ![X, X]) (φ n), _⟩⟩
  intros; funext n
  simp only [hf, peval, uncurry, aeval_bind₁]
  apply eval₂Hom_congr rfl _ rfl
  ext ⟨i, k⟩;
  fin_cases i <;> simp only [Matrix.head_cons, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    --  porting note: the end of the proof was added in the port.
    <;>
    open Matrix in
    simp only [Fin.mk_zero, Fin.mk_one, cons_val', empty_val', cons_val_fin_one, cons_val_zero,
      aeval_X, head_fin_const, cons_val_one]
#align witt_vector.is_poly₂.diag WittVector.IsPoly₂.diag

/-  porting note: port later
open Tactic

namespace Tactic

/-!
### The `@[is_poly]` attribute

This attribute is used to derive specialized composition instances
for `IsPoly` and `IsPoly₂` declarations.
-/

/-- If `n` is the name of a lemma with opened type `∀ vars, IsPoly p _`,
`mk_poly_comp_lemmas n vars p` adds composition instances to the environment
`n.comp_i` and `n.comp₂_i`.
-/
unsafe def mk_poly_comp_lemmas (n : Name) (vars : List expr) (p : expr) : tactic Unit := do
  let c ← mk_const n
  let appd := vars.foldl expr.app c
  let tgt_bod ←
    to_expr ``(fun f [hf : IsPoly $(p) f] => IsPoly.comp $(appd) hf) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod
  let nm := .str n "comp_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
  let tgt_bod ←
    to_expr ``(fun f [hf : IsPoly₂ $(p) f] => IsPoly.comp₂ $(appd) hf) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod
  let nm := .str n "comp₂_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
#align witt_vector.tactic.mk_poly_comp_lemmas witt_vector.tactic.mk_poly_comp_lemmas

/-- If `n` is the name of a lemma with opened type `∀ vars, IsPoly₂ p _`,
`mk_poly₂_comp_lemmas n vars p` adds composition instances to the environment
`n.comp₂_i` and `n.comp_diag`.
-/
unsafe def mk_poly₂_comp_lemmas (n : Name) (vars : List expr) (p : expr) : tactic Unit := do
  let c ← mk_const n
  let appd := vars.foldl expr.app c
  let tgt_bod ←
    to_expr
          ``(fun {f g} [hf : IsPoly $(p) f] [hg : IsPoly $(p) g] => IsPoly₂.comp $(appd) hf hg) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify
  let nm := .str n "comp₂_i"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
  let tgt_bod ←
    to_expr
          ``(fun {f g} [hf : IsPoly $(p) f] [hg : IsPoly $(p) g] =>
            (IsPoly₂.comp $(appd) hf hg).diag) >>=
        replace_univ_metas_with_univ_params
  let tgt_bod ← lambdas vars tgt_bod
  let tgt_tp ← infer_type tgt_bod >>= simp_lemmas.mk.dsimplify
  let nm := .str n "comp_diag"
  add_decl <| mk_definition nm tgt_tp tgt_tp tgt_bod
  set_attribute `instance nm
#align witt_vector.tactic.mk_poly₂_comp_lemmas witt_vector.tactic.mk_poly₂_comp_lemmas

/-- The `after_set` function for `@[is_poly]`. Calls `mk_poly(₂)_comp_lemmas`.
-/
unsafe def mk_comp_lemmas (n : Name) : tactic Unit := do
  let d ← get_decl n
  let (vars, tp) ← open_pis d.type
  match tp with
    | q(IsPoly $(p) _) => mk_poly_comp_lemmas n vars p
    | q(IsPoly₂ $(p) _) => mk_poly₂_comp_lemmas n vars p
    | _ => fail "@[is_poly] should only be applied to terms of type `IsPoly _ _` or `IsPoly₂ _ _`"
#align witt_vector.tactic.mk_comp_lemmas witt_vector.tactic.mk_comp_lemmas

/-- `@[is_poly]` is applied to lemmas of the form `IsPoly f φ` or `IsPoly₂ f φ`.
These lemmas should *not* be tagged as instances, and only atomic `IsPoly` defs should be tagged:
composition lemmas should not. Roughly speaking, lemmas that take `IsPoly` proofs as arguments
should not be tagged.

Type class inference struggles with function composition, and the higher order unification problems
involved in inferring `IsPoly` proofs are complex. The standard style writing these proofs by hand
doesn't work very well. Instead, we construct the type class hierarchy "under the hood", with
limited forms of composition.

Applying `@[is_poly]` to a lemma creates a number of instances. Roughly, if the tagged lemma is a
proof of `IsPoly f φ`, the instances added have the form
```lean
∀ g ψ, [IsPoly g ψ] → IsPoly (f ∘ g) _
```
Since `f` is fixed in this instance, it restricts the HO unification needed when the instance is
applied. Composition lemmas relating `IsPoly` with `IsPoly₂` are also added.
`idIsPoly` is an atomic instance.

The user-written lemmas are not instances. Users should be able to assemble `is_poly` proofs by hand
"as normal" if the tactic fails.
-/
@[user_attribute]
unsafe def isPolyAttr : user_attribute where
  Name := `IsPoly
  descr := "Lemmas with this attribute describe the polynomial structure of functions"
  after_set := some fun n _ _ => mk_comp_lemmas n
#align witt_vector.tactic.is_poly_attr WittVector.Tactic.isPolyAttr

end Tactic
-/

/-!
### `IsPoly` instances

These are not declared as instances at the top level,
but the `@[is_poly]` attribute adds instances based on each one.
Users are expected to use the non-instance versions manually.
-/


/-- The additive negation is a polynomial function on Witt vectors. -/
@[is_poly]
theorem negIsPoly [Fact p.Prime] : IsPoly p fun R _ => @Neg.neg (𝕎 R) _ :=
  ⟨⟨fun n => rename Prod.snd (wittNeg p n), by
      intros; funext n
      rw [neg_coeff, aeval_eq_eval₂Hom, eval₂Hom_rename]
      apply eval₂Hom_congr rfl _ rfl
      ext ⟨i, k⟩; fin_cases i; rfl⟩⟩
#align witt_vector.neg_is_poly WittVector.negIsPoly

section ZeroOne

/- To avoid a theory of 0-ary functions (a.k.a. constants)
we model them as constant unary functions. -/
/-- The function that is constantly zero on Witt vectors is a polynomial function. -/
instance zeroIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 0 :=
  ⟨⟨0, by intros; funext n; simp only [Pi.zero_apply, AlgHom.map_zero, zero_coeff]⟩⟩
#align witt_vector.zero_is_poly WittVector.zeroIsPoly

@[simp]
theorem bind₁_zero_wittPolynomial [Fact p.Prime] (n : ℕ) :
    bind₁ (0 : ℕ → MvPolynomial ℕ R) (wittPolynomial p R n) = 0 := by
  rw [← aeval_eq_bind₁, aeval_zero, constantCoeff_wittPolynomial, RingHom.map_zero]
#align witt_vector.bind₁_zero_witt_polynomial WittVector.bind₁_zero_wittPolynomial

/-- The coefficients of `1 : 𝕎 R` as polynomials. -/
def onePoly (n : ℕ) : MvPolynomial ℕ ℤ :=
  if n = 0 then 1 else 0
#align witt_vector.one_poly WittVector.onePoly

@[simp]
theorem bind₁_onePoly_wittPolynomial [hp : Fact p.Prime] (n : ℕ) :
    bind₁ onePoly (wittPolynomial p ℤ n) = 1 := by
  ext  -- porting note: `ext` was not in the mathport output.
  rw [wittPolynomial_eq_sum_c_mul_x_pow, AlgHom.map_sum, Finset.sum_eq_single 0]
  · simp only [onePoly, one_pow, one_mul, AlgHom.map_pow, C_1, pow_zero, bind₁_X_right, if_true,
      eq_self_iff_true]
  · intro i _hi hi0
    simp only [onePoly, if_neg hi0, zero_pow (pow_pos hp.1.pos _), MulZeroClass.mul_zero,
      AlgHom.map_pow, bind₁_X_right, AlgHom.map_mul]
  · rw [Finset.mem_range]
    -- porting note: was `decide`
    simp only [add_pos_iff, or_true, not_true, pow_zero, map_one, ge_iff_le, nonpos_iff_eq_zero,
      tsub_zero, one_mul, gt_iff_lt, IsEmpty.forall_iff]
#align witt_vector.bind₁_one_poly_witt_polynomial WittVector.bind₁_onePoly_wittPolynomial

/-- The function that is constantly one on Witt vectors is a polynomial function. -/
instance oneIsPoly [Fact p.Prime] : IsPoly p fun _ _ _ => 1 :=
  ⟨⟨onePoly, by
      intros; funext n; cases n
      · -- porting note: was `simp only [...]` but with slightly different `[...]`.
        simp only [Nat.zero_eq, lt_self_iff_false, one_coeff_zero, onePoly, ite_true, map_one]
      · -- porting note: was `simp only [...]` but with slightly different `[...]`.
        simp only [Nat.succ_pos', one_coeff_eq_of_pos, onePoly, Nat.succ_ne_zero, ite_false,
          map_zero]
  ⟩⟩
#align witt_vector.one_is_poly WittVector.oneIsPoly

end ZeroOne

/-- Addition of Witt vectors is a polynomial function. -/
@[is_poly]
theorem addIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· + ·) :=
  --  porting note: the proof was
  --  `⟨⟨wittAdd p, by intros; dsimp only [WittVector.hasAdd]; simp [eval]⟩⟩`
  ⟨⟨wittAdd p, by intros; ext; exact add_coeff _ _ _⟩⟩
#align witt_vector.add_is_poly₂ WittVector.addIsPoly₂

/-- Multiplication of Witt vectors is a polynomial function. -/
@[is_poly]
theorem mulIsPoly₂ [Fact p.Prime] : IsPoly₂ p fun _ _ => (· * ·) :=
  --  porting note: the proof was
  -- `⟨⟨wittMul p, by intros; dsimp only [WittVector.hasMul]; simp [eval]⟩⟩`
  ⟨⟨wittMul p, by intros; ext; exact mul_coeff _ _ _⟩⟩
#align witt_vector.mul_is_poly₂ WittVector.mulIsPoly₂

-- unfortunately this is not universe polymorphic, merely because `f` isn't
theorem IsPoly.map [Fact p.Prime] {f} (hf : IsPoly p f) (g : R →+* S) (x : 𝕎 R) :
    map g (f x) = f (map g x) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  -- see `IsPoly₂.map` for a slightly more general proof strategy
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp only [map_coeff, hf, map_aeval]
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  ext  -- porting note: this `ext` was not present in the mathport output
  simp only [map_coeff]
#align witt_vector.is_poly.map WittVector.IsPoly.map

namespace IsPoly₂

--  porting note: the argument `(fun _ _ => (· + ·))` to `IsPoly₂` was just `_`.
instance [Fact p.Prime] : Inhabited (IsPoly₂ p (fun _ _ => (· + ·))) :=
  ⟨addIsPoly₂⟩

/-- The composition of a binary polynomial function
 with a unary polynomial function in the first argument is polynomial. -/
theorem compLeft {g f} (hg : IsPoly₂ p g) (hf : IsPoly p f) :
    IsPoly₂ p fun _R _Rcr x y => g (f x) y :=
  hg.comp hf (WittVector.idIsPoly _)
#align witt_vector.is_poly₂.comp_left WittVector.IsPoly₂.compLeft

/-- The composition of a binary polynomial function
 with a unary polynomial function in the second argument is polynomial. -/
theorem compRight {g f} (hg : IsPoly₂ p g) (hf : IsPoly p f) :
    IsPoly₂ p fun _R _Rcr x y => g x (f y) :=
  hg.comp (WittVector.idIsPoly p) hf
#align witt_vector.is_poly₂.comp_right WittVector.IsPoly₂.compRight

theorem ext [Fact p.Prime] {f g} (hf : IsPoly₂ p f) (hg : IsPoly₂ p g)
    (h :
      ∀ (R : Type u) [_Rcr : CommRing R] (x y : 𝕎 R) (n : ℕ),
        ghostComponent n (f x y) = ghostComponent n (g x y)) :
    ∀ (R) [_Rcr : CommRing R] (x y : 𝕎 R), f x y = g x y := by
  obtain ⟨φ, hf⟩ := hf
  obtain ⟨ψ, hg⟩ := hg
  intros
  ext n
  rw [hf, hg, poly_eq_of_wittPolynomial_bind_eq' p φ ψ]
  --  porting note: `clear x y` does not work, since `x, y` are now hygienic
  intro k
  apply MvPolynomial.funext
  intro x
  simp only [hom_bind₁]
  specialize h (ULift ℤ) (mk p fun i => ⟨x (0, i)⟩) (mk p fun i => ⟨x (1, i)⟩) k
  simp only [ghostComponent_apply, aeval_eq_eval₂Hom] at h
  apply (ULift.ringEquiv.symm : ℤ ≃+* _).injective
  simp only [← RingEquiv.coe_toRingHom, map_eval₂Hom]
  convert h using 1
  all_goals
    --  porting note: this proof started with `funext i`
    simp only [hf, hg, MvPolynomial.eval, map_eval₂Hom]
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext1
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
    ext ⟨b, _⟩
    fin_cases b <;> simp only [coeff_mk, uncurry] <;> rfl
#align witt_vector.is_poly₂.ext WittVector.IsPoly₂.ext

-- unfortunately this is not universe polymorphic, merely because `f` isn't
theorem map [Fact p.Prime] {f} (hf : IsPoly₂ p f) (g : R →+* S) (x y : 𝕎 R) :
    map g (f x y) = f (map g x) (map g y) := by
  -- this could be turned into a tactic “macro” (taking `hf` as parameter)
  -- so that applications do not have to worry about the universe issue
  obtain ⟨φ, hf⟩ := hf
  ext n
  simp only [map_coeff, hf, map_aeval, peval, uncurry]
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  try ext ⟨i, k⟩; fin_cases i
  all_goals simp only [map_coeff, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  -- porting note: added the rest of the proof
  all_goals
    simp only [Fin.mk_zero, Fin.mk_one, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, map_coeff, Matrix.head_fin_const]
#align witt_vector.is_poly₂.map WittVector.IsPoly₂.map

end IsPoly₂

attribute [ghost_simps] AlgHom.map_zero AlgHom.map_one AlgHom.map_add AlgHom.map_mul AlgHom.map_sub
  AlgHom.map_neg AlgHom.id_apply map_natCast RingHom.map_zero RingHom.map_one RingHom.map_mul
  RingHom.map_add RingHom.map_sub RingHom.map_neg RingHom.id_apply mul_add add_mul add_zero zero_add
  mul_one one_mul MulZeroClass.mul_zero MulZeroClass.zero_mul Nat.succ_ne_zero add_tsub_cancel_right
  Nat.succ_eq_add_one if_true eq_self_iff_true if_false forall_true_iff forall₂_true_iff
  forall₃_true_iff

end  -- porting note: ends the `noncomputable section`?

end WittVector
