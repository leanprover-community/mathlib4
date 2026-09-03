/-
Copyright (c) 2020 Johan Commelin, Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.MvPolynomial.Variables

/-!

# Monad operations on `MvPolynomial`

This file defines two monadic operations on `MvPolynomial`. Given `p : MvPolynomial σ R`,

* `MvPolynomial.bind₁` and `MvPolynomial.join₁` operate on the variable type `σ`.
* `MvPolynomial.bind₂` and `MvPolynomial.join₂` operate on the coefficient type `R`.

- `MvPolynomial.bind₁ f φ` with `f : σ → MvPolynomial τ R` and `φ : MvPolynomial σ R`,
  is the polynomial `φ(f 1, ..., f i, ...) : MvPolynomial τ R`.
- `MvPolynomial.join₁ φ` with `φ : MvPolynomial (MvPolynomial σ R) R` collapses `φ` to
  a `MvPolynomial σ R`, by evaluating `φ` under the map `X f ↦ f` for `f : MvPolynomial σ R`.
  In other words, if you have a polynomial `φ` in a set of variables indexed by a polynomial ring,
  you evaluate the polynomial in these indexing polynomials.
- `MvPolynomial.bind₂ f φ` with `f : R →+* MvPolynomial σ S` and `φ : MvPolynomial σ R`
  is the `MvPolynomial σ S` obtained from `φ` by mapping the coefficients of `φ` through `f`
  and considering the resulting polynomial as polynomial expression in `MvPolynomial σ R`.
- `MvPolynomial.join₂ φ` with `φ : MvPolynomial σ (MvPolynomial σ R)` collapses `φ` to
  a `MvPolynomial σ R`, by considering `φ` as polynomial expression in `MvPolynomial σ R`.

These operations themselves have algebraic structure: `MvPolynomial.bind₁`
and `MvPolynomial.join₁` are algebra homs and
`MvPolynomial.bind₂` and `MvPolynomial.join₂` are ring homs.

They interact in convenient ways with `MvPolynomial.rename`, `MvPolynomial.map`,
`MvPolynomial.vars`, and other polynomial operations.
Indeed, `MvPolynomial.rename` is the "map" operation for the (`bind₁`, `join₁`) pair,
whereas `MvPolynomial.map` is the "map" operation for the other pair.

## Implementation notes

We add a `LawfulMonad` instance for the (`bind₁`, `join₁`) pair.
The second pair cannot be instantiated as a `Monad`,
since it is not a monad in `Type` but in `CommRingCat` (or rather `CommSemiRingCat`).

-/

@[expose] public section


noncomputable section

namespace MvPolynomial

open Finsupp

variable {σ : Type*} {τ : Type*}
variable {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/--
`bind₁` is the "left-hand side" bind operation on `MvPolynomial`, operating on the variable type.
Given a polynomial `p : MvPolynomial σ R` and a map `f : σ → MvPolynomial τ R` taking variables
in `p` to polynomials in the variable type `τ`, `bind₁ f p` replaces each variable in `p` with
its value under `f`, producing a new polynomial in `τ`. The coefficient type remains the same.
This operation is an algebra hom.
-/
@[deprecated aeval (since := "2026-09-02")]
def bind₁ (f : σ → MvPolynomial τ R) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval f

/-- `bind₂` is the "right-hand side" bind operation on `MvPolynomial`,
operating on the coefficient type.
Given a polynomial `p : MvPolynomial σ R` and
a map `f : R → MvPolynomial σ S` taking coefficients in `p` to polynomials over a new ring `S`,
`bind₂ f p` replaces each coefficient in `p` with its value under `f`,
producing a new polynomial over `S`.
The variable type remains the same. This operation is a ring hom.
-/
@[deprecated "use `eval₂Hom f X` instead" (since := "2026-09-02")]
def bind₂ (f : R →+* MvPolynomial σ S) : MvPolynomial σ R →+* MvPolynomial σ S :=
  eval₂Hom f X

/--
`join₁` is the monadic join operation corresponding to `MvPolynomial.bind₁`. Given a polynomial `p`
with coefficients in `R` whose variables are polynomials in `σ` with coefficients in `R`,
`join₁ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is an algebra hom.
-/
@[deprecated "use `aeval id` instead" (since := "2026-09-02")]
def join₁ : MvPolynomial (MvPolynomial σ R) R →ₐ[R] MvPolynomial σ R :=
  aeval id

/--
`join₂` is the monadic join operation corresponding to `MvPolynomial.bind₂`. Given a polynomial `p`
with variables in `σ` whose coefficients are polynomials in `σ` with coefficients in `R`,
`join₂ p` collapses `p` to a polynomial with variables in `σ` and coefficients in `R`.
This operation is a ring hom.
-/
@[deprecated "use `eval X` instead" (since := "2026-09-02")]
def join₂ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
  eval₂Hom (RingHom.id _) X

@[deprecated "this is now a syntactic equality" (since := "2026-09-02")]
theorem aeval_eq_bind₁ (f : σ → MvPolynomial τ R) : aeval f = bind₁ f :=
  rfl

@[deprecated aeval_eq_eval₂Hom (since := "2026-09-02")]
theorem eval₂Hom_C_eq_bind₁ (f : σ → MvPolynomial τ R) : eval₂Hom C f = bind₁ f :=
  rfl

@[deprecated "this is now a syntactic equality" (since := "2026-09-02")]
theorem eval₂Hom_eq_bind₂ (f : R →+* MvPolynomial σ S) : eval₂Hom f X = bind₂ f :=
  rfl

section

variable (σ R)

@[deprecated "this is now a syntactic equality" (since := "2026-09-02")]
theorem aeval_id_eq_join₁ : aeval id = @join₁ σ R _ :=
  rfl

@[deprecated aeval_eq_eval₂Hom (since := "2026-09-02")]
theorem eval₂Hom_C_id_eq_join₁ (φ : MvPolynomial (MvPolynomial σ R) R) :
    eval₂Hom C id φ = join₁ φ :=
  rfl

@[deprecated eval₂_id (since := "2026-09-02")]
theorem eval₂Hom_id_X_eq_join₂ : eval₂Hom (RingHom.id _) X = @join₂ σ R _ :=
  rfl

end

@[deprecated aeval_X (since := "2026-09-02")]
theorem bind₁_X_right (f : σ → MvPolynomial τ R) (i : σ) : bind₁ f (X i) = f i :=
  aeval_X f i

@[deprecated eval₂Hom_X' (since := "2026-09-02")]
theorem bind₂_X_right (f : R →+* MvPolynomial σ S) (i : σ) : bind₂ f (X i) = X i :=
  eval₂Hom_X' f X i

@[deprecated aeval_X_left (since := "2026-09-02")]
theorem bind₁_X_left : bind₁ (X : σ → MvPolynomial σ R) = AlgHom.id R _ := aeval_X_left

variable (f : σ → MvPolynomial τ R)

@[deprecated aeval_C (since := "2026-09-02")]
theorem bind₁_C_right (f : σ → MvPolynomial τ R) (x) : bind₁ f (C x) = C x := algHom_C _ _

@[deprecated eval₂Hom_C (since := "2026-09-02")]
theorem bind₂_C_right (f : R →+* MvPolynomial σ S) (r : R) : bind₂ f (C r) = f r :=
  eval₂Hom_C f X r

@[deprecated eval₂_eta (since := "2026-09-02")]
theorem bind₂_C_left : bind₂ (C : R →+* MvPolynomial σ R) = RingHom.id _ := RingHom.ext eval₂_eta

@[simp]
theorem eval₂Hom_comp_C (f : R →+* S) (g : σ → S) : (eval₂Hom f g).comp C = f := by
  ext1 r
  exact eval₂_C f g r

@[deprecated eval₂Hom_comp_C (since := "2026-09-02")]
theorem bind₂_comp_C (f : R →+* MvPolynomial σ S) : (bind₂ f).comp C = f :=
  RingHom.ext <| bind₂_C_right _

@[deprecated eval_map (since := "2026-09-02")]
theorem join₂_map (f : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    join₂ (map f φ) = bind₂ f φ := by simp only [join₂, bind₂, eval₂Hom_map_hom, RingHom.id_comp]

@[deprecated eval_comp_map (since := "2026-09-02")]
theorem join₂_comp_map (f : R →+* MvPolynomial σ S) : join₂.comp (map f) = bind₂ f :=
  RingHom.ext <| join₂_map _

@[simp]
theorem aeval_id_rename (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    aeval id (rename f p) = aeval f p := by rw [aeval_rename, Function.id_comp]

@[deprecated aeval_id_rename (since := "2026-09-02")]
theorem join₁_rename (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    join₁ (rename f φ) = bind₁ f φ :=
  aeval_id_rename _ _

@[deprecated "this is now a syntactic equality" (since := "2026-09-02")]
theorem bind₁_id : bind₁ (@id (MvPolynomial σ R)) = join₁ :=
  rfl

@[deprecated eval₂_id (since := "2026-09-02")]
theorem bind₂_id : bind₂ (RingHom.id (MvPolynomial σ R)) = join₂ :=
  rfl

@[deprecated comp_aeval_apply (since := "2026-09-02")]
theorem bind₁_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R)
    (φ : MvPolynomial σ R) : (bind₁ g) (bind₁ f φ) = bind₁ (fun i => bind₁ g (f i)) φ := by
  simp [bind₁, ← comp_aeval]

@[deprecated comp_aeval (since := "2026-09-02")]
theorem bind₁_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → MvPolynomial υ R) :
    (bind₁ g).comp (bind₁ f) = bind₁ fun i => bind₁ g (f i) := by
  ext1
  apply bind₁_bind₁

@[deprecated comp_eval₂Hom (since := "2026-09-02")]
theorem bind₂_comp_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T) :
    (bind₂ g).comp (bind₂ f) = bind₂ ((bind₂ g).comp f) :=
  comp_eval₂Hom f X (bind₂ g) |>.trans <|
    congrArg (eval₂Hom ((bind₂ g).comp f)) (funext (bind₂_X_right g))

@[deprecated map_eval₂Hom (since := "2026-09-02")]
theorem bind₂_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* MvPolynomial σ T)
    (φ : MvPolynomial σ R) : (bind₂ g) (bind₂ f φ) = bind₂ ((bind₂ g).comp f) φ :=
  RingHom.congr_fun (bind₂_comp_bind₂ f g) φ

theorem rename_comp_aeval {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) :
    (rename g).comp (aeval f) = aeval fun i => rename g <| f i := by
  ext1 i
  simp

@[deprecated rename_comp_aeval (since := "2026-09-02")]
theorem rename_comp_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) :
    (rename g).comp (bind₁ f) = bind₁ fun i => rename g <| f i :=
  rename_comp_aeval f g

theorem rename_aeval {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) (φ : MvPolynomial σ R) :
    rename g (aeval f φ) = aeval (fun i => rename g <| f i) φ := by
  rw [← rename_comp_aeval, AlgHom.comp_apply]

@[deprecated rename_aeval (since := "2026-09-02")]
theorem rename_bind₁ {υ : Type*} (f : σ → MvPolynomial τ R) (g : τ → υ) (φ : MvPolynomial σ R) :
    rename g (bind₁ f φ) = bind₁ (fun i => rename g <| f i) φ :=
  AlgHom.congr_fun (rename_comp_bind₁ f g) φ

@[deprecated map_eval₂Hom (since := "2026-09-02")]
theorem map_bind₂ (f : R →+* MvPolynomial σ S) (g : S →+* T) (φ : MvPolynomial σ R) :
    map g (bind₂ f φ) = bind₂ ((map g).comp f) φ := by
  simp only [bind₂, eval₂_comp_right, coe_eval₂Hom, eval₂_map]
  congr 1 with : 1
  simp only [Function.comp_apply, map_X]

@[deprecated aeval_comp_rename (since := "2026-09-02")]
theorem bind₁_comp_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) :
    (bind₁ f).comp (rename g) = bind₁ (f ∘ g) :=
  aeval_comp_rename g f

@[deprecated aeval_rename (since := "2026-09-02")]
theorem bind₁_rename {υ : Type*} (f : τ → MvPolynomial υ R) (g : σ → τ) (φ : MvPolynomial σ R) :
    bind₁ f (rename g φ) = bind₁ (f ∘ g) φ :=
  AlgHom.congr_fun (bind₁_comp_rename f g) φ

@[deprecated eval₂Hom_map_hom (since := "2026-09-02")]
theorem bind₂_map (f : S →+* MvPolynomial σ T) (g : R →+* S) (φ : MvPolynomial σ R) :
    bind₂ f (map g φ) = bind₂ (f.comp g) φ := by simp [bind₂]

@[simp]
theorem map_comp_C (f : R →+* S) : (map f).comp (C : R →+* MvPolynomial σ R) = C.comp f := by
  ext1
  apply map_C

-- mixing the two monad structures
@[deprecated map_aeval (since := "2026-09-02")]
theorem hom_bind₁ (f : MvPolynomial τ R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    f (bind₁ g φ) = eval₂Hom (f.comp C) (fun i => f (g i)) φ := by
  rw [bind₁, map_aeval, algebraMap_eq]

@[deprecated map_aeval_eq_aeval_map (since := "2026-09-02")]
theorem map_bind₁ (f : R →+* S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    map f (bind₁ g φ) = bind₁ (fun i : σ => (map f) (g i)) (map f φ) := by
  rw [hom_bind₁, map_comp_C, ← eval₂Hom_map_hom]
  rfl

@[deprecated map_aeval (since := "2026-09-02")]
theorem eval₂Hom_bind₁ (f : R →+* S) (g : τ → S) (h : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval₂Hom f g (bind₁ h φ) = eval₂Hom f (fun i => eval₂Hom f g (h i)) φ := by
  rw [hom_bind₁, eval₂Hom_comp_C]

@[deprecated comp_aeval_apply (since := "2026-09-02")]
theorem aeval_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    aeval f (bind₁ g φ) = aeval (fun i => aeval f (g i)) φ :=
  eval₂Hom_bind₁ _ _ _ _

@[deprecated comp_aeval (since := "2026-09-02")]
theorem aeval_comp_bind₁ [Algebra R S] (f : τ → S) (g : σ → MvPolynomial τ R) :
    (aeval f).comp (bind₁ g) = aeval fun i => aeval f (g i) := by
  ext1
  apply aeval_bind₁

@[deprecated comp_eval₂Hom (since := "2026-09-02")]
theorem eval₂Hom_comp_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S) :
    (eval₂Hom f g).comp (bind₂ h) = eval₂Hom ((eval₂Hom f g).comp h) g :=
  comp_eval₂Hom h X (eval₂Hom f g) |>.trans <|
    congrArg (eval₂Hom ((eval₂Hom f g).comp h)) (funext (eval₂Hom_X' f g))

@[deprecated map_eval₂Hom (since := "2026-09-02")]
theorem eval₂Hom_bind₂ (f : S →+* T) (g : σ → T) (h : R →+* MvPolynomial σ S)
    (φ : MvPolynomial σ R) : eval₂Hom f g (bind₂ h φ) = eval₂Hom ((eval₂Hom f g).comp h) g φ :=
  RingHom.congr_fun (eval₂Hom_comp_bind₂ f g h) φ

@[deprecated map_eval₂Hom (since := "2026-09-02")]
theorem aeval_bind₂ [Algebra S T] (f : σ → T) (g : R →+* MvPolynomial σ S) (φ : MvPolynomial σ R) :
    aeval f (bind₂ g φ) = eval₂Hom ((↑(aeval f : _ →ₐ[S] _) : _ →+* _).comp g) f φ :=
  eval₂Hom_bind₂ _ _ _ _

@[deprecated "this is now a syntactic equality" (since := "2026-09-02")]
alias eval₂Hom_C_left := eval₂Hom_C_eq_bind₁

@[deprecated aeval_monomial (since := "2026-09-02")]
theorem bind₁_monomial (f : σ → MvPolynomial τ R) (d : σ →₀ ℕ) (r : R) :
    bind₁ f (monomial d r) = C r * ∏ i ∈ d.support, f i ^ d i := by
  simp only [monomial_eq, map_mul, bind₁_C_right, Finsupp.prod, map_prod,
    map_pow, bind₁_X_right]

@[deprecated eval₂Hom_monomial (since := "2026-09-02")]
theorem bind₂_monomial (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) (r : R) :
    bind₂ f (monomial d r) = f r * monomial d 1 := by
  simp only [monomial_eq, map_mul, bind₂_C_right, Finsupp.prod, map_prod,
    map_pow, bind₂_X_right, C_1, one_mul]

@[simp]
theorem eval₂_X_monomial_one (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) :
    eval₂ f X (monomial d 1) = monomial d 1 := by
  rw [eval₂_monomial, map_one, monomial_eq, map_one]

@[deprecated eval₂_X_monomial_one (since := "2026-09-02")]
theorem bind₂_monomial_one (f : R →+* MvPolynomial σ S) (d : σ →₀ ℕ) :
    bind₂ f (monomial d 1) = monomial d 1 := by rw [bind₂_monomial, f.map_one, one_mul]

section

theorem vars_aeval [DecidableEq τ] (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    (aeval f φ).vars ⊆ φ.vars.biUnion fun i => (f i).vars := by
  obtain ⟨p, hp⟩ := exists_rename_coe_vars_eq φ
  choose cf hcf using fun x : φ.vars => exists_rename_coe_vars_eq (f x)
  let df (x : φ.vars) : MvPolynomial (φ.vars.biUnion fun i => (f i).vars) R :=
    (cf x).rename (fun i => ⟨i.1, Finset.subset_biUnion_of_mem _ x.2 i.2⟩)
  have hdf (x : φ.vars) : rename (↑) (df x) = f x := by
    unfold df
    rw [rename_rename, Function.comp_def, hcf]
  conv_lhs => rw [← hp, aeval_rename, Function.comp_def, ← funext hdf, ← rename_aeval]
  rw [← Finset.coe_subset, coe_vars_subset_iff]
  apply AlgHom.mem_range_self

@[deprecated vars_aeval (since := "2026-09-02")]
theorem vars_bind₁ [DecidableEq τ] (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    (bind₁ f φ).vars ⊆ φ.vars.biUnion fun i => (f i).vars :=
  vars_aeval f φ

end

theorem mem_vars_aeval (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
    (h : j ∈ (aeval f φ).vars) : ∃ i : σ, i ∈ φ.vars ∧ j ∈ (f i).vars := by
  classical
  simpa only [exists_prop, Finset.mem_biUnion, mem_support_iff, Ne] using vars_aeval f φ h

@[deprecated mem_vars_aeval (since := "2026-09-02")]
theorem mem_vars_bind₁ (f : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) {j : τ}
    (h : j ∈ (bind₁ f φ).vars) : ∃ i : σ, i ∈ φ.vars ∧ j ∈ (f i).vars :=
  mem_vars_aeval f φ h

instance monad : Monad fun σ => MvPolynomial σ R where
  map f p := rename f p
  pure := X
  bind p f := aeval f p

instance lawfulFunctor : LawfulFunctor fun σ => MvPolynomial σ R where
  map_const := by intros; rfl
  id_map := by intros; simp [(· <$> ·)]
  comp_map := by intros; simp [(· <$> ·)]

instance lawfulMonad : LawfulMonad fun σ => MvPolynomial σ R where
  pure_bind := by intros; simp [pure, bind]
  bind_assoc := by intros; simp [bind, comp_aeval_apply]
  seqLeft_eq _ _ := by
    simp [SeqLeft.seqLeft, Seq.seq, (· <$> ·), aeval_rename]
    simp [rename_eq_aeval, Function.comp_def]
  seqRight_eq := by
    intros
    simp [SeqRight.seqRight, Seq.seq, (· <$> ·),
      aeval_rename, Function.comp_def]
  pure_seq := by intros; simp [(· <$> ·), pure, Seq.seq]
  bind_pure_comp _ _ := congr(⇑$((rename_eq_aeval ..).symm) _)
  bind_map := by aesop

end MvPolynomial
