/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Formal group laws over commutative ring

Let `R` be a commutative ring, a one dimensional formal group law is a formal power series
`F(X,Y) ∈ R⟦X,Y⟧` such that
· `F(X,Y) = X + Y + higher order terms`.
· `F(F(X,Y),Z) = F(X,F(Y,Z))`.

Under this definition, we can prove that `F(X,0) = X` and `F(0,X) = X`. Moreover, there is a
unique power series `i(X)` such that `F(X, i(X)) = 0`, which is considered to be the inverse
of the formal group law `F(X,Y)`.

## Main definitions/lemmas

* Definition of one dimensional formal group law.

* Properties: `F(X,0) = 0` and `F(0,X) = X`.

* Additive formal group laws and multiplicative formal group laws.

* Instance: Group instance defined by the formal group law `F` over the ideal
  `PowerSeries.hasEvalIdeal`.

## References
* [Hazewinkel, Michiel. Formal Groups and Applications][hazewinkel1978]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ τ : Type*}

noncomputable section

open MvPowerSeries Finsupp

/-- The first indeterminate for a power series in two variables. -/
local notation "X₀" => (X (0 : Fin 2) : MvPowerSeries (Fin 2) R)

/-- The second indeterminate for a power series in two variables. -/
local notation "X₁" => (X (1 : Fin 2) : MvPowerSeries (Fin 2) R)

/-- The first indeterminate for a power series in three variables. -/
local notation "Y₀" => (X (0 : Fin 3) : MvPowerSeries (Fin 3) R)

/-- The second indeterminate for a power series in three variables. -/
local notation "Y₁" => (X (1 : Fin 3) : MvPowerSeries (Fin 3) R)

/-- The third indeterminate for a power series in three variables. -/
local notation "Y₂" => (X (2 : Fin 3) : MvPowerSeries (Fin 3) R)

variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`. -/
@[ext]
structure FormalGroup where
  /-- The underlying power series $F(X, Y)$ in two variables. -/
  toFun : MvPowerSeries (Fin 2) R
  /-- The constant coefficient of the formal group law is zero. -/
  zero_constantCoeff : constantCoeff toFun = 0
  /-- The coefficient of $X$ in $F(X, Y)$ is 1. -/
  lin_coeff_X : coeff (single 0 1) toFun = 1
  /-- The coefficient of $Y$ in $F(X, Y)$ is 1. -/
  lin_coeff_Y : coeff (single 1 1) toFun = 1
  /-- Associativity condition: $F(F(X, Y), Z) = F(X, F(Y, Z))$. -/
  assoc : subst ![subst ![Y₀, Y₁] toFun, Y₂] toFun
    = subst ![Y₀, subst ![Y₁, Y₂] toFun] toFun (S := R)

variable (R) in
/-- A commutative formal group law is a formal group law satisfies additional commutativity
condition. -/
@[ext]
structure CommFormalGroup extends FormalGroup R where
  /- Commutativity condition: `F (X, Y) = F (Y, X)`. -/
  comm : toFun = toFun.subst ![X₁, X₀]

/-- Given a formal group `F`, `F.comm` is a proposition that `F(X,Y) = F(Y,X)`. -/
def FormalGroup.comm (F : FormalGroup R) : Prop :=
  F.toFun = MvPowerSeries.subst ![X₁, X₀] F.toFun

/-- A commutative formal group law is a formal group law. -/
instance : Coe (CommFormalGroup R) (FormalGroup R) where
  coe := CommFormalGroup.toFormalGroup

section Lemma

namespace MvPowerSeries

variable {F : MvPowerSeries (Fin 2) R}

lemma HasSubst.X_two {i j : σ} : HasSubst ![X i, X j (R := R)] :=
  hasSubst_of_constantCoeff_zero (by simp)

lemma HasSubst.cons_subst_zero_left (hF : constantCoeff F = 0) :
    HasSubst (![subst ![Y₀, Y₁] F, Y₂]) (S := R) := by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s; fin_cases s
  · simpa using constantCoeff_subst_eq_zero .X_two (by simp) hF
  · simp

lemma HasSubst.cons_subst_zero_right (hF : constantCoeff F = 0) :
    HasSubst ![Y₀, subst ![Y₁, Y₂] F] (S := R):= by
  refine hasSubst_of_constantCoeff_zero ?_
  intro s; fin_cases s
  · simp
  · simpa using constantCoeff_subst_eq_zero .X_two (by simp) hF

end MvPowerSeries

end Lemma

namespace FormalGroup

/-- addition of two multi variate power series under the formal group `F` sense, namely
`f₀ + [F] f₁ := F (f₀, f₁)` -/
abbrev add (F : FormalGroup R) (f₀ f₁ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  subst ![f₀, f₁] F.toFun

/-- `f₀ +[F] f₁` means `F (f₀, f₁)`. -/
scoped[FormalGroup] notation:65 f₀:65 " +[" F:0 "] " f₁:66 => add F f₀ f₁

variable (F : FormalGroup R)

/-- Additive formal group law `Gₐ(X,Y) = X + Y`. -/
def Gₐ : CommFormalGroup R where
  toFun := X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (F := X₀ + X₁) (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (F := X₀ + X₁) (by simp)
    simp_rw [subst_add aux₁, subst_X aux₁, subst_add aux₂, subst_X aux₂]
    simp [subst_add .X_two, subst_X .X_two, add_assoc]
  comm := by simp [subst_add .X_two, subst_X .X_two, add_comm]

@[simp]
lemma Gₐ_apply : Gₐ.toFun = X₀ + X₁ := rfl

/-- Multiplicative formal group law `Gₘ(X,Y) = X + Y + XY`. -/
def Gₘ : CommFormalGroup R where
  toFun := X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (F := X₀ + X₁ + X₀ * X₁) (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (F := X₀ + X₁ + X₀ * X₁) (by simp)
    simp_rw [subst_add aux₁, subst_mul aux₁, subst_X aux₁, subst_add aux₂, subst_mul aux₂,
      subst_X aux₂]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, subst_add .X_two, Fin.isValue, subst_X .X_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, subst_mul .X_two]
    ring
  comm := by
    simp [subst_add .X_two, subst_mul .X_two, subst_X .X_two, add_comm, mul_comm]

@[simp]
lemma Gₘ_apply : Gₘ.toFun = X₀ + X₁ + X₀ * X₁ := rfl

omit [Algebra R S] in
/-- Given a algebra map `f : R →+* S` and a formal group law `F` over `R`, then `f_* F` is a
formal group law formal group law over `S`. This is constructed by applying `f` to all coefficients
of the underlying power series. -/
def map (f : R →+* S) : FormalGroup S where
  toFun := F.toFun.map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => (![g₁, g₂] i).map f := by ext1 i; fin_cases i <;> simp
    simp_rw [(map_X f _).symm, this, ← map_subst .X_two, this, ← map_subst
      (HasSubst.cons_subst_zero_left F.zero_constantCoeff), F.assoc,
      ← map_subst (HasSubst.cons_subst_zero_right F.zero_constantCoeff)]

omit [Algebra R S] in
@[simp]
lemma map_apply (f : R →+* S) : (F.map f).toFun = F.toFun.map f := rfl

end FormalGroup
