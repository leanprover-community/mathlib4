/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.Ring.NamePowerVars

/-! # Formal group laws over commutative ring

Let `R` be a commutative ring, a one dimensional formal group law is a formal power series
`F(X,Y) ∈ R⟦X,Y⟧` such that
  * `F(X,Y) = X + Y + higher order terms`.
  * `F(F(X,Y),Z) = F(X,F(Y,Z))`.

Under this definition, we can prove that `F(X,0) = X` and `F(0,X) = X`. Moreover, there is a
unique power series `i(X)` such that `F(X, i(X)) = 0`, which is considered to be the inverse
of the formal group law `F(X,Y)`.

## Main definitions/lemmas

* `FormalGroup R`: definition of one dimensional formal group law over commutative ring `R`.

* Properties: `F(X,0) = 0` and `F(0,X) = X`.

* Additive formal group laws `𝔾ₐ` and multiplicative formal group laws `𝔾ₘ`.

* Instance: Group instance defined by the formal group law `F` over the ideal
  `PowerSeries.hasEvalIdeal`.

## References
* [Hazewinkel, Michiel. Formal Groups and Applications][hazewinkel1978]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {σ τ : Type*}

noncomputable section

open MvPowerSeries Finsupp

name_power_vars X₀, X₁ over R

name_power_vars Y₀, Y₁, Y₂ over R

variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`. -/
@[ext]
structure FormalGroup where
  /-- The underlying power series $F(X, Y)$ in two variables. -/
  toPowerSeries : MvPowerSeries (Fin 2) R
  /-- The constant coefficient of the formal group law is zero. -/
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  /-- The coefficient of $X$ in $F(X, Y)$ is 1. -/
  lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
  /-- The coefficient of $Y$ in $F(X, Y)$ is 1. -/
  lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
  /-- Associativity condition: $F(F(X, Y), Z) = F(X, F(Y, Z))$. -/
  assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂]
    = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)

/-- The natural inclusion from formal group law into formal power series. -/
instance FormalGroup.coeToPowerSeries : Coe (FormalGroup R) (MvPowerSeries (Fin 2) R) :=
  ⟨toPowerSeries⟩

/-- Given a formal group `F`, `F.IsComm` is a proposition that $F(X,Y) = F(Y,X)$. -/
class FormalGroup.IsComm (F : FormalGroup R) : Prop where
  comm : F = (F : MvPowerSeries (Fin 2) R).subst ![X₁, X₀]

lemma FormalGroup.assoc' (F : FormalGroup R) {f₀ f₁ f₂ : MvPowerSeries σ R}
    (h₀ : PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) (h₂ : PowerSeries.HasSubst f₂) :
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![f₀, f₁], f₂] =
      F.toPowerSeries.subst ![f₀, F.toPowerSeries.subst ![f₁, f₂]] := by
  obtain aux₁ := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  obtain aux₂ := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  have : HasSubst ![f₀, f₁, f₂] :=
    hasSubst_of_constantCoeff_nilpotent fun s => by fin_cases s <;> simpa
  calc
    _ = (F.toPowerSeries.subst ![F.toPowerSeries.subst ![Y₀, Y₁], Y₂]).subst ![f₀, f₁, f₂] := by
      rw [subst_comp_subst_apply aux₁ this]
      congr! 2 with s
      fin_cases s
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero, subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst_X this]
      · simp [subst_X this]
    _ = _ := by
      rw [F.assoc, subst_comp_subst_apply aux₂ this]
      congr! 2 with s
      fin_cases s
      · simp [subst_X this]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst]

namespace FormalGroup

variable {σ : Type*} (F : FormalGroup R)

set_option linter.unusedVariables false in
/-- `Point F σ` represents the mathematical space of points of a formal group $F$
taking values in the formal power series ring `MvPowerSeries σ R` with the property
that constant coefficient is nilpotent.

TODO: Mathematically, a 1-dimensional formal group law $F$ over a ring $R$ defines a group
structure on the elements of a complete local $R$-algebra (specifically, its maximal ideal)
via the substitution operation $x +_F y = F(x, y)$. -/
@[nolint unusedArguments]
def Point (F : FormalGroup R) (σ : Type*) := {f : MvPowerSeries σ R // PowerSeries.HasSubst f}

instance : Add (F.Point σ) where
  add x y := ⟨(F : MvPowerSeries (Fin 2) R).subst ![x.val, y.val],
    isNilpotent_constCoeff_subst_of_isNilpotent_constCoeff
      (hasSubst_of_constantCoeff_nilpotent fun s => by fin_cases s <;> simp [x.prop, y.prop])
        (by simp [F.zero_constantCoeff])⟩

instance : Zero (F.Point σ) where
  zero := ⟨0, PowerSeries.HasSubst.zero⟩

/- TODO : Zero, SMul, Inv instance. -/

/-- Additive formal group law `𝔾ₐ(X,Y) = X + Y`. -/
@[simps]
def 𝔾ₐ : FormalGroup R where
  toPowerSeries := X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_X aux₁, subst_add aux₂, subst_X aux₂]
    simp [subst_add .X_X, subst_X .X_X, add_assoc]

instance : (𝔾ₐ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_X .X_X, add_comm]

/-- Multiplicative formal group law `𝔾ₘ(X,Y) = X + Y + XY`. -/
@[simps]
def 𝔾ₘ : FormalGroup R where
  toPowerSeries := X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_mul aux₁, subst_X aux₁, subst_add aux₂, subst_mul aux₂,
      subst_X aux₂]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, subst_add .X_X, Fin.isValue, subst_X .X_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, subst_mul .X_X]
    ring

instance : (𝔾ₘ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_mul .X_X, subst_X .X_X, add_comm, mul_comm]

/-- Given an algebra map `f : R →+* S` and a formal group law `F` over `R`, then `f_* F` is a
formal group law formal group law over `S`. This is constructed by applying `f` to all coefficients
of the underlying power series. -/
@[simps]
def map (f : R →+* S) : FormalGroup S where
  toPowerSeries := (F : MvPowerSeries (Fin 2) R).map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => (![g₁, g₂] i).map f := by ext1 i; fin_cases i <;> simp
    simp_rw [(map_X f _).symm, this, ← map_subst .X_X, this, ← map_subst
      (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff), F.assoc,
      ← map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff)]

end FormalGroup

section

namespace FormalGroup

variable (F : FormalGroup R)

/-- An abbreviation of $F(X,0)$ for a formal group $F$. -/
abbrev Xzero : PowerSeries R := subst ![PowerSeries.X, 0] F.toPowerSeries

lemma constantCoeff_Xzero : F.Xzero.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, Xzero, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.X_zero _ F.zero_constantCoeff]

@[simp]
lemma coeff_one_Xzero : F.Xzero.coeff 1 = 1 := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 0 1)]
  · simp [F.lin_coeff_X]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · by_cases hd₀ : d 0 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.X_zero

@[simp]
lemma Xzero_subst_Xzero : F.Xzero.subst F.Xzero = F.Xzero := by
  calc
    _ = F.toPowerSeries.subst ![F.toPowerSeries.subst ![PowerSeries.X, 0], 0] := by
      have : PowerSeries.HasSubst (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff, PowerSeries.X, constantCoeff_subst_eq_zero HasSubst.X_zero
          (by simp) F.zero_constantCoeff]
      rw [PowerSeries.subst, subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
      · exact HasSubst.X_zero
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 → PowerSeries R) := by
        ext x : 1; fin_cases x <;> rfl
      simp [F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst.X', PowerSeries.HasSubst]

lemma Xzero_eq_X : F.Xzero = PowerSeries.X := by
  haveI : Invertible (F.Xzero.coeff 1) := (coeff_one_Xzero F) ▸ invertibleOne
  calc
    _ = F.Xzero.substInv.subst (F.Xzero.subst F.Xzero) := by
      have aux₀ : PowerSeries.HasSubst F.Xzero :=
        PowerSeries.HasSubst.of_constantCoeff_zero' <| constantCoeff_Xzero F
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀, PowerSeries.subst_substInv_left _
        F.constantCoeff_Xzero , PowerSeries.subst_X aux₀, Xzero]
    _ = _ := by
      rw [Xzero_subst_Xzero, F.Xzero.subst_substInv_left F.constantCoeff_Xzero]

/-- An abbreviation of $F(0,X)$ for a formal group $F$. -/
abbrev zeroX : PowerSeries R := subst ![0, PowerSeries.X] F.toPowerSeries

lemma constantCoeff_zeroX : F.zeroX.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, zeroX, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.zero_X _ F.zero_constantCoeff]

@[simp]
lemma coeff_one_zeroX : F.zeroX.coeff 1 = 1 := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 1 1)]
  · simp [F.lin_coeff_Y]
  · intro d hd
    by_cases hd₁ : d 0 = 0
    · by_cases hd₀ : d 1 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.zero_X

@[simp]
lemma zeroX_subst_zeroX : F.zeroX.subst F.zeroX = F.zeroX := by
  calc
    _ = F.toPowerSeries.subst ![0, F.toPowerSeries.subst ![0, PowerSeries.X]] := by
      have : PowerSeries.HasSubst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff, PowerSeries.X, constantCoeff_subst_eq_zero HasSubst.zero_X
          (by simp) F.zero_constantCoeff]
      rw [PowerSeries.subst, subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
      · exact HasSubst.zero_X
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 → PowerSeries R) := by ext x : 1; fin_cases x <;> rfl
      simp [← F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst.X', PowerSeries.HasSubst]

lemma zeroX_eq_X : F.zeroX = PowerSeries.X := by
  haveI : Invertible (F.zeroX.coeff 1) := (coeff_one_zeroX F) ▸ invertibleOne
  calc
    _ = F.zeroX.substInv.subst (F.zeroX.subst F.zeroX) := by
      have aux₀ : PowerSeries.HasSubst F.zeroX :=
        PowerSeries.HasSubst.of_constantCoeff_zero' <| F.constantCoeff_zeroX
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀, PowerSeries.subst_substInv_left _
        F.constantCoeff_zeroX, PowerSeries.subst_X aux₀, zeroX]
    _ = _ := by
      rw [zeroX_subst_zeroX, F.zeroX.subst_substInv_left F.constantCoeff_zeroX]

theorem add_zero {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![f, 0] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![PowerSeries.X (R := R), 0]) := by
      rw [PowerSeries.subst, subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [PowerSeries.X, subst]
        · simp [subst, eval₂]
      exact HasSubst.X_zero
    _ = _ := by
      simp [Xzero_eq_X, PowerSeries.subst_X hf]

theorem zero_add {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![0, f] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![0, PowerSeries.X (R := R)]) := by
      rw [PowerSeries.subst, subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [subst, eval₂]
        · simp [PowerSeries.X, subst]
      · exact HasSubst.zero_X
    _ = _ := by
      simp [zeroX_eq_X, PowerSeries.subst_X hf]

instance : AddZeroClass (F.Point σ) where
  zero_add x := Subtype.ext (zero_add F x.prop)
  add_zero x := Subtype.ext (add_zero F x.prop)

end FormalGroup

end
