/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Rodriguez
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Center
public import Mathlib.GroupTheory.ClassEquation
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Wedderburn's Little Theorem

This file proves Wedderburn's Little Theorem.

## Main Declarations

* `littleWedderburn`: a finite division ring is a field.

## Future work

A couple simple generalisations are possible:
* A finite ring is commutative iff all its nilpotents lie in the center.
  [Chintala, Vineeth, *Sorry, the Nilpotents Are in the Center*][chintala2020]
* A ring is commutative if all its elements have finite order.
  [Dolan, S. W., *A Proof of Jacobson's Theorem*][dolan1975]

When alternativity is added to Mathlib, one could formalise the Artin-Zorn theorem, which states
that any finite alternative division ring is in fact a field.
https://en.wikipedia.org/wiki/Artin%E2%80%93Zorn_theorem

If interested, generalisations to semifields could be explored. The theory of semi-vector spaces is
not clear, but assuming that such a theory could be found where every module considered in the
below proof is free, then the proof works nearly verbatim.

-/

@[expose] public section

open scoped Polynomial
open Fintype

/-! Everything in this namespace is internal to the proof of Wedderburn's little theorem. -/
namespace LittleWedderburn

variable (D : Type*) [DivisionRing D]

private def InductionHyp : Prop :=
  ∀ {R : Subring D}, R < ⊤ → ∀ ⦃x y⦄, x ∈ R → y ∈ R → x * y = y * x

namespace InductionHyp

open Module Polynomial

variable {D}

@[implicit_reducible]
private def field (hD : InductionHyp D) {R : Subring D} (hR : R < ⊤)
    [Fintype D] [DecidableEq D] [DecidablePred (· ∈ R)] :
    Field R :=
  { show DivisionRing R from Fintype.divisionRingOfIsDomain R with
    mul_comm := fun x y ↦ Subtype.ext <| hD hR x.2 y.2 }

/-- We prove that if every subring of `D` is central, then so is `D`. -/
private theorem center_eq_top [Finite D] (hD : InductionHyp D) : Subring.center D = ⊤ := by
  classical
  cases nonempty_fintype D
  set Z := Subring.center D
  -- We proceed by contradiction; that is, we assume the center is strictly smaller than `D`.
  by_contra! hZ
  letI : Field Z := hD.field hZ.lt_top
  set q := card Z with card_Z
  have hq : 1 < q := by rw [card_Z]; exact one_lt_card
  let n := finrank Z D
  have card_D : card D = q ^ n := Module.card_eq_pow_finrank
  have h1qn : 1 ≤ q ^ n := by rw [← card_D]; exact card_pos
  -- We go about this by looking at the class equation for `Dˣ`:
  -- `q ^ n - 1 = q - 1 + ∑ x : conjugacy classes (D ∖ Dˣ), |x|`.
  -- The next few lines gets the equation into basically this form over `ℤ`.
  have key := Group.card_center_add_sum_card_noncenter_eq_card (Dˣ)
  rw [card_congr (show _ ≃* Zˣ from Subgroup.centerUnitsEquivUnitsCenter D).toEquiv,
      card_units, ← card_Z, card_units, card_D] at key
  -- By properties of the cyclotomic function, we have that `Φₙ(q) ∣ q ^ n - 1`; however, when
  -- `n ≠ 1`, then `¬Φₙ(q) | q - 1`; so if the sum over the conjugacy classes is divisible by
  -- `Φₙ(q)`, then `n = 1`, and therefore the vector space is trivial, as desired.
  let Φₙ := cyclotomic n ℤ
  apply_fun (Nat.cast : ℕ → ℤ) at key
  rw [Nat.cast_add, Nat.cast_sub h1qn, Nat.cast_sub hq.le, Nat.cast_one, Nat.cast_pow] at key
  suffices Φₙ.eval ↑q ∣ ↑(∑ x ∈ (ConjClasses.noncenter Dˣ).toFinset, x.carrier.toFinset.card) by
    have contra : Φₙ.eval _ ∣ _ := eval_dvd (cyclotomic.dvd_X_pow_sub_one n ℤ) (x := (q : ℤ))
    rw [eval_sub, eval_X_pow, eval_one, ← key, Int.dvd_add_left this] at contra
    refine (Nat.le_of_dvd ?_ ?_).not_gt (sub_one_lt_natAbs_cyclotomic_eval (n := n) ?_ hq.ne')
    · exact tsub_pos_of_lt hq
    · convert Int.natAbs_dvd_natAbs.mpr contra
      clear_value q
      simp only [eq_comm, Int.natAbs_eq_iff, Nat.cast_sub hq.le, Nat.cast_one, neg_sub, true_or]
    · by_contra! h
      obtain ⟨x, hx⟩ := finrank_le_one_iff.mp h
      refine not_le_of_gt hZ.lt_top (fun y _ ↦ Subring.mem_center_iff.mpr fun z ↦ ?_)
      obtain ⟨r, rfl⟩ := hx y
      obtain ⟨s, rfl⟩ := hx z
      rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm]
  rw [Nat.cast_sum]
  apply Finset.dvd_sum
  rintro ⟨x⟩ hx
  simp -zeta only [ConjClasses.quot_mk_eq_mk, Set.mem_toFinset] at hx ⊢
  set Zx := Subring.centralizer ({↑x} : Set D)
  -- The key thing is then to note that for all conjugacy classes `x`, `|x|` is given by
  -- `|Dˣ| / |Zxˣ|`, where `Zx` is the centralizer of `x`; but `Zx` is an algebra over `Z`, and
  -- therefore `|Zxˣ| = q ^ d - 1`, where `d` is the dimension of `D` as a vector space over `Z`.
  -- We therefore get that `|x| = (q ^ n - 1) / (q ^ d - 1)`, and as `d` is a strict divisor of `n`,
  -- we do have that `Φₙ(q) | (q ^ n - 1) / (q ^ d - 1)`; extending this over the whole sum
  -- gives us the desired contradiction..
  rw [Set.toFinset_card, ConjClasses.card_carrier, ← card_congr
        (show Zxˣ ≃* _ from unitsCentralizerEquiv _ x).toEquiv, card_units, card_D]
  have hZx : Zx ≠ ⊤ := by
    by_contra! hZx
    refine (ConjClasses.mk_bijOn (Dˣ)).mapsTo (Set.subset_center_units ?_) hx
    exact Subring.centralizer_eq_top_iff_subset.mp hZx <| Set.mem_singleton _
  letI : Field Zx := hD.field hZx.lt_top
  letI : Algebra Z Zx := (Subring.inclusion <| Subring.center_le_centralizer {(x : D)}).toAlgebra
  let d := finrank Z Zx
  have card_Zx : card Zx = q ^ d := Module.card_eq_pow_finrank
  have h1qd : 1 ≤ q ^ d := by rw [← card_Zx]; exact card_pos
  haveI : IsScalarTower Z Zx D := ⟨fun x y z ↦ mul_assoc _ _ _⟩
  rw [card_units, card_Zx]
  push_cast [h1qd, h1qn]
  apply Int.dvd_div_of_mul_dvd
  have aux : ∀ {k : ℕ}, ((X : ℤ[X]) ^ k - 1).eval ↑q = (q : ℤ) ^ k - 1 := by
    simp only [eval_X, eval_one, eval_pow, eval_sub, forall_const]
  rw [← aux, ← aux, ← eval_mul]
  refine map_dvd (evalRingHom ↑q) (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ ?_)
  refine Nat.mem_properDivisors.mpr ⟨⟨_, (finrank_mul_finrank Z Zx D).symm⟩, ?_⟩
  rw [← Nat.pow_lt_pow_iff_right hq, ← card_D, ← card_Zx]
  obtain ⟨b, -, hb⟩ := SetLike.exists_of_lt hZx.lt_top
  refine card_lt_of_injective_of_notMem _ Subtype.val_injective (?_ : b ∉ _)
  rintro ⟨b, rfl⟩
  exact hb b.2

end InductionHyp

private theorem center_eq_top [Finite D] : Subring.center D = ⊤ := by
  classical
  cases nonempty_fintype D
  induction hn : Fintype.card D using Nat.strong_induction_on generalizing D with | _ n IH
  apply InductionHyp.center_eq_top
  intro R hR x y hx hy
  suffices (⟨y, hy⟩ : R) ∈ Subring.center R by
    rw [Subring.mem_center_iff] at this
    simpa using this ⟨x, hx⟩
  let R_dr : DivisionRing R := Fintype.divisionRingOfIsDomain R
  rw [IH (Fintype.card R) _ R inferInstance rfl]
  · trivial
  rw [← hn, ← Subring.card_top D]
  convert! Set.card_lt_card hR

end LittleWedderburn

open LittleWedderburn

/-- A finite division ring is a field. See `Finite.isDomain_to_isField` and
`Fintype.divisionRingOfIsDomain` for more general statements, but these create data, and therefore
may cause diamonds if used improperly. -/
instance (priority := 100) littleWedderburn (D : Type*) [DivisionRing D] [Finite D] : Field D :=
  { ‹DivisionRing D› with
    mul_comm := fun x y ↦ by simp [Subring.mem_center_iff.mp ?_ x, center_eq_top D] }

alias Finite.divisionRing_to_field := littleWedderburn

/-- A finite domain is a field. See also `littleWedderburn` and `Fintype.divisionRingOfIsDomain`. -/
theorem Finite.isDomain_to_isField (D : Type*) [Finite D] [Ring D] [IsDomain D] : IsField D := by
  classical
  cases nonempty_fintype D
  let _ := Fintype.divisionRingOfIsDomain D
  let _ := littleWedderburn D
  exact Field.toIsField D
