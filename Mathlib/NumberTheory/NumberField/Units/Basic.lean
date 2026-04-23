/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike

/-!
# Units of a number field

We prove some basic results on the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K` and its torsion subgroup.

## Main definition

* `NumberField.Units.torsion`: the torsion subgroup of a number field.

## Main results

* `NumberField.isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if
  `|norm ℚ x| = 1`.

* `NumberField.Units.mem_torsion`: a unit `x : (𝓞 K)ˣ` is torsion iff `w x = 1` for all infinite
  places `w` of `K`.

## Tags
number field, units
-/

@[expose] public section

open scoped NumberField

noncomputable section

open NumberField Units

section Rat

set_option backward.isDefEq.respectTransparency false in
theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl

end Rat

variable (K : Type*) [Field K]

section IsUnit

variable {K}

theorem NumberField.isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]

end IsUnit

namespace NumberField.Units

section coe

instance : CoeHTC (𝓞 K)ˣ K :=
  ⟨fun x => algebraMap _ K (Units.val x)⟩

theorem coe_injective : Function.Injective ((↑) : (𝓞 K)ˣ → K) :=
  RingOfIntegers.coe_injective.comp Units.val_injective

variable {K}

theorem coe_coe (u : (𝓞 K)ˣ) : ((u : 𝓞 K) : K) = (u : K) := rfl

theorem coe_mul (x y : (𝓞 K)ˣ) : ((x * y : (𝓞 K)ˣ) : K) = (x : K) * (y : K) := rfl

theorem coe_pow (x : (𝓞 K)ˣ) (n : ℕ) : ((x ^ n : (𝓞 K)ˣ) : K) = (x : K) ^ n := by
  rw [← map_pow, ← val_pow_eq_pow_val]

theorem coe_zpow (x : (𝓞 K)ˣ) (n : ℤ) : (↑(x ^ n) : K) = (x : K) ^ n := by
  change ((Units.coeHom K).comp (map (algebraMap (𝓞 K) K))) (x ^ n) = _
  exact map_zpow _ x n

theorem coe_one : ((1 : (𝓞 K)ˣ) : K) = (1 : K) := rfl

theorem coe_neg_one : ((-1 : (𝓞 K)ˣ) : K) = (-1 : K) := rfl

theorem coe_ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

end coe

variable {K}

/--
The group homomorphism `(𝓞 K)ˣ →* ℂˣ` induced by a complex embedding of `K`.
-/
protected def complexEmbedding (φ : K →+* ℂ) : (𝓞 K)ˣ →* ℂˣ :=
  (map φ).comp (map (algebraMap (𝓞 K) K).toMonoidHom)

@[simp]
protected theorem complexEmbedding_apply (φ : K →+* ℂ) (u : (𝓞 K)ˣ) :
    Units.complexEmbedding φ u = φ u := rfl

protected theorem complexEmbedding_injective (φ : K →+* ℂ) :
    Function.Injective (Units.complexEmbedding φ) :=
  (map_injective φ.injective).comp (map_injective RingOfIntegers.coe_injective)

@[simp]
protected theorem complexEmbedding_inj (φ : K →+* ℂ) (u v : (𝓞 K)ˣ) :
    Units.complexEmbedding φ u = Units.complexEmbedding φ v ↔ u = v :=
  (Units.complexEmbedding_injective φ).eq_iff

open NumberField.InfinitePlace

variable (K)

@[simp]
protected theorem norm [NumberField K] (x : (𝓞 K)ˣ) :
    |Algebra.norm ℚ (x : K)| = 1 := by
  rw [← RingOfIntegers.coe_norm, isUnit_iff_norm.mp x.isUnit]

variable {K} in
theorem pos_at_place (x : (𝓞 K)ˣ) (w : InfinitePlace K) :
    0 < w x := pos_iff.mpr (coe_ne_zero x)

variable {K} in
theorem sum_mult_mul_log [NumberField K] (x : (𝓞 K)ˣ) :
    ∑ w : InfinitePlace K, w.mult * Real.log (w x) = 0 := by
  simpa [Units.norm, Real.log_prod, Real.log_pow] using
    congr_arg Real.log (prod_eq_abs_norm (x : K))

section torsion

/-- The torsion subgroup of the group of units. -/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

instance : Nonempty (torsion K) := One.instNonempty

variable [NumberField K]

theorem mem_torsion {x : (𝓞 K)ˣ} :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion]
  refine ⟨fun hx φ ↦ (((φ.comp <| algebraMap (𝓞 K) K).toMonoidHom.comp <|
    Units.coeHom _).isOfFinOrder hx).norm_eq_one, fun h ↦ isOfFinOrder_iff_pow_eq_one.2 ?_⟩
  obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.isIntegral_coe h
  exact ⟨n, hn, by ext; rw [NumberField.RingOfIntegers.coe_eq_algebraMap, coe_pow, hx,
    NumberField.RingOfIntegers.coe_eq_algebraMap, coe_one]⟩

/-- The torsion subgroup is finite. -/
instance : Fintype (torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

/-- The torsion subgroup is cyclic. -/
instance : IsCyclic (torsion K) := isCyclic_subgroup_units _

/-- The order of the torsion subgroup. -/
def torsionOrder : ℕ := Fintype.card (torsion K)

instance : NeZero (torsionOrder K) :=
  inferInstanceAs (NeZero (Fintype.card (torsion K)))

theorem torsionOrder_ne_zero :
    torsionOrder K ≠ 0 := NeZero.ne (torsionOrder K)

theorem torsionOrder_pos :
    0 < torsionOrder K := Nat.pos_of_neZero (torsionOrder K)

/-- If `k` does not divide `torsionOrder` then there are no nontrivial roots of unity of
  order dividing `k`. -/
theorem rootsOfUnity_eq_one {k : ℕ+} (hc : Nat.Coprime k (torsionOrder K))
    {ζ : (𝓞 K)ˣ} : ζ ∈ rootsOfUnity k (𝓞 K) ↔ ζ = 1 := by
  rw [mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
  refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc ?_ ?_)
  · exact orderOf_dvd_of_pow_eq_one h
  · have hζ : ζ ∈ torsion K := by
      rw [torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨k, k.prop, h⟩
    rw [orderOf_submonoid (⟨ζ, hζ⟩ : torsion K)]
    exact orderOf_dvd_card

/-- The group of roots of unity of order dividing `torsionOrder` is equal to the torsion
group. -/
theorem rootsOfUnity_eq_torsion :
    rootsOfUnity (torsionOrder K) (𝓞 K) = torsion K := by
  ext ζ
  rw [torsion, mem_rootsOfUnity]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨torsionOrder K, torsionOrder_pos K, h⟩
  · exact Subtype.ext_iff.mp (@pow_card_eq_one (torsion K) _ _ ⟨ζ, h⟩)

/--
The image of `torsion K` by a complex embedding is the group of complex roots of unity of
order `torsionOrder K`.
-/
theorem map_complexEmbedding_torsion (φ : K →+* ℂ) :
    (torsion K).map (Units.complexEmbedding φ) = rootsOfUnity (torsionOrder K) ℂ := by
  apply Subgroup.eq_of_le_of_card_ge
  · rw [← rootsOfUnity_eq_torsion]
    exact map_rootsOfUnity _ (torsionOrder K)
  · let e := ((torsion K).equivMapOfInjective (Units.complexEmbedding φ)
      (Units.complexEmbedding_injective φ)).symm.toEquiv
    rw [Nat.card_eq_fintype_card, Complex.card_rootsOfUnity, Nat.card_congr e, torsionOrder,
      Nat.card_eq_fintype_card]

theorem even_torsionOrder :
    Even (torsionOrder K) := by
  suffices orderOf (⟨-1, neg_one_mem_torsion⟩ : torsion K) = 2 by
    rw [even_iff_two_dvd, ← this]
    exact orderOf_dvd_card
  rw [← Subgroup.orderOf_coe, ← orderOf_units, Units.val_neg, val_one, orderOf_neg_one,
    ringChar.eq_zero, if_neg (by decide)]

section odd

variable {K}

set_option backward.isDefEq.respectTransparency false in
theorem torsion_eq_one_or_neg_one_of_odd_finrank
    (h : Odd (Module.finrank ℚ K)) (x : torsion K) : (x : (𝓞 K)ˣ) = 1 ∨ (x : (𝓞 K)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 K)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : K)),
        NumberField.InfinitePlace.nrRealPlaces_pos_of_odd_finrank h]
  · interval_cases hi : orderOf (x : (𝓞 K)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion _ x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

theorem torsionOrder_eq_two_of_odd_finrank (h : Odd (Module.finrank ℚ K)) :
    torsionOrder K = 2 := by
  classical
  refine (Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩)
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact torsion_eq_one_or_neg_one_of_odd_finrank h x

end odd

end torsion

end Units

end NumberField
