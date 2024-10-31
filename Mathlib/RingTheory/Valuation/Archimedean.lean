/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.Algebra.Order.Monoid.Submonoid
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Ring of integers under a given valuation in an multiplicatively archimedean codomain

-/

section Field

variable {F Γ₀ O : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
  [CommRing O] [Algebra O F] {v : Valuation F Γ₀}

instance : LinearOrderedCommGroupWithZero (MonoidHom.mrange v) where
  __ : CommGroupWithZero (MonoidHom.mrange v) := inferInstance
  __ : LinearOrder (MonoidHom.mrange v) := inferInstance
  zero_le_one := Subtype.coe_le_coe.mp zero_le_one
  mul_le_mul_left := by
    simp only [Subtype.forall, MonoidHom.mem_mrange, forall_exists_index, Submonoid.mk_mul_mk,
      Subtype.mk_le_mk, forall_apply_eq_imp_iff]
    intro a b hab c
    exact mul_le_mul_left' hab (v c)

namespace Valuation.Integers

lemma wfDvdMonoid_iff_wellFounded_gt_on_v (hv : Integers v O) :
    WfDvdMonoid O ↔ WellFounded ((· > ·) on (v ∘ algebraMap O F)) := by
  refine ⟨fun _ ↦ wellFounded_dvdNotUnit.mono ?_, fun h ↦ ⟨h.mono ?_⟩⟩ <;>
  simp [Function.onFun, hv.dvdNotUnit_iff_lt]

lemma wellFounded_gt_on_v_iff_discrete_mrange [Nontrivial (MonoidHom.mrange v)ˣ]
    (hv : Integers v O) :
    WellFounded ((· > ·) on (v ∘ algebraMap O F)) ↔
      Nonempty (MonoidHom.mrange v ≃*o WithZero (Multiplicative ℤ)) := by
  rw [← LinearOrderedCommGroupWithZero.wellFoundedOn_setOf_ge_gt_iff_nonempty_discrete_of_ne_zero
    one_ne_zero, ← Set.wellFoundedOn_range]
  classical
  refine ⟨fun h ↦ (h.mapsTo Subtype.val ?_).mono' (by simp), fun h ↦ (h.mapsTo ?_ ?_).mono' ?_⟩
  · rintro ⟨_, x, rfl⟩
    simp only [← Subtype.coe_le_coe, OneMemClass.coe_one, Set.mem_setOf_eq, Set.mem_range,
      Function.comp_apply]
    intro hx
    obtain ⟨y, rfl⟩ := hv.exists_of_le_one hx
    exact ⟨y, by simp⟩
  · exact fun x ↦ if hx : x ∈ MonoidHom.mrange v then ⟨x, hx⟩ else 1
  · intro
    simp only [Set.mem_range, Function.comp_apply, MonoidHom.mem_mrange, Set.mem_setOf_eq,
      forall_exists_index]
    rintro x rfl
    simp [← Subtype.coe_le_coe, hv.map_le_one]
  · simp [Function.onFun]

lemma isPrincipalIdealRing_iff_not_denselyOrdered [MulArchimedean Γ₀] (hv : Integers v O) :
    IsPrincipalIdealRing O ↔ ¬ DenselyOrdered (Set.range v) := by
  refine ⟨fun _ ↦ not_denselyOrdered_of_isPrincipalIdealRing hv, fun H ↦ ?_⟩
  rcases subsingleton_or_nontrivial (MonoidHom.mrange v)ˣ with hs|_
  · have h0 : (0 : MonoidHom.mrange v) = ⟨0, by simp⟩ := rfl
    have (x : (MonoidHom.mrange v)ˣ) : x.val = 1 := by
        rw [← Units.val_one, Units.eq_iff, Subsingleton.elim x 1]
    replace this : ∀ x ≠ 0, v x = 1 := by
      intros x hx
      specialize this (Units.mk0 ⟨v x, by simp⟩ _)
      · simp [ne_eq, Subtype.ext_iff, hx, h0]
      simpa [Subtype.ext_iff] using this
    suffices ∀ I : Ideal O, I = ⊥ ∨ I = ⊤ by
      constructor
      intro I
      rcases this I with rfl|rfl
      · exact ⟨0, Ideal.span_zero.symm⟩
      · exact ⟨1, Ideal.span_one.symm⟩
    simp_rw [or_iff_not_imp_right, Submodule.eq_bot_iff]
    intro I hI x hx
    contrapose! hI with h0
    specialize this (algebraMap O F x) (by simp [map_eq_zero_iff _ hv.hom_inj, h0])
    exact Ideal.eq_top_of_isUnit_mem _ hx (isUnit_of_one' hv this)
  have : IsDomain O := hv.hom_inj.isDomain
  have : ValuationRing O := ValuationRing.of_integers v hv
  have : IsBezout O := ValuationRing.instIsBezout
  have := ((IsBezout.TFAE (R := O)).out 1 3)
  rw [this, hv.wfDvdMonoid_iff_wellFounded_gt_on_v, hv.wellFounded_gt_on_v_iff_discrete_mrange,
    LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered]
  exact H

end Valuation.Integers

end Field
