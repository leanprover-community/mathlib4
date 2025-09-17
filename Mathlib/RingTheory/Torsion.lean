/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Torsion groups are the union of all subgroups of roots of unity

-/

variable {M : Type*} [CommMonoid M]

lemma CommGroup.mem_torsion_iff_exists_mem_rootsOfUnity {x : Mˣ} :
    x ∈ CommGroup.torsion Mˣ ↔ ∃ n ≠ 0, x ∈ rootsOfUnity n M := by
  simp [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one, Nat.pos_iff_ne_zero]

lemma rootsOfUnity_le_torsion (k : ℕ) [NeZero k] :
    rootsOfUnity k M ≤ CommGroup.torsion Mˣ := by
  intro
  have : k ≠ 0 := NeZero.out
  grind [CommGroup.mem_torsion_iff_exists_mem_rootsOfUnity]

lemma IsPrimitiveRoot.mem_torsion {ζ : Mˣ} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ ∈ CommGroup.torsion Mˣ :=
  CommGroup.mem_torsion_iff_exists_mem_rootsOfUnity.mpr ⟨n, hn, hζ.mem_rootsOfUnity⟩

lemma CommGroup.torsion_eq_biSup_rootsOfUnity :
    CommGroup.torsion Mˣ = ⨆ (n : ℕ) (_hn : n ≠ 0), rootsOfUnity n M := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [CommGroup.mem_torsion] at hx
    -- without `(i := ...)`, timeout at `isDefEq`
    rw [Subgroup.mem_biSup_of_directedOn (i := orderOf x) (orderOf_ne_zero_iff.mpr hx)]
    · use orderOf x
      simp [hx]
    · intro a ha b hb
      use a.lcm b
      simp_all [Function.onFun, rootsOfUnity_le_of_dvd, Nat.dvd_lcm_left, Nat.dvd_lcm_right]
  · simp only [iSup_le_iff]
    intro n hn
    have : NeZero n := ⟨hn⟩
    exact rootsOfUnity_le_torsion n

variable {R : Type*} [CommRing R] [IsDomain R]

lemma CommGroup.torsion_eq_rootsOfUnity_finite_card {R : Type*} [CommRing R] [IsDomain R]
    [Finite (CommGroup.torsion Rˣ)] :
    CommGroup.torsion Rˣ = rootsOfUnity (Nat.card (CommGroup.torsion Rˣ)) R := by
  have hc : IsCyclic (CommGroup.torsion Rˣ) :=
    isCyclic_of_subgroup_isDomain ((Units.coeHom R).comp (CommGroup.torsion Rˣ).subtype)
      (Units.val_injective.comp Subtype.val_injective)
  generalize h : Nat.card (CommGroup.torsion Rˣ) = n
  have : NeZero (Nat.card (CommGroup.torsion Rˣ)) :=
    ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  have : NeZero n := ⟨by simp_all [NeZero.out]⟩
  refine le_antisymm ?_ ?_
  · obtain ⟨ζ, hζ⟩ : ∃ ζ : Rˣ, IsPrimitiveRoot ζ n := by
      obtain ⟨ζ, hζ⟩ := hc.exists_ofOrder_eq_natCard
      rw [h, ← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff] at hζ
      exact ⟨ζ, hζ⟩
    intro x
    contrapose! h
    have : Fintype (torsion Rˣ) := Fintype.ofFinite _
    refine ne_of_gt ?_
    classical
    rw [← (card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot (n := n) (R := R)).mpr
      ⟨ζ, IsPrimitiveRoot.coe_units_iff.mpr hζ⟩, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_injective_of_notMem
      (Subgroup.inclusion (rootsOfUnity_le_torsion _)) (Subgroup.inclusion_injective _)
      (b := ⟨x, h.left⟩)
    simp [Subtype.ext_iff, - mem_rootsOfUnity, h.right]
  · exact rootsOfUnity_le_torsion _
