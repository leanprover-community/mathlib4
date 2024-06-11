/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root data and root systems

This file contains basic results for root systems and root data.

## Main definitions / results:

 * `RootPairing.ext`: In characteristic zero if there is no torsion, the correspondence between
   roots and coroots is unique.
 * `RootSystem.ext`: In characteristic zero if there is no torsion, a root system is determined
   entirely by its roots.
 * `RootSystem.mk'`: In characteristic zero if there is no torsion, to check that a family of
   roots form a root system, we do not need to check that the coroots are stable under reflections
   since this follows from the corresponding property for the roots.

## Todo

* Derived properties of pairs, e.g., (ultra)parallel linearly independent pairs generate infinite
   dihedral groups.
* Properties of Weyl group (faithful action on roots, finiteness for finite `ι`)
* Conditions for existence of Weyl-invariant form (e.g., finiteness).

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable (P : RootPairing ι R M N)

lemma isCrystallographic_iff :
    P.IsCrystallographic ↔ ∀ i j, ∃ z : ℤ, z = P.pairing i j := by
  rw [IsCrystallographic]
  refine ⟨fun h i j ↦ ?_, fun h i _ ⟨j, hj⟩ ↦ ?_⟩
  · simpa [AddSubgroup.mem_zmultiples_iff] using h i (mem_range_self j)
  · simpa [← hj, AddSubgroup.mem_zmultiples_iff] using h i j

lemma isReduced_iff : P.IsReduced ↔ ∀ (i j : ι), i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [IsReduced]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, false_or]
  · by_cases h' : i = j
    · exact Or.inl (congrArg (⇑P.root) h')
    · exact Or.inr (h i j h' hLin)

section pairs

variable (i j : ι)

lemma coxeterWeight_swap : coxeterWeight P i j = coxeterWeight P j i := by
  simp only [coxeterWeight, mul_comm]

lemma IsOrthogonal.symm : IsOrthogonal P i j ↔ IsOrthogonal P j i := by
  simp only [IsOrthogonal, and_comm]

lemma IsOrthogonal_comm (h : IsOrthogonal P i j) : Commute (P.reflection i) (P.reflection j) := by
  rw [Commute, SemiconjBy]
  ext v
  simp_all only [IsOrthogonal, reflection_mul, reflection_apply, smul_sub]
  simp_all only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    root_coroot_eq_pairing, smul_eq_mul, mul_zero, sub_zero]
  exact sub_right_comm v ((P.toLin v) (P.coroot j) • P.root j)
      ((P.toLin v) (P.coroot i) • P.root i)

lemma reflection_apply_lin_comb (x : M) (a b : R) :
    P.reflection i (x + a • P.root i + b • P.root j) =
    x + (- a - P.toLin x (P.coroot i) - b * P.pairing j i) • P.root i + b • P.root j := by
  rw [reflection_apply, LinearMap.map_add₂, LinearMap.map_add₂, map_smul, LinearMap.smul_apply,
    root_coroot_eq_pairing, pairing_same, smul_eq_mul, mul_comm, two_mul]
  simp only [map_smul, LinearMap.smul_apply, root_coroot_eq_pairing, smul_eq_mul, sub_smul,
    add_smul, neg_smul]
  abel

lemma reflection_reflection (x : M) : P.reflection i (P.reflection j x) =
    x - P.toLin x (P.coroot j) • P.root j - (P.toLin x (P.coroot i) -
    P.toLin x (P.coroot j) • (P.pairing j i)) • P.root i := by
  rw [reflection_apply P j, reflection_apply P i]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, root_coroot_eq_pairing,
    smul_eq_mul]

lemma linearDependent_of_eq_reflection (h : P.reflection i = P.reflection j) (h₁ : ¬ (2 : R) = 0) :
    ¬ LinearIndependent R ![P.root i, P.root j] := by
  have h₂ : ∀ (x : M), P.reflection i x = P.reflection j x := congrFun (congrArg DFunLike.coe h)
  have h₃ : ∀ (x : M), P.toLin x (P.coroot i) • P.root i = P.toLin x (P.coroot j) • P.root j := by
    intro x
    specialize h₂ x
    rw [reflection_apply, reflection_apply, sub_eq_sub_iff_add_eq_add, add_left_cancel_iff] at h₂
    exact id h₂.symm
  have h₄ : (2 : R) • P.root i + (-P.pairing i j) • P.root j = 0 := by
    specialize h₃ (P.root i)
    rw [root_coroot_two, root_coroot_eq_pairing] at h₃
    rw [h₃, neg_smul, add_neg_eq_zero]
  rw [@LinearIndependent.pair_iff]
  intro h'
  specialize h' 2 (-P.pairing i j)
  specialize h' h₄
  apply h₁ h'.left

/-!
lemma coxeterWeight_one_order (h: coxeterWeight P i j = 1) :
    orderOf (P.reflection i * P.reflection j) = 3 := by
  sorry

lemma coxeterWeight_two_order (h: coxeterWeight P i j = 2) :
    orderOf (P.reflection i * P.reflection j) = 4 := by
  sorry

lemma coxeterWeight_three_order (h: coxeterWeight P i j = 3) :
    orderOf (P.reflection i * P.reflection j) = 6 := by
  sorry


lemma Commute_IsOrthogonal (h : Commute (P.reflection i) (P.reflection j)) :
    IsOrthogonal P i j := by
  rw [IsOrthogonal, pairing, pairing]
  have hx : ∀ (x : M), (P.reflection i) (P.reflection j x) =
      (P.reflection j) (P.reflection i x) := by
    intro x
    rw [Commute, SemiconjBy] at h
    rw [← @reflection_mul, h, reflection_mul]

  -- try applying h to P.root i and P.root j
  sorry
-/

-- parallel, non-syemmetrizable, definite, indefinite, ultraparallel

--lemma parallel_linearIndependent

end pairs

variable [Finite ι]

lemma eq_of_pairing_pairing_eq_two [NoZeroSMulDivisors ℤ M] (i j : ι)
    (hij : P.pairing i j = 2) (hji : P.pairing j i = 2) :
    i = j := by
  set α := P.root i
  set β := P.root j
  set sα : M ≃ₗ[R] M := P.reflection i
  set sβ : M ≃ₗ[R] M := P.reflection j
  set sαβ : M ≃ₗ[R] M := sβ.trans sα
  have hα : sα β = β - (2 : R) • α := by rw [P.reflection_apply_root, hji]
  have hβ : sβ α = α - (2 : R) • β := by rw [P.reflection_apply_root, hij]
  have hb : BijOn sαβ (range P.root) (range P.root) :=
    (P.bijOn_reflection_root i).comp (P.bijOn_reflection_root j)
  set f : ℕ → M := fun n ↦ β + (2 * n : ℤ) • (α - β)
  have hf : ∀ n : ℕ, (sαβ^[n]) β = f n := by
    intro n
    induction n with
    | zero => simp [f]
    | succ n ih =>
      simp only [f, α, β, sα, sβ, sαβ, iterate_succ', ih, hα, hβ, two_smul, smul_add,
        mul_add, add_smul, comp_apply, map_zsmul, zsmul_sub, map_add, neg_sub, map_neg,
        smul_neg, map_sub, Nat.cast_succ, mul_one, LinearEquiv.trans_apply,
        reflection_apply_self] -- v4.7.0-rc1 issues
      abel
  set f' : ℕ → range P.root := fun n ↦ ⟨f n, by
    rw [← IsFixedPt.image_iterate hb.image_eq n, ← hf]; exact mem_image_of_mem _ (mem_range_self j)⟩
  have : ¬ Injective f' := not_injective_infinite_finite f'
  contrapose! this
  intros n m hnm
  rw [Subtype.mk_eq_mk, add_right_inj, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero,
    sub_eq_zero] at hnm
  linarith [hnm.resolve_right (P.root.injective.ne this)]

/-- Even though the roots may not span, coroots are distinguished by their pairing with the
roots. The proof depends crucially on the fact that there are finitely-many roots.

Modulo trivial generalisations, this statement is exactly Lemma 1.1.4 on page 87 of SGA 3 XXI. -/
lemma injOn_dualMap_subtype_span_root_coroot [NoZeroSMulDivisors ℤ M] :
    InjOn ((span R (range P.root)).subtype.dualMap ∘ₗ P.toLin.flip) (range P.coroot) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices ∀ k, P.pairing k i = P.pairing k j from
    P.eq_of_pairing_pairing_eq_two i j (by simp [← this i]) (by simp [this j])
  intro k
  simpa using LinearMap.congr_fun hij ⟨P.root k, Submodule.subset_span (mem_range_self k)⟩

/-- In characteristic zero if there is no torsion, the correspondence between roots and coroots is
unique.

Formally, the point is that the hypothesis `hc` depends only on the range of the coroot mappings. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {P₁ P₂ : RootPairing ι R M N}
    (he : P₁.toLin = P₂.toLin)
    (hr : P₁.root = P₂.root)
    (hp : P₁.reflection_perm = P₂.reflection_perm)
    (hc : range P₁.coroot = range P₂.coroot) :
    P₁ = P₂ := by
  suffices P₁.coroot = P₂.coroot by cases' P₁ with p₁; cases' P₂ with p₂; cases p₁; cases p₂; congr
  have := NoZeroSMulDivisors.int_of_charZero R M
  ext i
  apply P₁.injOn_dualMap_subtype_span_root_coroot (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply]
  apply Dual.eq_of_preReflection_mapsTo' (P₁.ne_zero i) (finite_range P₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact P₁.coroot_root_two i
  · exact P₁.reflection_mapsto_root i
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.reflection_mapsto_root i

/-- This lemma exists to support the definition `RootSystem.mk'` and usually should not be used
directly. The lemma `RootPairing.coroot_eq_coreflection_of_root_eq_of_span_eq_top` or even
`RootSystem.coroot_eq_coreflection_of_root_eq` will usually be more convenient. -/
lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top' [CharZero R] [NoZeroSMulDivisors R M]
    (p : PerfectPairing R M N)
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p.toLin (root i) (coroot i) = 2)
    (hs : ∀ i, MapsTo (preReflection (root i) (p.toLin.flip (coroot i))) (range root) (range root))
    (hsp : span R (range root) = ⊤)
    {i j k : ι} (hk : root k = preReflection (root i) (p.toLin.flip (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (p.toLin (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.toLin.flip α')
  set sβ := preReflection β (p.toLin.flip β')
  let sα' := preReflection α' (p.toLin α)
  have hij : preReflection (sα β) (p.toLin.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.toLin.flip (coroot i)) (root i) = 2 := by rw [LinearMap.flip_apply, hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.toLin.flip β') hpi,
      preReflection_apply] -- v4.7.0-rc1 issues
  have hk₀ : root k ≠ 0 := fun h ↦ by simpa [h] using hp k
  apply p.bijectiveRight.injective
  apply Dual.eq_of_preReflection_mapsTo hk₀ (finite_range root) hsp (hp k) (hs k)
  · simp [α, β, α', β', sα, sβ, sα', hk, preReflection_apply, hp i, hp j, mul_two,
      mul_comm (p.toLin α β')]
    ring -- v4.7.0-rc1 issues
  · rw [hk, hij]
    exact (hs i).comp <| (hs j).comp (hs i)

/-- In characteristic zero if there is no torsion and the roots span, if the `i`th reflection of the
`j`th root is the `k`th root, then the corresponding relationship holds for coroots. See also
`RootSystem.coroot_eq_coreflection_of_root_eq`. -/
lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top [CharZero R] [NoZeroSMulDivisors R M]
    (hsp : span R (range P.root) = ⊤)
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) :=
  coroot_eq_coreflection_of_root_eq_of_span_eq_top' P.toPerfectPairing P.root P.coroot
    P.coroot_root_two P.reflection_mapsto_root hsp hk

end RootPairing

namespace RootSystem

open RootPairing

variable [Finite ι]
variable (P : RootSystem ι R M N)

/-- In characteristic zero if there is no torsion, a finite root system is determined entirely by
its roots. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {P₁ P₂ : RootSystem ι R M N}
    (he : P₁.toLin = P₂.toLin)
    (hr : P₁.root = P₂.root)
    (hp : P₁.reflection_perm = P₂.reflection_perm) :
    P₁ = P₂ := by
  suffices ∀ P₁ P₂ : RootSystem ι R M N, P₁.toLin = P₂.toLin → P₁.root = P₂.root →
      range P₁.coroot ⊆ range P₂.coroot by
    have h₁ := this P₁ P₂ he hr
    have h₂ := this P₂ P₁ he.symm hr.symm
    cases' P₁ with P₁
    cases' P₂ with P₂
    congr
    exact RootPairing.ext he hr hp (le_antisymm h₁ h₂)
  clear! P₁ P₂
  rintro P₁ P₂ he hr - ⟨i, rfl⟩
  use i
  apply P₁.bijectiveRight.injective
  apply Dual.eq_of_preReflection_mapsTo (P₁.ne_zero i) (finite_range P₁.root) P₁.span_eq_top
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.reflection_mapsto_root i
  · exact P₁.coroot_root_two i
  · exact P₁.reflection_mapsto_root i

/-- In characteristic zero if there is no torsion, to check that a family of roots form a root
system, we do not need to check that the coroots are stable under reflections since this follows
from the corresponding property for the roots. -/
def mk' [CharZero R] [NoZeroSMulDivisors R M]
    (p : PerfectPairing R M N)
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p.toLin (root i) (coroot i) = 2)
    (hs : ∀ i, MapsTo (preReflection (root i) (p.toLin.flip (coroot i))) (range root) (range root))
    (hsp : span R (range root) = ⊤) :
    RootSystem ι R M N where
  toPerfectPairing := p
  root := root
  coroot := coroot
  root_coroot_two := hp
  span_eq_top := hsp
  reflection_perm i := reflection_in i p root coroot hp hs
  reflection_perm_root i j := by
    simp only [reflection_in_apply]
    rw [← (exist_root_reflection p root coroot hs i j).choose_spec]
  reflection_perm_coroot i j := by
    simp only [reflection_in_apply]
    refine (coroot_eq_coreflection_of_root_eq_of_span_eq_top' p root coroot hp hs hsp ?_).symm
    rw [← (exist_root_reflection p root coroot hs i j).choose_spec]

/-- In characteristic zero if there is no torsion, if the `i`th reflection of the `j`th root is the
`k`th root, then the corresponding relationship holds for coroots. -/
lemma coroot_eq_coreflection_of_root_eq [CharZero R] [NoZeroSMulDivisors R M]
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) :=
  P.coroot_eq_coreflection_of_root_eq_of_span_eq_top P.span_eq_top hk

end RootSystem
