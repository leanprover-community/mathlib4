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

variable (P : RootPairing ι R M N) (i j : ι)

lemma root_ne (h: i ≠ j) : P.root i ≠ P.root j := by
  simp_all only [ne_eq, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true]

lemma ne_zero [CharZero R] : (P.root i : M) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

lemma ne_zero' [CharZero R] : (P.coroot i : N) ≠ 0 :=
  fun h ↦ by simpa [h] using P.root_coroot_two i

@[simp]
lemma root_coroot_eq_pairing :
    P.toLin (P.root i) (P.coroot j) = P.pairing i j :=
  rfl

lemma coroot_root_eq_pairing :
    P.toLin.flip (P.coroot i) (P.root j) = P.pairing j i := by
  simp

@[simp]
lemma pairing_same : P.pairing i i = 2 := P.root_coroot_two i

lemma coroot_root_two :
    P.toLin.flip (P.coroot i) (P.root i) = 2 := by
  simp

@[simp] lemma flip_flip : P.flip.flip = P := rfl

lemma reflection_apply (x : M) :
    P.reflection i x = x - (P.toLin x (P.coroot i)) • P.root i :=
  rfl

lemma reflection_apply_root :
    P.reflection i (P.root j) = P.root j - (P.pairing j i) • P.root i :=
  rfl

@[simp]
lemma reflection_apply_self :
    P.reflection i (P.root i) = - P.root i :=
  Module.reflection_apply_self (P.coroot_root_two i)

@[simp]
lemma reflection_same (x : M) : P.reflection i (P.reflection i x) = x :=
  Module.involutive_reflection (P.coroot_root_two i) x

lemma reflection_invOn_self : InvOn (P.reflection i) (P.reflection i) (range P.root)
    (range P.root) := by
  constructor <;>
    exact fun x _ => Module.involutive_reflection (P.coroot_root_two i) x

lemma bijOn_reflection_root : BijOn (P.reflection i) (range P.root) (range P.root) := InvOn.bijOn
  (reflection_invOn_self P i) (mapsTo_preReflection_root P i) (mapsTo_preReflection_root P i)

lemma coreflection_apply (f : N) :
    P.coreflection i f = f - (P.toLin (P.root i) f) • P.coroot i :=
  rfl

@[simp]
lemma coreflection_apply_self :
    P.coreflection i (P.coroot i) = - P.coroot i :=
  Module.reflection_apply_self (P.flip.coroot_root_two i)

lemma coreflection_eq_flip_reflection (f : N) : P.coreflection i f = P.flip.reflection i f :=
  rfl

@[simp]
lemma coreflection_self (x : N) : P.coreflection i (P.coreflection i x) = x :=
  reflection_same P.flip i x

lemma coreflection_invOn_self : InvOn (P.coreflection i) (P.coreflection i) (range P.coroot)
    (range P.coroot) := reflection_invOn_self P.flip i

lemma bijOn_coreflection_coroot : BijOn (P.coreflection i) (range P.coroot) (range P.coroot) :=
  bijOn_reflection_root P.flip i

@[simp]
lemma reflection_image_eq :
    P.reflection i '' (range P.root) = range P.root :=
  (P.bijOn_reflection_root i).image_eq

@[simp]
lemma coreflection_image_eq :
    P.coreflection i '' (range P.coroot) = range P.coroot :=
  (P.bijOn_coreflection_coroot i).image_eq

lemma reflection_dualMap_eq_coreflection :
    (P.reflection i).dualMap ∘ₗ P.toLin.flip = P.toLin.flip ∘ₗ P.coreflection i := by
  ext n m
  simp [coreflection_apply, reflection_apply, mul_comm (P.toLin m (P.coroot i))]

lemma reflection_mul (x : M) :
    (P.reflection i * P.reflection j) x = P.reflection i (P.reflection j x) := rfl

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
  · exact P₁.mapsTo_preReflection_root i
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.mapsTo_preReflection_root i

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
    P.coroot_root_two P.mapsTo_preReflection_root hsp hk

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
    (hr : P₁.root = P₂.root) :
    P₁ = P₂ := by
  suffices ∀ P₁ P₂ : RootSystem ι R M N, P₁.toLin = P₂.toLin → P₁.root = P₂.root →
      range P₁.coroot ⊆ range P₂.coroot by
    have h₁ := this P₁ P₂ he hr
    have h₂ := this P₂ P₁ he.symm hr.symm
    cases' P₁ with P₁
    cases' P₂ with P₂
    congr
    exact RootPairing.ext he hr (le_antisymm h₁ h₂)
  clear! P₁ P₂
  rintro P₁ P₂ he hr - ⟨i, rfl⟩
  use i
  apply P₁.bijectiveRight.injective
  apply Dual.eq_of_preReflection_mapsTo (P₁.ne_zero i) (finite_range P₁.root) P₁.span_eq_top
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.mapsTo_preReflection_root i
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_preReflection_root i

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
  mapsTo_preReflection_root := hs
  span_eq_top := hsp
  mapsTo_preReflection_coroot := by
    rintro i - ⟨j, rfl⟩
    obtain ⟨k, h⟩ := hs i (mem_range_self j)
    exact ⟨k, coroot_eq_coreflection_of_root_eq_of_span_eq_top' p root coroot hp hs hsp h⟩

/-- In characteristic zero if there is no torsion, if the `i`th reflection of the `j`th root is the
`k`th root, then the corresponding relationship holds for coroots. -/
lemma coroot_eq_coreflection_of_root_eq [CharZero R] [NoZeroSMulDivisors R M]
    {i j k : ι} (hk : P.root k = P.reflection i (P.root j)) :
    P.coroot k = P.coreflection i (P.coroot j) :=
  P.coroot_eq_coreflection_of_root_eq_of_span_eq_top P.span_eq_top hk

end RootSystem
