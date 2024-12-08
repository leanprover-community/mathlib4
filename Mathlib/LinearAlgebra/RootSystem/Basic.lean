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
 * `RootPairing.mk'`: In characteristic zero if there is no torsion, to check that two finite
   families of roots and coroots form a root pairing, it is sufficient to check that they are
   stable under reflections.
 * `RootSystem.mk'`: In characteristic zero if there is no torsion, to check that a finite family of
   roots form a root system, we do not need to check that the coroots are stable under reflections
   since this follows from the corresponding property for the roots.

## TODO

* Properties of Weyl group (faithful action on roots, finiteness for finite `ι`)

-/

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

section reflection_perm

variable (p : PerfectPairing R M N) (root : ι ↪ M) (coroot : ι ↪ N) (i j : ι)
  (h : ∀ i, MapsTo (preReflection (root i) (p.toLin.flip (coroot i))) (range root) (range root))
include h

private theorem exist_eq_reflection_of_mapsTo  :
    ∃ k, root k = (preReflection (root i) (p.flip (coroot i))) (root j) :=
  h i (mem_range_self j)

variable (hp : ∀ i, p.toLin (root i) (coroot i) = 2)
include hp

private theorem choose_choose_eq_of_mapsTo :
    (exist_eq_reflection_of_mapsTo p root coroot i
      (exist_eq_reflection_of_mapsTo p root coroot i j h).choose h).choose = j := by
  refine root.injective ?_
  rw [(exist_eq_reflection_of_mapsTo p root coroot i _ h).choose_spec,
    (exist_eq_reflection_of_mapsTo p root coroot i j h).choose_spec]
  apply involutive_preReflection (x := root i) (hp i)

/-- The bijection on the indexing set induced by reflection. -/
@[simps]
protected def equiv_of_mapsTo :
    ι ≃ ι where
  toFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  invFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  left_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp
  right_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp

end reflection_perm

lemma infinite_of_linearIndependent_coxeterWeight_four [CharZero R] [NoZeroSMulDivisors ℤ M]
    (P : RootPairing ι R M N) (i j : ι) (hl : LinearIndependent R ![P.root i, P.root j])
    (hc : P.coxeterWeight i j = 4) : Infinite ι := by
  refine (infinite_range_iff (Embedding.injective P.root)).mp (Infinite.mono ?_
    ((infinite_range_reflection_reflection_iterate_iff (P.coroot_root_two i)
    (P.coroot_root_two j) ?_).mpr ?_))
  · rw [range_subset_iff]
    intro n
    rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo (P.coroot_root_two i)
      (P.mapsTo_reflection_root i)).comp (bijOn_reflection_of_mapsTo (P.coroot_root_two j)
      (P.mapsTo_reflection_root j))).image_eq n]
    exact mem_image_of_mem _ (mem_range_self j)
  · rw [coroot_root_eq_pairing, coroot_root_eq_pairing, ← hc, mul_comm, coxeterWeight]
  · rw [LinearIndependent.pair_iff] at hl
    specialize hl (P.pairing j i) (-2)
    simp only [neg_smul, neg_eq_zero, OfNat.ofNat_ne_zero, and_false, imp_false] at hl
    rw [ne_eq, coroot_root_eq_pairing, ← sub_eq_zero, sub_eq_add_neg]
    exact hl

variable [Finite ι] (P : RootPairing ι R M N) (i j : ι)

lemma coxeterWeight_ne_four_of_linearIndependent [CharZero R] [NoZeroSMulDivisors ℤ M]
    (hl : LinearIndependent R ![P.root i, P.root j]) :
    P.coxeterWeight i j ≠ 4 := by
  intro contra
  have := P.infinite_of_linearIndependent_coxeterWeight_four i j hl contra
  exact not_finite ι

/-- Even though the roots may not span, coroots are distinguished by their pairing with the
roots. The proof depends crucially on the fact that there are finitely-many roots.

Modulo trivial generalisations, this statement is exactly Lemma 1.1.4 on page 87 of SGA 3 XXI. -/
lemma injOn_dualMap_subtype_span_root_coroot [NoZeroSMulDivisors ℤ M] :
    InjOn ((span R (range P.root)).subtype.dualMap ∘ₗ P.toLin.flip) (range P.coroot) := by
  have := injOn_dualMap_subtype_span_range_range (finite_range P.root)
    (c := P.toLin.flip ∘ P.coroot) P.root_coroot_two P.mapsTo_reflection_root
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  exact P.bijectiveRight.injective <| this (mem_range_self i) (mem_range_self j) hij

/-- In characteristic zero if there is no torsion, the correspondence between roots and coroots is
unique.

Formally, the point is that the hypothesis `hc` depends only on the range of the coroot mappings. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {P₁ P₂ : RootPairing ι R M N}
    (he : P₁.toPerfectPairing = P₂.toPerfectPairing)
    (hr : P₁.root = P₂.root)
    (hc : range P₁.coroot = range P₂.coroot) :
    P₁ = P₂ := by
  have hp (hc' : P₁.coroot = P₂.coroot) : P₁.reflection_perm = P₂.reflection_perm := by
    ext i j
    refine P₁.root.injective ?_
    conv_rhs => rw [hr]
    simp only [root_reflection_perm, reflection_apply, coroot']
    simp only [hr, he, hc']
  suffices P₁.coroot = P₂.coroot by
    cases' P₁ with p₁; cases' P₂ with p₂; cases p₁; cases p₂; congr; exact hp this
  have := NoZeroSMulDivisors.int_of_charZero R M
  ext i
  apply P₁.injOn_dualMap_subtype_span_root_coroot (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply]
  apply Dual.eq_of_preReflection_mapsTo' (P₁.ne_zero i) (finite_range P₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.mapsTo_reflection_root i

private lemma coroot_eq_coreflection_of_root_eq' [CharZero R] [NoZeroSMulDivisors R M]
    (p : PerfectPairing R M N)
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p (root i) (coroot i) = 2)
    (hr : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hc : ∀ i, MapsTo (preReflection (coroot i) (p (root i))) (range coroot) (range coroot))
    {i j k : ι} (hk : root k = preReflection (root i) (p.flip (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (p (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by rw [PerfectPairing.flip_apply_apply, hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply]
  have hk₀ : root k ≠ 0 := fun h ↦ by simpa [h, ← PerfectPairing.toLin_apply] using hp k
  obtain ⟨l, hl⟩ := hc i (mem_range_self j)
  rw [← hl]
  have hkl : (p.flip (coroot l)) (root k) = 2 := by
    simp only [hl, preReflection_apply, hk, PerfectPairing.flip_apply_apply, map_sub, hp j,
      map_smul, smul_eq_mul, hp i, mul_sub, sα, α, α', β, mul_two, mul_add, LinearMap.sub_apply,
      LinearMap.smul_apply]
    rw [mul_comm (p (root i) (coroot j))]
    abel
  suffices p.flip (coroot k) = p.flip (coroot l) from p.bijectiveRight.injective this
  have _i : NoZeroSMulDivisors ℤ M := NoZeroSMulDivisors.int_of_charZero R M
  have := injOn_dualMap_subtype_span_range_range (finite_range root)
    (c := p.flip ∘ coroot) hp hr
  apply this (mem_range_self k) (mem_range_self l)
  refine Dual.eq_of_preReflection_mapsTo' hk₀ (finite_range root)
    (Submodule.subset_span <| mem_range_self k) (hp k) (hr k) hkl ?_
  rw [comp_apply, hl, hk, hij]
  exact (hr i).comp <| (hr j).comp (hr i)

/-- In characteristic zero if there is no torsion, to check that two finite families of roots and
coroots form a root pairing, it is sufficient to check that they are stable under reflections. -/
def mk' [Finite ι] [CharZero R] [NoZeroSMulDivisors R M]
    (p : PerfectPairing R M N)
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p (root i) (coroot i) = 2)
    (hr : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hc : ∀ i, MapsTo (preReflection (coroot i) (p (root i))) (range coroot) (range coroot)) :
    RootPairing ι R M N where
  toPerfectPairing := p
  root := root
  coroot := coroot
  root_coroot_two := hp
  reflection_perm i := RootPairing.equiv_of_mapsTo p root coroot i hr hp
  reflection_perm_root i j := by
    rw [equiv_of_mapsTo_apply, (exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec,
      preReflection_apply, PerfectPairing.flip_apply_apply]
  reflection_perm_coroot i j := by
    refine (coroot_eq_coreflection_of_root_eq' p root coroot hp hr hc ?_).symm
    rw [equiv_of_mapsTo_apply, (exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec]

end RootPairing

namespace RootSystem

open RootPairing

variable [Finite ι] (P : RootSystem ι R M N)

/-- In characteristic zero if there is no torsion, a finite root system is determined entirely by
its roots. -/
@[ext]
protected lemma ext [CharZero R] [NoZeroSMulDivisors R M]
    {P₁ P₂ : RootSystem ι R M N}
    (he : P₁.toPerfectPairing = P₂.toPerfectPairing)
    (hr : P₁.root = P₂.root) :
    P₁ = P₂ := by
  suffices ∀ P₁ P₂ : RootSystem ι R M N, P₁.toPerfectPairing = P₂.toPerfectPairing →
      P₁.root = P₂.root → range P₁.coroot ⊆ range P₂.coroot by
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
  · exact hr ▸ he ▸ P₂.mapsTo_reflection_root i
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i

private lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top [CharZero R] [NoZeroSMulDivisors R M]
    (p : PerfectPairing R M N)
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p (root i) (coroot i) = 2)
    (hs : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hsp : span R (range root) = ⊤)
    {i j k : ι} (hk : root k = preReflection (root i) (p.flip (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (p (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.toLin.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by rw [PerfectPairing.flip_apply_apply, hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply] -- v4.7.0-rc1 issues
  have hk₀ : root k ≠ 0 := fun h ↦ by simpa [h, ← PerfectPairing.toLin_apply] using hp k
  apply p.bijectiveRight.injective
  apply Dual.eq_of_preReflection_mapsTo hk₀ (finite_range root) hsp (hp k) (hs k)
  · simp [map_sub, α, β, α', β', sα, sβ, sα', hk, preReflection_apply, hp i, hp j, mul_two,
      mul_comm (p α β')]
    ring -- v4.7.0-rc1 issues
  · rw [hk, hij]
    exact (hs i).comp <| (hs j).comp (hs i)

/-- In characteristic zero if there is no torsion, to check that a finite family of roots form a
root system, we do not need to check that the coroots are stable under reflections since this
follows from the corresponding property for the roots. -/
def mk' [CharZero R] [NoZeroSMulDivisors R M]
    (p : PerfectPairing R M N)
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p.toLin (root i) (coroot i) = 2)
    (hs : ∀ i, MapsTo (preReflection (root i) (p.toLin.flip (coroot i))) (range root) (range root))
    (hsp : span R (range root) = ⊤) :
    RootSystem ι R M N where
  span_eq_top := hsp
  toRootPairing := RootPairing.mk' p root coroot hp hs <| by
    rintro i - ⟨j, rfl⟩
    use RootPairing.equiv_of_mapsTo p root coroot i hs hp j
    refine (coroot_eq_coreflection_of_root_eq_of_span_eq_top p root coroot hp hs hsp ?_)
    rw [equiv_of_mapsTo_apply, (exist_eq_reflection_of_mapsTo  p root coroot i j hs).choose_spec]

end RootSystem
