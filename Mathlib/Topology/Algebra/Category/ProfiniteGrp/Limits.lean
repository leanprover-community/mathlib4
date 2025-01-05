/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Youle Fang, Jujian Zhang, Yuyang Zhao
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# A profinite group is the projective limit of finite groups

We give the topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups.

## Main definitions

* `QuotientOpenNormalSubgroup` : The functor that maps open normal subgroup of a profinite group
  `P` to the quotient group of it (which is finite, as shown by previous lemmas).

* `toLimitQuotientOpenNormalSubgroup` : The continuous homomorphism from a profinite group `P` to
  projective limit of its quotients by open normal subgroups ordered by inclusion.

* `ContinuousMulEquivLimitQuotientOpenNormalSubgroup` : The `toLimitQuotientOpenNormalSubgroup` is a
  `ContinuousMulEquiv`

## Main Statements

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained within it.

-/

universe u

open CategoryTheory Topology TopologicalGroup

namespace ProfiniteGrp

theorem exist_openNormalSubgroup_sub_open_nhd_of_one {G : Type*} [Group G] [TopologicalSpace G]
    [TopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {U : Set G}
    (UOpen : IsOpen U) (einU : 1 ∈ U) : ∃ H : OpenNormalSubgroup G, (H : Set G) ⊆ U := by
  rcases ((Filter.HasBasis.mem_iff' ((nhds_basis_clopen (1 : G))) U ).mp <|
    mem_nhds_iff.mpr (by use U)) with ⟨W, hW, h⟩
  rcases exist_openNormalSubgroup_sub_clopen_nhd_of_one hW.2 hW.1 with ⟨H, hH⟩
  exact ⟨H, fun _ a ↦ h (hH a)⟩

section

instance (P : ProfiniteGrp) : SmallCategory (OpenNormalSubgroup P) :=
  Preorder.smallCategory (OpenNormalSubgroup ↑P.toProfinite.toTop)

/-- The functor from `OpenNormalSubgroup P` to `FiniteGrp` sending `U` to `P ⧸ U`,
where `P : ProfiniteGrp`. -/
def QuotientOpenNormalSubgroup (P : ProfiniteGrp) :
    OpenNormalSubgroup P ⥤ FiniteGrp := {
    obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
    map := fun fHK => QuotientGroup.map _ _ (.id _) (leOfHom fHK)
    map_id _ := QuotientGroup.map_id _
    map_comp f g := (QuotientGroup.map_comp_map
      _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm }

/-- The continuous homomorphism from a profinite group `P` to the projective limit of
its quotients by open normal subgroups ordered by inclusion.-/
def toLimitQuotientOpenNormalSubgroup (P : ProfiniteGrp.{u}) : P ⟶
    limit ((QuotientOpenNormalSubgroup P) ⋙ (forget₂ FiniteGrp ProfiniteGrp)) where
  toFun p := ⟨fun H => QuotientGroup.mk p, fun _ => rfl⟩
  map_one' := Subtype.val_inj.mp rfl
  map_mul' x y := Subtype.val_inj.mp rfl
  continuous_toFun := continuous_induced_rng.mpr (continuous_pi fun H ↦ by
    dsimp
    apply Continuous.mk
    intro s _
    rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
    refine isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ?_))
    convert IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out i)
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
    exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem) )

theorem toLimitQuotientOpenNormalSubgroup_dense (P : ProfiniteGrp.{u}) : Dense <|
    Set.range (toLimitQuotientOpenNormalSubgroup P) :=
  dense_iff_inter_open.mpr fun U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩ => (by
    simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
    rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
    let M := iInf (fun (j : J) => j.1.1.1)
    have hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
    have hMOpen : IsOpen (M : Set P) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
    let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
    rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
    use (toLimitQuotientOpenNormalSubgroup P).toFun origin
    refine ⟨?_, origin, rfl⟩
    rw [← hsv]
    apply hJ2
    intro a a_in_J
    let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
    rw [← (P.toLimitQuotientOpenNormalSubgroup.toFun origin).property M_to_Na]
    show (P.QuotientOpenNormalSubgroup.map M_to_Na) (QuotientGroup.mk' M origin) ∈ _
    rw [horigin]
    exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2 )

theorem toLimitQuotientOpenNormalSubgroup_surjective (P : ProfiniteGrp.{u}) :
    Function.Surjective (toLimitQuotientOpenNormalSubgroup P) := by
  have : IsClosed (Set.range P.toLimitQuotientOpenNormalSubgroup) :=
    P.toLimitQuotientOpenNormalSubgroup.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr this,
    Dense.closure_eq <| toLimitQuotientOpenNormalSubgroup_dense P]

theorem toLimitQuotientOpenNormalSubgroup_injective (P : ProfiniteGrp.{u}) :
    Function.Injective (toLimitQuotientOpenNormalSubgroup P) := by
  show Function.Injective (toLimitQuotientOpenNormalSubgroup P).toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  rcases exist_openNormalSubgroup_sub_open_nhd_of_one (isOpen_compl_singleton)
    (Set.mem_compl_singleton_iff.mpr fun a => xne1 a.symm) with ⟨H, hH⟩
  exact hH ((QuotientGroup.eq_one_iff x).mp (congrFun (Subtype.val_inj.mpr h) H)) rfl

/-- The topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups -/
noncomputable def ContinuousMulEquivLimitQuotientOpenNormalSubgroup (P : ProfiniteGrp.{u}) :
    P ≃ₜ* (limit ((QuotientOpenNormalSubgroup P) ⋙ (forget₂ FiniteGrp ProfiniteGrp))) := {
  (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _
  ⟨toLimitQuotientOpenNormalSubgroup_injective P, toLimitQuotientOpenNormalSubgroup_surjective P⟩)
    P.toLimitQuotientOpenNormalSubgroup.continuous_toFun)
  with
  map_mul' := (toLimitQuotientOpenNormalSubgroup P).map_mul' }

end

end ProfiniteGrp
