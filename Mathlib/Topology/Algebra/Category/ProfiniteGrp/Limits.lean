/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Youle Fang, Jujian Zhang, Yuyang Zhao
-/
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# A profinite group is the projective limit of finite groups

We define the topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups.

## Main definitions

* `toFiniteQuotientFunctor` : The functor from `OpenNormalSubgroup P` to `FiniteGrp`
  sending an open normal subgroup `U` to `P ⧸ U`, where `P : ProfiniteGrp`.

* `toLimit` : The continuous homomorphism from a profinite group `P` to
  the projective limit of its quotients by open normal subgroups ordered by inclusion.

* `ContinuousMulEquivLimittoFiniteQuotientFunctor` : The `toLimit` is a
  `ContinuousMulEquiv`

## Main Statements

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained in it.

-/

universe u

open CategoryTheory IsTopologicalGroup

namespace ProfiniteGrp

instance (P : ProfiniteGrp) : SmallCategory (OpenNormalSubgroup P) :=
  Preorder.smallCategory (OpenNormalSubgroup ↑P.toProfinite.toTop)

/-- The functor from `OpenNormalSubgroup P` to `FiniteGrp` sending `U` to `P ⧸ U`,
where `P : ProfiniteGrp`. -/
def toFiniteQuotientFunctor (P : ProfiniteGrp) : OpenNormalSubgroup P ⥤ FiniteGrp where
  obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
  map := fun fHK => FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom fHK))
  map_id _ := ConcreteCategory.ext <| QuotientGroup.map_id _
  map_comp f g := ConcreteCategory.ext <| (QuotientGroup.map_comp_map
    _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm

/-- The `MonoidHom` from a profinite group `P` to the projective limit of its quotients by
open normal subgroups ordered by inclusion -/
def toLimit_fun (P : ProfiniteGrp.{u}) : P →*
    limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  toFun p := ⟨fun _ => QuotientGroup.mk p, fun _ ↦ fun _ _ ↦ rfl⟩
  map_one' := Subtype.val_inj.mp rfl
  map_mul' _ _ := Subtype.val_inj.mp rfl

lemma toLimit_fun_continuous (P : ProfiniteGrp.{u}) : Continuous (toLimit_fun P) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  dsimp only [Functor.comp_obj, CompHausLike.coe_of, Functor.comp_map,
    CompHausLike.toCompHausLike_map, CompHausLike.compHausLikeToTop_map, Set.mem_setOf_eq,
    toLimit_fun, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  apply Continuous.mk
  intro s _
  rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
  refine isOpen_iUnion (fun i ↦ isOpen_iUnion (fun _ ↦ ?_))
  convert IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem)

/-- The morphism in the category of `ProfiniteGrp` from a profinite group `P` to
the projective limit of its quotients by open normal subgroups ordered by inclusion -/
def toLimit (P : ProfiniteGrp.{u}) : P ⟶
    limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp) :=
  ofHom { toLimit_fun P with
  continuous_toFun := toLimit_fun_continuous P }

/-- An auxiliary result, superseded by `toLimit_surjective` -/
theorem denseRange_toLimit (P : ProfiniteGrp.{u}) : DenseRange (toLimit P) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M := iInf (fun (j : J) => j.1.1.1)
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen : IsOpen (M : Set P) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
  let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use (toLimit P) origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
  rw [← (P.toLimit origin).property M_to_Na]
  show (P.toFiniteQuotientFunctor.map M_to_Na) (QuotientGroup.mk' M origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

theorem toLimit_surjective (P : ProfiniteGrp.{u}) : Function.Surjective (toLimit P) := by
  have : IsClosed (Set.range P.toLimit) :=
    P.toLimit.hom.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr this,
    Dense.closure_eq (denseRange_toLimit P)]

theorem toLimit_injective (P : ProfiniteGrp.{u}) : Function.Injective (toLimit P) := by
  show Function.Injective (toLimit P).hom.toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  rcases exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton)
    (Set.mem_compl_singleton_iff.mpr fun a => xne1 a.symm) with ⟨H, hH⟩
  exact hH ((QuotientGroup.eq_one_iff x).mp (congrFun (Subtype.val_inj.mpr h) H)) rfl

/-- The topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups -/
noncomputable def continuousMulEquivLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≃ₜ* (limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)) := {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨toLimit_injective P, toLimit_surjective P⟩)
    P.toLimit.hom.continuous_toFun) with
  map_mul' := (toLimit P).hom.map_mul' }

instance isIso_toLimit (P : ProfiniteGrp.{u}) : IsIso (toLimit P) := by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact ⟨toLimit_injective P, toLimit_surjective P⟩

/-- The isomorphism in the category of profinite group between a profinite group and
the projective limit of its quotients by open normal subgroups -/
noncomputable def isoLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≅ (limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivLimittoFiniteQuotientFunctor P)

end ProfiniteGrp
