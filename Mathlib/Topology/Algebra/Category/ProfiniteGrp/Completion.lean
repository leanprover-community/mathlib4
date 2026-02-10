/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Profinite completion of groups

We define the profinite completion of a group as the limit of its finite quotients,
and prove its universal property.
-/

@[expose] public section

namespace OpenNormalSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open normal subgroup of a compact topological group has finite index. -/
@[to_additive
  /-- An open normal additive subgroup of a compact topological additive group has finite index. -/]
def toFiniteIndexNormalSubgroup [CompactSpace G] [ContinuousMul G]
    (H : OpenNormalSubgroup G) : FiniteIndexNormalSubgroup G :=
  letI : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  FiniteIndexNormalSubgroup.ofSubgroup H.toSubgroup

@[to_additive]
theorem toFiniteIndexNormalSubgroup_mono [CompactSpace G] [ContinuousMul G]
    {H K : OpenNormalSubgroup G} (h : H ≤ K) :
    H.toFiniteIndexNormalSubgroup ≤ K.toFiniteIndexNormalSubgroup :=
  fun _ hx ↦ h hx

@[to_additive]
theorem toFiniteIndexNormalSubgroup_injective [CompactSpace G] [ContinuousMul G] :
    Function.Injective (toFiniteIndexNormalSubgroup (G := G)) := by
  intro H K h
  apply toSubgroup_injective
  exact congrArg (fun L : FiniteIndexNormalSubgroup G ↦ (L : Subgroup G)) h

end OpenNormalSubgroup

namespace ProfiniteGrp

open CategoryTheory

universe u

namespace ProfiniteCompletion

variable (G : GrpCat.{u})

/-- The diagram of finite quotients indexed by finite-index normal subgroups of `G`. -/
def finiteGrpDiagram : FiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u} where
  obj H := FiniteGrp.of <| G ⧸ H.toSubgroup
  map f := FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- The finite-quotient diagram viewed in `ProfiniteGrp`. -/
def diagram : FiniteIndexNormalSubgroup G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram _ ⋙ forget₂ _ _

/-- The profinite completion of `G` as a projective limit. -/
def completion : ProfiniteGrp.{u} := limit (diagram G)

/-- The canonical map from `G` to its profinite completion, as a function. -/
def etaFn (x : G) : completion G := ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

/-- The canonical morphism from `G` to its profinite completion. -/
def eta : G ⟶ GrpCat.of (completion G) := GrpCat.ofHom {
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
}

lemma denseRange : DenseRange (etaFn G) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => j.val
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : FiniteIndexNormalSubgroup G := { toSubgroup := M }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => (j.val.toSubgroup)) ⟨a, a_in_J⟩).hom
  rw [← (etaFn G origin).property M_to_Na]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).right

variable {G}
variable {P : ProfiniteGrp.{u}}

/-- The preimage of an open normal subgroup under a morphism to a profinite group. -/
def preimage (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) : FiniteIndexNormalSubgroup G :=
  H.toFiniteIndexNormalSubgroup.comap f.hom

lemma preimage_le {f : G ⟶ GrpCat.of P} {H K : OpenNormalSubgroup P}
    (h : H ≤ K) : preimage f H ≤ preimage f K :=
  FiniteIndexNormalSubgroup.comap_mono _ h

/-- The induced map on finite quotients coming from a morphism to `P`. -/
def quotientMap (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (G ⧸ (preimage f H).toSubgroup) ⟶ FiniteGrp.of (P ⧸ H.toSubgroup) :=
  FiniteGrp.ofHom <| QuotientGroup.map _ _ f.hom <| fun _ h => h

/-- The universal morphism from the profinite completion to `P`. -/
noncomputable
def lift (f : G ⟶ GrpCat.of P) : completion G ⟶ P :=
  P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram G)).π.app _ ≫ (ofFiniteGrpHom <| quotientMap f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      -- TODO: `dsimp` should handle this `change`; investigate missing simp lemmas in the
      -- `ProfiniteGrp` / `CompHausLike` API.
      change quotientMap f Y (x <| preimage f Y) =
        P.diagram.map g (quotientMap _ _ <| x <| preimage f X)
      have := hx <| preimage_le (f := f) g.le |>.hom
      obtain ⟨t, ht⟩ : ∃ g : G, QuotientGroup.mk g = x (preimage f X) :=
        QuotientGroup.mk_surjective (x (preimage f X))
      rw [← this, ← ht]
      have := P.cone.π.naturality g
      apply_fun fun q => q (f t) at this
      exact this
  }⟩

@[reassoc (attr := simp)]
lemma lift_eta (f : G ⟶ GrpCat.of P) : eta G ≫ (forget₂ _ _).map (lift f) = f := by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← (forget₂ ProfiniteGrp GrpCat).mapIso e |>.cancel_iso_hom_right]
  dsimp
  rw [Category.assoc, ← (forget₂ ProfiniteGrp GrpCat).map_comp (lift f) e.hom]
  change eta G ≫ ((forget₂ _ _).map ((_ ≫ e.inv) ≫ e.hom)) = _
  simp only [Category.assoc, Iso.inv_hom_id]
  rfl

lemma lift_unique (f g : completion G ⟶ P)
    (h : eta G ≫ (forget₂ _ _).map f = eta G ≫ (forget₂ _ _).map g) : f = g := by
  ext x
  apply congrFun
  refine (denseRange (G := G)).equalizer f.hom.continuous_toFun g.hom.continuous_toFun ?_
  funext y
  simpa [GrpCat.comp_apply] using (ConcreteCategory.congr_hom h y)

end ProfiniteCompletion

/-- The profinite completion functor. -/
@[simps]
noncomputable def profiniteCompletion : GrpCat.{u} ⥤ ProfiniteGrp.{u} where
  obj G := ProfiniteCompletion.completion G
  map f := ProfiniteCompletion.lift <| f ≫ ProfiniteCompletion.eta _
  map_id G := by
    apply ProfiniteCompletion.lift_unique
    cat_disch
  map_comp f g := by
    apply ProfiniteCompletion.lift_unique
    cat_disch

namespace ProfiniteCompletion

/-- The hom-set equivalence exhibiting the adjunction. -/
noncomputable
def homEquiv (G : GrpCat.{u}) (P : ProfiniteGrp.{u}) :
    (completion G ⟶ P) ≃ (G ⟶ GrpCat.of P) where
  toFun f := eta G ≫ (forget₂ _ _).map f
  invFun f := lift f
  left_inv f := by apply lift_unique; simp
  right_inv f := by simp

/-- The profinite completion is left adjoint to the forgetful functor. -/
noncomputable
def adjunction : profiniteCompletion ⊣ forget₂ _ _ :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by
      apply lift_unique
      simp [homEquiv]
  }

end ProfiniteCompletion

end ProfiniteGrp
