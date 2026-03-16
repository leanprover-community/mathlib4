/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Schemes over algebraically closed fields

We show that if `X` is locally of finite type over an algebraically closed field `k`,
then the closed points of `X` are in bijection with the `k`-points of `X`.
See `AlgebraicGeometry.pointEquivClosedPoint`.

-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x})

set_option backward.isDefEq.respectTransparency false in
/-- If `X` is a locally of finite type `k`-scheme and `k` is algebraically closed, then
the residue field of any closed point of `x` is isomorphic to `k`. -/
def residueFieldIsoBase : X.residueField x ≅ .of K :=
  letI : IsIso (Spec.preimage (X.fromSpecResidueField x ≫ f)) := by
    have : IsFinite (X.fromSpecResidueField x ≫ f) := by
      rw [isClosed_singleton_iff_isClosedImmersion] at hx
      rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
      infer_instance
    rw [ConcreteCategory.isIso_iff_bijective]
    refine IsAlgClosed.ringHom_bijective_of_isIntegral _ ?_
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  (asIso (Spec.preimage (X.fromSpecResidueField x ≫ f))).symm

@[simp, reassoc]
lemma SpecMap_residueFieldIsoBase_inv :
    Spec.map (residueFieldIsoBase f x hx).inv = X.fromSpecResidueField x ≫ f :=
  Spec.map_preimage _

/-- If `k` is algebraically closed, this is the `k`-point of `X` associated to a closed point. -/
noncomputable
def pointOfClosedPoint : Spec (.of K) ⟶ X :=
  Spec.map (residueFieldIsoBase f x hx).hom ≫ X.fromSpecResidueField x

@[reassoc (attr := simp)]
lemma pointOfClosedPoint_comp : pointOfClosedPoint f x hx ≫ f = 𝟙 _ := by
  simp [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv, ← Spec.map_comp]

@[simp]
lemma pointOfClosedPoint_apply (a : _) : pointOfClosedPoint f x hx a = x := by
  simp [pointOfClosedPoint]

/-- If `k` is algebraically closed,
then the closed points of `X` are in bijection with the `k`-points of `X`. -/
@[simps]
def pointEquivClosedPoint :
    {p : Spec (.of K) ⟶ X // p ≫ f = 𝟙 _} ≃ closedPoints X where
  toFun p := ⟨p.1 (IsLocalRing.closedPoint K), by
    have := isClosedImmersion_of_comp_eq_id _ _ p.2
    have := p.1.isClosedEmbedding.isClosed_range
    rwa [Set.range_eq_singleton] at this
    exact fun x ↦ congr(p.1 $(Subsingleton.elim _ _))⟩
  invFun x := ⟨pointOfClosedPoint f x.1 x.2, pointOfClosedPoint_comp f x.1 x.2⟩
  left_inv p := by
    ext
    refine ((Scheme.SpecToEquivOfField _ _).symm_apply_eq (x := ⟨_, _⟩)).mpr ?_
    rw [Scheme.SpecToEquivOfField_eq_iff]
    dsimp [Scheme.SpecToEquivOfField]
    simp only [Category.id_comp, exists_const]
    generalize_proofs _ h
    refine (Category.comp_id _).symm.trans (((residueFieldIsoBase f _ h).eq_inv_comp).mp ?_)
    rw [← Spec.map_injective.eq_iff]
    simp only [Spec.map_id, Spec.map_comp, SpecMap_residueFieldIsoBase_inv]
    rw [reassoc_of% Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, p.2]
  right_inv x := by simp

lemma ext_of_apply_closedPoint_eq
    {f g : Spec (.of K) ⟶ X} (h : X ⟶ Spec (.of K))
    [LocallyOfFiniteType h]
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (H : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g :=
  congr($((pointEquivClosedPoint h).injective (a₁ := ⟨f, hf⟩) (a₂ := ⟨g, hg⟩) (Subtype.ext H)).1)

/-- Let `X` and `Y` be locally of finite type `K`-schemes with `K` algebraically closed and `Y`
separated over `K`. Suppose `X` is reduced, then two `K`-morphisms `f g : X ⟶ Y` are equal if
they are equal on the closed points of a dense locally closed subset of `X`. -/
lemma ext_of_apply_eq {f g : X ⟶ Y} (i : Y ⟶ Spec (.of K)) [IsSeparated i] [LocallyOfFiniteType i]
    [IsReduced X] [LocallyOfFiniteType (f ≫ i)]
    (S : Set X) (hS : IsLocallyClosed S) (hS' : Dense S)
    (H : ∀ x ∈ S, IsClosed {x} → f x = g x)
    (H' : f ≫ i = g ≫ i) : f = g := by
  have : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace (f ≫ i)
  refine ext_of_fromSpecResidueField_eq f g i (S ∩ closedPoints X) ?_ ?_ H'
  · rwa [dense_iff_closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure hS,
      ← dense_iff_closure_eq]
  · intro x ⟨hxS, hx⟩
    rw [← cancel_epi (Spec.map (residueFieldIsoBase (f ≫ i) x hx).hom)]
    refine ext_of_apply_closedPoint_eq i ?_ ?_ (by simpa using H x hxS hx) <;>
      simp only [Category.assoc, ← SpecMap_residueFieldIsoBase_inv (f ≫ i) x hx, ← Spec.map_comp,
        Iso.inv_hom_id, Spec.map_id, ← H']

end AlgebraicGeometry
