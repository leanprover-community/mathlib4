/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant

/-!
# Composition of rational maps

This file defines composition for partial maps and rational maps between schemes.

## Main definitions

- `Scheme.PartialMap.comp`: given a dominant partial map `f : X.PartialMap Y` and any partial map
  `g : Y.PartialMap Z`, their composition `f.comp g : X.PartialMap Z` is defined on the preimage
  of `g`'s domain under `f`.
- `Scheme.RationalMap.comp`: composition of rational maps, defined via a dominant representative.

## Main statements

- `Scheme.PartialMap.comp_equiv_of_equiv`: Composition respects equivalence of partial maps.
- `Scheme.PartialMap.comp_assoc`: Composition of partial maps is associative.
- `Scheme.RationalMap.comp_assoc`: Composition of rational maps is associative.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

section PreirreducibleSpace

variable [PreirreducibleSpace X] [Nonempty Y]

namespace PartialMap

/-- Composition of partial maps. The domain of `f.comp g` is the preimage of `g.domain` under `f`,
viewed as an open subscheme of `X`. Requires `f.hom` to be dominant so that the domain is dense. -/
@[simps]
noncomputable def comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    X.PartialMap Z where
  domain := f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
  dense_domain := (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).2.dense <| by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
  hom := (f.domain.ι.isoImage _).inv ≫ (f.hom ∣_ g.domain) ≫ g.hom

lemma comp_restrict_left (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) (g : Y.PartialMap Z) :
    (f.restrict U hU hU').comp g = (f.comp g).restrict (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ⊓ U)
      ((f.comp g).dense_domain.inter_of_isOpen_right hU U.2) inf_le_left := by
  ext1
  · simp only [comp_domain, restrict_domain, restrict_hom, Hom.comp_preimage,
      ι_image_homOfLE_eq_ι_image_inf]
  · simp only [comp_hom, comp_domain, restrict_hom, restrict_domain, Hom.comp_preimage,
      morphismRestrict_comp, Category.assoc, isoOfEq_hom, homOfLE_homOfLE_assoc,
      ι_isoImage_inv_morphismRestrict_homOfLE_assoc]

lemma comp_restrict_right (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (V : Y.Opens) (hV : Dense (V : Set Y)) (hV' : V ≤ g.domain) :
    f.comp (g.restrict V hV hV') = (f.comp g).restrict
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ((f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V).2.dense <| by
        simpa [← Set.nonempty_preimage_iff] using
          f.hom.denseRange.inter_open_nonempty _ V.2 hV.nonempty)
      (f.domain.ι.image_mono (f.hom.preimage_mono hV')) := by
  ext1
  · rfl
  · simp only [comp_domain, restrict_domain, comp_hom, restrict_hom, isoOfEq_rfl, Iso.refl_hom,
      Category.id_comp, ← f.domain.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV'),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV']

/-- Composition respects equivalence of partial maps on the left. -/
lemma comp_equiv_of_equiv_left {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom]
    (h : f₁.equiv f₂) (g : Y.PartialMap Z) :
    (f₁.comp g).equiv (f₂.comp g) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : f₁.restrict W hW hW₁ = f₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr($(e).comp g)
  rw [comp_restrict_left, comp_restrict_left] at e
  exact equiv_of_restrict_eq _ _ e

/-- Composition respects equivalence of partial maps on the right. -/
lemma comp_equiv_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ : Y.PartialMap Z}
    (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr(f.comp $e)
  rw [comp_restrict_right, comp_restrict_right] at e
  exact equiv_of_restrict_eq _ _ e

/-- Composition respects equivalence of partial maps in both arguments. -/
lemma comp_equiv_of_equiv (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (hf : f₁.equiv f₂) (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.comp g₁).equiv (f₂.comp g₂) :=
  equivalence_rel.trans (comp_equiv_of_equiv_left hf _) (comp_equiv_of_equiv_right _ hg)

instance isDominant_comp_hom (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    [IsDominant g.hom] : IsDominant (f.comp g).hom := by
  dsimp only [comp_domain, comp_hom]
  have := IsZariskiLocalAtTarget.restrict ‹IsDominant f.hom› g.domain
  infer_instance

lemma comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
    [Nonempty X₃] (f : X₁.PartialMap X₂) [IsDominant f.hom] (g : X₂.PartialMap X₃)
    [IsDominant g.hom] (h : X₃.PartialMap Y) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext1
  · simp_rw [comp_domain, comp_hom, ← Category.assoc, Hom.comp_preimage, Hom.inv_preimage,
      ← Hom.comp_image, Hom.isoImage_hom_ι, Hom.comp_image, image_morphismRestrict_preimage]
  · simp_rw [comp_hom, comp_domain, morphismRestrict_comp,
      morphismRestrict_ι_image_ι_isoImage_inv_assoc, isoOfEq_hom, comp_hom, Hom.comp_preimage,
      Category.assoc]
    conv_lhs => rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    simp [← cancel_mono (Opens.ι _)]

lemma comp_toPartialMap (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) :
    f.comp g.toPartialMap = f.compHom g := by
  ext1
  · simp
  · simp_rw [comp_hom, Hom.toPartialMap_domain, Hom.toPartialMap_hom, compHom_hom, topIso_hom,
      morphismRestrict_ι_assoc, f.domain.ι_isoImage_inv_ι_assoc, isoOfEq_hom]
    rfl

@[simp]
lemma comp_id (f : X.PartialMap Y) [IsDominant f.hom] :
    f.comp (PartialMap.id Y) = f := by
  rw [comp_toPartialMap, compHom_id]

end PartialMap

namespace RationalMap

/-- Composition of rational maps. Requires `f` to be dominant, so that we may choose
a dominant representative. -/
noncomputable def comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) : X ⤏ Z :=
  Quotient.liftOn g (PartialMap.toRationalMap ∘ f.dominantRep.comp) <| fun _ _ h ↦ by
    rw [Function.comp_apply, Function.comp_apply, PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ h

lemma comp_def (f : X ⤏ Y) [f.IsDominant] (g : Y.PartialMap Z) :
    f.comp g.toRationalMap = (f.dominantRep.comp g).toRationalMap :=
  rfl

lemma toRationalMap_comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    f.toRationalMap.comp g.toRationalMap = (f.comp g).toRationalMap := by
  rw [RationalMap.comp_def, PartialMap.toRationalMap_eq_iff]
  exact PartialMap.comp_equiv_of_equiv_left f.toRationalMap_dominantRep_equiv _

@[simp]
lemma comp_id (f : X ⤏ Y) [f.IsDominant] : f.comp (RationalMap.id Y) = f := by
  simp [RationalMap.comp_def]

instance (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) [g.IsDominant] : (f.comp g).IsDominant := by
  rw [← g.toRationalMap_dominantRep, RationalMap.comp_def]
  haveI := f.dominantRep.isDominant_comp_hom g.dominantRep
  apply PartialMap.isDominant_toRationalMap

lemma comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
    [Nonempty X₃] (f₁ : X₁ ⤏ X₂) [f₁.IsDominant] (f₂ : X₂ ⤏ X₃) [f₂.IsDominant] (f₃ : X₃ ⤏ Y) :
    (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃) := by
  obtain ⟨f₃', rfl⟩ := f₃.exists_rep
  obtain ⟨f₂', rfl⟩ := f₂.exists_rep
  simp_rw [comp_def, ← PartialMap.comp_assoc, PartialMap.toRationalMap_eq_iff]
  apply PartialMap.comp_equiv_of_equiv_left
  have := f₂'.isDominant_hom_of_isDominant_toRationalMap
  apply (f₁.dominantRep.comp f₂').toRationalMap_dominantRep_equiv.trans
  apply PartialMap.comp_equiv_of_equiv_right
  exact f₂'.toRationalMap_dominantRep_equiv.symm

end RationalMap

end PreirreducibleSpace

@[simp]
lemma PartialMap.id_comp {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X.PartialMap Y) :
    (PartialMap.id X).comp f = f := by
  ext1
  · simp_rw [comp_domain, Hom.toPartialMap_domain, Hom.toPartialMap_hom, Category.comp_id,
      ← X.topIso_hom, ← Hom.inv_image, ← Hom.comp_image, Iso.inv_hom_id, Hom.id_image]
  · simp_rw [comp_hom, Hom.toPartialMap_hom, Hom.toPartialMap_domain, morphismRestrict_comp,
      morphismRestrict_id, ← X.topIso_hom, Hom.comp_preimage, Hom.id_preimage,
      Category.comp_id, morphismRestrict_eq_isoImage_hom_homOfLE, Category.assoc,
      Iso.inv_hom_id_assoc]
    rfl

@[simp]
lemma RationalMap.id_comp {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⤏ Y) [f.IsDominant] :
    (RationalMap.id X).comp f = f := by
  rw [← f.toRationalMap_dominantRep, toRationalMap_comp, PartialMap.id_comp]

end AlgebraicGeometry.Scheme
