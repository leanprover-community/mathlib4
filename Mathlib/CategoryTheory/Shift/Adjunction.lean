/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Adjoints commute with shifts

Given categories `C` and `D` that have shifts by an additive group `A`, functors `F : C ⥤ D`
and `G : C ⥤ D`, an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this file constructs
a `CommShift` structure on `G`. As an easy application, if `E : C ≌ D` is an equivalence and
`E.functor` has a `CommShift` structure, we get a `CommShift` structure on `E.inverse`.

The `CommShift` structure on `G` must be compatible with the one on `F` in the following sense
(cf. `Adjunction.CommShift`):
for every `a` in `A`, the natural transformation `adj.unit : 𝟭 C ⟶ G ⋙ F` commutes with
the isomorphism `shiftFunctor C A ⋙ G ⋙ F ≅ G ⋙ F ⋙ shiftFunctor C A` induces by
`F.commShiftIso a` and `G.commShiftIso a`. We actually require a similar condition for
`adj.counit`, but it follows from the one for `adj.unit`.

In order to simplify the construction of the `CommShift` structure on `G`, we first introduce
the compatibility condition on `adj.unit` for a fixed `a` in `A` and for isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`. We then prove that:
- If `e₁` and `e₂` satusfy this condition, then `e₁` uniquely determines `e₂` and vice versa.
- If `a = 0`, the isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G`
satisfy the condition.
- The condition is stable by addition on `A`, if we use `Functor.CommShift.isoAdd` to deduce
commutation isomorphism for `a + b` from such isomorphism from `a` and `b`.
- Given commutation isomorphisms for `F`, our candidate commutation isomorphisms for `G`,
constructed in `Adjunction.RightAdjointCommShift.iso`, satisfy the compatibility condition.

Once we have established all this, the compatibility of the commutation isomorphism for
`F` expressed in `CommShift.zero` and `CommShift.add` immediately implies the similar
statements for the commutation isomorphisms for `G`.

TODO: Construct a `CommShift` structure on `F` from a `CommShift` structure on `G`, using
opposite categories.

-/

namespace CategoryTheory

open Category

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]

namespace CommShift

variable {a b : A} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (f₁ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (e₂' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (f₂ : shiftFunctor D b ⋙ G ≅ G ⋙ shiftFunctor C b)

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibility of
`e₁` and `e₂` with the unit of the adjunction `adj`.
-/
abbrev CompatibilityUnit :=
  ∀ (X : C), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app _

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibility of
`e₁` and `e₂` with the counit of the adjunction `adj`.
-/
abbrev CompatibilityCounit :=
  ∀ (Y : D), adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app _ ≫ (adj.counit.app Y)⟦a⟧'

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, compatibility of `e₁` and `e₂` with the
unit of the adjunction `adj` implies compatibility with the counit of `adj`.
-/
lemma compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂) :
    CompatibilityCounit adj e₁ e₂ := by
  intro Y
  have eq := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _))] at eq
  dsimp at eq ⊢
  conv_rhs at eq => slice 3 4; rw [Iso.hom_inv_id_app]
  conv_rhs at eq => erw [id_comp]; rw [← Functor.map_comp, Iso.hom_inv_id_app];
                    erw [Functor.map_id]; rw [comp_id]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp, adj.unit_naturality_assoc, ← eq]
  slice_rhs 4 5 => rw [← Functor.map_comp, ← assoc, Iso.inv_hom_id_app]; erw [id_comp]
  erw [← e₂.inv.naturality]; rw [← assoc _ _ (e₂.inv.app Y), Functor.comp_map, ← Functor.map_comp]
  simp only [Functor.id_obj, Functor.comp_obj, right_triangle_components, Functor.map_id, id_comp,
    Iso.hom_inv_id_app]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then we get a formula for `e₂.inv` in terms of `e₁`.
-/
lemma CompatibilityUnit_right (h : CompatibilityUnit adj e₁ e₂) (Y : D) :
    e₂.inv.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧') := by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc, ← this, assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.id_obj, Functor.comp_map, assoc, comp_id,
    ← (shiftFunctor C a).map_comp, right_triangle_components, Functor.map_id]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
counit of the adjunction `adj`, then we get a formula for `e₁.hom` in terms of `e₂`.
-/
lemma CompatibilityCounit_left (h : CompatibilityCounit adj e₁ e₂) (X : C) :
    e₁.hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app _ := by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _)), ← assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id,
    id_comp] at this
  rw [this]
  erw [e₁.hom.naturality_assoc]
  rw [Functor.comp_map, ← Functor.map_comp, left_triangle_components]
  simp only [Functor.comp_obj, Functor.id_obj, Functor.map_id, comp_id]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then `e₁` uniquely determines `e₂`.
-/
lemma CompatibilityUnit_unique_right (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁ e₂') : e₂ = e₂' := by
  rw [← Iso.symm_eq_iff]
  ext _
  rw [Iso.symm_hom, Iso.symm_hom, CompatibilityUnit_right adj e₁ e₂ h,
    CompatibilityUnit_right adj e₁ e₂' h']

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
counit of the adjunction `adj`, then `e₂` uniquely determines `e₁`.
-/
lemma CompatibilityCounit_unique_left (h : CompatibilityCounit adj e₁ e₂)
    (h' : CompatibilityCounit adj e₁' e₂) : e₁ = e₁' := by
  ext _
  rw [CompatibilityCounit_left adj e₁ e₂ h, CompatibilityCounit_left adj e₁' e₂ h']

/--
The isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G` are
compatible with the unit of an adjunction `F ⊣ G`.
-/
lemma CompatibilityUnit_isoZero : CompatibilityUnit adj (Functor.CommShift.isoZero F A)
    (Functor.CommShift.isoZero G A) := by
  intro _
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app, Functor.map_comp,
    assoc, unit_naturality_assoc]
  slice_rhs 3 4 => rw [← G.map_comp, Iso.inv_hom_id_app]
  rw [← cancel_mono ((shiftFunctorZero C A).hom.app _)]
  simp only [Functor.id_obj, NatTrans.naturality, Functor.id_map, Functor.map_id, id_comp, assoc,
    Iso.inv_hom_id_app, comp_id]

/-- Given an adjunction `adj : F ⊣ G`, `a, b` in `A` and commutation isomorphisms
between shifts by `a` (resp. `b`) and `F` and `G`, if these commutation isomorphisms are
compatible with the unit of `adj`, then so are the commutation isomorphisms between shifts
by `a + b` and `F` and `G` constructed by `Functor.CommShift.isoAdd`.
-/
lemma CompatibilityUnit_isoAdd (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj f₁ f₂) :
    CompatibilityUnit adj (Functor.CommShift.isoAdd e₁ f₁) (Functor.CommShift.isoAdd e₂ f₂) := by
  intro X
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app, Functor.map_comp,
    assoc, unit_naturality_assoc]
  slice_rhs 5 6 => rw [← G.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]
  slice_rhs 4 5 => erw [f₂.hom.naturality]
  have := h' (X⟦a⟧)
  rw [← cancel_mono (f₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  simp only [Functor.id_obj, Functor.comp_obj, comp_id] at this
  slice_rhs 2 3 => rw [← this]
  simp only [Functor.comp_obj, assoc, Iso.inv_hom_id_app, comp_id, Functor.comp_map]
  rw [← cancel_mono ((shiftFunctorAdd C a b).hom.app _), assoc, assoc, assoc, assoc,
    Iso.inv_hom_id_app]; erw [comp_id]
  rw [← (shiftFunctor C b).map_comp, ← (shiftFunctor C b).map_comp, ← h X]
  simp only [Functor.comp_obj, NatTrans.naturality, Functor.comp_map, Functor.id_obj]

end CommShift

variable (A) [F.CommShift A] [G.CommShift A]

/--
The property for `CommShift` structures on `F` and `G` to be compatible with an
adjunction `F ⊣ G`.
-/
class CommShift : Prop where
  commShift_unit : NatTrans.CommShift adj.unit A := by infer_instance
  commShift_counit : NatTrans.CommShift adj.counit A := by infer_instance

namespace CommShift

attribute [instance] commShift_unit commShift_counit

/-- Constructor for `Adjunction.CommShift`. -/
lemma mk' (h : NatTrans.CommShift adj.unit A) :
    adj.CommShift A where
  commShift_counit := ⟨by
    intro a
    ext _
    simp [Functor.commShiftIso_comp_hom_app]
    refine (compatibilityCounit_of_compatibilityUnit adj (F.commShiftIso a) (G.commShiftIso a)
      (fun X ↦ ?_) _).symm
    have := h.comm' a
    apply_fun (fun x ↦ x.app X) at this
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.commShiftIso_id_hom_app, whiskerRight_app, id_comp, whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app] at this
    exact this
  ⟩

end CommShift

variable {A}

@[reassoc]
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
        G.map ((F.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (F.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.CommShift.comm_app adj.unit a X

@[reassoc]
lemma shift_counit_app [adj.CommShift A] (a : A) (Y : D) :
    (adj.counit.app Y)⟦a⟧' =
      (F.commShiftIso a).inv.app (G.obj Y) ≫ F.map ((G.commShiftIso a).inv.app Y) ≫
        adj.counit.app (Y⟦a⟧) := by
  have eq := NatTrans.CommShift.comm_app adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.commShiftIso_id_hom_app, comp_id] at eq
  rw [← eq, ← assoc (F.map ((G.commShiftIso a).inv.app _)), ← F.map_comp, Iso.inv_hom_id_app,
    F.map_id, id_comp, Iso.inv_hom_id_app_assoc]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]

namespace RightAdjointCommShift

variable (a b : A) (h : b + a = 0) [F.CommShift A]

/-- Auxiliary definition for `iso`. -/
noncomputable def iso' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D b a h).toAdjunction)
  (Adjunction.comp (shiftEquiv' C b a h).toAdjunction adj)).toFun (F.commShiftIso b)

/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, these are the candidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `G`.
-/
noncomputable def iso : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  iso' adj _ _ (neg_add_cancel a)

lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (G.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (G.map ((F.commShiftIso b).hom.app (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (G.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (G.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [Functor.comp_obj, iso, iso', shiftEquiv'_functor, shiftEquiv'_inverse,
    Equiv.toFun_as_coe, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app, comp_unit_app,
    Functor.id_obj, Equivalence.toAdjunction_unit, Functor.comp_map, comp_counit_app,
    Equivalence.toAdjunction_counit, Functor.map_comp, assoc]
  rfl

lemma iso_inv_app (Y : D) :
    (iso adj a).inv.app Y =
      adj.unit.app ((shiftFunctor C a).obj (G.obj Y)) ≫
          G.map ((shiftFunctorCompIsoId D b a h).inv.app
              (F.obj ((shiftFunctor C a).obj (G.obj Y)))) ≫
            G.map ((shiftFunctor D a).map ((shiftFunctor D b).map
                ((F.commShiftIso a).hom.app (G.obj Y)))) ≫
              G.map ((shiftFunctor D a).map ((shiftFunctorCompIsoId D a b
                  (by rw [eq_neg_of_add_eq_zero_left h, add_neg_cancel])).hom.app
                    (F.obj (G.obj Y)))) ≫
                G.map ((shiftFunctor D a).map (adj.counit.app Y)) := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [Functor.comp_obj, iso, iso', shiftEquiv', Equiv.toFun_as_coe,
    conjugateIsoEquiv_apply_inv, conjugateEquiv_apply_app, comp_unit_app, Functor.id_obj,
    Equivalence.toAdjunction_unit, Equivalence.Equivalence_mk'_unit, Iso.symm_hom, Functor.comp_map,
    comp_counit_app, Equivalence.toAdjunction_counit, Equivalence.Equivalence_mk'_counit,
    Functor.map_shiftFunctorCompIsoId_hom_app, assoc, Functor.map_comp]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]

/--
The commutation isomorphisms of `Adjunction.RightAdjointCommShift.iso` are compatible with
the unit of the adjunction.
-/
lemma iso_CompatibilityUnit (a : A) : CommShift.CompatibilityUnit adj (F.commShiftIso a)
    (iso adj a) := by
  intro _
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app _), assoc, assoc, Iso.hom_inv_id_app]
  dsimp
  rw [comp_id]
  simp only [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a), Functor.id_obj,
    Functor.comp_obj]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp only [homEquiv_counit, Functor.map_comp, assoc, counit_naturality, Functor.comp_obj,
    Functor.id_obj, counit_naturality_assoc, left_triangle_components_assoc]
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    left_triangle_components, Functor.map_id, comp_id]

end RightAdjointCommShift

variable (A)

/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this constructs
the unique compatible `CommShift` structure on `G`.
-/
@[simps]
noncomputable def rightAdjointCommShift [F.CommShift A] : G.CommShift A where
  iso a := RightAdjointCommShift.iso adj a
  zero := by
    refine CommShift.CompatibilityUnit_unique_right adj (F.commShiftIso 0)  _ _
      (RightAdjointCommShift.iso_CompatibilityUnit adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.CompatibilityUnit_isoZero adj
  add a b := by
    refine CommShift.CompatibilityUnit_unique_right adj (F.commShiftIso (a + b))  _ _
      (RightAdjointCommShift.iso_CompatibilityUnit adj (a + b)) ?_
    rw [F.commShiftIso_add]
    exact CommShift.CompatibilityUnit_isoAdd adj _ _ _ _
      (RightAdjointCommShift.iso_CompatibilityUnit adj a)
      (RightAdjointCommShift.iso_CompatibilityUnit adj b)

lemma commShift_of_leftAdjoint [F.CommShift A] :
    letI := adj.rightAdjointCommShift A
    adj.CommShift A := by
  letI := adj.rightAdjointCommShift A
  apply CommShift.mk'
  refine ⟨fun a => ?_⟩
  ext X
  dsimp
  simp only [Functor.commShiftIso_id_hom_app, Functor.comp_obj,
    Functor.id_obj, id_comp, Functor.commShiftIso_comp_hom_app]
  exact RightAdjointCommShift.iso_CompatibilityUnit adj a X

end Adjunction

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] (E : C ≌ D)

section

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence, this expresses the compatibility of `CommShift`
structures on `E.functor` and `E.inverse`.
-/
abbrev CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop :=
  E.toAdjunction.CommShift A

namespace CommShift

variable [E.functor.CommShift A] [E.inverse.CommShift A]

instance [E.CommShift A] : NatTrans.CommShift E.unitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.unit A)

instance [E.CommShift A]: NatTrans.CommShift E.counitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.counit A)

instance [h : E.functor.CommShift A] : E.symm.inverse.CommShift A := h
instance [h : E.inverse.CommShift A] : E.symm.functor.CommShift A := h

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk' (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_unit := h
  commShift_counit := (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk'' (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A where
  commShift_unit := by
    have h' := NatTrans.CommShift.of_iso_inv E.counitIso A
    have : NatTrans.CommShift E.unitIso.symm.hom A :=
      (Adjunction.CommShift.mk' E.symm.toAdjunction A h').commShift_counit
    exact NatTrans.CommShift.of_iso_inv E.unitIso.symm A
  commShift_counit := h

/--
If `E : C ≌ D` is an equivalence and we have compatible `CommShift` structures on `E.functor`
and `E.inverse`, then we also have compatible `CommShift` structures on `E.symm.functor`
and `E.symm.inverse`.
-/
instance [E.functor.CommShift A] [E.inverse.CommShift A] [E.CommShift A] :
    E.symm.CommShift A := mk' _ _
      (by dsimp only [Equivalence.symm, Iso.symm]; exact NatTrans.CommShift.of_iso_inv _ _)

end CommShift

end

variable (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.functor`,
this constructs the unique compatible `CommShift` structure on `E.inverse`.
-/
noncomputable def commShiftInverse [E.functor.CommShift A] : E.inverse.CommShift A :=
  E.toAdjunction.rightAdjointCommShift A

lemma commShift_of_functor [E.functor.CommShift A] :
    letI := E.commShiftInverse A
    E.CommShift A := by
  letI := E.commShiftInverse A
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint A).commShift_unit

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.inverse`,
this constructs the unique compatible `CommShift` structure on `E.functor`.
-/
noncomputable def commShiftFunctor [E.inverse.CommShift A] : E.functor.CommShift A :=
  E.symm.toAdjunction.rightAdjointCommShift A

lemma commShift_of_inverse [E.inverse.CommShift A] :
    letI := E.commShiftFunctor A
    E.CommShift A := by
  letI := E.commShiftFunctor A
  apply CommShift.mk''
  have : NatTrans.CommShift E.counitIso.symm.hom A :=
    (E.symm.toAdjunction.commShift_of_leftAdjoint A).commShift_unit
  exact NatTrans.CommShift.of_iso_inv E.counitIso.symm A

end Equivalence

end CategoryTheory
