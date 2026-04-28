/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Tactic.CategoryTheory.CancelIso

/-!
# Adjoints commute with shifts

Given categories `C` and `D` that have shifts by an additive group `A`, functors `F : C ⥤ D`
and `G : C ⥤ D`, an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this file constructs
a `CommShift` structure on `G`. We also do the construction in the other direction: given a
`CommShift` structure on `G`, we construct a `CommShift` structure on `G`; we could do this
using opposite categories, but the construction is simple enough that it is not really worth it.
As an easy application, if `E : C ≌ D` is an equivalence and `E.functor` has a `CommShift`
structure, we get a `CommShift` structure on `E.inverse`.

We now explain the construction of a `CommShift` structure on `G` given a `CommShift` structure
on `F`; the other direction is similar. The `CommShift` structure on `G` must be compatible with
the one on `F` in the following sense (cf. `Adjunction.CommShift`):
for every `a` in `A`, the natural transformation `adj.unit : 𝟭 C ⟶ G ⋙ F` commutes with
the isomorphism `shiftFunctor C A ⋙ G ⋙ F ≅ G ⋙ F ⋙ shiftFunctor C A` induces by
`F.commShiftIso a` and `G.commShiftIso a`. We actually require a similar condition for
`adj.counit`, but it follows from the one for `adj.unit`.

In order to simplify the construction of the `CommShift` structure on `G`, we first introduce
the compatibility condition on `adj.unit` for a fixed `a` in `A` and for isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`. We then prove that:
- If `e₁` and `e₂` satisfy this condition, then `e₁` uniquely determines `e₂` and vice versa.
- If `a = 0`, the isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G`
  satisfy the condition.
- The condition is stable by addition on `A`, if we use `Functor.CommShift.isoAdd` to deduce
  commutation isomorphism for `a + b` from such isomorphism from `a` and `b`.
- Given commutation isomorphisms for `F`, our candidate commutation isomorphisms for `G`,
  constructed in `Adjunction.RightAdjointCommShift.iso`, satisfy the compatibility condition.

Once we have established all this, the compatibility of the commutation isomorphism for
`F` expressed in `CommShift.zero` and `CommShift.add` immediately implies the similar
statements for the commutation isomorphisms for `G`.

-/

@[expose] public section

namespace CategoryTheory

open Category

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]
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

set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, compatibility of `e₁` and `e₂` with the
unit of the adjunction `adj` implies compatibility with the counit of `adj`.
-/
lemma compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂) :
    CompatibilityCounit adj e₁ e₂ := by
  intro Y
  have eq := h (G.obj Y)
  simp only [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _)),
    assoc, Iso.hom_inv_id_app_assoc, comp_id, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.comp_obj, Functor.map_id] at eq
  apply (adj.homEquiv _ _).injective
  dsimp
  rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp, adj.unit_naturality_assoc, ← eq]
  simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  erw [← e₂.inv.naturality]
  dsimp
  simp only [right_triangle_components, ← Functor.map_comp_assoc, Functor.map_id, id_comp,
    Iso.hom_inv_id_app, Functor.comp_obj]

set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then we get a formula for `e₂.inv` in terms of `e₁`.
-/
lemma compatibilityUnit_right (h : CompatibilityUnit adj e₁ e₂) (Y : D) :
    e₂.inv.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧') := by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc, ← this, assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.id_obj, Functor.comp_map, assoc, comp_id,
    ← (shiftFunctor C a).map_comp, right_triangle_components, Functor.map_id]

set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
counit of the adjunction `adj`, then we get a formula for `e₁.hom` in terms of `e₂`.
-/
lemma compatibilityCounit_left (h : CompatibilityCounit adj e₁ e₂) (X : C) :
    e₁.hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app _ := by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _)), ← assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id,
    id_comp] at this
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [this, dsimp% e₁.hom.naturality_assoc, ← Functor.map_comp, left_triangle_components]
  simp only [Functor.map_id, comp_id]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then `e₁` uniquely determines `e₂`.
-/
lemma compatibilityUnit_unique_right (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁ e₂') : e₂ = e₂' := by
  rw [← Iso.symm_eq_iff]
  ext
  rw [Iso.symm_hom, Iso.symm_hom, compatibilityUnit_right adj e₁ e₂ h,
    compatibilityUnit_right adj e₁ e₂' h']

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then `e₂` uniquely determines `e₁`.
-/
lemma compatibilityUnit_unique_left (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁' e₂) : e₁ = e₁' := by
  ext
  rw [compatibilityCounit_left adj e₁ e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h),
    compatibilityCounit_left adj e₁' e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h')]

set_option backward.isDefEq.respectTransparency false in
/--
The isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G` are
compatible with the unit of an adjunction `F ⊣ G`.
-/
lemma compatibilityUnit_isoZero : CompatibilityUnit adj (Functor.CommShift.isoZero F A)
    (Functor.CommShift.isoZero G A) := by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc,
    ← cancel_mono ((shiftFunctorZero C A).hom.app _), ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj, Functor.map_id, id_comp, NatTrans.naturality, Functor.id_map, assoc, comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Given an adjunction `adj : F ⊣ G`, `a, b` in `A` and commutation isomorphisms
between shifts by `a` (resp. `b`) and `F` and `G`, if these commutation isomorphisms are
compatible with the unit of `adj`, then so are the commutation isomorphisms between shifts
by `a + b` and `F` and `G` constructed by `Functor.CommShift.isoAdd`.
-/
lemma compatibilityUnit_isoAdd (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj f₁ f₂) :
    CompatibilityUnit adj (Functor.CommShift.isoAdd e₁ f₁) (Functor.CommShift.isoAdd e₂ f₂) := by
  intro X
  have := h' (X⟦a⟧)
  simp only [← cancel_mono (f₂.inv.app _), assoc, Iso.hom_inv_id_app,
    Functor.id_obj, Functor.comp_obj, comp_id] at this
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc]
  slice_rhs 5 6 => rw [← G.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]
  erw [f₂.hom.naturality_assoc]
  rw [← reassoc_of% this, ← cancel_mono ((shiftFunctorAdd C a b).hom.app _),
    assoc, assoc, assoc, assoc, assoc, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  dsimp
  rw [← (shiftFunctor C b).map_comp_assoc, ← (shiftFunctor C b).map_comp_assoc,
    assoc, ← h X, NatTrans.naturality]
  dsimp
  rw [comp_id]

end CommShift

variable (A) [F.CommShift A] [G.CommShift A]

/--
The property for `CommShift` structures on `F` and `G` to be compatible with an
adjunction `F ⊣ G`.
-/
class CommShift : Prop where
  commShift_unit : NatTrans.CommShift adj.unit A := by infer_instance
  commShift_counit : NatTrans.CommShift adj.counit A := by infer_instance

open CommShift in
attribute [instance] commShift_unit commShift_counit

@[reassoc (attr := simp)]
lemma unit_app_commShiftIso_hom_app [adj.CommShift A] (a : A) (X : C) :
    adj.unit.app (X⟦a⟧) ≫ ((F ⋙ G).commShiftIso a).hom.app X = (adj.unit.app X)⟦a⟧' := by
  simpa using (NatTrans.shift_app_comm adj.unit a X).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma unit_app_shift_commShiftIso_inv_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' ≫ ((F ⋙ G).commShiftIso a).inv.app X = adj.unit.app (X⟦a⟧) := by
  simp [← cancel_mono (((F ⋙ G).commShiftIso _).hom.app _)]

@[reassoc (attr := simp)]
lemma commShiftIso_hom_app_counit_app_shift [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).hom.app Y ≫ (adj.counit.app Y)⟦a⟧' = adj.counit.app (Y⟦a⟧) := by
  simpa using (NatTrans.shift_app_comm adj.counit a Y)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma commShiftIso_inv_app_counit_app [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).inv.app Y ≫ adj.counit.app (Y⟦a⟧) = (adj.counit.app Y)⟦a⟧' := by
  simp [← cancel_epi (((G ⋙ F).commShiftIso _).hom.app _)]

namespace CommShift


/-- Constructor for `Adjunction.CommShift`. -/
lemma mk' (_ : NatTrans.CommShift adj.unit A) :
    adj.CommShift A where
  commShift_counit := ⟨fun a ↦ by
    ext
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app, assoc, Functor.whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, comp_id]
    refine (compatibilityCounit_of_compatibilityUnit adj _ _ (fun X ↦ ?_) _).symm
    simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X⟩

/-- The identity adjunction is compatible with the trivial `CommShift` structure on the
identity functor.
-/
instance instId : (Adjunction.id (C := C)).CommShift A where
  commShift_counit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.hom A)
  commShift_unit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.inv A)

variable {E : Type*} [Category* E] {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
  [HasShift E A] [F'.CommShift A] [G'.CommShift A] [adj.CommShift A] [adj'.CommShift A]

/-- Compatibility of `Adjunction.Commshift` with the composition of adjunctions.
-/
instance instComp : (adj.comp adj').CommShift A where
  commShift_counit := by
    rw [comp_counit]
    infer_instance
  commShift_unit := by
    rw [comp_unit]
    infer_instance

end CommShift

variable {A}

@[reassoc]
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
        G.map ((F.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (F.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X

@[reassoc]
lemma shift_counit_app [adj.CommShift A] (a : A) (Y : D) :
    (adj.counit.app Y)⟦a⟧' =
      (F.commShiftIso a).inv.app (G.obj Y) ≫ F.map ((G.commShiftIso a).inv.app Y) ≫
        adj.counit.app (Y⟦a⟧) := by
  have eq := NatTrans.shift_app_comm adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, Functor.id_obj, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_id, id_comp, Iso.inv_hom_id_app_assoc]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]
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

@[reassoc]
lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (G.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (G.map ((F.commShiftIso b).hom.app (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (G.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (G.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', shiftEquiv']

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
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
  simp only [iso, iso', shiftEquiv', Equiv.toFun_as_coe, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_apply_app, Functor.comp_obj, comp_unit_app, Functor.id_obj,
    Equivalence.toAdjunction_unit, Equivalence.Equivalence_mk'_unit, Iso.symm_hom, Functor.comp_map,
    comp_counit_app, Equivalence.toAdjunction_counit, Equivalence.Equivalence_mk'_counit,
    Functor.map_shiftFunctorCompIsoId_hom_app, assoc, Functor.map_comp]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]

set_option backward.isDefEq.respectTransparency false in
/--
The commutation isomorphisms of `Adjunction.RightAdjointCommShift.iso` are compatible with
the unit of the adjunction.
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (F.commShiftIso a) (iso adj a) := by
  intro
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app _), assoc, assoc,
    Iso.hom_inv_id_app, RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp only [comp_id, homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    counit_naturality_assoc, left_triangle_components_assoc]
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    left_triangle_components, Functor.map_id, comp_id]

end RightAdjointCommShift

variable (A)

open RightAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this constructs
the unique compatible `CommShift` structure on `G`.
-/
@[simps -isSimp, implicit_reducible]
noncomputable def rightAdjointCommShift [F.CommShift A] : G.CommShift A where
  commShiftIso a := iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso 0) _ _
      (compatibilityUnit_iso adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso (a + b)) _ _
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [F.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

lemma commShift_of_leftAdjoint [F.CommShift A] :
    letI := adj.rightAdjointCommShift A
    adj.CommShift A := by
  letI := adj.rightAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a ↦ ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using RightAdjointCommShift.compatibilityUnit_iso adj a X

namespace LeftAdjointCommShift

variable {A} (a b : A) (h : a + b = 0) [G.CommShift A]

/-- Auxiliary definition for `iso`. -/
noncomputable def iso' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a b h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C a b h).toAdjunction adj)).invFun (G.commShiftIso b)

/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, these are the candidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `F`.
-/
noncomputable def iso : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  iso' adj _ _ (add_neg_cancel a)

@[reassoc]
lemma iso_hom_app (X : C) :
    (iso adj a).hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫
      F.map (G.map (((shiftFunctorCompIsoId D a b h).inv.app (F.obj X)))⟦a⟧') ≫
        F.map (((G.commShiftIso b).hom.app ((F.obj X)⟦a⟧))⟦a⟧') ≫
          F.map ((shiftFunctorCompIsoId C b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (G.obj ((F.obj X)⟦a⟧))) ≫ adj.counit.app ((F.obj X)⟦a⟧) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

@[reassoc]
lemma iso_inv_app (Y : C) :
    (iso adj a).inv.app Y = (F.map ((shiftFunctorCompIsoId C a b h).inv.app Y))⟦a⟧' ≫
      (F.map ((adj.unit.app (Y⟦a⟧))⟦b⟧'))⟦a⟧' ≫ (F.map ((G.commShiftIso b).inv.app
        (F.obj (Y⟦a⟧))))⟦a⟧' ≫ (adj.counit.app ((F.obj (Y⟦a⟧))⟦b⟧))⟦a⟧' ≫
          (shiftFunctorCompIsoId D b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (F.obj (Y⟦a⟧)) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

set_option backward.isDefEq.respectTransparency false in
/--
The commutation isomorphisms of `Adjunction.LeftAdjointCommShift.iso` are compatible with
the unit of the adjunction.
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (iso adj a) (G.commShiftIso a) := by
  intro
  rw [LeftAdjointCommShift.iso_hom_app adj _ _ (add_neg_cancel a)]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_shiftFunctorCompIsoId_inv_app,
    Functor.map_comp, assoc, unit_naturality_assoc, right_triangle_components_assoc]
  slice_rhs 4 5 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp]
  rw [shift_shiftFunctorCompIsoId_inv_app, ← Functor.comp_map,
    (shiftFunctorCompIsoId C _ _ (neg_add_cancel a)).hom.naturality_assoc]
  simp

end LeftAdjointCommShift

open LeftAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, this constructs
the unique compatible `CommShift` structure on `F`.
-/
@[simps -isSimp, implicit_reducible]
noncomputable def leftAdjointCommShift [G.CommShift A] : F.CommShift A where
  commShiftIso a := iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso 0)
      (compatibilityUnit_iso adj 0) ?_
    rw [G.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso (a + b))
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [G.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

lemma commShift_of_rightAdjoint [G.CommShift A] :
    letI := adj.leftAdjointCommShift A
    adj.CommShift A := by
  letI := adj.leftAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a ↦ ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using LeftAdjointCommShift.compatibilityUnit_iso adj a X

end Adjunction

namespace Equivalence

variable {C D : Type*} [Category* C] [Category* D] (E : C ≌ D)

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

instance [E.CommShift A] : NatTrans.CommShift E.counitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.counit A)

instance : E.symm.inverse.CommShift A := inferInstanceAs (E.functor.CommShift A)
instance : E.symm.functor.CommShift A := inferInstanceAs (E.inverse.CommShift A)

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk' (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_unit := h
  commShift_counit := (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

/--
The forward functor of the identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).functor.CommShift A :=
  inferInstanceAs <| (𝟭 C).CommShift A

/--
The inverse functor of the identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).inverse.CommShift A :=
  inferInstanceAs <| (𝟭 C).CommShift A


/--
The identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).CommShift A :=
  inferInstanceAs <| Adjunction.id.CommShift A

/--
If an equivalence `E : C ≌ D` is compatible with shifts, so is `E.symm`.
-/
instance [E.CommShift A] : E.symm.CommShift A :=
  mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))

/-- Constructor for `Equivalence.CommShift`. -/
lemma mk'' (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A :=
  have := mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))
  inferInstanceAs (E.symm.symm.CommShift A)

variable {F : Type*} [Category* F] [HasShift F A] {E' : D ≌ F} [E.CommShift A]
    [E'.functor.CommShift A] [E'.inverse.CommShift A] [E'.CommShift A]

/--
If `E : C ≌ D` and `E' : D ≌ F` are equivalences whose forward functors are compatible with shifts,
so is `(E.trans E').functor`.
-/
instance : (E.trans E').functor.CommShift A := by
  dsimp
  infer_instance

/--
If `E : C ≌ D` and `E' : D ≌ F` are equivalences whose inverse functors are compatible with shifts,
so is `(E.trans E').inverse`.
-/
instance : (E.trans E').inverse.CommShift A := by
  dsimp
  infer_instance

/--
If equivalences `E : C ≌ D` and `E' : D ≌ F` are compatible with shifts, so is `E.trans E'`.
-/
instance : (E.trans E').CommShift A :=
  inferInstanceAs ((E.toAdjunction.comp E'.toAdjunction).CommShift A)

end CommShift

end

variable (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.functor`,
this constructs the unique compatible `CommShift` structure on `E.inverse`.
-/
@[implicit_reducible]
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
@[implicit_reducible]
noncomputable def commShiftFunctor [E.inverse.CommShift A] : E.functor.CommShift A :=
  E.symm.toAdjunction.rightAdjointCommShift A

lemma commShift_of_inverse [E.inverse.CommShift A] :
    letI := E.commShiftFunctor A
    E.CommShift A := by
  letI := E.commShiftFunctor A
  have := E.symm.commShift_of_functor A
  exact inferInstanceAs (E.symm.symm.CommShift A)

end Equivalence

end CategoryTheory
