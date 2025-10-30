/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.ObjectProperty.Basic

/-!
# The full subcategory associated to a property of objects

Given a category `C` and `P : ObjectProperty C`, we define
a category structure on the type `P.FullSubcategory`
of objects in `C` satisfying `P`.

-/

universe v v' u u'

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type u} [Category.{v} C]

section

variable (P : ObjectProperty C)

/--
A subtype-like structure for full subcategories. Morphisms just ignore the property. We don't use
actual subtypes since the simp-normal form `↑X` of `X.val` does not work well for full
subcategories. -/
@[ext, stacks 001D "We do not define 'strictly full' subcategories."]
structure FullSubcategory where
  /-- The category of which this is a full subcategory -/
  obj : C
  /-- The predicate satisfied by all objects in this subcategory -/
  property : P obj

instance FullSubcategory.category : Category.{v} P.FullSubcategory :=
  inferInstanceAs (Category (InducedCategory _ FullSubcategory.obj))

@[ext]
lemma hom_ext {X Y : P.FullSubcategory} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g :=
  InducedCategory.hom_ext h

/-- The forgetful functor from a full subcategory into the original category
("forgetting" the condition).
-/
def ι : P.FullSubcategory ⥤ C :=
  inducedFunctor FullSubcategory.obj

@[simp]
theorem ι_obj {X} : P.ι.obj X = X.obj :=
  rfl

@[simp]
theorem ι_map {X Y} {f : X ⟶ Y} : P.ι.map f = f.hom :=
  rfl

@[simp]
lemma FullSubcategory.id_hom (X : P.FullSubcategory) :
    InducedCategory.Hom.hom (𝟙 X) = 𝟙 X.obj := rfl

@[simp, reassoc]
lemma FullSubcategory.comp_hom {X Y Z : P.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[deprecated (since := "2025-06-26")] alias FullSubcategory.id_def := FullSubcategory.id_hom
@[deprecated (since := "2025-06-26")] alias FullSubcategory.comp_def := FullSubcategory.comp_hom

variable {P} in
/-- Constructor for morphisms in a full subcategory. -/
@[simps]
def homMk {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) : X ⟶ Y where
  hom := f

/-- The inclusion of a full subcategory is fully faithful. -/
abbrev fullyFaithfulι :
    P.ι.FullyFaithful where
  preimage f := homMk _

instance full_ι : P.ι.Full := P.fullyFaithfulι.full
instance faithful_ι : P.ι.Faithful := P.fullyFaithfulι.faithful

/-- Constructor for isomorphisms in `P.FullSubcategory` when
`P : ObjectProperty C`. -/
@[simps]
def isoMk {X Y : P.FullSubcategory} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := homMk e.hom
  inv := homMk e.inv

variable {P}

@[reassoc (attr := simp)]
lemma isoHom_inv_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) :
    e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
  P.ι.congr_map e.hom_inv_id

@[reassoc (attr := simp)]
lemma isoInv_hom_id_hom {X Y : P.FullSubcategory} (e : X ≅ Y) :
    e.inv.hom ≫ e.hom.hom = 𝟙 _ :=
  P.ι.congr_map e.inv_hom_id

variable {P' : ObjectProperty C}

/-- If `P` and `P'` are properties of objects such that `P ≤ P'`, there is
an induced functor `P.FullSubcategory ⥤ P'.FullSubcategory`. -/
@[simps]
def ιOfLE (h : P ≤ P') : P.FullSubcategory ⥤ P'.FullSubcategory where
  obj X := ⟨X.1, h _ X.2⟩
  map f := homMk f.hom

/-- If `h : P ≤ P'`, then `ιOfLE h` is fully faithful. -/
def fullyFaithfulιOfLE (h : P ≤ P') :
    (ιOfLE h).FullyFaithful where
  preimage f := homMk f.hom

instance full_ιOfLE (h : P ≤ P') : (ιOfLE h).Full := (fullyFaithfulιOfLE h).full
instance faithful_ιOfLE (h : P ≤ P') : (ιOfLE h).Faithful := (fullyFaithfulιOfLE h).faithful

@[deprecated "use ιOfLECompιIso" (since := "2025-03-04")]
theorem FullSubcategory.map_inclusion (h : P ≤ P') : ιOfLE h ⋙ P'.ι = P.ι := rfl

/-- If `h : P ≤ P'` is an inequality of properties of objects,
this is the obvious isomorphism `ιOfLE h ⋙ P'.ι ≅ P.ι`. -/
def ιOfLECompιIso (h : P ≤ P') : ιOfLE h ⋙ P'.ι ≅ P.ι := Iso.refl _

end

section lift

variable {D : Type u'} [Category.{v'} D] (P Q : ObjectProperty D)
  (F : C ⥤ D) (hF : ∀ X, P (F.obj X))

/-- A functor which maps objects to objects satisfying a certain property induces a lift through
    the full subcategory of objects satisfying that property. -/
@[simps]
def lift : C ⥤ FullSubcategory P where
  obj X := ⟨F.obj X, hF X⟩
  map f := homMk (F.map f)

@[deprecated "use liftCompιIso" (since := "2025-03-04")]
theorem FullSubcategory.lift_comp_inclusion_eq :
    P.lift F hF ⋙ P.ι = F :=
  rfl

/-- Composing the lift of a functor through a full subcategory with the inclusion yields the
    original functor. This is actually true definitionally. -/
def liftCompιIso : P.lift F hF ⋙ P.ι ≅ F := Iso.refl _

@[simp]
lemma ι_obj_lift_obj (X : C) :
    P.ι.obj ((P.lift F hF).obj X) = F.obj X := rfl

@[simp]
lemma ι_obj_lift_map {X Y : C} (f : X ⟶ Y) :
    P.ι.map ((P.lift F hF).map f) = F.map f := rfl

instance [F.Faithful] : (P.lift F hF).Faithful :=
  Functor.Faithful.of_comp_iso (P.liftCompιIso F hF)

instance [F.Full] : (P.lift F hF).Full :=
  Functor.Full.of_comp_faithful_iso (P.liftCompιIso F hF)

variable {Q}

/-- When `h : P ≤ Q`, this is the canonical isomorphism
`P.lift F hF ⋙ ιOfLE h ≅ Q.lift F _`. -/
def liftCompιOfLEIso (h : P ≤ Q) :
    P.lift F hF ⋙ ιOfLE h ≅ Q.lift F (fun X ↦ h _ (hF X)) := Iso.refl _

@[deprecated "Use liftCompιOfLEIso" (since := "2025-03-04")]
theorem FullSubcategory.lift_comp_map (h : P ≤ Q) :
    P.lift F hF ⋙ ιOfLE h =
      Q.lift F (fun X ↦ h _ (hF X)) :=
  rfl

end lift

end ObjectProperty

@[deprecated (since := "2025-03-04")] alias FullSubcategory := ObjectProperty.FullSubcategory
@[deprecated (since := "2025-03-04")] alias fullSubcategoryInclusion := ObjectProperty.ι
@[deprecated (since := "2025-03-04")] alias fullSubcategoryInclusion.obj := ObjectProperty.ι_obj
@[deprecated (since := "2025-03-04")] alias fullSubcategoryInclusion.map := ObjectProperty.ι_map
@[deprecated (since := "2025-03-04")] alias fullyFaithfulFullSubcategoryInclusion :=
  ObjectProperty.fullyFaithfulι
@[deprecated (since := "2025-03-04")] alias FullSubcategory.map := ObjectProperty.ιOfLE
@[deprecated (since := "2025-03-04")] alias FullSubcategory.lift := ObjectProperty.lift
@[deprecated (since := "2025-03-04")] alias FullSubcategory.lift_comp_inclusion :=
  ObjectProperty.liftCompιIso
@[deprecated (since := "2025-03-04")] alias fullSubcategoryInclusion_obj_lift_obj :=
  ObjectProperty.ι_obj_lift_obj
@[deprecated (since := "2025-03-04")] alias fullSubcategoryInclusion_map_lift_map :=
  ObjectProperty.ι_obj_lift_map

end CategoryTheory
