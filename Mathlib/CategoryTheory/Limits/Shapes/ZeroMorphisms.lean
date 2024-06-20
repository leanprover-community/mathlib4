/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

#align_import category_theory.limits.shapes.zero_morphisms from "leanprover-community/mathlib"@"f7707875544ef1f81b32cb68c79e0e24e45a0e76"

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


noncomputable section

universe v u

universe v' u'

open CategoryTheory

open CategoryTheory.Category

open scoped Classical

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable (D : Type u') [Category.{v'} D]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class HasZeroMorphisms where
  /-- Every morphism space has zero -/
  [zero : ∀ X Y : C, Zero (X ⟶ Y)]
  /-- `f` composed with `0` is `0` -/
  comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := by aesop_cat
  /-- `0` composed with `f` is `0` -/
  zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := by aesop_cat
#align category_theory.limits.has_zero_morphisms CategoryTheory.Limits.HasZeroMorphisms
#align category_theory.limits.has_zero_morphisms.comp_zero' CategoryTheory.Limits.HasZeroMorphisms.comp_zero
#align category_theory.limits.has_zero_morphisms.zero_comp' CategoryTheory.Limits.HasZeroMorphisms.zero_comp

attribute [instance] HasZeroMorphisms.zero

variable {C}

@[simp]
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z
#align category_theory.limits.comp_zero CategoryTheory.Limits.comp_zero

@[simp]
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f
#align category_theory.limits.zero_comp CategoryTheory.Limits.zero_comp

instance hasZeroMorphismsPEmpty : HasZeroMorphisms (Discrete PEmpty) where
  zero := by aesop_cat
#align category_theory.limits.has_zero_morphisms_pempty CategoryTheory.Limits.hasZeroMorphismsPEmpty

instance hasZeroMorphismsPUnit : HasZeroMorphisms (Discrete PUnit) where
  zero X Y := by repeat (constructor)
#align category_theory.limits.has_zero_morphisms_punit CategoryTheory.Limits.hasZeroMorphismsPUnit

namespace HasZeroMorphisms

/-- This lemma will be immediately superseded by `ext`, below. -/
private theorem ext_aux (I J : HasZeroMorphisms C)
    (w : ∀ X Y : C, (I.zero X Y).zero = (J.zero X Y).zero) : I = J := by
  have : I.zero = J.zero := by
    funext X Y
    specialize w X Y
    apply congrArg Zero.mk w
  cases I; cases J
  congr
  · apply proof_irrel_heq
  · apply proof_irrel_heq
-- Porting note: private def; no align

/-- If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `HasZeroMorphisms` to exist at all.

See, particularly, the note on `zeroMorphismsOfZeroObject` below.
-/
theorem ext (I J : HasZeroMorphisms C) : I = J := by
  apply ext_aux
  intro X Y
  have : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (I.zero X Y).zero := by
    apply I.zero_comp X (J.zero Y Y).zero
  have that : (I.zero X Y).zero ≫ (J.zero Y Y).zero = (J.zero X Y).zero := by
    apply J.comp_zero (I.zero X Y).zero Y
  rw [← this, ← that]
#align category_theory.limits.has_zero_morphisms.ext CategoryTheory.Limits.HasZeroMorphisms.ext

instance : Subsingleton (HasZeroMorphisms C) :=
  ⟨ext⟩

end HasZeroMorphisms

open Opposite HasZeroMorphisms

instance hasZeroMorphismsOpposite [HasZeroMorphisms C] : HasZeroMorphisms Cᵒᵖ where
  zero X Y := ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero f Z := congr_arg Quiver.Hom.op (HasZeroMorphisms.zero_comp (unop Z) f.unop)
  zero_comp X {Y Z} (f : Y ⟶ Z) :=
    congrArg Quiver.Hom.op (HasZeroMorphisms.comp_zero f.unop (unop X))
#align category_theory.limits.has_zero_morphisms_opposite CategoryTheory.Limits.hasZeroMorphismsOpposite

section

variable [HasZeroMorphisms C]

@[simp] lemma op_zero (X Y : C) : (0 : X ⟶ Y).op = 0 := rfl
#align category_theory.op_zero CategoryTheory.Limits.op_zero

@[simp] lemma unop_zero (X Y : Cᵒᵖ) : (0 : X ⟶ Y).unop = 0 := rfl
#align category_theory.unop_zero CategoryTheory.Limits.unop_zero

theorem zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0 := by
  rw [← zero_comp, cancel_mono] at h
  exact h
#align category_theory.limits.zero_of_comp_mono CategoryTheory.Limits.zero_of_comp_mono

theorem zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0 := by
  rw [← comp_zero, cancel_epi] at h
  exact h
#align category_theory.limits.zero_of_epi_comp CategoryTheory.Limits.zero_of_epi_comp

theorem eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0) :
    f = 0 := by rw [← image.fac f, w, HasZeroMorphisms.comp_zero]
#align category_theory.limits.eq_zero_of_image_eq_zero CategoryTheory.Limits.eq_zero_of_image_eq_zero

theorem nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f ≠ 0) : image.ι f ≠ 0 :=
  fun h => w (eq_zero_of_image_eq_zero h)
#align category_theory.limits.nonzero_image_of_nonzero CategoryTheory.Limits.nonzero_image_of_nonzero

end

section

variable [HasZeroMorphisms D]

instance : HasZeroMorphisms (C ⥤ D) where
  zero F G := ⟨{ app := fun X => 0 }⟩
  comp_zero := fun η H => by
    ext X; dsimp; apply comp_zero
  zero_comp := fun F {G H} η => by
    ext X; dsimp; apply zero_comp

@[simp]
theorem zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0 := rfl
#align category_theory.limits.zero_app CategoryTheory.Limits.zero_app

end

namespace IsZero

variable [HasZeroMorphisms C]

theorem eq_zero_of_src {X Y : C} (o : IsZero X) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_src _ _
#align category_theory.limits.is_zero.eq_zero_of_src CategoryTheory.Limits.IsZero.eq_zero_of_src

theorem eq_zero_of_tgt {X Y : C} (o : IsZero Y) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_tgt _ _
#align category_theory.limits.is_zero.eq_zero_of_tgt CategoryTheory.Limits.IsZero.eq_zero_of_tgt

theorem iff_id_eq_zero (X : C) : IsZero X ↔ 𝟙 X = 0 :=
  ⟨fun h => h.eq_of_src _ _, fun h =>
    ⟨fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← id_comp f, ← id_comp (0: X ⟶ Y), h, zero_comp, zero_comp]; simp only⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← comp_id f, ← comp_id (0 : Y ⟶ X), h, comp_zero, comp_zero]; simp only ⟩⟩⟩⟩
#align category_theory.limits.is_zero.iff_id_eq_zero CategoryTheory.Limits.IsZero.iff_id_eq_zero

theorem of_mono_zero (X Y : C) [Mono (0 : X ⟶ Y)] : IsZero X :=
  (iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))
#align category_theory.limits.is_zero.of_mono_zero CategoryTheory.Limits.IsZero.of_mono_zero

theorem of_epi_zero (X Y : C) [Epi (0 : X ⟶ Y)] : IsZero Y :=
  (iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))
#align category_theory.limits.is_zero.of_epi_zero CategoryTheory.Limits.IsZero.of_epi_zero

theorem of_mono_eq_zero {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0) : IsZero X := by
  subst h
  apply of_mono_zero X Y
#align category_theory.limits.is_zero.of_mono_eq_zero CategoryTheory.Limits.IsZero.of_mono_eq_zero

theorem of_epi_eq_zero {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0) : IsZero Y := by
  subst h
  apply of_epi_zero X Y
#align category_theory.limits.is_zero.of_epi_eq_zero CategoryTheory.Limits.IsZero.of_epi_eq_zero

theorem iff_isSplitMono_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsZero X ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.id_comp f, h, zero_comp]
  · intro h
    rw [← IsSplitMono.id f]
    simp only [h, zero_comp]
#align category_theory.limits.is_zero.iff_is_split_mono_eq_zero CategoryTheory.Limits.IsZero.iff_isSplitMono_eq_zero

theorem iff_isSplitEpi_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsZero Y ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.comp_id f, h, comp_zero]
  · intro h
    rw [← IsSplitEpi.id f]
    simp [h]
#align category_theory.limits.is_zero.iff_is_split_epi_eq_zero CategoryTheory.Limits.IsZero.iff_isSplitEpi_eq_zero

theorem of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y) : IsZero X := by
  have hf := i.eq_zero_of_tgt f
  subst hf
  exact IsZero.of_mono_zero X Y
#align category_theory.limits.is_zero.of_mono CategoryTheory.Limits.IsZero.of_mono

theorem of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X) : IsZero Y := by
  have hf := i.eq_zero_of_src f
  subst hf
  exact IsZero.of_epi_zero X Y
#align category_theory.limits.is_zero.of_epi CategoryTheory.Limits.IsZero.of_epi

end IsZero

/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zeroMorphismsOfZeroObject` will then be incompatible with these categories because
    the `HasZeroMorphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `HasZeroMorphisms` separately, even if it already
    asks for an instance of `HasZeroObjects`. -/
def IsZero.hasZeroMorphisms {O : C} (hO : IsZero O) : HasZeroMorphisms C where
  zero X Y := { zero := hO.from_ X ≫ hO.to_ Y }
  zero_comp X {Y Z} f := by
    change (hO.from_ X ≫ hO.to_ Y) ≫ f = hO.from_ X ≫ hO.to_ Z
    rw [Category.assoc]
    congr
    apply hO.eq_of_src
  comp_zero {X Y} f Z := by
    change f ≫ (hO.from_ Y ≫ hO.to_ Z) = hO.from_ X ≫ hO.to_ Z
    rw [← Category.assoc]
    congr
    apply hO.eq_of_tgt
#align category_theory.limits.is_zero.has_zero_morphisms CategoryTheory.Limits.IsZero.hasZeroMorphisms

namespace HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zeroMorphismsOfZeroObject` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `HasZeroMorphisms` separately, even if it already
    asks for an instance of `HasZeroObjects`. -/
def zeroMorphismsOfZeroObject : HasZeroMorphisms C where
  zero X Y := { zero := (default : X ⟶ 0) ≫ default }
  zero_comp X {Y Z} f := by
    change ((default : X ⟶ 0) ≫ default) ≫ f = (default : X ⟶ 0) ≫ default
    rw [Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]
  comp_zero {X Y} f Z := by
    change f ≫ (default : Y ⟶ 0) ≫ default = (default : X ⟶ 0) ≫ default
    rw [← Category.assoc]
    congr
    simp only [eq_iff_true_of_subsingleton]
#align category_theory.limits.has_zero_object.zero_morphisms_of_zero_object CategoryTheory.Limits.HasZeroObject.zeroMorphismsOfZeroObject

section HasZeroMorphisms

variable [HasZeroMorphisms C]

@[simp]
theorem zeroIsoIsInitial_hom {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).hom = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_initial_hom CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_hom

@[simp]
theorem zeroIsoIsInitial_inv {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).inv = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_initial_inv CategoryTheory.Limits.HasZeroObject.zeroIsoIsInitial_inv

@[simp]
theorem zeroIsoIsTerminal_hom {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).hom = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_terminal_hom CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_hom

@[simp]
theorem zeroIsoIsTerminal_inv {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).inv = 0 := by ext
#align category_theory.limits.has_zero_object.zero_iso_is_terminal_inv CategoryTheory.Limits.HasZeroObject.zeroIsoIsTerminal_inv

@[simp]
theorem zeroIsoInitial_hom [HasInitial C] : zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C) := by ext
#align category_theory.limits.has_zero_object.zero_iso_initial_hom CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_hom

@[simp]
theorem zeroIsoInitial_inv [HasInitial C] : zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0) := by ext
#align category_theory.limits.has_zero_object.zero_iso_initial_inv CategoryTheory.Limits.HasZeroObject.zeroIsoInitial_inv

@[simp]
theorem zeroIsoTerminal_hom [HasTerminal C] : zeroIsoTerminal.hom = (0 : 0 ⟶ ⊤_ C) := by ext
#align category_theory.limits.has_zero_object.zero_iso_terminal_hom CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_hom

@[simp]
theorem zeroIsoTerminal_inv [HasTerminal C] : zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0) := by ext
#align category_theory.limits.has_zero_object.zero_iso_terminal_inv CategoryTheory.Limits.HasZeroObject.zeroIsoTerminal_inv

end HasZeroMorphisms

open ZeroObject

instance {B : Type*} [Category B] : HasZeroObject (B ⥤ C) :=
  (((CategoryTheory.Functor.const B).obj (0 : C)).isZero fun _ => isZero_zero _).hasZeroObject

end HasZeroObject

open ZeroObject

variable {D}

@[simp]
theorem IsZero.map [HasZeroObject D] [HasZeroMorphisms D] {F : C ⥤ D} (hF : IsZero F) {X Y : C}
    (f : X ⟶ Y) : F.map f = 0 :=
  (hF.obj _).eq_of_src _ _
#align category_theory.limits.is_zero.map CategoryTheory.Limits.IsZero.map

@[simp]
theorem _root_.CategoryTheory.Functor.zero_obj [HasZeroObject D] (X : C) :
    IsZero ((0 : C ⥤ D).obj X) :=
  (isZero_zero _).obj _
#align category_theory.functor.zero_obj CategoryTheory.Functor.zero_obj

@[simp]
theorem _root_.CategoryTheory.zero_map [HasZeroObject D] [HasZeroMorphisms D] {X Y : C}
    (f : X ⟶ Y) : (0 : C ⥤ D).map f = 0 :=
  (isZero_zero _).map _
#align category_theory.zero_map CategoryTheory.zero_map

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

@[simp]
theorem id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0) := by apply HasZeroObject.from_zero_ext
#align category_theory.limits.id_zero CategoryTheory.Limits.id_zero

-- This can't be a `simp` lemma because the left hand side would be a metavariable.
/-- An arrow ending in the zero object is zero -/
theorem zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 := by ext
#align category_theory.limits.zero_of_to_zero CategoryTheory.Limits.zero_of_to_zero

theorem zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 := by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [Iso.hom_inv_id, id_comp, comp_id]
  simpa using h
#align category_theory.limits.zero_of_target_iso_zero CategoryTheory.Limits.zero_of_target_iso_zero

/-- An arrow starting at the zero object is zero -/
theorem zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 := by ext
#align category_theory.limits.zero_of_from_zero CategoryTheory.Limits.zero_of_from_zero

theorem zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 := by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [Iso.hom_inv_id_assoc, id_comp, comp_id]
  simpa using h
#align category_theory.limits.zero_of_source_iso_zero CategoryTheory.Limits.zero_of_source_iso_zero

theorem zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0) : f = 0 :=
  zero_of_source_iso_zero f (Nonempty.some i)
#align category_theory.limits.zero_of_source_iso_zero' CategoryTheory.Limits.zero_of_source_iso_zero'

theorem zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0) : f = 0 :=
  zero_of_target_iso_zero f (Nonempty.some i)
#align category_theory.limits.zero_of_target_iso_zero' CategoryTheory.Limits.zero_of_target_iso_zero'

theorem mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : Mono f :=
  ⟨fun {Z} g h _ => by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩
#align category_theory.limits.mono_of_source_iso_zero CategoryTheory.Limits.mono_of_source_iso_zero

theorem epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : Epi f :=
  ⟨fun {Z} g h _ => by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩
#align category_theory.limits.epi_of_target_iso_zero CategoryTheory.Limits.epi_of_target_iso_zero

/-- An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as an `≃`.
-/
def idZeroEquivIsoZero (X : C) : 𝟙 X = 0 ≃ (X ≅ 0) where
  toFun h :=
    { hom := 0
      inv := 0 }
  invFun i := zero_of_target_iso_zero (𝟙 X) i
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.limits.id_zero_equiv_iso_zero CategoryTheory.Limits.idZeroEquivIsoZero

@[simp]
theorem idZeroEquivIsoZero_apply_hom (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).hom = 0 :=
  rfl
#align category_theory.limits.id_zero_equiv_iso_zero_apply_hom CategoryTheory.Limits.idZeroEquivIsoZero_apply_hom

@[simp]
theorem idZeroEquivIsoZero_apply_inv (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).inv = 0 :=
  rfl
#align category_theory.limits.id_zero_equiv_iso_zero_apply_inv CategoryTheory.Limits.idZeroEquivIsoZero_apply_inv

/-- If `0 : X ⟶ Y` is a monomorphism, then `X ≅ 0`. -/
@[simps]
def isoZeroOfMonoZero {X Y : C} (h : Mono (0 : X ⟶ Y)) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_mono (0 : X ⟶ Y)).mp (by simp)
#align category_theory.limits.iso_zero_of_mono_zero CategoryTheory.Limits.isoZeroOfMonoZero

/-- If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`. -/
@[simps]
def isoZeroOfEpiZero {X Y : C} (h : Epi (0 : X ⟶ Y)) : Y ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_epi (0 : X ⟶ Y)).mp (by simp)
#align category_theory.limits.iso_zero_of_epi_zero CategoryTheory.Limits.isoZeroOfEpiZero

/-- If a monomorphism out of `X` is zero, then `X ≅ 0`. -/
def isoZeroOfMonoEqZero {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0) : X ≅ 0 := by
  subst h
  apply isoZeroOfMonoZero ‹_›
#align category_theory.limits.iso_zero_of_mono_eq_zero CategoryTheory.Limits.isoZeroOfMonoEqZero

/-- If an epimorphism in to `Y` is zero, then `Y ≅ 0`. -/
def isoZeroOfEpiEqZero {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0) : Y ≅ 0 := by
  subst h
  apply isoZeroOfEpiZero ‹_›
#align category_theory.limits.iso_zero_of_epi_eq_zero CategoryTheory.Limits.isoZeroOfEpiEqZero

/-- If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices. -/
def isoOfIsIsomorphicZero {X : C} (P : IsIsomorphic X 0) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by
    cases' P with P
    rw [← P.hom_inv_id, ← Category.id_comp P.inv]
    apply Eq.symm
    simp only [id_comp, Iso.hom_inv_id, comp_zero]
    apply (idZeroEquivIsoZero X).invFun P
  inv_hom_id := by simp
#align category_theory.limits.iso_of_is_isomorphic_zero CategoryTheory.Limits.isoOfIsIsomorphicZero

end

section IsIso

variable [HasZeroMorphisms C]

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
@[simps]
def isIsoZeroEquiv (X Y : C) : IsIso (0 : X ⟶ Y) ≃ 𝟙 X = 0 ∧ 𝟙 Y = 0 where
  toFun := by
    intro i
    rw [← IsIso.hom_inv_id (0 : X ⟶ Y)]
    rw [← IsIso.inv_hom_id (0 : X ⟶ Y)]
    simp only [eq_self_iff_true,comp_zero,and_self,zero_comp]
  invFun h := ⟨⟨(0 : Y ⟶ X), by aesop_cat⟩⟩
  left_inv := by aesop_cat
  right_inv := by aesop_cat
#align category_theory.limits.is_iso_zero_equiv CategoryTheory.Limits.isIsoZeroEquiv

-- Porting note: simp solves these
attribute [-simp, nolint simpNF] isIsoZeroEquiv_apply isIsoZeroEquiv_symm_apply

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
def isIsoZeroSelfEquiv (X : C) : IsIso (0 : X ⟶ X) ≃ 𝟙 X = 0 := by simpa using isIsoZeroEquiv X X
#align category_theory.limits.is_iso_zero_self_equiv CategoryTheory.Limits.isIsoZeroSelfEquiv

variable [HasZeroObject C]

open ZeroObject

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are isomorphic to the zero object.
-/
def isIsoZeroEquivIsoZero (X Y : C) : IsIso (0 : X ⟶ Y) ≃ (X ≅ 0) × (Y ≅ 0) := by
  -- This is lame, because `Prod` can't cope with `Prop`, so we can't use `Equiv.prodCongr`.
  refine (isIsoZeroEquiv X Y).trans ?_
  symm
  fconstructor
  · rintro ⟨eX, eY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X).symm eX
    · exact (idZeroEquivIsoZero Y).symm eY
  · rintro ⟨hX, hY⟩
    fconstructor
    · exact (idZeroEquivIsoZero X) hX
    · exact (idZeroEquivIsoZero Y) hY
  · aesop_cat
  · aesop_cat
#align category_theory.limits.is_iso_zero_equiv_iso_zero CategoryTheory.Limits.isIsoZeroEquivIsoZero

theorem isIso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) :
    IsIso f := by
  rw [zero_of_source_iso_zero f i]
  exact (isIsoZeroEquivIsoZero _ _).invFun ⟨i, j⟩
#align category_theory.limits.is_iso_of_source_target_iso_zero CategoryTheory.Limits.isIso_of_source_target_iso_zero

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
def isIsoZeroSelfEquivIsoZero (X : C) : IsIso (0 : X ⟶ X) ≃ (X ≅ 0) :=
  (isIsoZeroEquivIsoZero X X).trans subsingletonProdSelfEquiv
#align category_theory.limits.is_iso_zero_self_equiv_iso_zero CategoryTheory.Limits.isIsoZeroSelfEquivIsoZero

end IsIso

/-- If there are zero morphisms, any initial object is a zero object. -/
theorem hasZeroObject_of_hasInitial_object [HasZeroMorphisms C] [HasInitial C] :
    HasZeroObject C := by
  refine ⟨⟨⊥_ C, fun X => ⟨⟨⟨0⟩, by aesop_cat⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩⟩
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ 0 := by congr!; apply Subsingleton.elim
    _ = 0 := HasZeroMorphisms.comp_zero _ _
#align category_theory.limits.has_zero_object_of_has_initial_object CategoryTheory.Limits.hasZeroObject_of_hasInitial_object

/-- If there are zero morphisms, any terminal object is a zero object. -/
theorem hasZeroObject_of_hasTerminal_object [HasZeroMorphisms C] [HasTerminal C] :
    HasZeroObject C := by
  refine ⟨⟨⊤_ C, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, by aesop_cat⟩⟩⟩⟩
  calc
    f = 𝟙 _ ≫ f := (Category.id_comp _).symm
    _ = 0 ≫ f := by congr!; apply Subsingleton.elim
    _ = 0 := zero_comp
#align category_theory.limits.has_zero_object_of_has_terminal_object CategoryTheory.Limits.hasZeroObject_of_hasTerminal_object

section Image

variable [HasZeroMorphisms C]

theorem image_ι_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
    [Epi (factorThruImage f)] (h : f ≫ g = 0) : image.ι f ≫ g = 0 :=
  zero_of_epi_comp (factorThruImage f) <| by simp [h]
#align category_theory.limits.image_ι_comp_eq_zero CategoryTheory.Limits.image_ι_comp_eq_zero

theorem comp_factorThruImage_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage g]
    (h : f ≫ g = 0) : f ≫ factorThruImage g = 0 :=
  zero_of_comp_mono (image.ι g) <| by simp [h]
#align category_theory.limits.comp_factor_thru_image_eq_zero CategoryTheory.Limits.comp_factorThruImage_eq_zero

variable [HasZeroObject C]

open ZeroObject

/-- The zero morphism has a `MonoFactorisation` through the zero object.
-/
@[simps]
def monoFactorisationZero (X Y : C) : MonoFactorisation (0 : X ⟶ Y) where
  I := 0
  m := 0
  e := 0
#align category_theory.limits.mono_factorisation_zero CategoryTheory.Limits.monoFactorisationZero

/-- The factorisation through the zero object is an image factorisation.
-/
def imageFactorisationZero (X Y : C) : ImageFactorisation (0 : X ⟶ Y) where
  F := monoFactorisationZero X Y
  isImage := { lift := fun F' => 0 }
#align category_theory.limits.image_factorisation_zero CategoryTheory.Limits.imageFactorisationZero

instance hasImage_zero {X Y : C} : HasImage (0 : X ⟶ Y) :=
  HasImage.mk <| imageFactorisationZero _ _
#align category_theory.limits.has_image_zero CategoryTheory.Limits.hasImage_zero

/-- The image of a zero morphism is the zero object. -/
def imageZero {X Y : C} : image (0 : X ⟶ Y) ≅ 0 :=
  IsImage.isoExt (Image.isImage (0 : X ⟶ Y)) (imageFactorisationZero X Y).isImage
#align category_theory.limits.image_zero CategoryTheory.Limits.imageZero

/-- The image of a morphism which is equal to zero is the zero object. -/
def imageZero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] : image f ≅ 0 :=
  image.eqToIso h ≪≫ imageZero
#align category_theory.limits.image_zero' CategoryTheory.Limits.imageZero'

@[simp]
theorem image.ι_zero {X Y : C} [HasImage (0 : X ⟶ Y)] : image.ι (0 : X ⟶ Y) = 0 := by
  rw [← image.lift_fac (monoFactorisationZero X Y)]
  simp
#align category_theory.limits.image.ι_zero CategoryTheory.Limits.image.ι_zero

/-- If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp]
theorem image.ι_zero' [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] :
    image.ι f = 0 := by
  rw [image.eq_fac h]
  simp
#align category_theory.limits.image.ι_zero' CategoryTheory.Limits.image.ι_zero'

end Image

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_sigma_ι {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasColimit (Discrete.functor f)] (b : β) : IsSplitMono (Sigma.ι f b) :=
  IsSplitMono.mk' { retraction := Sigma.desc <| Pi.single b (𝟙 _) }
#align category_theory.limits.is_split_mono_sigma_ι CategoryTheory.Limits.isSplitMono_sigma_ι

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_pi_π {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasLimit (Discrete.functor f)] (b : β) : IsSplitEpi (Pi.π f b) :=
  IsSplitEpi.mk' { section_ := Pi.lift <| Pi.single b (𝟙 _) }
#align category_theory.limits.is_split_epi_pi_π CategoryTheory.Limits.isSplitEpi_pi_π

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_coprod_inl [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inl : X ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc (𝟙 X) 0 }
#align category_theory.limits.is_split_mono_coprod_inl CategoryTheory.Limits.isSplitMono_coprod_inl

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_coprod_inr [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inr : Y ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc 0 (𝟙 Y) }
#align category_theory.limits.is_split_mono_coprod_inr CategoryTheory.Limits.isSplitMono_coprod_inr

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_prod_fst [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.fst : X ⨯ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := prod.lift (𝟙 X) 0 }
#align category_theory.limits.is_split_epi_prod_fst CategoryTheory.Limits.isSplitEpi_prod_fst

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_prod_snd [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.snd : X ⨯ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := prod.lift 0 (𝟙 Y) }
#align category_theory.limits.is_split_epi_prod_snd CategoryTheory.Limits.isSplitEpi_prod_snd

end CategoryTheory.Limits
