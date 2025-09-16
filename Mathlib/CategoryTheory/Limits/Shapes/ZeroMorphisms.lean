/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

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

universe w v v' u u'

open CategoryTheory

open CategoryTheory.Category

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable (D : Type u') [Category.{v'} D]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class HasZeroMorphisms where
  /-- Every morphism space has zero -/
  [zero : ∀ X Y : C, Zero (X ⟶ Y)]
  /-- `f` composed with `0` is `0` -/
  comp_zero : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := by cat_disch
  /-- `0` composed with `f` is `0` -/
  zero_comp : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := by cat_disch

attribute [instance] HasZeroMorphisms.zero

variable {C}

@[simp]
theorem comp_zero [HasZeroMorphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
    f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) :=
  HasZeroMorphisms.comp_zero f Z

@[simp]
theorem zero_comp [HasZeroMorphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
    (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) :=
  HasZeroMorphisms.zero_comp X f

instance hasZeroMorphismsPEmpty : HasZeroMorphisms (Discrete PEmpty) where
  zero := by cat_disch

instance hasZeroMorphismsPUnit : HasZeroMorphisms (Discrete PUnit) where
  zero X Y := by repeat (constructor)

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

instance : Subsingleton (HasZeroMorphisms C) :=
  ⟨ext⟩

end HasZeroMorphisms

open Opposite HasZeroMorphisms

instance hasZeroMorphismsOpposite [HasZeroMorphisms C] : HasZeroMorphisms Cᵒᵖ where
  zero X Y := ⟨(0 : unop Y ⟶ unop X).op⟩
  comp_zero f Z := congr_arg Quiver.Hom.op (HasZeroMorphisms.zero_comp (unop Z) f.unop)
  zero_comp X {Y Z} (f : Y ⟶ Z) :=
    congrArg Quiver.Hom.op (HasZeroMorphisms.comp_zero f.unop (unop X))

section

variable [HasZeroMorphisms C]

@[simp] lemma op_zero (X Y : C) : (0 : X ⟶ Y).op = 0 := rfl

@[simp] lemma unop_zero (X Y : Cᵒᵖ) : (0 : X ⟶ Y).unop = 0 := rfl

theorem zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [Mono g] (h : f ≫ g = 0) : f = 0 := by
  rw [← zero_comp, cancel_mono] at h
  exact h

theorem zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [Epi f] (h : f ≫ g = 0) : g = 0 := by
  rw [← comp_zero, cancel_epi] at h
  exact h

theorem eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : image.ι f = 0) :
    f = 0 := by rw [← image.fac f, w, HasZeroMorphisms.comp_zero]

theorem nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [HasImage f] (w : f ≠ 0) : image.ι f ≠ 0 :=
  fun h => w (eq_zero_of_image_eq_zero h)

end

section

variable [HasZeroMorphisms D]

instance : HasZeroMorphisms (C ⥤ D) where
  zero F G := ⟨{ app := fun _ => 0 }⟩
  comp_zero := fun η H => by
    ext X; dsimp; apply comp_zero
  zero_comp := fun F {G H} η => by
    ext X; dsimp; apply zero_comp

@[simp]
theorem zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0 := rfl

end

namespace IsZero

variable [HasZeroMorphisms C]

theorem eq_zero_of_src {X Y : C} (o : IsZero X) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_src _ _

theorem eq_zero_of_tgt {X Y : C} (o : IsZero Y) (f : X ⟶ Y) : f = 0 :=
  o.eq_of_tgt _ _

theorem iff_id_eq_zero (X : C) : IsZero X ↔ 𝟙 X = 0 :=
  ⟨fun h => h.eq_of_src _ _, fun h =>
    ⟨fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← id_comp f, ← id_comp (0 : X ⟶ Y), h, zero_comp, zero_comp]; simp only⟩⟩,
    fun Y => ⟨⟨⟨0⟩, fun f => by
        rw [← comp_id f, ← comp_id (0 : Y ⟶ X), h, comp_zero, comp_zero]; simp only ⟩⟩⟩⟩

theorem of_mono_zero (X Y : C) [Mono (0 : X ⟶ Y)] : IsZero X :=
  (iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))

theorem of_epi_zero (X Y : C) [Epi (0 : X ⟶ Y)] : IsZero Y :=
  (iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))

theorem of_mono_eq_zero {X Y : C} (f : X ⟶ Y) [Mono f] (h : f = 0) : IsZero X := by
  subst h
  apply of_mono_zero X Y

theorem of_epi_eq_zero {X Y : C} (f : X ⟶ Y) [Epi f] (h : f = 0) : IsZero Y := by
  subst h
  apply of_epi_zero X Y

theorem iff_isSplitMono_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitMono f] : IsZero X ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.id_comp f, h, zero_comp]
  · intro h
    rw [← IsSplitMono.id f]
    simp only [h, zero_comp]

theorem iff_isSplitEpi_eq_zero {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsZero Y ↔ f = 0 := by
  rw [iff_id_eq_zero]
  constructor
  · intro h
    rw [← Category.comp_id f, h, comp_zero]
  · intro h
    rw [← IsSplitEpi.id f]
    simp [h]

theorem of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (i : IsZero Y) : IsZero X := by
  have hf := i.eq_zero_of_tgt f
  subst hf
  exact IsZero.of_mono_zero X Y

theorem of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (i : IsZero X) : IsZero Y := by
  have hf := i.eq_zero_of_src f
  subst hf
  exact IsZero.of_epi_zero X Y

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
  zero X _ := { zero := (default : X ⟶ 0) ≫ default }
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

section HasZeroMorphisms

variable [HasZeroMorphisms C]

@[simp]
theorem zeroIsoIsInitial_hom {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).hom = 0 := by ext

@[simp]
theorem zeroIsoIsInitial_inv {X : C} (t : IsInitial X) : (zeroIsoIsInitial t).inv = 0 := by ext

@[simp]
theorem zeroIsoIsTerminal_hom {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).hom = 0 := by ext

@[simp]
theorem zeroIsoIsTerminal_inv {X : C} (t : IsTerminal X) : (zeroIsoIsTerminal t).inv = 0 := by ext

@[simp]
theorem zeroIsoInitial_hom [HasInitial C] : zeroIsoInitial.hom = (0 : 0 ⟶ ⊥_ C) := by ext

@[simp]
theorem zeroIsoInitial_inv [HasInitial C] : zeroIsoInitial.inv = (0 : ⊥_ C ⟶ 0) := by ext

@[simp]
theorem zeroIsoTerminal_hom [HasTerminal C] : zeroIsoTerminal.hom = (0 : 0 ⟶ ⊤_ C) := by ext

@[simp]
theorem zeroIsoTerminal_inv [HasTerminal C] : zeroIsoTerminal.inv = (0 : ⊤_ C ⟶ 0) := by ext

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

@[simp]
theorem _root_.CategoryTheory.Functor.zero_obj [HasZeroObject D] (X : C) :
    IsZero ((0 : C ⥤ D).obj X) :=
  (isZero_zero _).obj _

@[simp]
theorem _root_.CategoryTheory.zero_map [HasZeroObject D] [HasZeroMorphisms D] {X Y : C}
    (f : X ⟶ Y) : (0 : C ⥤ D).map f = 0 :=
  (isZero_zero _).map _

section

variable [HasZeroObject C] [HasZeroMorphisms C]

open ZeroObject

@[simp]
theorem id_zero : 𝟙 (0 : C) = (0 : (0 : C) ⟶ 0) := by apply HasZeroObject.from_zero_ext

-- This can't be a `simp` lemma because the left-hand side would be a metavariable.
/-- An arrow ending in the zero object is zero -/
theorem zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 := by ext

theorem zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 := by
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [Iso.hom_inv_id, id_comp, comp_id]
  simpa using h

/-- An arrow starting at the zero object is zero -/
theorem zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 := by ext

theorem zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 := by
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [Iso.hom_inv_id_assoc, id_comp]
  simpa using h

theorem zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic X 0) : f = 0 :=
  zero_of_source_iso_zero f (Nonempty.some i)

theorem zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : IsIsomorphic Y 0) : f = 0 :=
  zero_of_target_iso_zero f (Nonempty.some i)

theorem mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : Mono f :=
  ⟨fun {Z} g h _ => by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩

theorem epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : Epi f :=
  ⟨fun {Z} g h _ => by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩

/-- An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as an `≃`.
-/
def idZeroEquivIsoZero (X : C) : 𝟙 X = 0 ≃ (X ≅ 0) where
  toFun h :=
    { hom := 0
      inv := 0 }
  invFun i := zero_of_target_iso_zero (𝟙 X) i
  left_inv := by cat_disch
  right_inv := by cat_disch

@[simp]
theorem idZeroEquivIsoZero_apply_hom (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).hom = 0 :=
  rfl

@[simp]
theorem idZeroEquivIsoZero_apply_inv (X : C) (h : 𝟙 X = 0) : ((idZeroEquivIsoZero X) h).inv = 0 :=
  rfl

/-- If `0 : X ⟶ Y` is a monomorphism, then `X ≅ 0`. -/
@[simps]
def isoZeroOfMonoZero {X Y : C} (_ : Mono (0 : X ⟶ Y)) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_mono (0 : X ⟶ Y)).mp (by simp)

/-- If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`. -/
@[simps]
def isoZeroOfEpiZero {X Y : C} (_ : Epi (0 : X ⟶ Y)) : Y ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := (cancel_epi (0 : X ⟶ Y)).mp (by simp)

/-- If a monomorphism out of `X` is zero, then `X ≅ 0`. -/
def isoZeroOfMonoEqZero {X Y : C} {f : X ⟶ Y} [Mono f] (h : f = 0) : X ≅ 0 := by
  subst h
  apply isoZeroOfMonoZero ‹_›

/-- If an epimorphism in to `Y` is zero, then `Y ≅ 0`. -/
def isoZeroOfEpiEqZero {X Y : C} {f : X ⟶ Y} [Epi f] (h : f = 0) : Y ≅ 0 := by
  subst h
  apply isoZeroOfEpiZero ‹_›

/-- If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices. -/
def isoOfIsIsomorphicZero {X : C} (P : IsIsomorphic X 0) : X ≅ 0 where
  hom := 0
  inv := 0
  hom_inv_id := by
    have P := P.some
    rw [← P.hom_inv_id, ← Category.id_comp P.inv]
    apply Eq.symm
    simp only [id_comp, Iso.hom_inv_id, comp_zero]
    apply (idZeroEquivIsoZero X).invFun P
  inv_hom_id := by simp

end

section IsIso

variable [HasZeroMorphisms C]

/-- A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
def isIsoZeroEquiv (X Y : C) : IsIso (0 : X ⟶ Y) ≃ 𝟙 X = 0 ∧ 𝟙 Y = 0 where
  toFun := by
    intro i
    rw [← IsIso.hom_inv_id (0 : X ⟶ Y)]
    rw [← IsIso.inv_hom_id (0 : X ⟶ Y)]
    simp only [comp_zero,and_self,zero_comp]
  invFun h := ⟨⟨(0 : Y ⟶ X), by cat_disch⟩⟩
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
def isIsoZeroSelfEquiv (X : C) : IsIso (0 : X ⟶ X) ≃ 𝟙 X = 0 := by simpa using isIsoZeroEquiv X X

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
  · cat_disch
  · cat_disch

theorem isIso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) :
    IsIso f := by
  rw [zero_of_source_iso_zero f i]
  exact (isIsoZeroEquivIsoZero _ _).invFun ⟨i, j⟩

/-- A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
def isIsoZeroSelfEquivIsoZero (X : C) : IsIso (0 : X ⟶ X) ≃ (X ≅ 0) :=
  (isIsoZeroEquivIsoZero X X).trans subsingletonProdSelfEquiv

end IsIso

/-- If there are zero morphisms, any initial object is a zero object. -/
theorem hasZeroObject_of_hasInitial_object [HasZeroMorphisms C] [HasInitial C] :
    HasZeroObject C := by
  refine ⟨⟨⊥_ C, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩⟩⟩
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ 0 := by congr!; subsingleton
    _ = 0 := HasZeroMorphisms.comp_zero _ _

/-- If there are zero morphisms, any terminal object is a zero object. -/
theorem hasZeroObject_of_hasTerminal_object [HasZeroMorphisms C] [HasTerminal C] :
    HasZeroObject C := by
  refine ⟨⟨⊤_ C, fun X => ⟨⟨⟨0⟩, fun f => ?_⟩⟩, fun X => ⟨⟨⟨0⟩, by cat_disch⟩⟩⟩⟩
  calc
    f = 𝟙 _ ≫ f := (Category.id_comp _).symm
    _ = 0 ≫ f := by congr!; subsingleton
    _ = 0 := zero_comp

section Image

variable [HasZeroMorphisms C]

theorem image_ι_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage f]
    [Epi (factorThruImage f)] (h : f ≫ g = 0) : image.ι f ≫ g = 0 :=
  zero_of_epi_comp (factorThruImage f) <| by simp [h]

theorem comp_factorThruImage_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [HasImage g]
    (h : f ≫ g = 0) : f ≫ factorThruImage g = 0 :=
  zero_of_comp_mono (image.ι g) <| by simp [h]

variable [HasZeroObject C]

open ZeroObject

/-- The zero morphism has a `MonoFactorisation` through the zero object.
-/
@[simps]
def monoFactorisationZero (X Y : C) : MonoFactorisation (0 : X ⟶ Y) where
  I := 0
  m := 0
  e := 0

/-- The factorisation through the zero object is an image factorisation.
-/
def imageFactorisationZero (X Y : C) : ImageFactorisation (0 : X ⟶ Y) where
  F := monoFactorisationZero X Y
  isImage := { lift := fun _ => 0 }

instance hasImage_zero {X Y : C} : HasImage (0 : X ⟶ Y) :=
  HasImage.mk <| imageFactorisationZero _ _

/-- The image of a zero morphism is the zero object. -/
def imageZero {X Y : C} : image (0 : X ⟶ Y) ≅ 0 :=
  IsImage.isoExt (Image.isImage (0 : X ⟶ Y)) (imageFactorisationZero X Y).isImage

/-- The image of a morphism which is equal to zero is the zero object. -/
def imageZero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] : image f ≅ 0 :=
  image.eqToIso h ≪≫ imageZero

@[simp]
theorem image.ι_zero {X Y : C} [HasImage (0 : X ⟶ Y)] : image.ι (0 : X ⟶ Y) = 0 := by
  rw [← image.lift_fac (monoFactorisationZero X Y)]
  simp

/-- If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp]
theorem image.ι_zero' [HasEqualizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [HasImage f] :
    image.ι f = 0 := by
  rw [image.eq_fac h]
  simp

end Image

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_sigma_ι {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasColimit (Discrete.functor f)] (b : β) : IsSplitMono (Sigma.ι f b) := by
  classical exact IsSplitMono.mk' { retraction := Sigma.desc <| Pi.single b (𝟙 _) }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_pi_π {β : Type u'} [HasZeroMorphisms C] (f : β → C)
    [HasLimit (Discrete.functor f)] (b : β) : IsSplitEpi (Pi.π f b) := by
  classical exact IsSplitEpi.mk' { section_ := Pi.lift <| Pi.single b (𝟙 _) }

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_coprod_inl [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inl : X ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc (𝟙 X) 0 }

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance isSplitMono_coprod_inr [HasZeroMorphisms C] {X Y : C} [HasColimit (pair X Y)] :
    IsSplitMono (coprod.inr : Y ⟶ X ⨿ Y) :=
  IsSplitMono.mk' { retraction := coprod.desc 0 (𝟙 Y) }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_prod_fst [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.fst : X ⨯ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := prod.lift (𝟙 X) 0 }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance isSplitEpi_prod_snd [HasZeroMorphisms C] {X Y : C} [HasLimit (pair X Y)] :
    IsSplitEpi (prod.snd : X ⨯ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := prod.lift 0 (𝟙 Y) }


section

variable [HasZeroMorphisms C] [HasZeroObject C] {F : D ⥤ C}

/-- If a functor `F` is zero, then any cone for `F` with a zero point is limit. -/
def IsLimit.ofIsZero (c : Cone F) (hF : IsZero F) (hc : IsZero c.pt) : IsLimit c where
  lift _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_tgt _ _
  uniq _ _ _ := hc.eq_of_tgt _ _

/-- If a functor `F` is zero, then any cocone for `F` with a zero point is colimit. -/
def IsColimit.ofIsZero (c : Cocone F) (hF : IsZero F) (hc : IsZero c.pt) : IsColimit c where
  desc _ := 0
  fac _ j := (F.isZero_iff.1 hF j).eq_of_src _ _
  uniq _ _ _ := hc.eq_of_src _ _

lemma IsLimit.isZero_pt {c : Cone F} (hc : IsLimit c) (hF : IsZero F) : IsZero c.pt :=
  (isZero_zero C).of_iso (IsLimit.conePointUniqueUpToIso hc
    (IsLimit.ofIsZero (Cone.mk 0 0) hF (isZero_zero C)))

lemma IsColimit.isZero_pt {c : Cocone F} (hc : IsColimit c) (hF : IsZero F) : IsZero c.pt :=
  (isZero_zero C).of_iso (IsColimit.coconePointUniqueUpToIso hc
    (IsColimit.ofIsZero (Cocone.mk 0 0) hF (isZero_zero C)))

end

section

variable [HasZeroMorphisms C]

lemma IsTerminal.isZero {X : C} (hX : IsTerminal X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

lemma IsInitial.isZero {X : C} (hX : IsInitial X) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  apply hX.hom_ext

end

section PiIota

variable [HasZeroMorphisms C] {β : Type w} [DecidableEq β] (f : β → C) [HasProduct f]

/-- In the presence of 0-morphism we can define an inclusion morphism into any product. -/
def Pi.ι (b : β) : f b ⟶ ∏ᶜ f :=
  Pi.lift (Function.update (fun _ ↦ 0) b (𝟙 _))

@[reassoc (attr := simp)]
lemma Pi.ι_π_eq_id (b : β) : Pi.ι f b ≫ Pi.π f b = 𝟙 _ := by
  simp [Pi.ι]

@[reassoc]
lemma Pi.ι_π_of_ne {b c : β} (h : b ≠ c) : Pi.ι f b ≫ Pi.π f c = 0 := by
  simp [Pi.ι, Function.update_of_ne h.symm]

@[reassoc]
lemma Pi.ι_π (b c : β) :
    Pi.ι f b ≫ Pi.π f c = if h : b = c then eqToHom (congrArg f h) else 0 := by
  split_ifs with h
  · subst h; simp
  · simp [Pi.ι_π_of_ne f h]

instance (b : β) : Mono (Pi.ι f b) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ Pi.π f b) e

end PiIota

section SigmaPi

variable [HasZeroMorphisms C] {β : Type w} [DecidableEq β] (f : β → C) [HasCoproduct f]

/-- In the presence of 0-morphisms we can define a projection morphism from any coproduct. -/
def Sigma.π (b : β) : ∐ f ⟶ f b :=
  Limits.Sigma.desc (Function.update (fun _ ↦ 0) b (𝟙 _))

@[reassoc (attr := simp)]
lemma Sigma.ι_π_eq_id (b : β) : Sigma.ι f b ≫ Sigma.π f b = 𝟙 _ := by
  simp [Sigma.π]

@[reassoc]
lemma Sigma.ι_π_of_ne {b c : β} (h : b ≠ c) : Sigma.ι f b ≫ Sigma.π f c = 0 := by
  simp [Sigma.π, Function.update_of_ne h]

@[reassoc]
theorem Sigma.ι_π (b c : β) :
    Sigma.ι f b ≫ Sigma.π f c = if h : b = c then eqToHom (congrArg f h) else 0 := by
  split_ifs with h
  · subst h; simp
  · simp [Sigma.ι_π_of_ne f h]

instance (b : β) : Epi (Sigma.π f b) where
  left_cancellation _ _ e := by simpa using congrArg (Sigma.ι f b ≫ ·) e

end SigmaPi

section ProdInlInr

variable [HasZeroMorphisms C] (X Y : C) [HasBinaryProduct X Y]

/-- If a category `C` has 0-morphisms, there is a canonical inclusion from the first component `X`
into any product of objects `X ⨯ Y`. -/
def prod.inl : X ⟶ X ⨯ Y :=
  prod.lift (𝟙 _) 0

/-- If a category `C` has 0-morphisms, there is a canonical inclusion from the second component `Y`
into any product of objects `X ⨯ Y`. -/
def prod.inr : Y ⟶ X ⨯ Y :=
  prod.lift 0 (𝟙 _)

@[reassoc (attr := simp)]
lemma prod.inl_fst : prod.inl X Y ≫ prod.fst = 𝟙 X := by
  simp [prod.inl]

@[reassoc (attr := simp)]
lemma prod.inl_snd : prod.inl X Y ≫ prod.snd = 0 := by
  simp [prod.inl]

@[reassoc (attr := simp)]
lemma prod.inr_fst : prod.inr X Y ≫ prod.fst = 0 := by
  simp [prod.inr]

@[reassoc (attr := simp)]
lemma prod.inr_snd : prod.inr X Y ≫ prod.snd = 𝟙 Y := by
  simp [prod.inr]

instance : Mono (prod.inl X Y) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ prod.fst) e

instance : Mono (prod.inr X Y) where
  right_cancellation _ _ e := by simpa using congrArg (· ≫ prod.snd) e

end ProdInlInr

section CoprodFstSnd

variable [HasZeroMorphisms C] (X Y : C) [HasBinaryCoproduct X Y]

/-- If a category `C` has 0-morphisms, there is a canonical projection from a coproduct `X ⨿ Y` to
its first component `X`. -/
def coprod.fst : X ⨿ Y ⟶ X :=
  coprod.desc (𝟙 _) 0

/-- If a category `C` has 0-morphisms, there is a canonical projection from a coproduct `X ⨿ Y` to
its second component `Y`. -/
def coprod.snd : X ⨿ Y ⟶ Y :=
  coprod.desc 0 (𝟙 _)

@[reassoc (attr := simp)]
lemma coprod.inl_fst : coprod.inl ≫ coprod.fst X Y = 𝟙 X := by
  simp [coprod.fst]

@[reassoc (attr := simp)]
lemma coprod.inr_fst : coprod.inr ≫ coprod.fst X Y = 0 := by
  simp [coprod.fst]

@[reassoc (attr := simp)]
lemma coprod.inl_snd : coprod.inl ≫ coprod.snd X Y = 0 := by
  simp [coprod.snd]

@[reassoc (attr := simp)]
lemma coprod.inr_snd : coprod.inr ≫ coprod.snd X Y = 𝟙 Y := by
  simp [coprod.snd]

instance : Epi (coprod.fst X Y) where
  left_cancellation _ _ e := by simpa using congrArg (coprod.inl ≫ ·) e

instance : Epi (coprod.snd X Y) where
  left_cancellation _ _ e := by simpa using congrArg (coprod.inr ≫ ·) e

end CoprodFstSnd

end CategoryTheory.Limits
