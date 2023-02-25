/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.over
! leanprover-community/mathlib commit 8a318021995877a44630c898d0b2bc376fceef3b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.StructuredArrow
import Mathbin.CategoryTheory.Punit
import Mathbin.CategoryTheory.Functor.ReflectsIsomorphisms
import Mathbin.CategoryTheory.Functor.EpiMono

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

comma, slice, coslice, over, under
-/


namespace CategoryTheory

universe v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
variable {T : Type u₁} [Category.{v₁} T]

/-- The over category has as objects arrows in `T` with codomain `X` and as morphisms commutative
triangles.

See <https://stacks.math.columbia.edu/tag/001G>.
-/
def Over (X : T) :=
  CostructuredArrow (𝟭 T) X deriving Category
#align category_theory.over CategoryTheory.Over

-- Satisfying the inhabited linter
instance Over.inhabited [Inhabited T] : Inhabited (Over (default : T))
    where default :=
    { left := default
      right := default
      Hom := 𝟙 _ }
#align category_theory.over.inhabited CategoryTheory.Over.inhabited

namespace Over

variable {X : T}

@[ext]
theorem OverMorphism.ext {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g := by
  tidy
#align category_theory.over.over_morphism.ext CategoryTheory.Over.OverMorphism.ext

@[simp]
theorem over_right (U : Over X) : U.right = ⟨⟨⟩⟩ := by tidy
#align category_theory.over.over_right CategoryTheory.Over.over_right

@[simp]
theorem id_left (U : Over X) : CommaMorphism.left (𝟙 U) = 𝟙 U.left :=
  rfl
#align category_theory.over.id_left CategoryTheory.Over.id_left

@[simp]
theorem comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl
#align category_theory.over.comp_left CategoryTheory.Over.comp_left

@[simp, reassoc.1]
theorem w {A B : Over X} (f : A ⟶ B) : f.left ≫ B.Hom = A.Hom := by have := f.w <;> tidy
#align category_theory.over.w CategoryTheory.Over.w

/-- To give an object in the over category, it suffices to give a morphism with codomain `X`. -/
@[simps left Hom]
def mk {X Y : T} (f : Y ⟶ X) : Over X :=
  CostructuredArrow.mk f
#align category_theory.over.mk CategoryTheory.Over.mk

/-- We can set up a coercion from arrows with codomain `X` to `over X`. This most likely should not
    be a global instance, but it is sometimes useful. -/
def coeFromHom {X Y : T} : Coe (Y ⟶ X) (Over X) where coe := mk
#align category_theory.over.coe_from_hom CategoryTheory.Over.coeFromHom

section

attribute [local instance] coe_from_hom

@[simp]
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).Hom = f :=
  rfl
#align category_theory.over.coe_hom CategoryTheory.Over.coe_hom

end

/-- To give a morphism in the over category, it suffices to give an arrow fitting in a commutative
    triangle. -/
@[simps]
def homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.Hom = U.Hom := by obviously) : U ⟶ V :=
  CostructuredArrow.homMk f w
#align category_theory.over.hom_mk CategoryTheory.Over.homMk

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
@[simps]
def isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.Hom ≫ g.Hom = f.Hom := by obviously) :
    f ≅ g :=
  CostructuredArrow.isoMk hl hw
#align category_theory.over.iso_mk CategoryTheory.Over.isoMk

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain.

See <https://stacks.math.columbia.edu/tag/001G>.
-/
def forget : Over X ⥤ T :=
  Comma.fst _ _
#align category_theory.over.forget CategoryTheory.Over.forget

end

@[simp]
theorem forget_obj {U : Over X} : (forget X).obj U = U.left :=
  rfl
#align category_theory.over.forget_obj CategoryTheory.Over.forget_obj

@[simp]
theorem forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl
#align category_theory.over.forget_map CategoryTheory.Over.forget_map

/-- The natural cocone over the forgetful functor `over X ⥤ T` with cocone point `X`. -/
@[simps]
def forgetCocone (X : T) : Limits.Cocone (forget X) :=
  { x
    ι := { app := Comma.hom } }
#align category_theory.over.forget_cocone CategoryTheory.Over.forgetCocone

/-- A morphism `f : X ⟶ Y` induces a functor `over X ⥤ over Y` in the obvious way.

See <https://stacks.math.columbia.edu/tag/001G>.
-/
def map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y :=
  Comma.mapRight _ <| Discrete.natTrans fun _ => f
#align category_theory.over.map CategoryTheory.Over.map

section

variable {Y : T} {f : X ⟶ Y} {U V : Over X} {g : U ⟶ V}

@[simp]
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl
#align category_theory.over.map_obj_left CategoryTheory.Over.map_obj_left

@[simp]
theorem map_obj_hom : ((map f).obj U).Hom = U.Hom ≫ f :=
  rfl
#align category_theory.over.map_obj_hom CategoryTheory.Over.map_obj_hom

@[simp]
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl
#align category_theory.over.map_map_left CategoryTheory.Over.map_map_left

/-- Mapping by the identity morphism is just the identity functor. -/
def mapId : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (by tidy)) (by tidy)
#align category_theory.over.map_id CategoryTheory.Over.mapId

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map f ⋙ map g :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (by tidy)) (by tidy)
#align category_theory.over.map_comp CategoryTheory.Over.mapComp

end

instance forget_reflects_iso : ReflectsIsomorphisms (forget X)
    where reflects Y Z f t :=
    ⟨⟨over.hom_mk (inv ((forget X).map f))
          ((as_iso ((forget X).map f)).inv_comp_eq.2 (over.w f).symm),
        by tidy⟩⟩
#align category_theory.over.forget_reflects_iso CategoryTheory.Over.forget_reflects_iso

instance forget_faithful : Faithful (forget X) where
#align category_theory.over.forget_faithful CategoryTheory.Over.forget_faithful

-- TODO: Show the converse holds if `T` has binary products.
/--
If `k.left` is an epimorphism, then `k` is an epimorphism. In other words, `over.forget X` reflects
epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`category_theory.over.epi_left_of_epi`.
-/
theorem epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k :=
  (forget X).epi_of_epi_map hk
#align category_theory.over.epi_of_epi_left CategoryTheory.Over.epi_of_epi_left

/--
If `k.left` is a monomorphism, then `k` is a monomorphism. In other words, `over.forget X` reflects
monomorphisms.
The converse of `category_theory.over.mono_left_of_mono`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k :=
  (forget X).mono_of_mono_map hk
#align category_theory.over.mono_of_mono_left CategoryTheory.Over.mono_of_mono_left

/--
If `k` is a monomorphism, then `k.left` is a monomorphism. In other words, `over.forget X` preserves
monomorphisms.
The converse of `category_theory.over.mono_of_mono_left`.
-/
instance mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left :=
  by
  refine' ⟨fun (Y : T) l m a => _⟩
  let l' : mk (m ≫ f.hom) ⟶ f :=
    hom_mk l
      (by
        dsimp
        rw [← over.w k, reassoc_of a])
  suffices l' = hom_mk m by apply congr_arg comma_morphism.left this
  rw [← cancel_mono k]
  ext
  apply a
#align category_theory.over.mono_left_of_mono CategoryTheory.Over.mono_left_of_mono

section IteratedSlice

variable (f : Over X)

/-- Given f : Y ⟶ X, this is the obvious functor from (T/X)/f to T/Y -/
@[simps]
def iteratedSliceForward : Over f ⥤ Over f.left
    where
  obj α := Over.mk α.Hom.left
  map α β κ :=
    Over.homMk κ.left.left
      (by
        rw [autoParam_eq]
        rw [← over.w κ]
        rfl)
#align category_theory.over.iterated_slice_forward CategoryTheory.Over.iteratedSliceForward

/-- Given f : Y ⟶ X, this is the obvious functor from T/Y to (T/X)/f -/
@[simps]
def iteratedSliceBackward : Over f.left ⥤ Over f
    where
  obj g := mk (homMk g.Hom : mk (g.Hom ≫ f.Hom) ⟶ f)
  map g h α := homMk (homMk α.left (w_assoc α f.Hom)) (OverMorphism.ext (w α))
#align category_theory.over.iterated_slice_backward CategoryTheory.Over.iteratedSliceBackward

/-- Given f : Y ⟶ X, we have an equivalence between (T/X)/f and T/Y -/
@[simps]
def iteratedSliceEquiv : Over f ≌ Over f.left
    where
  Functor := iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso :=
    NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _) (by tidy)) (by tidy))
      fun X Y g => by
      ext
      dsimp
      simp
  counitIso :=
    NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _) (by tidy)) fun X Y g =>
      by
      ext
      dsimp
      simp
#align category_theory.over.iterated_slice_equiv CategoryTheory.Over.iteratedSliceEquiv

theorem iteratedSliceForward_forget :
    iteratedSliceForward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl
#align category_theory.over.iterated_slice_forward_forget CategoryTheory.Over.iteratedSliceForward_forget

theorem iteratedSliceBackward_forget_forget :
    iteratedSliceBackward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl
#align category_theory.over.iterated_slice_backward_forget_forget CategoryTheory.Over.iteratedSliceBackward_forget_forget

end IteratedSlice

section

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `over X ⥤ over (F.obj X)` in the obvious way. -/
@[simps]
def post (F : T ⥤ D) : Over X ⥤ Over (F.obj X)
    where
  obj Y := mk <| F.map Y.Hom
  map Y₁ Y₂ f := Over.homMk (F.map f.left) (by tidy <;> erw [← F.map_comp, w])
#align category_theory.over.post CategoryTheory.Over.post

end

end Over

/-- The under category has as objects arrows with domain `X` and as morphisms commutative
    triangles. -/
def Under (X : T) :=
  StructuredArrow X (𝟭 T)deriving Category
#align category_theory.under CategoryTheory.Under

-- Satisfying the inhabited linter
instance Under.inhabited [Inhabited T] : Inhabited (Under (default : T))
    where default :=
    { left := default
      right := default
      Hom := 𝟙 _ }
#align category_theory.under.inhabited CategoryTheory.Under.inhabited

namespace Under

variable {X : T}

@[ext]
theorem UnderMorphism.ext {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right) : f = g :=
  by tidy
#align category_theory.under.under_morphism.ext CategoryTheory.Under.UnderMorphism.ext

@[simp]
theorem under_left (U : Under X) : U.left = ⟨⟨⟩⟩ := by tidy
#align category_theory.under.under_left CategoryTheory.Under.under_left

@[simp]
theorem id_right (U : Under X) : CommaMorphism.right (𝟙 U) = 𝟙 U.right :=
  rfl
#align category_theory.under.id_right CategoryTheory.Under.id_right

@[simp]
theorem comp_right (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.right ≫ g.right :=
  rfl
#align category_theory.under.comp_right CategoryTheory.Under.comp_right

@[simp, reassoc.1]
theorem w {A B : Under X} (f : A ⟶ B) : A.Hom ≫ f.right = B.Hom := by have := f.w <;> tidy
#align category_theory.under.w CategoryTheory.Under.w

/-- To give an object in the under category, it suffices to give an arrow with domain `X`. -/
@[simps right Hom]
def mk {X Y : T} (f : X ⟶ Y) : Under X :=
  StructuredArrow.mk f
#align category_theory.under.mk CategoryTheory.Under.mk

/-- To give a morphism in the under category, it suffices to give a morphism fitting in a
    commutative triangle. -/
@[simps]
def homMk {U V : Under X} (f : U.right ⟶ V.right) (w : U.Hom ≫ f = V.Hom := by obviously) : U ⟶ V :=
  StructuredArrow.homMk f w
#align category_theory.under.hom_mk CategoryTheory.Under.homMk

/-- Construct an isomorphism in the over category given isomorphisms of the objects whose forward
direction gives a commutative triangle.
-/
def isoMk {f g : Under X} (hr : f.right ≅ g.right) (hw : f.Hom ≫ hr.Hom = g.Hom) : f ≅ g :=
  StructuredArrow.isoMk hr hw
#align category_theory.under.iso_mk CategoryTheory.Under.isoMk

@[simp]
theorem isoMk_hom_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.Hom ≫ hr.Hom = g.Hom) :
    (isoMk hr hw).Hom.right = hr.Hom :=
  rfl
#align category_theory.under.iso_mk_hom_right CategoryTheory.Under.isoMk_hom_right

@[simp]
theorem isoMk_inv_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.Hom ≫ hr.Hom = g.Hom) :
    (isoMk hr hw).inv.right = hr.inv :=
  rfl
#align category_theory.under.iso_mk_inv_right CategoryTheory.Under.isoMk_inv_right

section

variable (X)

/-- The forgetful functor mapping an arrow to its domain. -/
def forget : Under X ⥤ T :=
  Comma.snd _ _
#align category_theory.under.forget CategoryTheory.Under.forget

end

@[simp]
theorem forget_obj {U : Under X} : (forget X).obj U = U.right :=
  rfl
#align category_theory.under.forget_obj CategoryTheory.Under.forget_obj

@[simp]
theorem forget_map {U V : Under X} {f : U ⟶ V} : (forget X).map f = f.right :=
  rfl
#align category_theory.under.forget_map CategoryTheory.Under.forget_map

/-- The natural cone over the forgetful functor `under X ⥤ T` with cone point `X`. -/
@[simps]
def forgetCone (X : T) : Limits.Cone (forget X) :=
  { x
    π := { app := Comma.hom } }
#align category_theory.under.forget_cone CategoryTheory.Under.forgetCone

/-- A morphism `X ⟶ Y` induces a functor `under Y ⥤ under X` in the obvious way. -/
def map {Y : T} (f : X ⟶ Y) : Under Y ⥤ Under X :=
  Comma.mapLeft _ <| Discrete.natTrans fun _ => f
#align category_theory.under.map CategoryTheory.Under.map

section

variable {Y : T} {f : X ⟶ Y} {U V : Under Y} {g : U ⟶ V}

@[simp]
theorem map_obj_right : ((map f).obj U).right = U.right :=
  rfl
#align category_theory.under.map_obj_right CategoryTheory.Under.map_obj_right

@[simp]
theorem map_obj_hom : ((map f).obj U).Hom = f ≫ U.Hom :=
  rfl
#align category_theory.under.map_obj_hom CategoryTheory.Under.map_obj_hom

@[simp]
theorem map_map_right : ((map f).map g).right = g.right :=
  rfl
#align category_theory.under.map_map_right CategoryTheory.Under.map_map_right

/-- Mapping by the identity morphism is just the identity functor. -/
def mapId : map (𝟙 Y) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (by tidy)) (by tidy)
#align category_theory.under.map_id CategoryTheory.Under.mapId

/-- Mapping by the composite morphism `f ≫ g` is the same as mapping by `f` then by `g`. -/
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _) (by tidy)) (by tidy)
#align category_theory.under.map_comp CategoryTheory.Under.mapComp

end

instance forget_reflects_iso : ReflectsIsomorphisms (forget X)
    where reflects Y Z f t :=
    ⟨⟨under.hom_mk (inv ((under.forget X).map f)) ((is_iso.comp_inv_eq _).2 (under.w f).symm), by
        tidy⟩⟩
#align category_theory.under.forget_reflects_iso CategoryTheory.Under.forget_reflects_iso

instance forget_faithful : Faithful (forget X) where
#align category_theory.under.forget_faithful CategoryTheory.Under.forget_faithful

-- TODO: Show the converse holds if `T` has binary coproducts.
/-- If `k.right` is a monomorphism, then `k` is a monomorphism. In other words, `under.forget X`
reflects epimorphisms.
The converse does not hold without additional assumptions on the underlying category, see
`category_theory.under.mono_right_of_mono`.
-/
theorem mono_of_mono_right {f g : Under X} (k : f ⟶ g) [hk : Mono k.right] : Mono k :=
  (forget X).mono_of_mono_map hk
#align category_theory.under.mono_of_mono_right CategoryTheory.Under.mono_of_mono_right

/--
If `k.right` is a epimorphism, then `k` is a epimorphism. In other words, `under.forget X` reflects
epimorphisms.
The converse of `category_theory.under.epi_right_of_epi`.

This lemma is not an instance, to avoid loops in type class inference.
-/
theorem epi_of_epi_right {f g : Under X} (k : f ⟶ g) [hk : Epi k.right] : Epi k :=
  (forget X).epi_of_epi_map hk
#align category_theory.under.epi_of_epi_right CategoryTheory.Under.epi_of_epi_right

/--
If `k` is a epimorphism, then `k.right` is a epimorphism. In other words, `under.forget X` preserves
epimorphisms.
The converse of `category_theory.under.epi_of_epi_right`.
-/
instance epi_right_of_epi {f g : Under X} (k : f ⟶ g) [Epi k] : Epi k.right :=
  by
  refine' ⟨fun (Y : T) l m a => _⟩
  let l' : g ⟶ mk (g.hom ≫ m) :=
    hom_mk l
      (by
        dsimp
        rw [← under.w k, category.assoc, a, category.assoc])
  suffices l' = hom_mk m by apply congr_arg comma_morphism.right this
  rw [← cancel_epi k]
  ext
  apply a
#align category_theory.under.epi_right_of_epi CategoryTheory.Under.epi_right_of_epi

section

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `F : T ⥤ D` induces a functor `under X ⥤ under (F.obj X)` in the obvious way. -/
@[simps]
def post {X : T} (F : T ⥤ D) : Under X ⥤ Under (F.obj X)
    where
  obj Y := mk <| F.map Y.Hom
  map Y₁ Y₂ f := Under.homMk (F.map f.right) (by tidy <;> erw [← F.map_comp, w])
#align category_theory.under.post CategoryTheory.Under.post

end

end Under

end CategoryTheory

