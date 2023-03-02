/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.shapes.images
! leanprover-community/mathlib commit 563aed347eb59dc4181cb732cda0d124d736eaa3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.StrongEpi

/-!
# Categorical images

We define the categorical image of `f` as a factorisation `f = e ≫ m` through a monomorphism `m`,
so that `m` factors through the `m'` in any other such factorisation.

## Main definitions

* A `mono_factorisation` is a factorisation `f = e ≫ m`, where `m` is a monomorphism
* `is_image F` means that a given mono factorisation `F` has the universal property of the image.
* `has_image f` means that there is some image factorization for the morphism `f : X ⟶ Y`.
  * In this case, `image f` is some image object (selected with choice), `image.ι f : image f ⟶ Y`
    is the monomorphism `m` of the factorisation and `factor_thru_image f : X ⟶ image f` is the
    morphism `e`.
* `has_images C` means that every morphism in `C` has an image.
* Let `f : X ⟶ Y` and `g : P ⟶ Q` be morphisms in `C`, which we will represent as objects of the
  arrow category `arrow C`. Then `sq : f ⟶ g` is a commutative square in `C`. If `f` and `g` have
  images, then `has_image_map sq` represents the fact that there is a morphism
  `i : image f ⟶ image g` making the diagram

  X ----→ image f ----→ Y
  |         |           |
  |         |           |
  ↓         ↓           ↓
  P ----→ image g ----→ Q

  commute, where the top row is the image factorisation of `f`, the bottom row is the image
  factorisation of `g`, and the outer rectangle is the commutative square `sq`.
* If a category `has_images`, then `has_image_maps` means that every commutative square admits an
  image map.
* If a category `has_images`, then `has_strong_epi_images` means that the morphism to the image is
  always a strong epimorphism.

## Main statements

* When `C` has equalizers, the morphism `e` appearing in an image factorisation is an epimorphism.
* When `C` has strong epi images, then these images admit image maps.

## Future work
* TODO: coimages, and abelian categories.
* TODO: connect this with existing working in the group theory and ring theory libraries.

-/


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {X Y : C} (f : X ⟶ Y)

/-- A factorisation of a morphism `f = e ≫ m`, with `m` monic. -/
structure MonoFactorisation (f : X ⟶ Y) where
  i : C
  m : I ⟶ Y
  [m_mono : Mono m]
  e : X ⟶ I
  fac : e ≫ m = f := by obviously
#align category_theory.limits.mono_factorisation CategoryTheory.Limits.MonoFactorisation

restate_axiom mono_factorisation.fac'

attribute [simp, reassoc.1] mono_factorisation.fac

attribute [instance] mono_factorisation.m_mono

attribute [instance] mono_factorisation.m_mono

namespace MonoFactorisation

/-- The obvious factorisation of a monomorphism through itself. -/
def self [Mono f] : MonoFactorisation f where
  i := X
  m := f
  e := 𝟙 X
#align category_theory.limits.mono_factorisation.self CategoryTheory.Limits.MonoFactorisation.self

-- I'm not sure we really need this, but the linter says that an inhabited instance
-- ought to exist...
instance [Mono f] : Inhabited (MonoFactorisation f) :=
  ⟨self f⟩

variable {f}

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely
determined. -/
@[ext]
theorem ext {F F' : MonoFactorisation f} (hI : F.i = F'.i) (hm : F.m = eqToHom hI ≫ F'.m) :
    F = F' := by
  cases F; cases F'
  cases hI
  simp at hm
  dsimp at F_fac' F'_fac'
  congr
  · assumption
  · skip
    apply (cancel_mono F_m).1
    rw [F_fac', hm, F'_fac']
#align category_theory.limits.mono_factorisation.ext CategoryTheory.Limits.MonoFactorisation.ext

/-- Any mono factorisation of `f` gives a mono factorisation of `f ≫ g` when `g` is a mono. -/
@[simps]
def compMono (F : MonoFactorisation f) {Y' : C} (g : Y ⟶ Y') [Mono g] : MonoFactorisation (f ≫ g)
    where
  i := F.i
  m := F.m ≫ g
  m_mono := mono_comp _ _
  e := F.e
#align category_theory.limits.mono_factorisation.comp_mono CategoryTheory.Limits.MonoFactorisation.compMono

/-- A mono factorisation of `f ≫ g`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
def ofCompIso {Y' : C} {g : Y ⟶ Y'} [IsIso g] (F : MonoFactorisation (f ≫ g)) : MonoFactorisation f
    where
  i := F.i
  m := F.m ≫ inv g
  m_mono := mono_comp _ _
  e := F.e
#align category_theory.limits.mono_factorisation.of_comp_iso CategoryTheory.Limits.MonoFactorisation.ofCompIso

/-- Any mono factorisation of `f` gives a mono factorisation of `g ≫ f`. -/
@[simps]
def isoComp (F : MonoFactorisation f) {X' : C} (g : X' ⟶ X) : MonoFactorisation (g ≫ f)
    where
  i := F.i
  m := F.m
  e := g ≫ F.e
#align category_theory.limits.mono_factorisation.iso_comp CategoryTheory.Limits.MonoFactorisation.isoComp

/-- A mono factorisation of `g ≫ f`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
def ofIsoComp {X' : C} (g : X' ⟶ X) [IsIso g] (F : MonoFactorisation (g ≫ f)) : MonoFactorisation f
    where
  i := F.i
  m := F.m
  e := inv g ≫ F.e
#align category_theory.limits.mono_factorisation.of_iso_comp CategoryTheory.Limits.MonoFactorisation.ofIsoComp

/-- If `f` and `g` are isomorphic arrows, then a mono factorisation of `f`
gives a mono factorisation of `g` -/
@[simps]
def ofArrowIso {f g : Arrow C} (F : MonoFactorisation f.Hom) (sq : f ⟶ g) [IsIso sq] :
    MonoFactorisation g.Hom where
  i := F.i
  m := F.m ≫ sq.right
  e := inv sq.left ≫ F.e
  m_mono := mono_comp _ _
  fac := by simp only [fac_assoc, arrow.w, is_iso.inv_comp_eq, category.assoc]
#align category_theory.limits.mono_factorisation.of_arrow_iso CategoryTheory.Limits.MonoFactorisation.ofArrowIso

end MonoFactorisation

variable {f}

/-- Data exhibiting that a given factorisation through a mono is initial. -/
structure IsImage (F : MonoFactorisation f) where
  lift : ∀ F' : MonoFactorisation f, F.i ⟶ F'.i
  lift_fac' : ∀ F' : MonoFactorisation f, lift F' ≫ F'.m = F.m := by obviously
#align category_theory.limits.is_image CategoryTheory.Limits.IsImage

restate_axiom is_image.lift_fac'

attribute [simp, reassoc.1] is_image.lift_fac

namespace IsImage

@[simp, reassoc.1]
theorem fac_lift {F : MonoFactorisation f} (hF : IsImage F) (F' : MonoFactorisation f) :
    F.e ≫ hF.lift F' = F'.e :=
  (cancel_mono F'.m).1 <| by simp
#align category_theory.limits.is_image.fac_lift CategoryTheory.Limits.IsImage.fac_lift

variable (f)

/-- The trivial factorisation of a monomorphism satisfies the universal property. -/
@[simps]
def self [Mono f] : IsImage (MonoFactorisation.self f) where lift F' := F'.e
#align category_theory.limits.is_image.self CategoryTheory.Limits.IsImage.self

instance [Mono f] : Inhabited (IsImage (MonoFactorisation.self f)) :=
  ⟨self f⟩

variable {f}

-- TODO this is another good candidate for a future `unique_up_to_canonical_iso`.
/-- Two factorisations through monomorphisms satisfying the universal property
must factor through isomorphic objects. -/
@[simps]
def isoExt {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F') : F.i ≅ F'.i
    where
  Hom := hF.lift F'
  inv := hF'.lift F
  hom_inv_id' := (cancel_mono F.m).1 (by simp)
  inv_hom_id' := (cancel_mono F'.m).1 (by simp)
#align category_theory.limits.is_image.iso_ext CategoryTheory.Limits.IsImage.isoExt

variable {F F' : MonoFactorisation f} (hF : IsImage F) (hF' : IsImage F')

theorem isoExt_hom_m : (isoExt hF hF').Hom ≫ F'.m = F.m := by simp
#align category_theory.limits.is_image.iso_ext_hom_m CategoryTheory.Limits.IsImage.isoExt_hom_m

theorem isoExt_inv_m : (isoExt hF hF').inv ≫ F.m = F'.m := by simp
#align category_theory.limits.is_image.iso_ext_inv_m CategoryTheory.Limits.IsImage.isoExt_inv_m

theorem e_isoExt_hom : F.e ≫ (isoExt hF hF').Hom = F'.e := by simp
#align category_theory.limits.is_image.e_iso_ext_hom CategoryTheory.Limits.IsImage.e_isoExt_hom

theorem e_isoExt_inv : F'.e ≫ (isoExt hF hF').inv = F.e := by simp
#align category_theory.limits.is_image.e_iso_ext_inv CategoryTheory.Limits.IsImage.e_isoExt_inv

/-- If `f` and `g` are isomorphic arrows, then a mono factorisation of `f` that is an image
gives a mono factorisation of `g` that is an image -/
@[simps]
def ofArrowIso {f g : Arrow C} {F : MonoFactorisation f.Hom} (hF : IsImage F) (sq : f ⟶ g)
    [IsIso sq] : IsImage (F.of_arrow_iso sq)
    where
  lift F' := hF.lift (F'.of_arrow_iso (inv sq))
  lift_fac' F' := by
    simpa only [mono_factorisation.of_arrow_iso_m, arrow.inv_right, ← category.assoc,
      is_iso.comp_inv_eq] using hF.lift_fac (F'.of_arrow_iso (inv sq))
#align category_theory.limits.is_image.of_arrow_iso CategoryTheory.Limits.IsImage.ofArrowIso

end IsImage

variable (f)

/-- Data exhibiting that a morphism `f` has an image. -/
structure ImageFactorisation (f : X ⟶ Y) where
  f : MonoFactorisation f
  IsImage : IsImage F
#align category_theory.limits.image_factorisation CategoryTheory.Limits.ImageFactorisation

namespace ImageFactorisation

instance [Mono f] : Inhabited (ImageFactorisation f) :=
  ⟨⟨_, IsImage.self f⟩⟩

/-- If `f` and `g` are isomorphic arrows, then an image factorisation of `f`
gives an image factorisation of `g` -/
@[simps]
def ofArrowIso {f g : Arrow C} (F : ImageFactorisation f.Hom) (sq : f ⟶ g) [IsIso sq] :
    ImageFactorisation g.Hom where
  f := F.f.of_arrow_iso sq
  IsImage := F.IsImage.of_arrow_iso sq
#align category_theory.limits.image_factorisation.of_arrow_iso CategoryTheory.Limits.ImageFactorisation.ofArrowIso

end ImageFactorisation

/-- `has_image f` means that there exists an image factorisation of `f`. -/
class HasImage (f : X ⟶ Y) : Prop where mk' ::
  exists_image : Nonempty (ImageFactorisation f)
#align category_theory.limits.has_image CategoryTheory.Limits.HasImage

theorem HasImage.mk {f : X ⟶ Y} (F : ImageFactorisation f) : HasImage f :=
  ⟨Nonempty.intro F⟩
#align category_theory.limits.has_image.mk CategoryTheory.Limits.HasImage.mk

theorem HasImage.of_arrow_iso {f g : Arrow C} [h : HasImage f.Hom] (sq : f ⟶ g) [IsIso sq] :
    HasImage g.Hom :=
  ⟨⟨h.exists_image.some.of_arrow_iso sq⟩⟩
#align category_theory.limits.has_image.of_arrow_iso CategoryTheory.Limits.HasImage.of_arrow_iso

instance (priority := 100) mono_hasImage (f : X ⟶ Y) [Mono f] : HasImage f :=
  HasImage.mk ⟨_, IsImage.self f⟩
#align category_theory.limits.mono_has_image CategoryTheory.Limits.mono_hasImage

section

variable [HasImage f]

/-- Some factorisation of `f` through a monomorphism (selected with choice). -/
def Image.monoFactorisation : MonoFactorisation f :=
  (Classical.choice HasImage.exists_image).f
#align category_theory.limits.image.mono_factorisation CategoryTheory.Limits.Image.monoFactorisation

/-- The witness of the universal property for the chosen factorisation of `f` through
a monomorphism. -/
def Image.isImage : IsImage (Image.monoFactorisation f) :=
  (Classical.choice HasImage.exists_image).IsImage
#align category_theory.limits.image.is_image CategoryTheory.Limits.Image.isImage

/-- The categorical image of a morphism. -/
def image : C :=
  (Image.monoFactorisation f).i
#align category_theory.limits.image CategoryTheory.Limits.image

/-- The inclusion of the image of a morphism into the target. -/
def image.ι : image f ⟶ Y :=
  (Image.monoFactorisation f).m
#align category_theory.limits.image.ι CategoryTheory.Limits.image.ι

@[simp]
theorem image.as_ι : (Image.monoFactorisation f).m = image.ι f :=
  rfl
#align category_theory.limits.image.as_ι CategoryTheory.Limits.image.as_ι

instance : Mono (image.ι f) :=
  (Image.monoFactorisation f).m_mono

/-- The map from the source to the image of a morphism. -/
def factorThruImage : X ⟶ image f :=
  (Image.monoFactorisation f).e
#align category_theory.limits.factor_thru_image CategoryTheory.Limits.factorThruImage

/-- Rewrite in terms of the `factor_thru_image` interface. -/
@[simp]
theorem as_factorThruImage : (Image.monoFactorisation f).e = factorThruImage f :=
  rfl
#align category_theory.limits.as_factor_thru_image CategoryTheory.Limits.as_factorThruImage

@[simp, reassoc.1]
theorem image.fac : factorThruImage f ≫ image.ι f = f :=
  (Image.monoFactorisation f).fac
#align category_theory.limits.image.fac CategoryTheory.Limits.image.fac

variable {f}

/-- Any other factorisation of the morphism `f` through a monomorphism receives a map from the
image. -/
def image.lift (F' : MonoFactorisation f) : image f ⟶ F'.i :=
  (Image.isImage f).lift F'
#align category_theory.limits.image.lift CategoryTheory.Limits.image.lift

@[simp, reassoc.1]
theorem image.lift_fac (F' : MonoFactorisation f) : image.lift F' ≫ F'.m = image.ι f :=
  (Image.isImage f).lift_fac' F'
#align category_theory.limits.image.lift_fac CategoryTheory.Limits.image.lift_fac

@[simp, reassoc.1]
theorem image.fac_lift (F' : MonoFactorisation f) : factorThruImage f ≫ image.lift F' = F'.e :=
  (Image.isImage f).fac_lift F'
#align category_theory.limits.image.fac_lift CategoryTheory.Limits.image.fac_lift

@[simp]
theorem image.isImage_lift (F : MonoFactorisation f) : (Image.isImage f).lift F = image.lift F :=
  rfl
#align category_theory.limits.image.is_image_lift CategoryTheory.Limits.image.isImage_lift

@[simp, reassoc.1]
theorem IsImage.lift_ι {F : MonoFactorisation f} (hF : IsImage F) :
    hF.lift (Image.monoFactorisation f) ≫ image.ι f = F.m :=
  hF.lift_fac _
#align category_theory.limits.is_image.lift_ι CategoryTheory.Limits.IsImage.lift_ι

-- TODO we could put a category structure on `mono_factorisation f`,
-- with the morphisms being `g : I ⟶ I'` commuting with the `m`s
-- (they then automatically commute with the `e`s)
-- and show that an `image_of f` gives an initial object there
-- (uniqueness of the lift comes for free).
instance image.lift_mono (F' : MonoFactorisation f) : Mono (image.lift F') :=
  by
  apply mono_of_mono _ F'.m
  simpa using mono_factorisation.m_mono _
#align category_theory.limits.image.lift_mono CategoryTheory.Limits.image.lift_mono

theorem HasImage.uniq (F' : MonoFactorisation f) (l : image f ⟶ F'.i) (w : l ≫ F'.m = image.ι f) :
    l = image.lift F' :=
  (cancel_mono F'.m).1 (by simp [w])
#align category_theory.limits.has_image.uniq CategoryTheory.Limits.HasImage.uniq

/-- If `has_image g`, then `has_image (f ≫ g)` when `f` is an isomorphism. -/
instance {X Y Z : C} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) [HasImage g] : HasImage (f ≫ g)
    where exists_image :=
    ⟨{  f :=
          { i := image g
            m := image.ι g
            e := f ≫ factorThruImage g }
        IsImage :=
          {
            lift := fun F' =>
              image.lift
                { i := F'.i
                  m := F'.m
                  e := inv f ≫ F'.e } } }⟩

end

section

variable (C)

/-- `has_images` asserts that every morphism has an image. -/
class HasImages : Prop where
  HasImage : ∀ {X Y : C} (f : X ⟶ Y), HasImage f
#align category_theory.limits.has_images CategoryTheory.Limits.HasImages

attribute [instance] has_images.has_image

end

section

variable (f)

/-- The image of a monomorphism is isomorphic to the source. -/
def imageMonoIsoSource [Mono f] : image f ≅ X :=
  IsImage.isoExt (Image.isImage f) (IsImage.self f)
#align category_theory.limits.image_mono_iso_source CategoryTheory.Limits.imageMonoIsoSource

@[simp, reassoc.1]
theorem imageMonoIsoSource_inv_ι [Mono f] : (imageMonoIsoSource f).inv ≫ image.ι f = f := by
  simp [image_mono_iso_source]
#align category_theory.limits.image_mono_iso_source_inv_ι CategoryTheory.Limits.imageMonoIsoSource_inv_ι

@[simp, reassoc.1]
theorem imageMonoIsoSource_hom_self [Mono f] : (imageMonoIsoSource f).Hom ≫ f = image.ι f :=
  by
  conv =>
    lhs
    congr
    skip
    rw [← image_mono_iso_source_inv_ι f]
  rw [← category.assoc, iso.hom_inv_id, category.id_comp]
#align category_theory.limits.image_mono_iso_source_hom_self CategoryTheory.Limits.imageMonoIsoSource_hom_self

-- This is the proof that `factor_thru_image f` is an epimorphism
-- from https://en.wikipedia.org/wiki/Image_%28category_theory%29, which is in turn taken from:
-- Mitchell, Barry (1965), Theory of categories, MR 0202787, p.12, Proposition 10.1
@[ext]
theorem image.ext [HasImage f] {W : C} {g h : image f ⟶ W} [HasLimit (parallelPair g h)]
    (w : factorThruImage f ≫ g = factorThruImage f ≫ h) : g = h :=
  by
  let q := equalizer.ι g h
  let e' := equalizer.lift _ w
  let F' : mono_factorisation f :=
    { i := equalizer g h
      m := q ≫ image.ι f
      m_mono := by apply mono_comp
      e := e' }
  let v := image.lift F'
  have t₀ : v ≫ q ≫ image.ι f = image.ι f := image.lift_fac F'
  have t : v ≫ q = 𝟙 (image f) :=
    (cancel_mono_id (image.ι f)).1
      (by
        convert t₀ using 1
        rw [category.assoc])
  -- The proof from wikipedia next proves `q ≫ v = 𝟙 _`,
  -- and concludes that `equalizer g h ≅ image f`,
  -- but this isn't necessary.
  calc
    g = 𝟙 (image f) ≫ g := by rw [category.id_comp]
    _ = v ≫ q ≫ g := by rw [← t, category.assoc]
    _ = v ≫ q ≫ h := by rw [equalizer.condition g h]
    _ = 𝟙 (image f) ≫ h := by rw [← category.assoc, t]
    _ = h := by rw [category.id_comp]
    
#align category_theory.limits.image.ext CategoryTheory.Limits.image.ext

instance [HasImage f] [∀ {Z : C} (g h : image f ⟶ Z), HasLimit (parallelPair g h)] :
    Epi (factorThruImage f) :=
  ⟨fun Z g h w => image.ext f w⟩

theorem epi_image_of_epi {X Y : C} (f : X ⟶ Y) [HasImage f] [E : Epi f] : Epi (image.ι f) :=
  by
  rw [← image.fac f] at E
  skip
  exact epi_of_epi (factor_thru_image f) (image.ι f)
#align category_theory.limits.epi_image_of_epi CategoryTheory.Limits.epi_image_of_epi

theorem epi_of_epi_image {X Y : C} (f : X ⟶ Y) [HasImage f] [Epi (image.ι f)]
    [Epi (factorThruImage f)] : Epi f :=
  by
  rw [← image.fac f]
  apply epi_comp
#align category_theory.limits.epi_of_epi_image CategoryTheory.Limits.epi_of_epi_image

end

section

variable {f} {f' : X ⟶ Y} [HasImage f] [HasImage f']

/-- An equation between morphisms gives a comparison map between the images
(which momentarily we prove is an iso).
-/
def image.eqToHom (h : f = f') : image f ⟶ image f' :=
  image.lift
    { i := image f'
      m := image.ι f'
      e := factorThruImage f' }
#align category_theory.limits.image.eq_to_hom CategoryTheory.Limits.image.eqToHom

instance (h : f = f') : IsIso (image.eqToHom h) :=
  ⟨⟨image.eqToHom h.symm,
      ⟨(cancel_mono (image.ι f)).1 (by simp [image.eq_to_hom]),
        (cancel_mono (image.ι f')).1 (by simp [image.eq_to_hom])⟩⟩⟩

/-- An equation between morphisms gives an isomorphism between the images. -/
def image.eqToIso (h : f = f') : image f ≅ image f' :=
  asIso (image.eqToHom h)
#align category_theory.limits.image.eq_to_iso CategoryTheory.Limits.image.eqToIso

/-- As long as the category has equalizers,
the image inclusion maps commute with `image.eq_to_iso`.
-/
theorem image.eq_fac [HasEqualizers C] (h : f = f') :
    image.ι f = (image.eqToIso h).Hom ≫ image.ι f' :=
  by
  ext
  simp [image.eq_to_iso, image.eq_to_hom]
#align category_theory.limits.image.eq_fac CategoryTheory.Limits.image.eq_fac

end

section

variable {Z : C} (g : Y ⟶ Z)

/-- The comparison map `image (f ≫ g) ⟶ image g`. -/
def image.preComp [HasImage g] [HasImage (f ≫ g)] : image (f ≫ g) ⟶ image g :=
  image.lift
    { i := image g
      m := image.ι g
      e := f ≫ factorThruImage g }
#align category_theory.limits.image.pre_comp CategoryTheory.Limits.image.preComp

@[simp, reassoc.1]
theorem image.preComp_ι [HasImage g] [HasImage (f ≫ g)] :
    image.preComp f g ≫ image.ι g = image.ι (f ≫ g) := by simp [image.pre_comp]
#align category_theory.limits.image.pre_comp_ι CategoryTheory.Limits.image.preComp_ι

@[simp, reassoc.1]
theorem image.factorThruImage_preComp [HasImage g] [HasImage (f ≫ g)] :
    factorThruImage (f ≫ g) ≫ image.preComp f g = f ≫ factorThruImage g := by simp [image.pre_comp]
#align category_theory.limits.image.factor_thru_image_pre_comp CategoryTheory.Limits.image.factorThruImage_preComp

/-- `image.pre_comp f g` is a monomorphism.
-/
instance image.preComp_mono [HasImage g] [HasImage (f ≫ g)] : Mono (image.preComp f g) :=
  by
  apply mono_of_mono _ (image.ι g)
  simp only [image.pre_comp_ι]
  infer_instance
#align category_theory.limits.image.pre_comp_mono CategoryTheory.Limits.image.preComp_mono

/-- The two step comparison map
  `image (f ≫ (g ≫ h)) ⟶ image (g ≫ h) ⟶ image h`
agrees with the one step comparison map
  `image (f ≫ (g ≫ h)) ≅ image ((f ≫ g) ≫ h) ⟶ image h`.
 -/
theorem image.preComp_comp {W : C} (h : Z ⟶ W) [HasImage (g ≫ h)] [HasImage (f ≫ g ≫ h)]
    [HasImage h] [HasImage ((f ≫ g) ≫ h)] :
    image.preComp f (g ≫ h) ≫ image.preComp g h =
      image.eqToHom (Category.assoc f g h).symm ≫ image.preComp (f ≫ g) h :=
  by
  apply (cancel_mono (image.ι h)).1
  simp [image.pre_comp, image.eq_to_hom]
#align category_theory.limits.image.pre_comp_comp CategoryTheory.Limits.image.preComp_comp

variable [HasEqualizers C]

/-- `image.pre_comp f g` is an epimorphism when `f` is an epimorphism
(we need `C` to have equalizers to prove this).
-/
instance image.preComp_epi_of_epi [HasImage g] [HasImage (f ≫ g)] [Epi f] :
    Epi (image.preComp f g) :=
  by
  apply epi_of_epi_fac (image.factor_thru_image_pre_comp _ _)
  exact epi_comp _ _
#align category_theory.limits.image.pre_comp_epi_of_epi CategoryTheory.Limits.image.preComp_epi_of_epi

instance hasImage_iso_comp [IsIso f] [HasImage g] : HasImage (f ≫ g) :=
  HasImage.mk
    { f := (Image.monoFactorisation g).isoComp f
      IsImage := { lift := fun F' => image.lift (F'.ofIsoComp f) } }
#align category_theory.limits.has_image_iso_comp CategoryTheory.Limits.hasImage_iso_comp

/-- `image.pre_comp f g` is an isomorphism when `f` is an isomorphism
(we need `C` to have equalizers to prove this).
-/
instance image.isIso_precomp_iso (f : X ⟶ Y) [IsIso f] [HasImage g] : IsIso (image.preComp f g) :=
  ⟨⟨image.lift
        { i := image (f ≫ g)
          m := image.ι (f ≫ g)
          e := inv f ≫ factorThruImage (f ≫ g) },
      ⟨by
        ext
        simp [image.pre_comp], by
        ext
        simp [image.pre_comp]⟩⟩⟩
#align category_theory.limits.image.is_iso_precomp_iso CategoryTheory.Limits.image.isIso_precomp_iso

-- Note that in general we don't have the other comparison map you might expect
-- `image f ⟶ image (f ≫ g)`.
instance hasImage_comp_iso [HasImage f] [IsIso g] : HasImage (f ≫ g) :=
  HasImage.mk
    { f := (Image.monoFactorisation f).comp_mono g
      IsImage := { lift := fun F' => image.lift F'.of_comp_iso } }
#align category_theory.limits.has_image_comp_iso CategoryTheory.Limits.hasImage_comp_iso

/-- Postcomposing by an isomorphism induces an isomorphism on the image. -/
def image.compIso [HasImage f] [IsIso g] : image f ≅ image (f ≫ g)
    where
  Hom := image.lift (Image.monoFactorisation (f ≫ g)).of_comp_iso
  inv := image.lift ((Image.monoFactorisation f).comp_mono g)
#align category_theory.limits.image.comp_iso CategoryTheory.Limits.image.compIso

@[simp, reassoc.1]
theorem image.compIso_hom_comp_image_ι [HasImage f] [IsIso g] :
    (image.compIso f g).Hom ≫ image.ι (f ≫ g) = image.ι f ≫ g :=
  by
  ext
  simp [image.comp_iso]
#align category_theory.limits.image.comp_iso_hom_comp_image_ι CategoryTheory.Limits.image.compIso_hom_comp_image_ι

@[simp, reassoc.1]
theorem image.compIso_inv_comp_image_ι [HasImage f] [IsIso g] :
    (image.compIso f g).inv ≫ image.ι f = image.ι (f ≫ g) ≫ inv g :=
  by
  ext
  simp [image.comp_iso]
#align category_theory.limits.image.comp_iso_inv_comp_image_ι CategoryTheory.Limits.image.compIso_inv_comp_image_ι

end

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

instance {X Y : C} (f : X ⟶ Y) [HasImage f] : HasImage (Arrow.mk f).Hom :=
  show HasImage f by infer_instance

end

section HasImageMap

/-- An image map is a morphism `image f → image g` fitting into a commutative square and satisfying
    the obvious commutativity conditions. -/
structure ImageMap {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] (sq : f ⟶ g) where
  map : image f.Hom ⟶ image g.Hom
  map_ι' : map ≫ image.ι g.Hom = image.ι f.Hom ≫ sq.right := by obviously
#align category_theory.limits.image_map CategoryTheory.Limits.ImageMap

instance inhabitedImageMap {f : Arrow C} [HasImage f.Hom] : Inhabited (ImageMap (𝟙 f)) :=
  ⟨⟨𝟙 _, by tidy⟩⟩
#align category_theory.limits.inhabited_image_map CategoryTheory.Limits.inhabitedImageMap

restate_axiom image_map.map_ι'

attribute [simp, reassoc.1] image_map.map_ι

@[simp, reassoc.1]
theorem ImageMap.factor_map {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] (sq : f ⟶ g)
    (m : ImageMap sq) : factorThruImage f.Hom ≫ m.map = sq.left ≫ factorThruImage g.Hom :=
  (cancel_mono (image.ι g.Hom)).1 <| by simp
#align category_theory.limits.image_map.factor_map CategoryTheory.Limits.ImageMap.factor_map

/-- To give an image map for a commutative square with `f` at the top and `g` at the bottom, it
    suffices to give a map between any mono factorisation of `f` and any image factorisation of
    `g`. -/
def ImageMap.transport {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] (sq : f ⟶ g)
    (F : MonoFactorisation f.Hom) {F' : MonoFactorisation g.Hom} (hF' : IsImage F')
    {map : F.i ⟶ F'.i} (map_ι : map ≫ F'.m = F.m ≫ sq.right) : ImageMap sq
    where
  map := image.lift F ≫ map ≫ hF'.lift (Image.monoFactorisation g.Hom)
  map_ι' := by simp [map_ι]
#align category_theory.limits.image_map.transport CategoryTheory.Limits.ImageMap.transport

/-- `has_image_map sq` means that there is an `image_map` for the square `sq`. -/
class HasImageMap {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] (sq : f ⟶ g) : Prop where mk' ::
  HasImageMap : Nonempty (ImageMap sq)
#align category_theory.limits.has_image_map CategoryTheory.Limits.HasImageMap

theorem HasImageMap.mk {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] {sq : f ⟶ g}
    (m : ImageMap sq) : HasImageMap sq :=
  ⟨Nonempty.intro m⟩
#align category_theory.limits.has_image_map.mk CategoryTheory.Limits.HasImageMap.mk

theorem HasImageMap.transport {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] (sq : f ⟶ g)
    (F : MonoFactorisation f.Hom) {F' : MonoFactorisation g.Hom} (hF' : IsImage F')
    (map : F.i ⟶ F'.i) (map_ι : map ≫ F'.m = F.m ≫ sq.right) : HasImageMap sq :=
  HasImageMap.mk <| ImageMap.transport sq F hF' map_ι
#align category_theory.limits.has_image_map.transport CategoryTheory.Limits.HasImageMap.transport

/-- Obtain an `image_map` from a `has_image_map` instance. -/
def HasImageMap.imageMap {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] (sq : f ⟶ g)
    [HasImageMap sq] : ImageMap sq :=
  Classical.choice <| @HasImageMap.hasImageMap _ _ _ _ _ _ sq _
#align category_theory.limits.has_image_map.image_map CategoryTheory.Limits.HasImageMap.imageMap

-- see Note [lower instance priority]
instance (priority := 100) hasImageMapOfIsIso {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom]
    (sq : f ⟶ g) [IsIso sq] : HasImageMap sq :=
  HasImageMap.mk
    { map := image.lift ((Image.monoFactorisation g.Hom).of_arrow_iso (inv sq))
      map_ι' := by
        erw [← cancel_mono (inv sq).right, category.assoc, ← mono_factorisation.of_arrow_iso_m,
          image.lift_fac, category.assoc, ← comma.comp_right, is_iso.hom_inv_id, comma.id_right,
          category.comp_id] }
#align category_theory.limits.has_image_map_of_is_iso CategoryTheory.Limits.hasImageMapOfIsIso

instance HasImageMap.comp {f g h : Arrow C} [HasImage f.Hom] [HasImage g.Hom] [HasImage h.Hom]
    (sq1 : f ⟶ g) (sq2 : g ⟶ h) [HasImageMap sq1] [HasImageMap sq2] : HasImageMap (sq1 ≫ sq2) :=
  HasImageMap.mk
    { map := (HasImageMap.imageMap sq1).map ≫ (HasImageMap.imageMap sq2).map
      map_ι' := by
        simp only [image_map.map_ι, image_map.map_ι_assoc, comma.comp_right, category.assoc] }
#align category_theory.limits.has_image_map.comp CategoryTheory.Limits.HasImageMap.comp

variable {f g : Arrow C} [HasImage f.Hom] [HasImage g.Hom] (sq : f ⟶ g)

section

attribute [local ext] image_map

instance : Subsingleton (ImageMap sq) :=
  Subsingleton.intro fun a b =>
    ImageMap.ext a b <| (cancel_mono (image.ι g.Hom)).1 <| by simp only [image_map.map_ι]

end

variable [HasImageMap sq]

/-- The map on images induced by a commutative square. -/
abbrev image.map : image f.Hom ⟶ image g.Hom :=
  (HasImageMap.imageMap sq).map
#align category_theory.limits.image.map CategoryTheory.Limits.image.map

theorem image.factor_map : factorThruImage f.Hom ≫ image.map sq = sq.left ≫ factorThruImage g.Hom :=
  by simp
#align category_theory.limits.image.factor_map CategoryTheory.Limits.image.factor_map

theorem image.map_ι : image.map sq ≫ image.ι g.Hom = image.ι f.Hom ≫ sq.right := by simp
#align category_theory.limits.image.map_ι CategoryTheory.Limits.image.map_ι

theorem image.map_homMk'_ι {X Y P Q : C} {k : X ⟶ Y} [HasImage k] {l : P ⟶ Q} [HasImage l]
    {m : X ⟶ P} {n : Y ⟶ Q} (w : m ≫ l = k ≫ n) [HasImageMap (Arrow.homMk' w)] :
    image.map (Arrow.homMk' w) ≫ image.ι l = image.ι k ≫ n :=
  image.map_ι _
#align category_theory.limits.image.map_hom_mk'_ι CategoryTheory.Limits.image.map_homMk'_ι

section

variable {h : Arrow C} [HasImage h.Hom] (sq' : g ⟶ h)

variable [HasImageMap sq']

/-- Image maps for composable commutative squares induce an image map in the composite square. -/
def imageMapComp : ImageMap (sq ≫ sq') where map := image.map sq ≫ image.map sq'
#align category_theory.limits.image_map_comp CategoryTheory.Limits.imageMapComp

@[simp]
theorem image.map_comp [HasImageMap (sq ≫ sq')] :
    image.map (sq ≫ sq') = image.map sq ≫ image.map sq' :=
  show (HasImageMap.imageMap (sq ≫ sq')).map = (imageMapComp sq sq').map by congr
#align category_theory.limits.image.map_comp CategoryTheory.Limits.image.map_comp

end

section

variable (f)

/-- The identity `image f ⟶ image f` fits into the commutative square represented by the identity
    morphism `𝟙 f` in the arrow category. -/
def imageMapId : ImageMap (𝟙 f) where map := 𝟙 (image f.Hom)
#align category_theory.limits.image_map_id CategoryTheory.Limits.imageMapId

@[simp]
theorem image.map_id [HasImageMap (𝟙 f)] : image.map (𝟙 f) = 𝟙 (image f.Hom) :=
  show (HasImageMap.imageMap (𝟙 f)).map = (imageMapId f).map by congr
#align category_theory.limits.image.map_id CategoryTheory.Limits.image.map_id

end

end HasImageMap

section

variable (C) [HasImages C]

/-- If a category `has_image_maps`, then all commutative squares induce morphisms on images. -/
class HasImageMaps where
  HasImageMap : ∀ {f g : Arrow C} (st : f ⟶ g), HasImageMap st
#align category_theory.limits.has_image_maps CategoryTheory.Limits.HasImageMaps

attribute [instance] has_image_maps.has_image_map

end

section HasImageMaps

variable [HasImages C] [HasImageMaps C]

/-- The functor from the arrow category of `C` to `C` itself that maps a morphism to its image
    and a commutative square to the induced morphism on images. -/
@[simps]
def im : Arrow C ⥤ C where
  obj f := image f.Hom
  map _ _ st := image.map st
#align category_theory.limits.im CategoryTheory.Limits.im

end HasImageMaps

section StrongEpiMonoFactorisation

/-- A strong epi-mono factorisation is a decomposition `f = e ≫ m` with `e` a strong epimorphism
    and `m` a monomorphism. -/
structure StrongEpiMonoFactorisation {X Y : C} (f : X ⟶ Y) extends MonoFactorisation f where
  [e_strongEpi : StrongEpi e]
#align category_theory.limits.strong_epi_mono_factorisation CategoryTheory.Limits.StrongEpiMonoFactorisation

attribute [instance] strong_epi_mono_factorisation.e_strong_epi

/-- Satisfying the inhabited linter -/
instance strongEpiMonoFactorisationInhabited {X Y : C} (f : X ⟶ Y) [StrongEpi f] :
    Inhabited (StrongEpiMonoFactorisation f) :=
  ⟨⟨⟨Y, 𝟙 Y, f, by simp⟩⟩⟩
#align category_theory.limits.strong_epi_mono_factorisation_inhabited CategoryTheory.Limits.strongEpiMonoFactorisationInhabited

/-- A mono factorisation coming from a strong epi-mono factorisation always has the universal
    property of the image. -/
def StrongEpiMonoFactorisation.toMonoIsImage {X Y : C} {f : X ⟶ Y}
    (F : StrongEpiMonoFactorisation f) : IsImage F.toMonoFactorisation
    where lift G :=
    (CommSq.mk (show G.e ≫ G.m = F.e ≫ F.m by rw [F.to_mono_factorisation.fac, G.fac])).lift
#align category_theory.limits.strong_epi_mono_factorisation.to_mono_is_image CategoryTheory.Limits.StrongEpiMonoFactorisation.toMonoIsImage

variable (C)

/-- A category has strong epi-mono factorisations if every morphism admits a strong epi-mono
    factorisation. -/
class HasStrongEpiMonoFactorisations : Prop where mk' ::
  has_fac : ∀ {X Y : C} (f : X ⟶ Y), Nonempty (StrongEpiMonoFactorisation f)
#align category_theory.limits.has_strong_epi_mono_factorisations CategoryTheory.Limits.HasStrongEpiMonoFactorisations

variable {C}

theorem HasStrongEpiMonoFactorisations.mk
    (d : ∀ {X Y : C} (f : X ⟶ Y), StrongEpiMonoFactorisation f) :
    HasStrongEpiMonoFactorisations C :=
  ⟨fun X Y f => Nonempty.intro <| d f⟩
#align category_theory.limits.has_strong_epi_mono_factorisations.mk CategoryTheory.Limits.HasStrongEpiMonoFactorisations.mk

instance (priority := 100) hasImages_of_hasStrongEpiMonoFactorisations
    [HasStrongEpiMonoFactorisations C] : HasImages C
    where HasImage X Y f :=
    let F' := Classical.choice (HasStrongEpiMonoFactorisations.has_fac f)
    HasImage.mk
      { f := F'.toMonoFactorisation
        IsImage := F'.toMonoIsImage }
#align category_theory.limits.has_images_of_has_strong_epi_mono_factorisations CategoryTheory.Limits.hasImages_of_hasStrongEpiMonoFactorisations

end StrongEpiMonoFactorisation

section HasStrongEpiImages

variable (C) [HasImages C]

/-- A category has strong epi images if it has all images and `factor_thru_image f` is a strong
    epimorphism for all `f`. -/
class HasStrongEpiImages : Prop where
  strong_factorThruImage : ∀ {X Y : C} (f : X ⟶ Y), StrongEpi (factorThruImage f)
#align category_theory.limits.has_strong_epi_images CategoryTheory.Limits.HasStrongEpiImages

attribute [instance] has_strong_epi_images.strong_factor_thru_image

end HasStrongEpiImages

section HasStrongEpiImages

/-- If there is a single strong epi-mono factorisation of `f`, then every image factorisation is a
    strong epi-mono factorisation. -/
theorem strongEpi_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y}
    (F : StrongEpiMonoFactorisation f) {F' : MonoFactorisation f} (hF' : IsImage F') :
    StrongEpi F'.e := by
  rw [← is_image.e_iso_ext_hom F.to_mono_is_image hF']
  apply strong_epi_comp
#align category_theory.limits.strong_epi_of_strong_epi_mono_factorisation CategoryTheory.Limits.strongEpi_of_strongEpiMonoFactorisation

theorem strongEpi_factorThruImage_of_strongEpiMonoFactorisation {X Y : C} {f : X ⟶ Y} [HasImage f]
    (F : StrongEpiMonoFactorisation f) : StrongEpi (factorThruImage f) :=
  strongEpi_of_strongEpiMonoFactorisation F <| Image.isImage f
#align category_theory.limits.strong_epi_factor_thru_image_of_strong_epi_mono_factorisation CategoryTheory.Limits.strongEpi_factorThruImage_of_strongEpiMonoFactorisation

/-- If we constructed our images from strong epi-mono factorisations, then these images are
    strong epi images. -/
instance (priority := 100) hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
    [HasStrongEpiMonoFactorisations C] : HasStrongEpiImages C
    where strong_factorThruImage X Y f :=
    strongEpi_factorThruImage_of_strongEpiMonoFactorisation <|
      Classical.choice <| HasStrongEpiMonoFactorisations.has_fac f
#align category_theory.limits.has_strong_epi_images_of_has_strong_epi_mono_factorisations CategoryTheory.Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

end HasStrongEpiImages

section HasStrongEpiImages

variable [HasImages C]

/-- A category with strong epi images has image maps. -/
instance (priority := 100) hasImageMapsOfHasStrongEpiImages [HasStrongEpiImages C] : HasImageMaps C
    where HasImageMap f g st :=
    HasImageMap.mk
      {
        map :=
          (CommSq.mk
              (show
                (st.left ≫ factorThruImage g.Hom) ≫ image.ι g.Hom =
                  factorThruImage f.Hom ≫ image.ι f.Hom ≫ st.right
                by simp)).lift }
#align category_theory.limits.has_image_maps_of_has_strong_epi_images CategoryTheory.Limits.hasImageMapsOfHasStrongEpiImages

/-- If a category has images, equalizers and pullbacks, then images are automatically strong epi
    images. -/
instance (priority := 100) hasStrongEpiImages_of_hasPullbacks_of_hasEqualizers [HasPullbacks C]
    [HasEqualizers C] : HasStrongEpiImages C
    where strong_factorThruImage X Y f :=
    StrongEpi.mk' fun A B h h_mono x y sq =>
      CommSq.HasLift.mk'
        { l :=
            image.lift
                { i := pullback h y
                  m := pullback.snd ≫ image.ι f
                  m_mono := mono_comp _ _
                  e := pullback.lift _ _ sq.w } ≫
              pullback.fst
          fac_left' := by simp only [image.fac_lift_assoc, pullback.lift_fst]
          fac_right' := by
            ext
            simp only [sq.w, category.assoc, image.fac_lift_assoc, pullback.lift_fst_assoc] }
#align category_theory.limits.has_strong_epi_images_of_has_pullbacks_of_has_equalizers CategoryTheory.Limits.hasStrongEpiImages_of_hasPullbacks_of_hasEqualizers

end HasStrongEpiImages

variable [HasStrongEpiMonoFactorisations C]

variable {X Y : C} {f : X ⟶ Y}

/--
If `C` has strong epi mono factorisations, then the image is unique up to isomorphism, in that if
`f` factors as a strong epi followed by a mono, this factorisation is essentially the image
factorisation.
-/
def image.isoStrongEpiMono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f) [StrongEpi e]
    [Mono m] : I' ≅ image f :=
  IsImage.isoExt
      {   i := I'
          m
          e }.toMonoIsImage <|
    Image.isImage f
#align category_theory.limits.image.iso_strong_epi_mono CategoryTheory.Limits.image.isoStrongEpiMono

@[simp]
theorem image.isoStrongEpiMono_hom_comp_ι {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
    [StrongEpi e] [Mono m] : (image.isoStrongEpiMono e m comm).Hom ≫ image.ι f = m :=
  IsImage.lift_fac _ _
#align category_theory.limits.image.iso_strong_epi_mono_hom_comp_ι CategoryTheory.Limits.image.isoStrongEpiMono_hom_comp_ι

@[simp]
theorem image.isoStrongEpiMono_inv_comp_mono {I' : C} (e : X ⟶ I') (m : I' ⟶ Y) (comm : e ≫ m = f)
    [StrongEpi e] [Mono m] : (image.isoStrongEpiMono e m comm).inv ≫ m = image.ι f :=
  image.lift_fac _
#align category_theory.limits.image.iso_strong_epi_mono_inv_comp_mono CategoryTheory.Limits.image.isoStrongEpiMono_inv_comp_mono

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {C D : Type _} [Category C] [Category D]

theorem hasStrongEpiMonoFactorisations_imp_of_isEquivalence (F : C ⥤ D) [IsEquivalence F]
    [h : HasStrongEpiMonoFactorisations C] : HasStrongEpiMonoFactorisations D :=
  ⟨fun X Y f =>
    by
    let em : strong_epi_mono_factorisation (F.inv.map f) :=
      (has_strong_epi_mono_factorisations.has_fac (F.inv.map f)).some
    haveI : mono (F.map em.m ≫ F.as_equivalence.counit_iso.hom.app Y) := mono_comp _ _
    haveI : strong_epi (F.as_equivalence.counit_iso.inv.app X ≫ F.map em.e) := strong_epi_comp _ _
    exact
      Nonempty.intro
        { i := F.obj em.I
          e := F.as_equivalence.counit_iso.inv.app X ≫ F.map em.e
          m := F.map em.m ≫ F.as_equivalence.counit_iso.hom.app Y
          fac := by
            simpa only [category.assoc, ← F.map_comp_assoc, em.fac', is_equivalence.fun_inv_map,
              iso.inv_hom_id_app, iso.inv_hom_id_app_assoc] using category.comp_id _ }⟩
#align category_theory.functor.has_strong_epi_mono_factorisations_imp_of_is_equivalence CategoryTheory.Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence

end CategoryTheory.Functor

