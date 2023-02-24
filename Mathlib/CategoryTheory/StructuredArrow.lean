/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison

! This file was ported from Lean 3 source module category_theory.structured_arrow
! leanprover-community/mathlib commit fef8efdf78f223294c34a41875923ab1272322d4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Punit
import Mathlib.CategoryTheory.Comma
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : C`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/


namespace CategoryTheory

-- morphism levels before object levels. See note [CategoryTheory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`),
has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
-- @[nolint has_nonempty_instance]
def StructuredArrow (S : D) (T : C ⥤ D) :=
  Comma (Functor.fromPUnit S) T 
#align category_theory.structured_arrow CategoryTheory.StructuredArrow

-- Porting note: not found by inferInstance
instance (S : D) (T : C ⥤ D) : Category (StructuredArrow S T) := commaCategory  

namespace StructuredArrow

/-- The obvious projection functor from structured arrows. -/
@[simps!]
def proj (S : D) (T : C ⥤ D) : StructuredArrow S T ⥤ C :=
  Comma.snd _ _
#align category_theory.structured_arrow.proj CategoryTheory.StructuredArrow.proj

variable {S S' S'' : D} {Y Y' : C} {T : C ⥤ D}

/-- Construct a structured arrow from a morphism. -/
def mk (f : S ⟶ T.obj Y) : StructuredArrow S T :=
  ⟨⟨⟨⟩⟩, Y, f⟩
#align category_theory.structured_arrow.mk CategoryTheory.StructuredArrow.mk

@[simp]
theorem mk_left (f : S ⟶ T.obj Y) : (mk f).left = ⟨⟨⟩⟩ :=
  rfl
#align category_theory.structured_arrow.mk_left CategoryTheory.StructuredArrow.mk_left

@[simp]
theorem mk_right (f : S ⟶ T.obj Y) : (mk f).right = Y :=
  rfl
#align category_theory.structured_arrow.mk_right CategoryTheory.StructuredArrow.mk_right

@[simp]
theorem mk_hom_eq_self (f : S ⟶ T.obj Y) : (mk f).hom = f :=
  rfl
#align category_theory.structured_arrow.mk_hom_eq_self CategoryTheory.StructuredArrow.mk_hom_eq_self

@[reassoc (attr := simp)]
theorem w {A B : StructuredArrow S T} (f : A ⟶ B) : A.hom ≫ T.map f.right = B.hom := by
  have := f.w ; aesop_cat
#align category_theory.structured_arrow.w CategoryTheory.StructuredArrow.w

/-- To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def homMk {f f' : StructuredArrow S T} (g : f.right ⟶ f'.right) (w : f.hom ≫ T.map g = f'.hom) :
    f ⟶ f' where
  left := eqToHom (by ext)
  right := g
  w := by
    dsimp
    simpa using w.symm
#align category_theory.structured_arrow.hom_mk CategoryTheory.StructuredArrow.homMk

/-- Given a structured arrow `X ⟶ F(U)`, and an arrow `U ⟶ Y`, we can construct a morphism of
structured arrow given by `(X ⟶ F(U)) ⟶ (X ⟶ F(U) ⟶ F(Y))`.
-/
def homMk' {F : C ⥤ D} {X : D} {Y : C} (U : StructuredArrow X F) (f : U.right ⟶ Y) :
    U ⟶ mk (U.hom ≫ F.map f) where 
  left := by cases U.left; exact 𝟙 _   
  right := f
#align category_theory.structured_arrow.hom_mk' CategoryTheory.StructuredArrow.homMk'

/-- To construct an isomorphism of structured arrows,
we need an isomorphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps!]
def isoMk {f f' : StructuredArrow S T} (g : f.right ≅ f'.right) (w : f.hom ≫ T.map g.hom = f'.hom) :
    f ≅ f' :=
  Comma.isoMk (eqToIso (by ext)) g (by simpa [eqToHom_map] using w.symm)
#align category_theory.structured_arrow.iso_mk CategoryTheory.StructuredArrow.isoMk

theorem ext {A B : StructuredArrow S T} (f g : A ⟶ B) : f.right = g.right → f = g := 
  have : Subsingleton (A.left ⟶  B.left) := sorry
  CommaMorphism.ext _ _ (Subsingleton.elim _ _)
#align category_theory.structured_arrow.ext CategoryTheory.StructuredArrow.ext

theorem ext_iff {A B : StructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.right = g.right :=
  ⟨fun h => h ▸ rfl, ext f g⟩
#align category_theory.structured_arrow.ext_iff CategoryTheory.StructuredArrow.ext_iff

instance proj_faithful : Faithful (proj S T) where 
  map_injective {_ _} := ext
#align category_theory.structured_arrow.proj_faithful CategoryTheory.StructuredArrow.proj_faithful

/-- The converse of this is true with additional assumptions, see `mono_iff_mono_right`. -/
theorem mono_of_mono_right {A B : StructuredArrow S T} (f : A ⟶ B) [h : Mono f.right] : Mono f :=
  (proj S T).mono_of_mono_map h
#align category_theory.structured_arrow.mono_of_mono_right CategoryTheory.StructuredArrow.mono_of_mono_right

theorem epi_of_epi_right {A B : StructuredArrow S T} (f : A ⟶ B) [h : Epi f.right] : Epi f :=
  (proj S T).epi_of_epi_map h
#align category_theory.structured_arrow.epi_of_epi_right CategoryTheory.StructuredArrow.epi_of_epi_right

instance mono_homMk {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Mono f] :
    Mono (homMk f w) :=
  (proj S T).mono_of_mono_map h
#align category_theory.structured_arrow.mono_hom_mk CategoryTheory.StructuredArrow.mono_homMk

instance epi_homMk {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Epi f] :
    Epi (homMk f w) :=
  (proj S T).epi_of_epi_map h
#align category_theory.structured_arrow.epi_hom_mk CategoryTheory.StructuredArrow.epi_homMk

/-- Eta rule for structured arrows. Prefer `structured_arrow.eta`, since equality of objects tends
    to cause problems. -/
theorem eq_mk (f : StructuredArrow S T) : f = mk f.hom := by
  cases f
  congr
#align category_theory.structured_arrow.eq_mk CategoryTheory.StructuredArrow.eq_mk

/-- Eta rule for structured arrows. -/
@[simps!]
def eta (f : StructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _) (by aesop_cat)
#align category_theory.structured_arrow.eta CategoryTheory.StructuredArrow.eta

/-- A morphism between source objects `S ⟶ S'`
contravariantly induces a functor between structured arrows,
`structured_arrow S' T ⥤ structured_arrow S T`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps!]
def map (f : S ⟶ S') : StructuredArrow S' T ⥤ StructuredArrow S T :=
  Comma.mapLeft _ ((Functor.const _).map f)
#align category_theory.structured_arrow.map CategoryTheory.StructuredArrow.map

@[simp]
theorem map_mk {f : S' ⟶ T.obj Y} (g : S ⟶ S') : (map g).obj (mk f) = mk (g ≫ f) :=
  rfl
#align category_theory.structured_arrow.map_mk CategoryTheory.StructuredArrow.map_mk

@[simp]
theorem map_id {f : StructuredArrow S T} : (map (𝟙 S)).obj f = f := by
  rw [eq_mk f]
  simp
#align category_theory.structured_arrow.map_id CategoryTheory.StructuredArrow.map_id

@[simp]
theorem map_comp {f : S ⟶ S'} {f' : S' ⟶ S''} {h : StructuredArrow S'' T} :
    (map (f ≫ f')).obj h = (map f).obj ((map f').obj h) := by
  rw [eq_mk h]
  simp
#align category_theory.structured_arrow.map_comp CategoryTheory.StructuredArrow.map_comp

instance proj_reflects_iso : ReflectsIsomorphisms (proj S T) where 
  reflects {Y Z} f t :=
    ⟨⟨StructuredArrow.homMk (inv ((proj S T).map f)) (by simp), by aesop_cat⟩⟩
#align category_theory.structured_arrow.proj_reflects_iso CategoryTheory.StructuredArrow.proj_reflects_iso

open CategoryTheory.Limits

-- attribute [local tidy] tactic.discrete_cases

/-- The identity structured arrow is initial. -/
def mkIdInitial [Full T] [Faithful T] : IsInitial (mk (𝟙 (T.obj Y))) where
  desc c :=
    homMk (T.preimage c.X.hom)
      (by
        dsimp
        simp)
  fac := fun _ ⟨a⟩ => by cases a
  uniq c m _ := by
    apply CommaMorphism.ext
    · aesop_cat
    · apply T.map_injective
      simpa only [homMk_right, T.image_preimage, ← w m] using (Category.id_comp _).symm
#align category_theory.structured_arrow.mk_id_initial CategoryTheory.StructuredArrow.mkIdInitial

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(S, F ⋙ G) ⥤ (S, G)`. -/
@[simps!]
def pre (S : D) (F : B ⥤ C) (G : C ⥤ D) : StructuredArrow S (F ⋙ G) ⥤ StructuredArrow S G :=
  Comma.preRight _ F G
#align category_theory.structured_arrow.pre CategoryTheory.StructuredArrow.pre

/-- The functor `(S, F) ⥤ (G(S), F ⋙ G)`. -/
@[simps]
def post (S : C) (F : B ⥤ C) (G : C ⥤ D) : StructuredArrow S F ⥤ StructuredArrow (G.obj S) (F ⋙ G)
    where
  obj X :=
    { left := ⟨⟨⟩⟩ 
      right := X.right
      hom := G.map X.hom }
  map f :=
    { left := 𝟙 ⟨⟨⟩⟩ 
      right := f.right
      w := by simp [Functor.comp_map, ← G.map_comp, ← f.w] }
#align category_theory.structured_arrow.post CategoryTheory.StructuredArrow.post

instance small_proj_preimage_of_locallySmall {𝒢 : Set C} [Small.{v₁} 𝒢] [LocallySmall.{v₁} D] :
    Small.{v₁} ((proj S T).obj ⁻¹' 𝒢) := by
  suffices (proj S T).obj ⁻¹' 𝒢 = Set.range fun f : ΣG : 𝒢, S ⟶ T.obj G => mk f.2
    by
    rw [this]
    infer_instance
  exact Set.ext fun X => ⟨fun h => ⟨⟨⟨_, h⟩, X.hom⟩, (eq_mk _).symm⟩, by aesop_cat⟩
#align category_theory.structured_arrow.small_proj_preimage_of_locally_small CategoryTheory.StructuredArrow.small_proj_preimage_of_locallySmall

end StructuredArrow

/-- The category of `S`-costructured arrows with target `T : D` (here `S : C ⥤ D`),
has as its objects `D`-morphisms of the form `S Y ⟶ T`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
-- @[nolint has_nonempty_instance] -- Porting note: removed
def CostructuredArrow (S : C ⥤ D) (T : D) :=
  Comma S (Functor.fromPUnit T)
#align category_theory.costructured_arrow CategoryTheory.CostructuredArrow

instance (S : C ⥤ D) (T : D) : Category (CostructuredArrow S T) := commaCategory

namespace CostructuredArrow

/-- The obvious projection functor from costructured arrows. -/
@[simps!]
def proj (S : C ⥤ D) (T : D) : CostructuredArrow S T ⥤ C :=
  Comma.fst _ _
#align category_theory.costructured_arrow.proj CategoryTheory.CostructuredArrow.proj

variable {T T' T'' : D} {Y Y' : C} {S : C ⥤ D}

/-- Construct a costructured arrow from a morphism. -/
def mk (f : S.obj Y ⟶ T) : CostructuredArrow S T :=
  ⟨Y, ⟨⟨⟩⟩, f⟩
#align category_theory.costructured_arrow.mk CategoryTheory.CostructuredArrow.mk

@[simp]
theorem mk_left (f : S.obj Y ⟶ T) : (mk f).left = Y :=
  rfl
#align category_theory.costructured_arrow.mk_left CategoryTheory.CostructuredArrow.mk_left

@[simp]
theorem mk_right (f : S.obj Y ⟶ T) : (mk f).right = ⟨⟨⟩⟩ :=
  rfl
#align category_theory.costructured_arrow.mk_right CategoryTheory.CostructuredArrow.mk_right

@[simp]
theorem mk_hom_eq_self (f : S.obj Y ⟶ T) : (mk f).hom = f :=
  rfl
#align category_theory.costructured_arrow.mk_hom_eq_self CategoryTheory.CostructuredArrow.mk_hom_eq_self

@[reassoc (attr := simp)]
theorem w {A B : CostructuredArrow S T} (f : A ⟶ B) : S.map f.left ≫ B.hom = A.hom := by aesop_cat
#align category_theory.costructured_arrow.w CategoryTheory.CostructuredArrow.w

/-- To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps!]
def homMk {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left) (w : S.map g ≫ f'.hom = f.hom) :
    f ⟶ f' where
  left := g
  right := eqToHom (by ext)
  w := by simpa [eqToHom_map] using w
#align category_theory.costructured_arrow.hom_mk CategoryTheory.CostructuredArrow.homMk

/-- To construct an isomorphism of costructured arrows,
we need an isomorphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps!]
def isoMk {f f' : CostructuredArrow S T} (g : f.left ≅ f'.left) (w : S.map g.hom ≫ f'.hom = f.hom) :
    f ≅ f' :=
  Comma.isoMk g (eqToIso (by ext)) (by simpa [eqToHom_map] using w)
#align category_theory.costructured_arrow.iso_mk CategoryTheory.CostructuredArrow.isoMk

theorem ext {A B : CostructuredArrow S T} (f g : A ⟶ B) (h : f.left = g.left) : f = g :=
  CommaMorphism.ext _ _ h (Subsingleton.elim _ _)
#align category_theory.costructured_arrow.ext CategoryTheory.CostructuredArrow.ext

theorem ext_iff {A B : CostructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.left = g.left :=
  ⟨fun h => h ▸ rfl, ext f g⟩
#align category_theory.costructured_arrow.ext_iff CategoryTheory.CostructuredArrow.ext_iff

instance proj_faithful : Faithful (proj S T) where map_injective {_ _} := ext
#align category_theory.costructured_arrow.proj_faithful CategoryTheory.CostructuredArrow.proj_faithful

theorem mono_of_mono_left {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Mono f.left] : Mono f :=
  (proj S T).mono_of_mono_map h
#align category_theory.costructured_arrow.mono_of_mono_left CategoryTheory.CostructuredArrow.mono_of_mono_left

/-- The converse of this is true with additional assumptions, see `epi_iff_epi_left`. -/
theorem epi_of_epi_left {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Epi f.left] : Epi f :=
  (proj S T).epi_of_epi_map h
#align category_theory.costructured_arrow.epi_of_epi_left CategoryTheory.CostructuredArrow.epi_of_epi_left

instance mono_homMk {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Mono f] :
    Mono (homMk f w) :=
  (proj S T).mono_of_mono_map h
#align category_theory.costructured_arrow.mono_hom_mk CategoryTheory.CostructuredArrow.mono_homMk

instance epi_homMk {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Epi f] :
    Epi (homMk f w) :=
  (proj S T).epi_of_epi_map h
#align category_theory.costructured_arrow.epi_hom_mk CategoryTheory.CostructuredArrow.epi_homMk

/-- Eta rule for costructured arrows. Prefer `costructured_arrow.eta`, as equality of objects tends
    to cause problems. -/
theorem eq_mk (f : CostructuredArrow S T) : f = mk f.hom := by
  cases f
  congr
#align category_theory.costructured_arrow.eq_mk CategoryTheory.CostructuredArrow.eq_mk

/-- Eta rule for costructured arrows. -/
@[simps!]
def eta (f : CostructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _) (by aesop_cat)
#align category_theory.costructured_arrow.eta CategoryTheory.CostructuredArrow.eta

/-- A morphism between target objects `T ⟶ T'`
covariantly induces a functor between costructured arrows,
`costructured_arrow S T ⥤ costructured_arrow S T'`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps!]
def map (f : T ⟶ T') : CostructuredArrow S T ⥤ CostructuredArrow S T' :=
  Comma.mapRight _ ((Functor.const _).map f)
#align category_theory.costructured_arrow.map CategoryTheory.CostructuredArrow.map

@[simp]
theorem map_mk {f : S.obj Y ⟶ T} (g : T ⟶ T') : (map g).obj (mk f) = mk (f ≫ g) :=
  rfl
#align category_theory.costructured_arrow.map_mk CategoryTheory.CostructuredArrow.map_mk

@[simp]
theorem map_id {f : CostructuredArrow S T} : (map (𝟙 T)).obj f = f := by
  rw [eq_mk f]
  simp
#align category_theory.costructured_arrow.map_id CategoryTheory.CostructuredArrow.map_id

@[simp]
theorem map_comp {f : T ⟶ T'} {f' : T' ⟶ T''} {h : CostructuredArrow S T} :
    (map (f ≫ f')).obj h = (map f').obj ((map f).obj h) := by
  rw [eq_mk h]
  simp
#align category_theory.costructured_arrow.map_comp CategoryTheory.CostructuredArrow.map_comp

instance proj_reflects_iso : ReflectsIsomorphisms (proj S T) where 
  reflects {Y Z} f t :=
    ⟨⟨CostructuredArrow.homMk (inv ((proj S T).map f)) (by simp), by aesop_cat⟩⟩
#align category_theory.costructured_arrow.proj_reflects_iso CategoryTheory.CostructuredArrow.proj_reflects_iso

open CategoryTheory.Limits

-- attribute [local tidy] tactic.discrete_cases -- Porting note: removed

/-- The identity costructured arrow is terminal. -/
def mkIdTerminal [Full S] [Faithful S] : IsTerminal (mk (𝟙 (S.obj Y))) where
  lift c :=
    homMk (S.preimage c.X.hom)
      (by
        dsimp
        simp)
  fac := fun _ ⟨a⟩ => by cases a
  uniq := by
    rintro c m -
    apply CommaMorphism.ext
    · apply S.map_injective
      simpa only [homMk_left, S.image_preimage, ← w m] using (Category.comp_id _).symm
    · aesop_cat
#align category_theory.costructured_arrow.mk_id_terminal CategoryTheory.CostructuredArrow.mkIdTerminal

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(F ⋙ G, S) ⥤ (G, S)`. -/
@[simps!]
def pre (F : B ⥤ C) (G : C ⥤ D) (S : D) : CostructuredArrow (F ⋙ G) S ⥤ CostructuredArrow G S :=
  Comma.preLeft F G _
#align category_theory.costructured_arrow.pre CategoryTheory.CostructuredArrow.pre

/-- The functor `(F, S) ⥤ (F ⋙ G, G(S))`. -/
@[simps]
def post (F : B ⥤ C) (G : C ⥤ D) (S : C) :
    CostructuredArrow F S ⥤ CostructuredArrow (F ⋙ G) (G.obj S) where
  obj X :=
    { left := X.left
      right := ⟨⟨⟩⟩ 
      hom := G.map X.hom }
  map f :=
    { left := f.left
      right := 𝟙 _
      w := by simp [Functor.comp_map, ← G.map_comp, ← f.w] }
#align category_theory.costructured_arrow.post CategoryTheory.CostructuredArrow.post

instance small_proj_preimage_of_locallySmall {𝒢 : Set C} [Small.{v₁} 𝒢] [LocallySmall.{v₁} D] :
    Small.{v₁} ((proj S T).obj ⁻¹' 𝒢) := by
  suffices (proj S T).obj ⁻¹' 𝒢 = Set.range fun f : ΣG : 𝒢, S.obj G ⟶ T => mk f.2
    by
    rw [this]
    infer_instance
  exact Set.ext fun X => ⟨fun h => ⟨⟨⟨_, h⟩, X.hom⟩, (eq_mk _).symm⟩, by aesop_cat⟩
#align category_theory.costructured_arrow.small_proj_preimage_of_locally_small CategoryTheory.CostructuredArrow.small_proj_preimage_of_locallySmall

end CostructuredArrow

open Opposite

namespace StructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `d ⟶ F.obj c` to the category of costructured arrows
`F.op.obj c ⟶ (op d)`.
-/
@[simps]
def toCostructuredArrow (F : C ⥤ D) (d : D) :
    (StructuredArrow d F)ᵒᵖ ⥤ CostructuredArrow F.op (op d) where
  obj X := @CostructuredArrow.mk _ _ _ _ _ (op X.unop.right) F.op X.unop.hom.op
  map f :=
    CostructuredArrow.homMk f.unop.right.op
      (by
        dsimp
        rw [← op_comp, ← f.unop.w, Functor.const_obj_map]
        erw [Category.id_comp])
#align category_theory.structured_arrow.to_costructured_arrow CategoryTheory.StructuredArrow.toCostructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `op d ⟶ F.op.obj c` to the category of costructured arrows
`F.obj c ⟶ d`.
-/
@[simps]
def toCostructuredArrow' (F : C ⥤ D) (d : D) :
    (StructuredArrow (op d) F.op)ᵒᵖ ⥤ CostructuredArrow F d
    where
  obj X := @CostructuredArrow.mk _ _ _ _ _ (unop X.unop.right) F X.unop.hom.unop
  map f :=
    CostructuredArrow.homMk f.unop.right.unop
      (by
        dsimp
        rw [← Quiver.Hom.unop_op (F.map (Quiver.Hom.unop f.unop.right)), ← unop_comp, ← F.op_map, ←
          f.unop.w, Functor.const_obj_map]
        erw [Category.id_comp])
#align category_theory.structured_arrow.to_costructured_arrow' CategoryTheory.StructuredArrow.toCostructuredArrow'

end StructuredArrow

namespace CostructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.obj c ⟶ d` to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
@[simps]
def toStructuredArrow (F : C ⥤ D) (d : D) : (CostructuredArrow F d)ᵒᵖ ⥤ StructuredArrow (op d) F.op
    where
  obj X := @StructuredArrow.mk _ _ _ _ _ (op X.unop.left) F.op X.unop.hom.op
  map f :=
    StructuredArrow.homMk f.unop.left.op
      (by
        dsimp
        rw [← op_comp, f.unop.w, Functor.const_obj_map]
        erw [Category.comp_id])
#align category_theory.costructured_arrow.to_structured_arrow CategoryTheory.CostructuredArrow.toStructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.op.obj c ⟶ op d` to the category of structured arrows
`d ⟶ F.obj c`.
-/
@[simps]
def toStructuredArrow' (F : C ⥤ D) (d : D) : (CostructuredArrow F.op (op d))ᵒᵖ ⥤ StructuredArrow d F
    where
  obj X := @StructuredArrow.mk _ _ _ _ _ (unop X.unop.left) F X.unop.hom.unop
  map f :=
    StructuredArrow.homMk f.unop.left.unop
      (by
        dsimp
        rw [← Quiver.Hom.unop_op (F.map f.unop.left.unop), ← unop_comp, ← F.op_map, f.unop.w,
          Functor.const_obj_map]
        erw [Category.comp_id])
#align category_theory.costructured_arrow.to_structured_arrow' CategoryTheory.CostructuredArrow.toStructuredArrow'

end CostructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, the category of structured arrows `d ⟶ F.obj c`
is contravariantly equivalent to the category of costructured arrows `F.op.obj c ⟶ op d`.
-/
def structuredArrowOpEquivalence (F : C ⥤ D) (d : D) :
    (StructuredArrow d F)ᵒᵖ ≌ CostructuredArrow F.op (op d) :=
  Equivalence.mk (StructuredArrow.toCostructuredArrow F d)
    (CostructuredArrow.toStructuredArrow' F d).rightOp
    (NatIso.ofComponents
      (fun X =>
        (@StructuredArrow.isoMk _ _ _ _ _ _ (StructuredArrow.mk (unop X).hom) (unop X) (Iso.refl _)
            (by aesop_cat)).op)
      fun {X Y} f => Quiver.Hom.unop_inj <| by 
        dsimp [StructuredArrow.isoMk,Comma.isoMk,StructuredArrow.homMk] --wtf
        apply CommaMorphism.ext 
        · apply ULift.ext; simp
        · sorry  
      )
    (NatIso.ofComponents
      (fun X =>
        @CostructuredArrow.isoMk _ _ _ _ _ _ (CostructuredArrow.mk X.hom) X (Iso.refl _) 
          (by aesop_cat)) fun {X Y} f => by 
            apply CommaMorphism.ext; apply ULift.ext; dsimp; simp)
#align category_theory.structured_arrow_op_equivalence CategoryTheory.structuredArrowOpEquivalence

/-- For a functor `F : C ⥤ D` and an object `d : D`, the category of costructured arrows
`F.obj c ⟶ d` is contravariantly equivalent to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
def costructuredArrowOpEquivalence (F : C ⥤ D) (d : D) :
    (CostructuredArrow F d)ᵒᵖ ≌ StructuredArrow (op d) F.op :=
  Equivalence.mk (CostructuredArrow.toStructuredArrow F d)
    (StructuredArrow.toCostructuredArrow' F d).rightOp
    (NatIso.ofComponents
      (fun X =>
        (@CostructuredArrow.isoMk _ _ _ _ _ _ (CostructuredArrow.mk (unop X).hom) (unop X)
            (Iso.refl _) (by aesop_cat)).op)
      fun {X Y} f => Quiver.Hom.unop_inj <| by 
        apply CommaMorphism.ext; dsimp; simp; sorry; sorry)
    (NatIso.ofComponents
      (fun X =>
        @StructuredArrow.isoMk _ _ _ _ _ _ (StructuredArrow.mk X.hom) X (Iso.refl _) 
          (by aesop_cat)) fun {X Y} f => by 
            apply CommaMorphism.ext; apply ULift.ext; dsimp; simp; sorry)
#align category_theory.costructured_arrow_op_equivalence CategoryTheory.costructuredArrowOpEquivalence

end CategoryTheory

