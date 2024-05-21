/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Logic.Small.Set

#align_import category_theory.structured_arrow from "leanprover-community/mathlib"@"8a318021995877a44630c898d0b2bc376fceef3b"

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
-- We explicitly come from `PUnit.{1}` here to obtain the correct universe for morphisms of
-- structured arrows.
-- Porting note(#5171): linter not ported yet
-- @[nolint has_nonempty_instance]
def StructuredArrow (S : D) (T : C ⥤ D) :=
  Comma (Functor.fromPUnit.{0} S) T
#align category_theory.structured_arrow CategoryTheory.StructuredArrow

-- Porting note: not found by inferInstance
instance (S : D) (T : C ⥤ D) : Category (StructuredArrow S T) := commaCategory

namespace StructuredArrow

/-- The obvious projection functor from structured arrows. -/
@[simps!]
def proj (S : D) (T : C ⥤ D) : StructuredArrow S T ⥤ C :=
  Comma.snd _ _
#align category_theory.structured_arrow.proj CategoryTheory.StructuredArrow.proj

variable {S S' S'' : D} {Y Y' Y'' : C} {T T' : C ⥤ D}

-- Porting note: this lemma was added because `Comma.hom_ext`
-- was not triggered automatically
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma hom_ext {X Y : StructuredArrow S T} (f g : X ⟶ Y) (h : f.right = g.right) : f = g :=
  CommaMorphism.ext _ _ (Subsingleton.elim _ _) h

@[simp]
theorem hom_eq_iff {X Y : StructuredArrow S T} (f g : X ⟶ Y) : f = g ↔ f.right = g.right :=
  ⟨fun h ↦ by rw [h], hom_ext _ _⟩

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
  have := f.w; aesop_cat
#align category_theory.structured_arrow.w CategoryTheory.StructuredArrow.w

@[simp]
theorem comp_right {X Y Z : StructuredArrow S T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

@[simp]
theorem id_right (X : StructuredArrow S T) : (𝟙 X : X ⟶ X).right = 𝟙 X.right := rfl

@[simp]
theorem eqToHom_right {X Y : StructuredArrow S T} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  simp only [eqToHom_refl, id_right]

@[simp]
theorem left_eq_id {X Y : StructuredArrow S T} (f : X ⟶ Y) : f.left = 𝟙 _ := rfl

/-- To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def homMk {f f' : StructuredArrow S T} (g : f.right ⟶ f'.right)
    (w : f.hom ≫ T.map g = f'.hom := by aesop_cat) : f ⟶ f' where
  left := 𝟙 _
  right := g
  w := by
    dsimp
    simpa using w.symm
#align category_theory.structured_arrow.hom_mk CategoryTheory.StructuredArrow.homMk

/- Porting note: it appears the simp lemma is not getting generated but the linter
picks up on it (seems like a bug). Either way simp solves it.  -/
attribute [-simp, nolint simpNF] homMk_left

/-- Given a structured arrow `X ⟶ T(Y)`, and an arrow `Y ⟶ Y'`, we can construct a morphism of
    structured arrows given by `(X ⟶ T(Y)) ⟶ (X ⟶ T(Y) ⟶ T(Y'))`.  -/
@[simps]
def homMk' (f : StructuredArrow S T) (g : f.right ⟶ Y') : f ⟶ mk (f.hom ≫ T.map g) where
  left := 𝟙 _
  right := g
#align category_theory.structured_arrow.hom_mk' CategoryTheory.StructuredArrow.homMk'

lemma homMk'_id (f : StructuredArrow S T) : homMk' f (𝟙 f.right) = eqToHom (by aesop_cat) := by
  ext
  simp [eqToHom_right]

lemma homMk'_mk_id (f : S ⟶ T.obj Y) : homMk' (mk f) (𝟙 Y) = eqToHom (by aesop_cat) :=
  homMk'_id _

lemma homMk'_comp (f : StructuredArrow S T) (g : f.right ⟶ Y') (g' : Y' ⟶ Y'') :
    homMk' f (g ≫ g') = homMk' f g ≫ homMk' (mk (f.hom ≫ T.map g)) g' ≫ eqToHom (by simp) := by
  ext
  simp [eqToHom_right]

lemma homMk'_mk_comp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    homMk' (mk f) (g ≫ g') = homMk' (mk f) g ≫ homMk' (mk (f ≫ T.map g)) g' ≫ eqToHom (by simp) :=
  homMk'_comp _ _ _

/-- Variant of `homMk'` where both objects are applications of `mk`. -/
@[simps]
def mkPostcomp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') : mk f ⟶ mk (f ≫ T.map g) where
  left := 𝟙 _
  right := g

lemma mkPostcomp_id (f : S ⟶ T.obj Y) : mkPostcomp f (𝟙 Y) = eqToHom (by aesop_cat) := by aesop_cat
lemma mkPostcomp_comp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    mkPostcomp f (g ≫ g') = mkPostcomp f g ≫ mkPostcomp (f ≫ T.map g) g' ≫ eqToHom (by simp) := by
  aesop_cat

/-- To construct an isomorphism of structured arrows,
we need an isomorphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps!]
def isoMk {f f' : StructuredArrow S T} (g : f.right ≅ f'.right)
    (w : f.hom ≫ T.map g.hom = f'.hom := by aesop_cat) :
    f ≅ f' :=
  Comma.isoMk (eqToIso (by ext)) g (by simpa using w.symm)
#align category_theory.structured_arrow.iso_mk CategoryTheory.StructuredArrow.isoMk

/- Porting note: it appears the simp lemma is not getting generated but the linter
picks up on it. Either way simp solves these. -/
attribute [-simp, nolint simpNF] isoMk_hom_left_down_down isoMk_inv_left_down_down

theorem ext {A B : StructuredArrow S T} (f g : A ⟶ B) : f.right = g.right → f = g :=
  CommaMorphism.ext _ _ (Subsingleton.elim _ _)
#align category_theory.structured_arrow.ext CategoryTheory.StructuredArrow.ext

theorem ext_iff {A B : StructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.right = g.right :=
  ⟨fun h => h ▸ rfl, ext f g⟩
#align category_theory.structured_arrow.ext_iff CategoryTheory.StructuredArrow.ext_iff

instance proj_faithful : (proj S T).Faithful where
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

/-- Eta rule for structured arrows. Prefer `StructuredArrow.eta` for rewriting, since equality of
    objects tends to cause problems. -/
theorem eq_mk (f : StructuredArrow S T) : f = mk f.hom :=
  rfl
#align category_theory.structured_arrow.eq_mk CategoryTheory.StructuredArrow.eq_mk

/-- Eta rule for structured arrows. -/
@[simps!]
def eta (f : StructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _)
#align category_theory.structured_arrow.eta CategoryTheory.StructuredArrow.eta

/- Porting note: it appears the simp lemma is not getting generated but the linter
picks up on it. Either way simp solves these. -/
attribute [-simp, nolint simpNF] eta_hom_left_down_down eta_inv_left_down_down

/-- A morphism between source objects `S ⟶ S'`
contravariantly induces a functor between structured arrows,
`StructuredArrow S' T ⥤ StructuredArrow S T`.

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

/-- An isomorphism `S ≅ S'` induces an equivalence `StructuredArrow S T ≌ StructuredArrow S' T`. -/
@[simp]
def mapIso (i : S ≅ S') : StructuredArrow S T ≌ StructuredArrow S' T :=
  Comma.mapLeftIso _ ((Functor.const _).mapIso i)

/-- A natural isomorphism `T ≅ T'` induces an equivalence
    `StructuredArrow S T ≌ StructuredArrow S T'`. -/
@[simp]
def mapNatIso (i : T ≅ T') : StructuredArrow S T ≌ StructuredArrow S T' :=
  Comma.mapRightIso _ i

instance proj_reflectsIsomorphisms : (proj S T).ReflectsIsomorphisms where
  reflects {Y Z} f t :=
    ⟨⟨StructuredArrow.homMk
        (inv ((proj S T).map f))
        (by rw [Functor.map_inv, IsIso.comp_inv_eq]; simp),
      by constructor <;> apply CommaMorphism.ext <;> dsimp at t ⊢ <;> simp⟩⟩
#align category_theory.structured_arrow.proj_reflects_iso CategoryTheory.StructuredArrow.proj_reflectsIsomorphisms

open CategoryTheory.Limits

/-- The identity structured arrow is initial. -/
noncomputable def mkIdInitial [T.Full] [T.Faithful] : IsInitial (mk (𝟙 (T.obj Y))) where
  desc c := homMk (T.preimage c.pt.hom)
  uniq c m _ := by
    apply CommaMorphism.ext
    · aesop_cat
    · apply T.map_injective
      simpa only [homMk_right, T.map_preimage, ← w m] using (Category.id_comp _).symm
#align category_theory.structured_arrow.mk_id_initial CategoryTheory.StructuredArrow.mkIdInitial

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(S, F ⋙ G) ⥤ (S, G)`. -/
@[simps!]
def pre (S : D) (F : B ⥤ C) (G : C ⥤ D) : StructuredArrow S (F ⋙ G) ⥤ StructuredArrow S G :=
  Comma.preRight _ F G
#align category_theory.structured_arrow.pre CategoryTheory.StructuredArrow.pre

instance (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.Faithful] : (pre S F G).Faithful :=
  show (Comma.preRight _ _ _).Faithful from inferInstance

instance (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.Full] : (pre S F G).Full :=
  show (Comma.preRight _ _ _).Full from inferInstance

instance (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.EssSurj] : (pre S F G).EssSurj :=
  show (Comma.preRight _ _ _).EssSurj from inferInstance

/-- If `F` is an equivalence, then so is the functor `(S, F ⋙ G) ⥤ (S, G)`. -/
instance isEquivalence_pre (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.IsEquivalence] :
    (pre S F G).IsEquivalence :=
  Comma.isEquivalence_preRight _ _ _

/-- The functor `(S, F) ⥤ (G(S), F ⋙ G)`. -/
@[simps]
def post (S : C) (F : B ⥤ C) (G : C ⥤ D) :
    StructuredArrow S F ⥤ StructuredArrow (G.obj S) (F ⋙ G) where
  obj X := StructuredArrow.mk (G.map X.hom)
  map f := StructuredArrow.homMk f.right (by simp [Functor.comp_map, ← G.map_comp, ← f.w])
#align category_theory.structured_arrow.post CategoryTheory.StructuredArrow.post

instance (S : C) (F : B ⥤ C) (G : C ⥤ D) : (post S F G).Faithful where
  map_injective {_ _} _ _ h := by simpa [ext_iff] using h

instance (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Faithful] : (post S F G).Full where
  map_surjective f := ⟨homMk f.right (G.map_injective (by simpa using f.w.symm)), by aesop_cat⟩

instance (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] : (post S F G).EssSurj where
  mem_essImage h := ⟨mk (G.preimage h.hom), ⟨isoMk (Iso.refl _) (by simp)⟩⟩

/-- If `G` is fully faithful, then `post S F G : (S, F) ⥤ (G(S), F ⋙ G)` is an equivalence. -/
instance isEquivalence_post (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] [G.Faithful] :
    (post S F G).IsEquivalence where

section

variable {L : D} {R : C ⥤ D} {L' : B} {R' : A ⥤ B} {F : C ⥤ A} {G : D ⥤ B}
  (α : L' ⟶ G.obj L) (β : R ⋙ G ⟶ F ⋙ R')

/-- The functor `StructuredArrow L R ⥤ StructuredArrow L' R'` that is deduced from
a natural transformation `R ⋙ G ⟶ F ⋙ R'` and a morphism `L' ⟶ G.obj L.` -/
@[simps!]
def map₂ : StructuredArrow L R ⥤ StructuredArrow L' R' :=
  Comma.map (F₁ := 𝟭 (Discrete PUnit)) (Discrete.natTrans (fun _ => α)) β

instance faithful_map₂ [F.Faithful] : (map₂ α β).Faithful := by
  apply Comma.faithful_map

instance full_map₂ [G.Faithful] [F.Full] [IsIso α] [IsIso β] : (map₂ α β).Full := by
  apply Comma.full_map

instance essSurj_map₂ [F.EssSurj] [G.Full] [IsIso α] [IsIso β] : (map₂ α β).EssSurj := by
  apply Comma.essSurj_map

noncomputable instance isEquivalenceMap₂
    [F.IsEquivalence] [G.Faithful] [G.Full] [IsIso α] [IsIso β] :
    (map₂ α β).IsEquivalence := by
  apply Comma.isEquivalenceMap

end

instance small_proj_preimage_of_locallySmall {𝒢 : Set C} [Small.{v₁} 𝒢] [LocallySmall.{v₁} D] :
    Small.{v₁} ((proj S T).obj ⁻¹' 𝒢) := by
  suffices (proj S T).obj ⁻¹' 𝒢 = Set.range fun f : ΣG : 𝒢, S ⟶ T.obj G => mk f.2 by
    rw [this]
    infer_instance
  exact Set.ext fun X => ⟨fun h => ⟨⟨⟨_, h⟩, X.hom⟩, (eq_mk _).symm⟩, by aesop_cat⟩
#align category_theory.structured_arrow.small_proj_preimage_of_locally_small CategoryTheory.StructuredArrow.small_proj_preimage_of_locallySmall

/-- A structured arrow is called universal if it is initial. -/
abbrev IsUniversal (f : StructuredArrow S T) := IsInitial f

namespace IsUniversal

variable {f g : StructuredArrow S T}

theorem uniq (h : IsUniversal f) (η : f ⟶ g) : η = h.to g :=
  h.hom_ext η (h.to g)

/-- The family of morphisms out of a universal arrow. -/
def desc (h : IsUniversal f) (g : StructuredArrow S T) : f.right ⟶ g.right :=
  (h.to g).right

/-- Any structured arrow factors through a universal arrow. -/
@[reassoc (attr := simp)]
theorem fac (h : IsUniversal f) (g : StructuredArrow S T) :
    f.hom ≫ T.map (h.desc g) = g.hom :=
  Category.id_comp g.hom ▸ (h.to g).w.symm

theorem hom_desc (h : IsUniversal f) {c : C} (η : f.right ⟶ c) :
    η = h.desc (mk <| f.hom ≫ T.map η) :=
  let g := mk <| f.hom ≫ T.map η
  congrArg CommaMorphism.right (h.hom_ext (homMk η rfl : f ⟶ g) (h.to g))

/-- Two morphisms out of a universal `T`-structured arrow are equal if their image under `T` are
equal after precomposing the universal arrow. -/
theorem hom_ext (h : IsUniversal f) {c : C} {η η' : f.right ⟶ c}
    (w : f.hom ≫ T.map η = f.hom ≫ T.map η') : η = η' := by
  rw [h.hom_desc η, h.hom_desc η', w]

theorem existsUnique (h : IsUniversal f) (g : StructuredArrow S T) :
    ∃! η : f.right ⟶ g.right, f.hom ≫ T.map η = g.hom :=
  ⟨h.desc g, h.fac g, fun f w ↦ h.hom_ext <| by simp [w]⟩

end IsUniversal

end StructuredArrow

/-- The category of `S`-costructured arrows with target `T : D` (here `S : C ⥤ D`),
has as its objects `D`-morphisms of the form `S Y ⟶ T`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
-- We explicitly come from `PUnit.{1}` here to obtain the correct universe for morphisms of
-- costructured arrows.
-- @[nolint has_nonempty_instance] -- Porting note(#5171): linter not ported yet
def CostructuredArrow (S : C ⥤ D) (T : D) :=
  Comma S (Functor.fromPUnit.{0} T)
#align category_theory.costructured_arrow CategoryTheory.CostructuredArrow

instance (S : C ⥤ D) (T : D) : Category (CostructuredArrow S T) := commaCategory

namespace CostructuredArrow

/-- The obvious projection functor from costructured arrows. -/
@[simps!]
def proj (S : C ⥤ D) (T : D) : CostructuredArrow S T ⥤ C :=
  Comma.fst _ _
#align category_theory.costructured_arrow.proj CategoryTheory.CostructuredArrow.proj

variable {T T' T'' : D} {Y Y' Y'' : C} {S S' : C ⥤ D}

-- Porting note: this lemma was added because `Comma.hom_ext`
-- was not triggered automatically
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
lemma hom_ext {X Y : CostructuredArrow S T} (f g : X ⟶ Y) (h : f.left = g.left) : f = g :=
  CommaMorphism.ext _ _ h (Subsingleton.elim _ _)

@[simp]
theorem hom_eq_iff {X Y : CostructuredArrow S T} (f g : X ⟶ Y) : f = g ↔ f.left = g.left :=
  ⟨fun h ↦ by rw [h], hom_ext _ _⟩

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

-- @[reassoc (attr := simp)] Porting note: simp can solve these
@[reassoc]
theorem w {A B : CostructuredArrow S T} (f : A ⟶ B) : S.map f.left ≫ B.hom = A.hom := by simp
#align category_theory.costructured_arrow.w CategoryTheory.CostructuredArrow.w

@[simp]
theorem comp_left {X Y Z : CostructuredArrow S T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

@[simp]
theorem id_left (X : CostructuredArrow S T) : (𝟙 X : X ⟶ X).left = 𝟙 X.left := rfl

@[simp]
theorem eqToHom_left {X Y : CostructuredArrow S T} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  simp only [eqToHom_refl, id_left]

@[simp]
theorem right_eq_id {X Y : CostructuredArrow S T} (f : X ⟶ Y) : f.right = 𝟙 _ := rfl

/-- To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps!]
def homMk {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left)
    (w : S.map g ≫ f'.hom = f.hom := by aesop_cat) : f ⟶ f' where
  left := g
  right := 𝟙 _
#align category_theory.costructured_arrow.hom_mk CategoryTheory.CostructuredArrow.homMk

/- Porting note: it appears the simp lemma is not getting generated but the linter
picks up on it. Either way simp can prove this -/
attribute [-simp, nolint simpNF] homMk_right_down_down

/-- Given a costructured arrow `S(Y) ⟶ X`, and an arrow `Y' ⟶ Y'`, we can construct a morphism of
    costructured arrows given by `(S(Y) ⟶ X) ⟶ (S(Y') ⟶ S(Y) ⟶ X)`. -/
@[simps]
def homMk' (f : CostructuredArrow S T) (g : Y' ⟶ f.left) : mk (S.map g ≫ f.hom) ⟶ f where
  left := g
  right := 𝟙 _

lemma homMk'_id (f : CostructuredArrow S T) : homMk' f (𝟙 f.left) = eqToHom (by aesop_cat) := by
  ext
  simp [eqToHom_left]

lemma homMk'_mk_id (f : S.obj Y ⟶ T) : homMk' (mk f) (𝟙 Y) = eqToHom (by aesop_cat) :=
  homMk'_id _

lemma homMk'_comp (f : CostructuredArrow S T) (g : Y' ⟶ f.left) (g' : Y'' ⟶ Y') :
    homMk' f (g' ≫ g) = eqToHom (by simp) ≫ homMk' (mk (S.map g ≫ f.hom)) g' ≫ homMk' f g := by
  ext
  simp [eqToHom_left]

lemma homMk'_mk_comp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    homMk' (mk f) (g' ≫ g) = eqToHom (by simp) ≫ homMk' (mk (S.map g ≫ f)) g' ≫ homMk' (mk f) g :=
  homMk'_comp _ _ _

/-- Variant of `homMk'` where both objects are applications of `mk`. -/
@[simps]
def mkPrecomp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) : mk (S.map g ≫ f) ⟶ mk f where
  left := g
  right := 𝟙 _

lemma mkPrecomp_id (f : S.obj Y ⟶ T) : mkPrecomp f (𝟙 Y) = eqToHom (by aesop_cat) := by aesop_cat
lemma mkPrecomp_comp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    mkPrecomp f (g' ≫ g) = eqToHom (by simp) ≫ mkPrecomp (S.map g ≫ f) g' ≫ mkPrecomp f g := by
  aesop_cat

/-- To construct an isomorphism of costructured arrows,
we need an isomorphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps!]
def isoMk {f f' : CostructuredArrow S T} (g : f.left ≅ f'.left)
    (w : S.map g.hom ≫ f'.hom = f.hom := by aesop_cat) : f ≅ f' :=
  Comma.isoMk g (eqToIso (by ext)) (by simpa using w)
#align category_theory.costructured_arrow.iso_mk CategoryTheory.CostructuredArrow.isoMk

/- Porting note: it appears the simp lemma is not getting generated but the linter
picks up on it. Either way simp solves these. -/
attribute [-simp, nolint simpNF] isoMk_hom_right_down_down isoMk_inv_right_down_down

theorem ext {A B : CostructuredArrow S T} (f g : A ⟶ B) (h : f.left = g.left) : f = g :=
  CommaMorphism.ext _ _ h (Subsingleton.elim _ _)
#align category_theory.costructured_arrow.ext CategoryTheory.CostructuredArrow.ext

theorem ext_iff {A B : CostructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.left = g.left :=
  ⟨fun h => h ▸ rfl, ext f g⟩
#align category_theory.costructured_arrow.ext_iff CategoryTheory.CostructuredArrow.ext_iff

instance proj_faithful : (proj S T).Faithful where map_injective {_ _} := ext
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

/-- Eta rule for costructured arrows. Prefer `CostructuredArrow.eta` for rewriting, as equality of
    objects tends to cause problems. -/
theorem eq_mk (f : CostructuredArrow S T) : f = mk f.hom :=
  rfl
#align category_theory.costructured_arrow.eq_mk CategoryTheory.CostructuredArrow.eq_mk

/-- Eta rule for costructured arrows. -/
@[simps!]
def eta (f : CostructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _)
#align category_theory.costructured_arrow.eta CategoryTheory.CostructuredArrow.eta

/- Porting note: it appears the simp lemma is not getting generated but the linter
picks up on it. Either way simp solves these. -/
attribute [-simp, nolint simpNF] eta_hom_right_down_down eta_inv_right_down_down

/-- A morphism between target objects `T ⟶ T'`
covariantly induces a functor between costructured arrows,
`CostructuredArrow S T ⥤ CostructuredArrow S T'`.

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

/-- An isomorphism `T ≅ T'` induces an equivalence
    `CostructuredArrow S T ≌ CostructuredArrow S T'`. -/
@[simp]
def mapIso (i : T ≅ T') : CostructuredArrow S T ≌ CostructuredArrow S T' :=
  Comma.mapRightIso _ ((Functor.const _).mapIso i)

/-- A natural isomorphism `S ≅ S'` induces an equivalence
    `CostrucutredArrow S T ≌ CostructuredArrow S' T`. -/
@[simp]
def mapNatIso (i : S ≅ S') : CostructuredArrow S T ≌ CostructuredArrow S' T :=
  Comma.mapLeftIso _ i

instance proj_reflectsIsomorphisms : (proj S T).ReflectsIsomorphisms where
  reflects {Y Z} f t :=
    ⟨⟨CostructuredArrow.homMk
        (inv ((proj S T).map f))
        (by rw [Functor.map_inv, IsIso.inv_comp_eq]; simp),
      by constructor <;> ext <;> dsimp at t ⊢ <;> simp⟩⟩
#align category_theory.costructured_arrow.proj_reflects_iso CategoryTheory.CostructuredArrow.proj_reflectsIsomorphisms

open CategoryTheory.Limits

/-- The identity costructured arrow is terminal. -/
noncomputable def mkIdTerminal [S.Full] [S.Faithful] : IsTerminal (mk (𝟙 (S.obj Y))) where
  lift c := homMk (S.preimage c.pt.hom)
  uniq := by
    rintro c m -
    ext
    apply S.map_injective
    simpa only [homMk_left, S.map_preimage, ← w m] using (Category.comp_id _).symm
#align category_theory.costructured_arrow.mk_id_terminal CategoryTheory.CostructuredArrow.mkIdTerminal

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(F ⋙ G, S) ⥤ (G, S)`. -/
@[simps!]
def pre (F : B ⥤ C) (G : C ⥤ D) (S : D) : CostructuredArrow (F ⋙ G) S ⥤ CostructuredArrow G S :=
  Comma.preLeft F G _
#align category_theory.costructured_arrow.pre CategoryTheory.CostructuredArrow.pre

instance (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.Faithful] : (pre F G S).Faithful :=
  show (Comma.preLeft _ _ _).Faithful from inferInstance

instance (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.Full] : (pre F G S).Full :=
  show (Comma.preLeft _ _ _).Full from inferInstance

instance (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.EssSurj] : (pre F G S).EssSurj :=
  show (Comma.preLeft _ _ _).EssSurj from inferInstance

/-- If `F` is an equivalence, then so is the functor `(F ⋙ G, S) ⥤ (G, S)`. -/
instance isEquivalence_pre (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.IsEquivalence] :
    (pre F G S).IsEquivalence :=
  Comma.isEquivalence_preLeft _ _ _

/-- The functor `(F, S) ⥤ (F ⋙ G, G(S))`. -/
@[simps]
def post (F : B ⥤ C) (G : C ⥤ D) (S : C) :
    CostructuredArrow F S ⥤ CostructuredArrow (F ⋙ G) (G.obj S) where
  obj X := CostructuredArrow.mk (G.map X.hom)
  map f := CostructuredArrow.homMk f.left (by simp [Functor.comp_map, ← G.map_comp, ← f.w])
#align category_theory.costructured_arrow.post CategoryTheory.CostructuredArrow.post

instance (F : B ⥤ C) (G : C ⥤ D) (S : C) : (post F G S).Faithful where
  map_injective {_ _} _ _ h := by simpa [ext_iff] using h

instance (F : B ⥤ C) (G : C ⥤ D) (S : C) [G.Faithful] : (post F G S).Full where
  map_surjective f := ⟨homMk f.left (G.map_injective (by simpa using f.w)), by aesop_cat⟩

instance (F : B ⥤ C) (G : C ⥤ D) (S : C) [G.Full] : (post F G S).EssSurj where
  mem_essImage h := ⟨mk (G.preimage h.hom), ⟨isoMk (Iso.refl _) (by simp)⟩⟩

/-- If `G` is fully faithful, then `post F G S : (F, S) ⥤ (F ⋙ G, G(S))` is an equivalence. -/
instance isEquivalence_post (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] [G.Faithful] :
    (post F G S).IsEquivalence where

section

variable {U : A ⥤ B} {V : B} {F : C ⥤ A} {G : D ⥤ B}
  (α : F ⋙ U ⟶ S ⋙ G) (β : G.obj T ⟶ V)

/-- The functor `CostructuredArrow S T ⥤ CostructuredArrow U V` that is deduced from
a natural transformation `F ⋙ U ⟶ S ⋙ G` and a morphism `G.obj T ⟶ V` -/
@[simps!]
def map₂ : CostructuredArrow S T ⥤ CostructuredArrow U V :=
  Comma.map (F₂ := 𝟭 (Discrete PUnit)) α (Discrete.natTrans (fun _ => β))

instance faithful_map₂ [F.Faithful] : (map₂ α β).Faithful := by
  apply Comma.faithful_map

instance full_map₂ [G.Faithful] [F.Full] [IsIso α] [IsIso β] : (map₂ α β).Full := by
  apply Comma.full_map

instance essSurj_map₂ [F.EssSurj] [G.Full] [IsIso α] [IsIso β] : (map₂ α β).EssSurj := by
  apply Comma.essSurj_map

noncomputable instance isEquivalenceMap₂
    [F.IsEquivalence] [G.Faithful] [G.Full] [IsIso α] [IsIso β] :
    (map₂ α β).IsEquivalence := by
  apply Comma.isEquivalenceMap

end

instance small_proj_preimage_of_locallySmall {𝒢 : Set C} [Small.{v₁} 𝒢] [LocallySmall.{v₁} D] :
    Small.{v₁} ((proj S T).obj ⁻¹' 𝒢) := by
  suffices (proj S T).obj ⁻¹' 𝒢 = Set.range fun f : ΣG : 𝒢, S.obj G ⟶ T => mk f.2 by
    rw [this]
    infer_instance
  exact Set.ext fun X => ⟨fun h => ⟨⟨⟨_, h⟩, X.hom⟩, (eq_mk _).symm⟩, by aesop_cat⟩
#align category_theory.costructured_arrow.small_proj_preimage_of_locally_small CategoryTheory.CostructuredArrow.small_proj_preimage_of_locallySmall

/-- A costructured arrow is called universal if it is terminal. -/
abbrev IsUniversal (f : CostructuredArrow S T) := IsTerminal f

namespace IsUniversal

variable {f g : CostructuredArrow S T}

theorem uniq (h : IsUniversal f) (η : g ⟶ f) : η = h.from g :=
  h.hom_ext η (h.from g)

/-- The family of morphisms into a universal arrow. -/
def lift (h : IsUniversal f) (g : CostructuredArrow S T) : g.left ⟶ f.left :=
  (h.from g).left

/-- Any costructured arrow factors through a universal arrow. -/
@[reassoc (attr := simp)]
theorem fac (h : IsUniversal f) (g : CostructuredArrow S T) :
    S.map (h.lift g) ≫ f.hom = g.hom :=
  Category.comp_id g.hom ▸ (h.from g).w

theorem hom_desc (h : IsUniversal f) {c : C} (η : c ⟶ f.left) :
    η = h.lift (mk <| S.map η ≫ f.hom) :=
  let g := mk <| S.map η ≫ f.hom
  congrArg CommaMorphism.left (h.hom_ext (homMk η rfl : g ⟶ f) (h.from g))

/-- Two morphisms into a universal `S`-costructured arrow are equal if their image under `S` are
equal after postcomposing the universal arrow. -/
theorem hom_ext (h : IsUniversal f) {c : C} {η η' : c ⟶ f.left}
    (w : S.map η ≫ f.hom = S.map η' ≫ f.hom) : η = η' := by
  rw [h.hom_desc η, h.hom_desc η', w]

theorem existsUnique (h : IsUniversal f) (g : CostructuredArrow S T) :
    ∃! η : g.left ⟶ f.left, S.map η ≫ f.hom = g.hom :=
  ⟨h.lift g, h.fac g, fun f w ↦ h.hom_ext <| by simp [w]⟩

end IsUniversal

end CostructuredArrow

namespace Functor

variable {E : Type u₃} [Category.{v₃} E]

/-- Given `X : D` and `F : C ⥤ D`, to upgrade a functor `G : E ⥤ C` to a functor
    `E ⥤ StructuredArrow X F`, it suffices to provide maps `X ⟶ F.obj (G.obj Y)` for all `Y` making
    the obvious triangles involving all `F.map (G.map g)` commute.

    This is of course the same as providing a cone over `F ⋙ G` with cone point `X`, see
    `Functor.toStructuredArrowIsoToStructuredArrow`. -/
@[simps]
def toStructuredArrow (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) → X ⟶ F.obj (G.obj Y))
    (h : ∀ {Y Z : E} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) : E ⥤ StructuredArrow X F where
  obj Y := StructuredArrow.mk (f Y)
  map g := StructuredArrow.homMk (G.map g) (h g)

/-- Upgrading a functor `E ⥤ C` to a functor `E ⥤ StructuredArrow X F` and composing with the
    forgetful functor `StructuredArrow X F ⥤ C` recovers the original functor. -/
def toStructuredArrowCompProj (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) → X ⟶ F.obj (G.obj Y))
    (h : ∀ {Y Z : E} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ⋙ StructuredArrow.proj _ _ ≅ G :=
  Iso.refl _

@[simp]
lemma toStructuredArrow_comp_proj (G : E ⥤ C) (X : D) (F : C ⥤ D)
    (f : (Y : E) → X ⟶ F.obj (G.obj Y)) (h : ∀ {Y Z : E} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ⋙ StructuredArrow.proj _ _ = G :=
  rfl

/-- Given `F : C ⥤ D` and `X : D`, to upgrade a functor `G : E ⥤ C` to a functor
    `E ⥤ CostructuredArrow F X`, it suffices to provide maps `F.obj (G.obj Y) ⟶ X` for all `Y`
    making the obvious triangles involving all `F.map (G.map g)` commute.

    This is of course the same as providing a cocone over `F ⋙ G` with cocone point `X`, see
    `Functor.toCostructuredArrowIsoToCostructuredArrow`. -/
@[simps]
def toCostructuredArrow (G : E ⥤ C) (F : C ⥤ D) (X : D) (f : (Y : E) → F.obj (G.obj Y) ⟶ X)
    (h : ∀ {Y Z : E} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) : E ⥤ CostructuredArrow F X where
  obj Y := CostructuredArrow.mk (f Y)
  map g := CostructuredArrow.homMk (G.map g) (h g)

/-- Upgrading a functor `E ⥤ C` to a functor `E ⥤ CostructuredArrow F X` and composing with the
    forgetful functor `CostructuredArrow F X ⥤ C` recovers the original functor. -/
def toCostructuredArrowCompProj (G : E ⥤ C) (F : C ⥤ D) (X : D)
    (f : (Y : E) → F.obj (G.obj Y) ⟶ X) (h : ∀ {Y Z : E} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ⋙ CostructuredArrow.proj _ _ ≅ G :=
  Iso.refl _

@[simp]
lemma toCostructuredArrow_comp_proj (G : E ⥤ C) (F : C ⥤ D) (X : D)
    (f : (Y : E) → F.obj (G.obj Y) ⟶ X) (h : ∀ {Y Z : E} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ⋙ CostructuredArrow.proj _ _ = G :=
rfl

end Functor

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
    (StructuredArrow (op d) F.op)ᵒᵖ ⥤ CostructuredArrow F d where
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
def toStructuredArrow (F : C ⥤ D) (d : D) :
    (CostructuredArrow F d)ᵒᵖ ⥤ StructuredArrow (op d) F.op where
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
def toStructuredArrow' (F : C ⥤ D) (d : D) :
    (CostructuredArrow F.op (op d))ᵒᵖ ⥤ StructuredArrow d F where
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
      (fun X => (StructuredArrow.isoMk (Iso.refl _)).op)
      fun {X Y} f => Quiver.Hom.unop_inj <| by
        apply CommaMorphism.ext <;>
          dsimp [StructuredArrow.isoMk, Comma.isoMk,StructuredArrow.homMk]; simp)
    (NatIso.ofComponents
      (fun X => CostructuredArrow.isoMk (Iso.refl _))
      fun {X Y} f => by
        apply CommaMorphism.ext <;>
          dsimp [CostructuredArrow.isoMk, Comma.isoMk, CostructuredArrow.homMk]; simp)
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
      (fun X => (CostructuredArrow.isoMk (Iso.refl _)).op)
      fun {X Y} f => Quiver.Hom.unop_inj <| by
        apply CommaMorphism.ext <;>
          dsimp [CostructuredArrow.isoMk, CostructuredArrow.homMk, Comma.isoMk]; simp)
    (NatIso.ofComponents
      (fun X => StructuredArrow.isoMk (Iso.refl _))
      fun {X Y} f => by
        apply CommaMorphism.ext <;>
          dsimp [StructuredArrow.isoMk, StructuredArrow.homMk, Comma.isoMk]; simp)
#align category_theory.costructured_arrow_op_equivalence CategoryTheory.costructuredArrowOpEquivalence

end CategoryTheory
