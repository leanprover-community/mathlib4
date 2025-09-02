/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kim Morrison
-/
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.PUnit
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : C`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/


namespace CategoryTheory

-- morphism levels before object levels. See note [CategoryTheory universes].
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`),
has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
-- We explicitly come from `PUnit.{1}` here to obtain the correct universe for morphisms of
-- structured arrows.
def StructuredArrow (S : D) (T : C ⥤ D) :=
  Comma (Functor.fromPUnit.{0} S) T

/-- See through the type synonym `StructuredArrow S T = Comma _ _`. -/
instance (S : D) (T : C ⥤ D) : Category (StructuredArrow S T) :=
  inferInstanceAs <| Category (Comma _ _)

namespace StructuredArrow

/-- The obvious projection functor from structured arrows. -/
@[simps!]
def proj (S : D) (T : C ⥤ D) : StructuredArrow S T ⥤ C :=
  Comma.snd _ _

variable {S S' S'' : D} {Y Y' Y'' : C} {T T' : C ⥤ D}

@[ext]
lemma hom_ext {X Y : StructuredArrow S T} (f g : X ⟶ Y) (h : f.right = g.right) : f = g :=
  CommaMorphism.ext (Subsingleton.elim _ _) h

@[simp]
theorem hom_eq_iff {X Y : StructuredArrow S T} (f g : X ⟶ Y) : f = g ↔ f.right = g.right :=
  ⟨fun h ↦ by rw [h], hom_ext _ _⟩

/-- Construct a structured arrow from a morphism. -/
def mk (f : S ⟶ T.obj Y) : StructuredArrow S T :=
  ⟨⟨⟨⟩⟩, Y, f⟩

@[simp]
theorem mk_left (f : S ⟶ T.obj Y) : (mk f).left = ⟨⟨⟩⟩ :=
  rfl

@[simp]
theorem mk_right (f : S ⟶ T.obj Y) : (mk f).right = Y :=
  rfl

@[simp]
theorem mk_hom_eq_self (f : S ⟶ T.obj Y) : (mk f).hom = f :=
  rfl

@[reassoc (attr := simp)]
theorem w {A B : StructuredArrow S T} (f : A ⟶ B) : A.hom ≫ T.map f.right = B.hom := by
  have := f.w; cat_disch

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
theorem left_eq_id {X Y : StructuredArrow S T} (f : X ⟶ Y) : f.left = 𝟙 X.left := rfl

/-- To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps right]
def homMk {f f' : StructuredArrow S T} (g : f.right ⟶ f'.right)
    (w : f.hom ≫ T.map g = f'.hom := by cat_disch) : f ⟶ f' where
  left := 𝟙 f.left
  right := g
  w := by
    dsimp
    simpa using w.symm

theorem homMk_surjective {f f' : StructuredArrow S T} (φ : f ⟶ f') :
    ∃ (ψ : f.right ⟶ f'.right) (hψ : f.hom ≫ T.map ψ = f'.hom),
      φ = StructuredArrow.homMk ψ hψ :=
  ⟨φ.right, StructuredArrow.w φ, rfl⟩

/-- Given a structured arrow `X ⟶ T(Y)`, and an arrow `Y ⟶ Y'`, we can construct a morphism of
structured arrows given by `(X ⟶ T(Y)) ⟶ (X ⟶ T(Y) ⟶ T(Y'))`. -/
@[simps]
def homMk' (f : StructuredArrow S T) (g : f.right ⟶ Y') : f ⟶ mk (f.hom ≫ T.map g) where
  left := 𝟙 _
  right := g

lemma homMk'_id (f : StructuredArrow S T) : homMk' f (𝟙 f.right) = eqToHom (by cat_disch) := by
  simp [eqToHom_right]

lemma homMk'_mk_id (f : S ⟶ T.obj Y) : homMk' (mk f) (𝟙 Y) = eqToHom (by simp) :=
  homMk'_id _

lemma homMk'_comp (f : StructuredArrow S T) (g : f.right ⟶ Y') (g' : Y' ⟶ Y'') :
    homMk' f (g ≫ g') = homMk' f g ≫ homMk' (mk (f.hom ≫ T.map g)) g' ≫ eqToHom (by simp) := by
  simp [eqToHom_right]

lemma homMk'_mk_comp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    homMk' (mk f) (g ≫ g') = homMk' (mk f) g ≫ homMk' (mk (f ≫ T.map g)) g' ≫ eqToHom (by simp) :=
  homMk'_comp _ _ _

/-- Variant of `homMk'` where both objects are applications of `mk`. -/
@[simps]
def mkPostcomp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') : mk f ⟶ mk (f ≫ T.map g) where
  left := 𝟙 _
  right := g

lemma mkPostcomp_id (f : S ⟶ T.obj Y) : mkPostcomp f (𝟙 Y) = eqToHom (by simp) := by simp
lemma mkPostcomp_comp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    mkPostcomp f (g ≫ g') = mkPostcomp f g ≫ mkPostcomp (f ≫ T.map g) g' ≫ eqToHom (by simp) := by
  simp

/-- To construct an isomorphism of structured arrows,
we need an isomorphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps! hom_right inv_right]
def isoMk {f f' : StructuredArrow S T} (g : f.right ≅ f'.right)
    (w : f.hom ≫ T.map g.hom = f'.hom := by cat_disch) :
    f ≅ f' :=
  Comma.isoMk (eqToIso (by ext)) g (by simpa using w.symm)

theorem obj_ext (x y : StructuredArrow S T) (hr : x.right = y.right)
    (hh : x.hom ≫ T.map (eqToHom hr) = y.hom) : x = y := by
  cases x
  cases y
  cases hr
  cat_disch

theorem ext {A B : StructuredArrow S T} (f g : A ⟶ B) : f.right = g.right → f = g :=
  CommaMorphism.ext (Subsingleton.elim _ _)

theorem ext_iff {A B : StructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.right = g.right :=
  ⟨fun h => h ▸ rfl, ext f g⟩

instance proj_faithful : (proj S T).Faithful where
  map_injective {_ _} := ext

/-- The converse of this is true with additional assumptions, see `mono_iff_mono_right`. -/
theorem mono_of_mono_right {A B : StructuredArrow S T} (f : A ⟶ B) [h : Mono f.right] : Mono f :=
  (proj S T).mono_of_mono_map h

theorem epi_of_epi_right {A B : StructuredArrow S T} (f : A ⟶ B) [h : Epi f.right] : Epi f :=
  (proj S T).epi_of_epi_map h

instance mono_homMk {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Mono f] :
    Mono (homMk f w) :=
  (proj S T).mono_of_mono_map h

instance epi_homMk {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Epi f] :
    Epi (homMk f w) :=
  (proj S T).epi_of_epi_map h

/-- Eta rule for structured arrows. Prefer `StructuredArrow.eta` for rewriting, since equality of
objects tends to cause problems. -/
theorem eq_mk (f : StructuredArrow S T) : f = mk f.hom :=
  rfl

/-- Eta rule for structured arrows. -/
@[simps! hom_right inv_right]
def eta (f : StructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _)

lemma mk_surjective (f : StructuredArrow S T) :
    ∃ (Y : C) (g : S ⟶ T.obj Y), f = mk g :=
  ⟨_, _, eq_mk f⟩

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

@[simp]
theorem map_mk {f : S' ⟶ T.obj Y} (g : S ⟶ S') : (map g).obj (mk f) = mk (g ≫ f) :=
  rfl

@[simp]
theorem map_id {f : StructuredArrow S T} : (map (𝟙 S)).obj f = f := by
  rw [eq_mk f]
  simp

@[simp]
theorem map_comp {f : S ⟶ S'} {f' : S' ⟶ S''} {h : StructuredArrow S'' T} :
    (map (f ≫ f')).obj h = (map f).obj ((map f').obj h) := by
  rw [eq_mk h]
  simp

/-- An isomorphism `S ≅ S'` induces an equivalence `StructuredArrow S T ≌ StructuredArrow S' T`. -/
@[simps!]
def mapIso (i : S ≅ S') : StructuredArrow S T ≌ StructuredArrow S' T :=
  Comma.mapLeftIso _ ((Functor.const _).mapIso i)

/-- A natural isomorphism `T ≅ T'` induces an equivalence
`StructuredArrow S T ≌ StructuredArrow S T'`. -/
@[simps!]
def mapNatIso (i : T ≅ T') : StructuredArrow S T ≌ StructuredArrow S T' :=
  Comma.mapRightIso _ i

instance proj_reflectsIsomorphisms : (proj S T).ReflectsIsomorphisms where
  reflects {Y Z} f t :=
    ⟨⟨StructuredArrow.homMk
        (inv ((proj S T).map f))
        (by rw [Functor.map_inv, IsIso.comp_inv_eq]; simp),
      by constructor <;> apply CommaMorphism.ext <;> dsimp at t ⊢ <;> simp⟩⟩

open CategoryTheory.Limits

/-- The identity structured arrow is initial. -/
noncomputable def mkIdInitial [T.Full] [T.Faithful] : IsInitial (mk (𝟙 (T.obj Y))) where
  desc c := homMk (T.preimage c.pt.hom)
  uniq c m _ := by
    apply CommaMorphism.ext
    · simp
    · apply T.map_injective
      simpa only [homMk_right, T.map_preimage, ← w m] using (Category.id_comp _).symm

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(S, F ⋙ G) ⥤ (S, G)`. -/
@[simps!]
def pre (S : D) (F : B ⥤ C) (G : C ⥤ D) : StructuredArrow S (F ⋙ G) ⥤ StructuredArrow S G :=
  Comma.preRight _ F G

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

instance (S : C) (F : B ⥤ C) (G : C ⥤ D) : (post S F G).Faithful where
  map_injective {_ _} _ _ h := by simpa [ext_iff] using h

instance (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Faithful] : (post S F G).Full where
  map_surjective f := ⟨homMk f.right (G.map_injective (by simpa using f.w.symm)), by simp⟩

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

/-- The composition of two applications of `map₂` is naturally isomorphic to a single such one. -/
def map₂CompMap₂Iso {C' : Type u₆} [Category.{v₆} C'] {D' : Type u₅} [Category.{v₅} D']
    {L'' : D'} {R'' : C' ⥤ D'} {F' : C' ⥤ C} {G' : D' ⥤ D} (α' : L ⟶ G'.obj L'')
    (β' : R'' ⋙ G' ⟶ F' ⋙ R) :
    map₂ α' β' ⋙ map₂ α β ≅
    map₂ (α ≫ G.map α')
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight β' _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ β ≫ (Functor.associator _ _ _).inv) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _))

end

/-- `StructuredArrow.post` is a special case of `StructuredArrow.map₂` up to natural isomorphism. -/
def postIsoMap₂ (S : C) (F : B ⥤ C) (G : C ⥤ D) :
    post S F G ≅ map₂ (F := 𝟭 _) (𝟙 _) (𝟙 (F ⋙ G)) :=
  NatIso.ofComponents fun _ => isoMk <| Iso.refl _

/-- `StructuredArrow.map` is a special case of `StructuredArrow.map₂` up to natural isomorphism. -/
def mapIsoMap₂ {S S' : D} (f : S ⟶ S') : map (T := T) f ≅ map₂ (F := 𝟭 _) (G := 𝟭 _) f (𝟙 T) :=
  NatIso.ofComponents fun _ => isoMk <| Iso.refl _

/-- `StructuredArrow.pre` is a special case of `StructuredArrow.map₂` up to natural isomorphism. -/
def preIsoMap₂ (S : D) (F : B ⥤ C) (G : C ⥤ D) :
    pre S F G ≅ map₂ (G := 𝟭 _) (𝟙 _) (𝟙 (F ⋙ G)) :=
  NatIso.ofComponents fun _ => isoMk <| Iso.refl _

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
def CostructuredArrow (S : C ⥤ D) (T : D) :=
  Comma S (Functor.fromPUnit.{0} T)

instance (S : C ⥤ D) (T : D) : Category (CostructuredArrow S T) := commaCategory

namespace CostructuredArrow

/-- The obvious projection functor from costructured arrows. -/
@[simps!]
def proj (S : C ⥤ D) (T : D) : CostructuredArrow S T ⥤ C :=
  Comma.fst _ _

variable {T T' T'' : D} {Y Y' Y'' : C} {S S' : C ⥤ D}

@[ext]
lemma hom_ext {X Y : CostructuredArrow S T} (f g : X ⟶ Y) (h : f.left = g.left) : f = g :=
  CommaMorphism.ext h (Subsingleton.elim _ _)

@[simp]
theorem hom_eq_iff {X Y : CostructuredArrow S T} (f g : X ⟶ Y) : f = g ↔ f.left = g.left :=
  ⟨fun h ↦ by rw [h], hom_ext _ _⟩

/-- Construct a costructured arrow from a morphism. -/
def mk (f : S.obj Y ⟶ T) : CostructuredArrow S T :=
  ⟨Y, ⟨⟨⟩⟩, f⟩

@[simp]
theorem mk_left (f : S.obj Y ⟶ T) : (mk f).left = Y :=
  rfl

@[simp]
theorem mk_right (f : S.obj Y ⟶ T) : (mk f).right = ⟨⟨⟩⟩ :=
  rfl

@[simp]
theorem mk_hom_eq_self (f : S.obj Y ⟶ T) : (mk f).hom = f :=
  rfl

@[reassoc]
theorem w {A B : CostructuredArrow S T} (f : A ⟶ B) : S.map f.left ≫ B.hom = A.hom := by simp

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
theorem right_eq_id {X Y : CostructuredArrow S T} (f : X ⟶ Y) : f.right = 𝟙 X.right := rfl

/-- To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps! left]
def homMk {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left)
    (w : S.map g ≫ f'.hom = f.hom := by cat_disch) : f ⟶ f' where
  left := g
  right := 𝟙 f.right

theorem homMk_surjective {f f' : CostructuredArrow S T} (φ : f ⟶ f') :
    ∃ (ψ : f.left ⟶ f'.left) (hψ : S.map ψ ≫ f'.hom = f.hom),
      φ = CostructuredArrow.homMk ψ hψ :=
  ⟨φ.left, CostructuredArrow.w φ, rfl⟩

/-- Given a costructured arrow `S(Y) ⟶ X`, and an arrow `Y' ⟶ Y'`, we can construct a morphism of
costructured arrows given by `(S(Y) ⟶ X) ⟶ (S(Y') ⟶ S(Y) ⟶ X)`. -/
@[simps]
def homMk' (f : CostructuredArrow S T) (g : Y' ⟶ f.left) : mk (S.map g ≫ f.hom) ⟶ f where
  left := g
  right := 𝟙 _

lemma homMk'_id (f : CostructuredArrow S T) : homMk' f (𝟙 f.left) = eqToHom (by cat_disch) := by
  simp [eqToHom_left]

lemma homMk'_mk_id (f : S.obj Y ⟶ T) : homMk' (mk f) (𝟙 Y) = eqToHom (by simp) :=
  homMk'_id _

lemma homMk'_comp (f : CostructuredArrow S T) (g : Y' ⟶ f.left) (g' : Y'' ⟶ Y') :
    homMk' f (g' ≫ g) = eqToHom (by simp) ≫ homMk' (mk (S.map g ≫ f.hom)) g' ≫ homMk' f g := by
  simp [eqToHom_left]

lemma homMk'_mk_comp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    homMk' (mk f) (g' ≫ g) = eqToHom (by simp) ≫ homMk' (mk (S.map g ≫ f)) g' ≫ homMk' (mk f) g :=
  homMk'_comp _ _ _

/-- Variant of `homMk'` where both objects are applications of `mk`. -/
@[simps]
def mkPrecomp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) : mk (S.map g ≫ f) ⟶ mk f where
  left := g
  right := 𝟙 _

lemma mkPrecomp_id (f : S.obj Y ⟶ T) : mkPrecomp f (𝟙 Y) = eqToHom (by simp) := by simp
lemma mkPrecomp_comp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    mkPrecomp f (g' ≫ g) = eqToHom (by simp) ≫ mkPrecomp (S.map g ≫ f) g' ≫ mkPrecomp f g := by
  simp

/-- To construct an isomorphism of costructured arrows,
we need an isomorphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps! hom_left inv_left]
def isoMk {f f' : CostructuredArrow S T} (g : f.left ≅ f'.left)
    (w : S.map g.hom ≫ f'.hom = f.hom := by cat_disch) : f ≅ f' :=
  Comma.isoMk g (eqToIso (by ext)) (by simpa using w)

theorem obj_ext (x y : CostructuredArrow S T) (hl : x.left = y.left)
    (hh : S.map (eqToHom hl) ≫ y.hom = x.hom) : x = y := by
  cases x
  cases y
  cases hl
  cat_disch

theorem ext {A B : CostructuredArrow S T} (f g : A ⟶ B) (h : f.left = g.left) : f = g :=
  CommaMorphism.ext h (Subsingleton.elim _ _)

theorem ext_iff {A B : CostructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.left = g.left :=
  ⟨fun h => h ▸ rfl, ext f g⟩

instance proj_faithful : (proj S T).Faithful where map_injective {_ _} := ext

theorem mono_of_mono_left {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Mono f.left] : Mono f :=
  (proj S T).mono_of_mono_map h

/-- The converse of this is true with additional assumptions, see `epi_iff_epi_left`. -/
theorem epi_of_epi_left {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Epi f.left] : Epi f :=
  (proj S T).epi_of_epi_map h

instance mono_homMk {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Mono f] :
    Mono (homMk f w) :=
  (proj S T).mono_of_mono_map h

instance epi_homMk {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Epi f] :
    Epi (homMk f w) :=
  (proj S T).epi_of_epi_map h

/-- Eta rule for costructured arrows. Prefer `CostructuredArrow.eta` for rewriting, as equality of
objects tends to cause problems. -/
theorem eq_mk (f : CostructuredArrow S T) : f = mk f.hom :=
  rfl

/-- Eta rule for costructured arrows. -/
@[simps! hom_left inv_left]
def eta (f : CostructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _)

lemma mk_surjective (f : CostructuredArrow S T) :
    ∃ (Y : C) (g : S.obj Y ⟶ T), f = mk g :=
  ⟨_, _, eq_mk f⟩

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

@[simp]
theorem map_mk {f : S.obj Y ⟶ T} (g : T ⟶ T') : (map g).obj (mk f) = mk (f ≫ g) :=
  rfl

@[simp]
theorem map_id {f : CostructuredArrow S T} : (map (𝟙 T)).obj f = f := by
  rw [eq_mk f]
  simp

@[simp]
theorem map_comp {f : T ⟶ T'} {f' : T' ⟶ T''} {h : CostructuredArrow S T} :
    (map (f ≫ f')).obj h = (map f').obj ((map f).obj h) := by
  rw [eq_mk h]
  simp

/-- An isomorphism `T ≅ T'` induces an equivalence
`CostructuredArrow S T ≌ CostructuredArrow S T'`. -/
@[simps!]
def mapIso (i : T ≅ T') : CostructuredArrow S T ≌ CostructuredArrow S T' :=
  Comma.mapRightIso _ ((Functor.const _).mapIso i)

/-- A natural isomorphism `S ≅ S'` induces an equivalence
`CostrucutredArrow S T ≌ CostructuredArrow S' T`. -/
@[simps!]
def mapNatIso (i : S ≅ S') : CostructuredArrow S T ≌ CostructuredArrow S' T :=
  Comma.mapLeftIso _ i

instance proj_reflectsIsomorphisms : (proj S T).ReflectsIsomorphisms where
  reflects {Y Z} f t :=
    ⟨⟨CostructuredArrow.homMk
        (inv ((proj S T).map f))
        (by rw [Functor.map_inv, IsIso.inv_comp_eq]; simp),
      by constructor <;> ext <;> dsimp at t ⊢ <;> simp⟩⟩

open CategoryTheory.Limits

/-- The identity costructured arrow is terminal. -/
noncomputable def mkIdTerminal [S.Full] [S.Faithful] : IsTerminal (mk (𝟙 (S.obj Y))) where
  lift c := homMk (S.preimage c.pt.hom)
  uniq := by
    rintro c m -
    ext
    apply S.map_injective
    simpa only [homMk_left, S.map_preimage, ← w m] using (Category.comp_id _).symm

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(F ⋙ G, S) ⥤ (G, S)`. -/
@[simps!]
def pre (F : B ⥤ C) (G : C ⥤ D) (S : D) : CostructuredArrow (F ⋙ G) S ⥤ CostructuredArrow G S :=
  Comma.preLeft F G _

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
  map f := CostructuredArrow.homMk f.left (by simp [Functor.comp_map, ← G.map_comp])

instance (F : B ⥤ C) (G : C ⥤ D) (S : C) : (post F G S).Faithful where
  map_injective {_ _} _ _ h := by simpa [ext_iff] using h

instance (F : B ⥤ C) (G : C ⥤ D) (S : C) [G.Faithful] : (post F G S).Full where
  map_surjective f := ⟨homMk f.left (G.map_injective (by simpa using f.w)), by simp⟩

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

/-- `CostructuredArrow.post` is a special case of `CostructuredArrow.map₂` up to natural
isomorphism. -/
def postIsoMap₂ (S : C) (F : B ⥤ C) (G : C ⥤ D) :
    post F G S ≅ map₂ (F := 𝟭 _) (𝟙 (F ⋙ G)) (𝟙 _) :=
  NatIso.ofComponents fun _ => isoMk <| Iso.refl _

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
  map f := CostructuredArrow.homMk f.unop.right.op (by simp [← op_comp])

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
          f.unop.w]
        simp)

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
  map f := StructuredArrow.homMk f.unop.left.op (by simp [← op_comp])

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
        simp)

end CostructuredArrow

/-- For a functor `F : C ⥤ D` and an object `d : D`, the category of structured arrows `d ⟶ F.obj c`
is contravariantly equivalent to the category of costructured arrows `F.op.obj c ⟶ op d`.
-/
def structuredArrowOpEquivalence (F : C ⥤ D) (d : D) :
    (StructuredArrow d F)ᵒᵖ ≌ CostructuredArrow F.op (op d) where
  functor := StructuredArrow.toCostructuredArrow F d
  inverse := (CostructuredArrow.toStructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
      (fun X => (StructuredArrow.isoMk (Iso.refl _)).op)
      fun {X Y} f => Quiver.Hom.unop_inj <| by
        apply CommaMorphism.ext <;>
          dsimp [StructuredArrow.isoMk, Comma.isoMk,StructuredArrow.homMk]; simp
  counitIso := NatIso.ofComponents
      (fun X => CostructuredArrow.isoMk (Iso.refl _))
      fun {X Y} f => by
        apply CommaMorphism.ext <;>
          dsimp [CostructuredArrow.isoMk, Comma.isoMk, CostructuredArrow.homMk]; simp

/-- For a functor `F : C ⥤ D` and an object `d : D`, the category of costructured arrows
`F.obj c ⟶ d` is contravariantly equivalent to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
def costructuredArrowOpEquivalence (F : C ⥤ D) (d : D) :
    (CostructuredArrow F d)ᵒᵖ ≌ StructuredArrow (op d) F.op where
  functor := CostructuredArrow.toStructuredArrow F d
  inverse := (StructuredArrow.toCostructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
      (fun X => (CostructuredArrow.isoMk (Iso.refl _)).op)
      fun {X Y} f => Quiver.Hom.unop_inj <| by
        apply CommaMorphism.ext <;>
          dsimp [CostructuredArrow.isoMk, CostructuredArrow.homMk, Comma.isoMk]; simp
  counitIso := NatIso.ofComponents
      (fun X => StructuredArrow.isoMk (Iso.refl _))
      fun {X Y} f => by
        apply CommaMorphism.ext <;>
          dsimp [StructuredArrow.isoMk, StructuredArrow.homMk, Comma.isoMk]; simp

section Pre

variable {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G : D ⥤ E} {e : E}

/-- The functor establishing the equivalence `StructuredArrow.preEquivalence`. -/
@[simps!]
def StructuredArrow.preEquivalenceFunctor (f : StructuredArrow e G) :
    StructuredArrow f (pre e F G) ⥤ StructuredArrow f.right F where
  obj g := mk g.hom.right
  map φ := homMk φ.right.right <| by
    have := w φ
    simp only [Functor.const_obj_obj] at this ⊢
    rw [← this, comp_right]
    simp

/-- The inverse functor establishing the equivalence `StructuredArrow.preEquivalence`. -/
@[simps!]
def StructuredArrow.preEquivalenceInverse (f : StructuredArrow e G) :
    StructuredArrow f.right F ⥤ StructuredArrow f (pre e F G) where
  obj g := mk
            (Y := mk (Y := g.right)
              (f.hom ≫ (G.map g.hom : G.obj f.right ⟶ (F ⋙ G).obj g.right)))
            (homMk g.hom)
  map φ := homMk <| homMk φ.right <| by
    simp only [Functor.const_obj_obj, Functor.comp_obj, mk_right, mk_left, mk_hom_eq_self,
      Functor.comp_map, Category.assoc, ← w φ, Functor.map_comp]

/-- A structured arrow category on a `StructuredArrow.pre e F G` functor is equivalent to the
structured arrow category on F -/
@[simps]
def StructuredArrow.preEquivalence (f : StructuredArrow e G) :
    StructuredArrow f (pre e F G) ≌ StructuredArrow f.right F where
  functor := preEquivalenceFunctor F f
  inverse := preEquivalenceInverse F f
  unitIso := NatIso.ofComponents (fun _ => isoMk (isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

/-- The functor `StructuredArrow d T ⥤ StructuredArrow e (T ⋙ S)` that `u : e ⟶ S.obj d`
induces via `StructuredArrow.map₂` can be expressed up to isomorphism by
`StructuredArrow.preEquivalence` and `StructuredArrow.proj`. -/
def StructuredArrow.map₂IsoPreEquivalenceInverseCompProj {T : C ⥤ D} {S : D ⥤ E} {T' : C ⥤ E}
    (d : D) (e : E) (u : e ⟶ S.obj d) (α : T ⋙ S ⟶ T') :
    map₂ (F := 𝟭 _) u α ≅ (preEquivalence T (mk u)).inverse ⋙ proj (mk u) (pre _ T S) ⋙
      map₂ (F := 𝟭 _) (G := 𝟭 _) (𝟙 _) α :=
  NatIso.ofComponents fun _ => isoMk (Iso.refl _)

/-- The functor establishing the equivalence `CostructuredArrow.preEquivalence`. -/
@[simps!]
def CostructuredArrow.preEquivalence.functor (f : CostructuredArrow G e) :
    CostructuredArrow (pre F G e) f ⥤ CostructuredArrow F f.left where
  obj g := mk g.hom.left
  map φ := homMk φ.left.left <| by
    have := w φ
    simp only [Functor.const_obj_obj] at this ⊢
    rw [← this, comp_left]
    simp

/-- The inverse functor establishing the equivalence `CostructuredArrow.preEquivalence`. -/
@[simps!]
def CostructuredArrow.preEquivalence.inverse (f : CostructuredArrow G e) :
    CostructuredArrow F f.left ⥤ CostructuredArrow (pre F G e) f where
  obj g := mk (Y := mk (Y := g.left) (G.map g.hom ≫ f.hom)) (homMk g.hom)
  map φ := homMk <| homMk φ.left <| by
    simp only [Functor.const_obj_obj, Functor.comp_obj, mk_left, Functor.comp_map, mk_hom_eq_self,
      ← w φ, Functor.map_comp, Category.assoc]

/-- A costructured arrow category on a `CostructuredArrow.pre F G e` functor is equivalent to the
costructured arrow category on F -/
def CostructuredArrow.preEquivalence (f : CostructuredArrow G e) :
    CostructuredArrow (pre F G e) f ≌ CostructuredArrow F f.left where
  functor := preEquivalence.functor F f
  inverse := preEquivalence.inverse F f
  unitIso := NatIso.ofComponents (fun _ => isoMk (isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

/-- The functor `CostructuredArrow T d ⥤ CostructuredArrow (T ⋙ S) e` that `u : S.obj d ⟶ e`
induces via `CostructuredArrow.map₂` can be expressed up to isomorphism by
`CostructuredArrow.preEquivalence` and `CostructuredArrow.proj`. -/
def CostructuredArrow.map₂IsoPreEquivalenceInverseCompProj (T : C ⥤ D) (S : D ⥤ E) (d : D) (e : E)
    (u : S.obj d ⟶ e) :
    map₂ (F := 𝟭 _) (U := T ⋙ S) (𝟙 (T ⋙ S)) u ≅
      (preEquivalence T (mk u)).inverse ⋙ proj (pre T S _) (mk u) :=
  NatIso.ofComponents fun _ => isoMk (Iso.refl _)

end Pre

section Prod

section

variable {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  (S : D) (S' : D') (T : C ⥤ D) (T' : C' ⥤ D')

@[reassoc (attr := simp)]
theorem StructuredArrow.w_prod_fst {X Y : StructuredArrow (S, S') (T.prod T')}
    (f : X ⟶ Y) : X.hom.1 ≫ T.map f.right.1 = Y.hom.1 :=
  congr_arg _root_.Prod.fst (StructuredArrow.w f)

@[reassoc (attr := simp)]
theorem StructuredArrow.w_prod_snd {X Y : StructuredArrow (S, S') (T.prod T')}
    (f : X ⟶ Y) : X.hom.2 ≫ T'.map f.right.2 = Y.hom.2 :=
  congr_arg _root_.Prod.snd (StructuredArrow.w f)

/-- Implementation; see `StructuredArrow.prodEquivalence`. -/
@[simps]
def StructuredArrow.prodFunctor :
    StructuredArrow (S, S') (T.prod T') ⥤ StructuredArrow S T × StructuredArrow S' T' where
  obj f := ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨StructuredArrow.homMk η.right.1 (by simp),
            StructuredArrow.homMk η.right.2 (by simp)⟩

/-- Implementation; see `StructuredArrow.prodEquivalence`. -/
@[simps]
def StructuredArrow.prodInverse :
    StructuredArrow S T × StructuredArrow S' T' ⥤ StructuredArrow (S, S') (T.prod T') where
  obj f := .mk (Y := (f.1.right, f.2.right)) ⟨f.1.hom, f.2.hom⟩
  map η := StructuredArrow.homMk ⟨η.1.right, η.2.right⟩ (by simp)

/-- The natural equivalence
`StructuredArrow (S, S') (T.prod T') ≌ StructuredArrow S T × StructuredArrow S' T'`. -/
@[simps]
def StructuredArrow.prodEquivalence :
    StructuredArrow (S, S') (T.prod T') ≌ StructuredArrow S T × StructuredArrow S' T' where
  functor := StructuredArrow.prodFunctor S S' T T'
  inverse := StructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)

end

section

variable {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  (S : C ⥤ D) (S' : C' ⥤ D') (T : D) (T' : D')

@[reassoc (attr := simp)]
theorem CostructuredArrow.w_prod_fst {A B : CostructuredArrow (S.prod S') (T, T')} (f : A ⟶ B) :
    S.map f.left.1 ≫ B.hom.1 = A.hom.1 :=
  congr_arg _root_.Prod.fst (CostructuredArrow.w f)

@[reassoc (attr := simp)]
theorem CostructuredArrow.w_prod_snd {A B : CostructuredArrow (S.prod S') (T, T')} (f : A ⟶ B) :
    S'.map f.left.2 ≫ B.hom.2 = A.hom.2 :=
  congr_arg _root_.Prod.snd (CostructuredArrow.w f)

/-- Implementation; see `CostructuredArrow.prodEquivalence`. -/
@[simps]
def CostructuredArrow.prodFunctor :
    CostructuredArrow (S.prod S') (T, T') ⥤ CostructuredArrow S T × CostructuredArrow S' T' where
  obj f := ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨CostructuredArrow.homMk η.left.1 (by simp),
            CostructuredArrow.homMk η.left.2 (by simp)⟩

/-- Implementation; see `CostructuredArrow.prodEquivalence`. -/
@[simps]
def CostructuredArrow.prodInverse :
    CostructuredArrow S T × CostructuredArrow S' T' ⥤ CostructuredArrow (S.prod S') (T, T') where
  obj f := .mk (Y := (f.1.left, f.2.left)) ⟨f.1.hom, f.2.hom⟩
  map η := CostructuredArrow.homMk ⟨η.1.left, η.2.left⟩ (by simp)

/-- The natural equivalence
`CostructuredArrow (S.prod S') (T, T') ≌ CostructuredArrow S T × CostructuredArrow S' T'`. -/
@[simps]
def CostructuredArrow.prodEquivalence :
    CostructuredArrow (S.prod S') (T, T') ≌ CostructuredArrow S T × CostructuredArrow S' T' where
  functor := CostructuredArrow.prodFunctor S S' T T'
  inverse := CostructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)

end

end Prod

end CategoryTheory
