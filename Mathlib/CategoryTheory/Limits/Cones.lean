/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Floris van Doorn
-/
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Cones and cocones

We define `Cone F`, a cone over a functor `F`,
and `F.cones : Cᵒᵖ ⥤ Type`, the functor associating to `X` the cones over `F` with cone point `X`.

A cone `c` is defined by specifying its cone point `c.pt` and a natural transformation `c.π`
from the constant `c.pt`-valued functor to `F`.

We provide `c.w f : c.π.app j ≫ F.map f = c.π.app j'` for any `f : j ⟶ j'`
as a wrapper for `c.π.naturality f` avoiding unneeded identity morphisms.

We define `c.extend f`, where `c : cone F` and `f : Y ⟶ c.pt` for some other `Y`,
which replaces the cone point by `Y` and inserts `f` into each of the components of the cone.
Similarly we have `c.whisker F` producing a `Cone (E ⋙ F)`

We define morphisms of cones, and the category of cones.

We define `Cone.postcompose α : cone F ⥤ cone G` for `α` a natural transformation `F ⟶ G`.

And, of course, we dualise all this to cocones as well.

For more results about the category of cones, see `cone_category.lean`.
-/


-- morphism levels before object levels. See note [category theory universes].
universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

open CategoryTheory

variable {J : Type u₁} [Category.{v₁} J]
variable {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory

namespace Functor

variable (F : J ⥤ C)

/-- If `F : J ⥤ C` then `F.cones` is the functor assigning to an object `X : C` the
type of natural transformations from the constant functor with value `X` to `F`.
An object representing this functor is a limit of `F`.
-/
@[simps!]
def cones : Cᵒᵖ ⥤ Type max u₁ v₃ :=
  (const J).op ⋙ yoneda.obj F

/-- If `F : J ⥤ C` then `F.cocones` is the functor assigning to an object `(X : C)`
the type of natural transformations from `F` to the constant functor with value `X`.
An object corepresenting this functor is a colimit of `F`.
-/
@[simps!]
def cocones : C ⥤ Type max u₁ v₃ :=
  const J ⋙ coyoneda.obj (op F)

end Functor

section

variable (J C)

/-- Functorially associated to each functor `J ⥤ C`, we have the `C`-presheaf consisting of
cones with a given cone point.
-/
@[simps!]
def cones : (J ⥤ C) ⥤ Cᵒᵖ ⥤ Type max u₁ v₃ where
  obj := Functor.cones
  map f := whiskerLeft (const J).op (yoneda.map f)

/-- Contravariantly associated to each functor `J ⥤ C`, we have the `C`-copresheaf consisting of
cocones with a given cocone point.
-/
@[simps!]
def cocones : (J ⥤ C)ᵒᵖ ⥤ C ⥤ Type max u₁ v₃ where
  obj F := Functor.cocones (unop F)
  map f := whiskerLeft (const J) (coyoneda.map f)

end

namespace Limits

section

/-- A `c : Cone F` is:
* an object `c.pt` and
* a natural transformation `c.π : c.pt ⟶ F` from the constant `c.pt` functor to `F`.

Example: if `J` is a category coming from a poset then the data required to make
a term of type `Cone F` is morphisms `πⱼ : c.pt ⟶ F j` for all `j : J` and,
for all `i ≤ j` in `J`, morphisms `πᵢⱼ : F i ⟶ F j` such that `πᵢ ≫ πᵢⱼ = πⱼ`.

`Cone F` is equivalent, via `cone.equiv` below, to `Σ X, F.cones.obj X`.
-/
structure Cone (F : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from the constant functor at `X` to `F` -/
  π : (const J).obj pt ⟶ F

instance inhabitedCone (F : Discrete PUnit ⥤ C) : Inhabited (Cone F) :=
  ⟨{  pt := F.obj ⟨⟨⟩⟩
      π := { app := fun ⟨⟨⟩⟩ => 𝟙 _
             naturality := by
              intro X Y f
              match X, Y, f with
              | .mk A, .mk B, .up g =>
                cat_disch
           }
  }⟩

@[reassoc (attr := simp)]
theorem Cone.w {F : J ⥤ C} (c : Cone F) {j j' : J} (f : j ⟶ j') :
    c.π.app j ≫ F.map f = c.π.app j' := by
  rw [← c.π.naturality f]
  apply id_comp

/-- A `c : Cocone F` is
* an object `c.pt` and
* a natural transformation `c.ι : F ⟶ c.pt` from `F` to the constant `c.pt` functor.

For example, if the source `J` of `F` is a partially ordered set, then to give
`c : Cocone F` is to give a collection of morphisms `ιⱼ : F j ⟶ c.pt` and, for
all `j ≤ k` in `J`, morphisms `ιⱼₖ : F j ⟶ F k` such that `Fⱼₖ ≫ Fₖ = Fⱼ` for all `j ≤ k`.

`Cocone F` is equivalent, via `Cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
structure Cocone (F : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from `F` to the constant functor at `pt` -/
  ι : F ⟶ (const J).obj pt

instance inhabitedCocone (F : Discrete PUnit ⥤ C) : Inhabited (Cocone F) :=
  ⟨{  pt := F.obj ⟨⟨⟩⟩
      ι := { app := fun ⟨⟨⟩⟩ => 𝟙 _
             naturality := by
              intro X Y f
              match X, Y, f with
              | .mk A, .mk B, .up g =>
                simp
           }
  }⟩

@[reassoc]
theorem Cocone.w {F : J ⥤ C} (c : Cocone F) {j j' : J} (f : j ⟶ j') :
    F.map f ≫ c.ι.app j' = c.ι.app j := by
  rw [c.ι.naturality f]
  apply comp_id

end

variable {F : J ⥤ C}

namespace Cone

/-- The isomorphism between a cone on `F` and an element of the functor `F.cones`. -/
@[simps!]
def equiv (F : J ⥤ C) : Cone F ≅ Σ X, F.cones.obj X where
  hom c := ⟨op c.pt, c.π⟩
  inv c :=
    { pt := c.1.unop
      π := c.2 }
  hom_inv_id := by
    funext X
    cases X
    rfl
  inv_hom_id := by
    funext X
    cases X
    rfl

/-- A map to the vertex of a cone naturally induces a cone by composition. -/
@[simps]
def extensions (c : Cone F) : yoneda.obj c.pt ⋙ uliftFunctor.{u₁} ⟶ F.cones where
  app _ f := (const J).map f.down ≫ c.π

/-- A map to the vertex of a cone induces a cone by composition. -/
@[simps]
def extend (c : Cone F) {X : C} (f : X ⟶ c.pt) : Cone F :=
  { pt := X
    π := c.extensions.app (op X) ⟨f⟩ }

/-- Whisker a cone by precomposition of a functor. -/
@[simps]
def whisker (E : K ⥤ J) (c : Cone F) : Cone (E ⋙ F) where
  pt := c.pt
  π := whiskerLeft E c.π

end Cone

namespace Cocone

/-- The isomorphism between a cocone on `F` and an element of the functor `F.cocones`. -/
def equiv (F : J ⥤ C) : Cocone F ≅ Σ X, F.cocones.obj X where
  hom c := ⟨c.pt, c.ι⟩
  inv c :=
    { pt := c.1
      ι := c.2 }
  hom_inv_id := by
    funext X
    cases X
    rfl
  inv_hom_id := by
    funext X
    cases X
    rfl

/-- A map from the vertex of a cocone naturally induces a cocone by composition. -/
@[simps]
def extensions (c : Cocone F) : coyoneda.obj (op c.pt) ⋙ uliftFunctor.{u₁} ⟶ F.cocones where
  app _ f := c.ι ≫ (const J).map f.down

/-- A map from the vertex of a cocone induces a cocone by composition. -/
@[simps]
def extend (c : Cocone F) {Y : C} (f : c.pt ⟶ Y) : Cocone F where
  pt := Y
  ι := c.extensions.app Y ⟨f⟩

/-- Whisker a cocone by precomposition of a functor. See `whiskering` for a functorial
version.
-/
@[simps]
def whisker (E : K ⥤ J) (c : Cocone F) : Cocone (E ⋙ F) where
  pt := c.pt
  ι := whiskerLeft E c.ι

end Cocone

/-- A cone morphism between two cones for the same diagram is a morphism of the cone points which
commutes with the cone legs. -/
structure ConeMorphism (A B : Cone F) where
  /-- A morphism between the two vertex objects of the cones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  w : ∀ j : J, hom ≫ B.π.app j = A.π.app j := by cat_disch

attribute [reassoc (attr := simp)] ConeMorphism.w

instance inhabitedConeMorphism (A : Cone F) : Inhabited (ConeMorphism A A) :=
  ⟨{ hom := 𝟙 _ }⟩

/-- The category of cones on a given diagram. -/
@[simps]
instance Cone.category : Category (Cone F) where
  Hom A B := ConeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/- We do not want `simps` automatically generate the lemma for simplifying the
hom field of a category. So we need to write the `ext` lemma in terms of the
categorical morphism, rather than the underlying structure. -/
@[ext]
theorem ConeMorphism.ext {c c' : Cone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

@[reassoc (attr := simp)]
lemma ConeMorphism.hom_inv_id {c d : Cone F} (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

@[reassoc (attr := simp)]
lemma ConeMorphism.inv_hom_id {c d : Cone F} (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

instance {c d : Cone F} (f : c ≅ d) : IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

instance {c d : Cone F} (f : c ≅ d) : IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

@[reassoc (attr := simp)]
lemma ConeMorphism.map_w {c c' : Cone F} (f : c ⟶ c') (G : C ⥤ D) (j : J) :
    G.map f.hom ≫ G.map (c'.π.app j) = G.map (c.π.app j) := by
  simp only [← map_comp, ConeMorphism.w]

namespace Cones

/-- To give an isomorphism between cones, it suffices to give an
  isomorphism between their vertices which commutes with the cone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {c c' : Cone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      w := fun j => φ.inv_comp_eq.mpr (w j) }

/-- Eta rule for cones. -/
@[simps!]
def eta (c : Cone F) : c ≅ ⟨c.pt, c.π⟩ :=
  Cones.ext (Iso.refl _)

/-- Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
theorem cone_iso_of_hom_iso {K : J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.hom] : IsIso f :=
  ⟨⟨{   hom := inv f.hom
        w := fun j => (asIso f.hom).inv_comp_eq.2 (f.w j).symm }, by cat_disch⟩⟩

/-- There is a morphism from an extended cone to the original cone. -/
@[simps]
def extend (s : Cone F) {X : C} (f : X ⟶ s.pt) : s.extend f ⟶ s where
  hom := f

/-- Extending a cone by the identity does nothing. -/
@[simps!]
def extendId (s : Cone F) : s.extend (𝟙 s.pt) ≅ s :=
  Cones.ext (Iso.refl _)

/-- Extending a cone by a composition is the same as extending the cone twice. -/
@[simps!]
def extendComp (s : Cone F) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ s.pt) :
    s.extend (f ≫ g) ≅ (s.extend g).extend f :=
  Cones.ext (Iso.refl _)

/-- A cone extended by an isomorphism is isomorphic to the original cone. -/
@[simps]
def extendIso (s : Cone F) {X : C} (f : X ≅ s.pt) : s.extend f.hom ≅ s where
  hom := { hom := f.hom }
  inv := { hom := f.inv }

instance {s : Cone F} {X : C} (f : X ⟶ s.pt) [IsIso f] : IsIso (Cones.extend s f) :=
  ⟨(extendIso s (asIso f)).inv, by cat_disch⟩

/--
Functorially postcompose a cone for `F` by a natural transformation `F ⟶ G` to give a cone for `G`.
-/
@[simps]
def postcompose {G : J ⥤ C} (α : F ⟶ G) : Cone F ⥤ Cone G where
  obj c :=
    { pt := c.pt
      π := c.π ≫ α }
  map f := { hom := f.hom }

/-- Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
@[simps!]
def postcomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
  NatIso.ofComponents fun s => Cones.ext (Iso.refl _)

/-- Postcomposing by the identity does not change the cone up to isomorphism. -/
@[simps!]
def postcomposeId : postcompose (𝟙 F) ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun s => Cones.ext (Iso.refl _)

/-- If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cones.
-/
@[simps]
def postcomposeEquivalence {G : J ⥤ C} (α : F ≅ G) : Cone F ≌ Cone G where
  functor := postcompose α.hom
  inverse := postcompose α.inv
  unitIso := NatIso.ofComponents fun s => Cones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s => Cones.ext (Iso.refl _)

/-- Whiskering on the left by `E : K ⥤ J` gives a functor from `Cone F` to `Cone (E ⋙ F)`.
-/
@[simps]
def whiskering (E : K ⥤ J) : Cone F ⥤ Cone (E ⋙ F) where
  obj c := c.whisker E
  map f := { hom := f.hom }

/-- Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[simps]
def whiskeringEquivalence (e : K ≌ J) : Cone F ≌ Cone (e.functor ⋙ F) where
  functor := whiskering e.functor
  inverse := whiskering e.inverse ⋙ postcompose (e.invFunIdAssoc F).hom
  unitIso := NatIso.ofComponents fun s => Cones.ext (Iso.refl _)
  counitIso :=
    NatIso.ofComponents
      fun s =>
        Cones.ext (Iso.refl _)
          (by
            intro k
            simpa [e.counit_app_functor] using s.w (e.unitInv.app k))

/-- The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
@[simps! functor inverse unitIso counitIso]
def equivalenceOfReindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : Cone F ≌ Cone G :=
  (whiskeringEquivalence e).trans (postcomposeEquivalence α)

section

variable (F)

/-- Forget the cone structure and obtain just the cone point. -/
@[simps]
def forget : Cone F ⥤ C where
  obj t := t.pt
  map f := f.hom

variable (G : C ⥤ D)

/-- A functor `G : C ⥤ D` sends cones over `F` to cones over `F ⋙ G` functorially. -/
@[simps]
def functoriality : Cone F ⥤ Cone (F ⋙ G) where
  obj A :=
    { pt := G.obj A.pt
      π :=
        { app := fun j => G.map (A.π.app j)
          naturality := by intros; erw [← G.map_comp]; simp } }
  map f :=
    { hom := G.map f.hom
      w := ConeMorphism.map_w f G }

/-- Functoriality is functorial. -/
def functorialityCompFunctoriality (H : D ⥤ E) :
    functoriality F G ⋙ functoriality (F ⋙ G) H ≅ functoriality F (G ⋙ H) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp [functoriality])

instance functoriality_full [G.Full] [G.Faithful] : (functoriality F G).Full where
  map_surjective t :=
    ⟨{ hom := G.preimage t.hom
       w := fun j => G.map_injective (by simpa using t.w j) }, by cat_disch⟩

instance functoriality_faithful [G.Faithful] : (Cones.functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    ConeMorphism.ext f g <| G.map_injective <| congr_arg ConeMorphism.hom h

/-- If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cones over `F` and cones over `F ⋙ e.functor`.
-/
@[simps]
def functorialityEquivalence (e : C ≌ D) : Cone F ≌ Cone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  { functor := functoriality F e.functor
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (postcomposeEquivalence f).functor
    unitIso := NatIso.ofComponents fun c => Cones.ext (e.unitIso.app _)
    counitIso := NatIso.ofComponents fun c => Cones.ext (e.counitIso.app _) }

/-- If `F` reflects isomorphisms, then `Cones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cone_isomorphism (F : C ⥤ D) [F.ReflectsIsomorphisms] (K : J ⥤ C) :
    (Cones.functoriality K F).ReflectsIsomorphisms := by
  constructor
  intro A B f _
  haveI : IsIso (F.map f.hom) :=
    (Cones.forget (K ⋙ F)).map_isIso ((Cones.functoriality K F).map f)
  haveI := ReflectsIsomorphisms.reflects F f.hom
  apply cone_iso_of_hom_iso

end

end Cones

/-- A cocone morphism between two cocones for the same diagram is a morphism of the cocone points
which commutes with the cocone legs. -/
structure CoconeMorphism (A B : Cocone F) where
  /-- A morphism between the (co)vertex objects in `C` -/
  hom : A.pt ⟶ B.pt
  /-- The triangle made from the two natural transformations and `hom` commutes -/
  w : ∀ j : J, A.ι.app j ≫ hom = B.ι.app j := by cat_disch

instance inhabitedCoconeMorphism (A : Cocone F) : Inhabited (CoconeMorphism A A) :=
  ⟨{ hom := 𝟙 _ }⟩

attribute [reassoc (attr := simp)] CoconeMorphism.w

@[simps]
instance Cocone.category : Category (Cocone F) where
  Hom A B := CoconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/- We do not want `simps` automatically generate the lemma for simplifying the
hom field of a category. So we need to write the `ext` lemma in terms of the
categorical morphism, rather than the underlying structure. -/
@[ext]
theorem CoconeMorphism.ext {c c' : Cocone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

@[reassoc (attr := simp)]
lemma CoconeMorphism.hom_inv_id {c d : Cocone F} (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cocone.category_comp_hom]

@[reassoc (attr := simp)]
lemma CoconeMorphism.inv_hom_id {c d : Cocone F} (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cocone.category_comp_hom]

instance {c d : Cocone F} (f : c ≅ d) : IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

instance {c d : Cocone F} (f : c ≅ d) : IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

@[reassoc (attr := simp)]
lemma CoconeMorphism.map_w {c c' : Cocone F} (f : c ⟶ c') (G : C ⥤ D) (j : J) :
    G.map (c.ι.app j) ≫ G.map f.hom = G.map (c'.ι.app j) := by
  simp only [← map_comp, CoconeMorphism.w]

namespace Cocones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {c c' : Cocone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, c.ι.app j ≫ φ.hom = c'.ι.app j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      w := fun j => φ.comp_inv_eq.mpr (w j).symm }

/-- Eta rule for cocones. -/
@[simps!]
def eta (c : Cocone F) : c ≅ ⟨c.pt, c.ι⟩ :=
  Cocones.ext (Iso.refl _)

/-- Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/
theorem cocone_iso_of_hom_iso {K : J ⥤ C} {c d : Cocone K} (f : c ⟶ d) [i : IsIso f.hom] :
    IsIso f :=
  ⟨⟨{ hom := inv f.hom
      w := fun j => (asIso f.hom).comp_inv_eq.2 (f.w j).symm }, by cat_disch⟩⟩

/-- There is a morphism from a cocone to its extension. -/
@[simps]
def extend (s : Cocone F) {X : C} (f : s.pt ⟶ X) : s ⟶ s.extend f where
  hom := f

/-- Extending a cocone by the identity does nothing. -/
@[simps!]
def extendId (s : Cocone F) : s ≅ s.extend (𝟙 s.pt) :=
  Cocones.ext (Iso.refl _)

/-- Extending a cocone by a composition is the same as extending the cone twice. -/
@[simps!]
def extendComp (s : Cocone F) {X Y : C} (f : s.pt ⟶ X) (g : X ⟶ Y) :
    s.extend (f ≫ g) ≅ (s.extend f).extend g :=
  Cocones.ext (Iso.refl _)

/-- A cocone extended by an isomorphism is isomorphic to the original cone. -/
@[simps]
def extendIso (s : Cocone F) {X : C} (f : s.pt ≅ X) : s ≅ s.extend f.hom where
  hom := { hom := f.hom }
  inv := { hom := f.inv }

instance {s : Cocone F} {X : C} (f : s.pt ⟶ X) [IsIso f] : IsIso (Cocones.extend s f) :=
  ⟨(extendIso s (asIso f)).inv, by cat_disch⟩

/-- Functorially precompose a cocone for `F` by a natural transformation `G ⟶ F` to give a cocone
for `G`. -/
@[simps]
def precompose {G : J ⥤ C} (α : G ⟶ F) : Cocone F ⥤ Cocone G where
  obj c :=
    { pt := c.pt
      ι := α ≫ c.ι }
  map f := { hom := f.hom }

/-- Precomposing a cocone by the composite natural transformation `α ≫ β` is the same as
precomposing by `β` and then by `α`. -/
def precomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    precompose (α ≫ β) ≅ precompose β ⋙ precompose α :=
  NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)

/-- Precomposing by the identity does not change the cocone up to isomorphism. -/
def precomposeId : precompose (𝟙 F) ≅ 𝟭 (Cocone F) :=
  NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)

/-- If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cocones.
-/
@[simps]
def precomposeEquivalence {G : J ⥤ C} (α : G ≅ F) : Cocone F ≌ Cocone G where
  functor := precompose α.hom
  inverse := precompose α.inv
  unitIso := NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)

/-- Whiskering on the left by `E : K ⥤ J` gives a functor from `Cocone F` to `Cocone (E ⋙ F)`.
-/
@[simps]
def whiskering (E : K ⥤ J) : Cocone F ⥤ Cocone (E ⋙ F) where
  obj c := c.whisker E
  map f := { hom := f.hom }

/-- Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[simps]
def whiskeringEquivalence (e : K ≌ J) : Cocone F ≌ Cocone (e.functor ⋙ F) where
  functor := whiskering e.functor
  inverse :=
    whiskering e.inverse ⋙
      precompose
        ((Functor.leftUnitor F).inv ≫
          whiskerRight e.counitIso.inv F ≫ (Functor.associator _ _ _).inv)
  unitIso := NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s =>
    Cocones.ext (Iso.refl _) fun k => by simpa [e.counitInv_app_functor k] using s.w (e.unit.app k)

/--
The categories of cocones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
@[simps! functor_obj]
def equivalenceOfReindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : Cocone F ≌ Cocone G :=
  (whiskeringEquivalence e).trans (precomposeEquivalence α.symm)

section

variable (F)

/-- Forget the cocone structure and obtain just the cocone point. -/
@[simps]
def forget : Cocone F ⥤ C where
  obj t := t.pt
  map f := f.hom

variable (G : C ⥤ D)

/-- A functor `G : C ⥤ D` sends cocones over `F` to cocones over `F ⋙ G` functorially. -/
@[simps]
def functoriality : Cocone F ⥤ Cocone (F ⋙ G) where
  obj A :=
    { pt := G.obj A.pt
      ι :=
        { app := fun j => G.map (A.ι.app j)
          naturality := by intros; erw [← G.map_comp]; simp } }
  map f :=
    { hom := G.map f.hom
      w := CoconeMorphism.map_w f G }

/-- Functoriality is functorial. -/
def functorialityCompFunctoriality (H : D ⥤ E) :
    functoriality F G ⋙ functoriality (F ⋙ G) H ≅ functoriality F (G ⋙ H) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by simp [functoriality])

instance functoriality_full [G.Full] [G.Faithful] : (functoriality F G).Full where
  map_surjective t :=
    ⟨{ hom := G.preimage t.hom
       w := fun j => G.map_injective (by simpa using t.w j) }, by cat_disch⟩

instance functoriality_faithful [G.Faithful] : (functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    CoconeMorphism.ext f g <| G.map_injective <| congr_arg CoconeMorphism.hom h

/-- If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cocones over `F` and cocones over `F ⋙ e.functor`.
-/
@[simps]
def functorialityEquivalence (e : C ≌ D) : Cocone F ≌ Cocone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  { functor := functoriality F e.functor
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (precomposeEquivalence f.symm).functor
    unitIso := NatIso.ofComponents fun c => Cocones.ext (e.unitIso.app _)
    counitIso := NatIso.ofComponents fun c => Cocones.ext (e.counitIso.app _) }

/-- If `F` reflects isomorphisms, then `Cocones.functoriality F` reflects isomorphisms
as well.
-/
instance reflects_cocone_isomorphism (F : C ⥤ D) [F.ReflectsIsomorphisms] (K : J ⥤ C) :
    (Cocones.functoriality K F).ReflectsIsomorphisms := by
  constructor
  intro A B f _
  haveI : IsIso (F.map f.hom) :=
    (Cocones.forget (K ⋙ F)).map_isIso ((Cocones.functoriality K F).map f)
  haveI := ReflectsIsomorphisms.reflects F f.hom
  apply cocone_iso_of_hom_iso

end

end Cocones

end Limits

namespace Functor

variable (H : C ⥤ D) {F : J ⥤ C} {G : J ⥤ C}

open CategoryTheory.Limits

/-- The image of a cone in C under a functor G : C ⥤ D is a cone in D. -/
@[simps!]
def mapCone (c : Cone F) : Cone (F ⋙ H) :=
  (Cones.functoriality F H).obj c

/-- The construction `mapCone` respects functor composition. -/
@[simps!]
noncomputable def mapConeMapCone {F : J ⥤ C} {H : C ⥤ D} {H' : D ⥤ E} (c : Cone F) :
    H'.mapCone (H.mapCone c) ≅ (H ⋙ H').mapCone c := Cones.ext (Iso.refl _)

/-- The image of a cocone in C under a functor G : C ⥤ D is a cocone in D. -/
@[simps!]
def mapCocone (c : Cocone F) : Cocone (F ⋙ H) :=
  (Cocones.functoriality F H).obj c

/-- The construction `mapCocone` respects functor composition. -/
@[simps!]
noncomputable def mapCoconeMapCocone {F : J ⥤ C} {H : C ⥤ D} {H' : D ⥤ E} (c : Cocone F) :
    H'.mapCocone (H.mapCocone c) ≅ (H ⋙ H').mapCocone c := Cocones.ext (Iso.refl _)

/-- Given a cone morphism `c ⟶ c'`, construct a cone morphism on the mapped cones functorially. -/
def mapConeMorphism {c c' : Cone F} (f : c ⟶ c') : H.mapCone c ⟶ H.mapCone c' :=
  (Cones.functoriality F H).map f

/-- Given a cocone morphism `c ⟶ c'`, construct a cocone morphism on the mapped cocones
functorially. -/
def mapCoconeMorphism {c c' : Cocone F} (f : c ⟶ c') : H.mapCocone c ⟶ H.mapCocone c' :=
  (Cocones.functoriality F H).map f

/-- If `H` is an equivalence, we invert `H.mapCone` and get a cone for `F` from a cone
for `F ⋙ H`. -/
noncomputable def mapConeInv [IsEquivalence H] (c : Cone (F ⋙ H)) : Cone F :=
  (Limits.Cones.functorialityEquivalence F (asEquivalence H)).inverse.obj c

/-- `mapCone` is the left inverse to `mapConeInv`. -/
noncomputable def mapConeMapConeInv {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H]
    (c : Cone (F ⋙ H)) :
    mapCone H (mapConeInv H c) ≅ c :=
  (Limits.Cones.functorialityEquivalence F (asEquivalence H)).counitIso.app c

/-- `MapCone` is the right inverse to `mapConeInv`. -/
noncomputable def mapConeInvMapCone {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cone F) :
    mapConeInv H (mapCone H c) ≅ c :=
  (Limits.Cones.functorialityEquivalence F (asEquivalence H)).unitIso.symm.app c

/-- If `H` is an equivalence, we invert `H.mapCone` and get a cone for `F` from a cone
for `F ⋙ H`. -/
noncomputable def mapCoconeInv [IsEquivalence H] (c : Cocone (F ⋙ H)) : Cocone F :=
  (Limits.Cocones.functorialityEquivalence F (asEquivalence H)).inverse.obj c

/-- `mapCocone` is the left inverse to `mapCoconeInv`. -/
noncomputable def mapCoconeMapCoconeInv {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H]
    (c : Cocone (F ⋙ H)) :
    mapCocone H (mapCoconeInv H c) ≅ c :=
  (Limits.Cocones.functorialityEquivalence F (asEquivalence H)).counitIso.app c

/-- `mapCocone` is the right inverse to `mapCoconeInv`. -/
noncomputable def mapCoconeInvMapCocone {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cocone F) :
    mapCoconeInv H (mapCocone H c) ≅ c :=
  (Limits.Cocones.functorialityEquivalence F (asEquivalence H)).unitIso.symm.app c

/-- `functoriality F _ ⋙ postcompose (whisker_left F _)` simplifies to `functoriality F _`. -/
@[simps!]
def functorialityCompPostcompose {H H' : C ⥤ D} (α : H ≅ H') :
    Cones.functoriality F H ⋙ Cones.postcompose (whiskerLeft F α.hom) ≅ Cones.functoriality F H' :=
  NatIso.ofComponents fun c => Cones.ext (α.app _)

/-- For `F : J ⥤ C`, given a cone `c : Cone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the postcomposition of the cone `H.mapCone` using the isomorphism `α` is
isomorphic to the cone `H'.mapCone`.
-/
@[simps!]
def postcomposeWhiskerLeftMapCone {H H' : C ⥤ D} (α : H ≅ H') (c : Cone F) :
    (Cones.postcompose (whiskerLeft F α.hom :)).obj (mapCone H c) ≅ mapCone H' c :=
  (functorialityCompPostcompose α).app c

/--
`mapCone` commutes with `postcompose`. In particular, for `F : J ⥤ C`, given a cone `c : Cone F`, a
natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious ways of producing
a cone over `G ⋙ H`, and they are both isomorphic.
-/
@[simps!]
def mapConePostcompose {α : F ⟶ G} {c} :
    mapCone H ((Cones.postcompose α).obj c) ≅
      (Cones.postcompose (whiskerRight α H :)).obj (mapCone H c) :=
  Cones.ext (Iso.refl _)

/-- `mapCone` commutes with `postcomposeEquivalence`
-/
@[simps!]
def mapConePostcomposeEquivalenceFunctor {α : F ≅ G} {c} :
    mapCone H ((Cones.postcomposeEquivalence α).functor.obj c) ≅
      (Cones.postcomposeEquivalence (isoWhiskerRight α H :)).functor.obj (mapCone H c) :=
  Cones.ext (Iso.refl _)

/-- `functoriality F _ ⋙ precompose (whiskerLeft F _)` simplifies to `functoriality F _`. -/
@[simps!]
def functorialityCompPrecompose {H H' : C ⥤ D} (α : H ≅ H') :
    Cocones.functoriality F H ⋙ Cocones.precompose (whiskerLeft F α.inv) ≅
      Cocones.functoriality F H' :=
  NatIso.ofComponents fun c => Cocones.ext (α.app _)

/--
For `F : J ⥤ C`, given a cocone `c : Cocone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the precomposition of the cocone `H.mapCocone` using the isomorphism `α` is
isomorphic to the cocone `H'.mapCocone`.
-/
@[simps!]
def precomposeWhiskerLeftMapCocone {H H' : C ⥤ D} (α : H ≅ H') (c : Cocone F) :
    (Cocones.precompose (whiskerLeft F α.inv :)).obj (mapCocone H c) ≅ mapCocone H' c :=
  (functorialityCompPrecompose α).app c

/-- `map_cocone` commutes with `precompose`. In particular, for `F : J ⥤ C`, given a cocone
`c : Cocone F`, a natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious
ways of producing a cocone over `G ⋙ H`, and they are both isomorphic.
-/
@[simps!]
def mapCoconePrecompose {α : F ⟶ G} {c} :
    mapCocone H ((Cocones.precompose α).obj c) ≅
      (Cocones.precompose (whiskerRight α H :)).obj (mapCocone H c) :=
  Cocones.ext (Iso.refl _)

/-- `mapCocone` commutes with `precomposeEquivalence`
-/
@[simps!]
def mapCoconePrecomposeEquivalenceFunctor {α : F ≅ G} {c} :
    mapCocone H ((Cocones.precomposeEquivalence α).functor.obj c) ≅
      (Cocones.precomposeEquivalence (isoWhiskerRight α H :)).functor.obj (mapCocone H c) :=
  Cocones.ext (Iso.refl _)

/-- `mapCone` commutes with `whisker`
-/
@[simps!]
def mapConeWhisker {E : K ⥤ J} {c : Cone F} : mapCone H (c.whisker E) ≅ (mapCone H c).whisker E :=
  Cones.ext (Iso.refl _)

/-- `mapCocone` commutes with `whisker`
-/
@[simps!]
def mapCoconeWhisker {E : K ⥤ J} {c : Cocone F} :
    mapCocone H (c.whisker E) ≅ (mapCocone H c).whisker E :=
  Cocones.ext (Iso.refl _)

end Functor

end CategoryTheory

namespace CategoryTheory.Limits

section

variable {F : J ⥤ C}

/-- Change a `Cocone F` into a `Cone F.op`. -/
@[simps]
def Cocone.op (c : Cocone F) : Cone F.op where
  pt := Opposite.op c.pt
  π := NatTrans.op c.ι

/-- Change a `Cone F` into a `Cocone F.op`. -/
@[simps]
def Cone.op (c : Cone F) : Cocone F.op where
  pt := Opposite.op c.pt
  ι := NatTrans.op c.π

/-- Change a `Cocone F.op` into a `Cone F`. -/
@[simps]
def Cocone.unop (c : Cocone F.op) : Cone F where
  pt := Opposite.unop c.pt
  π := NatTrans.removeOp c.ι

/-- Change a `Cone F.op` into a `Cocone F`. -/
@[simps]
def Cone.unop (c : Cone F.op) : Cocone F where
  pt := Opposite.unop c.pt
  ι := NatTrans.removeOp c.π

variable (F)

/-- The category of cocones on `F`
is equivalent to the opposite category of
the category of cones on the opposite of `F`.
-/
def coconeEquivalenceOpConeOp : Cocone F ≌ (Cone F.op)ᵒᵖ where
  functor :=
    { obj := fun c => op (Cocone.op c)
      map := fun {X} {Y} f =>
        Quiver.Hom.op
          { hom := f.hom.op
            w := fun j => by
              apply Quiver.Hom.unop_inj
              dsimp
              apply CoconeMorphism.w } }
  inverse :=
    { obj := fun c => Cone.unop (unop c)
      map := fun {X} {Y} f =>
        { hom := f.unop.hom.unop
          w := fun j => by
            apply Quiver.Hom.op_inj
            dsimp
            apply ConeMorphism.w } }
  unitIso := NatIso.ofComponents (fun c => Cocones.ext (Iso.refl _))
  counitIso :=
    NatIso.ofComponents
      (fun c => (Cones.ext (Iso.refl c.unop.pt)).op)
      fun {X} {Y} f =>
      Quiver.Hom.unop_inj (ConeMorphism.ext _ _ (by simp))
  functor_unitIso_comp c := by
    apply Quiver.Hom.unop_inj
    apply ConeMorphism.ext
    dsimp
    apply comp_id

attribute [simps] coconeEquivalenceOpConeOp

end

section

variable {F : J ⥤ Cᵒᵖ}

/-- Change a cocone on `F.leftOp : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
@[simps!]
def coneOfCoconeLeftOp (c : Cocone F.leftOp) : Cone F where
  pt := op c.pt
  π := NatTrans.removeLeftOp c.ι

/-- Change a cone on `F : J ⥤ Cᵒᵖ` to a cocone on `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
def coconeLeftOpOfCone (c : Cone F) : Cocone F.leftOp where
  pt := unop c.pt
  ι := NatTrans.leftOp c.π

/- When trying use `@[simps]` to generate the `ι_app` field of this definition, `@[simps]` tries to
  reduce the RHS using `expr.dsimp` and `expr.simp`, but for some reason the expression is not
  being simplified properly. -/
/-- Change a cone on `F.leftOp : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
@[simps pt]
def coconeOfConeLeftOp (c : Cone F.leftOp) : Cocone F where
  pt := op c.pt
  ι := NatTrans.removeLeftOp c.π

@[simp]
theorem coconeOfConeLeftOp_ι_app (c : Cone F.leftOp) (j) :
    (coconeOfConeLeftOp c).ι.app j = (c.π.app (op j)).op := by
  dsimp only [coconeOfConeLeftOp]
  simp

/-- Change a cocone on `F : J ⥤ Cᵒᵖ` to a cone on `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[simps!]
def coneLeftOpOfCocone (c : Cocone F) : Cone F.leftOp where
  pt := unop c.pt
  π := NatTrans.leftOp c.ι

end

section

variable {F : Jᵒᵖ ⥤ C}

/-- Change a cocone on `F.rightOp : J ⥤ Cᵒᵖ` to a cone on `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def coneOfCoconeRightOp (c : Cocone F.rightOp) : Cone F where
  pt := unop c.pt
  π := NatTrans.removeRightOp c.ι

/-- Change a cone on `F : Jᵒᵖ ⥤ C` to a cocone on `F.rightOp : Jᵒᵖ ⥤ C`. -/
@[simps]
def coconeRightOpOfCone (c : Cone F) : Cocone F.rightOp where
  pt := op c.pt
  ι := NatTrans.rightOp c.π

/-- Change a cone on `F.rightOp : J ⥤ Cᵒᵖ` to a cocone on `F : Jᵒᵖ ⥤ C`. -/
@[simps]
def coconeOfConeRightOp (c : Cone F.rightOp) : Cocone F where
  pt := unop c.pt
  ι := NatTrans.removeRightOp c.π

/-- Change a cocone on `F : Jᵒᵖ ⥤ C` to a cone on `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[simps]
def coneRightOpOfCocone (c : Cocone F) : Cone F.rightOp where
  pt := op c.pt
  π := NatTrans.rightOp c.ι

end

section

variable {F : Jᵒᵖ ⥤ Cᵒᵖ}

/-- Change a cocone on `F.unop : J ⥤ C` into a cone on `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def coneOfCoconeUnop (c : Cocone F.unop) : Cone F where
  pt := op c.pt
  π := NatTrans.removeUnop c.ι

/-- Change a cone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cocone on `F.unop : J ⥤ C`. -/
@[simps]
def coconeUnopOfCone (c : Cone F) : Cocone F.unop where
  pt := unop c.pt
  ι := NatTrans.unop c.π

/-- Change a cone on `F.unop : J ⥤ C` into a cocone on `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[simps]
def coconeOfConeUnop (c : Cone F.unop) : Cocone F where
  pt := op c.pt
  ι := NatTrans.removeUnop c.π

/-- Change a cocone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cone on `F.unop : J ⥤ C`. -/
@[simps]
def coneUnopOfCocone (c : Cocone F) : Cone F.unop where
  pt := unop c.pt
  π := NatTrans.unop c.ι

end

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {F : J ⥤ C}

section

variable (G : C ⥤ D)

/-- The opposite cocone of the image of a cone is the image of the opposite cocone. -/
@[simps!]
def mapConeOp (t : Cone F) : (mapCone G t).op ≅ mapCocone G.op t.op :=
  Cocones.ext (Iso.refl _)

/-- The opposite cone of the image of a cocone is the image of the opposite cone. -/
@[simps!]
def mapCoconeOp {t : Cocone F} : (mapCocone G t).op ≅ mapCone G.op t.op :=
  Cones.ext (Iso.refl _)

end

end CategoryTheory.Functor
