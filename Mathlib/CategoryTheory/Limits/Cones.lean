/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

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

set_option backward.defeqAttrib.useBackward true

@[expose] public section



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
@[simps! obj map]
def cones : Cᵒᵖ ⥤ Type (max u₁ v₃) :=
  (const J).op ⋙ yoneda.obj F

/-- If `F : J ⥤ C` then `F.cocones` is the functor assigning to an object `(X : C)`
the type of natural transformations from `F` to the constant functor with value `X`.
An object corepresenting this functor is a colimit of `F`.
-/
@[simps! obj map]
def cocones : C ⥤ Type (max u₁ v₃) :=
  const J ⋙ coyoneda.obj (op F)

end Functor

section

variable (J C)

/-- Functorially associated to each functor `J ⥤ C`, we have the `C`-presheaf consisting of
cones with a given cone point.
-/
@[simps! obj_obj obj_map map_app]
def cones : (J ⥤ C) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₃) where
  obj := Functor.cones
  map f := whiskerLeft (const J).op (yoneda.map f)

/-- Contravariantly associated to each functor `J ⥤ C`, we have the `C`-copresheaf consisting of
cocones with a given cocone point.
-/
@[simps! obj_obj obj_map map_app]
def cocones : (J ⥤ C)ᵒᵖ ⥤ C ⥤ Type (max u₁ v₃) where
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

/-- A `c : Cocone F` is
* an object `c.pt` and
* a natural transformation `c.ι : F ⟶ c.pt` from `F` to the constant `c.pt` functor.

For example, if the source `J` of `F` is a partially ordered set, then to give
`c : Cocone F` is to give a collection of morphisms `ιⱼ : F j ⟶ c.pt` and, for
all `j ≤ k` in `J`, morphisms `ιⱼₖ : F j ⟶ F k` such that `Fⱼₖ ≫ Fₖ = Fⱼ` for all `j ≤ k`.

`Cocone F` is equivalent, via `Cone.equiv` below, to `Σ X, F.cocones.obj X`.
-/
@[to_dual existing]
structure Cocone (F : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from `F` to the constant functor at `pt` -/
  ι : F ⟶ (const J).obj pt

@[to_dual]
instance inhabitedCone (F : Discrete PUnit ⥤ C) : Inhabited (Cone F) :=
  ⟨{  pt := F.obj ⟨⟨⟩⟩
      π := { app := fun ⟨⟨⟩⟩ => 𝟙 _
             naturality := by
              intro X Y f
              match X, Y, f with
              | .mk A, .mk B, .up g =>
                simp
           }
  }⟩

set_option backward.defeqAttrib.useBackward true in
@[to_dual (attr := reassoc (attr := simp))]
theorem Cone.w {F : J ⥤ C} (c : Cone F) {j j' : J} (f : j ⟶ j') :
    dsimp% c.π.app j ≫ F.map f = c.π.app j' := by
  simpa using (c.π.naturality f).symm

attribute [elementwise] Cocone.w Cone.w

end

variable {F : J ⥤ C}

namespace Cone

/-- The isomorphism between a cone on `F` and an element of the functor `F.cones`. -/
@[simps!]
def equiv (F : J ⥤ C) : dsimp% Cone F ≅ Σ X, F.cones.obj X where
  hom := ↾fun c ↦ ⟨op c.pt, c.π⟩
  inv := ↾fun c ↦
    { pt := c.1.unop
      π := c.2 }
  hom_inv_id := by
    ext X
    cases X
    rfl
  inv_hom_id := by
    ext X
    cases X
    all_goals rfl

/-- A map to the vertex of a cone naturally induces a cone by composition. -/
@[simps]
def extensions (c : Cone F) : uliftYoneda.obj c.pt ⟶ F.cones where
  app _ := ↾fun f ↦ (const J).map f.down ≫ c.π

/-- A map to the vertex of a cone induces a cone by composition. -/
@[to_dual (attr := simps)
/-- A map from the vertex of a cocone induces a cocone by composition. -/]
def extend (c : Cone F) {X : C} (f : X ⟶ c.pt) : Cone F where
  pt := X
  π := (const J).map f ≫ c.π

/-- Whisker a cone by precomposition of a functor. -/
@[to_dual (attr := simps)
/-- Whisker a cocone by precomposition of a functor. See `whiskering` for a functorial
version.
-/]
def whisker (E : K ⥤ J) (c : Cone F) : Cone (E ⋙ F) where
  pt := c.pt
  π := whiskerLeft E c.π

end Cone

namespace Cocone

/-- The isomorphism between a cocone on `F` and an element of the functor `F.cocones`. -/
def equiv (F : J ⥤ C) : Cocone F ≅ Σ X, F.cocones.obj X where
  hom := ↾fun c ↦ ⟨c.pt, c.ι⟩
  inv := ↾fun c ↦
    { pt := c.1
      ι := c.2 }
  hom_inv_id := by
    ext X
    cases X
    rfl
  inv_hom_id := by
    ext X
    cases X
    all_goals rfl

/-- A map from the vertex of a cocone naturally induces a cocone by composition. -/
@[simps]
def extensions (c : Cocone F) : coyoneda.obj (op c.pt) ⋙ uliftFunctor.{u₁} ⟶ F.cocones where
  app _ := ↾fun f ↦ c.ι ≫ (const J).map f.down

end Cocone

/-- A cone morphism between two cones for the same diagram is a morphism of the cone points which
commutes with the cone legs. -/
structure ConeMorphism (A B : Cone F) where
  /-- A morphism between the two vertex objects of the cones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  w (j : J) : hom ≫ B.π.app j = A.π.app j := by cat_disch

/-- A cocone morphism between two cocones for the same diagram is a morphism of the cocone points
which commutes with the cocone legs. -/
@[to_dual (reorder := A B)]
structure CoconeMorphism (A B : Cocone F) where
  /-- A morphism between the (co)vertex objects in `C` -/
  hom : A.pt ⟶ B.pt
  /-- The triangle made from the two natural transformations and `hom` commutes -/
  w (j : J) : dsimp% A.ι.app j ≫ hom = B.ι.app j := by cat_disch

attribute [reassoc (attr := simp)] ConeMorphism.w CoconeMorphism.w
attribute [to_dual existing] ConeMorphism.casesOn

@[to_dual]
instance inhabitedConeMorphism (A : Cone F) : Inhabited (ConeMorphism A A) :=
  ⟨{ hom := 𝟙 _ }⟩

/-- The category of cones on a given diagram. -/
@[to_dual (attr := simps) /-- The category of cocones on a given diagram. -/]
instance Cone.category : Category (Cone F) where
  Hom A B := ConeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/- We do not want `simps` automatically generate the lemma for simplifying the
hom field of a category. So we need to write the `ext` lemma in terms of the
categorical morphism, rather than the underlying structure. -/
@[to_dual (attr := ext)
/- We do not want `simps` automatically generate the lemma for simplifying the
hom field of a category. So we need to write the `ext` lemma in terms of the
categorical morphism, rather than the underlying structure. -/]
theorem ConeMorphism.ext {c c' : Cone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

@[to_dual (attr := reassoc (attr := simp))]
lemma ConeMorphism.hom_inv_id {c d : Cone F} (f : c ≅ d) : f.hom.hom ≫ f.inv.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

@[to_dual (attr := reassoc (attr := simp))]
lemma ConeMorphism.inv_hom_id {c d : Cone F} (f : c ≅ d) : f.inv.hom ≫ f.hom.hom = 𝟙 _ := by
  simp [← Cone.category_comp_hom]

@[to_dual]
instance {c d : Cone F} (f : c ≅ d) : IsIso f.hom.hom := ⟨f.inv.hom, by simp⟩

@[to_dual]
instance {c d : Cone F} (f : c ≅ d) : IsIso f.inv.hom := ⟨f.hom.hom, by simp⟩

@[to_dual (attr := reassoc (attr := simp))]
lemma ConeMorphism.map_w {c c' : Cone F} (f : c ⟶ c') (G : C ⥤ D) (j : J) :
    G.map f.hom ≫ G.map (c'.π.app j) = G.map (c.π.app j) := by
  simp [← map_comp]

namespace Cone

/-- To give an isomorphism between cones, it suffices to give an
isomorphism between their vertices which commutes with the cone maps. -/
@[to_dual (attr := simps) ext_inv
/-- To give an isomorphism between cocones, it suffices to give an
isomorphism between their vertices which commutes with the cone maps. -/]
def ext {c c' : Cone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      w := fun j => φ.inv_comp_eq.mpr (w j) }

/-- To give an isomorphism between cones, it suffices to give an
isomorphism between their vertices which commutes with the cone maps. -/
@[to_dual (attr := simps!) ext
/-- To give an isomorphism between cocones, it suffices to give an
isomorphism between their vertices which commutes with the cocone maps. -/]
def ext_inv {c c' : Cone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, φ.inv ≫ c.π.app j = c'.π.app j := by cat_disch) : c ≅ c' :=
  ext φ fun j ↦ (Iso.inv_comp_eq φ).mp (w j)

attribute [aesop apply safe (rule_sets := [CategoryTheory])] Limits.Cone.ext Limits.Cocone.ext

/-- Eta rule for cones. -/
@[to_dual (attr := simps!) /-- Eta rule for cocones. -/]
def eta (c : Cone F) : c ≅ ⟨c.pt, c.π⟩ :=
  ext (Iso.refl _)

/-- Given a cone morphism whose object part is an isomorphism, produce an
isomorphism of cones.
-/
@[to_dual
/-- Given a cocone morphism whose object part is an isomorphism, produce an
isomorphism of cocones.
-/]
theorem cone_iso_of_hom_iso {K : J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.hom] : IsIso f :=
  ⟨⟨{   hom := inv f.hom
        w := fun j => (asIso f.hom).inv_comp_eq.2 (f.w j).symm }, by cat_disch⟩⟩

/-- There is a morphism from an extended cone to the original cone. -/
@[to_dual (attr := simps) /-- There is a morphism from a cocone to its extension. -/]
def extendHom (s : Cone F) {X : C} (f : X ⟶ s.pt) : s.extend f ⟶ s where
  hom := f

/-- Extending a cone by the identity does nothing. -/
@[to_dual (attr := simps!) /-- Extending a cocone by the identity does nothing. -/]
def extendId (s : Cone F) : s.extend (𝟙 s.pt) ≅ s :=
  ext (Iso.refl _)

/-- Extending a cone by a composition is the same as extending the cone twice. -/
@[to_dual (attr := simps!) (reorder := f g)
/-- Extending a cocone by a composition is the same as extending the cone twice. -/]
def extendComp (s : Cone F) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ s.pt) :
    s.extend (f ≫ g) ≅ (s.extend g).extend f :=
  ext (Iso.refl _)

/-- A cone extended by an isomorphism is isomorphic to the original cone. -/
@[to_dual (attr := simps)
/-- A cocone extended by an isomorphism is isomorphic to the original cone. -/]
def extendIso (s : Cone F) {X : C} (f : s.pt ≅ X) : s ≅ s.extend f.inv where
  hom := { hom := f.hom }
  inv := { hom := f.inv }

@[to_dual]
instance {s : Cone F} {X : C} (f : X ⟶ s.pt) [IsIso f] : IsIso (s.extendHom f) :=
  ⟨(extendIso s (asIso' f)).hom, by cat_disch⟩

/--
Functorially postcompose a cone for `F` by a natural transformation `F ⟶ G` to give a cone for `G`.
-/
@[to_dual (attr := simps)
/-- Functorially precompose a cocone for `F` by a natural transformation `G ⟶ F` to give a cocone
for `G`. -/]
def postcompose {G : J ⥤ C} (α : F ⟶ G) : Cone F ⥤ Cone G where
  obj c :=
    { pt := c.pt
      π := c.π ≫ α }
  map f := { hom := f.hom }

/-- Postcomposing a cone by the composite natural transformation `α ≫ β` is the same as
postcomposing by `α` and then by `β`. -/
@[to_dual (attr := simps!) (reorder := α β)
/-- Precomposing a cocone by the composite natural transformation `α ≫ β` is the same as
precomposing by `β` and then by `α`. -/]
def postcomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
  NatIso.ofComponents fun s => ext (Iso.refl _)

/-- Postcomposing by the identity does not change the cone up to isomorphism. -/
@[to_dual (attr := simps!)
/-- Precomposing by the identity does not change the cocone up to isomorphism. -/]
def postcomposeId : postcompose (𝟙 F) ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun s => ext (Iso.refl _)

/-- If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cones.
-/
@[to_dual (attr := simps)
/-- If `F` and `G` are naturally isomorphic functors, then they have equivalent categories of
cocones.
-/]
def postcomposeEquivalence {G : J ⥤ C} (α : F ≅ G) : Cone F ≌ Cone G where
  functor := postcompose α.hom
  inverse := postcompose α.inv
  unitIso := NatIso.ofComponents fun s => ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s => ext (Iso.refl _)

/-- Whiskering on the left by `E : K ⥤ J` gives a functor from `Cone F` to `Cone (E ⋙ F)`.
-/
@[to_dual (attr := simps)
/-- Whiskering on the left by `E : K ⥤ J` gives a functor from `Cocone F` to `Cocone (E ⋙ F)`.
-/]
def whiskering (E : K ⥤ J) : Cone F ⥤ Cone (E ⋙ F) where
  obj c := c.whisker E
  map f := { hom := f.hom }

/-- Whiskering by an equivalence gives an equivalence between categories of cones.
-/
@[to_dual (attr := simps)
/-- Whiskering by an equivalence gives an equivalence between categories of cones.
-/]
def whiskeringEquivalence (e : K ≌ J) : Cone F ≌ Cone (e.functor ⋙ F) where
  functor := whiskering e.functor
  inverse := whiskering e.inverse ⋙ postcompose (e.invFunIdAssoc F).hom
  unitIso := NatIso.ofComponents fun s => ext (Iso.refl _)
  counitIso :=
    NatIso.ofComponents
      fun s =>
        ext (Iso.refl _)
          (by
            intro k
            simpa [e.counit_app_functor] using s.w (e.unitInv.app k))

/-- The categories of cones over `F` and `G` are equivalent if `F` and `G` are naturally isomorphic
(possibly after changing the indexing category by an equivalence).
-/
@[to_dual (attr := simps! functor inverse unitIso counitIso)
/-- The categories of cocones over `F` and `G` are equivalent if `F` and `G` are naturally
isomorphic (possibly after changing the indexing category by an equivalence).
-/]
def equivalenceOfReindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : Cone F ≌ Cone G :=
  (whiskeringEquivalence e).trans (postcomposeEquivalence α)

section

variable (F)

/-- Forget the cone structure and obtain just the cone point. -/
@[to_dual (attr := simps) /-- Forget the cocone structure and obtain just the cocone point. -/]
def forget : Cone F ⥤ C where
  obj t := t.pt
  map f := f.hom

variable (G : C ⥤ D)

/-- A functor `G : C ⥤ D` sends cones over `F` to cones over `F ⋙ G` functorially. -/
@[to_dual (attr := simps)
/-- A functor `G : C ⥤ D` sends cocones over `F` to cocones over `F ⋙ G` functorially. -/]
def functoriality : Cone F ⥤ Cone (F ⋙ G) where
  obj A :=
    { pt := G.obj A.pt
      π :=
        { app := fun j => G.map (A.π.app j)
          naturality := by simp [← G.map_comp] } }
  map f :=
    { hom := G.map f.hom
      w := ConeMorphism.map_w f G }

/-- Functoriality is functorial. -/
@[to_dual /-- Functoriality is functorial. -/]
def functorialityCompFunctoriality (H : D ⥤ E) :
    functoriality F G ⋙ functoriality (F ⋙ G) H ≅ functoriality F (G ⋙ H) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

@[to_dual]
instance functoriality_full [G.Full] [G.Faithful] : (functoriality F G).Full where
  map_surjective t :=
    ⟨{ hom := G.preimage t.hom
       w := fun j => G.map_injective (by simpa using t.w j) }, by cat_disch⟩

@[to_dual]
instance functoriality_faithful [G.Faithful] : (functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    ConeMorphism.ext f g <| G.map_injective <| congr_arg ConeMorphism.hom h

/-- If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cones over `F` and cones over `F ⋙ e.functor`.
-/
@[to_dual (attr := simps)
/-- If `e : C ≌ D` is an equivalence of categories, then `functoriality F e.functor` induces an
equivalence between cocones over `F` and cocones over `F ⋙ e.functor`.
-/]
def functorialityEquivalence (e : C ≌ D) : Cone F ≌ Cone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  { functor := functoriality F e.functor
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (postcomposeEquivalence f).functor
    unitIso := NatIso.ofComponents fun c => ext (e.unitIso.app _)
    counitIso := NatIso.ofComponents fun c => ext (e.counitIso.app _) }

/-- If `F` reflects isomorphisms, then `functoriality F` reflects isomorphisms
as well.
-/
@[to_dual
/-- If `F` reflects isomorphisms, then `Cocones.functoriality F` reflects isomorphisms
as well.
-/]
instance reflects_cone_isomorphism (F : C ⥤ D) [F.ReflectsIsomorphisms] (K : J ⥤ C) :
    (functoriality K F).ReflectsIsomorphisms := by
  constructor
  intro A B f _
  haveI : IsIso (F.map f.hom) :=
    (forget (K ⋙ F)).map_isIso ((functoriality K F).map f)
  haveI := ReflectsIsomorphisms.reflects F f.hom
  apply cone_iso_of_hom_iso

end

end Cone

namespace Cones

@[deprecated (since := "2026-03-06")] alias ext := Cone.ext
@[deprecated (since := "2026-03-06")] alias eta := Cone.eta
@[deprecated (since := "2026-03-06")] alias cone_iso_of_hom_iso := Cone.cone_iso_of_hom_iso
@[deprecated (since := "2026-03-06")] alias extend := Cone.extendHom
@[deprecated (since := "2026-03-06")] alias extendId := Cone.extendId
@[deprecated (since := "2026-03-06")] alias extendComp := Cone.extendComp
@[deprecated (since := "2026-03-06")] alias extendIso := Cone.extendIso
@[deprecated (since := "2026-03-06")] alias postcompose := Cone.postcompose
@[deprecated (since := "2026-03-06")] alias postcomposeComp := Cone.postcomposeComp
@[deprecated (since := "2026-03-06")] alias postcomposeId := Cone.postcomposeId
@[deprecated (since := "2026-03-06")] alias postcomposeEquivalence := Cone.postcomposeEquivalence
@[deprecated (since := "2026-03-06")] alias whiskering := Cone.whiskering
@[deprecated (since := "2026-03-06")] alias whiskeringEquivalence := Cone.whiskeringEquivalence
@[deprecated (since := "2026-03-06")] alias equivalenceOfReindexing := Cone.equivalenceOfReindexing
@[deprecated (since := "2026-03-06")] alias forget := Cone.forget
@[deprecated (since := "2026-03-06")] alias functoriality := Cone.functoriality
@[deprecated (since := "2026-03-06")]
alias functorialityCompFunctoriality := Cone.functorialityCompFunctoriality
@[deprecated (since := "2026-03-06")] alias functoriality_full := Cone.functoriality_full
@[deprecated (since := "2026-03-06")] alias functoriality_faithful := Cone.functoriality_faithful
@[deprecated (since := "2026-03-06")]
alias functorialityEquivalence := Cone.functorialityEquivalence
@[deprecated (since := "2026-03-06")]
alias reflects_cone_isomorphism := Cone.reflects_cone_isomorphism

end Cones

namespace Cocones

@[deprecated (since := "2026-03-06")] alias ext := Cocone.ext
@[deprecated (since := "2026-03-06")] alias eta := Cocone.eta
@[deprecated (since := "2026-03-06")] alias cone_iso_of_hom_iso := Cocone.cocone_iso_of_hom_iso
@[deprecated (since := "2026-03-06")] alias extend := Cocone.extendHom
@[deprecated (since := "2026-03-06")] alias extendId := Cocone.extendId
@[deprecated (since := "2026-03-06")] alias extendComp := Cocone.extendComp
@[deprecated (since := "2026-03-06")] alias extendIso := Cocone.extendIso
@[deprecated (since := "2026-03-06")] alias postcompose := Cocone.precompose
@[deprecated (since := "2026-03-06")] alias postcomposeComp := Cocone.precomposeComp
@[deprecated (since := "2026-03-06")] alias postcomposeId := Cocone.precomposeId
@[deprecated (since := "2026-03-06")] alias postcomposeEquivalence := Cocone.precomposeEquivalence
@[deprecated (since := "2026-03-06")] alias whiskering := Cocone.whiskering
@[deprecated (since := "2026-03-06")] alias whiskeringEquivalence := Cocone.whiskeringEquivalence
@[deprecated (since := "2026-03-06")]
alias equivalenceOfReindexing := Cocone.equivalenceOfReindexing
@[deprecated (since := "2026-03-06")] alias forget := Cocone.forget
@[deprecated (since := "2026-03-06")] alias functoriality := Cocone.functoriality
@[deprecated (since := "2026-03-06")]
alias functorialityCompFunctoriality := Cocone.functorialityCompFunctoriality
@[deprecated (since := "2026-03-06")] alias functoriality_full := Cocone.functoriality_full
@[deprecated (since := "2026-03-06")] alias functoriality_faithful := Cocone.functoriality_faithful
@[deprecated (since := "2026-03-06")]
alias functorialityEquivalence := Cocone.functorialityEquivalence
@[deprecated (since := "2026-03-06")]
alias reflects_cone_isomorphism := Cocone.reflects_cocone_isomorphism

end Cocones

end Limits

namespace Functor

variable (H : C ⥤ D) {F : J ⥤ C} {G : J ⥤ C}

open CategoryTheory.Limits

/-- The image of a cone in C under a functor G : C ⥤ D is a cone in D. -/
@[to_dual (attr := simps!)
/-- The image of a cocone in C under a functor G : C ⥤ D is a cocone in D. -/]
def mapCone (c : Cone F) : Cone (F ⋙ H) :=
  (Cone.functoriality F H).obj c

/-- The construction `mapCone` respects functor composition. -/
@[to_dual (attr := simps!)
/-- The construction `mapCocone` respects functor composition. -/]
noncomputable def mapConeMapCone {F : J ⥤ C} {H : C ⥤ D} {H' : D ⥤ E} (c : Cone F) :
    H'.mapCone (H.mapCone c) ≅ (H ⋙ H').mapCone c := Cone.ext (Iso.refl _)

/-- Given a cone morphism `c ⟶ c'`, construct a cone morphism on the mapped cones functorially. -/
@[to_dual
/-- Given a cocone morphism `c ⟶ c'`, construct a cocone morphism on the mapped cocones
functorially. -/]
def mapConeMorphism {c c' : Cone F} (f : c ⟶ c') : H.mapCone c ⟶ H.mapCone c' :=
  (Cone.functoriality F H).map f

/-- If `H` is an equivalence, we invert `H.mapCone` and get a cone for `F` from a cone
for `F ⋙ H`. -/
@[to_dual
/-- If `H` is an equivalence, we invert `H.mapCone` and get a cone for `F` from a cone
for `F ⋙ H`. -/]
noncomputable def mapConeInv [IsEquivalence H] (c : Cone (F ⋙ H)) : Cone F :=
  (Limits.Cone.functorialityEquivalence F (asEquivalence H)).inverse.obj c

/-- `mapCone` is the left inverse to `mapConeInv`. -/
@[to_dual /-- `mapCocone` is the left inverse to `mapCoconeInv`. -/]
noncomputable def mapConeMapConeInv {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H]
    (c : Cone (F ⋙ H)) :
    mapCone H (mapConeInv H c) ≅ c :=
  (Limits.Cone.functorialityEquivalence F (asEquivalence H)).counitIso.app c

/-- `mapCone` is the right inverse to `mapConeInv`. -/
@[to_dual /-- `mapCocone` is the right inverse to `mapCoconeInv`. -/]
noncomputable def mapConeInvMapCone {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cone F) :
    mapConeInv H (mapCone H c) ≅ c :=
  (Limits.Cone.functorialityEquivalence F (asEquivalence H)).unitIso.symm.app c

/-- `functoriality F _ ⋙ postcompose (whisker_left F _)` simplifies to `functoriality F _`. -/
@[to_dual (attr := simps!)
/-- `functoriality F _ ⋙ precompose (whiskerLeft F _)` simplifies to `functoriality F _`. -/]
def functorialityCompPostcompose {H H' : C ⥤ D} (α : H ≅ H') :
    Cone.functoriality F H ⋙ Cone.postcompose (whiskerLeft F α.hom) ≅ Cone.functoriality F H' :=
  NatIso.ofComponents fun c => Cone.ext (α.app _)

/-- For `F : J ⥤ C`, given a cone `c : Cone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the postcomposition of the cone `H.mapCone` using the isomorphism `α` is
isomorphic to the cone `H'.mapCone`.
-/
@[to_dual (attr := simps!)
/--
For `F : J ⥤ C`, given a cocone `c : Cocone F`, and a natural isomorphism `α : H ≅ H'` for functors
`H H' : C ⥤ D`, the precomposition of the cocone `H.mapCocone` using the isomorphism `α` is
isomorphic to the cocone `H'.mapCocone`.
-/]
def postcomposeWhiskerLeftMapCone {H H' : C ⥤ D} (α : H ≅ H') (c : Cone F) :
    (Cone.postcompose (whiskerLeft F α.hom :)).obj (mapCone H c) ≅ mapCone H' c :=
  (functorialityCompPostcompose α).app c

/--
`mapCone` commutes with `postcompose`. In particular, for `F : J ⥤ C`, given a cone `c : Cone F`, a
natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious ways of producing
a cone over `G ⋙ H`, and they are both isomorphic.
-/
@[to_dual (attr := simps!)
/-- `map_cocone` commutes with `precompose`. In particular, for `F : J ⥤ C`, given a cocone
`c : Cocone F`, a natural transformation `α : F ⟶ G` and a functor `H : C ⥤ D`, we have two obvious
ways of producing a cocone over `G ⋙ H`, and they are both isomorphic.
-/]
def mapConePostcompose {α : F ⟶ G} {c} :
    mapCone H ((Cone.postcompose α).obj c) ≅
      (Cone.postcompose (whiskerRight α H :)).obj (mapCone H c) :=
  Cone.ext (Iso.refl _)

/-- `mapCone` commutes with `postcomposeEquivalence` -/
@[to_dual (attr := simps!) /-- `mapCocone` commutes with `precomposeEquivalence` -/]
def mapConePostcomposeEquivalenceFunctor {α : F ≅ G} {c} :
    mapCone H ((Cone.postcomposeEquivalence α).functor.obj c) ≅
      (Cone.postcomposeEquivalence (isoWhiskerRight α H :)).functor.obj (mapCone H c) :=
  Cone.ext (Iso.refl _)

/-- `mapCone` commutes with `whisker` -/
@[to_dual (attr := simps!) /-- `mapCocone` commutes with `whisker` -/]
def mapConeWhisker {E : K ⥤ J} {c : Cone F} : mapCone H (c.whisker E) ≅ (mapCone H c).whisker E :=
  Cone.ext (Iso.refl _)

end Functor

namespace Limits

section

variable {F : J ⥤ C}

/-- Change a `Cone F` into a `Cocone F.op`. -/
@[to_dual (attr := simps) /-- Change a `Cocone F` into a `Cone F.op`. -/]
def Cone.op (c : Cone F) : Cocone F.op where
  pt := Opposite.op c.pt
  ι := NatTrans.op c.π

/-- Change a `Cone F.op` into a `Cocone F`. -/
@[to_dual (attr := simps) /-- Change a `Cocone F.op` into a `Cone F`. -/]
def Cone.unop (c : Cone F.op) : Cocone F where
  pt := Opposite.unop c.pt
  ι := NatTrans.removeOp c.π

variable (F)

set_option backward.isDefEq.respectTransparency false in
/-- The category of cocones on `F` is equivalent to the opposite category of
the category of cones on the opposite of `F`.
-/
@[to_dual (attr := simp)
/-- The category of cones on `F` is equivalent to the opposite category of
the category of cocones on the opposite of `F`.
-/]
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
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Cones on `F : J ⥤ C` are equivalent to cocones on `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : J ⥤ C` are equivalent to cones on `F.op : Jᵒᵖ ⥤ Cᵒᵖ`. -/]
def coneOpEquiv {F : J ⥤ C} : (Cone F)ᵒᵖ ≌ Cocone F.op where
  functor.obj c := c.unop.op
  functor.map f := { hom := f.unop.hom.op, w j := congr($(f.unop.w j.unop).op) }
  inverse.obj c := .op <| c.unop
  inverse.map f := ⟨{ hom := f.hom.unop, w j := congr($(f.w (.op j)).unop) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

section

variable {F : J ⥤ Cᵒᵖ}

/-- Change a cocone on `F.leftOp : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps!)
/-- Change a cone on `F.leftOp : Jᵒᵖ ⥤ C` to a cocone on `F : J ⥤ Cᵒᵖ`. -/]
def coneOfCoconeLeftOp (c : Cocone F.leftOp) : Cone F where
  pt := op c.pt
  π := NatTrans.removeLeftOp c.ι

/-- Change a cone on `F : J ⥤ Cᵒᵖ` to a cocone on `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps!)
/-- Change a cocone on `F : J ⥤ Cᵒᵖ` to a cone on `F.leftOp : Jᵒᵖ ⥤ C`. -/]
def coconeLeftOpOfCone (c : Cone F) : Cocone F.leftOp where
  pt := unop c.pt
  ι := NatTrans.leftOp c.π

/-- Cones on `F : J ⥤ Cᵒᵖ` are equivalent to cocones on `F.leftOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : J ⥤ Cᵒᵖ` are equivalent to cones on `F.leftOp : Jᵒᵖ ⥤ C`. -/]
def coconeLeftOpOfConeEquiv {F : J ⥤ Cᵒᵖ} : (Cone F)ᵒᵖ ≌ Cocone F.leftOp where
  functor.obj c := coconeLeftOpOfCone c.unop
  functor.map f := { hom := f.unop.hom.unop, w j := congr($(f.unop.w j.unop).unop) }
  inverse.obj c := .op <| coneOfCoconeLeftOp c
  inverse.map f := ⟨{ hom := f.hom.op, w j := congr($(f.w (.op j)).op) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

section

variable {F : Jᵒᵖ ⥤ C}

/-- Change a cocone on `F.rightOp : J ⥤ Cᵒᵖ` to a cone on `F : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps)
/-- Change a cone on `F.rightOp : J ⥤ Cᵒᵖ` to a cocone on `F : Jᵒᵖ ⥤ C`. -/]
def coneOfCoconeRightOp (c : Cocone F.rightOp) : Cone F where
  pt := unop c.pt
  π := NatTrans.removeRightOp c.ι

/-- Change a cone on `F : Jᵒᵖ ⥤ C` to a cocone on `F.rightOp : Jᵒᵖ ⥤ C`. -/
@[to_dual (attr := simps)
/-- Change a cocone on `F : Jᵒᵖ ⥤ C` to a cone on `F.rightOp : J ⥤ Cᵒᵖ`. -/]
def coconeRightOpOfCone (c : Cone F) : Cocone F.rightOp where
  pt := op c.pt
  ι := NatTrans.rightOp c.π

/-- Cones on `F : Jᵒᵖ ⥤ C` are equivalent to cocones on `F.rightOp : J ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : Jᵒᵖ ⥤ C` are equivalent to cones on `F.rightOp : J ⥤ Cᵒᵖ`. -/]
def coconeRightOpOfConeEquiv {F : Jᵒᵖ ⥤ C} : (Cone F)ᵒᵖ ≌ Cocone F.rightOp where
  functor.obj c := coconeRightOpOfCone c.unop
  functor.map f := { hom := f.unop.hom.op, w j := congr($(f.unop.w (.op j)).op) }
  inverse.obj c := .op <| coneOfCoconeRightOp c
  inverse.map f := ⟨{ hom := f.hom.unop, w j := congr($(f.w j.unop).unop) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

section

variable {F : Jᵒᵖ ⥤ Cᵒᵖ}

/-- Change a cocone on `F.unop : J ⥤ C` into a cone on `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/
@[to_dual (attr := simps)
/-- Change a cone on `F.unop : J ⥤ C` into a cocone on `F : Jᵒᵖ ⥤ Cᵒᵖ`. -/]
def coneOfCoconeUnop (c : Cocone F.unop) : Cone F where
  pt := op c.pt
  π := NatTrans.removeUnop c.ι

/-- Change a cone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cocone on `F.unop : J ⥤ C`. -/
@[to_dual (attr := simps)
/-- Change a cocone on `F : Jᵒᵖ ⥤ Cᵒᵖ` into a cone on `F.unop : J ⥤ C`. -/]
def coconeUnopOfCone (c : Cone F) : Cocone F.unop where
  pt := unop c.pt
  ι := NatTrans.unop c.π

/-- Cones on `F : Jᵒᵖ ⥤ Cᵒᵖ` are equivalent to cocones on `F.unop : J ⥤ C`. -/
@[to_dual (attr := simps)
/-- Cocones on `F : Jᵒᵖ ⥤ Cᵒᵖ` are equivalent to cones on `F.unop : J ⥤ C`. -/]
def coconeUnopOfConeEquiv {F : Jᵒᵖ ⥤ Cᵒᵖ} : (Cone F)ᵒᵖ ≌ Cocone F.unop where
  functor.obj c := coconeUnopOfCone c.unop
  functor.map f := { hom := f.unop.hom.unop, w j := congr($(f.unop.w (.op j)).unop) }
  inverse.obj c := .op <| coneOfCoconeUnop c
  inverse.map f := ⟨{ hom := f.hom.op, w j := congr($(f.w j.unop).op) }⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {F : J ⥤ C} (G : C ⥤ D)

/-- The opposite cocone of the image of a cone is the image of the opposite cocone. -/
@[to_dual (attr := simps!)
/-- The opposite cone of the image of a cocone is the image of the opposite cone. -/]
def mapConeOp (t : Cone F) : (mapCone G t).op ≅ mapCocone G.op t.op :=
  Cocone.ext (Iso.refl _)

end CategoryTheory.Functor
