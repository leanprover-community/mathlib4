/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoidOfCategory
public import Mathlib.CategoryTheory.IsoCat

/-!
# The fundamental groupoid of a simplicial set

In this file, we define the fundamental groupoid
`SSet.Truncated.FundamentalGroupoid X` of a `2`-truncated simplicial set `X`.
We also define the fundamental groupoid `SSet.FundamentalGroupoid X` of
a simplicial set `X`.

## Implementation notes

In order to get good definitional properties at implicit transparency,
we do not define `FundamentalGroupoid X` as `FreeGroupoid X.HomotopyCategory`,
but only as an induced category via a bijection
`FundamentalGroupoid X ≃ FreeGroupoid X.HomotopyCategory`.
If `f : X ⟶ Y` is a morphism of simplicial sets and `x : X _⦋0⦌`,
this allows to obtain the equality
`(mapFundamentalGroupoid f).obj (mk x) = mk (f.app _ x)`
by `with_implicit rfl`.


-/

@[expose] public section

universe u

open CategoryTheory Simplicial SimplicialObject.Truncated

namespace SSet.Truncated

variable {X Y Z : SSet.Truncated.{u} 2}

variable (X) in
/-- The fundamental groupoid of a `2`-truncated simplicial set. -/
structure FundamentalGroupoid : Type u where
  /-- The underlying vertex. -/
  pt : X _⦋0⦌₂

namespace FundamentalGroupoid

lemma mk_surjective : Function.Surjective (mk (X := X)) :=
  fun x ↦ ⟨x.pt, rfl⟩

/-- The bijection `FundamentalGroupoid X ≃ FreeGroupoid X.HomotopyCategory` that is
used to define the category structure on `FundamentalGroupoid X`
when `X` is a`2`-truncated simplicial set. -/
def equivFreeGroupoid : FundamentalGroupoid X ≃ FreeGroupoid X.HomotopyCategory where
  toFun x := FreeGroupoid.mk (HomotopyCategory.mk x.pt)
  invFun x := mk x.as.as.as.as

instance : Category (FundamentalGroupoid X) :=
  inferInstanceAs (Category (InducedCategory _ equivFreeGroupoid))

variable (X) in
/-- The isomorphism of categories between `FundamentalGroupoid X` and
`FreeGroupoid X.HomotopyCategory` when `X` is a`2`-truncated simplicial set. -/
def isoCatFreeGroupoid :
    IsoCat (FundamentalGroupoid X) (FreeGroupoid X.HomotopyCategory) :=
  InducedCategory.isoCat (equivFreeGroupoid (X := X))

variable (X) in
/-- The equivalence of categories between `FundamentalGroupoid X` and
`FreeGroupoid X.HomotopyCategory` when `X` is a`2`-truncated simplicial set. -/
abbrev equivalenceFreeGroupoid :
    FundamentalGroupoid X ≌ FreeGroupoid X.HomotopyCategory :=
  (isoCatFreeGroupoid X).toEquivalence

instance : Groupoid (FundamentalGroupoid X) :=
  .ofFullyFaithfulToGroupoid _ (equivalenceFreeGroupoid X).fullyFaithfulFunctor

/-- Constructor for morphisms in the fundamental groupoid of a `2`-truncated simplicial set. -/
@[no_expose]
def homMk {x y : X _⦋0⦌₂} (e : Edge x y) : mk x ⟶ mk y where
  hom := FreeGroupoid.homMk (HomotopyCategory.homMk e)

@[simp]
lemma homMk_id (x : X _⦋0⦌₂) : homMk (Edge.id x) = 𝟙 (mk x) :=
  (equivalenceFreeGroupoid X).functor.map_injective
    (((FreeGroupoid.of X.HomotopyCategory).congr_map (by simp)).trans
    ((FreeGroupoid.of X.HomotopyCategory).map_id _))

/-- Induction principle for morphisms in the fundamental groupoid
of a `2`-truncated simplicial set: in order to prove a property
of all morphisms, it suffices to do it for morphisms induced
by edges and show that the property is stable by inverses and
by composition; -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma hom_rec {motive : ∀ ⦃x y : FundamentalGroupoid X⦄, (x ⟶ y) → Prop}
    (homMk : ∀ ⦃x y : X _⦋0⦌₂⦄ (e : Edge x y), motive (homMk e))
    (inv : ∀ ⦃x y : FundamentalGroupoid X⦄ (f : x ⟶ y), motive f → motive (inv f))
    (comp : ∀ ⦃x y z : FundamentalGroupoid X⦄ (f : x ⟶ y) (g : y ⟶ z),
      motive f → motive g → motive (f ≫ g))
    {x y : FundamentalGroupoid X} (f : x ⟶ y) :
    motive f := by
  obtain ⟨x, rfl⟩ := (isoCatFreeGroupoid X).objEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := (isoCatFreeGroupoid X).objEquiv.symm.surjective y
  obtain ⟨f, rfl⟩ := (equivalenceFreeGroupoid X).inverse.map_surjective f
  induction f with
  | homMk f =>
    induction f using HomotopyCategory.hom_rec with
    | homMk f => exact homMk f
    | comp _ _ hf hg => simpa using! comp _ _ hf hg
  | inv _ hf => simpa using! inv _ hf
  | comp _ _ hf hg => simpa using! comp _ _ hf hg

section

variable {D : Type*} [Groupoid D]
  (obj : X _⦋0⦌₂ → D) (map : ∀ {x y : X _⦋0⦌₂}, Edge x y → (obj x ⟶ obj y))
  (map_comp : ∀ {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (_ : Edge.CompStruct e₀₁ e₁₂ e₀₂), map e₀₁ ≫ map e₁₂ = map e₀₂)

/-- Auxiliary definition for `desc`. -/
@[no_expose]
private def desc' : FreeGroupoid (X.HomotopyCategory) ⥤ D :=
  FreeGroupoid.lift (HomotopyCategory.lift obj map (fun X ↦ by
    rw [← cancel_epi (map (.id X)), Category.comp_id, map_comp (.idCompId X)]) map_comp)

/-- Auxiliary definition for `desc`. -/
@[no_expose]
def descMap {x y : FundamentalGroupoid X} (f : x ⟶ y) : obj x.pt ⟶ obj y.pt :=
  (desc' obj map map_comp).map f.hom

@[simp]
lemma descMap_homMk {x y : X _⦋0⦌₂} (e : Edge x y) :
    (descMap obj map map_comp) (homMk e) = map e :=
  (FreeGroupoid.lift_map_homMk ..).trans (HomotopyCategory.lift_map_homMk ..)

/-- Constructor for functors from the fundamental groupoid of a `2`-truncated simplicial set. -/
@[implicit_reducible]
def desc : FundamentalGroupoid X ⥤ D where
  obj x := obj x.pt
  map f := descMap obj map map_comp f
  map_id _ := by apply (desc' obj map map_comp).map_id _
  map_comp _ _ := by apply (desc' obj map map_comp).map_comp

@[simp]
lemma desc_obj_mk (x : X _⦋0⦌₂) :
    (desc obj map map_comp).obj (mk x) = obj x := rfl

@[simp]
lemma desc_map_homMk {x y : X _⦋0⦌₂} (e : Edge x y) :
    (desc obj map map_comp).map (homMk e) = map e :=
  descMap_homMk obj map map_comp e

end

lemma functor_ext {D : Type*} [Groupoid D] {F G : FundamentalGroupoid X ⥤ D}
    (h₁ : ∀ (x : X _⦋0⦌₂), F.obj (mk x) = G.obj (mk x))
    (h₂ : ∀ {x y : X _⦋0⦌₂} (e : Edge x y), F.map (homMk e) =
      eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm) :
    F = G :=
  (isoCatFreeGroupoid X).symm.functor_comp_injective
    (FreeGroupoid.lift_unique'
      (HomotopyCategory.lift_unique' _ _ _
        (Cat.FreeRefl.functor_ext h₁ h₂)))

end FundamentalGroupoid

open FundamentalGroupoid

@[reassoc]
lemma Edge.CompStruct.homMk_comp {x₀ x₁ x₂ : X _⦋0⦌₂} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ :=
  (equivalenceFreeGroupoid X).functor.map_injective
    (by simpa using! ((FreeGroupoid.of X.HomotopyCategory).congr_map
      (HomotopyCategory.homMk_comp_homMk h)))

/-- The functor `FundamentalGroupoid X ⥤ FundamentalGroupoid Y` that is induced
by a morphism of `2`-truncated simplicial sets. -/
@[implicit_reducible]
def mapFundamentalGroupoid (f : X ⟶ Y) :
    FundamentalGroupoid X ⥤ FundamentalGroupoid Y :=
  desc (fun x ↦ mk (f.app _ x)) (fun e ↦ homMk (e.map f))
    (fun h ↦ (h.map f).homMk_comp)

@[simp]
lemma mapFundamentalGroupoid_obj_mk (f : X ⟶ Y) (x : X _⦋0⦌₂) :
    (mapFundamentalGroupoid f).obj (.mk x) = (.mk (f.app _ x)) := rfl

@[simp]
lemma mapFundamentalGroupoid_map_homMk (f : X ⟶ Y) {x y : X _⦋0⦌₂} (e : Edge x y) :
    (mapFundamentalGroupoid f).map (homMk e) = homMk (e.map f) := by rfl

example (f : X ⟶ Y) (x : X _⦋0⦌₂) :
    (mapFundamentalGroupoid f).obj (.mk x) = (.mk (f.app _ x)) := by
  with_implicit rfl

variable (X) in
lemma mapFundamentalGroupoid_id :
    mapFundamentalGroupoid (𝟙 X) = 𝟭 _ :=
  FundamentalGroupoid.functor_ext (fun _ ↦ rfl) (by cat_disch)

lemma mapFundamentalGroupoid_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapFundamentalGroupoid (f ≫ g) = mapFundamentalGroupoid f ⋙ mapFundamentalGroupoid g :=
  FundamentalGroupoid.functor_ext (fun _ ↦ rfl) (by cat_disch)

/-- The isomorphism of fundamental groupoids that is induced
by an isomorphism of `2`-truncated simplicial sets. -/
def mapIsoFundamentalGroupoid {X Y : SSet.Truncated.{u} 2} (e : X ≅ Y) :
    IsoCat (FundamentalGroupoid X) (FundamentalGroupoid Y) where
  functor := mapFundamentalGroupoid e.hom
  inverse := mapFundamentalGroupoid e.inv
  unit_eq := by rw [← mapFundamentalGroupoid_comp, e.hom_inv_id, mapFundamentalGroupoid_id]
  counit_eq := by rw [← mapFundamentalGroupoid_comp, e.inv_hom_id, mapFundamentalGroupoid_id]

instance {X Y : SSet.Truncated.{u} 2} (f : X ⟶ Y) [IsIso f] :
    (mapFundamentalGroupoid f).IsEquivalence :=
  (mapIsoFundamentalGroupoid (asIso f)).toEquivalence.isEquivalence_functor

end SSet.Truncated

namespace SSet

variable {X Y : SSet.{u}}

variable (X) in
/-- The fundamental groupoid of a simplicial set `X`. -/
abbrev FundamentalGroupoid : Type u :=
  ((truncation 2).obj X).FundamentalGroupoid

namespace FundamentalGroupoid

/-- Constructor for objects of the fundamental groupoid of a simplicial set `X`. -/
@[implicit_reducible]
def mk (x : X _⦋0⦌) : FundamentalGroupoid X := Truncated.FundamentalGroupoid.mk x

lemma mk_surjective : Function.Surjective (mk (X := X)) :=
  Truncated.FundamentalGroupoid.mk_surjective

/-- Induction principle for the objects of the fundamental groupoid of a simplicial set. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : FundamentalGroupoid X → Sort*}
    (mk : ∀ (x : X _⦋0⦌), motive (mk x)) (x : FundamentalGroupoid X) :
    motive x :=
  mk _

/-- Constructor for morphisms in the fundamental groupoid of a simplicial set `X`. -/
def homMk {x y : X _⦋0⦌} (e : Edge x y) : mk x ⟶ mk y :=
  Truncated.FundamentalGroupoid.homMk e

@[simp]
lemma homMk_id (x : X _⦋0⦌) : homMk (Edge.id x) = 𝟙 (mk x) :=
  Truncated.FundamentalGroupoid.homMk_id _

/-- Induction principle for morphisms in the fundamental groupoid
of a simplicial set: in order to prove a property of all morphisms,
it suffices to do it for morphisms induced by edges and show that
the property is stable by inverses and by composition; -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma hom_rec {motive : ∀ ⦃x y : FundamentalGroupoid X⦄, (x ⟶ y) → Prop}
    (homMk : ∀ ⦃x y : X _⦋0⦌⦄ (e : Edge x y), motive (homMk e))
    (inv : ∀ ⦃x y : FundamentalGroupoid X⦄ (f : x ⟶ y), motive f → motive (inv f))
    (comp : ∀ ⦃x y z : FundamentalGroupoid X⦄ (f : x ⟶ y) (g : y ⟶ z),
      motive f → motive g → motive (f ≫ g))
    {x y : FundamentalGroupoid X} (f : x ⟶ y) :
    motive f := by
  apply Truncated.FundamentalGroupoid.hom_rec
  all_goals assumption

section

variable {D : Type*} [Groupoid D]
  (obj : X _⦋0⦌ → D) (map : ∀ {x y : X _⦋0⦌}, Edge x y → (obj x ⟶ obj y))
  (map_comp : ∀ {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂}
    (_ : Edge.CompStruct e₀₁ e₁₂ e₀₂), map e₀₁ ≫ map e₁₂ = map e₀₂)

/-- Constructor for functors from the fundamental groupoid of a simplicial set. -/
@[implicit_reducible]
def desc : FundamentalGroupoid X ⥤ D :=
  Truncated.FundamentalGroupoid.desc obj map map_comp


@[simp]
lemma desc_obj_mk (x : X _⦋0⦌) :
    (desc obj map map_comp).obj (mk x) = obj x := rfl

@[simp]
lemma desc_map_homMk {x y : X _⦋0⦌} (e : Edge x y) :
    (desc obj map map_comp).map (homMk e) = map e :=
  Truncated.FundamentalGroupoid.desc_map_homMk ..

end

section

variable {D : Type*} [Category* D] {F G : FundamentalGroupoid X ⥤ D}

open MorphismProperty in
/-- Constructor for natural transformations for functors from the
fundamental groupoid of a simplicial set. -/
@[simps!]
def natTransMk (app : ∀ (x : X _⦋0⦌), F.obj (mk x) ⟶ G.obj (mk x))
    (naturality : ∀ {x y : X _⦋0⦌} (e : Edge x y),
      F.map (homMk e) ≫ app y = app x ≫ G.map (homMk e) := by cat_disch) : F ⟶ G where
  app x := app x.pt
  naturality := by
    let φ (x : FundamentalGroupoid X) := app x.pt
    intro _ _ f
    change naturalityProperty φ f
    induction f with
    | homMk e => exact naturality e
    | inv f hf => exact (naturalityProperty.stableUnderInverse φ) (asIso f) hf
    | comp f g hf hg => exact comp_mem _ _ _ hf hg

/-- Constructor for natural isomorphisms for functors from the
fundamental groupoid of a simplicial set. -/
@[simps!]
def natIsoMk (app : ∀ (x : X _⦋0⦌), F.obj (mk x) ≅ G.obj (mk x))
    (naturality : ∀ {x y : X _⦋0⦌} (e : Edge x y),
      F.map (homMk e) ≫ (app y).hom =
        (app x).hom ≫ G.map (homMk e) := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (fun x ↦ app x.pt)
    (fun f ↦ (natTransMk _ naturality).naturality f)

end

lemma functor_ext {D : Type*} [Groupoid D] {F G : FundamentalGroupoid X ⥤ D}
    (h₁ : ∀ (x : X _⦋0⦌), F.obj (mk x) = G.obj (mk x))
    (h₂ : ∀ {x y : X _⦋0⦌} (e : Edge x y), F.map (homMk e) =
      eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm) :
    F = G :=
  Truncated.FundamentalGroupoid.functor_ext h₁ h₂

end FundamentalGroupoid

open FundamentalGroupoid

@[reassoc]
lemma Edge.CompStruct.homMk_comp {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂}
    {e₀₂ : Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    homMk e₀₁ ≫ homMk e₁₂ = homMk e₀₂ :=
  h.toTruncated.homMk_comp

/-- The functor `FundamentalGroupoid X ⥤ FundamentalGroupoid Y` that is induced
by a morphism of simplicial sets. -/
@[implicit_reducible]
def mapFundamentalGroupoid (f : X ⟶ Y) :
    FundamentalGroupoid X ⥤ FundamentalGroupoid Y :=
  SSet.Truncated.mapFundamentalGroupoid ((truncation 2).map f)

@[simp]
lemma mapFundamentalGroupoid_obj_mk (f : X ⟶ Y) (x : X _⦋0⦌) :
    (mapFundamentalGroupoid f).obj (mk x) = mk (f.app _ x) := rfl

@[simp]
lemma mapFundamentalGroupoid_map_homMk (f : X ⟶ Y) {x y : X _⦋0⦌} (e : Edge x y) :
    (mapFundamentalGroupoid f).map (homMk e) = homMk (e.map f) := by rfl

example (f : X ⟶ Y) (x : X _⦋0⦌) :
    (mapFundamentalGroupoid f).obj (mk x) = mk (f.app _ x) := by
  with_implicit rfl

/-- The isomorphism of fundamental groupoids that is induced
by a morphism of simplicial sets which induces an isomorphism
on the `2`-truncations. -/
noncomputable def isoCatMapFundamentalGroupoid (f : X ⟶ Y)
    (hf : IsIso ((truncation 2).map f) := by infer_instance) :
    IsoCat (FundamentalGroupoid X) (FundamentalGroupoid Y) :=
  Truncated.mapIsoFundamentalGroupoid (asIso ((truncation 2).map f))

lemma isEquivalence_mapFundamentalGroupoid (f : X ⟶ Y)
    (hf : IsIso ((truncation 2).map f) := by infer_instance) :
    (mapFundamentalGroupoid f).IsEquivalence :=
  (isoCatMapFundamentalGroupoid f).toEquivalence.isEquivalence_functor

end SSet
