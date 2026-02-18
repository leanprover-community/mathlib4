/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar, Arnoud van der Leer
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The Coherent Isomorphism

In this file, we define two related types.

We first define the free walking or free-living isomorphism `WalkingIso`: the category with
two objects `false` and `true`, and morphisms `false ⟶ true` and `true ⟶ false`.
We show that the type of functor from `WalkingIso` into any category is equivalent to the type of
isomorphisms in that category.

Then we define the simplicial set `coherentIso` as the nerve of `WalkingIso`.
Since the morphism types in `WalkingIso` are given by `unit`, the `n`-simplices of `coherentIso` are
equivalent to `Fin 2`-vectors of length `n + 1`. This shows that the `n`-simplices of `coherentIso`
have decidable equality.
Lastly, we show that `hom : coherentIso _⦋1⦌` (the edge from `false` to `true`) has an inverse,
and `isIsoOfEqMapHom` concludes from this that for any simplicial set `X`,
any morphism `g : coherentIso ⟶ X` and any `f : X _⦋1⦌`,
if `g` sends `hom` to `f`, then `f` has an inverse.

-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects `false` and `true`. -/
inductive WalkingIso : Type u where
  | zero : WalkingIso
  | one  : WalkingIso

attribute [aesop safe cases (rule_sets := [CategoryTheory])] WalkingIso
attribute [grind cases] WalkingIso

namespace WalkingIso

/-- The underlying type of `WalkingIso` is equivalent to `Bool`, since they both have 2 elements. -/
def equivBool : WalkingIso.{u} ≃ Bool where
  toFun := fun
    | .zero => false
    | .one => true
  invFun := fun
    | false => .zero
    | true => .one
  left_inv := by
    rintro (_ | _) <;>
    rfl
  right_inv := by
    rintro (_ | _) <;>
    rfl

instance : DecidableEq WalkingIso.{u} :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq equivBool)

/-- The free isomorphism is the codiscrete category on two objects. -/
instance : Category.{0, u} WalkingIso.{u} where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

instance homUnique {x y : WalkingIso.{u}} : Unique (x ⟶ y) := inferInstanceAs (Unique Unit)

section

variable {C : Type u} [Category.{v} C]

/-- The isomorphism at the heart of `WalkingIso` -/
def iso : zero ≅ one where
  hom := ()
  inv := ()

/-- Functors out of `WalkingIso` define isomorphisms in the target category. -/
@[simps!]
def toIso (F : WalkingIso.{w} ⥤ C) : F.obj zero ≅ F.obj one := F.mapIso iso

/-- From an isomorphism in a category, true can build a functor out of `WalkingIso` to
  that category. -/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso.{w} ⥤ C where
  obj := fun
    | zero => X
    | one => Y
  map := @fun
    | zero, zero, _ => 𝟙 _
    | zero, one,  _ => e.hom
    | one, zero, _ => e.inv
    | one, one,  _ => 𝟙 _
  map_comp := by rintro (_ | _) (_ | _) (_ | _) <;> simp

/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
def equiv : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · rintro (_ | _) <;> rfl
    · rintro (_ | _) (_ | _) (_) <;>
    ( rw [heq_eq_eq]
      unfold fromIso toIso
      dsimp
      try rw [← F.map_id]
      rfl )

end

/-- There are functors from the one-object category into `WalkingIso`,
  sending the object to either `zero` or `one`. -/
def coev (i : WalkingIso.{u}) : Fin 1 ⥤ WalkingIso.{u} := ComposableArrows.mk₀ i

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial Edge

/-- The simplicial set that encodes a single isomorphism.
  Its n-simplices are formal compositions of arrows in WalkingIso. -/
def coherentIso : SSet := nerve WalkingIso.{u}

namespace coherentIso

/-- Since the morphisms in WalkingIso do not carry information, an n-simplex of coherentIso
  is equivalent to an (n + 1)-vector of the objects of WalkingIso. -/
def equivFun {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → WalkingIso.{u}) where
  toFun f := f.obj
  invFun f := .mk f (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Since `Bool` (and hence `WalkingIso`) has decidable equality,
  the simplices of coherentIso have decidable equality as well. -/
instance (n : ℕ) : DecidableEq (coherentIso.{u} _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso.equivFun)

/-- The source vertex of `coherentIso`. -/
def x₀ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero.{u}

/-- The target vertex of `coherentIso`. -/
def x₁ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one.{u}

/-- The forwards edge of `coherentIso`. -/
def hom : Edge.{u} x₀ x₁ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The backwards edge of `coherentIso`. -/
def inv : Edge.{u} x₁ x₀ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The forwards and backwards edge of `coherentIso` compose to the identity. -/
def homInvId : Edge.CompStruct.{u} hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The backwards and forwards edge of `coherentIso` compose to the identity. -/
def invHomId : Edge.CompStruct.{u} inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` has an inverse. -/
def isIsoHom : Edge.InvStruct.{u} coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/-- The image of `hom` under an SSet has an inverse. -/
def isIsoMapHom {X : SSet} (g : coherentIso ⟶ X) : InvStruct.{u} (coherentIso.hom.map g)
  := isIsoHom.map g

/-- If an edge is equal to the image of `hom` under an SSet morphism,
  this edge has an inverse. -/
def isIsoOfEqMapHom {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {f : Edge x₀ x₁}
    {g : coherentIso ⟶ X}
    (hfg : f.edge = g.app _ hom.edge) :
  f.InvStruct :=
  (isIsoMapHom g).ofEq hfg.symm

end coherentIso

end SSet
