/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar, Arnoud van der Leer
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
public import Mathlib.CategoryTheory.CodiscreteCategory

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
and `invStructOfEqMapHom` concludes from this that for any simplicial set `X`,
any morphism `g : coherentIso ⟶ X` and any `f : X _⦋1⦌`,
if `g` sends `hom` to `f`, then `f` has an inverse.

-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as the codiscrete category on `Bool`. -/
abbrev WalkingIso : Type u := Codiscrete (ULift Bool)

namespace WalkingIso

/-- The underlying type of `WalkingIso` is equivalent to `Bool`, since they both have 2 elements. -/
def equivBool : WalkingIso.{u} ≃ Bool := codiscreteEquiv.trans Equiv.ulift

instance homUnique {x y : WalkingIso.{u}} : Unique (x ⟶ y) := inferInstanceAs (Unique Unit)

section

variable {C : Type u} [Category.{v} C]

/-- The domain of the isomorphism -/
def zero : WalkingIso := .mk (ULift.up false)

/-- The codomain of the isomorphism -/
def one : WalkingIso := .mk (ULift.up true)

/-- The isomorphism at the heart of `WalkingIso` -/
def iso : zero ≅ one := Codiscrete.iso zero one

lemma eq_iso_hom (f : zero ⟶ one) : f = iso.hom := Codiscrete.eq_iso_hom f

lemma eq_iso_inv (f : one ⟶ zero) : f = iso.inv := Codiscrete.eq_iso_inv f

/-- Functors out of `WalkingIso` define isomorphisms in the target category. -/
@[simps!]
def toIso (F : WalkingIso.{w} ⥤ C) : F.obj zero ≅ F.obj one := F.mapIso iso

/-- From an isomorphism in a category, true can build a functor out of `WalkingIso` to
  that category. -/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso.{w} ⥤ C where
  obj x := by
    rcases ULift.down x.as
    · exact X
    · exact Y
  map {x} {y} _ := by
    rcases ULift.down x.as <;> rcases ULift.down y.as
    · exact 𝟙 _
    · exact e.hom
    · exact e.inv
    · exact 𝟙 _
  map_comp := by rintro (_ | _) (_ | _) (_ | _) <;> simp
  map_id := by rintro (_ | _) <;> rfl

section

variable {X Y : C} (e : X ≅ Y)

@[simp]
lemma fromIso_zero : (fromIso e).obj .zero = X := rfl

@[simp]
lemma fromIso_one : (fromIso e).obj .one = Y := rfl

@[simp]
lemma fromIso_map_zero_zero (f : zero ⟶ zero) : (fromIso e).map f = 𝟙 X := rfl

@[simp]
lemma fromIso_hom (f : zero ⟶ one) : (fromIso e).map f = e.hom := rfl

@[simp]
lemma fromIso_inv (f : one ⟶ zero) : (fromIso e).map f = e.inv := rfl

@[simp]
lemma fromIso_map_one_one (f : one ⟶ one) : (fromIso e).map f = 𝟙 Y := rfl

end

/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
@[simps]
def equiv : (WalkingIso.{w} ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · rintro (_ | _) <;> rfl
    · rintro (_ | _) (_ | _) (_) <;>
    ( rw [heq_eq_eq]
      dsimp
      try rw [← F.map_id]
      rfl )

/- TODO: Extend the above to an equivalence of categories between
the functor category `WalkingIso.{w} ⥤ C` and `Core C`. -/

end

end WalkingIso

namespace Codiscrete

open Simplicial

/-- Since the morphisms in a codiscrete category do not carry information, an n-simplex of
  coherentIso is equivalent to an X-vector of length (n + 1). -/
def equivFun {X : Type u} {n : ℕ} : nerve (Codiscrete X) _⦋n⦌ ≃ (Fin (n + 1) → X) where
  toFun f n := (f.obj n).as
  invFun f := .mk (fun n ↦ .mk (f n)) (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Since `Bool` (and hence `WalkingIso`) has decidable equality,
  the simplices of coherentIso have decidable equality as well. -/
instance {X : Type u} [DecidableEq X] {n : ℕ} : DecidableEq (nerve (Codiscrete X) _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq equivFun)

end Codiscrete

end CategoryTheory

namespace SSet

open Simplicial Edge

/-- The simplicial set that encodes a single isomorphism.
  Its n-simplices are formal compositions of arrows in WalkingIso. -/
def coherentIso : SSet := nerve WalkingIso.{u}

namespace coherentIso

instance : IsStrictSegal coherentIso := inferInstanceAs (IsStrictSegal (nerve _))

instance {n : ℕ} : DecidableEq (coherentIso _⦋n⦌) :=
  inferInstanceAs (DecidableEq (nerve (Codiscrete _) _⦋n⦌))

/-- The source vertex of `coherentIso`. -/
def x₀ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.zero.{u}

/-- The target vertex of `coherentIso`. -/
def x₁ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ WalkingIso.one.{u}

/-- The forwards edge of `coherentIso`. -/
def hom : Edge.{u} x₀ x₁ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.hom
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The backwards edge of `coherentIso`. -/
def inv : Edge.{u} x₁ x₀ where
  edge := ComposableArrows.mk₁ WalkingIso.iso.inv
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The forwards and backwards edge of `coherentIso` compose to the identity. -/
def homInvId : Edge.CompStruct.{u} hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.hom WalkingIso.iso.inv
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The backwards and forwards edge of `coherentIso` compose to the identity. -/
def invHomId : Edge.CompStruct.{u} inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ WalkingIso.iso.inv WalkingIso.iso.hom
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` has an inverse. -/
@[simps]
def invStructHom : Edge.InvStruct.{u} coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/-- If an edge is equal to the image of `hom` under an SSet morphism,
  this edge has an inverse. -/
def invStructOfEqMapHom {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}
    {f : Edge x₀ x₁}
    {g : coherentIso ⟶ X}
    (hfg : f.edge = g.app _ hom.edge) :
    f.InvStruct :=
  (invStructHom.map g).ofEq hfg.symm

end coherentIso

end SSet
