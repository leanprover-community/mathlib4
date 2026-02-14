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

universe u v

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects `false` and `true`. -/
def WalkingIso : Type u := ULift Bool

namespace WalkingIso

/-- The free isomorphism is the codiscrete category on two objects. -/
instance : Category (WalkingIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u} [Category.{v} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category. -/
def toIso (F : WalkingIso ⥤ C) : F.obj (ULift.up false) ≅ F.obj (ULift.up true) where
  hom := F.map PUnit.unit
  inv := F.map PUnit.unit
  hom_inv_id := by rw [← F.map_comp, ← F.map_id]; rfl
  inv_hom_id := by rw [← F.map_comp, ← F.map_id]; rfl

/-- From an isomorphism in a category, true can build a functor out of `WalkingIso` to
  that category. -/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso ⥤ C where
  obj := fun
    | (ULift.up false) => X
    | (ULift.up true) => Y
  map := @fun
    | ULift.up false, ULift.up false, _ => 𝟙 _
    | ULift.up false, ULift.up true,  _ => e.hom
    | ULift.up true, ULift.up false, _ => e.inv
    | ULift.up true, ULift.up true,  _ => 𝟙 _
  map_comp := by simp [WalkingIso, Quiver.Hom]

/-- An equivalence between the type of `WalkingIso`s in `C` and the type of isomorphisms in `C`. -/
def equiv : (WalkingIso ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj (ULift.up false), F.obj (ULift.up true), toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · simp [WalkingIso]
      constructor <;> rfl
    · simp only [WalkingIso, ULift.forall, Bool.forall_bool, heq_eq_eq]
      unfold fromIso toIso
      dsimp
      constructor <;> constructor <;>
      ( intro ⟨⟩
        try rfl
        try (rw [← F.map_id]; rfl) )

end

/-- There are functors from the one-object category into `WalkingIso`,
  sending the object to either `true` or `false`. -/
def coev (i : Bool) : Fin 1 ⥤ WalkingIso := ComposableArrows.mk₀ (ULift.up i)

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial Edge

/-- The simplicial set that encodes a single isomorphism.
  Its n-simplices are formal compositions of arrows in WalkingIso. -/
def coherentIso : SSet := nerve WalkingIso

namespace coherentIso

/-- Since the morphisms in WalkingIso do not carry information, an n-simplex of coherentIso
  is equivalent to an (n + 1)-vector of the objects of WalkingIso. -/
def equivFun {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → Bool) where
  toFun f := ULift.down ∘ f.obj
  invFun f := .mk (ULift.up ∘ f) (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Since Fin 2 has decidable equality,
  the simplices of coherentIso have decidable equality as well. -/
instance (n : ℕ) : DecidableEq (coherentIso _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso.equivFun)

/-- The source vertex of `coherentIso`. -/
def x₀ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ (ULift.up false)

/-- The target vertex of `coherentIso`. -/
def x₁ : coherentIso _⦋0⦌ :=
  ComposableArrows.mk₀ (ULift.up false)

/-- The forwards edge of `coherentIso`. -/
def hom : Edge x₀ x₁ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The backwards edge of `coherentIso`. -/
def inv : Edge x₁ x₀ where
  edge := ComposableArrows.mk₁ ⟨⟩
  src_eq := ComposableArrows.ext₀ rfl
  tgt_eq := ComposableArrows.ext₀ rfl

/-- The forwards and backwards edge of `coherentIso` compose to the identity. -/
def homInvId : Edge.CompStruct hom inv (Edge.id x₀) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The backwards and forwards edge of `coherentIso` compose to the identity. -/
def invHomId : Edge.CompStruct inv hom (Edge.id x₁) where
  simplex := ComposableArrows.mk₂ ⟨⟩ ⟨⟩
  d₂ := ComposableArrows.ext₁ rfl rfl rfl
  d₀ := ComposableArrows.ext₁ rfl rfl rfl
  d₁ := ComposableArrows.ext₁ rfl rfl rfl

/-- The forwards edge of `coherentIso` has an inverse. -/
def isIsoHom : Edge.InvStruct coherentIso.hom where
  inv := inv
  homInvId := homInvId
  invHomId := invHomId

/-- The image of `hom` under an SSet has an inverse. -/
def isIsoMapHom {X : SSet} (g : coherentIso ⟶ X) : InvStruct (coherentIso.hom.map g)
  := isIsoHom.map g

/-- If an edge is equal to the image of `hom` under an SSet morphism,
  this edge has an inverse. -/
def isIsoOfEqMapHom {X : SSet} {x₀ x₁ : X _⦋0⦌}
    {f : Edge x₀ x₁}
    {g : coherentIso ⟶ X}
    (hfg : f.edge = g.app _ hom.edge) :
  f.InvStruct :=
  (isIsoMapHom g).ofEq hfg.symm

end coherentIso

end SSet
