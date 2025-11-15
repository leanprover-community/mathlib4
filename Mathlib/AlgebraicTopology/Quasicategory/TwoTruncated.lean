/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated

/-!
# 2-truncated quasicategories and homotopy relations

We define 2-truncated quasicategories `Quasicategory₂` by three horn-filling properties,
and the left and right homotopy relations `HomotopicL` and `HomotopicR` on the edges in a
2-truncated simplicial set.

We prove that for 2-truncated quasicategories, both homotopy relations are equivalence
relations, and that the left and right homotopy relations coincide.

For a 2-truncated quasicategory `A`, we define a category `HomotopyCategory₂ A` whose
morphisms are given by (left) homotopy classes of edges. The construction of this category
is different from `HomotopyCategory A` in `AlgebraicTopology.SimplicialSet.HomotopyCat`:
* `HomotopyCategory₂ A` has morphisms given by homotopy classes of edges
* `HomotopyCategory A` has morphisms given by equivalence classes of paths in the underlying
  reflexive quiver of `A`.

The two constructions agree for 2-truncated quasicategories (TODO: handled by future PR).

## Implementation notes

Throughout this file, we make use of `Edge` and `CompStruct` to conveniently deal with
edges and triangles in a 2-truncated simplicial set.
-/

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated
open Edge CompStruct

/--
A 2-truncated quasicategory is a 2-truncated simplicial set with the properties:
* (2, 1)-filling: given two consecutive `Edge`s `e₀₁` and `e₁₂`, there exists a `CompStruct`
  with (0, 1)-edge `e₀₁` and (0, 2)-edge `e₁₂`.
* (3, 1)-filling: given three `CompStruct`s `f₃`, `f₀` and `f₂` which form a (3, 1)-horn,
  there exists a fourth `CompStruct` such that the four faces form the boundary
  ∂Δ[3] of a 3-simplex.
* (3, 2)-filling: given three `CompStruct`s `f₃`, `f₀` and `f₁` which form a (3, 2)-horn,
  there exists a fourth `CompStruct` such that the four faces form the boundary
  ∂Δ[3] of a 3-simplex.
-/
class Quasicategory₂ (X : Truncated 2) where
  fill21 {x₀ x₁ x₂ : X _⦋0⦌₂}
      (e₀₁ : Edge x₀ x₁) (e₁₂ : Edge x₁ x₂) :
      Nonempty (Σ e₀₂ : Edge x₀ x₂, CompStruct e₀₁ e₁₂ e₀₂)
  fill31 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₂ : CompStruct e₀₁ e₁₃ e₀₃) :
      Nonempty (CompStruct e₀₂ e₂₃ e₀₃)
  fill32 {x₀ x₁ x₂ x₃ : X _⦋0⦌₂}
      {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
      {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
      (f₃ : CompStruct e₀₁ e₁₂ e₀₂)
      (f₀ : CompStruct e₁₂ e₂₃ e₁₃)
      (f₁ : CompStruct e₀₂ e₂₃ e₀₃) :
      Nonempty (CompStruct e₀₁ e₁₃ e₀₃)

/--
Two edges `f` and `g` are left homotopic if there is a `CompStruct` with
(0, 1)-edge `f`, (1, 2)-edge `id` and (0, 2)-edge `g`. We use `Nonempty` to
have a `Prop` valued `HomotopicL`.
-/
abbrev HomotopicL {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y) :=
  Nonempty (CompStruct f (id y) g)

/--
Two edges `f` and `g` are right homotopic if there is a `CompStruct` with
(0, 1)-edge `id`, (1, 2)-edge `f`, and (0, 2)-edge `g`. We use `Nonempty` to
have a `Prop` valued `HomotopicR`.
-/
abbrev HomotopicR {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y) :=
  Nonempty (CompStruct (id x) f g)

section homotopy_eqrel
variable {X : Truncated 2}

/--
The left homotopy relation is reflexive.
-/
lemma HomotopicL.refl {x y : X _⦋0⦌₂} {f : Edge x y} : HomotopicL f f := ⟨compId f⟩

/--
The left homotopy relation is symmetric.
-/
lemma HomotopicL.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicL f g) :
    HomotopicL g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill31 hfg (idComp (id y)) (compId f)

/--
The left homotopy relation is transitive.
-/
lemma HomotopicL.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicL f g)
    (hgh : HomotopicL g h) : HomotopicL f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill32 hfg (idComp (id y)) hgh

/--
The right homotopy relation is reflexive.
-/
lemma HomotopicR.refl {x y : X _⦋0⦌₂} {f : Edge x y} : HomotopicR f f := ⟨idComp f⟩

/--
The right homotopy relation is symmetric.
-/
lemma HomotopicR.symm [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} (hfg : HomotopicR f g) :
    HomotopicR g f := by
  rcases hfg with ⟨hfg⟩
  exact Quasicategory₂.fill32 (idComp (id x)) hfg (idComp f)

/--
The right homotopy relation is transitive.
-/
lemma HomotopicR.trans [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g h : Edge x y} (hfg : HomotopicR f g)
    (hgh : HomotopicR g h) : HomotopicR f h := by
  rcases hfg with ⟨hfg⟩
  rcases hgh with ⟨hgh⟩
  exact Quasicategory₂.fill31 (idComp (id x)) hfg hgh

/--
In a 2-truncated quasicategory, left homotopy implies right homotopy.
-/
lemma HomotopicL.homotopicR [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
    (h : HomotopicL f g) : HomotopicR f g := by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill32 (idComp f) (compId f) h

/--
In a 2-truncated quasicategory, right homotopy implies left homotopy.
-/
lemma HomotopicR.homotopicL [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y}
    (h : HomotopicR f g) : HomotopicL f g := by
  rcases h with ⟨h⟩
  exact Quasicategory₂.fill31 (idComp f) (compId f) h

/--
In a 2-truncated quasicategory, the right and left homotopy relations coincide.
-/
theorem homotopicL_iff_homotopicR [Quasicategory₂ X] {x y : X _⦋0⦌₂} {f g : Edge x y} :
    HomotopicL f g ↔ HomotopicR f g :=
  ⟨HomotopicL.homotopicR, HomotopicR.homotopicL⟩

end homotopy_eqrel


section homotopy_category
variable {A : Truncated 2} [Quasicategory₂ A] {x y z : A _⦋0⦌₂}

/--
Given a 2-simplex with edges `f`, `g` and `h`, and an additional edge `g'` homotopic to `g`,
there exists a 2-simplex with edges  `f`, `g'` and `h`.
-/
lemma transport_edge₀ {f : Edge x y} {g g' : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL g g') : Nonempty (CompStruct f g' h) := by
  rcases htpy with ⟨htpy⟩
  exact Quasicategory₂.fill32 s htpy (compId h)

/--
Given a 2-simplex with edges `f`, `g` and `h`, and an additional edge `h'` homotopic to `h`,
there exists a 2-simplex with edges  `f`, `g` and `h'`.
-/
lemma transport_edge₁ {f : Edge x y} {g : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL h h') : Nonempty (CompStruct f g h') := by
  rcases (HomotopicL.homotopicR htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 (idComp f) s htpy

/--
Given a 2-simplex with edges `f`, `g` and `h`, and an additional edge `f'` homotopic to `f`,
there exists a 2-simplex with edges  `f'`, `g` and `h`.
-/
lemma transport_edge₂ {f f' : Edge x y} {g : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) (htpy : HomotopicL f f') : Nonempty (CompStruct f' g h) := by
  rcases (HomotopicL.homotopicR htpy) with ⟨htpy⟩
  exact Quasicategory₂.fill31 htpy s (idComp h)

/--
The combination of `transport_edge₀`, `transport_edge₁`, and `transport_edge₂`
-/
lemma transport_all_edges {f f' : Edge x y} {g g' : Edge y z} {h h' : Edge x z}
    (hf : HomotopicL f f') (hg : HomotopicL g g') (hh : HomotopicL h h')
    (s : CompStruct f g h) : Nonempty (CompStruct f' g' h') :=
  Nonempty.elim
    (Nonempty.elim (transport_edge₂ s hf) (fun s ↦ transport_edge₀ s hg))
    (fun s ↦ transport_edge₁ s hh)

/--
Given two consecutive `Edge`s `f` and `g`, the long diagonals of any two 2-simplices
`s` and `s'` with spine `f``g` are homotopic.
-/
lemma comp_unique {f : Edge x y} {g : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (s' : CompStruct f g h') : HomotopicL h h' :=
  HomotopicR.homotopicL (Quasicategory₂.fill32 (idComp f) s s')

/--
Given two consecutive edges `f`, `g`  in a 2-truncated quasicategory, nonconstructively choose:
* an edge that is the diagonal of a 2-simplex with spine given by `f` and `g`, and
* a 2-simplex witness this property.
-/
noncomputable
def composeEdges {x₀ x₁ x₂ : A _⦋0⦌₂} (f : Edge x₀ x₁) (g : Edge x₁ x₂) :=
  Nonempty.some (Quasicategory₂.fill21 f g)

/--
The edge `composeEdges f g` is the unique edge up to homotopy such that there is
a 2-simplex with spine given by `f` and `g`
-/
lemma composeEdges_unique {x₀ x₁ x₂ : A _⦋0⦌₂} {f : Edge x₀ x₁} {g : Edge x₁ x₂} {h : Edge x₀ x₂}
    (s : CompStruct f g h) : HomotopicL h (composeEdges f g).1 :=
  comp_unique s (composeEdges f g).2

/--
Given two pairs of composable edges `f`, `g` and `f'`, `g'` such that `f` ≃ `f'` and
`g` ≃ `g'`, their composites `h` and `h'` chosen by `composeEdges` are homotopic.
-/
lemma composeEdges_homotopic {x₀ x₁ x₂ : A _⦋0⦌₂} {f f' : Edge x₀ x₁} {g g' : Edge x₁ x₂}
    (hf : HomotopicL f f') (hg : HomotopicL g g') :
    HomotopicL (composeEdges f g).1 (composeEdges f' g').1 := by
  apply comp_unique (composeEdges f g).2
  apply Nonempty.some
  exact transport_all_edges (HomotopicL.symm hf) (HomotopicL.symm hg)
    (HomotopicL.refl) (composeEdges f' g').2

/--
The homotopy category of a 2-truncated quasicategory `A` has as objects the vertices of `A`
-/
def HomotopyCategory₂ (A : Truncated 2) := A _⦋0⦌₂

/--
Left homotopy is an equivalence relation on the edges of `A`.
Remark: We could have equivalently chosen right homotopy, as shown by `homotopicL_iff_homotopicR`.
-/
instance instSetoidEdge (x y : A _⦋0⦌₂) : Setoid (Edge x y) where
  r := HomotopicL
  iseqv := ⟨fun _ ↦ HomotopicL.refl, HomotopicL.symm, HomotopicL.trans⟩

/--
The morphisms between two vertices `x`, `y` in `HomotopyCategory₂ A` are homotopy classes
of edges between `x` and `y`.
-/
def HomotopyCategory₂.Hom (x y : A _⦋0⦌₂) := Quotient (instSetoidEdge x y)

/--
Composition of morphisms in `HomotopyCategory₂ A` is given by lifting the edge
chosen by `composeEdges`.
-/
noncomputable
instance : CategoryStruct (HomotopyCategory₂ A) where
  Hom x₀ x₁ := HomotopyCategory₂.Hom x₀ x₁
  id x₀ := Quotient.mk' (Edge.id x₀)
  comp := Quotient.lift₂
    (fun f g ↦ ⟦(composeEdges f g).1⟧)
    (fun _ _ _ _ hf hg ↦ Quotient.sound (composeEdges_homotopic hf hg))

noncomputable
instance instCategoryHomotopyCategory₂ : Category (HomotopyCategory₂ A) where
  id_comp f := by
    rcases f with ⟨f⟩
    apply Quotient.sound
    exact symm (composeEdges_unique (CompStruct.idComp f))
  comp_id f := by
    rcases f with ⟨f⟩
    apply Quotient.sound
    exact symm (composeEdges_unique (CompStruct.compId f))
  assoc f g h := by
    rcases f, g, h with ⟨⟨f⟩, ⟨g⟩, ⟨h⟩⟩
    apply Quotient.sound
    apply composeEdges_unique
    let fg := (composeEdges f g).1
    apply Nonempty.some
    exact Quasicategory₂.fill32 (composeEdges f g).2 (composeEdges g h).2 (composeEdges fg h).2

end homotopy_category

end SSet.Truncated
