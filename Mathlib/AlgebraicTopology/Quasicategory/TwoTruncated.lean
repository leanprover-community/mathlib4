/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Komaromy
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated

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

@[expose] public section

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
(0, 1)-edge `f`, (1, 2)-edge `Edge.id` and (0, 2)-edge `g`. We use `Nonempty` to
have a `Prop` valued `HomotopicL`.
-/
abbrev HomotopicL {X : Truncated 2} {x y : X _⦋0⦌₂} (f g : Edge x y) :=
  Nonempty (CompStruct f (id y) g)

/--
Two edges `f` and `g` are right homotopic if there is a `CompStruct` with
(0, 1)-edge `Edge.id`, (1, 2)-edge `f`, and (0, 2)-edge `g`. We use `Nonempty` to
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
Given `CompStruct f g h` and `CompStruct f' g' h'` with the same vertices and edges such
that `f` ≃ `f'` and `g` ≃ `g'`, then the long diagonal edges `h` and `h'` are also homotopic.
-/
lemma Edge.CompStruct.comp_unique {f f' : Edge x y} {g g' : Edge y z} {h h' : Edge x z}
    (s : CompStruct f g h) (s' : CompStruct f' g' h')
    (hf : HomotopicL f f') (hg : HomotopicL g g') : HomotopicL h h' := by
  rcases hg.homotopicR with ⟨hg⟩
  rcases hf with ⟨hf⟩
  let ⟨s₁⟩ := Quasicategory₂.fill32 hf (idComp g') s'
  let ⟨s₂⟩ := Quasicategory₂.fill31 (compId f) hg s₁
  exact Quasicategory₂.fill31 s (compId g) s₂

/--
Given two consecutive edges `f`, `g`  in a 2-truncated quasicategory, nonconstructively choose
an edge that is the diagonal of a 2-simplex with spine given by `f` and `g`. The `CompStruct`
witnessing this property is given by `Edge.composeStruct`.
-/
noncomputable
def Edge.comp (f : Edge x y) (g : Edge y z) := (Nonempty.some (Quasicategory₂.fill21 f g )).1

/--
See `Edge.comp`
-/
noncomputable
def Edge.compStruct (f : Edge x y) (g : Edge y z) := (Nonempty.some (Quasicategory₂.fill21 f g )).2

/--
The edge `composeEdges f g` is the unique edge up to homotopy such that there is
a 2-simplex with spine given by `f` and `g`.
-/
lemma composeEdges_unique {f : Edge x y} {g : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) : HomotopicL h (comp f g) :=
  comp_unique s (compStruct f g) .refl .refl

/--
Given two pairs of composable edges `f`, `g` and `f'`, `g'` such that `f` ≃ `f'` and
`g` ≃ `g'`, their composites `h` and `h'` chosen by `composeEdges` are homotopic.
-/
lemma composeEdges_homotopic {f f' : Edge x y} {g g' : Edge y z}
    (hf : HomotopicL f f') (hg : HomotopicL g g') :
    HomotopicL (comp f g) (comp f' g') :=
  comp_unique (compStruct f g) (compStruct f' g') hf hg

/--
The homotopy category of a 2-truncated quasicategory `A` has as objects the vertices of `A`
-/
structure HomotopyCategory₂ (A : Truncated 2) where
  /-- An object of the homotopy category is a vertex of `A`. -/
  pt : A _⦋0⦌₂

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
def HomotopyCategory₂.Hom (x y : HomotopyCategory₂ A) := Quotient (instSetoidEdge x.pt y.pt)

/--
Composition of morphisms in `HomotopyCategory₂ A` is given by lifting the edge
chosen by `composeEdges`.
-/
noncomputable
instance : CategoryStruct (HomotopyCategory₂ A) where
  Hom x y := HomotopyCategory₂.Hom x y
  id x := Quotient.mk' (Edge.id x.pt)
  comp := Quotient.lift₂
    (fun f g ↦ ⟦comp f g⟧)
    (fun _ _ _ _ hf hg ↦ Quotient.sound (composeEdges_homotopic hf hg))

/--
A vertex `x` of `A` defines an object of `HomotopyCategory₂ A`.
-/
def mk (x : A _⦋0⦌₂) : HomotopyCategory₂ A := ⟨x⟩

/--
Any edge in the 2-truncated simplicial set `A` defines a morphism in the homotopy category
by taking its equivalence class.
-/
def homMk (f : Edge x y) : mk x ⟶ mk y := ⟦f⟧

/--
The trivial (degenerate) edge at a vertex `x` is a representative for the
identity morphism `x ⟶ x`.
-/
@[simp]
lemma homMk_refl (x : HomotopyCategory₂ A) : homMk (Edge.id x.pt) = 𝟙 x := rfl

/--
(Left) homotopic edges represent the same morphism in the homotopy category.
-/
lemma homMk_eq_of_homotopy {f f' : Edge x y} (h : HomotopicL f f') :
  homMk f = homMk f' := Quotient.eq.mpr h

/--
A `CompStruct f g h` is a witness for the fact that the morphisms represented by
`f` and `g` compose to the morphism represented by `h`.
-/
lemma Edge.CompStruct.fac {f : Edge x y} {g : Edge y z} {h : Edge x z}
    (s : CompStruct f g h) : homMk f ≫ homMk g = homMk h :=
  homMk_eq_of_homotopy (composeEdges_unique s).symm

/--
If we have a factorization `homMk f ≫ homMk g = homMk h`, we know that there exists
some `CompStruct f g h`.
-/
lemma Edge.CompStruct.compStruct_from_fac {f : Edge x y} {g : Edge y z} {h : Edge x z}
    (fac : homMk f ≫ homMk g = homMk h) : Nonempty (CompStruct f g h) := by
  dsimp [homMk, CategoryStruct.comp] at fac
  rw [Quotient.eq_iff_equiv] at fac
  exact Quasicategory₂.fill32 (compStruct f g) (compId g) fac.some

/--
A combination of `Edge.CompStruct.fac` and `Edge.CompStruct.compStruct_from_fac`.
-/
lemma Edge.CompStruct.fac_iff_compStruct {f : Edge x y} {g : Edge y z} {h : Edge x z} :
    homMk f ≫ homMk g = homMk h ↔ Nonempty (CompStruct f g h) :=
  ⟨compStruct_from_fac, fun ⟨s⟩ ↦ fac s⟩

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
    let fg := comp f g
    apply Nonempty.some
    exact Quasicategory₂.fill32 (compStruct f g) (compStruct g h) (compStruct fg h)

end homotopy_category

end SSet.Truncated
