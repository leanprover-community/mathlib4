/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Dialectica category

We define the category `Dial` of the Dialectica interpretation, after [dialectica1989].

## Background

Dialectica categories are important models of linear type theory. They satisfy most of the
distinctions that linear logic was meant to introduce and many models do not satisfy, like the
independence of constants. Many linear type theories are being used at the
moment--[nLab] describes some of them: for quantum systems, for effects in programming, for linear
dependent types. In particular, dialectica categories are connected to polynomial functors, being a
slightly more sophisticated version of polynomial types, as discussed, for instance, in Moss and
von Glehn's [*Dialectica models of type theory*]. As such they are related to the polynomial
constructions being [developed][Poly] by Awodey, Riehl, and Hazratpour. For the non-dependent
version developed here several applications are known to Petri Nets, small cardinals
in Set Theory, state in imperative programming, and others, see [Dialectica Categories].

## References

* [Valeria de Paiva, The Dialectica Categories.][dialectica1989]
  ([pdf](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf))

[nLab]: https://ncatlab.org/nlab/show/linear+type+theory
[*Dialectica models of type theory*]: https://arxiv.org/abs/2105.00283
[Poly]: https://github.com/sinhp/Poly
[Dialectica Categories]: https://github.com/vcvpaiva/DialecticaCategories

-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open Limits

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

variable (C) in
/-- The Dialectica category. An object of the category is a triple `⟨U, X, α ⊆ U × X⟩`,
and a morphism from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair `(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that
`{(u,y) | α(u, F(u, y))} ⊆ {(u,y) | β(f(u), y)}`. The subset `α` is actually encoded as an element
of `Subobject (U × X)`, and the above inequality is expressed using pullbacks. -/
structure Dial where
  /-- The source object -/
  src : C
  /-- The target object -/
  tgt : C
  /-- A subobject of `src ⨯ tgt`, interpreted as a relation -/
  rel : Subobject (src ⨯ tgt)

namespace Dial

local notation "π₁" => prod.fst
local notation "π₂" => prod.snd
local notation "π(" a ", " b ")" => prod.lift a b

/-- A morphism in the `Dial C` category from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair
`(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that `{(u,y) | α(u, F(u, y))} ≤ {(u,y) | β(f(u), y)}`. -/
@[ext] structure Hom (X Y : Dial C) where
  /-- Maps the sources -/
  f : X.src ⟶ Y.src
  /-- Maps the targets (contravariantly) -/
  F : X.src ⨯ Y.tgt ⟶ X.tgt
  /-- This says `{(u, y) | α(u, F(u, y))} ⊆ {(u, y) | β(f(u), y)}` using subobject pullbacks -/
  le :
    (Subobject.pullback π(π₁, F)).obj X.rel ≤
    (Subobject.pullback (prod.map f (𝟙 _))).obj Y.rel

set_option backward.isDefEq.respectTransparency false in
theorem comp_le_lemma {X Y Z : Dial C} (F : Dial.Hom X Y) (G : Dial.Hom Y Z) :
    (Subobject.pullback π(π₁, π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F)).obj X.rel ≤
    (Subobject.pullback (prod.map (F.f ≫ G.f) (𝟙 Z.tgt))).obj Z.rel := by
  refine
    le_trans ?_ <| ((Subobject.pullback (π(π₁, prod.map F.f (𝟙 _) ≫ G.F))).monotone F.le).trans <|
    le_trans ?_ <| ((Subobject.pullback (prod.map F.f (𝟙 Z.tgt))).monotone G.le).trans ?_
    <;> simp [← Subobject.pullback_comp]

set_option backward.isDefEq.respectTransparency false in
@[simps]
instance : Category (Dial C) where
  Hom := Dial.Hom
  id X := {
    f := 𝟙 _
    F := π₂
    le := by simp
  }
  comp {_ _ _} (F G : Dial.Hom ..) := {
    f := F.f ≫ G.f
    F := π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F
    le := comp_le_lemma F G
  }
  assoc f g h := by
    simp only [Category.assoc, Hom.mk.injEq, true_and]
    rw [← Category.assoc, ← Category.assoc]; congr 1
    ext <;> simp

@[ext] theorem hom_ext {X Y : Dial C} {x y : X ⟶ Y} (hf : x.f = y.f) (hF : x.F = y.F) : x = y :=
  Hom.ext hf hF

set_option backward.isDefEq.respectTransparency false in
/--
An isomorphism in `Dial C` can be induced by isomorphisms on the source and target,
which respect the respective relations on `X` and `Y`.
-/
@[simps] def isoMk {X Y : Dial C} (e₁ : X.src ≅ Y.src) (e₂ : X.tgt ≅ Y.tgt)
    (eq : X.rel = (Subobject.pullback (prod.map e₁.hom e₂.hom)).obj Y.rel) : X ≅ Y where
  hom := {
    f := e₁.hom
    F := π₂ ≫ e₂.inv
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }
  inv := {
    f := e₁.inv
    F := π₂ ≫ e₂.hom
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }

end Dial

end CategoryTheory
