/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.Nerve

/-!
# Composable arrows

If `C` is a category, the type of `n`-simplices in the nerve of `C` identifies
to the type of functors `Fin (n + 1) ⥤ C`, which can be thought as families of `n` composable
arrows in `C`. In this file, we introduce and study this category `ComposableArrows C n`
of `n` composable arrows in `C`.

TODO (@joelriou):
* define various constructors for objects, morphisms, isomorphisms in `ComposableArrows C n`
* extensionality lemmas for morphisms
* extensionality lemmas for objects (useful for getting equalities of simplices in `nerve C`)
* construction of `precomp F f : ComposableArrows C (n + 1)` when `F : ComposableArrows C n`
and `f : X ⟶ F.left` with good definitional properties.
* constructors like `mk₃ f g h : ComposableArrows C 3` which would take as inputs a certain
number of composable morphisms
* redefine `Arrow C` as `ComposableArrow C 1`?
* construct some elements in `ComposableArrows m (Fin (n + 1))` for small `n`
the precomposition with which shall induce funtors
`ComposableArrows C n ⥤ ComposableArrows C m` which correspond to simplicial operations
(specifically faces) with good definitional properties (this might be necessary for
up to `n = 7` in order to formalize spectral sequences following Verdier)

-/

namespace CategoryTheory

open Category

variable (C : Type*) [Category C]

/-- `ComposableArrows C n` is the type of functors `Fin (n + 1) ⥤ C`. -/
abbrev ComposableArrows (n : ℕ) := Fin (n + 1) ⥤ C

/-- The type of `n`-simplices in the simplicial set `nerve C` is
definitionally equal to `ComposableArrows C n`. -/
lemma nerve_obj_eq_composableArrows (n : ℕ) :
    (nerve C).obj (Opposite.op (SimplexCategory.mk n)) = ComposableArrows C n := rfl

namespace ComposableArrows

variable {C} {n : ℕ}
variable (F G : ComposableArrows C n)

/-- The `i`th object (with `i : ℕ` such that `i ≤ n`) of `F : ComposableArrows C n`. -/
@[simp]
abbrev obj' (i : ℕ) (hi : i ≤ n := by linarith) : C := F.obj ⟨i, by linarith⟩

/-- The map `F.obj' i ⟶ F.obj' j` when `F : ComposableArrows C n`, and `i` and `j`
are natural numbers such that `i ≤ j ≤ n`. -/
@[simp]
abbrev map' (i j : ℕ) (hij : i ≤ j := by linarith) (hjn : j ≤ n := by linarith) :
  F.obj ⟨i, by linarith⟩ ⟶ F.obj ⟨j, by linarith⟩ := F.map (homOfLE (by
    simp only [Fin.mk_le_mk]
    linarith))

lemma map'_self (i : ℕ) (hi : i ≤ n := by linarith) :
    F.map' i i = 𝟙 _ := F.map_id _

lemma map'_comp (i j k : ℕ) (hij : i ≤ j := by linarith)
    (hjk : j ≤ k := by linarith) (hk : k ≤ n := by linarith) :
    F.map' i k = F.map' i j ≫ F.map' j k :=
  F.map_comp _ _

/-- The leftmost object of `F : ComposableArrows C n`. -/
abbrev left := obj' F 0

/-- The rightmost object of `F : ComposableArrows C n`. -/
abbrev right := obj' F n

/-- The canonical map `F.left ⟶ F.right` for `F : ComposableArrows C n`. -/
abbrev hom : F.left ⟶ F.right := map' F 0 n

variable {F G}

/-- The map `F.obj' i ⟶ G.obj' i` induced on `i`th objects by a morphism `F ⟶ G`
in `ComposableArrows C n` when `i` is a natural number such that `i ≤ n`. -/
@[simp]
abbrev app' (φ : F ⟶ G) (i : ℕ) (hi : i ≤ n := by linarith) :
    F.obj' i ⟶ G.obj' i := φ.app _

/-- Constructor for `ComposableArrows C 0`. -/
@[simps!]
def mk₀ (X : C) : ComposableArrows C 0 := (Functor.const (Fin 1)).obj X

namespace Mk₁

variable (X₀ X₁ : C)

/-- The map which sends `0 : Fin 2` to `X₀` and `1` to `X₁`. -/
@[simp]
def obj : Fin 2 → C
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩  => X₁

variable {X₀ X₁} (f : X₀ ⟶ X₁)

/-- The obvious map `obj X₀ X₁ i ⟶ obj X₀ X₁ j` whenever `i j : Fin 2` satisfy `i ≤ j`. -/
@[simp]
def map : ∀ (i j : Fin 2) (_ : i ≤ j), obj X₀ X₁ i ⟶ obj X₀ X₁ j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _

lemma map_id (i : Fin 2) : map f i i (by simp) = 𝟙 _ :=
  match i with
    | 0 => rfl
    | 1 => rfl

lemma map_comp {i j k : Fin 2} (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk :=
  match i with
    | 0 =>
        match j with
          | 0 => by rw [map_id, id_comp]
          | 1 => by
              obtain rfl : k = 1 := k.eq_one_of_neq_zero (by rintro rfl; simp at hjk)
              rw [map_id, comp_id]
    | 1 => by
        obtain rfl := j.eq_one_of_neq_zero (by rintro rfl; simp at hij)
        obtain rfl := k.eq_one_of_neq_zero (by rintro rfl; simp at hjk)
        rw [map_id, id_comp]

end Mk₁

/-- Constructor for `ComposableArrows C 1`. -/
@[simps]
def mk₁ {X₀ X₁ : C} (f : X₀ ⟶ X₁) : ComposableArrows C 1 where
  obj := Mk₁.obj X₀ X₁
  map g := Mk₁.map f _ _ (leOfHom g)
  map_id := Mk₁.map_id f
  map_comp g g' := Mk₁.map_comp f (leOfHom g) (leOfHom g')

end ComposableArrows

end CategoryTheory
