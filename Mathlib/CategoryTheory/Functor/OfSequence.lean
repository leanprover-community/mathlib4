/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.EqToHom

/-!
# Functors from the category of the ordered set `ℕ`

In this file, we provide a constructor `Functor.ofSequence`
for functors `ℕ ⥤ C` which takes as an input a sequence
of morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`.

We also provide a constructor `NatTrans.ofSequence` for natural
transformations between functors `ℕ ⥤ C` which allows to check
the naturality condition only for morphisms `n ⟶ n + 1`.

-/

namespace CategoryTheory

open Category

variable {C : Type*} [Category C]

namespace Functor

variable {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))

namespace OfSequence

lemma congr_f (i j : ℕ) (h : i = j) :
    f i = eqToHom (by rw [h]) ≫ f j ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The morphism `X i ⟶ X (i + k)` obtained by composing `k` morphisms of
the form `X n ⟶ X (n + 1)`. -/
@[simp]
def map' : ∀ (i k : ℕ), X i ⟶ X (i + k)
  | _, 0 => 𝟙 _
  | i, (k+1) => map' i k ≫ f (i + k)

lemma comp_map' (i k₁ k₂ : ℕ) :
    map' f i k₁ ≫ map' f (i + k₁) k₂ =
      map' f i (k₁ + k₂) ≫ eqToHom (by rw [add_assoc]) := by
  revert i k₁
  induction k₂ with
  | zero => simp
  | succ k₂ hk₂ =>
      intro i k₁
      simp [reassoc_of% (hk₂ i k₁), congr_f f _ _ (add_assoc i k₁ k₂)]

/-- The morphism `X i ⟶ X j` obtained by composing morphisms of
the form `X n ⟶ X (n + 1)` when `i ≤ j`. -/
def map (i j : ℕ) (hij : i ≤ j) : X i ⟶ X j :=
  map' f i (j - i) ≫ eqToHom (by congr; omega)

lemma map_eq (i j k : ℕ) (hk : i + k = j) :
    map f i j (by omega) = map' f i k ≫ eqToHom (by rw [hk]) := by
  obtain rfl := tsub_eq_of_eq_add_rev hk.symm
  rfl

lemma map_id (i : ℕ) : map f i i (by rfl) = 𝟙 _ := by
  rw [map_eq f i i 0 (by omega), eqToHom_refl, comp_id]
  rfl

lemma map_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk := by
  obtain ⟨k₁, rfl⟩ := Nat.exists_eq_add_of_le hij
  obtain ⟨k₂, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [map_eq f i _ k₁ rfl, eqToHom_refl, comp_id, map_eq f (i + k₁) _ k₂ rfl, eqToHom_refl,
    comp_id, comp_map', map_eq f i (i + k₁ + k₂) (k₁ + k₂) (by rw [add_assoc])]

lemma map_of_le_succ (n : ℕ) :
    map f n (n+1) (by omega) = f n := by
  simp [map_eq f n _ 1 rfl]

end OfSequence

/-- The functor `ℕ ⥤ C` constructed from a sequence of
morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`. -/
@[simps obj]
def ofSequence : ℕ ⥤ C where
  obj := X
  map {i j} φ := OfSequence.map f i j (leOfHom φ)
  map_id i := OfSequence.map_id f i
  map_comp {i j k} α β := OfSequence.map_comp f i j k (leOfHom α) (leOfHom β)

@[simp]
lemma ofSequence_map_homOfLE_succ (n : ℕ) :
    (ofSequence f).map (homOfLE (Nat.le_add_right n 1)) = f n :=
  OfSequence.map_of_le_succ f n

end Functor

namespace NatTrans

variable {F G : ℕ ⥤ C} (app : ∀ (n : ℕ), F.obj n ⟶ G.obj n)
  (naturality : ∀ (n : ℕ), F.map (homOfLE (n.le_add_right 1)) ≫ app (n + 1) =
      app n ≫ G.map (homOfLE (n.le_add_right 1)))

/-- Constructor for natural transformations `F ⟶ G` in `ℕ ⥤ C` which takes as inputs
the morphisms `F.obj n ⟶ G.obj n` for all `n : ℕ` and the naturality condition only
for morphisms of the form `n ⟶ n + 1`. -/
@[simps app]
def ofSequence : F ⟶ G where
  app := app
  naturality := by
    intro i j φ
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
    obtain rfl := Subsingleton.elim φ (homOfLE (by omega))
    revert i j
    induction k with
    | zero =>
        intro i j hk
        obtain rfl : j = i := by omega
        simp
    | succ k hk =>
        intro i j hk'
        obtain rfl : j = i + k + 1 := by omega
        simp only [← homOfLE_comp (show i ≤ i + k by omega) (show i + k ≤ i + k + 1 by omega),
          Functor.map_comp, assoc, naturality, reassoc_of% (hk rfl)]

end NatTrans

end CategoryTheory
