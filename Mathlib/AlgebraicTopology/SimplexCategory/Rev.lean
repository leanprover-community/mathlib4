/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The covariant involution of the simplex category

In this file, we introduce the functor `rev : SimplexCategory ⥤ SimplexCategory`
which, via the equivalence between the simplex category and the
category of nonempty finite linearly ordered types, corresponds to
the *covariant* functor which sends a type `α` to `αᵒᵈ`.

-/

open CategoryTheory

namespace SimplexCategory

/-- The covariant involution `rev : SimplexCategory ⥤ SimplexCategory` which,
via the equivalence between the simplex category and the
category of nonempty finite linearly ordered types, corresponds to
the *covariant* functor which sends a type `α` to `αᵒᵈ`.
This functor sends the object `⦋n⦌` to `⦋n⦌` and a map `f : ⦋n⦌ ⟶ ⦋m⦌`
is sent to the monotone map `(i : Fin (n + 1)) ↦ (f i.rev).rev`. -/
@[simps obj]
def rev : SimplexCategory ⥤ SimplexCategory where
  obj n := n
  map {n m} f := Hom.mk ⟨fun i ↦ (f i.rev).rev, fun i j hij ↦ by
    rw [Fin.rev_le_rev]
    exact f.toOrderHom.monotone (by rwa [Fin.rev_le_rev])⟩

@[simp]
lemma rev_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (rev.map f).toOrderHom (a := n) (b := m) i = (f.toOrderHom i.rev).rev := by
  rfl

@[simp]
lemma rev_map_δ {n : ℕ} (i : Fin (n + 2)) :
    rev.map (δ i) = δ i.rev := by
  ext j : 3
  rw [rev_map_apply]
  dsimp [δ]
  rw [Fin.succAbove_rev_right, Fin.rev_rev]

@[simp]
lemma rev_map_σ {n : ℕ} (i : Fin (n + 1)) :
    rev.map (σ i) = σ i.rev := by
  ext j : 3
  rw [rev_map_apply]
  dsimp [σ]
  rw [Fin.predAbove_rev_right, Fin.rev_rev]

/-- The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
is a covariant involution. -/
@[simps!]
def revCompRevIso : rev ⋙ rev ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

@[simp]
lemma rev_map_rev_map {n m : SimplexCategory} (f : n ⟶ m) :
    rev.map (rev.map f) = f := by
  aesop

/-- The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
as an equivalence of category. -/
@[simps]
def revEquivalence : SimplexCategory ≌ SimplexCategory where
  functor := rev
  inverse := rev
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso

end SimplexCategory
