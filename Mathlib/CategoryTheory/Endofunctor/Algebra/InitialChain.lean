/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Iterated endofunctors and the initial chain

Given an endofunctor `F : C ⥤ C`, we define the iterated functor `F.iterate n : C ⥤ C`
which applies `F` a total of `n` times. This is a general-purpose definition that does
not require the category to have an initial object.

Given additionally an initial object, the *initial chain* is the sequence
`⊥ → F(⊥) → F²(⊥) → ⋯` viewed as a functor from `ℕ` (as a preorder category) to `C`.

## Main definitions

- `CategoryTheory.Functor.iterate F n` : the `n`-th iterate `F^n : C ⥤ C`
- `CategoryTheory.Endofunctor.iterateMap F n` : the successor map `F^n(⊥) → F^{n+1}(⊥)`
- `CategoryTheory.Endofunctor.initialChain F` : the functor `ℕ ⥤ C`

## Main results

- `CategoryTheory.Endofunctor.initialChain_map_succ` : the map for `n ≤ n+1` is `iterateMap F n`
- `CategoryTheory.Endofunctor.initialChain_map_succ_eq` : the chain map at successor indices
  equals `F` applied to the chain map

## References

- [J. Adamek, *Free algebras and automata realizations in the language of categories and
  functors*][adamek1974]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory.Functor

/-- The `n`-th iterate of an endofunctor `F : C ⥤ C`:
`F.iterate 0 = 𝟭 C` and `F.iterate (n + 1) = F.iterate n ⋙ F`. -/
def iterate (F : C ⥤ C) : ℕ → (C ⥤ C)
  | 0 => 𝟭 C
  | n + 1 => F.iterate n ⋙ F

@[simp]
lemma iterate_zero (F : C ⥤ C) : F.iterate 0 = 𝟭 C := rfl

@[simp]
lemma iterate_succ (F : C ⥤ C) (n : ℕ) : F.iterate (n + 1) = F.iterate n ⋙ F := rfl

end CategoryTheory.Functor

namespace CategoryTheory.Endofunctor

section InitialChain

variable (F : C ⥤ C) [HasInitial C]

/-- The successor map `F^n(⊥) → F^{n+1}(⊥)` in the initial chain, defined by
applying `F` iteratively to the unique map from the initial object. -/
noncomputable def iterateMap :
    (n : ℕ) → (F.iterate n).obj (⊥_ C) ⟶ (F.iterate (n + 1)).obj (⊥_ C)
  | 0 => initial.to _
  | n + 1 => F.map (iterateMap n)

/-- The initial chain: the functor `ℕ ⥤ C` sending `n` to `F^n(⊥)`,
constructed via `Functor.ofSequence` from the successor maps. -/
noncomputable def initialChain : ℕ ⥤ C :=
  Functor.ofSequence (X := fun n => (F.iterate n).obj (⊥_ C)) (iterateMap F)

@[simp]
lemma initialChain_obj (n : ℕ) :
    (initialChain F).obj n = (F.iterate n).obj (⊥_ C) := rfl

@[simp]
lemma initialChain_map_succ (n : ℕ) :
    (initialChain F).map (homOfLE (Nat.le_add_right n 1)) = iterateMap F n :=
  Functor.ofSequence_map_homOfLE_succ (iterateMap F) n

/-- The chain map at successor indices equals `F` applied to the chain map.
This is the key structural property: the `(m+1)`-to-`(n+1)` map in the chain
is `F` applied to the `m`-to-`n` map. -/
lemma initialChain_map_succ_eq {m n : ℕ} (h : m ≤ n) :
    (initialChain F).map (homOfLE (Nat.succ_le_succ h)) =
    F.map ((initialChain F).map (homOfLE h)) := by
  induction h with
  | refl =>
    have h1 : (homOfLE (Nat.succ_le_succ (le_refl m)) : (m+1 : ℕ) ⟶ (m+1 : ℕ)) = 𝟙 _ :=
      Subsingleton.elim _ _
    have h2 : (homOfLE (le_refl m) : (m : ℕ) ⟶ (m : ℕ)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [h1, h2, Functor.map_id, Functor.map_id, F.map_id]
    rfl
  | @step k h' ih =>
    have decomp_lhs :
        (homOfLE (Nat.succ_le_succ (Nat.le.step h')) : (m+1 : ℕ) ⟶ (k+2 : ℕ)) =
        (homOfLE (Nat.succ_le_succ h') : (m+1 : ℕ) ⟶ (k+1 : ℕ)) ≫
        (homOfLE (Nat.le_add_right (k+1) 1) : (k+1 : ℕ) ⟶ (k+2 : ℕ)) :=
      Subsingleton.elim _ _
    have decomp_rhs :
        (homOfLE (Nat.le.step h') : (m : ℕ) ⟶ (k+1 : ℕ)) =
        (homOfLE h' : (m : ℕ) ⟶ (k : ℕ)) ≫
        (homOfLE (Nat.le_add_right k 1) : (k : ℕ) ⟶ (k+1 : ℕ)) :=
      Subsingleton.elim _ _
    rw [decomp_lhs, Functor.map_comp, ih, decomp_rhs, Functor.map_comp, F.map_comp]
    congr 1
    rw [initialChain_map_succ, initialChain_map_succ]
    rfl

end InitialChain

end CategoryTheory.Endofunctor
