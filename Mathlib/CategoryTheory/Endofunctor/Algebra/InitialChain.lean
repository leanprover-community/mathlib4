/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Iterated endofunctors and chains from a seed morphism

Given an endofunctor `F : C ⥤ C` and a seed morphism `α : X ⟶ F.obj X`, we define
the iterated morphism `iterateMap α n : F^n(X) ⟶ F^{n+1}(X)` and the functor
`chainMk α : ℕ ⥤ C` sending `n` to `F^n(X)` with successor maps given by `iterateMap α`.

The *initial chain* `⊥ → F(⊥) → F²(⊥) → ⋯` is the special case `X = ⊥_ C` with
`α = initial.to _`, and is provided as `initialChain F`.

## Main definitions

- `CategoryTheory.Functor.iterate F n` : the `n`-th iterate `F^n : C ⥤ C`
- `CategoryTheory.Endofunctor.iterateMap α n` : the `n`-th iterated morphism from a seed
- `CategoryTheory.Endofunctor.chainMk α` : the chain functor `ℕ ⥤ C` from a seed
- `CategoryTheory.Endofunctor.initialChain F` : the initial chain, specialization of `chainMk`

## Main results

- `CategoryTheory.Endofunctor.chainMk_map_succ` : successor maps are `iterateMap α`
- `CategoryTheory.Endofunctor.chainMk_map_succ_eq` : the chain map at successor indices
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

section ChainMk

variable {F : C ⥤ C} {X : C} (α : X ⟶ F.obj X)

/-- The `n`-th iterated morphism `F^n(X) ⟶ F^{n+1}(X)`, defined from the seed
`α : X ⟶ F.obj X` by iteratively applying `F`. -/
def iterateMap : ∀ (n : ℕ), (F.iterate n).obj X ⟶ (F.iterate (n + 1)).obj X
  | 0 => α
  | n + 1 => F.map (iterateMap n)

/-- The chain `X → F(X) → F²(X) → ⋯` as a functor `ℕ ⥤ C`, constructed from a seed
morphism `α : X ⟶ F.obj X`. -/
def chainMk : ℕ ⥤ C :=
  Functor.ofSequence (X := fun n => (F.iterate n).obj X) (iterateMap α)

@[simp]
lemma chainMk_obj (n : ℕ) : (chainMk α).obj n = (F.iterate n).obj X := rfl

@[simp]
lemma chainMk_map_succ (n : ℕ) :
    (chainMk α).map (homOfLE (Nat.le_add_right n 1)) = iterateMap α n :=
  Functor.ofSequence_map_homOfLE_succ (iterateMap α) n

/-- The chain map at successor indices equals `F` applied to the chain map.
This is the key structural property: the `(m+1)`-to-`(n+1)` map in the chain
is `F` applied to the `m`-to-`n` map. -/
lemma chainMk_map_succ_eq {m n : ℕ} (h : m ≤ n) :
    (chainMk α).map (homOfLE (Nat.succ_le_succ h)) =
    F.map ((chainMk α).map (homOfLE h)) := by
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
    rw [chainMk_map_succ, chainMk_map_succ]
    rfl

end ChainMk

section InitialChain

variable (F : C ⥤ C) [HasInitial C]

/-- The initial chain `⊥ → F(⊥) → F²(⊥) → ⋯` as a functor `ℕ ⥤ C`,
obtained by specializing `chainMk` to the seed map `initial.to (F.obj (⊥_ C))`. -/
noncomputable def initialChain : ℕ ⥤ C :=
  chainMk (initial.to (F.obj (⊥_ C)))

@[simp]
lemma initialChain_obj (n : ℕ) :
    (initialChain F).obj n = (F.iterate n).obj (⊥_ C) := rfl

@[simp]
lemma initialChain_map_succ (n : ℕ) :
    (initialChain F).map (homOfLE (Nat.le_add_right n 1)) =
    iterateMap (initial.to (F.obj (⊥_ C))) n :=
  chainMk_map_succ _ n

lemma initialChain_map_succ_eq {m n : ℕ} (h : m ≤ n) :
    (initialChain F).map (homOfLE (Nat.succ_le_succ h)) =
    F.map ((initialChain F).map (homOfLE h)) :=
  chainMk_map_succ_eq _ h

end InitialChain

end CategoryTheory.Endofunctor
