/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.ComposableArrows

/-!
# Exact sequences

A sequence of `n` composable arrows `S : ComposableArrows C` (i.e. a functor
`S : Fin (n + 1) ⥤ C`) is said to be exact (`S.Exact`) if the composition
of two consecutive arrows are zero (`S.IsComplex`) and the diagram is
exact at each `i` for `1 ≤ i < n`.

Together with the inductive construction of composable arrows
`ComposableArrows.precomp`, this is useful in order to state that certain
finite sequences of morphisms are exact (e.g the snake lemma), even though
in the applications it would usually be more convenient to use individual
lemmas expressing the exactness at a particular object.

This implementation is a refactor of `exact_seq` with appeared in the
Liquid Tensor Experiement as a property of lists in `Arrow C`.

-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- The composable arrows associated to a short complex. -/
@[simps!]
def ShortComplex.toComposableArrows (S : ShortComplex C) : ComposableArrows C 2 :=
  ComposableArrows.mk₂ S.f S.g

namespace ComposableArrows

variable {n : ℕ} (S : ComposableArrows C n)

/-- `F : ComposableArrows C n` is a complex if all compositions of
two consecutive arrows are zero. -/
structure IsComplex : Prop where
  /-- the composition of two consecutive arrows is zero -/
  zero (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

attribute [reassoc] IsComplex.zero

variable {S}

@[reassoc]
lemma IsComplex.zero' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    S.map' i j ≫ S.map' j k = 0 := by
  subst hij hjk
  exact hS.zero i hk

lemma isComplex_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) :
    S₂.IsComplex where
  zero i hi := by
    rw [← cancel_epi (ComposableArrows.app' e.hom i), comp_zero,
      ← NatTrans.naturality_assoc, ← NatTrans.naturality,
      reassoc_of% (h₁.zero i hi), zero_comp]

lemma isComplex_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.IsComplex ↔ S₂.IsComplex :=
  ⟨isComplex_of_iso e, isComplex_of_iso e.symm⟩

lemma isComplex₀ (S : ComposableArrows C 0) : S.IsComplex where
  zero i hi := by simp at hi

lemma isComplex₁ (S : ComposableArrows C 1) : S.IsComplex where
  zero i hi := by exfalso; linarith

variable (S)

/-- The short complex consisting of maps `S.map' i j` and `S.map' j k` when we know
that `S : ComposableArrows C n` satisfies `S.IsComplex`. -/
@[simps!]
def sc' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    ShortComplex C :=
  ShortComplex.mk (S.map' i j) (S.map' j k) (hS.zero' i j k)

/-- The short complex consisting of maps `S.map' i (i + 1)` and `S.map' (i + 1) (i + 2)`
when we know that `S : ComposableArrows C n` satisfies `S.IsComplex`. -/
abbrev sc (hS : S.IsComplex) (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    ShortComplex C :=
    S.sc' hS i (i + 1) (i + 2)

/-- `F : ComposableArrows C n` is exact if it is a complex and that all short
complexes consisting of two consecutive arrows are exact. -/
structure Exact extends S.IsComplex : Prop where
  exact (i : ℕ) (hi : i + 2 ≤ n := by linarith) : (S.sc toIsComplex i).Exact

variable {S}

lemma IsExact.exact' (hS : S.Exact) (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    (S.sc' hS.toIsComplex i j k).Exact := by
  subst hij hjk
  exact hS.exact i hk

/-- Functoriality maps for `ComposableArrows.sc'`. -/
@[simps]
def sc'Map {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    S₁.sc' h₁ i j k ⟶ S₂.sc' h₂ i j k where
  τ₁ := φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _

/-- Functoriality maps for `ComposableArrows.sc`. -/
@[simps!]
def scMap {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    S₁.sc h₁ i ⟶ S₂.sc h₂ i :=
  sc'Map φ h₁ h₂ i (i + 1) (i + 2)

/-- The isomorphism `S₁.sc' _ i j k ≅ S₂.sc' _ i j k` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
def sc'MapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    S₁.sc' h₁ i j k ≅ S₂.sc' h₂ i j k where
  hom := sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> dsimp <;> simp
  inv_hom_id := by ext <;> dsimp <;> simp

/-- The isomorphism `S₁.sc _ i ≅ S₂.sc _ i` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
def scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    S₁.sc h₁ i ≅ S₂.sc h₂ i where
  hom := scMap e.hom h₁ h₂ i
  inv := scMap e.inv h₂ h₁ i
  hom_inv_id := by ext <;> dsimp <;> simp
  inv_hom_id := by ext <;> dsimp <;> simp

lemma exact_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) :
    S₂.Exact where
  toIsComplex := isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (scMapIso e h₁.toIsComplex
    (isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)

lemma exact_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

end ComposableArrows

end CategoryTheory
