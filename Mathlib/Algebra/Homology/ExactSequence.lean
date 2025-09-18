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
Liquid Tensor Experiment as a property of lists in `Arrow C`.

-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- The composable arrows associated to a short complex. -/
@[simps!]
def ShortComplex.toComposableArrows (S : ShortComplex C) : ComposableArrows C 2 :=
  ComposableArrows.mk₂ S.f S.g

/-- A map of short complexes induces a map of composable arrows with the same data. -/
def ShortComplex.mapToComposableArrows {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    S₁.toComposableArrows ⟶ S₂.toComposableArrows :=
  ComposableArrows.homMk₂ φ.τ₁ φ.τ₂ φ.τ₃ φ.comm₁₂.symm φ.comm₂₃.symm

@[simp]
theorem ShortComplex.mapToComposableArrows_app_0 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 0 = φ.τ₁ := rfl

@[simp]
theorem ShortComplex.mapToComposableArrows_app_1 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 1 = φ.τ₂ := rfl

@[simp]
theorem ShortComplex.mapToComposableArrows_app_2 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (ShortComplex.mapToComposableArrows φ).app 2 = φ.τ₃ := rfl

@[simp]
theorem ShortComplex.mapToComposableArrows_id {S₁ : ShortComplex C} :
    (ShortComplex.mapToComposableArrows (𝟙 S₁)) = 𝟙 S₁.toComposableArrows := by
  cat_disch

@[simp]
theorem ShortComplex.mapToComposableArrows_comp {S₁ S₂ S₃ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (ψ : S₂ ⟶ S₃) : ShortComplex.mapToComposableArrows (φ ≫ ψ) =
      ShortComplex.mapToComposableArrows φ ≫ ShortComplex.mapToComposableArrows ψ := by
  cat_disch

namespace ComposableArrows

variable {n : ℕ} (S : ComposableArrows C n)

/-- `F : ComposableArrows C n` is a complex if all compositions of
two consecutive arrows are zero. -/
structure IsComplex : Prop where
  /-- the composition of two consecutive arrows is zero -/
  zero (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

attribute [reassoc] IsComplex.zero

variable {S}

@[reassoc]
lemma IsComplex.zero' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
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
  zero i hi := by omega

variable (S)

/-- The short complex consisting of maps `S.map' i j` and `S.map' j k` when we know
that `S : ComposableArrows C n` satisfies `S.IsComplex`. -/
abbrev sc' (hS : S.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    ShortComplex C :=
  ShortComplex.mk (S.map' i j) (S.map' j k) (hS.zero' i j k)

/-- The short complex consisting of maps `S.map' i (i + 1)` and `S.map' (i + 1) (i + 2)`
when we know that `S : ComposableArrows C n` satisfies `S.IsComplex`. -/
abbrev sc (hS : S.IsComplex) (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    ShortComplex C :=
  S.sc' hS i (i + 1) (i + 2)

/-- `F : ComposableArrows C n` is exact if it is a complex and that all short
complexes consisting of two consecutive arrows are exact. -/
structure Exact : Prop extends S.IsComplex where
  exact (i : ℕ) (hi : i + 2 ≤ n := by omega) : (S.sc toIsComplex i).Exact

variable {S}

lemma Exact.exact' (hS : S.Exact) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    (S.sc' hS.toIsComplex i j k).Exact := by
  subst hij hjk
  exact hS.exact i hk

/-- Functoriality maps for `ComposableArrows.sc'`. -/
@[simps]
def sc'Map {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    S₁.sc' h₁ i j k ⟶ S₂.sc' h₂ i j k where
  τ₁ := φ.app _
  τ₂ := φ.app _
  τ₃ := φ.app _

/-- Functoriality maps for `ComposableArrows.sc`. -/
@[simps!]
def scMap {S₁ S₂ : ComposableArrows C n} (φ : S₁ ⟶ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    S₁.sc h₁ i ⟶ S₂.sc h₂ i :=
  sc'Map φ h₁ h₂ i (i + 1) (i + 2)

/-- The isomorphism `S₁.sc' _ i j k ≅ S₂.sc' _ i j k` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
def sc'MapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex) (i j k : ℕ) (hij : i + 1 = j := by omega)
    (hjk : j + 1 = k := by omega) (hk : k ≤ n := by omega) :
    S₁.sc' h₁ i j k ≅ S₂.sc' h₂ i j k where
  hom := sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

/-- The isomorphism `S₁.sc _ i ≅ S₂.sc _ i` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
def scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by omega) :
    S₁.sc h₁ i ≅ S₂.sc h₂ i where
  hom := scMap e.hom h₁ h₂ i
  inv := scMap e.inv h₂ h₁ i
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

lemma exact_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.Exact) :
    S₂.Exact where
  toIsComplex := isComplex_of_iso e h₁.toIsComplex
  exact i hi := ShortComplex.exact_of_iso (scMapIso e h₁.toIsComplex
    (isComplex_of_iso e h₁.toIsComplex) i) (h₁.exact i hi)

lemma exact_iff_of_iso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) :
    S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

lemma exact₀ (S : ComposableArrows C 0) : S.Exact where
  toIsComplex := S.isComplex₀
  exact i hi := by simp at hi

lemma exact₁ (S : ComposableArrows C 1) : S.Exact where
  toIsComplex := S.isComplex₁
  exact i hi := by exfalso; omega

lemma isComplex₂_iff (S : ComposableArrows C 2) :
    S.IsComplex ↔ S.map' 0 1 ≫ S.map' 1 2 = 0 := by
  constructor
  · intro h
    exact h.zero 0 (by omega)
  · intro h
    refine IsComplex.mk (fun i hi => ?_)
    obtain rfl : i = 0 := by omega
    exact h

lemma isComplex₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) :
    S.IsComplex :=
  S.isComplex₂_iff.2 w

lemma _root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows (S : ShortComplex C) :
    S.toComposableArrows.IsComplex :=
  -- Disable `Fin.reduceFinMk` because otherwise `Precompose.map_one_succ` does not apply. (https://github.com/leanprover-community/mathlib4/issues/27382)
  isComplex₂_mk _ (by simp [-Fin.reduceFinMk])

lemma exact₂_iff (S : ComposableArrows C 2) (hS : S.IsComplex) :
    S.Exact ↔ (S.sc' hS 0 1 2).Exact := by
  constructor
  · intro h
    exact h.exact 0 (by omega)
  · intro h
    refine Exact.mk hS (fun i hi => ?_)
    obtain rfl : i = 0 := by omega
    exact h

lemma exact₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
    (h : (ShortComplex.mk _ _ w).Exact) : S.Exact :=
  (S.exact₂_iff (S.isComplex₂_mk w)).2 h

lemma _root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows
    {S : ShortComplex C} (hS : S.Exact) :
    S.toComposableArrows.Exact :=
  exact₂_mk _ _ hS

lemma _root_.CategoryTheory.ShortComplex.exact_iff_exact_toComposableArrows
    (S : ShortComplex C) :
    S.Exact ↔ S.toComposableArrows.Exact :=
  (S.toComposableArrows.exact₂_iff S.isComplex_toComposableArrows).symm

lemma exact_iff_δ₀ (S : ComposableArrows C (n + 2)) :
    S.Exact ↔ (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact ∧ S.δ₀.Exact := by
  constructor
  · intro h
    constructor
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero 0
      exact h.exact 0 (by omega)
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero (i + 1)))
        (fun i hi => h.exact (i + 1))
  · rintro ⟨h, h₀⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · obtain _ | i := i
      · exact h.toIsComplex.zero 0
      · exact h₀.toIsComplex.zero i
    · obtain _ | i := i
      · exact h.exact 0
      · exact h₀.exact i

lemma Exact.δ₀ {S : ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δ₀.Exact := by
  rw [exact_iff_δ₀] at hS
  exact hS.2

/-- If `S : ComposableArrows C (n + 2)` is such that the first two arrows form
an exact sequence and that the tail `S.δ₀` is exact, then `S` is also exact.
See `ShortComplex.SnakeInput.snake_lemma` in `Algebra.Homology.ShortComplex.SnakeLemma`
for a use of this lemma. -/
lemma exact_of_δ₀ {S : ComposableArrows C (n + 2)}
    (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) : S.Exact := by
  rw [exact_iff_δ₀]
  constructor <;> assumption

lemma exact_iff_δlast {n : ℕ} (S : ComposableArrows C (n + 2)) :
    S.Exact ↔ S.δlast.Exact ∧ (mk₂ (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).Exact := by
  constructor
  · intro h
    constructor
    · exact Exact.mk (IsComplex.mk (fun i hi => h.toIsComplex.zero i))
        (fun i hi => h.exact i)
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero n
      exact h.exact n (by omega)
  · rintro ⟨h, h'⟩
    refine Exact.mk (IsComplex.mk (fun i hi => ?_)) (fun i hi => ?_)
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.toIsComplex.zero i
      · exact h'.toIsComplex.zero 0
    · simp only [Nat.add_le_add_iff_right] at hi
      obtain hi | rfl := hi.lt_or_eq
      · exact h.exact i
      · exact h'.exact 0

lemma Exact.δlast {S : ComposableArrows C (n + 2)} (hS : S.Exact) :
    S.δlast.Exact := by
  rw [exact_iff_δlast] at hS
  exact hS.1

lemma exact_of_δlast {n : ℕ} (S : ComposableArrows C (n + 2))
    (h₁ : S.δlast.Exact) (h₂ : (mk₂ (S.map' n (n + 1)) (S.map' (n + 1) (n + 2))).Exact) :
    S.Exact := by
  rw [exact_iff_δlast]
  constructor <;> assumption

lemma Exact.isIso_map' {C : Type*} [Category C] [Preadditive C]
    [Balanced C] {n : ℕ} {S : ComposableArrows C n} (hS : S.Exact) (k : ℕ) (hk : k + 3 ≤ n)
    (h₀ : S.map' k (k + 1) = 0) (h₁ : S.map' (k + 2) (k + 3) = 0) :
    IsIso (S.map' (k + 1) (k + 2)) := by
  have := (hS.exact k).mono_g h₀
  have := (hS.exact (k + 1)).epi_f h₁
  apply isIso_of_mono_of_epi

end ComposableArrows

end CategoryTheory
