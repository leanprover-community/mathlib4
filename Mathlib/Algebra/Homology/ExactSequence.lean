/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.ComposableArrows

/-!
# Exact sequences

When `S : ComposableArrows C n` (i.e. `S : Fin (n + 1) ⥤ C`, which we may
consider as a sequence of `n` composable arrows `S.map' i (i + 1)` in a category `C`
for `0 ≤ i < n` ), we shall say that it is exact (`S.Exact`) if the composition
of two consecutive arrows are zero (`S.IsComplex`) and that the diagram is
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
  zero (i : ℕ) (hi : i + 2 ≤ n := by linarith) :
    S.map' i (i + 1) ≫ S.map' (i + 1) (i + 2) = 0

variable {S}

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
complex consisting of two consecutive arrows are exact. -/
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
def sc'MapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i j k : ℕ) (hij : i + 1 = j := by linarith)
    (hjk : j + 1 = k := by linarith) (hk : k ≤ n := by linarith) :
    S₁.sc' h₁ i j k ≅ S₂.sc' h₂ i j k where
  hom := sc'Map e.hom h₁ h₂ i j k
  inv := sc'Map e.inv h₂ h₁ i j k
  hom_inv_id := by ext <;> dsimp <;> simp
  inv_hom_id := by ext <;> dsimp <;> simp

/-- The isomorphism `S₁.sc _ i ≅ S₂.sc _ i` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
def scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂) (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
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

lemma exact₀ (S : ComposableArrows C 0) : S.Exact where
  toIsComplex := S.isComplex₀
  exact i hi := by simp at hi

lemma exact₁ (S : ComposableArrows C 1) : S.Exact where
  toIsComplex := S.isComplex₁
  exact i hi := by exfalso; linarith

lemma isComplex₂_iff (S : ComposableArrows C 2) :
    S.IsComplex ↔ S.map' 0 1 ≫ S.map' 1 2 = 0 := by
  constructor
  · intro h
    exact h.zero 0 (by linarith)
  · intro h
    refine' IsComplex.mk (fun i hi => _)
    obtain rfl : i = 0 := by linarith
    exact h

lemma isComplex₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0) :
    S.IsComplex :=
  S.isComplex₂_iff.2 w

lemma _root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows (S : ShortComplex C) :
    S.toComposableArrows.IsComplex :=
  isComplex₂_mk _ (by simp)

lemma exact₂_iff (S : ComposableArrows C 2) (hS : S.IsComplex) :
    S.Exact ↔ (S.sc' hS 0 1 2).Exact := by
  constructor
  · intro h
    exact h.exact 0 (by linarith)
  · intro h
    refine' Exact.mk hS (fun i hi => _)
    obtain rfl : i = 0 := by linarith
    exact h

lemma exact₂_mk (S : ComposableArrows C 2) (w : S.map' 0 1 ≫ S.map' 1 2 = 0)
    (h : (ShortComplex.mk _ _ w).Exact) : S.Exact :=
  (S.exact₂_iff (S.isComplex₂_mk w)).2 h

lemma _root_.CategoryTheory.ShortComplex.Exact.exact_toComposableArrows
    {S : ShortComplex C} (hS : S.Exact) :
    S.toComposableArrows.Exact :=
  exact₂_mk _ _ hS

lemma exact_iff_δ₀ (S : ComposableArrows C (n + 2)) :
    S.Exact ↔ (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact ∧ S.δ₀.Exact := by
  constructor
  · intro h
    constructor
    · rw [exact₂_iff]; swap
      · rw [isComplex₂_iff]
        exact h.toIsComplex.zero 0
      exact h.exact 0 (by linarith)
    · refine' Exact.mk (IsComplex.mk (fun i hi => _)) (fun i hi => _)
      · exact h.toIsComplex.zero (i + 1)
      · exact h.exact (i + 1)
  · rintro ⟨h, h₀⟩
    refine' Exact.mk (IsComplex.mk (fun i hi => _)) (fun i hi => _)
    · obtain _ | i := i
      · exact h.toIsComplex.zero 0
      · exact h₀.toIsComplex.zero i
    · obtain _ | i := i
      · exact h.exact 0
      · exact h₀.exact i

lemma exact_of_δ₀ {S : ComposableArrows C (n + 2)}
    (h : (mk₂ (S.map' 0 1) (S.map' 1 2)).Exact) (h₀ : S.δ₀.Exact) : S.Exact := by
  rw [exact_iff_δ₀]
  constructor <;> assumption

section

variable {X₀ X₁ X₂ X₃ X₄ X₅ : C} {f₁ : X₀ ⟶ X₁} {f₂ : X₁ ⟶ X₂}
  {f₃ : X₂ ⟶ X₃} {f₄ : X₃ ⟶ X₄} {f₅ : X₄ ⟶ X₅}
  {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0} {w₃ : f₃ ≫ f₄ = 0} {w₄ : f₄ ≫ f₅ = 0}
  (ex₁ : (ShortComplex.mk _ _ w₁).Exact)
  (ex₂ : (ShortComplex.mk _ _ w₂).Exact)
  (ex₃ : (ShortComplex.mk _ _ w₃).Exact)
  (ex₄ : (ShortComplex.mk _ _ w₄).Exact)

example : (((mk₃ f₃ f₄ f₅).precomp f₂).precomp f₁).Exact :=
  exact_of_δ₀ (exact₂_mk _ _ ex₁) (exact_of_δ₀ (exact₂_mk _ _ ex₂)
    (exact_of_δ₀ (exact₂_mk _ _ ex₃) ((exact₂_mk _ _ ex₄))))

end

end ComposableArrows

end CategoryTheory
