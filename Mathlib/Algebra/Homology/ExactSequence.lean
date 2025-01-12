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
  -- See https://github.com/leanprover/lean4/issues/2862
  -- Without `decide := true`, simp gets stuck at `hi : autoParam False _auto✝`
  zero i hi := by simp +decide at hi

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
structure Exact extends S.IsComplex : Prop where
  exact (i : ℕ) (hi : i + 2 ≤ n := by omega) : (S.sc toIsComplex i).Exact

variable {S}

lemma Exact.exact_truncation (hex : S.Exact) (i : ℕ) (h : i ≤ n) :
    Exact (Monotone.functor (f := Fin.castLE (n := i + 1) (m := n + 1) (by simp [h]))
    (fun ⦃a b⦄ h ↦ h) ⋙ S) :=
  Exact.mk (IsComplex.mk (fun i hi => hex.toIsComplex.zero i)) (fun i hi => hex.exact i)

variable (S)

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
  hom_inv_id := by ext <;> dsimp <;> simp
  inv_hom_id := by ext <;> dsimp <;> simp

/-- The isomorphism `S₁.sc _ i ≅ S₂.sc _ i` induced by an isomorphism `S₁ ≅ S₂`
in `ComposableArrows C n`. -/
@[simps]
def scMapIso {S₁ S₂ : ComposableArrows C n} (e : S₁ ≅ S₂)
    (h₁ : S₁.IsComplex) (h₂ : S₂.IsComplex)
    (i : ℕ) (hi : i + 2 ≤ n := by omega) :
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
  -- See https://github.com/leanprover/lean4/issues/2862
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

#adaptation_note /-- nightly-2024-03-11
We turn off simprocs here.
Ideally someone will investigate whether `simp` lemmas can be rearranged
so that this works without the `set_option`,
*or* come up with a proposal regarding finer control of disabling simprocs. -/
set_option simprocs false in
lemma _root_.CategoryTheory.ShortComplex.isComplex_toComposableArrows (S : ShortComplex C) :
    S.toComposableArrows.IsComplex :=
  isComplex₂_mk _ (by simp)

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



universe u v

variable {D : Type u} [Category.{v,u} D] [HasZeroMorphisms D] (F : C ⥤ D)
  [F.PreservesZeroMorphisms]

/-- The image of a complex by a functor preserving zero morphisms is a complex.-/
def IsComplex.comp_complex (S : ComposableArrows C n) (hS : S.IsComplex) :
    ComposableArrows.IsComplex (S ⋙ F) := by
  refine IsComplex.mk (fun i hi ↦ ?_)
  change F.map _ ≫ F.map _ = 0
  rw [← F.map_comp, hS.zero i hi, F.map_zero]

/-- For every `S : ComposableArrows C n`, every functor `F : C ⥤ F` and every `i` such that
`i + 2 ≤ n`, the image of the shoft complex `S.sc i` by `F` is isomorphic to `(S ⋙ F).sc i`.-/
def IsComplex.map_sc_iso_sc_comp (S : ComposableArrows C n) (hS : S.IsComplex) (i : ℕ)
    (hi : i + 2 ≤ n := by omega) :
    (S.sc hS i hi).map F ≅ ComposableArrows.sc (S ⋙ F) (hS.comp_complex F) i hi :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- The image of an exact sequence by an exact functor is exact.-/
def Exact.comp_exact [F.PreservesHomology]
    (S : ComposableArrows C n) (hex : S.Exact) : ComposableArrows.Exact (S ⋙ F) := by
  refine Exact.mk (hex.toIsComplex.comp_complex F) (fun i hi ↦ ?_)
  rw [← ShortComplex.exact_iff_of_iso (hex.toIsComplex.map_sc_iso_sc_comp F S i hi)]
  exact (hex.exact i hi).map F

/-- If `S : ComposableArrows C n` and `F : C ⥤ D` is a faithful functor (preserving
zero morphisms) such that `S ⋙ F` is a complex, then `S` is a complex.-/
def isComplex_of_comp_complex [F.Faithful] (S : ComposableArrows C n)
    (hS : ComposableArrows.IsComplex (S ⋙ F)) : S.IsComplex := by
  refine IsComplex.mk (fun i hi ↦ ?_)
  apply F.map_injective
  rw [F.map_zero, F.map_comp]
  exact hS.zero i hi

/-- If `S : ComposableArrows C n` and `F : C ⥤ D` is an exact faithful functor
such that `S ⋙ F` is exact, then `S` is exact. This also assume that `S` has homology
in every degree.-/
def Exact.exact_of_comp_exact [F.Faithful] [F.PreservesHomology]
    (S : ComposableArrows C n) (hex : ComposableArrows.Exact (S ⋙ F))
    [∀ i (hi : i + 2 ≤ n := by omega),
    (S.sc (isComplex_of_comp_complex F _ hex.toIsComplex) i hi).HasHomology] : S.Exact := by
  refine Exact.mk (isComplex_of_comp_complex F _ hex.toIsComplex) (fun i hi ↦ ?_)
  rw [← ShortComplex.exact_map_iff_of_faithful _ F, ShortComplex.exact_iff_of_iso
    (((isComplex_of_comp_complex F _ hex.toIsComplex)).map_sc_iso_sc_comp F S i hi)]
  exact hex.exact i hi

end ComposableArrows

end CategoryTheory
