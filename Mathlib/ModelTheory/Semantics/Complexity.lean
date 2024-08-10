/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Semantics.Relabel
import Mathlib.ModelTheory.Syntax.Complexity

/-!
# Basics on First-Order Semantics
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

## Main Results

## Implementation Notes

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P] [Nonempty M]
variable {α : Type u'} {β : Type v'} {γ : Type*} {n : ℕ}

open FirstOrder Cardinal

open Structure Cardinal Fin

namespace BoundedFormula

theorem realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} :
    (φ.toPrenexImpRight ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  induction' hψ with _ _ hψ _ _ _hψ ih _ _ _hψ ih
  · rw [hψ.toPrenexImpRight]
  · refine _root_.trans (forall_congr' fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  · unfold toPrenexImpRight
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases h : φ.Realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩

theorem realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} : (φ.toPrenexImp ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  revert ψ
  induction' hφ with _ _ hφ _ _ _hφ ih _ _ _hφ ih <;> intro ψ hψ
  · rw [hφ.toPrenexImp]
    exact realize_toPrenexImpRight hφ hψ
  · unfold toPrenexImp
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hψ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ha (h a)
    · by_cases h : ψ.Realize v xs
      · inhabit M
        exact ⟨default, fun _h'' => h⟩
      · obtain ⟨a, ha⟩ := not_forall.1 (h ∘ h')
        exact ⟨a, fun h => (ha h).elim⟩
  · refine _root_.trans (forall_congr' fun _ => ih hψ.liftAt) ?_
    simp

@[simp]
theorem realize_toPrenex (φ : L.BoundedFormula α n) {v : α → M} :
    ∀ {xs : Fin n → M}, φ.toPrenex.Realize v xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ f1 f2 h1 h2 _ _ h
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · intros
    rw [toPrenex, realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex, realize_imp,
      realize_imp, h1, h2]
  · intros
    rw [realize_all, toPrenex, realize_all]
    exact forall_congr' fun a => h

end BoundedFormula

end Language

end FirstOrder
