/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module model_theory.ultraproducts
! leanprover-community/mathlib commit f1ae620609496a37534c2ab3640b641d5be8b6f0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.ModelTheory.Quotients
import Mathbin.Order.Filter.Germ
import Mathbin.Order.Filter.Ultrafilter

/-! # Ultraproducts and Łoś's Theorem

## Main Definitions
* `first_order.language.ultraproduct.Structure` is the ultraproduct structure on `filter.product`.

## Main Results
* Łoś's Theorem: `first_order.language.ultraproduct.sentence_realize`. An ultraproduct models a
sentence `φ` if and only if the set of structures in the product that model `φ` is in the
ultrafilter.

## Tags
ultraproduct, Los's theorem

-/


universe u v

variable {α : Type _} (M : α → Type _) (u : Ultrafilter α)

open FirstOrder Filter

open Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [∀ a, L.Structure (M a)]

namespace Ultraproduct

instance setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M) :=
  {
    (u : Filter α).productSetoid
      M with
    toStructure :=
      { funMap := fun n f x a => funMap f fun i => x i a
        rel_map := fun n r x => ∀ᶠ a : α in u, RelMap r fun i => x i a }
    fun_equiv := fun n f x y xy =>
      by
      refine' mem_of_superset (Inter_mem.2 xy) fun a ha => _
      simp only [Set.mem_interᵢ, Set.mem_setOf_eq] at ha
      simp only [Set.mem_setOf_eq, ha]
    rel_equiv := fun n r x y xy => by
      rw [← iff_eq_eq]
      refine' ⟨fun hx => _, fun hy => _⟩
      · refine' mem_of_superset (inter_mem hx (Inter_mem.2 xy)) _
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_interᵢ, Set.mem_setOf_eq] at *
        rw [← funext ha2]
        exact ha1
      · refine' mem_of_superset (inter_mem hy (Inter_mem.2 xy)) _
        rintro a ⟨ha1, ha2⟩
        simp only [Set.mem_interᵢ, Set.mem_setOf_eq] at *
        rw [funext ha2]
        exact ha1 }
#align first_order.language.ultraproduct.setoid_prestructure FirstOrder.Language.Ultraproduct.setoidPrestructure

variable {M} {u}

instance structure : L.Structure ((u : Filter α).product M) :=
  Language.quotientStructure
#align first_order.language.ultraproduct.Structure FirstOrder.Language.Ultraproduct.structure

theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ a, M a) :
    (funMap f fun i => (x i : (u : Filter α).product M)) = fun a => funMap f fun i => x i a := by
  apply fun_map_quotient_mk
#align first_order.language.ultraproduct.fun_map_cast FirstOrder.Language.Ultraproduct.funMap_cast

theorem term_realize_cast {β : Type _} (x : β → ∀ a, M a) (t : L.term β) :
    (t.realize fun i => (x i : (u : Filter α).product M)) = fun a => t.realize fun i => x i a :=
  by
  convert@term.realize_quotient_mk L _ ((u : Filter α).productSetoid M)
      (ultraproduct.setoid_prestructure M u) _ t x
  ext a
  induction t
  · rfl
  · simp only [term.realize, t_ih]
    rfl
#align first_order.language.ultraproduct.term_realize_cast FirstOrder.Language.Ultraproduct.term_realize_cast

variable [∀ a : α, Nonempty (M a)]

theorem boundedFormula_realize_cast {β : Type _} {n : ℕ} (φ : L.BoundedFormula β n)
    (x : β → ∀ a, M a) (v : Fin n → ∀ a, M a) :
    (φ.realize (fun i : β => (x i : (u : Filter α).product M)) fun i => v i) ↔
      ∀ᶠ a : α in u, φ.realize (fun i : β => x i a) fun i => v i a :=
  by
  letI := (u : Filter α).productSetoid M
  induction' φ with _ _ _ _ _ _ _ _ m _ _ ih ih' k φ ih
  · simp only [bounded_formula.realize, eventually_const]
  · have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [bounded_formula.realize, (Sum.comp_elim coe x v).symm, h2, term_realize_cast]
    exact Quotient.eq''
  · have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [bounded_formula.realize, (Sum.comp_elim coe x v).symm, term_realize_cast, h2]
    exact rel_map_quotient_mk _ _
  · simp only [bounded_formula.realize, ih v, ih' v]
    rw [Ultrafilter.eventually_imp]
  · simp only [bounded_formula.realize]
    trans
      ∀ m : ∀ a : α, M a,
        φ.realize (fun i : β => (x i : (u : Filter α).product M))
          (Fin.snoc (coe ∘ v) (↑m : (u : Filter α).product M))
    · exact forall_quotient_iff
    have h' :
      ∀ (m : ∀ a, M a) (a : α),
        (fun i : Fin (k + 1) => (Fin.snoc v m : _ → ∀ a, M a) i a) =
          Fin.snoc (fun i : Fin k => v i a) (m a) :=
      by
      refine' fun m a => funext (Fin.reverseInduction _ fun i hi => _)
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    simp only [← Fin.comp_snoc, ih, h']
    refine' ⟨fun h => _, fun h m => _⟩
    · contrapose! h
      simp_rw [← Ultrafilter.eventually_not, not_forall] at h
      refine'
        ⟨fun a : α =>
          Classical.epsilon fun m : M a =>
            ¬φ.realize (fun i => x i a) (Fin.snoc (fun i => v i a) m),
          _⟩
      rw [← Ultrafilter.eventually_not]
      exact Filter.mem_of_superset h fun a ha => Classical.epsilon_spec ha
    · rw [Filter.eventually_iff] at *
      exact Filter.mem_of_superset h fun a ha => ha (m a)
#align first_order.language.ultraproduct.bounded_formula_realize_cast FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast

theorem realize_formula_cast {β : Type _} (φ : L.Formula β) (x : β → ∀ a, M a) :
    (φ.realize fun i => (x i : (u : Filter α).product M)) ↔
      ∀ᶠ a : α in u, φ.realize fun i => x i a :=
  by
  simp_rw [formula.realize, ← bounded_formula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)
#align first_order.language.ultraproduct.realize_formula_cast FirstOrder.Language.Ultraproduct.realize_formula_cast

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Łoś's Theorem : A sentence is true in an ultraproduct if and only if the set of structures it is
  true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.Sentence) : (u : Filter α).product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ :=
  by
  simp_rw [sentence.realize, ← realize_formula_cast φ, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)
#align first_order.language.ultraproduct.sentence_realize FirstOrder.Language.Ultraproduct.sentence_realize

instance : Nonempty ((u : Filter α).product M) :=
  letI : ∀ a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  instNonempty

end Ultraproduct

end Language

end FirstOrder

