/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Quotients
import Mathlib.Order.Filter.Germ
import Mathlib.Order.Filter.Ultrafilter

#align_import model_theory.ultraproducts from "leanprover-community/mathlib"@"f1ae620609496a37534c2ab3640b641d5be8b6f0"

/-! # Ultraproducts and Łoś's Theorem

## Main Definitions
* `FirstOrder.Language.Ultraproduct.Structure` is the ultraproduct structure on `Filter.Product`.

## Main Results
* Łoś's Theorem: `FirstOrder.Language.Ultraproduct.sentence_realize`. An ultraproduct models a
sentence `φ` if and only if the set of structures in the product that model `φ` is in the
ultrafilter.

## Tags
ultraproduct, Los's theorem

-/


universe u v

variable {α : Type*} (M : α → Type*) (u : Ultrafilter α)

open FirstOrder Filter

open Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [∀ a, L.Structure (M a)]

namespace Ultraproduct

instance setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M) :=
  { (u : Filter α).productSetoid M with
    toStructure :=
      { funMap := fun {n} f x a => funMap f fun i => x i a
        RelMap := fun {n} r x => ∀ᶠ a : α in u, RelMap r fun i => x i a }
    fun_equiv := fun {n} f x y xy => by
      refine' mem_of_superset (iInter_mem.2 xy) fun a ha => _
      -- ⊢ a ∈ {x_1 | (fun a => funMap f x a = funMap f y a) x_1}
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at ha
      -- ⊢ a ∈ {x_1 | (fun a => funMap f x a = funMap f y a) x_1}
      simp only [Set.mem_setOf_eq, ha]
      -- 🎉 no goals
    rel_equiv := fun {n} r x y xy => by
      rw [← iff_eq_eq]
      -- ⊢ RelMap r x ↔ RelMap r y
      refine' ⟨fun hx => _, fun hy => _⟩
      -- ⊢ RelMap r y
      · refine' mem_of_superset (inter_mem hx (iInter_mem.2 xy)) _
        -- ⊢ {x_1 | (fun a => RelMap r fun i => x i a) x_1} ∩ ⋂ (i : Fin n), {x_1 | (fun  …
        rintro a ⟨ha1, ha2⟩
        -- ⊢ a ∈ {x | (fun a => RelMap r fun i => y i a) x}
        simp only [Set.mem_iInter, Set.mem_setOf_eq] at *
        -- ⊢ RelMap r fun i => y i a
        rw [← funext ha2]
        -- ⊢ RelMap r fun x_1 => x x_1 a
        exact ha1
        -- 🎉 no goals
      · refine' mem_of_superset (inter_mem hy (iInter_mem.2 xy)) _
        -- ⊢ {x | (fun a => RelMap r fun i => y i a) x} ∩ ⋂ (i : Fin n), {x_1 | (fun a => …
        rintro a ⟨ha1, ha2⟩
        -- ⊢ a ∈ {x_1 | (fun a => RelMap r fun i => x i a) x_1}
        simp only [Set.mem_iInter, Set.mem_setOf_eq] at *
        -- ⊢ RelMap r fun i => x i a
        rw [funext ha2]
        -- ⊢ RelMap r fun x => y x a
        exact ha1 }
        -- 🎉 no goals
#align first_order.language.ultraproduct.setoid_prestructure FirstOrder.Language.Ultraproduct.setoidPrestructure

variable {M} {u}

instance «structure» : L.Structure ((u : Filter α).Product M) :=
  Language.quotientStructure
set_option linter.uppercaseLean3 false in
#align first_order.language.ultraproduct.Structure FirstOrder.Language.Ultraproduct.structure

theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ a, M a) :
    (funMap f fun i => (x i : (u : Filter α).Product M)) =
      (fun a => funMap f fun i => x i a : (u : Filter α).Product M) := by
  apply funMap_quotient_mk'
  -- 🎉 no goals
#align first_order.language.ultraproduct.fun_map_cast FirstOrder.Language.Ultraproduct.funMap_cast

theorem term_realize_cast {β : Type*} (x : β → ∀ a, M a) (t : L.Term β) :
    (t.realize fun i => (x i : (u : Filter α).Product M)) =
      (fun a => t.realize fun i => x i a : (u : Filter α).Product M) := by
  convert @Term.realize_quotient_mk' L _ ((u : Filter α).productSetoid M)
      (Ultraproduct.setoidPrestructure M u) _ t x using 2
  ext a
  -- ⊢ Term.realize (fun i => x i a) t = Term.realize x t a
  induction t
  -- ⊢ Term.realize (fun i => x i a) (var _a✝) = Term.realize x (var _a✝) a
  case var =>
    rfl
  case func _ _ _ t_ih =>
    simp only [Term.realize, t_ih]
    rfl
#align first_order.language.ultraproduct.term_realize_cast FirstOrder.Language.Ultraproduct.term_realize_cast

variable [∀ a : α, Nonempty (M a)]

theorem boundedFormula_realize_cast {β : Type*} {n : ℕ} (φ : L.BoundedFormula β n)
    (x : β → ∀ a, M a) (v : Fin n → ∀ a, M a) :
    (φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (fun i => (v i : (u : Filter α).Product M))) ↔
      ∀ᶠ a : α in u, φ.Realize (fun i : β => x i a) fun i => v i a := by
  letI := (u : Filter α).productSetoid M
  -- ⊢ (BoundedFormula.Realize φ (fun i => Quotient.mk' (x i)) fun i => Quotient.mk …
  induction' φ with _ _ _ _ _ _ _ _ m _ _ ih ih' k φ ih
  · simp only [BoundedFormula.Realize, eventually_const]
    -- 🎉 no goals
  · have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2, term_realize_cast]
    -- ⊢ Term.realize (Sum.elim (fun i => Quotient.mk' (x i)) fun i => Quotient.mk' ( …
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm,
      term_realize_cast, term_realize_cast]
    exact Quotient.eq''
    -- 🎉 no goals
  · have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    -- ⊢ (RelMap R✝ fun i => Term.realize (Sum.elim (fun i => Quotient.mk' (x i)) fun …
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm]
    -- ⊢ (RelMap R✝ fun i => Term.realize (Quotient.mk' ∘ Sum.elim x v) (ts✝ i)) ↔ ∀ᶠ …
    conv_lhs => enter [2, i]; erw [term_realize_cast]
    -- ⊢ (RelMap R✝ fun i => Quotient.mk' fun a => Term.realize (fun i => Sum.elim x  …
    apply relMap_quotient_mk'
    -- 🎉 no goals
  · simp only [BoundedFormula.Realize, ih v, ih' v]
    -- ⊢ ((∀ᶠ (a : α) in ↑u, BoundedFormula.Realize f₁✝ (fun i => x i a) fun i => v i …
    rw [Ultrafilter.eventually_imp]
    -- 🎉 no goals
  · simp only [BoundedFormula.Realize]
    -- ⊢ (∀ (x_1 : Quotient (productSetoid ↑u fun a => M a)), BoundedFormula.Realize  …
    apply Iff.trans (b := ∀ m : ∀ a : α, M a,
      φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (Fin.snoc (((↑) : (∀ a, M a) → (u : Filter α).Product M) ∘ v)
          (m : (u : Filter α).Product M)))
    · exact forall_quotient_iff
      -- 🎉 no goals
    have h' :
      ∀ (m : ∀ a, M a) (a : α),
        (fun i : Fin (k + 1) => (Fin.snoc v m : _ → ∀ a, M a) i a) =
          Fin.snoc (fun i : Fin k => v i a) (m a) := by
      refine' fun m a => funext (Fin.reverseInduction _ fun i _ => _)
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    simp only [← Fin.comp_snoc]
    -- ⊢ (∀ (m : (a : α) → M a), BoundedFormula.Realize φ (fun i => Quotient.mk' (x i …
    simp only [Function.comp, ih, h']
    -- ⊢ (∀ (m : (a : α) → M a), ∀ᶠ (a : α) in ↑u, BoundedFormula.Realize φ (fun i => …
    refine' ⟨fun h => _, fun h m => _⟩
    -- ⊢ ∀ᶠ (a : α) in ↑u, ∀ (x_1 : M a), BoundedFormula.Realize φ (fun i => x i a) ( …
    · contrapose! h
      -- ⊢ ∃ m, ¬∀ᶠ (a : α) in ↑u, BoundedFormula.Realize φ (fun i => x i a) (Fin.snoc  …
      simp_rw [← Ultrafilter.eventually_not, not_forall] at h
      -- ⊢ ∃ m, ¬∀ᶠ (a : α) in ↑u, BoundedFormula.Realize φ (fun i => x i a) (Fin.snoc  …
      refine'
        ⟨fun a : α =>
          Classical.epsilon fun m : M a =>
            ¬φ.Realize (fun i => x i a) (Fin.snoc (fun i => v i a) m),
          _⟩
      rw [← Ultrafilter.eventually_not]
      -- ⊢ ∀ᶠ (x_1 : α) in ↑u, ¬BoundedFormula.Realize φ (fun i => x i x_1) (Fin.snoc ( …
      exact Filter.mem_of_superset h fun a ha => Classical.epsilon_spec ha
      -- 🎉 no goals
    · rw [Filter.eventually_iff] at *
      -- ⊢ {x_1 | BoundedFormula.Realize φ (fun i => x i x_1) (Fin.snoc (fun i => v i x …
      exact Filter.mem_of_superset h fun a ha => ha (m a)
      -- 🎉 no goals
#align first_order.language.ultraproduct.bounded_formula_realize_cast FirstOrder.Language.Ultraproduct.boundedFormula_realize_cast

theorem realize_formula_cast {β : Type*} (φ : L.Formula β) (x : β → ∀ a, M a) :
    (φ.Realize fun i => (x i : (u : Filter α).Product M)) ↔
      ∀ᶠ a : α in u, φ.Realize fun i => x i a := by
  simp_rw [Formula.Realize, ← boundedFormula_realize_cast φ x, iff_eq_eq]
  -- ⊢ BoundedFormula.Realize φ (fun i => Quotient.mk' (x i)) default = BoundedForm …
  exact congr rfl (Subsingleton.elim _ _)
  -- 🎉 no goals
#align first_order.language.ultraproduct.realize_formula_cast FirstOrder.Language.Ultraproduct.realize_formula_cast

/-- Łoś's Theorem : A sentence is true in an ultraproduct if and only if the set of structures it is
  true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ := by
  simp_rw [Sentence.Realize]
  -- ⊢ Formula.Realize φ default ↔ ∀ᶠ (a : α) in ↑u, Formula.Realize φ default
  erw [← realize_formula_cast φ, iff_eq_eq]
  -- ⊢ Formula.Realize φ default = Formula.Realize φ fun i => Quotient.mk' fun a => …
  exact congr rfl (Subsingleton.elim _ _)
  -- 🎉 no goals
#align first_order.language.ultraproduct.sentence_realize FirstOrder.Language.Ultraproduct.sentence_realize

nonrec instance Product.instNonempty : Nonempty ((u : Filter α).Product M) :=
  letI : ∀ a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  instNonempty
#align first_order.language.ultraproduct.product.nonempty FirstOrder.Language.Ultraproduct.Product.instNonempty

end Ultraproduct

end Language

end FirstOrder
