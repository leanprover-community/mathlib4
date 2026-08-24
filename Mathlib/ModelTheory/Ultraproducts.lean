/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Quotients
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Defs

import all Mathlib.Order.Filter.Germ.Basic

/-!
# Ultraproducts and Łoś's Theorem

## Main Definitions

- `FirstOrder.Language.Ultraproduct.Structure` is the ultraproduct structure on `Filter.Product`.

## Main Results

- Łoś's Theorem: `FirstOrder.Language.Ultraproduct.sentence_realize`. An ultraproduct models a
  sentence `φ` if and only if the set of structures in the product that model `φ` is in the
  ultrafilter.

## Tags

ultraproduct, Los's theorem
-/

public section

universe u v

variable {α : Type*} (M : α → Type*) (u : Ultrafilter α)

open FirstOrder Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [∀ a, L.Structure (M a)]

namespace Ultraproduct

private instance setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M) where
  toStructure.funMap {_} f x :=
    ⟨⟨⋂ i, (x i).1.1, iInter_mem.2 fun i => (x i).1.2⟩,
      fun a => funMap f fun i => (x i).2 ⟨a.1, Set.mem_iInter.1 a.2 i⟩⟩
  toStructure.RelMap {_} r x := ∀ᶠ a : α in u,
    ∀ h : ∀ i, a ∈ (x i).1.1, RelMap (M := M a) r fun i => (x i).2 ⟨a, h i⟩
  fun_equiv {_} f _ _ hxy :=
    mem_of_superset (iInter_mem.2 hxy) fun _ ha hx hy =>
      congrArg (funMap f) (funext fun i =>
        Set.mem_iInter.1 ha i (Set.mem_iInter.1 hx i) (Set.mem_iInter.1 hy i))
  rel_equiv {_} r x y hxy := propext <| eventually_congr <|
    mem_of_superset (inter_mem (iInter_mem.2 hxy) (inter_mem
      (iInter_mem.2 fun i => (x i).1.2) (iInter_mem.2 fun i => (y i).1.2))) fun _ ha =>
        (forall_prop_of_true (Set.mem_iInter.1 ha.2.1)).trans
          ((forall_prop_of_true (Set.mem_iInter.1 ha.2.2)).trans
            (Eq.to_iff (congrArg (RelMap r) (funext fun i => Set.mem_iInter.1 ha.1 i
              (Set.mem_iInter.1 ha.2.1 i) (Set.mem_iInter.1 ha.2.2 i)))).symm).symm

variable {M} {u}

@[no_expose]
instance «structure» : L.Structure ((u : Filter α).Product M) :=
  inferInstanceAs <| L.Structure (Quotient _)

theorem funMap_ofPartialFun {n : ℕ} (f : L.Functions n)
    {s : Set α} (hs : s ∈ (u : Filter α)) (x : Fin n → ∀ a ∈ s, M a) :
    (funMap f fun i => Product.ofPartialFun s hs (x i)) =
      Product.ofPartialFun s hs fun a ha => funMap f fun i => x i a ha := by
  unfold Product.ofPartialFun
  refine (funMap_quotient_mk' _ f _).trans (Quotient.sound ?_)
  exact .of_forall fun _ _ _ => rfl

theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ a, M a) :
    (funMap f fun i => (x i : (u : Filter α).Product M)) =
      (fun a => funMap f fun i => x i a : (u : Filter α).Product M) :=
  funMap_ofPartialFun f Filter.univ_mem fun i a _ => x i a

theorem relMap_ofPartialFun {n : ℕ} (f : L.Relations n)
    {s : Set α} (hs : s ∈ (u : Filter α)) (x : Fin n → ∀ a ∈ s, M a) :
    (RelMap f fun i => Product.ofPartialFun s hs (x i)) ↔
      ∀ᶠ a in (u : Filter α), ∀ h : a ∈ s, RelMap f fun i => x i a h := by
  unfold Product.ofPartialFun
  refine (relMap_quotient_mk' _ f _).trans (Filter.eventually_congr ?_)
  refine (Filter.eventually_mem_set.2 hs).mono fun a ha => ?_
  rw [forall_prop_of_true (fun i => ha), forall_prop_of_true ha]

theorem termRealize_ofPartialFun {β : Type*}
    {s : Set α} (hs : s ∈ (u : Filter α)) (x : β → ∀ a ∈ s, M a) (t : L.Term β) :
    (t.realize fun i => Product.ofPartialFun s hs (x i)) =
      Product.ofPartialFun s hs fun a ha => t.realize fun i => (x i a ha) := by
  induction t with
  | var => simp
  | func _ _ ih => simp_rw [Term.realize_func, ih, funMap_ofPartialFun]

theorem term_realize_cast {β : Type*} (x : β → ∀ a, M a) (t : L.Term β) :
    (t.realize fun i => (x i : (u : Filter α).Product M)) =
      (fun a => t.realize fun i => x i a : (u : Filter α).Product M) :=
  termRealize_ofPartialFun Filter.univ_mem _ t

theorem boundedFormulaRealize_ofPartialFun {β : Type*} {n : ℕ} (φ : L.BoundedFormula β n)
    {s : Set α} (hs : s ∈ (u : Filter α)) (x : β → ∀ a ∈ s, M a) (v : Fin n → ∀ a ∈ s, M a) :
    (φ.Realize (fun i => Product.ofPartialFun s hs (x i))
        (fun i => Product.ofPartialFun s hs (v i))) ↔
      ∀ᶠ a : α in (u : Filter α), ∀ ha : a ∈ s,
        φ.Realize (fun i => x i a ha) (fun i => v i a ha) := by
  induction φ generalizing s with (
    have h₁ : (fun i ↦ Product.ofPartialFun s hs (x i)) = Product.ofPartialFun s hs ∘ x := rfl
    have h₂ : (fun i ↦ Product.ofPartialFun s hs (v i)) = Product.ofPartialFun s hs ∘ v := rfl
    have h₃ (a ha) : (fun i ↦ x i a ha) = ((· a ha) ∘ x) := rfl
    have h₄ (a ha) : (fun i ↦ v i a ha) = ((· a ha) ∘ v) := rfl)
  | falsum => simp [BoundedFormula.Realize, hs]
  | equal t₁ t₂ =>
    simp_rw [BoundedFormula.Realize, h₁, h₂, h₃, h₄, ← Sum.comp_elim, Function.comp_def]
    rw [termRealize_ofPartialFun, termRealize_ofPartialFun, Product.ofPartialFun_eq_iff]
    simp
  | rel R ts =>
    simp_rw [BoundedFormula.Realize, h₁, h₂, h₃, h₄, ← Sum.comp_elim, Function.comp_def]
    simp_rw [termRealize_ofPartialFun, relMap_ofPartialFun]
  | imp f₁ f₂ ih₁ ih₂ =>
    simp_rw [BoundedFormula.realize_imp, ih₁, ih₂]
    rw [← Ultrafilter.eventually_imp]
    exact eventually_congr <| (eventually_mem_set.2 hs).mono fun _ ha => by simp [ha]
  | @all n f ih =>
    simp_rw [BoundedFormula.realize_all]
    refine ⟨Function.mtr ?_, fun h c => ?_⟩
    · simp_rw [not_eventually, not_forall, Ultrafilter.frequently_iff_eventually]
      intro h
      let P : Set α := { a | ∃ (ha : a ∈ s) (b : M a),
        ¬f.Realize (fun i => x i a ha) (Fin.snoc (fun i => v i a ha) b)}
      choose hPs C hC using fun (a : α) (ha : a ∈ P) => ha
      refine ⟨Product.ofPartialFun P h C, ?_⟩
      simp_rw [← Product.ofPartialFun_eq_of_subset h hPs]
      rw [← Function.comp_def (Product.ofPartialFun P h),
        ← Function.comp_def (Product.ofPartialFun P h), ← Fin.comp_snoc,
        Function.comp_def, Function.comp_def, ih h, not_eventually,
        Ultrafilter.frequently_iff_eventually]
      refine h.mono fun a ha => not_forall.2 ⟨ha, ?_⟩
      specialize hC a ha
      rw [← Function.comp_def (· a ha) (Fin.snoc (fun i a ha => v i a (hPs a ha)) C), Fin.comp_snoc]
      exact hC
    · induction c using Product.inductionOnPartialFun with | ofPartialFun t ht c
      simp_rw [← Product.ofPartialFun_eq_of_subset (inter_mem hs ht) Set.inter_subset_right,
        ← Product.ofPartialFun_eq_of_subset (inter_mem hs ht) Set.inter_subset_left,
        ← Function.comp_def (Product.ofPartialFun (s ∩ t) _),
        ← Fin.comp_snoc, Function.comp_def, ih]
      refine h.mono fun a ha hst => ?_
      rw [← Function.comp_def (· a hst) (Fin.snoc
        (fun i a ha => v i a ha.1) (fun a ha => c a ha.2)), Fin.comp_snoc]
      apply ha

theorem boundedFormula_realize_cast {β : Type*} {n : ℕ} (φ : L.BoundedFormula β n)
    (x : β → ∀ a, M a) (v : Fin n → ∀ a, M a) :
    (φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (fun i => (v i : (u : Filter α).Product M))) ↔
      ∀ᶠ a : α in u, φ.Realize (fun i : β => x i a) fun i => v i a :=
  (boundedFormulaRealize_ofPartialFun φ Filter.univ_mem _ _).trans (by simp)

theorem formulaRealize_ofPartialFun {β : Type*} (φ : L.Formula β)
    {s : Set α} (hs : s ∈ (u : Filter α)) (x : β → ∀ a ∈ s, M a) :
    (φ.Realize fun i => Product.ofPartialFun s hs (x i)) ↔
      ∀ᶠ a : α in u, ∀ ha : a ∈ s, φ.Realize fun i => x i a ha := by
  simp_rw [Formula.Realize, ← boundedFormulaRealize_ofPartialFun φ hs x, iff_eq_eq]
  exact congrArg _ (Subsingleton.elim _ _)

theorem realize_formula_cast {β : Type*} (φ : L.Formula β) (x : β → ∀ a, M a) :
    (φ.Realize fun i => (x i : (u : Filter α).Product M)) ↔
      ∀ᶠ a : α in u, φ.Realize fun i => x i a :=
  (formulaRealize_ofPartialFun φ Filter.univ_mem _).trans (by simp)

/-- **Łoś's Theorem**: A sentence is true in an ultraproduct if and only if the set of structures
it is true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ := by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

end Ultraproduct

end Language

end FirstOrder
