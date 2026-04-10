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

@[expose] public section

universe u v

variable {α : Type*} (M : α → Type*) (u : Ultrafilter α)

open FirstOrder Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [∀ a, L.Structure (M a)]

namespace Ultraproduct

variable {M} {u}

def sectionDom {n : ℕ} (x : Fin n → Product.Section (u : Filter α) M) : Set α :=
  { a | ∀ i, a ∈ (x i).dom }

theorem sectionDom_mem {n : ℕ} (x : Fin n → Product.Section (u : Filter α) M) :
    sectionDom (M := M) (u := u) x ∈ (u : Filter α) := by
  refine Filter.mem_of_superset (iInter_mem.2 fun i => (x i).dom_mem) ?_
  intro a ha
  simpa [sectionDom] using ha

def sectionStructure : L.Structure (Product.Section (u : Filter α) M) where
  funMap := fun {_} f x =>
    { dom := sectionDom (M := M) (u := u) x
      dom_mem := sectionDom_mem (M := M) (u := u) x
      val := by
        intro a
        cases a with
        | mk a ha =>
            exact funMap f fun i => (x i).val ⟨a, ha i⟩ }
  RelMap := fun {_} r x =>
    { a : α |
        ∃ h : a ∈ sectionDom (M := M) (u := u) x,
          RelMap r fun i => ((by simpa using (x i).val ⟨a, h i⟩) : M a) } ∈ u

instance setoidPrestructure : L.Prestructure ((u : Filter α).productSetoid M) where
  toStructure := sectionStructure (M := M) (u := u)
  fun_equiv := by
    classical
    intro n f x y xy
    -- xy : ∀ i, ∀ᶠ a in u, ∃ hx hy, (x i).val ⟨a, hx⟩ = (y i).val ⟨a, hy⟩
    -- Combine all eventually conditions
    have hall : ∀ᶠ a in (u : Filter α),
        ∀ i, ∃ hx : a ∈ (x i).dom, ∃ hy : a ∈ (y i).dom,
          (x i).val ⟨a, hx⟩ = (y i).val ⟨a, hy⟩ := by
      rw [Filter.eventually_all]
      exact xy
    exact hall.mono fun a ha => by
      choose hx hy heq using ha
      refine ⟨fun i => hx i, fun i => hy i, ?_⟩
      exact congrArg (funMap f) (funext heq)
  rel_equiv := by
    classical
    intro n r x y xy
    change
      ({ a : α | ∃ h : a ∈ sectionDom (M := M) (u := u) x,
          RelMap r fun i =>
            ((by simpa using (x i).val ⟨a, h i⟩) : M a) } ∈
        (u : Filter α)) =
      ({ a : α | ∃ h : a ∈ sectionDom (M := M) (u := u) y,
          RelMap r fun i =>
            ((by simpa using (y i).val ⟨a, h i⟩) : M a) } ∈
        (u : Filter α))
    have hall : ∀ᶠ a in (u : Filter α),
        ∀ i, ∃ hx : a ∈ (x i).dom, ∃ hy : a ∈ (y i).dom,
          (x i).val ⟨a, hx⟩ = (y i).val ⟨a, hy⟩ := by
      rw [Filter.eventually_all]
      exact xy
    apply propext
    constructor
    · intro hx
      refine Filter.mem_of_superset (inter_mem hx hall) ?_
      intro a ⟨⟨hxDom, hRel⟩, ha⟩
      choose hx' hy' heq using ha
      have hEq : (fun i => ((by simpa using (x i).val ⟨a, hxDom i⟩) : M a)) =
          fun i => ((by simpa using (y i).val ⟨a, hy' i⟩) : M a) := by
        funext i
        simpa using (by rw [show hxDom i = hx' i from Subsingleton.elim ..]; exact heq i)
      exact ⟨fun i => hy' i, hEq ▸ hRel⟩
    · intro hy
      refine Filter.mem_of_superset (inter_mem hy hall) ?_
      intro a ⟨⟨hyDom, hRel⟩, ha⟩
      choose hx' hy' heq using ha
      have hEq : (fun i => ((by simpa using (y i).val ⟨a, hyDom i⟩) : M a)) =
          fun i => ((by simpa using (x i).val ⟨a, hx' i⟩) : M a) := by
        funext i
        simpa using (by rw [show hyDom i = hy' i from Subsingleton.elim ..]; exact (heq i).symm)
      exact ⟨fun i => hx' i, hEq ▸ hRel⟩

noncomputable instance «structure» : L.Structure ((u : Filter α).Product M) :=
  Language.quotientStructure

theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ a, M a) :
    (funMap f fun i => (x i : (u : Filter α).Product M)) =
      (fun a => funMap f fun i => x i a : (u : Filter α).Product M) := by
  rw [funMap_quotient_mk']
  refine Quotient.sound ?_
  exact Filter.Eventually.of_forall fun a =>
    ⟨fun _ => trivial, trivial, rfl⟩

theorem term_realize_cast {β : Type*} (x : β → ∀ a, M a) (t : L.Term β) :
    (t.realize fun i => (x i : (u : Filter α).Product M)) =
      (fun a => t.realize fun i => x i a : (u : Filter α).Product M) := by
  induction t with
  | var => rfl
  | func f ts ih =>
      simp [Term.realize, ih, funMap_cast]

variable [∀ a : α, Nonempty (M a)]

theorem boundedFormula_realize_cast {β : Type*} {n : ℕ} (φ : L.BoundedFormula β n)
    (x : β → ∀ a, M a) (v : Fin n → ∀ a, M a) :
    (φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (fun i => (v i : (u : Filter α).Product M))) ↔
      ∀ᶠ a : α in u, φ.Realize (fun i : β => x i a) fun i => v i a := by
  induction φ with
  | falsum => simp only [BoundedFormula.Realize, eventually_const]
  | equal =>
    have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm,
      term_realize_cast, term_realize_cast]
    simpa using (Filter.Product.eq_iff_ofTotal (l := (u : Filter α)) (ε := M) _ _)
  | rel R ts =>
    have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm]
    conv_lhs => enter [2, i]; erw [term_realize_cast]
    let P : Prop :=
      @RelMap L (Product.Section (u : Filter α) M) (sectionStructure (M := M) (u := u)) _ R
        (fun i => Product.ofTotal (fun a => Term.realize (fun i => Sum.elim x v i a) (ts i)))
    have hq' :
        (RelMap R fun i =>
          (⟦Product.ofTotal (fun a => Term.realize (fun i => Sum.elim x v i a) (ts i))⟧ :
            (u : Filter α).Product M)) ↔ P := by
      simpa [P] using
        (relMap_quotient_mk' (L := L) (s := (u : Filter α).productSetoid M)
          (r := R)
          (x := fun i => Product.ofTotal
            (fun a => Term.realize (fun i => Sum.elim x v i a) (ts i))))
    have htotal : P ↔
        ∀ᶠ a : α in u, RelMap R fun i => Term.realize (fun i => Sum.elim x v i a) (ts i) := by
      dsimp [P]
      change
        ({ a : α | ∃ h : a ∈ sectionDom (M := M) (u := u)
            (fun i => Product.ofTotal (fun a => Term.realize (fun i => Sum.elim x v i a) (ts i))),
            RelMap R fun i =>
              ((by simpa using
                    ((Product.ofTotal (l := (u : Filter α))
                      (fun a =>
                        Term.realize
                          (fun i => Sum.elim x v i a)
                          (ts i))).val
                      ⟨a, h i⟩ : M a)) :
                M a) } ∈
            (u : Filter α)) ↔
        ∀ᶠ a : α in u,
          RelMap R fun i =>
            Term.realize (fun i => Sum.elim x v i a) (ts i)
      simp [Filter.Eventually, sectionDom, Product.ofTotal]
    exact hq'.trans htotal
  | imp _ _ ih ih' =>
    simp only [BoundedFormula.Realize, ih v, ih' v]
    rw [Ultrafilter.eventually_imp]
  | @all k φ ih =>
    classical
    simp only [BoundedFormula.Realize]
    let totalize : Product.Section (u : Filter α) M → (a : α) → M a := fun s a =>
      if h : a ∈ s.dom then s.val ⟨a, h⟩ else Classical.choice (inferInstance : Nonempty (M a))
    have htotalize :
        ∀ s : Product.Section (u : Filter α) M,
          ((totalize s : (u : Filter α).Product M) =
            (Quotient.mk _ s : (u : Filter α).Product M)) := by
      intro s
      apply Quotient.sound
      exact Filter.mem_of_superset s.dom_mem fun a ha =>
        ⟨trivial, ha, by simp [totalize, Product.ofTotal, ha]⟩
    have hforall :
        (∀ x_1 : (u : Filter α).Product M,
            φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
              (Fin.snoc (((↑) : (∀ a, M a) → (u : Filter α).Product M) ∘ v) x_1)) ↔
          ∀ m : ∀ a : α, M a,
            φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
              (Fin.snoc (((↑) : (∀ a, M a) → (u : Filter α).Product M) ∘ v)
                (m : (u : Filter α).Product M)) := by
      constructor
      · intro h m
        exact h (m : (u : Filter α).Product M)
      · intro h z
        refine Quotient.inductionOn z ?_
        intro s
        exact (htotalize s).symm ▸ h (totalize s)
    apply Iff.trans (b := ∀ m : ∀ a : α, M a,
      φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (Fin.snoc (((↑) : (∀ a, M a) → (u : Filter α).Product M) ∘ v)
          (m : (u : Filter α).Product M)))
    · exact hforall
    have h' :
      ∀ (m : ∀ a, M a) (a : α),
        (fun i : Fin (k + 1) => (Fin.snoc v m : _ → ∀ a, M a) i a) =
          Fin.snoc (fun i : Fin k => v i a) (m a) := by
      refine fun m a => funext (Fin.reverseInduction ?_ fun i _ => ?_)
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    simp only [← Fin.comp_snoc]
    simp only [Function.comp_def, ih, h']
    refine ⟨fun h => ?_, fun h m => ?_⟩
    · contrapose! h
      refine
        ⟨fun a : α =>
          Classical.epsilon fun m : M a =>
            ¬φ.Realize (fun i => x i a) (Fin.snoc (fun i => v i a) m),
          ?_⟩
      exact Filter.mem_of_superset h fun a ha => Classical.epsilon_spec ha
    · rw [Filter.eventually_iff] at *
      exact Filter.mem_of_superset h fun a ha => ha (m a)

theorem realize_formula_cast {β : Type*} (φ : L.Formula β) (x : β → ∀ a, M a) :
    (φ.Realize fun i => (x i : (u : Filter α).Product M)) ↔
      ∀ᶠ a : α in u, φ.Realize fun i => x i a := by
  simp_rw [Formula.Realize, ← boundedFormula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

/-- **Łoś's Theorem**: A sentence is true in an ultraproduct if and only if the set of structures
it is true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ := by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

nonrec instance Product.instNonempty : Nonempty ((u : Filter α).Product M) :=
  letI : ∀ a, Inhabited (M a) := fun _ => Classical.inhabited_of_nonempty'
  inferInstance

end Ultraproduct

end Language

end FirstOrder
