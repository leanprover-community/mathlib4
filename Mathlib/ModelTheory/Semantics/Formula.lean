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
variable {T : L.Theory}

open FirstOrder Cardinal

open Structure Cardinal Fin


namespace Formula

/-- A formula can be evaluated as true or false by giving values to each free variable. -/
nonrec def Realize (φ : L.Formula α) (v : α → M) : Prop :=
  φ.Realize v default

variable {φ ψ : L.Formula α} {v : α → M}

@[simp]
theorem realize_not : φ.not.Realize v ↔ ¬φ.Realize v :=
  Iff.rfl

@[simp]
theorem realize_bot : (⊥ : L.Formula α).Realize v ↔ False :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.Formula α).Realize v ↔ True :=
  BoundedFormula.realize_top

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v :=
  BoundedFormula.realize_inf

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v ↔ φ.Realize v → ψ.Realize v :=
  BoundedFormula.realize_imp

@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term α} :
    (R.formula ts).Realize v ↔ RelMap R fun i => (ts i).realize v :=
  BoundedFormula.realize_rel.trans (by simp)

@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.formula₁ t).Realize v ↔ RelMap R ![t.realize v] := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] := by
  rw [Relations.formula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v :=
  BoundedFormula.realize_sup

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v) :=
  BoundedFormula.realize_iff

@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α → β} {v : β → M} :
    (φ.relabel g).Realize v ↔ φ.Realize (v ∘ g) := by
  rw [Realize, Realize, relabel, BoundedFormula.realize_relabel, iff_eq_eq, Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)

theorem realize_relabel_sum_inr (φ : L.Formula (Fin n)) {v : Empty → M} {x : Fin n → M} :
    (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, Sum.elim_comp_inr, Fin.castAdd_zero,
    cast_refl, Function.comp_id,
    Subsingleton.elim (x ∘ (natAdd n : Fin 0 → Fin n)) default]

@[simp]
theorem realize_equal {t₁ t₂ : L.Term α} {x : α → M} :
    (t₁.equal t₂).Realize x ↔ t₁.realize x = t₂.realize x := by simp [Term.equal, Realize]

@[simp]
theorem realize_graph {f : L.Functions n} {x : Fin n → M} {y : M} :
    (Formula.graph f).Realize (Fin.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]

end Formula

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
nonrec def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.Realize (default : _ → M)

-- input using \|= or \vDash, but not using \models
@[inherit_doc Sentence.Realize]
infixl:51 " ⊨ " => Sentence.Realize

@[simp]
theorem Sentence.realize_not {φ : L.Sentence} : M ⊨ φ.not ↔ ¬M ⊨ φ :=
  Iff.rfl

namespace Formula

@[simp]
theorem realize_equivSentence_symm_con [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] (φ : L[[α]].Sentence) :
    ((equivSentence.symm φ).Realize fun a => (L.con a : M)) ↔ φ.Realize M := by
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr with (_ | a)
  · simp
  · cases a

@[simp]
theorem realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => (L.con a : M) := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ), _root_.Equiv.symm_apply_apply]

theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : α → M) :
    (equivSentence.symm φ).Realize v ↔
      @Sentence.Realize _ M (@Language.withConstantsStructure L M _ α (constantsOn.structure v))
        φ :=
  letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ

end Formula

/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀ φ ∈ T, M ⊨ φ

-- input using \|= or \vDash, but not using \models
@[inherit_doc Theory.Model]
infixl:51 " ⊨ " => Theory.Model

variable {M} (T : L.Theory)

@[simp default-10]
theorem Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩

theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h

variable (L M)

/-- The complete theory of a structure `M` is the set of all sentences `M` satisfies. -/
def completeTheory : L.Theory :=
  { φ | M ⊨ φ }

variable (N)

/-- Two structures are elementarily equivalent when they satisfy the same sentences. -/
def ElementarilyEquivalent : Prop :=
  L.completeTheory M = L.completeTheory N

@[inherit_doc FirstOrder.Language.ElementarilyEquivalent]
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

variable {L} {M} {N}

@[simp]
theorem mem_completeTheory {φ : Sentence L} : φ ∈ L.completeTheory M ↔ M ⊨ φ :=
  Iff.rfl

theorem elementarilyEquivalent_iff : M ≅[L] N ↔ ∀ φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_setOf_eq]

namespace Equiv

@[simp]
theorem realize_boundedFormula (g : M ≃[L] N) (φ : L.BoundedFormula α n) {v : α → M}
    {xs : Fin n → M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp only [BoundedFormula.Realize, ← Sum.comp_elim, Equiv.realize_term, g.injective.eq_iff]
  · simp only [BoundedFormula.Realize, ← Sum.comp_elim, Equiv.realize_term]
    exact g.map_rel _ _
  · rw [BoundedFormula.Realize, ih1, ih2, BoundedFormula.Realize]
  · rw [BoundedFormula.Realize, BoundedFormula.Realize]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Fin.comp_snoc, ih3] at h'
      exact h'
    · intro h a
      have h' := h (g.symm a)
      rw [← ih3, Fin.comp_snoc, g.apply_symm_apply] at h'
      exact h'

@[simp]
theorem realize_formula (g : M ≃[L] N) (φ : L.Formula α) {v : α → M} :
    φ.Realize (g ∘ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← g.realize_boundedFormula φ, iff_eq_eq,
    Unique.eq_default (g ∘ default)]

theorem realize_sentence (g : M ≃[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← g.realize_formula, Unique.eq_default (g ∘ default)]

theorem theory_model (g : M ≃[L] N) [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (g.realize_sentence φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

theorem elementarilyEquivalent (g : M ≃[L] N) : M ≅[L] N :=
  elementarilyEquivalent_iff.2 g.realize_sentence

end Equiv

variable {T : L.Theory}

instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.not_mem_empty φ hφ).elim⟩

namespace Theory

theorem Model.mono {T' : L.Theory} (_h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
  ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩

theorem Model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T ∪ T' := by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)

@[simp]
theorem model_union_iff {T' : L.Theory} : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    h.1.union h.2⟩

theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp

theorem model_iff_subset_completeTheory : M ⊨ T ↔ T ⊆ L.completeTheory M :=
  T.model_iff

theorem completeTheory.subset [MT : M ⊨ T] : T ⊆ L.completeTheory M :=
  model_iff_subset_completeTheory.1 MT

end Theory

instance model_completeTheory : M ⊨ L.completeTheory M :=
  Theory.model_iff_subset_completeTheory.2 (subset_refl _)

variable (M N)

theorem realize_iff_of_model_completeTheory [N ⊨ L.completeTheory M] (φ : L.Sentence) :
    N ⊨ φ ↔ M ⊨ φ := by
  refine ⟨fun h => ?_, (L.completeTheory M).realize_sentence_of_mem⟩
  contrapose! h
  rw [← Sentence.realize_not] at *
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)

variable {M N}

namespace BoundedFormula

@[simp]
theorem realize_alls {φ : L.BoundedFormula α n} {v : α → M} :
    φ.alls.Realize v ↔ ∀ xs : Fin n → M, φ.Realize v xs := by
  induction' n with n ih
  · exact Unique.forall_iff.symm
  · simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]
theorem realize_exs {φ : L.BoundedFormula α n} {v : α → M} :
    φ.exs.Realize v ↔ ∃ xs : Fin n → M, φ.Realize v xs := by
  induction' n with n ih
  · exact Unique.exists_iff.symm
  · simp only [BoundedFormula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iAlls
    [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} : (φ.iAlls f).Realize v ↔
      ∀ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp,
    castAdd_zero, finCongr_refl, OrderIso.refl_apply, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp],
      fun _ => by simp [Function.comp]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iAlls [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iAlls f) v v' ↔
      ∀ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  rw [← Formula.realize_iAlls, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iExs
    [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} : (φ.iExs f).Realize v ↔
      ∃ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp,
    castAdd_zero, finCongr_refl, OrderIso.refl_apply, Sum.elim_map, id_eq]
  rw [← not_iff_not, not_exists, not_exists]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp],
      fun _ => by simp [Function.comp]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iExs [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExs f) v v' ↔
      ∃ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  rw [← Formula.realize_iExs, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α n) (v : α ⊕ (Fin n) → M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 a8 a9 a0
  · rfl
  · simp [BoundedFormula.Realize]
  · simp [BoundedFormula.Realize]
  · rw [toFormula, Formula.Realize, realize_imp, ← Formula.Realize, ih1, ← Formula.Realize, ih2,
      realize_imp]
  · rw [toFormula, Formula.Realize, realize_all, realize_all]
    refine forall_congr' fun a => ?_
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h, realize_relabel, Formula.Realize, iff_iff_eq]
    simp only [Function.comp]
    congr with x
    · cases' x with _ x
      · simp
      · refine Fin.lastCases ?_ ?_ x
        · rw [Sum.elim_inr, Sum.elim_inr,
            finSumFinEquiv_symm_last, Sum.map_inr, Sum.elim_inr]
          simp [Fin.snoc]
        · simp only [castSucc, Function.comp_apply, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← castSucc]
          simp
    · exact Fin.elim0 x

@[simp]
theorem realize_iSup (s : Finset β) (f : β → L.BoundedFormula α n)
    (v : α → M) (v' : Fin n → M) :
    (iSup s f).Realize v v' ↔ ∃ b ∈ s, (f b).Realize v v' := by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList,
    exists_exists_and_eq_and]

@[simp]
theorem realize_iInf (s : Finset β) (f : β → L.BoundedFormula α n)
    (v : α → M) (v' : Fin n → M) :
    (iInf s f).Realize v v' ↔ ∀ b ∈ s, (f b).Realize v v' := by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

end BoundedFormula

namespace ElementarilyEquivalent

@[symm]
nonrec theorem symm (h : M ≅[L] N) : N ≅[L] M :=
  h.symm

@[trans]
nonrec theorem trans (MN : M ≅[L] N) (NP : N ≅[L] P) : M ≅[L] P :=
  MN.trans NP

theorem completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N :=
  h

theorem realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (elementarilyEquivalent_iff.1 h) φ

theorem theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T := by
  rw [Theory.model_iff_subset_completeTheory, Theory.model_iff_subset_completeTheory,
    h.completeTheory_eq]

theorem theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T :=
  h.theory_model_iff.1 MT

end ElementarilyEquivalent

end Language

end FirstOrder
