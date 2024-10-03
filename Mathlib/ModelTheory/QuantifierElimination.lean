/-
Copyright (c) 2024 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Complexity

/-!
# Quantifier Elimination

This file defines when a theory eliminates quantifiers and establishes basic quantifier elimination
tests.

## Main Definitions

- `FirstOrder.Language.Theory.HasQE`: `T.HasQE` indicates that `T` has quantifier elimination -
  every formula is equivalent to a quantifier-free formula.

## Main Results

- `FirstOrder.Language.Theory.hasQE_iff_ex_equivalent_isQF` shows that to eliminate quantifiers, it
  suffices to eliminate a single existential quantifier.

-/

universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type u'} {n : ℕ}
variable {M : Type w} [L.Structure M]

namespace Theory

open Fin

variable (T)

/-- A theory has quantifier elimination when every formula is equivalent to a quantifier-free
formula. -/
def HasQE : Prop :=
  ∀ {n} (φ : L.Formula (Fin n)), ∃ (ψ : L.Formula (Fin n)), ψ.IsQF ∧ (φ ⇔[T] ψ)

variable {T}

namespace HasQE

lemma mono {T' : L.Theory} (hTT' : T ⊆ T') (hT : T.HasQE) : T'.HasQE :=
  fun φ => (hT φ).imp (fun _ => And.imp_right (SemanticallyEquivalent.mono hTT'))

theorem exists_isQF_equivalent (hT : T.HasQE) (φ : L.BoundedFormula α n) :
    ∃ (ψ : L.BoundedFormula α n), ψ.IsQF ∧ (φ ⇔[T] ψ) := by
  classical
  obtain ⟨ψ₁, ψ₁QF, φ'ψ₁⟩ := hT ((φ.restrictFreeVar id).toFormula.relabel (Fintype.equivFin _))
  use BoundedFormula.relabel (Sum.map Subtype.val id) (ψ₁.relabel (Fintype.equivFin _).symm)
  refine ⟨(ψ₁QF.relabel _).relabel _, fun M v xs => ?_⟩
  have h : (((xs ∘ natAdd n) ∘ natAdd 0) ∘ natAdd 0 : Fin 0 → M) = default := Unique.eq_default _
  simp only [Formula.relabel, BoundedFormula.realize_iff, BoundedFormula.realize_relabel,
    Nat.add_zero, castAdd_zero, cast_refl, CompTriple.comp_eq, ← φ'ψ₁.realize_bd_iff, h]
  rw [← Formula.Realize, BoundedFormula.realize_toFormula,
    ← BoundedFormula.realize_restrictFreeVar_id, iff_eq_eq]
  congr
  · ext a
    simp only [Function.comp_apply, Sum.elim_inl, _root_.Equiv.symm_apply_apply, Sum.map_inl]
  · ext i
    simp only [Function.comp_apply, Sum.elim_inl, _root_.Equiv.symm_apply_apply, Sum.map_inr, id_eq,
      Sum.elim_inr]

end HasQE

lemma hasQE_iff_bd : T.HasQE ↔ ∀ {n} (φ : L.BoundedFormula Empty n),
    ∃ (ψ : L.BoundedFormula Empty n), ψ.IsQF ∧ (φ ⇔[T] ψ) := by
  refine ⟨fun h n φ => h.exists_isQF_equivalent φ, fun h n φ => ?_⟩
  obtain ⟨ψ₁, ψ₁QF, φ'ψ₁⟩ := h (BoundedFormula.relabel Sum.inr φ)
  use ψ₁.toFormula.relabel (Equiv.emptySum _ _)
  refine ⟨ψ₁QF.toFormula.relabel _, fun M v xs => ?_⟩
  simp only [Formula.relabel, Nat.add_zero, BoundedFormula.realize_iff,
    BoundedFormula.realize_relabel, castAdd_zero, cast_refl, CompTriple.comp_eq]
  rw [Unique.eq_default (xs ∘ natAdd 0 : Fin 0 → M), ← Formula.Realize,
    BoundedFormula.realize_toFormula, ← φ'ψ₁.realize_bd_iff]
  simp only [Nat.add_zero, BoundedFormula.realize_relabel, castAdd_zero, cast_refl,
    CompTriple.comp_eq, Sum.elim_comp_inl_inr, iff_eq_eq]
  congr
  exact Subsingleton.elim xs _

theorem hasQE_iff_ex_equivalent_isQF :
    T.HasQE ↔
      ∀ {n} (φ : L.BoundedFormula Empty (n + 1)), φ.IsQF →
        ∃ (ψ : L.BoundedFormula Empty n), ψ.IsQF ∧ (φ.ex ⇔[T] ψ) := by
  rw [hasQE_iff_bd]
  refine ⟨fun h _ φ _ => h φ.ex, fun h _ φ => ?_⟩
  induction φ using BoundedFormula.induction_on_exists_not with
  | hqf ih => exact ⟨_, ih, refl _⟩
  | hnot ih =>
    obtain ⟨ψ, hψ, hφψ⟩ := ih
    exact ⟨ψ.not, hψ.not, hφψ.not⟩
  | hex ih =>
    obtain ⟨ψ, hψ, hφψ⟩ := ih
    exact (h _ hψ).imp (fun _ => And.imp id hφψ.ex.trans)
  | hse ih =>
    exact exists_congr (fun _ => and_congr_right'
      ⟨(ih.mono T.empty_subset).symm.trans, (ih.mono T.empty_subset).trans⟩)

end Theory

variable (L)

abbrev Morleyization_aux : Language := ⟨fun _ => Empty, fun n => L.Formula (Fin n)⟩

abbrev Morleyization := L.sum L.Morleyization_aux

variable {L}

instance : L.Morleyization_aux.Structure M where
  RelMap φ v := φ.Realize v

@[simp]
lemma Morleyization.relationsBoundedFormula_realize (φ : L.Formula (Fin n)) (v : Fin n → M) :
    (Relations.formula (Sum.inr φ) Term.var : L.Morleyization.Formula (Fin n)).Realize v ↔
    φ.Realize v := by rfl

noncomputable def Formula.MorleyAxiom (φ : L.Formula (Fin n)) :
    L.Morleyization.Sentence :=
  Formula.iAlls Sum.inr (LHom.sumInl.onFormula φ ⇔ Relations.formula (Sum.inr φ) Term.var)

lemma Formula.realize_MorleyAxiom (φ : L.Formula (Fin n)) : M ⊨ φ.MorleyAxiom := by
  simp only [Sentence.Realize, MorleyAxiom, realize_iAlls, Sum.elim_inr, realize_iff,
    LHom.realize_onFormula, realize_rel, Term.realize_var]
  intro xs
  rfl

@[simp]
def Term.deMorleyize : L.Morleyization.Term α → L.Term α
  | var a => var a
  | func (Sum.inl f) ts => func f (fun i => (ts i).deMorleyize)

@[simp]
lemma sumInl_onTerm_deMorleyize {t : L.Morleyization.Term α} :
    LHom.sumInl.onTerm t.deMorleyize = t := by
  induction t with
  | var a => rfl
  | func f ts ih =>
    match f with
    | Sum.inl f =>
      simp only [LHom.onTerm, LHom.sumInl_onFunction, ih]

@[simp]
def BoundedFormula.deMorleyize :
    ∀ {n}, L.Morleyization.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, (equal t₁ t₂) => equal t₁.deMorleyize t₂.deMorleyize
  | _, (rel (Sum.inl R) ts) => rel R (fun i => (ts i).deMorleyize)
  | _, (rel (Sum.inr φ) ts) => (BoundedFormula.subst φ (fun i => (ts i).deMorleyize)).relabel id
  | _, (imp φ ψ) => φ.deMorleyize.imp ψ.deMorleyize
  | _, (all φ) => φ.deMorleyize.all

def MorleyizationTheory : L.Morleyization.Theory :=
  ⋃ n, (Set.range (Formula.MorleyAxiom : L.Formula (Fin n) → _))

lemma onFormula_iff_morleyization {φ : L.Formula (Fin n)} :
    LHom.sumInl.onFormula φ ⇔[L.MorleyizationTheory] Relations.formula (Sum.inr φ) Term.var := by
  intro M v xs
  rw [Unique.eq_default xs]
  have h : L.MorleyizationTheory ⊨ᵇ Formula.MorleyAxiom φ :=
    Theory.models_sentence_of_mem (Set.mem_iUnion_of_mem _ (Set.mem_range_self φ))
  have h' := h M default default
  simp only [Formula.MorleyAxiom, BoundedFormula.realize_iAlls, Sum.elim_inr, Formula.realize_iff,
    Formula.realize_rel, Term.realize_var] at h'
  rw [← Formula.Realize]
  simp only [Formula.realize_iff, Formula.realize_rel, Term.realize_var, h' v]

-- lemma onFormula_deMorleyize_iff {m : ℕ} (φ : L.Morleyization.BoundedFormula (Fin m) n) :
--     LHom.sumInl.onBoundedFormula φ.deMorleyize ⇔[L.MorleyizationTheory] φ := by
--   induction φ with
--   | falsum => rfl
--   | equal t₁ t₂ =>
--     simp only [LHom.onBoundedFormula, sumInl_onTerm_deMorleyize]
--     rfl
--   | rel R ts =>
--     have h : (LHom.sumInl.onTerm ∘ fun i ↦ (ts i).deMorleyize) = ts := by
--         ext i
--         simp only [Function.comp_apply, sumInl_onTerm_deMorleyize]
--     cases R with
--     | inl R =>
--       simp only [LHom.onBoundedFormula, LHom.sumInl_onRelation, h]
--       rfl
--     | inr φ =>
--       simp only [BoundedFormula.deMorleyize]
--       have h' : L.MorleyizationTheory ⊨ᵇ Formula.MorleyAxiom φ :=
--         Theory.models_sentence_of_mem (Set.mem_iUnion_of_mem _ (Set.mem_range_self φ))
--       intro M v xs
--       have h'' := h' M default default
--       simp only [Formula.MorleyAxiom, BoundedFormula.realize_iAlls, Sum.elim_inr,
--         Formula.realize_iff, Formula.realize_rel, Term.realize_var] at h''
--       have h3 := h'' (fun i => (ts i).realize (Sum.elim v xs))
--       simp only at h3
--       simp only [BoundedFormula.deMorleyize, BoundedFormula.realize_iff]


--       sorry
--   | imp _ _ ih1 ih2 => exact ih1.imp ih2
--   | all _ ih => exact ih.all

namespace Theory

variable (T)

protected def Morleyization : L.Morleyization.Theory :=
  LHom.sumInl.onTheory T ∪ L.MorleyizationTheory

instance models_Morleyization [M ⊨ T] : M ⊨ T.Morleyization := by
  refine ⟨fun _ h => ?_⟩
  simp only [Theory.Morleyization, Set.mem_union, LHom.mem_onTheory, Set.mem_iUnion,
    Set.mem_range] at h
  obtain (⟨ψ, h, rfl⟩ | ⟨_, ψ, rfl⟩) := h
  · simp only [LHom.realize_onSentence]
    exact Theory.realize_sentence_of_mem _ h
  · exact ψ.realize_MorleyAxiom

-- theorem Morleyization_hasQE : T.Morleyization.HasQE := by
--   intro n φ

--   sorry


end Theory

end Language

end FirstOrder
