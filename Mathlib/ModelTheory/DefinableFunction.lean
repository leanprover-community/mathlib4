/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed

universe u v w x y z

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) {α : Type w} {β : Type x} {γ : Type y}
variable [Finite β] {M : Type z} [L.Structure M] [T.Model M] [Nonempty M]

def FunctionalFormula (α : Type w) (β : Type x) [Finite β] : Type _ :=
  { φ : L.Formula (α ⊕ β) // T ⊨ᵇ Formula.iExsUnique id φ }

namespace FunctionalFormula

variable {T}

theorem exists_fun_eq_iff (f : T.FunctionalFormula α β) : ∃ f' : (α → M) → (β → M),
    ∀ x, ∀ y, f' x = y ↔ f.1.Realize (Sum.elim x y) := by
  rcases f with ⟨φ, h⟩
  have := fun x : α → M => h.realize_formula M (v := x)
  simp only [Formula.realize_iExsUnique, ExistsUnique, id_eq, Classical.skolem] at this
  rcases this with ⟨f, hf⟩
  use f
  intro x y
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact (hf x).1
  · rintro h
    exact ((hf x).2 y h).symm

noncomputable def realize (f : T.FunctionalFormula α β) : (α → M) → (β → M) :=
  Classical.choose (f.exists_fun_eq_iff)

theorem realize_spec {f : T.FunctionalFormula α β} {x : α → M} {y : β → M} :
    f.realize x = y ↔ f.1.Realize (Sum.elim x y) :=
  Classical.choose_spec (f.exists_fun_eq_iff) x y

theorem realize_spec' {f : T.FunctionalFormula α β} {x : α ⊕ β → M} :
    f.1.Realize x ↔ f.realize (x ∘ Sum.inl) = x ∘ Sum.inr := by
  rw [realize_spec]; simp

theorem realize_spec2 {f : T.FunctionalFormula α β} {x : α ⊕ β → M} {y : Fin 0 → M} :
    BoundedFormula.Realize f.1 x y ↔ f.realize (x ∘ Sum.inl) = x ∘ Sum.inr := by
  rw [← realize_spec', Formula.Realize, iff_iff_eq]
  congr; ext x; exact Fin.elim0 x

def ofTerm (t : L.Term α) : T.FunctionalFormula α Unit :=
  ⟨Term.equal (t.relabel Sum.inl) (var (Sum.inr ())), by
    simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq,
      Formula.realize_equal, Term.realize_relabel, Sum.elim_comp_inl, Term.realize_var,
      Sum.elim_inr, forall_const]
    intro M x
    use fun _ => t.realize x
    simp +contextual [funext_iff, eq_comm]⟩

@[simp]
theorem realize_ofTerm (t : L.Term α) (x : α → M) :
    (ofTerm (T := T) t).realize x = fun _ => t.realize x := by
  rw [realize_spec]
  simp [ofTerm, Formula.Realize, Term.realize_relabel, Term.realize_var, Term.equal,
    Function.comp_def]

variable (T)
noncomputable def comap (f : β → α) : T.FunctionalFormula α β :=
  let e := Fintype.ofFinite β
  ⟨Formula.iAlls (γ := β) Sum.inl
    (BoundedFormula.iInf (Finset.univ : Finset β)
      (fun b => Term.equal (var (Sum.inr b)) (var (Sum.inl (f b))))), by
  simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq, Formula.realize_iAlls,
    Sum.elim_inl, forall_const]
  intro M x
  use fun y => x (f y)
  simp [Formula.Realize, Term.equal, funext_iff]⟩

variable {T}
@[simp]
theorem realize_comap (f : β → α) (x : α → M) : (comap T f).realize x = x ∘ f := by
  rw [realize_spec]
  simp [comap, Formula.Realize, Term.equal]

variable (T)
protected noncomputable def id : T.FunctionalFormula β β :=
  comap T id

@[simp]
theorem realize_id (x : β → M) :
    (FunctionalFormula.id T).realize (T := T) (M := M) x = x := by
  simp [FunctionalFormula.id]

variable {T}
noncomputable def comp [Finite γ] (f : T.FunctionalFormula β γ) (g : T.FunctionalFormula α β) :
    T.FunctionalFormula α γ :=
  ⟨Formula.iExs (α := (α ⊕ γ) ⊕ β) (γ := β) id
    (f.1.relabel (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)) ⊓
     g.1.relabel (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)), by
  simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_relabel, forall_const]
  intro M x
  use f.realize (g.realize x)
  simp only [Function.comp_def, Formula.realize_iExs, id_eq, Formula.realize_relabel,
    forall_exists_index]
  refine ⟨?_, ?_⟩
  · use g.realize x
    simp [realize_spec', Function.comp_def]
  · intro y z
    simp only [realize_spec', Function.comp_def, Sum.elim_inl, Sum.elim_inr, funext_iff, and_imp]
    intro h1 h2 g
    simp only [← h1, ← h2]⟩

@[simp]
theorem realize_comp [Finite γ] (f : T.FunctionalFormula β γ) (g : T.FunctionalFormula α β)
    (x : α → M) : (f.comp g).realize x = f.realize (g.realize x) := by
  rw [realize_spec]
  simp only [comp, Function.comp_def, Formula.realize_iExs, id_eq, Formula.realize_inf,
    Formula.realize_relabel]
  use g.realize x
  simp [Function.comp_def, realize_spec']

noncomputable def toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : ∀ b, T.FunctionalFormula α (γ b)) :
    T.FunctionalFormula α (Σ b, γ b) :=
  let e := Fintype.ofFinite β
  ⟨BoundedFormula.iInf (Finset.univ : Finset β)
    (fun b => (f b).1.relabel (Sum.elim Sum.inl (fun g => Sum.inr ⟨_, g⟩))), by
  simp only [ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq, forall_const]
  intro M x
  use (fun i : Σ b, γ b => (f i.1).realize x i.2)
  simp only [Formula.Realize, Formula.relabel, Function.comp_def, BoundedFormula.realize_iInf,
    Finset.mem_univ, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero, Fin.cast_refl,
    CompTriple.comp_eq, Sum.elim_inl, Fin.natAdd_zero, realize_spec2, Sum.elim_inr, imp_self,
    implies_true, funext_iff, eq_comm, forall_const, true_and]
  intro y h z
  cases z
  rw [h]⟩

@[simp]
theorem realize_toSigma {γ : β → Type y} [∀ b, Finite (γ b)]
    (f : ∀ b, T.FunctionalFormula α (γ b)) (x : α → M) :
    (toSigma f).realize x = fun i => (f i.1).realize x i.2 := by
  rw [realize_spec]
  simp only [Formula.Realize, toSigma, Formula.relabel, Function.comp_def,
    BoundedFormula.realize_iInf, Finset.mem_univ, BoundedFormula.realize_relabel, Nat.add_zero,
    Fin.castAdd_zero, Fin.cast_refl, CompTriple.comp_eq, Sum.elim_inl, Fin.natAdd_zero,
    forall_const]
  intro b
  rw [realize_spec2]
  congr

end FunctionalFormula

open FunctionalFormula

def FunctionalFormulaLang : Language where
  Functions := fun n => FunctionalFormula.{u, v, 0, 0} T (Fin n) Unit
  Relations := L.Relations

namespace FunctionalFormulaLang

def of : L →ᴸ FunctionalFormulaLang T where
  onFunction := fun _ f => ofTerm (func f var)
  onRelation := fun _ R => R

def theory : (FunctionalFormulaLang T).Theory :=
  (of T).onTheory T ∪
    ⋃ (n : ℕ), Set.range (fun f : FunctionalFormula T (Fin n) Unit =>
      Formula.iAlls (γ := Fin n ⊕ Unit) Sum.inr <|
        (Term.equal (func f (fun i => var (Sum.inl i))) (var (Sum.inr ()))).iff
        ((of T).onFormula f.1))

@[simps]
noncomputable instance : (FunctionalFormulaLang T).Structure M where
  funMap := fun f x => f.realize x ()
  RelMap := fun R => Structure.RelMap (L := L) R

instance : (of T).IsExpansionOn M where
    map_onFunction := by intros; simp [of]
    map_onRelation := by intros; simp [of]

noncomputable instance : (FunctionalFormulaLang.theory T).Model M where
  realize_of_mem := fun φ hφ => by
    simp only [theory, Set.mem_union, LHom.mem_onTheory, Set.mem_iUnion, Set.mem_range] at hφ
    rcases hφ with ⟨φ₀, hφ₀, rfl⟩ | ⟨i, hi, rfl⟩
    · simp only [LHom.realize_onSentence]
      exact realize_sentence_of_mem T hφ₀
    · simp only [Sentence.Realize, Formula.realize_iAlls, Sum.elim_inr, Formula.realize_iff,
        Formula.realize_equal, Term.realize_func, Term.realize_var, instStructure_funMap,
        LHom.realize_onFormula, realize_spec', Function.comp_def, funext_iff]
      intro i
      refine ⟨?_, ?_⟩
      · rintro h ⟨⟩; exact h
      · intro h; exact h _


end FunctionalFormulaLang

end Theory

end Language

end FirstOrder
