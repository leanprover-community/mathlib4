/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.ModelTheory.Algebra.Field.IsAlgClosed

universe u v w x

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) {α : Type w} {β : Type x}

def IsFunctional [Finite β] (φ : L.Formula (α ⊕ β)) : Prop :=
  T ⊨ᵇ Formula.iExsUnique id φ

def FunctionalFormula (α : Type w) (β : Type x) [Finite β] : Type _ :=
  { φ : L.Formula (α ⊕ β) // T.IsFunctional φ }

namespace FunctionalFormula

variable [Finite β] {T} {M : Type w} [L.Structure M] [T.Model M] [Nonempty M]

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

def ofTerm (t : L.Term α) : T.FunctionalFormula α Unit :=
  ⟨Term.equal (t.relabel Sum.inl) (var (Sum.inr ())), by
    simp only [IsFunctional, ModelsBoundedFormula, BoundedFormula.realize_iExsUnique, id_eq,
      Formula.realize_equal, Term.realize_relabel, Sum.elim_comp_inl, Term.realize_var,
      Sum.elim_inr, forall_const]
    intro M x
    use fun _ => t.realize x
    simp [funext_iff, eq_comm]⟩

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
  T.map of

end FunctionalFormulaLang

end Theory

end Language

end FirstOrder
