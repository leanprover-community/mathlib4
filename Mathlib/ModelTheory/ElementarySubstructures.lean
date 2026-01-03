/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.ElementaryMaps
public import Mathlib.ModelTheory.Definability

/-!
# Elementary Substructures

## Main Definitions

- A `FirstOrder.Language.ElementarySubstructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

## Main Results

- The Tarski-Vaught Test for substructures:
  `FirstOrder.Language.Substructure.isElementary_of_exists` gives a simple criterion for a
  substructure to be elementary.
-/

@[expose] public section


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

/-- A substructure is elementary when every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
def Substructure.IsElementary (S : L.Substructure M) : Prop :=
  ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → S), φ.Realize (((↑) : _ → M) ∘ x) ↔ φ.Realize x

variable (L M)

/-- An elementary substructure is one in which every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
structure ElementarySubstructure where
  /-- The underlying substructure -/
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary

variable {L M}

namespace ElementarySubstructure

attribute [coe] toSubstructure

instance instCoe : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩

instance instSetLike : SetLike (L.ElementarySubstructure M) M :=
  ⟨fun x => x.toSubstructure.carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, _⟩ _ => by
    congr⟩

instance inducedStructure (S : L.ElementarySubstructure M) : L.Structure S :=
  Substructure.inducedStructure

@[simp]
theorem isElementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.isElementary'

/-- The natural embedding of an `L.Substructure` of `M` into `M`. -/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := (↑)
  map_formula' := S.isElementary

@[simp]
theorem subtype_apply {S : L.ElementarySubstructure M} {x : S} : subtype S x = x :=
  rfl

theorem subtype_injective (S : L.ElementarySubstructure M) : Function.Injective (subtype S) :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype (S : L.ElementarySubstructure M) : ⇑S.subtype = Subtype.val :=
  rfl

/-- The substructure `M` of the structure `M` is elementary. -/
instance instTop : Top (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun _ _ _ => Substructure.realize_formula_top.symm⟩⟩

instance instInhabited : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.ElementarySubstructure M) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.univ :=
  rfl

@[simp]
theorem realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) : S ⊨ φ ↔ M ⊨ φ :=
  S.subtype.map_sentence φ

@[simp]
theorem theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔ M ⊨ T := by
  simp only [Theory.model_iff, realize_sentence]

instance theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} : S ⊨ T :=
  (theory_model_iff S T).2 h

instance instNonempty [Nonempty M] {S : L.ElementarySubstructure M} : Nonempty S :=
  (model_nonemptyTheory_iff L).1 inferInstance

theorem elementarilyEquivalent (S : L.ElementarySubstructure M) : S ≅[L] M :=
  S.subtype.elementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/-- The Tarski-Vaught test for elementarity of a substructure. -/
theorem isElementary_of_exists (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    S.IsElementary := fun _ => S.subtype.isElementary_of_exists htv

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps]
def toElementarySubstructure (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    L.ElementarySubstructure M :=
  ⟨S, S.isElementary_of_exists htv⟩

end Substructure

/-- A set satisfies the Tarski-Vaught property if it meets every nonempty definable subset. -/
def TarskiVaught (A : Set M) : Prop :=
  ∀ (D : Set M), D.Nonempty → A.Definable₁ L D → (D ∩ A).Nonempty

namespace TarskiVaught

open Set Substructure

variable {A : Set M}

/-- The closure of a set with the Tarski-Vaught property equals to itself. -/
theorem closure_eq_self (hA : L.TarskiVaught A) :
    closure L A = A := by
  refine Eq.symm (Subset.antisymm ?_ ?_)
  · exact subset_closure
  · intro x hx
    simp only [SetLike.mem_coe, mem_closure_iff_exists_term] at hx
    obtain ⟨t,ht⟩ := hx
    let D : Set M := {x}
    have : A.Definable₁ L D := by
      simp only [Definable₁, Definable]
      exists (Term.var 0).equal (t.relabel Sum.inl).varsToConstants
      ext v
      simp only [Fin.isValue, mem_singleton_iff, mem_setOf_eq, Formula.realize_equal,
        Term.realize_var, D, ←ht]
      refine Eq.congr_right ?_
      simp only [Term.realize_varsToConstants, coe_con, Term.realize_relabel, Sum.elim_comp_inl]
    specialize hA D (singleton_nonempty x) this
    exact singleton_inter_nonempty.mp hA

/-- The closure of a set with the Tarski-Vaught property is an elementary substructure. -/
theorem isElementary_closure (hA : L.TarskiVaught A) :
    (closure L A).IsElementary := by
  refine isElementary_of_exists ((closure L).toFun A) ?_
  intro n φ x a hφ
  let D : Set M := {y : M | φ.Realize default (Fin.snoc (Subtype.val ∘ x) y)}
  have hD_ne : D.Nonempty := ⟨a,hφ⟩
  have hD : A.Definable₁ L D := by
    simp only [Definable₁, Definable, Fin.isValue]
    refine ⟨((L.lhomWithConstants A).onBoundedFormula φ).toFormula.relabel
      (Sum.elim Empty.elim id) |>.subst (fun i => Fin.lastCases (Term.var 0)
        (fun j => (L.con ⟨x j, by
        nth_rw 1 [← hA.closure_eq_self]
        simp only [Subtype.coe_prop]
        ⟩).term) i), ?_⟩
    ext v
    simp only [Fin.isValue, mem_setOf_eq, Formula.relabel, Formula.Realize,
      BoundedFormula.realize_subst, BoundedFormula.realize_relabel, Nat.add_zero, Fin.castAdd_zero,
      Fin.cast_refl, Function.comp_id, Fin.natAdd_zero, D]
    rw [← Formula.Realize, BoundedFormula.realize_toFormula, LHom.realize_onBoundedFormula]
    exact Iff.of_eq <| congrArg₂ _ (funext fun e => e.elim)
      (funext fun i => by cases i using Fin.lastCases <;> simp)
  obtain ⟨b, hbD, hbA⟩ := hA D hD_ne hD
  exact ⟨⟨b, by rwa [← hA.closure_eq_self] at hbA⟩, hbD⟩

/-- Bundles the closure of a set with the Tarski-Vaught property as an elementary substructure. -/
def toElementarySubstructure (hA : L.TarskiVaught A) :
    L.ElementarySubstructure M :=
  ⟨closure L A, hA.isElementary_closure⟩

end TarskiVaught

end Language

end FirstOrder
