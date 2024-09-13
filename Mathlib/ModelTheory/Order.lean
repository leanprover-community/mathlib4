/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Complexity

/-!
# Ordered First-Ordered Structures

This file defines ordered first-order languages and structures, as well as their theories.

## Main Definitions

- `FirstOrder.Language.order` is the language consisting of a single relation representing `≤`.
- `FirstOrder.Language.orderStructure` is the structure on an ordered type, assigning the symbol
  representing `≤` to the actual relation `≤`.
- `FirstOrder.Language.IsOrdered` points out a specific symbol in a language as representing `≤`.
- `FirstOrder.Language.OrderedStructure` indicates that the `≤` symbol in an ordered language
  is interpreted as the actual relation `≤` in a particular structure.
- `FirstOrder.Language.linearOrderTheory` and similar define the theories of preorders,
  partial orders, and linear orders.
- `FirstOrder.Language.dlo` defines the theory of dense linear orders without endpoints, a
  particularly useful example in model theory.

## Main Results

- `PartialOrder`s model the theory of partial orders, `LinearOrder`s model the theory of
  linear orders, and dense linear orders without endpoints model `Language.dlo`.
-/


universe u v w w'

namespace FirstOrder

namespace Language


open FirstOrder Structure

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The language consisting of a single relation representing `≤`. -/
protected def order : Language :=
  Language.mk₂ Empty Empty Empty Empty Unit

instance orderStructure [LE M] : Language.order.Structure M :=
  Structure.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => (· ≤ ·)

namespace Order

instance Language.instIsRelational : IsRelational Language.order :=
  Language.isRelational_mk₂

instance Language.instSubsingleton : Subsingleton (Language.order.Relations n) :=
  Language.subsingleton_mk₂_relations

end Order

/-- A language is ordered if it has a symbol representing `≤`. -/
class IsOrdered (L : Language.{u, v}) where
  leSymb : L.Relations 2

export IsOrdered (leSymb)

section IsOrdered

variable [IsOrdered L]

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ ≤ t₂`. -/
def Term.le (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  leSymb.boundedFormula₂ t₁ t₂

/-- Joins two terms `t₁, t₂` in a formula representing `t₁ < t₂`. -/
def Term.lt (t₁ t₂ : L.Term (α ⊕ (Fin n))) : L.BoundedFormula α n :=
  t₁.le t₂ ⊓ ∼(t₂.le t₁)

variable (L)

/-- The language homomorphism sending the unique symbol `≤` of `Language.order` to `≤` in an ordered
 language. -/
def orderLHom : Language.order →ᴸ L :=
  LHom.mk₂ Empty.elim Empty.elim Empty.elim Empty.elim fun _ => leSymb

end IsOrdered

instance : IsOrdered Language.order :=
  ⟨Unit.unit⟩

@[simp]
theorem orderLHom_leSymb [L.IsOrdered] :
    (orderLHom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl

@[simp]
theorem orderLHom_order : orderLHom Language.order = LHom.id Language.order :=
  LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

instance sum.instIsOrdered : IsOrdered (L.sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

section

variable (L) [IsOrdered L]

/-- The theory of preorders. -/
def preorderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.transitive}

instance : Theory.IsUniversal L.preorderTheory := ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩

/-- The theory of partial orders. -/
def partialOrderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.antisymmetric, leSymb.transitive}

instance : Theory.IsUniversal L.partialOrderTheory := ⟨by
  simp only [partialOrderTheory,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_antisymmetric,
    leSymb.isUniversal_transitive⟩⟩

/-- The theory of linear orders. -/
def linearOrderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.antisymmetric, leSymb.transitive, leSymb.total}

instance : Theory.IsUniversal L.linearOrderTheory := ⟨by
  simp only [linearOrderTheory,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_antisymmetric,
    leSymb.isUniversal_transitive, leSymb.isUniversal_total⟩⟩

example [L.Structure M] [M ⊨ L.linearOrderTheory] (S : L.Substructure M) :
    S ⊨ L.linearOrderTheory := inferInstance

/-- A sentence indicating that an order has no top element:
$\forall x, \exists y, \neg y \le x$.   -/
def noTopOrderSentence : L.Sentence :=
  ∀'∃'∼((&1).le &0)

/-- A sentence indicating that an order has no bottom element:
$\forall x, \exists y, \neg x \le y$. -/
def noBotOrderSentence : L.Sentence :=
  ∀'∃'∼((&0).le &1)

/-- A sentence indicating that an order is dense:
$\forall x, \forall y, x < y \to \exists z, x < z \wedge z < y$. -/
def denselyOrderedSentence : L.Sentence :=
  ∀'∀'((&0).lt &1 ⟹ ∃'((&0).lt &2 ⊓ (&2).lt &1))

/-- The theory of dense linear orders without endpoints. -/
def dlo : L.Theory :=
  L.linearOrderTheory ∪ {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}

end

variable (L M)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
abbrev OrderedStructure [IsOrdered L] [LE M] [L.Structure M] : Prop :=
  LHom.IsExpansionOn (orderLHom L) M

variable {L M}

@[simp]
theorem orderedStructure_iff [IsOrdered L] [LE M] [L.Structure M] :
    L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M :=
  Iff.rfl

instance orderedStructure_LE [LE M] : OrderedStructure Language.order M := by
  rw [orderedStructure_iff, orderLHom_order]
  exact LHom.id_isExpansionOn M

instance model_preorder [Preorder M] : M ⊨ Language.order.preorderTheory := by
  simp only [preorderTheory, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, Relations.realize_reflexive, relMap_apply₂, forall_eq,
    Relations.realize_transitive]
  exact ⟨le_refl, fun _ _ _ => le_trans⟩

instance model_partialOrder [PartialOrder M] : M ⊨ Language.order.partialOrderTheory := by
  simp only [partialOrderTheory, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, Relations.realize_reflexive, relMap_apply₂, Relations.realize_antisymmetric,
    forall_eq, Relations.realize_transitive]
  exact ⟨le_refl, fun _ _ => le_antisymm, fun _ _ _ => le_trans⟩

instance model_linearOrder [LinearOrder M] : M ⊨ Language.order.linearOrderTheory := by
  simp only [linearOrderTheory, Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, Relations.realize_reflexive, relMap_apply₂, Relations.realize_antisymmetric,
    Relations.realize_transitive, forall_eq, Relations.realize_total]
  exact ⟨le_refl, fun _ _ => le_antisymm, fun _ _ _ => le_trans, le_total⟩

section OrderedStructure

variable [IsOrdered L] [L.Structure M]

@[simp]
theorem relMap_leSymb [LE M] [L.OrderedStructure M] {a b : M} :
    RelMap (leSymb : L.Relations 2) ![a, b] ↔ a ≤ b := by
  rw [← orderLHom_leSymb, LHom.map_onRelation]
  rfl

@[simp]
theorem Term.realize_le [LE M] [L.OrderedStructure M] {t₁ t₂ : L.Term (α ⊕ (Fin n))} {v : α → M}
    {xs : Fin n → M} :
    (t₁.le t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by
  simp [Term.le]

@[simp]
theorem Term.realize_lt [Preorder M] [L.OrderedStructure M] {t₁ t₂ : L.Term (α ⊕ (Fin n))}
    {v : α → M} {xs : Fin n → M} :
    (t₁.lt t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [Term.lt, lt_iff_le_not_le]

end OrderedStructure

section LE

variable [LE M]

theorem realize_noTopOrder_iff : M ⊨ Language.order.noTopOrderSentence ↔ NoTopOrder M := by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_le a

@[simp]
theorem realize_noTopOrder [h : NoTopOrder M] : M ⊨ Language.order.noTopOrderSentence :=
  realize_noTopOrder_iff.2 h

theorem realize_noBotOrder_iff : M ⊨ Language.order.noBotOrderSentence ↔ NoBotOrder M := by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_ge a

@[simp]
theorem realize_noBotOrder [h : NoBotOrder M] : M ⊨ Language.order.noBotOrderSentence :=
  realize_noBotOrder_iff.2 h

end LE

theorem realize_denselyOrdered_iff [Preorder M] :
    M ⊨ Language.order.denselyOrderedSentence ↔ DenselyOrdered M := by
  simp only [denselyOrderedSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, Term.realize, Term.realize_lt,
    Sum.elim_inr, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  refine ⟨fun h => ⟨fun a b ab => h a b ab⟩, ?_⟩
  intro h a b ab
  exact exists_between ab

@[simp]
theorem realize_denselyOrdered [Preorder M] [h : DenselyOrdered M] :
    M ⊨ Language.order.denselyOrderedSentence :=
  realize_denselyOrdered_iff.2 h

instance model_dlo [LinearOrder M] [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] :
    M ⊨ Language.order.dlo := by
  simp only [dlo, Set.union_insert, Set.union_singleton, Theory.model_iff, Set.mem_insert_iff,
    forall_eq_or_imp, realize_noTopOrder, realize_noBotOrder, realize_denselyOrdered,
    true_and_iff]
  rw [← Theory.model_iff]
  infer_instance

end Language

end FirstOrder
