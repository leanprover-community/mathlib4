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
- `FirstOrder.Language.IsOrdered` points out a specific symbol in a language as representing `≤`.
- `FirstOrder.Language.OrderedStructure` indicates that the `≤` symbol in an ordered language
  is interpreted as the actual relation `≤` in a particular structure.
- `FirstOrder.Language.linearOrderTheory` and similar define the theories of preorders,
  partial orders, and linear orders.
- `FirstOrder.Language.dlo` defines the theory of dense linear orders without endpoints, a
  particularly useful example in model theory.
- `FirstOrder.Language.orderStructure` is the structure on an ordered type, assigning the symbol
  representing `≤` to the actual relation `≤`.
- Conversely, `FirstOrder.Language.LEOfStructure`, `FirstOrder.Language.preorderOfModels`,
  `FirstOrder.Language.partialOrderOfModels`, and `FirstOrder.Language.linearOrderOfModels`
  are the orders induced by first-order structures modelling the relevant theory.

## Main Results

- `PartialOrder`s model the theory of partial orders, `LinearOrder`s model the theory of
  linear orders, and dense linear orders without endpoints model `Language.dlo`.
-/


universe u v w w'

namespace FirstOrder

namespace Language

open FirstOrder Structure

variable {L : Language.{u, v}} {α : Type w} {M : Type w'} {n : ℕ}

/-- The type of relations for the language of orders, consisting of a single binary relation `le`.
-/
inductive orderRel : ℕ → Type
  | le : orderRel 2
  deriving DecidableEq

/-- The relational language consisting of a single relation representing `≤`. -/
protected def order : Language := ⟨fun _ => Empty, orderRel⟩
  deriving IsRelational

namespace order

@[simp]
lemma forall_relations {P : ∀ (n) (_ : Language.order.Relations n), Prop} :
    (∀ {n} (R), P n R) ↔ P 2 .le := ⟨fun h => h _, fun h n R =>
      match n, R with
      | 2, .le => h⟩

instance instSubsingleton : Subsingleton (Language.order.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

end order

/-- A language is ordered if it has a symbol representing `≤`. -/
class IsOrdered (L : Language.{u, v}) where
  /-- The relation symbol representing `≤`. -/
  leSymb : L.Relations 2

export IsOrdered (leSymb)

instance : IsOrdered Language.order :=
  ⟨.le⟩

lemma order.relation_eq_leSymb : (R : Language.order.Relations 2) → R = leSymb
  | .le => rfl

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
@[simps] def orderLHom : Language.order →ᴸ L where
  onRelation | _, .le => leSymb

@[simp]
theorem orderLHom_leSymb :
    (orderLHom L).onRelation leSymb = (leSymb : L.Relations 2) :=
  rfl

@[simp]
theorem orderLHom_order : orderLHom Language.order = LHom.id Language.order :=
  LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

/-- The theory of preorders. -/
def preorderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.transitive}

instance : Theory.IsUniversal L.preorderTheory := ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩

/-- The theory of partial orders. -/
def partialOrderTheory : L.Theory :=
  insert leSymb.antisymmetric L.preorderTheory

instance : Theory.IsUniversal L.partialOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_antisymmetric

/-- The theory of linear orders. -/
def linearOrderTheory : L.Theory :=
  insert leSymb.total L.partialOrderTheory

instance : Theory.IsUniversal L.linearOrderTheory :=
  Theory.IsUniversal.insert leSymb.isUniversal_total

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

variable [L.Structure M]

instance [h : M ⊨ L.dlo] : M ⊨ L.linearOrderTheory := h.mono Set.subset_union_left

instance [h : M ⊨ L.linearOrderTheory] : M ⊨ L.partialOrderTheory := h.mono (Set.subset_insert _ _)

instance [h : M ⊨ L.partialOrderTheory] : M ⊨ L.preorderTheory := h.mono (Set.subset_insert _ _)

end IsOrdered

instance sum.instIsOrdered : IsOrdered (L.sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

variable (L M)

/-- Any linearly-ordered type is naturally a structure in the language `Language.order`.
This is not an instance, because sometimes the `Language.order.Structure` is defined first. -/
def orderStructure [LE M] : Language.order.Structure M where
  RelMap | .le => (fun x => x 0 ≤ x 1)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is `≤`. -/
class OrderedStructure [L.IsOrdered] [LE M] [L.Structure M] : Prop where
  relMap_leSymb : ∀ (x : Fin 2 → M), RelMap (leSymb : L.Relations 2) x ↔ (x 0 ≤ x 1)

export OrderedStructure (relMap_leSymb)

attribute [simp] relMap_leSymb

variable {L M}

section order_to_structure

variable [IsOrdered L] [L.Structure M]

section LE

variable [LE M]

instance [Language.order.Structure M] [Language.order.OrderedStructure M]
    [(orderLHom L).IsExpansionOn M] : L.OrderedStructure M where
  relMap_leSymb x := by
    rw [← orderLHom_leSymb L, LHom.IsExpansionOn.map_onRelation, relMap_leSymb]

variable [L.OrderedStructure M]

instance [Language.order.Structure M] [Language.order.OrderedStructure M] :
    LHom.IsExpansionOn (orderLHom L) M where
  map_onRelation := by simp [order.relation_eq_leSymb]

@[simp]
theorem Term.realize_le {t₁ t₂ : L.Term (α ⊕ (Fin n))} {v : α → M}
    {xs : Fin n → M} :
    (t₁.le t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by
  simp [Term.le]

theorem realize_noTopOrder_iff : M ⊨ L.noTopOrderSentence ↔ NoTopOrder M := by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_le a

theorem realize_noBotOrder_iff : M ⊨ L.noBotOrderSentence ↔ NoBotOrder M := by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  refine ⟨fun h => ⟨fun a => h a⟩, ?_⟩
  intro h a
  exact exists_not_ge a

variable (L)

@[simp]
theorem realize_noTopOrder [h : NoTopOrder M] : M ⊨ L.noTopOrderSentence :=
  realize_noTopOrder_iff.2 h

@[simp]
theorem realize_noBotOrder [h : NoBotOrder M] : M ⊨ L.noBotOrderSentence :=
  realize_noBotOrder_iff.2 h

end LE

@[simp]
theorem orderedStructure_iff
    [LE M] [Language.order.Structure M] [Language.order.OrderedStructure M] :
    L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

section Preorder

variable [Preorder M] [L.OrderedStructure M]

instance model_preorder : M ⊨ L.preorderTheory := by
  simp only [preorderTheory, Theory.model_insert_iff, Relations.realize_reflexive, relMap_leSymb,
    Theory.model_singleton_iff, Relations.realize_transitive]
  exact ⟨le_refl, fun _ _ _ => le_trans⟩

@[simp]
theorem Term.realize_lt {t₁ t₂ : L.Term (α ⊕ (Fin n))}
    {v : α → M} {xs : Fin n → M} :
    (t₁.lt t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [Term.lt, lt_iff_le_not_le]

theorem realize_denselyOrdered_iff :
    M ⊨ L.denselyOrderedSentence ↔ DenselyOrdered M := by
  simp only [denselyOrderedSentence, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_imp, BoundedFormula.realize_all, Term.realize, Term.realize_lt,
    Sum.elim_inr, BoundedFormula.realize_ex, BoundedFormula.realize_inf]
  refine ⟨fun h => ⟨fun a b ab => h a b ab⟩, ?_⟩
  intro h a b ab
  exact exists_between ab

@[simp]
theorem realize_denselyOrdered [h : DenselyOrdered M] :
    M ⊨ L.denselyOrderedSentence :=
  realize_denselyOrdered_iff.2 h

end Preorder

instance model_partialOrder [PartialOrder M] [L.OrderedStructure M] :
    M ⊨ L.partialOrderTheory := by
  simp only [partialOrderTheory, Theory.model_insert_iff, Relations.realize_antisymmetric,
    relMap_leSymb, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    model_preorder, and_true]
  exact fun _ _ => le_antisymm

section LinearOrder

variable [LinearOrder M] [L.OrderedStructure M]

instance model_linearOrder : M ⊨ L.linearOrderTheory := by
  simp only [linearOrderTheory, Theory.model_insert_iff, Relations.realize_total, relMap_leSymb,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, model_partialOrder,
    and_true]
  exact le_total

instance model_dlo [DenselyOrdered M] [NoTopOrder M] [NoBotOrder M] :
    M ⊨ L.dlo := by
  simp [dlo, model_linearOrder, Theory.model_insert_iff]

end LinearOrder

end order_to_structure

section structure_to_order

variable (L) [IsOrdered L] (M) [L.Structure M]

/-- Any structure in an ordered language can be ordered correspondingly. -/
def leOfStructure : LE M where
  le a b := Structure.RelMap (leSymb : L.Relations 2) ![a,b]

instance : @OrderedStructure L M _ (L.leOfStructure M) _ := by
  letI := L.leOfStructure M
  constructor
  simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
  intros
  rfl

instance [h : DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a,b])] :
    DecidableRel (@LE.le M (L.leOfStructure M)) := by
  letI := L.leOfStructure M
  exact h

/-- Any model of a theory of preorders is a preorder. -/
def preorderOfModels [h : M ⊨ L.preorderTheory] : Preorder M where
  __ := L.leOfStructure M
  le_refl := Relations.realize_reflexive.1 ((Theory.model_iff _).1 h _
    (by simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))
  le_trans := Relations.realize_transitive.1 ((Theory.model_iff _).1 h _
    (by simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, or_true]))

/-- Any model of a theory of partial orders is a partial order. -/
def partialOrderOfModels [h : M ⊨ L.partialOrderTheory] : PartialOrder M where
  __ := L.preorderOfModels M
  le_antisymm := Relations.realize_antisymmetric.1 ((Theory.model_iff _).1 h _
    (by simp only [partialOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))

/-- Any model of a theory of linear orders is a linear order. -/
def linearOrderOfModels [h : M ⊨ L.linearOrderTheory]
    [DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a,b])] :
    LinearOrder M where
  __ := L.partialOrderOfModels M
  le_total := Relations.realize_total.1 ((Theory.model_iff _).1 h _
    (by simp only [linearOrderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))
  decidableLE := inferInstance

end structure_to_order

end Language

end FirstOrder
