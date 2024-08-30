/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.Fraisse

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

variable (L)

/-- A language is ordered if it has a symbol representing `≤`. -/
class IsOrdered (L : Language.{u, v}) where
  /-- The relation symbol representing `≤`. -/
  leSymb : L.Relations 2

export IsOrdered (leSymb)

variable {L}

instance : IsOrdered Language.order := ⟨.le⟩

lemma order.relation_eq_leSymb : {R : Language.order.Relations 2} → R = leSymb
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
def orderLHom : Language.order →ᴸ L where
  onRelation | _, .le => leSymb

@[simp]
lemma orderLHom_apply : (R : Language.order.Relations 2) → L.orderLHom.onRelation R = leSymb
  | .le => rfl

variable (M)

/-- A structure is ordered if its language has a `≤` symbol whose interpretation is -/
class OrderedStructure [LE M] [L.Structure M] : Prop where
  relMap_leSymb : ∀ (x : Fin 2 → M), RelMap (leSymb : L.Relations 2) x ↔ (x 0 ≤ x 1)

export OrderedStructure (relMap_leSymb)

attribute [simp] relMap_leSymb

instance [LE M] [L.Structure M] [L.OrderedStructure M]
    [Language.order.Structure M] [Language.order.OrderedStructure M] :
    LHom.IsExpansionOn (orderLHom L) M where
  map_onRelation := by simp [order.relation_eq_leSymb]
  map_onFunction := fun {n} => (IsRelational.empty_functions _).elim

end IsOrdered

@[simp]
theorem orderLHom_leSymb [L.IsOrdered] :
    (orderLHom L).onRelation leSymb = (leSymb : L.Relations 2) := rfl

@[simp]
theorem orderLHom_order : orderLHom Language.order = LHom.id Language.order :=
  LHom.funext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

instance sum.instIsOrdered : IsOrdered (L.sum Language.order) :=
  ⟨Sum.inr IsOrdered.leSymb⟩

/-- Any linearly-ordered type is naturally a structure in the language `Language.order`.
This is not an instance, because sometimes the `Language.order.Structure` is defined first. -/
def orderStructure [LE M] : Language.order.Structure M where
  RelMap | .le => (fun x => x 0 ≤ x 1)

section

variable (L) [IsOrdered L]

/-- The theory of preorders. -/
abbrev preorderTheory : L.Theory :=
  {leSymb.reflexive, leSymb.transitive}

instance : Theory.IsUniversal L.preorderTheory := ⟨by
  simp only [preorderTheory, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_reflexive, leSymb.isUniversal_transitive⟩⟩

/-- The theory of partial orders. -/
abbrev partialOrderTheory : L.Theory := insert leSymb.antisymmetric L.preorderTheory

instance : Theory.IsUniversal L.partialOrderTheory := ⟨by
  simp only [partialOrderTheory,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_antisymmetric, leSymb.isUniversal_reflexive,
    leSymb.isUniversal_transitive⟩⟩

/-- The theory of linear orders. -/
abbrev linearOrderTheory : L.Theory := insert leSymb.total L.partialOrderTheory

instance : Theory.IsUniversal L.linearOrderTheory := ⟨by
  simp only [linearOrderTheory,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨leSymb.isUniversal_total, leSymb.isUniversal_antisymmetric, leSymb.isUniversal_reflexive,
    leSymb.isUniversal_transitive⟩⟩

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
abbrev dlo : L.Theory :=
  L.linearOrderTheory ∪ {L.noTopOrderSentence, L.noBotOrderSentence, L.denselyOrderedSentence}

variable [L.Structure M]

instance [h : M ⊨ L.dlo] : M ⊨ L.linearOrderTheory := h.mono Set.subset_union_left

instance [h : M ⊨ L.linearOrderTheory] : M ⊨ L.partialOrderTheory := h.mono (Set.subset_insert _ _)

instance [h : M ⊨ L.partialOrderTheory] : M ⊨ L.preorderTheory := h.mono (Set.subset_insert _ _)

end

instance [IsOrdered L] [LE M] [Language.order.Structure M] [Language.order.OrderedStructure M]
    [L.Structure M] [(orderLHom L).IsExpansionOn M] : L.OrderedStructure M where
  relMap_leSymb := fun x => by
    rw [← orderLHom_apply L leSymb, LHom.IsExpansionOn.map_onRelation, relMap_leSymb]

@[simp]
theorem orderedStructure_iff [IsOrdered L] [LE M]
    [Language.order.Structure M] [Language.order.OrderedStructure M] [L.Structure M] :
    L.OrderedStructure M ↔ LHom.IsExpansionOn (orderLHom L) M :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

section models_from_orders

variable [L.IsOrdered] [L.Structure M]

instance model_preorder [Preorder M] [L.OrderedStructure M] :
    M ⊨ L.preorderTheory := by
  simp only [Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, Relations.realize_reflexive, relMap_apply₂, forall_eq,
    Relations.realize_transitive, relMap_leSymb]
  exact ⟨le_refl, fun _ _ _ => le_trans⟩

instance model_partialOrder [PartialOrder M] [L.OrderedStructure M] :
    M ⊨ L.partialOrderTheory := by
  simp only [Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, Relations.realize_reflexive, relMap_apply₂, Relations.realize_antisymmetric,
    forall_eq, Relations.realize_transitive, relMap_leSymb]
  exact ⟨fun _ _ => le_antisymm, le_refl, fun _ _ _ => le_trans⟩

instance model_linearOrder [LinearOrder M] [L.OrderedStructure M] :
    M ⊨ L.linearOrderTheory := by
  simp only [Theory.model_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, Relations.realize_reflexive, relMap_apply₂, Relations.realize_antisymmetric,
    Relations.realize_transitive, forall_eq, Relations.realize_total, relMap_leSymb]
  exact ⟨le_total, fun _ _ => le_antisymm, le_refl, fun _ _ _ => le_trans⟩

end models_from_orders

section orders_from_models

variable (L) [IsOrdered L] (M) [L.Structure M]

/-- Any structure in an ordered language can be ordered correspondingly. -/
abbrev leOfStructure : LE M where
  le := fun a b => Structure.RelMap (leSymb : L.Relations 2) ![a,b]

instance : @OrderedStructure L M _ (L.leOfStructure M) _ := by
  letI := L.leOfStructure M
  constructor
  simp only [Fin.forall_fin_succ_pi, Fin.cons_zero, Fin.forall_fin_zero_pi]
  intros
  rfl

instance [DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a,b])] :
    DecidableRel (@LE.le M (L.leOfStructure M)) := by
  letI := L.leOfStructure M
  infer_instance

/-- Any model of a theory of preorders is a preorder. -/
def preorderOfModels [h : M ⊨ L.preorderTheory] : Preorder M where
  __ := L.leOfStructure M
  le_refl := Relations.realize_reflexive.1 ((Theory.model_iff _).1 h _
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))
  le_trans := Relations.realize_transitive.1 ((Theory.model_iff _).1 h _
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]))

/-- Any model of a theory of partial orders is a partial order. -/
def partialOrderOfModels [h : M ⊨ L.partialOrderTheory] : PartialOrder M where
  __ := L.preorderOfModels M
  le_antisymm := Relations.realize_antisymmetric.1 ((Theory.model_iff _).1 h _
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))

/-- Any model of a theory of linear orders is a linear order. -/
def linearOrderOfModels [h : M ⊨ L.linearOrderTheory]
    [DecidableRel (fun (a b : M) => Structure.RelMap (leSymb : L.Relations 2) ![a,b])] :
    LinearOrder M where
  __ := L.partialOrderOfModels M
  le_total := Relations.realize_total.1 ((Theory.model_iff _).1 h _
    (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]))
  decidableLE := inferInstance

end orders_from_models

namespace Term

variable [IsOrdered L] [L.Structure M]

@[simp]
theorem realize_le [LE M] [L.OrderedStructure M] {t₁ t₂ : L.Term (α ⊕ (Fin n))} {v : α → M}
    {xs : Fin n → M} :
    (t₁.le t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) ≤ t₂.realize (Sum.elim v xs) := by
  simp [Term.le]

@[simp]
theorem realize_lt [Preorder M] [L.OrderedStructure M] {t₁ t₂ : L.Term (α ⊕ (Fin n))}
    {v : α → M} {xs : Fin n → M} :
    (t₁.lt t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) < t₂.realize (Sum.elim v xs) := by
  simp [Term.lt, lt_iff_le_not_le]

end Term

section LE

variable [L.IsOrdered] [L.Structure M] [LE M] [L.OrderedStructure M]

theorem realize_noTopOrder_iff : M ⊨ L.noTopOrderSentence ↔ NoTopOrder M := by
  simp only [noTopOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  exact ⟨fun h => ⟨fun a => h a⟩, fun h a => exists_not_le a⟩

@[simp]
theorem realize_noTopOrder [h : NoTopOrder M] : M ⊨ L.noTopOrderSentence :=
  realize_noTopOrder_iff.2 h

theorem realize_noBotOrder_iff : M ⊨ L.noBotOrderSentence ↔ NoBotOrder M := by
  simp only [noBotOrderSentence, Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_ex, BoundedFormula.realize_not, Term.realize, Term.realize_le,
    Sum.elim_inr]
  exact ⟨fun h => ⟨fun a => h a⟩, fun h a => exists_not_ge a⟩

@[simp]
theorem realize_noBotOrder [h : NoBotOrder M] : M ⊨ L.noBotOrderSentence :=
  realize_noBotOrder_iff.2 h

variable (L) (M)

theorem noTopOrder_of_dlo [h: M ⊨ L.dlo] : NoTopOrder M :=
  realize_noTopOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or]))

theorem noBotOrder_of_dlo [h: M ⊨ L.dlo] : NoBotOrder M :=
  realize_noBotOrder_iff.1 (L.dlo.realize_sentence_of_mem (by
    simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      true_or, or_true]))

end LE

section Preorder

variable [L.IsOrdered] [L.Structure M] [Preorder M] [L.OrderedStructure M]

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

instance model_dlo [L.IsOrdered] [L.Structure M] [LinearOrder M] [DenselyOrdered M]
    [NoTopOrder M] [NoBotOrder M] [L.OrderedStructure M] :
    M ⊨ L.dlo := by
  simp only [Set.union_insert, Set.union_singleton, Theory.model_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, realize_noTopOrder, realize_noBotOrder,
    realize_denselyOrdered, Relations.realize_total, relMap_leSymb, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Relations.realize_antisymmetric,
    Relations.realize_reflexive, forall_eq, Relations.realize_transitive, true_and]
  exact ⟨le_total, fun _ _ => le_antisymm, le_refl, fun _ _ _ => le_trans⟩

instance [Language.order.Structure M] [LE M] [Language.order.OrderedStructure M]
    {N : Type*} [Language.order.Structure N] [LE N] [Language.order.OrderedStructure N] :
    Language.order.StrongHomClass (M ↪o N) M N :=
  ⟨fun _ => (IsRelational.empty_functions _).elim,
    by simp only [order.forall_relations, order.relation_eq_leSymb, relMap_leSymb, Fin.isValue,
    Function.comp_apply, RelEmbedding.map_rel_iff, implies_true]⟩

lemma dlo_age (M : Type w)
    [Language.order.Structure M] [Mdlo : M ⊨ Language.order.dlo] [Infinite M] :
    Language.order.age M = {M : CategoryTheory.Bundled.{w} Language.order.Structure |
      Finite M ∧ M ⊨ Language.order.linearOrderTheory} := by
  classical
  rw [age]
  ext N
  refine ⟨fun ⟨hF, h⟩ => ⟨hF.finite, Theory.IsUniversal.models_of_embedding h.some⟩,
    fun ⟨hF, h⟩ => ⟨FG.of_finite, ?_⟩⟩
  letI := Language.order.linearOrderOfModels M
  letI := Language.order.linearOrderOfModels N
  exact ⟨StrongHomClass.toEmbedding (nonempty_orderEmbedding_of_finite_infinite N M).some⟩

end Language

end FirstOrder
