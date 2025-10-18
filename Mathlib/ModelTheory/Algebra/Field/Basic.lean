/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Algebra.Ring.Basic
import Mathlib.Algebra.Field.MinimalAxioms
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# The First-Order Theory of Fields

This file defines the first-order theory of fields as a theory over the language of rings.

## Main definitions

- `FirstOrder.Language.Theory.field` : the theory of fields
- `FirstOrder.Model.fieldOfModelField` : a model of the theory of fields on a type `K` that
  already has ring operations.
- `FirstOrder.Model.compatibleRingOfModelField` : shows that the ring operations on `K` given
  by `fieldOfModelField` are compatible with the ring operations on `K` given by the
  `Language.ring.Structure` instance.
-/

variable {K : Type*}

namespace FirstOrder

namespace Field

open Language Ring Structure BoundedFormula

/-- An indexing type to name each of the field axioms. The theory
of fields is defined as the range of a function `FieldAxiom ->
Language.ring.Sentence` -/
inductive FieldAxiom : Type
  | addAssoc : FieldAxiom
  | zeroAdd : FieldAxiom
  | negAddCancel : FieldAxiom
  | mulAssoc : FieldAxiom
  | mulComm : FieldAxiom
  | oneMul : FieldAxiom
  | existsInv : FieldAxiom
  | leftDistrib : FieldAxiom
  | existsPairNE : FieldAxiom

/-- The first-order sentence corresponding to each field axiom -/
@[simp]
def FieldAxiom.toSentence : FieldAxiom → Language.ring.Sentence
  | .addAssoc => ∀' ∀' ∀' (((&0 + &1) + &2) =' (&0 + (&1 + &2)))
  | .zeroAdd => ∀' (((0 : Language.ring.Term _) + &0) =' &0)
  | .negAddCancel => ∀' ∀' ((-&0 + &0) =' 0)
  | .mulAssoc => ∀' ∀' ∀' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .mulComm => ∀' ∀' ((&0 * &1) =' (&1 * &0))
  | .oneMul => ∀' (((1 : Language.ring.Term _) * &0) =' &0)
  | .existsInv => ∀' (∼(&0 =' 0) ⟹ ∃' ((&0 * &1) =' 1))
  | .leftDistrib => ∀' ∀' ∀' ((&0 * (&1 + &2)) =' ((&0 * &1) + (&0 * &2)))
  | .existsPairNE => ∃' ∃' (∼(&0 =' &1))

/-- The Proposition corresponding to each field axiom -/
@[simp]
def FieldAxiom.toProp (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K] :
    FieldAxiom → Prop
  | .addAssoc => ∀ x y z : K, (x + y) + z = x + (y + z)
  | .zeroAdd => ∀ x : K, 0 + x = x
  | .negAddCancel => ∀ x : K, -x + x = 0
  | .mulAssoc => ∀ x y z : K, (x * y) * z = x * (y * z)
  | .mulComm => ∀ x y : K, x * y = y * x
  | .oneMul => ∀ x : K, 1 * x = x
  | .existsInv => ∀ x : K, x ≠ 0 → ∃ y, x * y = 1
  | .leftDistrib => ∀ x y z : K, x * (y + z) = x * y + x * z
  | .existsPairNE => ∃ x y : K, x ≠ y

/-- The first-order theory of fields, as a theory over the language of rings -/
def _root_.FirstOrder.Language.Theory.field : Language.ring.Theory :=
  Set.range FieldAxiom.toSentence

theorem FieldAxiom.realize_toSentence_iff_toProp {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    (ax : FieldAxiom) :
    (K ⊨ (ax.toSentence : Sentence Language.ring)) ↔ ax.toProp K := by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, Fin.snoc]

theorem FieldAxiom.toProp_of_model {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    [Theory.field.Model K] (ax : FieldAxiom) : ax.toProp K :=
  (FieldAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem Theory.field
      (Set.mem_range_self ax))

open FieldAxiom

/-- A model for the theory of fields is a field. To introduced locally on Types that don't
already have instances for ring operations.

When this is used, it is almost always useful to also add locally the instance
`compatibleFieldOfModelField` afterwards. -/
noncomputable abbrev fieldOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : Field K :=
  letI : DecidableEq K := Classical.decEq K
  letI := addOfRingStructure K
  letI := mulOfRingStructure K
  letI := negOfRingStructure K
  letI := zeroOfRingStructure K
  letI := oneOfRingStructure K
  letI := compatibleRingOfRingStructure K
  have exists_inv : ∀ x : K, x ≠ 0 → ∃ y : K, x * y = 1 :=
    existsInv.toProp_of_model
  letI : Inv K := ⟨fun x => if hx0 : x = 0 then 0 else Classical.choose (exists_inv x hx0)⟩
  Field.ofMinimalAxioms K
    addAssoc.toProp_of_model
    zeroAdd.toProp_of_model
    negAddCancel.toProp_of_model
    mulAssoc.toProp_of_model
    mulComm.toProp_of_model
    oneMul.toProp_of_model
    (fun x hx0 => show x * (dite _ _ _) = _ from
        (dif_neg hx0).symm ▸ Classical.choose_spec (existsInv.toProp_of_model x hx0))
    (dif_pos rfl)
    leftDistrib.toProp_of_model
    existsPairNE.toProp_of_model

section

attribute [local instance] fieldOfModelField

/-- The instances given by `fieldOfModelField` are compatible with the `Language.ring.Structure`
instance on `K`. This instance is to be used on models for the language of fields that do
not already have the ring operations on the Type.

Always add `fieldOfModelField` as a local instance first before using this instance.
-/
noncomputable abbrev compatibleRingOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : CompatibleRing K :=
  compatibleRingOfRingStructure K

end

instance [Field K] [CompatibleRing K] : Theory.field.Model K :=
  { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (K := K)]
      cases a with
      | existsPairNE => exact exists_pair_ne K
      | existsInv => exact fun x hx0 => ⟨x⁻¹, mul_inv_cancel₀ hx0⟩
      | addAssoc => exact add_assoc
      | zeroAdd => exact zero_add
      | negAddCancel => exact neg_add_cancel
      | mulAssoc => exact mul_assoc
      | mulComm => exact mul_comm
      | oneMul => exact one_mul
      | leftDistrib => exact mul_add }

end Field

end FirstOrder
