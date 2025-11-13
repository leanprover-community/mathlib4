/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.CharP.Basic
import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing
import Mathlib.ModelTheory.Algebra.Field.Basic

/-!
# First-order theory of fields

This file defines the first-order theory of fields of characteristic `p` as a theory over the
language of rings

## Main definitions

- `FirstOrder.Language.Theory.fieldOfChar` : the first-order theory of fields of characteristic `p`
  as a theory over the language of rings
-/

variable {p : ℕ} {K : Type*}

namespace FirstOrder

namespace Field

open Language Ring

/-- For a given natural number `n`, `eqZero n` is the sentence in the language of rings
saying that `n` is zero. -/
noncomputable def eqZero (n : ℕ) : Language.ring.Sentence :=
  Term.equal (termOfFreeCommRing n) 0

@[simp] theorem realize_eqZero [CommRing K] [CompatibleRing K] (n : ℕ)
    (v : Empty → K) : (Formula.Realize (eqZero n) v) ↔ ((n : K) = 0) := by
  simp [eqZero]

/-- The first-order theory of fields of characteristic `p` as a theory over the language of rings -/
def _root_.FirstOrder.Language.Theory.fieldOfChar (p : ℕ) : Language.ring.Theory :=
  Theory.field ∪
  if p = 0
  then (fun q => ∼(eqZero q)) '' {q : ℕ | q.Prime}
  else if p.Prime then {eqZero p}
  else {⊥}

instance model_hasChar_of_charP [Field K] [CompatibleRing K] [CharP K p] :
    (Theory.fieldOfChar p).Model K := by
  refine Language.Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  cases CharP.char_is_prime_or_zero K p with
  | inl hp =>
    simp [hp.ne_zero, hp, Sentence.Realize]
  | inr hp =>
    subst hp
    simp only [ite_true, Theory.model_iff, Set.mem_image, Set.mem_setOf_eq,
      Sentence.Realize, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Formula.realize_not, realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero]
    exact CharP.charP_to_charZero K

theorem charP_iff_model_fieldOfChar [Field K] [CompatibleRing K] :
    (Theory.fieldOfChar p).Model K ↔ CharP K p := by
  simp only [Theory.fieldOfChar, Theory.model_union_iff,
    (show (Theory.field.Model K) by infer_instance), true_and]
  split_ifs with hp0 hp
  · subst hp0
    simp only [Theory.model_iff, Set.mem_image, Set.mem_setOf_eq, Sentence.Realize,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Formula.realize_not,
      realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero]
    exact ⟨fun _ => CharP.ofCharZero _, fun _ => CharP.charP_to_charZero K⟩
  · simp only [Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize, forall_eq,
      realize_eqZero, ← CharP.charP_iff_prime_eq_zero hp]
  · simp only [Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize,
      forall_eq, Formula.realize_bot, false_iff]
    intro H
    cases (CharP.char_is_prime_or_zero K p) <;> simp_all

instance model_fieldOfChar_of_charP [Field K] [CompatibleRing K]
    [CharP K p] : (Theory.fieldOfChar p).Model K :=
  charP_iff_model_fieldOfChar.2 inferInstance

variable (p) (K)
/- Not an instance because it caused performance problems in a different file. -/
theorem charP_of_model_fieldOfChar [Field K] [CompatibleRing K]
    [h : (Theory.fieldOfChar p).Model K] : CharP K p :=
  charP_iff_model_fieldOfChar.1 h

end Field

end FirstOrder
