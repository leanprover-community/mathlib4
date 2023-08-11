/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.ModelTheory.Algebra.Field.FreeCommRing
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Prime

namespace FirstOrder

namespace Language

namespace field

noncomputable def eqZero (n : ℕ) : Language.field.Sentence :=
  Term.equal (termOfFreeCommRing n) 0

end field

open field

@[simp] theorem realize_eqZero {K : Type _} [CompatibleField K] (n : ℕ)
    (v : Empty → K) : (Formula.Realize (eqZero n) v) ↔ ((n : K) = 0) := by
    simp [eqZero, Term.realize]

def Theory.hasChar (p : ℕ) : Language.field.Theory :=
  if p = 0
  then (fun q => ∼(eqZero q)) '' {q : ℕ | q.Prime}
  else if p.Prime then {eqZero p}
  else {⊥}

theorem model_hasChar_of_charP {K : Type _} [CompatibleField K] {p : ℕ} [CharP K p] :
    (Theory.hasChar p).Model K := by
  rw [Theory.hasChar]
  cases CharP.char_is_prime_or_zero K p with
  | inl hp =>
    simp [hp.ne_zero, hp, Sentence.Realize]
  | inr hp =>
    subst hp
    simp only [ite_false, ite_true, Theory.model_iff, Set.mem_image, Set.mem_setOf_eq,
      Sentence.Realize, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Formula.realize_not, realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero]
    exact CharP.charP_to_charZero K


theorem charP_of_model_hasChar {K : Type _} [CompatibleField K]
    [h : (Theory.hasChar p).Model K] : CharP K p := by
  rw [Theory.hasChar] at h
  split_ifs at h with hp0 hp
  · subst hp0
    simp only [Theory.model_iff, Set.mem_image, Set.mem_setOf_eq, Sentence.Realize,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Formula.realize_not,
      realize_eqZero, ← CharZero.charZero_iff_forall_prime_ne_zero] at h
    refine CharP.ofCharZero K
  · simp only [Theory.model_iff, Set.mem_singleton_iff, Sentence.Realize, forall_eq,
      realize_eqZero, ← CharP.charP_iff_prime_eq_zero hp] at h
    exact h
  · simp [Sentence.Realize] at h

end Language

end FirstOrder
