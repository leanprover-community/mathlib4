/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Zify

/-!
# The length function, reduced words, and descents

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

Given any element $w \in W$, its *length* (`CoxeterSystem.length`), denoted $\ell(w)$, is the
minimum number $\ell$ such that $w$ can be written as a product of a sequence of $\ell$ simple
reflections:
$$w = s_{i_1} \cdots s_{i_\ell}.$$
We prove for all $w_1, w_2 \in W$ that $\ell (w_1 w_2) \leq \ell (w_1) + \ell (w_2)$
and that $\ell (w_1 w_2)$ has the same parity as $\ell (w_1) + \ell (w_2)$.

We define a *reduced word* (`CoxeterSystem.IsReduced`) for an element $w \in W$ to be a way of
writing $w$ as a product of exactly $\ell(w)$ simple reflections. Every element of $W$ has a reduced
word.

We say that $i \in B$ is a *left descent* (`CoxeterSystem.IsLeftDescent`) of $w \in W$ if
$\ell(s_i w) < \ell(w)$. We show that if $i$ is a left descent of $w$, then
$\ell(s_i w) + 1 = \ell(w)$. On the other hand, if $i$ is not a left descent of $w$, then
$\ell(s_i w) = \ell(w) + 1$. We similarly define right descents (`CoxeterSystem.IsRightDescent`) and
prove analogous results.

## Main definitions

* `cs.length`
* `cs.IsReduced`
* `cs.IsLeftDescent`
* `cs.IsRightDescent`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd

/-! ### Length -/

private theorem exists_word_with_prod (w : W) : ∃ n ω, n = ω.length ∧ π ω = w := by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

open scoped Classical in
/-- The length of `w`; i.e., the minimum number of simple reflections that
must be multiplied to form `w`. -/
@[no_expose] noncomputable def length (w : W) : ℕ := Nat.find (cs.exists_word_with_prod w)

local prefix:100 "ℓ " => cs.length

/-- The proposition that `ω` is reduced; that is, it has minimal length among all words that
represent the same element of `W`. -/
def IsReduced (ω : List B) : Prop := ℓ (π ω) = ω.length

theorem IsReduced.eq {ω : List B} (hω : cs.IsReduced ω) : ℓ (π ω) = ω.length := hω

theorem exists_isReduced (w : W) : ∃ ω : List B, cs.IsReduced ω ∧ w = π ω := by
  classical
  obtain ⟨ω, hω, rfl⟩ := Nat.find_spec (cs.exists_word_with_prod w)
  exact ⟨ω, hω, rfl⟩

@[deprecated (since := "2026-03-25")] alias exists_reduced_word := exists_isReduced
@[deprecated (since := "2026-03-25")] alias exists_reduced_word' := exists_isReduced

open scoped Classical in
theorem length_wordProd_le (ω : List B) : ℓ (π ω) ≤ ω.length :=
  Nat.find_min' (cs.exists_word_with_prod (π ω)) ⟨ω, rfl, rfl⟩

@[simp] theorem length_one : ℓ (1 : W) = 0 := Nat.eq_zero_of_le_zero (cs.length_wordProd_le [])

@[simp]
theorem length_eq_zero_iff {w : W} : ℓ w = 0 ↔ w = 1 := by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have : ω = [] := eq_nil_of_length_eq_zero (hω.symm.trans h)
    rw [this, wordProd_nil]
  · rintro rfl
    exact cs.length_one

@[simp]
theorem length_inv (w : W) : ℓ (w⁻¹) = ℓ w := by
  apply Nat.le_antisymm
  · rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← hω] at this
  · rcases cs.exists_isReduced w⁻¹ with ⟨ω, hω, h'ω⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← h'ω, ← hω, inv_inv, ← h'ω] at this

theorem length_mul_le (w₁ w₂ : W) : ℓ (w₁ * w₂) ≤ ℓ w₁ + ℓ w₂ := by
  rcases cs.exists_isReduced w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases cs.exists_isReduced w₂ with ⟨ω₂, hω₂, rfl⟩
  have := cs.length_wordProd_le (ω₁ ++ ω₂)
  simpa [hω₁.eq, hω₂.eq, wordProd_append] using this

theorem length_le_length_mul_add_left (w₁ w₂ : W) : ℓ w₂ ≤ ℓ (w₁ * w₂) + ℓ w₁ := by
  simpa [add_comm] using cs.length_mul_le w₁⁻¹ (w₁ * w₂)

theorem length_le_length_mul_add_right (w₁ w₂ : W) : ℓ w₁ ≤ ℓ (w₁ * w₂) + ℓ w₂ := by
  simpa using cs.length_mul_le (w₁ * w₂) w₂⁻¹

@[deprecated length_le_length_mul_add_right (since := "2026-03-25")]
theorem length_mul_ge_length_sub_length (w₁ w₂ : W) : ℓ w₁ - ℓ w₂ ≤ ℓ (w₁ * w₂) := by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_right ..

@[deprecated length_le_length_mul_add_left (since := "2026-03-25")]
theorem length_mul_ge_length_sub_length' (w₁ w₂ : W) : ℓ w₂ - ℓ w₁ ≤ ℓ (w₁ * w₂) := by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_left ..

set_option linter.deprecated false in
@[deprecated "use `length_le_length_mul_add_left` and `length_le_length_mul_add_right"
(since := "2026-03-25")]
theorem length_mul_ge_max (w₁ w₂ : W) : max (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) ≤ ℓ (w₁ * w₂) :=
  max_le (length_mul_ge_length_sub_length ..) (length_mul_ge_length_sub_length' ..)

/-- The homomorphism that sends each element `w : W` to the parity of the length of `w`.
(See `lengthParity_eq_ofAdd_length`.) -/
def lengthParity : W →* Multiplicative (ZMod 2) := cs.lift ⟨fun _ ↦ Multiplicative.ofAdd 1, by
  simp_rw [CoxeterMatrix.IsLiftable, ← ofAdd_add, (by decide : (1 + 1 : ZMod 2) = 0)]
  simp⟩

theorem lengthParity_simple (i : B) :
    cs.lengthParity (s i) = Multiplicative.ofAdd 1 := cs.lift_apply_simple _ _

theorem lengthParity_comp_simple :
    cs.lengthParity ∘ cs.simple = fun _ ↦ Multiplicative.ofAdd 1 := funext cs.lengthParity_simple

theorem lengthParity_eq_ofAdd_length (w : W) :
    cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w)) := by
  rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
  rw [hω, wordProd, map_list_prod, List.map_map, lengthParity_comp_simple, map_const',
    prod_replicate, ← ofAdd_nsmul, nsmul_one]

theorem length_mul_mod_two (w₁ w₂ : W) : ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2 := by
  rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_add]
  simpa only [lengthParity_eq_ofAdd_length, ofAdd_add] using map_mul cs.lengthParity w₁ w₂

@[simp]
theorem length_simple (i : B) : ℓ (s i) = 1 := by
  apply Nat.le_antisymm
  · simpa using cs.length_wordProd_le [i]
  · by_contra! length_lt_one
    have : cs.lengthParity (s i) = Multiplicative.ofAdd 0 := by
      rw [lengthParity_eq_ofAdd_length, Nat.lt_one_iff.mp length_lt_one, Nat.cast_zero]
    have : Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd 1 :=
      this.symm.trans (cs.lengthParity_simple i)
    contradiction

theorem length_eq_one_iff {w : W} : ℓ w = 1 ↔ ∃ i : B, w = s i := by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    rcases List.length_eq_one_iff.mp (hω.symm.trans h) with ⟨i, rfl⟩
    exact ⟨i, cs.wordProd_singleton i⟩
  · rintro ⟨i, rfl⟩
    exact cs.length_simple i

theorem length_mul_simple_ne (w : W) (i : B) : ℓ (w * s i) ≠ ℓ w := by
  intro eq
  have length_mod_two := cs.length_mul_mod_two w (s i)
  rw [eq, length_simple] at length_mod_two
  lia

theorem length_simple_mul_ne (w : W) (i : B) : ℓ (s i * w) ≠ ℓ w := by
  rw [← length_inv]
  simpa using cs.length_mul_simple_ne w⁻¹ i

theorem length_mul_simple (w : W) (i : B) : ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w := by
  rcases (cs.length_mul_simple_ne w i).lt_or_gt with h | h <;> rw [← Nat.add_one_le_iff] at h
  · refine .inr (h.antisymm ?_)
    simpa using cs.length_le_length_mul_add_right w (s i)
  · refine .inl (h.antisymm' ?_)
    simpa using cs.length_mul_le w (s i)

theorem length_simple_mul (w : W) (i : B) : ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w := by
  have := cs.length_mul_simple w⁻¹ i
  rwa [(by simp : w⁻¹ * (s i) = ((s i) * w)⁻¹), length_inv, length_inv] at this

/-! ### Reduced words -/

@[simp]
theorem isReduced_reverse_iff (ω : List B) : cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω := by
  simp [IsReduced]

theorem IsReduced.reverse {cs : CoxeterSystem M W} {ω : List B}
    (hω : cs.IsReduced ω) : cs.IsReduced (ω.reverse) :=
  (cs.isReduced_reverse_iff ω).mpr hω


private theorem isReduced_take_and_drop {ω : List B} (hω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.take j) ∧ cs.IsReduced (ω.drop j) := by
  have h₁ : ℓ (π (ω.take j)) ≤ (ω.take j).length := cs.length_wordProd_le (ω.take j)
  have h₂ : ℓ (π (ω.drop j)) ≤ (ω.drop j).length := cs.length_wordProd_le (ω.drop j)
  have h₃ := calc
    (ω.take j).length + (ω.drop j).length
    _ = ω.length := by rw [← List.length_append, ω.take_append_drop j]
    _ = ℓ (π ω) := hω.symm
    _ = ℓ (π (ω.take j) * π (ω.drop j)) := by rw [← cs.wordProd_append, ω.take_append_drop j]
    _ ≤ ℓ (π (ω.take j)) + ℓ (π (ω.drop j)) := cs.length_mul_le _ _
  unfold IsReduced
  lia

theorem IsReduced.take {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.take j) :=
  (isReduced_take_and_drop _ hω _).1

theorem IsReduced.drop {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.drop j) :=
  (isReduced_take_and_drop _ hω _).2

theorem not_isReduced_alternatingWord (i i' : B) {m : ℕ} (hM : M i i' ≠ 0) (hm : m > M i i') :
    ¬cs.IsReduced (alternatingWord i i' m) := by
  induction hm with
  | refl => -- Base case; m = M i i' + 1
    suffices h : ℓ (π (alternatingWord i i' (M i i' + 1))) < M i i' + 1 by
      unfold IsReduced
      rw [Nat.succ_eq_add_one, length_alternatingWord]
      lia
    have : M i i' + 1 ≤ M i i' * 2 := by linarith [Nat.one_le_iff_ne_zero.mpr hM]
    rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' _ this]
    have : M i i' * 2 - (M i i' + 1) = M i i' - 1 := by lia
    rw [this]
    calc
      ℓ (π (alternatingWord i' i (M i i' - 1)))
      _ ≤ (alternatingWord i' i (M i i' - 1)).length := cs.length_wordProd_le _
      _ = M i i' - 1 := length_alternatingWord _ _ _
      _ ≤ M i i' := Nat.sub_le _ _
      _ < M i i' + 1 := Nat.lt_succ_self _
  | step m ih => -- Inductive step
    contrapose ih
    rw [alternatingWord_succ'] at ih
    apply IsReduced.drop (j := 1) at ih
    simpa using ih

/-! ### Descents -/

/-- The proposition that `i` is a left descent of `w`; that is, $\ell(s_i w) < \ell(w)$. -/
def IsLeftDescent (w : W) (i : B) : Prop := ℓ (s i * w) < ℓ w

/-- The proposition that `i` is a right descent of `w`; that is, $\ell(w s_i) < \ell(w)$. -/
def IsRightDescent (w : W) (i : B) : Prop := ℓ (w * s i) < ℓ w

theorem not_isLeftDescent_one (i : B) : ¬cs.IsLeftDescent 1 i := by simp [IsLeftDescent]

theorem not_isRightDescent_one (i : B) : ¬cs.IsRightDescent 1 i := by simp [IsRightDescent]

theorem isLeftDescent_inv_iff {w : W} {i : B} :
    cs.IsLeftDescent w⁻¹ i ↔ cs.IsRightDescent w i := by
  unfold IsLeftDescent IsRightDescent
  nth_rw 1 [← length_inv]
  simp

theorem isRightDescent_inv_iff {w : W} {i : B} :
    cs.IsRightDescent w⁻¹ i ↔ cs.IsLeftDescent w i := by
  simpa using (cs.isLeftDescent_inv_iff (w := w⁻¹)).symm

theorem exists_leftDescent_of_ne_one {w : W} (hw : w ≠ 1) : ∃ i : B, cs.IsLeftDescent w i := by
  rcases cs.exists_isReduced w with ⟨ω, h, rfl⟩
  have h₁ : ω ≠ [] := by rintro rfl; simp at hw
  rcases List.exists_cons_of_ne_nil h₁ with ⟨i, ω', rfl⟩
  use i
  rw [IsLeftDescent, h, wordProd_cons, simple_mul_simple_cancel_left]
  calc
    ℓ (π ω') ≤ ω'.length := cs.length_wordProd_le ω'
    _ < (i :: ω').length := by simp

theorem exists_rightDescent_of_ne_one {w : W} (hw : w ≠ 1) : ∃ i : B, cs.IsRightDescent w i := by
  simp only [← isLeftDescent_inv_iff]
  apply exists_leftDescent_of_ne_one
  simpa

theorem isLeftDescent_iff {w : W} {i : B} :
    cs.IsLeftDescent w i ↔ ℓ (s i * w) + 1 = ℓ w := by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_left (by lia)
  · lia

theorem not_isLeftDescent_iff {w : W} {i : B} :
    ¬cs.IsLeftDescent w i ↔ ℓ (s i * w) = ℓ w + 1 := by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_right (by lia)
  · lia

theorem isRightDescent_iff {w : W} {i : B} :
    cs.IsRightDescent w i ↔ ℓ (w * s i) + 1 = ℓ w := by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_left (by lia)
  · lia

theorem not_isRightDescent_iff {w : W} {i : B} :
    ¬cs.IsRightDescent w i ↔ ℓ (w * s i) = ℓ w + 1 := by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_right (by lia)
  · lia

theorem isLeftDescent_iff_not_isLeftDescent_mul {w : W} {i : B} :
    cs.IsLeftDescent w i ↔ ¬cs.IsLeftDescent (s i * w) i := by
  rw [isLeftDescent_iff, not_isLeftDescent_iff, simple_mul_simple_cancel_left]
  tauto

theorem isRightDescent_iff_not_isRightDescent_mul {w : W} {i : B} :
    cs.IsRightDescent w i ↔ ¬cs.IsRightDescent (w * s i) i := by
  rw [isRightDescent_iff, not_isRightDescent_iff, simple_mul_simple_cancel_right]
  tauto

end CoxeterSystem
