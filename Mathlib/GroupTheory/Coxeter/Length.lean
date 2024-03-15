/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group

/-!
# The length function, reduced words, reflections, inversions, and inversion sequences
Throughout this file, `B` is a type and `M : Matrix B B ℕ` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* Matrix.CoxeterGroup M`, where `Matrix.CoxeterGroup M` refers to
the quotient of the free group on `B` by the Coxeter relations given by the matrix `M`. See
`Mathlib.GroupTheory.Coxeter.Basic` for more details.

We define the length function $\ell : W → \mathbb{N}$, and we prove that
$\ell (w_1 w_2) \leq \ell (w_1) + \ell (w_2)$
and that $\ell (w_1 w_2)$ and $\ell (w_1) + \ell (w_2)$ have the same parity.

We define a *reduced word* for an element $w \in W$ to be a way of writing $w$ as a product
of exactly $\ell(w)$ simple reflections. We define a *reflection* to be an element of the form
$t = u s_i u^{-1}$, where $u \in W$ and $s_i$ is a simple reflection. We say that a reflection $t$
is a *left inversion* of an element $w \in W$ if $\ell(t w) < \ell (w)$, and we say it is a
*right inversion* of $w$ if $\ell(w t) > \ell(w)$.

Given a word, we define its *left inversion sequence* and its *right inversion sequence*. We prove
that if a word is reduced, then both of its inversion sequences contain no duplicates.
In fact, the right (respectively, left) inversion sequence of a reduced word for $w$ consists of all
of the right (respectively, left) inversions of $w$ in some order, but we do not prove that in this
file.

## Main definitions
* `cs.length`
* `cs.IsReflection`
* `cs.IsLeftInversion`
* `cs.IsRightInversion`
* `cs.leftInvSeq`
* `cs.rightInvSeq`

## References
* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*][bjorner2005]
-/

noncomputable section

namespace CoxeterSystem

open List Matrix Function

variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simpleReflection
local prefix:100 "π" => cs.wordProd

/-! ### Length -/

local instance (w : W) : DecidablePred (fun n ↦ ∃ ω : List B, ω.length = n ∧ π ω = w) :=
  Classical.decPred _

private theorem exists_word_with_prod (w : W) : ∃ n : ℕ, ∃ ω : List B, ω.length = n ∧ π ω = w := by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

/-- The length of `w`; i.e., the minimum number of simple reflections that
must be multiplied to form `w`. -/
def length (w : W) : ℕ := Nat.find (cs.exists_word_with_prod w)
local prefix:100 "ℓ" => cs.length

theorem exists_reduced_word (w : W) : ∃ ω : List B, ω.length = ℓ w ∧ w = π ω := by
  have := Nat.find_spec (cs.exists_word_with_prod w)
  tauto

theorem length_wordProd_le (ω : List B) : ℓ (π ω) ≤ ω.length := by
  apply Nat.find_min' (cs.exists_word_with_prod (π ω))
  use ω

@[simp] theorem length_one : ℓ (1 : W) = 0 := Nat.eq_zero_of_le_zero (cs.length_wordProd_le [])

theorem length_eq_zero_iff {w : W} : ℓ w = 0 ↔ w = 1 := by
  constructor
  · intro h
    rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
    have : ω = [] := eq_nil_of_length_eq_zero (hω.trans h)
    rw [this]
    simp
  · rintro rfl
    exact cs.length_one

@[simp] theorem length_inv (w : W) : ℓ (w⁻¹) = ℓ w := by
  apply Nat.le_antisymm
  · rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
    have := cs.length_wordProd_le (List.reverse ω)
    simp at this
    rwa [hω] at this
  · rcases cs.exists_reduced_word w⁻¹ with ⟨ω, hω, h'ω⟩
    have := cs.length_wordProd_le (List.reverse ω)
    simp at this
    rwa [← h'ω, hω, inv_inv] at this

theorem length_mul_le (w₁ w₂ : W) :
    ℓ (w₁ * w₂) ≤ ℓ w₁ + ℓ w₂ := by
  rcases cs.exists_reduced_word w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases cs.exists_reduced_word w₂ with ⟨ω₂, hω₂, rfl⟩
  have := cs.length_wordProd_le (ω₁ ++ ω₂)
  simp at this
  rwa [hω₁, hω₂] at this

theorem length_mul_ge (w₁ w₂ : W) :
    ℓ (w₁ * w₂) ≥ max (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) := by
  apply max_le_iff.mpr
  constructor
  · apply Nat.sub_le_of_le_add
    have := cs.length_mul_le (w₁ * w₂) w₂⁻¹
    simp at this
    assumption
  · apply Nat.sub_le_of_le_add
    have := cs.length_mul_le (w₁ * w₂)⁻¹ w₁
    simp only [length_inv] at this
    simp at this
    assumption

private def lengthParity (cs : CoxeterSystem M W) : W →* Multiplicative (ZMod 2) := cs.lift (
    show IsLiftable M (fun _ ↦ Multiplicative.ofAdd 1) by
      intro i i'
      dsimp
      rw [← ofAdd_add, one_add_one_eq_two, (by decide : (2 : ZMod 2) = 0)]
      simp
  )

private theorem lengthParity_simple :
    ⇑(CoxeterSystem.lengthParity cs) ∘ simpleReflection cs = fun _ ↦ Multiplicative.ofAdd 1 := by
  ext x
  dsimp
  rw [lengthParity, lift_apply_simple]

private theorem parity_length_eq' (w : W) :
    Multiplicative.toAdd (cs.lengthParity w) = ((↑) : ℕ → ZMod 2) (ℓ w) := by
  rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
  nth_rw 1 [wordProd]
  rw [MonoidHom.map_list_prod, List.map_map, lengthParity_simple,
      map_const', prod_replicate, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
  tauto

theorem length_mul_mod_two (w₁ w₂ : W) : ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2 := by
  rw [← ZMod.nat_cast_eq_nat_cast_iff']
  rw [(by simp : (↑(length cs w₁ + length cs w₂) : ZMod 2) = ↑(length cs w₁) + ↑(length cs w₂))]
  repeat rw [← parity_length_eq']
  simp

@[simp] theorem length_simple (i : B) : ℓ (s i) = 1 := by
  apply Nat.le_antisymm
  · show length cs (s i) ≤ 1
    have := cs.length_wordProd_le [i]
    simp at this
    tauto
  · show 1 ≤ length cs (s i)
    by_contra! length_lt_1
    have := congrArg Multiplicative.toAdd (congrFun cs.lengthParity_simple i)
    simp [parity_length_eq'] at this
    rw [Nat.lt_one_iff.mp length_lt_1] at this
    contradiction

theorem length_eq_one_iff {w : W} : ℓ w = 1 ↔ ∃ i : B, w = s i := by
  constructor
  · intro h
    rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
    rcases List.length_eq_one.mp (hω.trans h) with ⟨i, rfl⟩
    use i
    simp
  · rintro ⟨i, rfl⟩
    exact cs.length_simple i

theorem length_mul_simple (w : W) (i : B) :
    ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w := by
  rcases Nat.lt_trichotomy (ℓ (w * s i)) (ℓ w) with lt | eq | gt
  · -- lt : ℓ (w * s i) < ℓ w
    right
    have length_ge := (max_le_iff.mp (cs.length_mul_ge w (s i))).left
    simp at length_ge
    -- length_ge : ℓ w ≤ ℓ (w * s i) + 1
    linarith
  · -- eq : ℓ (w * s i) = ℓ w
    have length_mod_two := cs.length_mul_mod_two w (s i)
    rw [eq] at length_mod_two
    simp at length_mod_two
    -- length_mod_two : (ℓ w) % 2 = (ℓ w + 1) % 2
    rcases Nat.mod_two_eq_zero_or_one (ℓ w) with even | odd
    · rw [even, Nat.succ_mod_two_eq_one_iff.mpr even] at length_mod_two
      contradiction
    · rw [odd, Nat.succ_mod_two_eq_zero_iff.mpr odd] at length_mod_two
      contradiction
  · -- gt : ℓ w < ℓ (w * s i)
    left
    have length_le := cs.length_mul_le w (s i)
    simp at length_le
    -- length_le : ℓ (w * s i) ≤ ℓ w + 1
    linarith

theorem length_simple_mul (w : W) (i : B) :
    ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w := by
  have := cs.length_mul_simple w⁻¹ i
  rwa [(by simp : w⁻¹ * (s i) = ((s i) * w)⁻¹), length_inv, length_inv] at this

/-- The word of length `m` that alternates between `i` and `i'`, ending with `i'`.-/
def alternatingWord (i i' : B) (m : ℕ) : List B :=
  match m with
  | 0    => []
  | m+1  => (alternatingWord i' i m).concat i'

theorem alternatingWord_succ (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (alternatingWord i' i m).concat i' := by
  rfl

theorem alternatingWord_succ' (i i' : B) (m : ℕ) :
    alternatingWord i i' (m + 1) = (if Even m then i' else i) :: alternatingWord i i' m := by
  induction' m with m ih generalizing i i'
  · simp [alternatingWord]
  · rw [alternatingWord]
    nth_rw 1 [ih i' i]
    rw [alternatingWord]
    simp [Nat.even_add_one]

@[simp] theorem length_alternatingWord (i i' : B) (m : ℕ) :
    List.length (alternatingWord i i' m) = m := by
  induction' m with m ih generalizing i i'
  · dsimp [alternatingWord]
  · simp [alternatingWord]
    exact ih i' i

theorem prod_alternatingWord_eq_pow (i i' : B) (m : ℕ) :
    π (alternatingWord i i' m) = (if Even m then 1 else s i') * (s i * s i') ^ (m / 2) := by
  induction' m with m ih
  · simp [alternatingWord]
  · rw [alternatingWord_succ', wordProd_cons, ih, Nat.succ_eq_add_one]
    rcases Nat.even_or_odd m with even | odd
    · rcases even with ⟨k, rfl⟩
      ring_nf
      have : Odd (1 + k * 2) := by use k; ring
      simp [← two_mul, Nat.odd_iff_not_even.mp this]
      rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
      norm_num
    · rcases odd with ⟨k, rfl⟩
      ring_nf
      have h₁ : Odd (1 + k * 2) := by use k; ring
      have h₂ : Even (2 + k * 2) := by use (k + 1); ring
      simp [Nat.odd_iff_not_even.mp h₁, h₂]
      rw [Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
      norm_num
      rw [pow_succ, mul_assoc]

theorem prod_alternatingWord_eq_prod_alternatingWord (i i' : B) (m : ℕ) (hm : m ≤ M i i' * 2) :
    π (alternatingWord i i' m) = π (alternatingWord i' i (M i i' * 2 - m)) := by
  rw [prod_alternatingWord_eq_pow, prod_alternatingWord_eq_pow]
  simp_rw [← Int.even_coe_nat]
  -- Rewrite everything in terms of an integer m' which is equal to m.
  rw [← zpow_coe_nat, ← zpow_coe_nat, Int.ofNat_ediv, Int.ofNat_ediv, Int.ofNat_sub hm]
  let m' : ℤ := m
  rw [← (by rfl : m' = m)]
  -- The resulting equation holds for all integers m'.
  generalize m' = m'

  rw [Int.ofNat_mul, (by norm_num : (↑(2 : ℕ) : ℤ) = 2)]
  clear hm

  rcases Int.even_or_odd m' with even | odd
  · rcases even with ⟨k, rfl⟩
    ring_nf
    have : Even (k * 2) := by use k; ring
    rw [if_pos this]
    have : Even (-(k * 2) + ↑(M i i') * 2) := by use -k + (M i i'); ring
    rw [if_pos this]
    rw [(by ring : -(k * 2) + ↑(M i i') * 2 = (-k + ↑(M i i')) * 2)]
    rw [Int.mul_ediv_cancel _ (by norm_num), Int.mul_ediv_cancel _ (by norm_num)]
    rw [zpow_add, zpow_coe_nat]
    rw [simple_mul_pow']
    rw [zpow_neg, ← inv_zpow]
    simp
  · rcases odd with ⟨k, rfl⟩
    ring_nf
    have : ¬Even (1 + k * 2) := by apply Int.odd_iff_not_even.mp; use k; ring
    rw [if_neg this]
    have : ¬Even (-1 - k * 2 + ↑(M i i') * 2) := by
      apply Int.odd_iff_not_even.mp
      use ↑(M i i') - k - 1
      ring
    rw [if_neg this]
    rw [(by ring : -1 - k * 2 + ↑(M i i') * 2 = -1 + (-k + ↑(M i i')) * 2)]
    rw [Int.add_mul_ediv_right _ _ (by norm_num), Int.add_mul_ediv_right _ _ (by norm_num)]
    norm_num
    rw [zpow_add, zpow_add, zpow_coe_nat]
    rw [simple_mul_pow']
    rw [zpow_neg, ← inv_zpow, zpow_neg, ← inv_zpow]
    simp [← mul_assoc]

/-! ### Reduced words -/

def IsReduced (ω : List B) : Prop := ℓ (π ω) = ω.length

@[simp] theorem isReduced_reverse (ω : List B) : cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω := by
  simp [IsReduced]

theorem exists_reduced_word' (w : W) : ∃ ω : List B, cs.IsReduced ω ∧ w = π ω := by
  rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
  use ω
  tauto

private theorem isReduced_take_and_drop {ω : List B} (rω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.take j) ∧ cs.IsReduced (ω.drop j) := by
  have take_append_drop : ω = ω.take j ++ ω.drop j           := (List.take_append_drop _ _).symm
  have mul_take_drop : π ω = π (ω.take j) * π (ω.drop j)     := by
    rw [← wordProd_append]
    nth_rw 1 [take_append_drop]

  have take_length : ℓ (π (ω.take j)) ≤ (ω.take j).length    := cs.length_wordProd_le (ω.take j)
  have drop_length : ℓ (π (ω.drop j)) ≤ (ω.drop j).length    := cs.length_wordProd_le (ω.drop j)

  have length_add_ge := calc
    ℓ (π (ω.take j)) + ℓ (π (ω.drop j))
    _ ≥ ℓ (π ω)                                              := by
        rw [mul_take_drop]
        exact cs.length_mul_le _ _
    _ = ω.length                                             := rω
    _ = (ω.take j).length + (ω.drop j).length                := by
        nth_rw 1 [take_append_drop]
        exact List.length_append _ _

  constructor
  · unfold IsReduced
    linarith
  · unfold IsReduced
    linarith

theorem isReduced_take {ω : List B} (rω : cs.IsReduced ω) (j : ℕ) : cs.IsReduced (ω.take j) :=
  (isReduced_take_and_drop _ rω _).1

theorem isReduced_drop {ω : List B} (rω : cs.IsReduced ω) (j : ℕ) : cs.IsReduced (ω.drop j) :=
  (isReduced_take_and_drop _ rω _).2

theorem not_isReduced_alternatingWord (i i' : B) (m : ℕ) (hM : M i i' ≠ 0) (hm : m > M i i') :
    ¬ cs.IsReduced (alternatingWord i i' m) := by
  induction' hm with m _ ih
  · -- Base case; m = M i i' + 1
    suffices h : ℓ (π (alternatingWord i i' (M i i' + 1))) < M i i' + 1 by
      unfold IsReduced
      rw [Nat.succ_eq_add_one, length_alternatingWord]
      linarith
    have : M i i' + 1 ≤ M i i' * 2 := by linarith [Nat.one_le_iff_ne_zero.mpr hM]
    rw [cs.prod_alternatingWord_eq_prod_alternatingWord i i' _ this]

    have : M i i' * 2 - (M i i' + 1) = M i i' - 1 := by
      apply (Nat.sub_eq_iff_eq_add' this).mpr
      rw [add_assoc, add_comm 1, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM)]
      exact mul_two _
    rw [this]

    calc
      ℓ (π (alternatingWord i' i (M i i' - 1)))
      _ ≤ (alternatingWord i' i (M i i' - 1)).length  := cs.length_wordProd_le _
      _ = M i i' - 1                                  := length_alternatingWord _ _ _
      _ ≤ M i i'                                      := Nat.sub_le _ _
      _ < M i i' + 1                                  := Nat.lt_succ_self _
  · -- Inductive step
    contrapose! ih
    rw [alternatingWord_succ'] at ih
    apply isReduced_drop (j := 1) at ih
    simp at ih
    assumption

/-! ### Reflections, inversions, and inversion sequences -/

/-- The proposition that `t` is a reflection of the Coxeter system `cs`; i.e., it is of the form
$w s_i w^{-1}$, where $w \in W$ and $s_i$ is a simple reflection. -/
def IsReflection (t : W) : Prop := ∃ w : W, ∃ i : B, t = w * s i * w⁻¹

def reflections : Set W := {t : W | cs.IsReflection t}

theorem isReflection_simple (i : B) : cs.IsReflection (s i) := by use 1, i; simp

theorem pow_two_eq_one_of_isReflection {t : W} (rt : cs.IsReflection t) : t ^ 2 = 1 := by
  rcases rt with ⟨w, i, rfl⟩
  rw [pow_two]
  group
  rw [mul_assoc w]
  simp

theorem inv_reflection_eq {t : W} (rt : cs.IsReflection t) : t⁻¹ = t := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two]
  exact cs.pow_two_eq_one_of_isReflection rt

alias inv_eq_self_of_isReflection := inv_reflection_eq

theorem length_reflection_odd {t : W} (rt : cs.IsReflection t) : Odd (ℓ t) := by
  rw [Nat.odd_iff]
  rcases rt with ⟨w, i, rfl⟩
  rw [length_mul_mod_two, Nat.add_mod, length_mul_mod_two, ← Nat.add_mod,
      length_simple, length_inv, add_comm, ← add_assoc, ← two_mul, Nat.mul_add_mod]
  norm_num

alias odd_length_of_isReflection := length_reflection_odd

theorem isReflection_conjugate_iff (w t : W) :
    cs.IsReflection (w * t * w⁻¹) ↔ cs.IsReflection t := by
  constructor
  · rintro ⟨u, i, hi⟩
    use w⁻¹ * u, i
    rw [mul_inv_rev (w⁻¹) u, inv_inv, ← mul_assoc]
    repeat rw [mul_assoc w⁻¹]
    rw [← hi]
    group
  · rintro ⟨u, i, rfl⟩
    use w * u, i
    group

/-- The proposition that `t` is a right inversion of `w`; i.e., `t` is a reflection and
$\ell (w t) < \ell(w)$. -/
def IsRightInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (w * t) < ℓ w
/-- The proposition that `t` is a left inversion of `w`; i.e., `t` is a reflection and
$\ell (t w) < \ell(w)$. -/
def IsLeftInversion (w t : W) : Prop := cs.IsReflection t ∧ ℓ (t * w) < ℓ w

/-- The right inversion sequence of `ω`. The right inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_\ell}\cdots s_{i_1}\cdots s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_{\ell - 2}}s_{i_{\ell - 1}}s_{i_\ell}, \ldots,
    s_{i_{\ell}}s_{i_{\ell - 1}}s_{i_\ell}, s_{i_\ell}.$$
-/
def rightInvSeq (ω : List B) : List W :=
  match ω with
  | []          => []
  | i :: ω      => (π ω)⁻¹ * (s i) * (π ω) :: rightInvSeq ω

/-- The left inversion sequence of `ω`. The left inversion sequence of a word
$s_{i_1} \cdots s_{i_\ell}$ is the sequence
$$s_{i_1}, s_{i_1}s_{i_2}s_{i_1}, s_{i_1}s_{i_2}s_{i_3}s_{i_2}s_{i_1}, \ldots,
    s_{i_1}\cdots s_{i_\ell}\cdots s_{i_1}.$$
-/
def leftInvSeq (ω : List B) : List W :=
  match ω with
  | []          => []
  | i :: ω      => s i :: List.map (MulAut.conj (s i)) (leftInvSeq ω)

local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq

@[simp] theorem rightInvSeq_nil : ris [] = [] := rfl
@[simp] theorem leftInvSeq_nil : lis [] = [] := rfl
@[simp] theorem rightInvSeq_singleton (i : B) : ris [i] = [s i] := by simp [rightInvSeq]
@[simp] theorem leftInvSeq_singleton (i : B) : lis [i] = [s i] := rfl

theorem rightInvSeq_concat (ω : List B) (i : B) :
    ris (ω.concat i) = (List.map (MulAut.conj (s i)) (ris ω)).concat (s i) := by
  induction' ω with j ω ih
  · simp
  · dsimp [rightInvSeq]
    rw [ih]
    simp only [concat_eq_append, wordProd_append, wordProd_cons, wordProd_nil, mul_one, mul_inv_rev,
      simple_inv, cons_append, cons.injEq, and_true]
    group

theorem leftInvSeq_concat (ω : List B) (i : B) :
    lis (ω.concat i) = (lis ω).concat ((π ω) * (s i) * (π ω)⁻¹) := by
  induction' ω with j ω ih
  · simp
  · dsimp [leftInvSeq]
    rw [ih]
    simp only [concat_eq_append, map_append, map_cons, _root_.map_mul, MulAut.conj_apply,
      simple_inv, map_inv, mul_inv_rev, map_nil, wordProd_cons, cons_append, cons.injEq,
      append_cancel_left_eq, and_true, true_and]
    group
    simp [mul_assoc]

private theorem leftInvSeq_eq_reverse_rightInvSeq_reverse (ω : List B) :
    lis ω = (ris ω.reverse).reverse := by
  induction' ω with i ω ih
  · simp
  · rw [leftInvSeq, reverse_cons, ← concat_eq_append, rightInvSeq_concat, ih]
    simp [map_reverse]

theorem rightInvSeq_reverse (ω : List B) :
    ris (ω.reverse) = (lis ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem leftInvSeq_reverse (ω : List B) :
    lis (ω.reverse) = (ris ω).reverse := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

@[simp] theorem length_rightInvSeq (ω : List B) : (ris ω).length = ω.length := by
  induction' ω with i ω ih
  · simp
  · simpa [rightInvSeq]

@[simp] theorem length_leftInvSeq (ω : List B) : (lis ω).length = ω.length := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]

theorem getD_rightInvSeq (ω : List B) (j : ℕ) :
    (ris ω).getD j 1 = (π (ω.drop (j + 1)))⁻¹
        * (Option.map (cs.simpleReflection) (ω.get? j)).getD 1
        * π (ω.drop (j + 1)) := by
  induction' ω with i ω ih generalizing j
  · simp
  · dsimp [rightInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · simp [getD_cons_succ]
      rw [ih j']

theorem getD_leftInvSeq (ω : List B) (j : ℕ) :
    (lis ω).getD j 1 = π (ω.take j)
        * (Option.map (cs.simpleReflection) (ω.get? j)).getD 1
        * (π (ω.take j))⁻¹ := by
  induction' ω with i ω ih generalizing j
  · simp
  · dsimp [leftInvSeq]
    rcases j with _ | j'
    · simp [getD_cons_zero]
    · rw [getD_cons_succ]
      rw [(by simp : 1 = ⇑(MulAut.conj (simpleReflection cs i)) 1)]
      rw [getD_map]
      rw [ih j']
      simp [← mul_assoc]

theorem getD_rightInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((ris ω).getD j 1) * ((ris ω).getD j 1) = 1 := by
  simp [getD_rightInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp [← mul_assoc]
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem getD_leftInvSeq_mul_self (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * ((lis ω).getD j 1) = 1 := by
  simp [getD_leftInvSeq, mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp [← mul_assoc]
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem rightInvSeq_drop (ω : List B) (j : ℕ) :
    ris (ω.drop j) = (ris ω).drop j := by
  induction' j with j ih₁ generalizing ω
  · simp
  · induction' ω with k ω _
    · simp
    · rw [drop_succ_cons, ih₁ ω, rightInvSeq, drop_succ_cons]

theorem leftInvSeq_take (ω : List B) (j : ℕ) :
    lis (ω.take j) = (lis ω).take j := by
  rcases em (j ≤ ω.length) with le | gt
  · simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]
    rw [List.reverse_take j (by simpa)]
    nth_rw 1 [← List.reverse_reverse ω]
    rw [List.reverse_take j (by simpa)]
    simp [rightInvSeq_drop]
  · have : ω.length ≤ j := by linarith
    rw [take_length_le this, take_length_le (by simpa)]

theorem isReflection_of_mem_rightInvSeq (ω : List B) (t : W) (ht : t ∈ ris ω) :
    cs.IsReflection t := by
  induction' ω with i ω ih
  · simp at ht
  · dsimp [rightInvSeq] at ht
    rcases ht with _ | ⟨_, mem⟩
    · use (π ω)⁻¹, i
      group
    · exact ih mem

theorem isReflection_of_mem_leftInvSeq (ω : List B) (t : W) (ht : t ∈ lis ω) :
    cs.IsReflection t := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse] at ht
  exact cs.isReflection_of_mem_rightInvSeq ω.reverse t ht

theorem wordProd_mul_getD_rightInvSeq (ω : List B) (j : ℕ) :
    π ω * ((ris ω).getD j 1) = π (ω.eraseIdx j) := by
  rw [getD_rightInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 1 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  simp [mul_assoc]
  simp [← mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem getD_leftInvSeq_mul_wordProd (ω : List B) (j : ℕ) :
    ((lis ω).getD j 1) * π ω = π (ω.eraseIdx j) := by
  rw [getD_leftInvSeq, eraseIdx_eq_take_drop_succ]
  nth_rw 4 [← take_append_drop (j + 1) ω]
  rw [take_succ]
  simp [mul_assoc]
  simp [← mul_assoc]
  rcases em (j < ω.length) with hj | nhj
  · rw [get?_eq_get hj]
    simp
  · rw [get?_eq_none.mpr (by linarith)]
    simp

theorem prod_rightInvSeq (ω : List B) : prod (ris ω) = (π ω)⁻¹ := by
  induction' ω with i ω ih
  · simp
  · simp [rightInvSeq, ih]

theorem prod_leftInvSeq (ω : List B) : prod (lis ω) = (π ω)⁻¹ := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse, prod_reverse_noncomm]
  have : List.map (fun x ↦ x⁻¹) (ris ω.reverse) = ris ω.reverse := calc
    List.map (fun x ↦ x⁻¹) (ris ω.reverse)
    _ = List.map id (ris ω.reverse)             := by
        apply List.map_congr
        intro t ht
        exact cs.inv_reflection_eq (cs.isReflection_of_mem_rightInvSeq _ t ht)
    _ = ris ω.reverse                           := map_id _
  rw [this]
  nth_rw 2 [← reverse_reverse ω]
  rw [wordProd_reverse]
  exact cs.prod_rightInvSeq _

theorem nodup_rightInvSeq_of_reduced {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (ris ω) := by
  apply List.nodup_iff_get?_ne_get?.mpr
  intro j j' j_lt_j' j'_lt_length dup
  -- dup : get? (rightInvSeq cs ω) j = get? (rightInvSeq cs ω) j'
  -- ⊢ False

  simp at j'_lt_length
  -- j'_lt_length: j' < List.length ω

  rw [get?_eq_get (by simp; linarith), get?_eq_get (by simp; linarith)] at dup
  apply Option.some_injective at dup
  rw [← getD_eq_get _ 1, ← getD_eq_get _ 1] at dup

  let t := (ris ω).getD j 1
  let t' := (ris (ω.eraseIdx j)).getD (j' - 1) 1

  have h₁ : t' = (ris (ω.eraseIdx j)).getD (j' - 1) 1 := by rfl

  have h₂ : t' = (ris ω).getD j' 1                    := by
    rw [h₁]
    rw [cs.getD_rightInvSeq, cs.getD_rightInvSeq]
    rw [(Nat.sub_add_cancel (by linarith) : j' - 1 + 1 = j')]
    rw [eraseIdx_eq_take_drop_succ]
    rw [drop_append_eq_append_drop]
    rw [drop_length_le (by simp; left; linarith)]
    rw [length_take, drop_drop, nil_append]
    rw [min_eq_left_of_lt (j_lt_j'.trans j'_lt_length)]
    rw [Nat.succ_eq_add_one, ← add_assoc, Nat.sub_add_cancel (by linarith)]
    rw [mul_left_inj, mul_right_inj]
    congr 2
    -- ⊢ get? (take j ω ++ drop (j + 1) ω) (j' - 1) = get? ω j'
    rw [get?_append_right (by simp; left; exact Nat.le_sub_one_of_lt j_lt_j')]
    rw [get?_drop]
    congr
    -- ⊢ j + 1 + (j' - 1 - List.length (take j ω)) = j'
    rw [length_take]
    rw [min_eq_left_of_lt (j_lt_j'.trans j'_lt_length)]
    rw [Nat.sub_sub, add_comm 1, Nat.add_sub_cancel' (by linarith)]

  have h₃ : t * t' = 1                                := by
    rw [(by rfl : t = getD (ris ω) j 1), h₂]
    rw [dup]
    exact cs.getD_rightInvSeq_mul_self _ _

  have h₄ := calc
    π ω   = π ω * t * t'                              := by rw [mul_assoc, h₃]; group
    _     = (π (ω.eraseIdx j)) * t'                   :=
        congrArg (· * t') (cs.wordProd_mul_getD_rightInvSeq _ _)
    _     = π ((ω.eraseIdx j).eraseIdx (j' - 1))      :=
        cs.wordProd_mul_getD_rightInvSeq _ _

  have h₅ := calc
    ω.length = ℓ (π ω)                                    := rω.symm
    _        = ℓ (π ((ω.eraseIdx j).eraseIdx (j' - 1)))   := congrArg cs.length h₄
    _        ≤ ((ω.eraseIdx j).eraseIdx (j' - 1)).length  := cs.length_wordProd_le _

  have h₆ := add_le_add_right (add_le_add_right h₅ 1) 1

  have h₇ : j' - 1 < List.length (eraseIdx ω j)           := by
    apply (@Nat.add_lt_add_iff_right 1).mp
    rw [Nat.sub_add_cancel (by linarith)]
    rw [length_eraseIdx_add_one (by linarith)]
    linarith

  rw [length_eraseIdx_add_one h₇] at h₆
  rw [length_eraseIdx_add_one (by linarith)] at h₆
  linarith

theorem nodup_leftInvSeq_of_reduced {ω : List B} (rω : cs.IsReduced ω) : List.Nodup (lis ω) := by
  simp [leftInvSeq_eq_reverse_rightInvSeq_reverse]
  apply nodup_rightInvSeq_of_reduced
  simpa

end CoxeterSystem

end
