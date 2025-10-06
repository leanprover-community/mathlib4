/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Ackermann function

In this file, we define the two-argument Ackermann function `ack`. Despite having a recursive
definition, we show that this isn't a primitive recursive function.

## Main results

- `exists_lt_ack_of_nat_primrec`: any primitive recursive function is pointwise bounded above by
  `ack m` for some `m`.
- `not_primrec₂_ack`: the two-argument Ackermann function is not primitive recursive.
- `computable₂_ack`: the two-argument Ackermann function is computable.

## Proof approach

We very broadly adapt the proof idea from
https://www.planetmath.org/ackermannfunctionisnotprimitiverecursive. Namely, we prove that for any
primitive recursive `f : ℕ → ℕ`, there exists `m` such that `f n < ack m n` for all `n`. This then
implies that `fun n => ack n n` can't be primitive recursive, and so neither can `ack`. We aren't
able to use the same bounds as in that proof though, since our approach of using pairing functions
differs from their approach of using multivariate functions.

The important bounds we show during the main inductive proof (`exists_lt_ack_of_nat_primrec`)
are the following. Assuming `∀ n, f n < ack a n` and `∀ n, g n < ack b n`, we have:

- `∀ n, pair (f n) (g n) < ack (max a b + 3) n`.
- `∀ n, g (f n) < ack (max a b + 2) n`.
- `∀ n, Nat.rec (f n.unpair.1) (fun (y IH : ℕ) => g (pair n.unpair.1 (pair y IH)))
  n.unpair.2 < ack (max a b + 9) n`.

The last one is evidently the hardest. Using `unpair_add_le`, we reduce it to the more manageable

- `∀ m n, rec (f m) (fun (y IH : ℕ) => g (pair m (pair y IH))) n <
  ack (max a b + 9) (m + n)`.

We then prove this by induction on `n`. Our proof crucially depends on `ack_pair_lt`, which is
applied twice, giving us a constant of `4 + 4`. The rest of the proof consists of simpler bounds
which bump up our constant to `9`.
-/


open Nat

/-- The two-argument Ackermann function, defined so that

- `ack 0 n = n + 1`
- `ack (m + 1) 0 = ack m 1`
- `ack (m + 1) (n + 1) = ack m (ack (m + 1) n)`.

This is of interest as both a fast-growing function, and as an example of a recursive function that
isn't primitive recursive. -/
def ack : ℕ → ℕ → ℕ
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)

@[simp]
theorem ack_zero (n : ℕ) : ack 0 n = n + 1 := by rw [ack]

@[simp]
theorem ack_succ_zero (m : ℕ) : ack (m + 1) 0 = ack m 1 := by rw [ack]

@[simp]
theorem ack_succ_succ (m n : ℕ) : ack (m + 1) (n + 1) = ack m (ack (m + 1) n) := by rw [ack]

@[simp]
theorem ack_one (n : ℕ) : ack 1 n = n + 2 := by
  induction n with
  | zero => simp
  | succ n IH => simp [IH]

@[simp]
theorem ack_two (n : ℕ) : ack 2 n = 2 * n + 3 := by
  induction n with
  | zero => simp
  | succ n IH => simpa [mul_succ]

@[simp]
theorem ack_three (n : ℕ) : ack 3 n = 2 ^ (n + 3) - 3 := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [ack_succ_succ, IH, ack_two, Nat.succ_add, Nat.pow_succ 2 (n + 3), mul_comm _ 2,
        Nat.mul_sub_left_distrib, ← Nat.sub_add_comm, two_mul 3, Nat.add_sub_add_right]
    calc  2 * 3
      _ ≤ 2 * 2 ^ 3 := by simp
      _ ≤ 2 * 2 ^ (n + 3) := by gcongr <;> omega

theorem ack_pos : ∀ m n, 0 < ack m n
  | 0, n => by simp
  | m + 1, 0 => by
    rw [ack_succ_zero]
    apply ack_pos
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    apply ack_pos

theorem one_lt_ack_succ_left : ∀ m n, 1 < ack (m + 1) n
  | 0, n => by simp
  | m + 1, 0 => by
    rw [ack_succ_zero]
    apply one_lt_ack_succ_left
  | m + 1, n + 1 => by
    rw [ack_succ_succ]
    apply one_lt_ack_succ_left

theorem one_lt_ack_succ_right : ∀ m n, 1 < ack m (n + 1)
  | 0, n => by simp
  | m + 1, n => one_lt_ack_succ_left m (n + 1)

theorem ack_strictMono_right : ∀ m, StrictMono (ack m)
  | 0, n₁, n₂, h => by simpa using h
  | m + 1, 0, n + 1, _h => by
    rw [ack_succ_zero, ack_succ_succ]
    exact ack_strictMono_right _ (one_lt_ack_succ_left m n)
  | m + 1, n₁ + 1, n₂ + 1, h => by
    rw [ack_succ_succ, ack_succ_succ]
    apply ack_strictMono_right _ (ack_strictMono_right _ _)
    rwa [add_lt_add_iff_right] at h

theorem ack_mono_right (m : ℕ) : Monotone (ack m) :=
  (ack_strictMono_right m).monotone

theorem ack_injective_right (m : ℕ) : Function.Injective (ack m) :=
  (ack_strictMono_right m).injective

@[simp]
theorem ack_lt_iff_right {m n₁ n₂ : ℕ} : ack m n₁ < ack m n₂ ↔ n₁ < n₂ :=
  (ack_strictMono_right m).lt_iff_lt

@[simp]
theorem ack_le_iff_right {m n₁ n₂ : ℕ} : ack m n₁ ≤ ack m n₂ ↔ n₁ ≤ n₂ :=
  (ack_strictMono_right m).le_iff_le

@[simp]
theorem ack_inj_right {m n₁ n₂ : ℕ} : ack m n₁ = ack m n₂ ↔ n₁ = n₂ :=
  (ack_injective_right m).eq_iff

theorem max_ack_right (m n₁ n₂ : ℕ) : ack m (max n₁ n₂) = max (ack m n₁) (ack m n₂) :=
  (ack_mono_right m).map_max

theorem add_lt_ack : ∀ m n, m + n < ack m n
  | 0, n => by simp
  | m + 1, 0 => by simpa using add_lt_ack m 1
  | m + 1, n + 1 =>
    calc
      m + 1 + n + 1 ≤ m + (m + n + 2) := by omega
      _ < ack m (m + n + 2) := add_lt_ack _ _
      _ ≤ ack m (ack (m + 1) n) :=
        ack_mono_right m <| le_of_eq_of_le (by rw [succ_eq_add_one]; ring_nf)
        <| succ_le_of_lt <| add_lt_ack (m + 1) n
      _ = ack (m + 1) (n + 1) := (ack_succ_succ m n).symm

theorem add_add_one_le_ack (m n : ℕ) : m + n + 1 ≤ ack m n :=
  succ_le_of_lt (add_lt_ack m n)

theorem lt_ack_left (m n : ℕ) : m < ack m n :=
  (self_le_add_right m n).trans_lt <| add_lt_ack m n

theorem lt_ack_right (m n : ℕ) : n < ack m n :=
  (self_le_add_left n m).trans_lt <| add_lt_ack m n

-- we reorder the arguments to appease the equation compiler
private theorem ack_strict_mono_left' : ∀ {m₁ m₂} (n), m₁ < m₂ → ack m₁ n < ack m₂ n
  | m, 0, _ => fun h => (not_lt_zero m h).elim
  | 0, m + 1, 0 => fun _h => by simpa using one_lt_ack_succ_right m 0
  | 0, m + 1, n + 1 => fun h => by
    rw [ack_zero, ack_succ_succ]
    apply lt_of_le_of_lt (le_trans _ <| add_le_add_left (add_add_one_le_ack _ _) m) (add_lt_ack _ _)
    omega
  | m₁ + 1, m₂ + 1, 0 => fun h => by
    simpa using ack_strict_mono_left' 1 ((add_lt_add_iff_right 1).1 h)
  | m₁ + 1, m₂ + 1, n + 1 => fun h => by
    rw [ack_succ_succ, ack_succ_succ]
    exact
      (ack_strict_mono_left' _ <| (add_lt_add_iff_right 1).1 h).trans
        (ack_strictMono_right _ <| ack_strict_mono_left' n h)

theorem ack_strictMono_left (n : ℕ) : StrictMono fun m => ack m n := fun _m₁ _m₂ =>
  ack_strict_mono_left' n

theorem ack_mono_left (n : ℕ) : Monotone fun m => ack m n :=
  (ack_strictMono_left n).monotone

theorem ack_injective_left (n : ℕ) : Function.Injective fun m => ack m n :=
  (ack_strictMono_left n).injective

@[simp]
theorem ack_lt_iff_left {m₁ m₂ n : ℕ} : ack m₁ n < ack m₂ n ↔ m₁ < m₂ :=
  (ack_strictMono_left n).lt_iff_lt

@[simp]
theorem ack_le_iff_left {m₁ m₂ n : ℕ} : ack m₁ n ≤ ack m₂ n ↔ m₁ ≤ m₂ :=
  (ack_strictMono_left n).le_iff_le

@[simp]
theorem ack_inj_left {m₁ m₂ n : ℕ} : ack m₁ n = ack m₂ n ↔ m₁ = m₂ :=
  (ack_injective_left n).eq_iff

theorem max_ack_left (m₁ m₂ n : ℕ) : ack (max m₁ m₂) n = max (ack m₁ n) (ack m₂ n) :=
  (ack_mono_left n).map_max

@[gcongr]
theorem ack_le_ack {m₁ m₂ n₁ n₂ : ℕ} (hm : m₁ ≤ m₂) (hn : n₁ ≤ n₂) : ack m₁ n₁ ≤ ack m₂ n₂ :=
  (ack_mono_left n₁ hm).trans <| ack_mono_right m₂ hn

theorem ack_succ_right_le_ack_succ_left (m n : ℕ) : ack m (n + 1) ≤ ack (m + 1) n := by
  rcases n with - | n
  · simp
  · rw [ack_succ_succ]
    apply ack_mono_right m (le_trans _ <| add_add_one_le_ack _ n)
    cutsat

-- All the inequalities from this point onwards are specific to the main proof.
private theorem sq_le_two_pow_add_one_minus_three (n : ℕ) : n ^ 2 ≤ 2 ^ (n + 1) - 3 := by
  induction n with
  | zero => simp
  | succ k hk =>
    rcases k with - | k
    · simp
    · rw [add_sq, Nat.pow_succ 2, mul_comm _ 2, two_mul (2 ^ _),
          add_tsub_assoc_of_le, add_comm (2 ^ _), add_assoc]
      · apply Nat.add_le_add hk
        norm_num
        apply succ_le_of_lt
        rw [Nat.pow_succ, mul_comm _ 2, mul_lt_mul_iff_right₀ (zero_lt_two' ℕ)]
        exact Nat.lt_two_pow_self
      · rw [Nat.pow_succ, Nat.pow_succ]
        linarith [one_le_pow k 2 zero_lt_two]

theorem ack_add_one_sq_lt_ack_add_three : ∀ m n, (ack m n + 1) ^ 2 ≤ ack (m + 3) n
  | 0, n => by simpa using sq_le_two_pow_add_one_minus_three (n + 2)
  | m + 1, 0 => by
    rw [ack_succ_zero, ack_succ_zero]
    apply ack_add_one_sq_lt_ack_add_three
  | m + 1, n + 1 => by
    rw [ack_succ_succ, ack_succ_succ]
    apply (ack_add_one_sq_lt_ack_add_three _ _).trans (ack_mono_right _ <| ack_mono_left _ _)
    cutsat

theorem ack_ack_lt_ack_max_add_two (m n k : ℕ) : ack m (ack n k) < ack (max m n + 2) k :=
  calc
    ack m (ack n k) ≤ ack (max m n) (ack n k) := ack_mono_left _ (le_max_left _ _)
    _ < ack (max m n) (ack (max m n + 1) k) :=
      ack_strictMono_right _ <| ack_strictMono_left k <| lt_succ_of_le <| le_max_right m n
    _ = ack (max m n + 1) (k + 1) := (ack_succ_succ _ _).symm
    _ ≤ ack (max m n + 2) k := ack_succ_right_le_ack_succ_left _ _

theorem ack_add_one_sq_lt_ack_add_four (m n : ℕ) : ack m ((n + 1) ^ 2) < ack (m + 4) n :=
  calc
    ack m ((n + 1) ^ 2) < ack m ((ack m n + 1) ^ 2) :=
      ack_strictMono_right m <| Nat.pow_lt_pow_left (succ_lt_succ <| lt_ack_right m n) two_ne_zero
    _ ≤ ack m (ack (m + 3) n) := ack_mono_right m <| ack_add_one_sq_lt_ack_add_three m n
    _ ≤ ack (m + 2) (ack (m + 3) n) := ack_mono_left _ <| by cutsat
    _ = ack (m + 3) (n + 1) := (ack_succ_succ _ n).symm
    _ ≤ ack (m + 4) n := ack_succ_right_le_ack_succ_left _ n

theorem ack_pair_lt (m n k : ℕ) : ack m (pair n k) < ack (m + 4) (max n k) :=
  (ack_strictMono_right m <| pair_lt_max_add_one_sq n k).trans <|
    ack_add_one_sq_lt_ack_add_four _ _

/-- If `f` is primitive recursive, there exists `m` such that `f n < ack m n` for all `n`. -/
theorem exists_lt_ack_of_nat_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ m, ∀ n, f n < ack m n := by
  induction hf with
  | zero => exact ⟨0, ack_pos 0⟩
  | succ =>
    refine ⟨1, fun n => ?_⟩
    rw [succ_eq_one_add]
    apply add_lt_ack
  | left =>
    refine ⟨0, fun n => ?_⟩
    rw [ack_zero, Nat.lt_succ_iff]
    exact unpair_left_le n
  | right =>
    refine ⟨0, fun n => ?_⟩
    rw [ack_zero, Nat.lt_succ_iff]
    exact unpair_right_le n
  | pair hf hg IHf IHg =>
    obtain ⟨a, ha⟩ := IHf; obtain ⟨b, hb⟩ := IHg
    refine
      ⟨max a b + 3, fun n =>
        (pair_lt_max_add_one_sq _ _).trans_le <|
          (Nat.pow_le_pow_left (add_le_add_right ?_ _) 2).trans <|
            ack_add_one_sq_lt_ack_add_three _ _⟩
    rw [max_ack_left]
    exact max_le_max (ha n).le (hb n).le
  | comp hf hg IHf IHg =>
    obtain ⟨a, ha⟩ := IHf; obtain ⟨b, hb⟩ := IHg
    exact
      ⟨max a b + 2, fun n =>
        (ha _).trans <| (ack_strictMono_right a <| hb n).trans <| ack_ack_lt_ack_max_add_two a b n⟩
  | @prec f g hf hg IHf IHg =>
    obtain ⟨a, ha⟩ := IHf; obtain ⟨b, hb⟩ := IHg
    -- We prove this simpler inequality first.
    have :
      ∀ {m n},
        rec (f m) (fun y IH => g <| pair m <| pair y IH) n < ack (max a b + 9) (m + n) := by
      intro m n
      -- We induct on n.
      induction n with
      | zero => -- The base case is easy.
        apply (ha m).trans (ack_strictMono_left m <| (le_max_left a b).trans_lt _)
        cutsat
      | succ n IH => -- We get rid of the first `pair`.
        simp only
        apply (hb _).trans ((ack_pair_lt _ _ _).trans_le _)
        -- If m is the maximum, we get a very weak inequality.
        rcases lt_or_ge _ m with h₁ | h₁
        · rw [max_eq_left h₁.le]
          gcongr <;> omega
        rw [max_eq_right h₁]
        -- We get rid of the second `pair`.
        apply (ack_pair_lt _ _ _).le.trans
        -- If n is the maximum, we get a very weak inequality.
        rcases lt_or_ge _ n with h₂ | h₂
        · rw [max_eq_left h₂.le, add_assoc]
          exact
            ack_le_ack (Nat.add_le_add (le_max_right a b) <| by simp)
              ((le_succ n).trans <| self_le_add_left _ _)
        rw [max_eq_right h₂]
        -- We now use the inductive hypothesis, and some simple algebraic manipulation.
        apply (ack_strictMono_right _ IH).le.trans
        rw [add_succ m, add_succ _ 8, succ_eq_add_one, succ_eq_add_one,
            ack_succ_succ (_ + 8), add_assoc]
        exact ack_mono_left _ (Nat.add_le_add (le_max_right a b) le_rfl)
    -- The proof is now simple.
    exact ⟨max a b + 9, fun n => this.trans_le <| ack_mono_right _ <| unpair_add_le n⟩

theorem not_nat_primrec_ack_self : ¬Nat.Primrec fun n => ack n n := fun h => by
  obtain ⟨m, hm⟩ := exists_lt_ack_of_nat_primrec h
  exact (hm m).false

theorem not_primrec_ack_self : ¬Primrec fun n => ack n n := by
  rw [Primrec.nat_iff]
  exact not_nat_primrec_ack_self

/-- The Ackermann function is not primitive recursive. -/
theorem not_primrec₂_ack : ¬Primrec₂ ack := fun h =>
  not_primrec_ack_self <| h.comp Primrec.id Primrec.id

namespace Nat.Partrec.Code

/-- The code for the partially applied Ackermann function.
This is used to prove that the Ackermann function is computable. -/
def pappAck : ℕ → Code
  | 0 => .succ
  | n + 1 => step (pappAck n)
where
  /-- Yields single recursion step on `pappAck`. -/
  step (c : Code) : Code :=
    .curry (.prec (.comp c (.const 1)) (.comp c (.comp .right .right))) 0

lemma primrec_pappAck_step : Primrec pappAck.step := by
  apply_rules
    [Code.primrec₂_curry.comp, Code.primrec₂_prec.comp, Code.primrec₂_comp.comp,
      _root_.Primrec.id, Primrec.const]

@[simp]
lemma eval_pappAck_step_zero (c : Code) : (pappAck.step c).eval 0 = c.eval 1 := by
  simp [pappAck.step, Code.eval]

@[simp]
lemma eval_pappAck_step_succ (c : Code) (n) :
    (pappAck.step c).eval (n + 1) = ((pappAck.step c).eval n).bind c.eval := by
  simp [pappAck.step, Code.eval]

lemma primrec_pappAck : Primrec pappAck := by
  suffices Primrec (Nat.rec Code.succ (fun _ c => pappAck.step c)) by
    convert this using 2 with n; induction n <;> simp [pappAck, *]
  apply_rules [Primrec.nat_rec₁, primrec_pappAck_step.comp, Primrec.snd]

@[simp]
lemma eval_pappAck (m n) : (pappAck m).eval n = Part.some (ack m n) := by
  induction m, n using ack.induct with
    | case1 n => simp [Code.eval, pappAck]
    | case2 m hm => simp [pappAck, hm]
    | case3 m n hmn₁ hmn₂ => dsimp only [pappAck] at *; simp [hmn₁, hmn₂]

/-- The Ackermann function is computable. -/
theorem _root_.computable₂_ack : Computable₂ ack := by
  apply _root_.Partrec.of_eq_tot
    (f := fun p : ℕ × ℕ => (pappAck p.1).eval p.2) (g := fun p : ℕ × ℕ => ack p.1 p.2)
  · change Partrec₂ (fun m n => (pappAck m).eval n)
    apply_rules only
      [Code.eval_part.comp₂, Computable.fst, Computable.snd, primrec_pappAck.to_comp.comp]
  · simp

end Nat.Partrec.Code
