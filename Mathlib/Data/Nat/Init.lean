/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Batteries.Tactic.Alias
import Batteries.Tactic.Init
import Mathlib.Init
import Mathlib.Data.Int.Notation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Util.AssertExists

/-!
# Basic operations on the natural numbers

This file contains:
* some basic lemmas about natural numbers
* extra recursors:
  * `leRecOn`, `le_induction`: recursion and induction principles starting at non-zero numbers
  * `decreasing_induction`: recursion growing downwards
  * `le_rec_on'`, `decreasing_induction'`: versions with slightly weaker assumptions
  * `strong_rec'`: recursion based on strong inequalities
* decidability instances on predicates about the natural numbers

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

See note [foundational algebra order theory].
-/

library_note "foundational algebra order theory"/--
Batteries has a home-baked development of the algebraic and order-theoretic theory of `ℕ` and `ℤ
which, in particular, is not typeclass-mediated. This is useful to set up the algebra and finiteness
libraries in mathlib (naturals and integers show up as indices/offsets in lists, cardinality in
finsets, powers in groups, ...).

Less basic uses of `ℕ` and `ℤ` should however use the typeclass-mediated development.

The relevant files are:
* `Mathlib/Data/Nat/Basic.lean` for the continuation of the home-baked development on `ℕ`
* `Mathlib/Data/Int/Init.lean` for the continuation of the home-baked development on `ℤ`
* `Mathlib/Algebra/Group/Nat.lean` for the monoid instances on `ℕ`
* `Mathlib/Algebra/Group/Int.lean` for the group instance on `ℤ`
* `Mathlib/Algebra/Ring/Nat.lean` for the semiring instance on `ℕ`
* `Mathlib/Algebra/Ring/Int.lean` for the ring instance on `ℤ`
* `Mathlib/Algebra/Order/Group/Nat.lean` for the ordered monoid instance on `ℕ`
* `Mathlib/Algebra/Order/Group/Int.lean` for the ordered group instance on `ℤ`
* `Mathlib/Algebra/Order/Ring/Nat.lean` for the ordered semiring instance on `ℕ`
* `Mathlib/Algebra/Order/Ring/Int.lean` for the ordered ring instance on `ℤ`
-/

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

open Function

namespace Nat
variable {a b c d e m n k : ℕ} {p : ℕ → Prop}

/-! ### `succ`, `pred` -/

lemma succ_pos' : 0 < succ n := succ_pos n

alias _root_.LT.lt.nat_succ_le := succ_le_of_lt

alias ⟨of_le_succ, _⟩ := le_succ_iff

@[deprecated (since := "2025-08-21")] alias forall_lt_succ := forall_lt_succ_right

@[deprecated (since := "2025-08-15")] alias exists_lt_succ := exists_lt_succ_right

lemma two_lt_of_ne : ∀ {n}, n ≠ 0 → n ≠ 1 → n ≠ 2 → 2 < n
  | 0, h, _, _ => (h rfl).elim
  | 1, _, h, _ => (h rfl).elim
  | 2, _, _, h => (h rfl).elim
  | n + 3, _, _, _ => le_add_left 3 n

lemma two_le_iff : ∀ n, 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp

/-! ### `add` -/

/-! ### `sub` -/

/-! ### `mul` -/

lemma mul_def : Nat.mul m n = m * n := mul_eq

lemma two_mul_ne_two_mul_add_one : 2 * n ≠ 2 * m + 1 :=
  mt (congrArg (· % 2))
    (by rw [Nat.add_comm, add_mul_mod_self_left, mul_mod_right, mod_eq_of_lt] <;> simp)

@[deprecated (since := "2025-06-05")] alias mul_right_eq_self_iff := mul_eq_left
@[deprecated (since := "2025-06-05")] alias mul_left_eq_self_iff := mul_eq_right
@[deprecated (since := "2025-06-05")] alias eq_zero_of_double_le := eq_zero_of_two_mul_le

/-! ### `div` -/

lemma le_div_two_iff_mul_two_le {n m : ℕ} : m ≤ n / 2 ↔ (m : ℤ) * 2 ≤ n := by
  rw [Nat.le_div_iff_mul_le Nat.zero_lt_two, ← Int.ofNat_le, Int.natCast_mul, Int.ofNat_two]

/-- A version of `Nat.div_lt_self` using successors, rather than additional hypotheses. -/
lemma div_lt_self' (a b : ℕ) : (a + 1) / (b + 2) < a + 1 :=
  Nat.div_lt_self (Nat.succ_pos _) (Nat.succ_lt_succ (Nat.succ_pos _))

@[deprecated (since := "2025-04-15")] alias sub_mul_div' := sub_mul_div

@[deprecated (since := "2025-06-05")] alias eq_zero_of_le_half := eq_zero_of_le_div_two
@[deprecated (since := "2025-06-05")] alias le_half_of_half_lt_sub := le_div_two_of_div_two_lt_sub
@[deprecated (since := "2025-06-05")] alias half_le_of_sub_le_half := div_two_le_of_sub_le_div_two
@[deprecated (since := "2025-06-05")] protected alias div_le_of_le_mul' := Nat.div_le_of_le_mul
@[deprecated (since := "2025-06-05")] protected alias div_le_self' := Nat.div_le_self

lemma two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 := by
  omega

/-! ### `pow` -/

lemma one_le_pow' (n m : ℕ) : 1 ≤ (m + 1) ^ n := one_le_pow n (m + 1) (succ_pos m)

alias sq_sub_sq := pow_two_sub_pow_two

/-!
### Recursion and induction principles

This section is here due to dependencies -- the lemmas here require some of the lemmas
proved above, and some of the results in later sections depend on the definitions in this section.
-/

@[simp]
lemma rec_zero {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) : Nat.rec h0 h 0 = h0 := rfl

-- Not `@[simp]` since `simp` can reduce the whole term.
lemma rec_add_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) (n : ℕ) :
    Nat.rec h0 h (n + 1) = h n (Nat.rec h0 h n) := rfl

@[simp] lemma rec_one {C : ℕ → Sort*} (h0 : C 0) (h : ∀ n, C n → C (n + 1)) :
    Nat.rec (motive := C) h0 h 1 = h 0 h0 := rfl

/-- Recursion starting at a non-zero number: given a map `C k → C (k+1)` for each `k ≥ n`,
there is a map from `C n` to each `C m`, `n ≤ m`.

This is a version of `Nat.le.rec` that works for `Sort u`.
Similarly to `Nat.le.rec`, it can be used as
```
induction hle using Nat.leRec with
| refl => sorry
| le_succ_of_le hle ih => sorry
```
-/
@[elab_as_elim]
def leRec {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
    ∀ {m} (h : n ≤ m), motive m h
  | 0, H => Nat.eq_zero_of_le_zero H ▸ refl
  | m + 1, H =>
    (le_succ_iff.1 H).by_cases
      (fun h : n ≤ m ↦ le_succ_of_le h <| leRec refl le_succ_of_le h)
      (fun h : n = m + 1 ↦ h ▸ refl)

-- This verifies the signatures of the recursor matches the builtin one, as promised in the
-- above.
theorem leRec_eq_leRec : @Nat.leRec.{0} = @Nat.le.rec := rfl

@[simp]
lemma leRec_self {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h)) :
    (leRec (motive := motive) refl le_succ_of_le (Nat.le_refl _) :
    motive n (Nat.le_refl _)) = refl := by
  cases n <;> simp [leRec, Or.by_cases, dif_neg]

@[simp]
lemma leRec_succ {n} {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl : motive n (Nat.le_refl _))
    (le_succ_of_le : ∀ ⦃k⦄ (h : n ≤ k), motive k h → motive (k + 1) (le_succ_of_le h))
    (h1 : n ≤ m) {h2 : n ≤ m + 1} :
    (leRec (motive := motive) refl le_succ_of_le h2) =
      le_succ_of_le h1 (leRec (motive := motive) refl le_succ_of_le h1) := by
  conv =>
    lhs
    rw [leRec, Or.by_cases, dif_pos h1]

lemma leRec_succ' {n} {motive : (m : ℕ) → n ≤ m → Sort*} (refl le_succ_of_le) :
    (leRec (motive := motive) refl le_succ_of_le (le_succ _)) = le_succ_of_le _ refl := by
  rw [leRec_succ, leRec_self]

lemma leRec_trans {n m k} {motive : (m : ℕ) → n ≤ m → Sort*} (refl le_succ_of_le)
    (hnm : n ≤ m) (hmk : m ≤ k) :
    leRec (motive := motive) refl le_succ_of_le (Nat.le_trans hnm hmk) =
      leRec
        (leRec refl (fun _ h => le_succ_of_le h) hnm)
        (fun _ h => le_succ_of_le <| Nat.le_trans hnm h) hmk := by
  induction hmk with
  | refl => rw [leRec_self]
  | step hmk ih => rw [leRec_succ _ _ (Nat.le_trans hnm hmk), ih, leRec_succ]

lemma leRec_succ_left {motive : (m : ℕ) → n ≤ m → Sort*}
    (refl le_succ_of_le) {m} (h1 : n ≤ m) (h2 : n + 1 ≤ m) :
    -- the `@` is needed for this to elaborate, even though we only provide explicit arguments!
    @leRec _ _ (le_succ_of_le (Nat.le_refl _) refl)
        (fun _ h ih => le_succ_of_le (le_of_succ_le h) ih) _ h2 =
      leRec (motive := motive) refl le_succ_of_le h1 := by
  rw [leRec_trans _ _ (le_succ n) h2, leRec_succ']

/-- Recursion starting at a non-zero number: given a map `C k → C (k + 1)` for each `k`,
there is a map from `C n` to each `C m`, `n ≤ m`. For a version where the assumption is only made
when `k ≥ n`, see `Nat.leRec`. -/
@[elab_as_elim]
def leRecOn {C : ℕ → Sort*} {n : ℕ} : ∀ {m}, n ≤ m → (∀ {k}, C k → C (k + 1)) → C n → C m :=
  fun h of_succ self => Nat.leRec self (fun _ _ => @of_succ _) h

lemma leRecOn_self {C : ℕ → Sort*} {n} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn n.le_refl next x : C n) = x :=
  leRec_self _ _

lemma leRecOn_succ {C : ℕ → Sort*} {n m} (h1 : n ≤ m) {h2 : n ≤ m + 1} {next} (x : C n) :
    (leRecOn h2 next x : C (m + 1)) = next (leRecOn h1 next x : C m) :=
  leRec_succ _ _ _

lemma leRecOn_succ' {C : ℕ → Sort*} {n} {h : n ≤ n + 1} {next : ∀ {k}, C k → C (k + 1)} (x : C n) :
    (leRecOn h next x : C (n + 1)) = next x :=
  leRec_succ' _ _

lemma leRecOn_trans {C : ℕ → Sort*} {n m k} (hnm : n ≤ m) (hmk : m ≤ k) {next} (x : C n) :
    (leRecOn (Nat.le_trans hnm hmk) (@next) x : C k) =
      leRecOn hmk (@next) (leRecOn hnm (@next) x) :=
  leRec_trans _ _ _ _

lemma leRecOn_succ_left {C : ℕ → Sort*} {n m}
    {next : ∀ {k}, C k → C (k + 1)} (x : C n) (h1 : n ≤ m) (h2 : n + 1 ≤ m) :
    (leRecOn h2 next (next x) : C m) = (leRecOn h1 next x : C m) :=
  leRec_succ_left (motive := fun n _ => C n) _ (fun _ _ => @next _) _ _

/-- Recursion principle based on `<`. -/
@[elab_as_elim]
protected def strongRec' {p : ℕ → Sort*} (H : ∀ n, (∀ m, m < n → p m) → p n) : ∀ n : ℕ, p n
  | n => H n fun m _ ↦ Nat.strongRec' H m

/-- Recursion principle based on `<` applied to some natural number. -/
@[elab_as_elim]
def strongRecOn' {P : ℕ → Sort*} (n : ℕ) (h : ∀ n, (∀ m, m < n → P m) → P n) : P n :=
  Nat.strongRec' h n

lemma strongRecOn'_beta {P : ℕ → Sort*} {h} :
    (strongRecOn' n h : P n) = h n fun m _ ↦ (strongRecOn' m h : P m) := by
  simp only [strongRecOn']; rw [Nat.strongRec']

/-- Induction principle starting at a non-zero number.
To use in an induction proof, the syntax is `induction n, hn using Nat.le_induction` (or the same
for `induction'`).

This is an alias of `Nat.leRec`, specialized to `Prop`. -/
@[elab_as_elim]
lemma le_induction {m : ℕ} {P : ∀ n, m ≤ n → Prop} (base : P m m.le_refl)
    (succ : ∀ n hmn, P n hmn → P (n + 1) (le_succ_of_le hmn)) : ∀ n hmn, P n hmn :=
  @Nat.leRec (motive := P) _ base succ

/-- An equivalent formulation of the induction step. -/
lemma le_induction_step_iff {P : ℕ → Prop} : (∀ n, P n → P (n + 1)) ↔ (∀ n m, n ≤ m → P n → P m) :=
  ⟨
    fun h _ m hnm hn ↦ Nat.le_induction hn (fun m _ ↦ h m) m hnm,
    fun h _ ↦ h _ _ <| by omega,
  ⟩

/-- Induction principle deriving the next case from the two previous ones. -/
def twoStepInduction {P : ℕ → Sort*} (zero : P 0) (one : P 1)
    (more : ∀ n, P n → P (n + 1) → P (n + 2)) : ∀ a, P a
  | 0 => zero
  | 1 => one
  | _ + 2 => more _ (twoStepInduction zero one more _) (twoStepInduction zero one more _)

@[elab_as_elim]
protected theorem strong_induction_on {p : ℕ → Prop} (n : ℕ)
    (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
  Nat.strongRecOn n h

protected theorem case_strong_induction_on {p : ℕ → Prop} (a : ℕ) (hz : p 0)
    (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a :=
  Nat.caseStrongRecOn a hz hi

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `k < n`, then `P n` implies `P m` for
all `m ≤ n`.
Also works for functions to `Sort*`.

For a version also assuming `m ≤ k`, see `Nat.decreasingInduction'`. -/
@[elab_as_elim]
def decreasingInduction {n} {motive : (m : ℕ) → m ≤ n → Sort*}
    (of_succ : ∀ k (h : k < n), motive (k + 1) h → motive k (le_of_succ_le h))
    (self : motive n (Nat.le_refl _)) {m} (mn : m ≤ n) : motive m mn := by
  induction mn using leRec with
  | refl => exact self
  | @le_succ_of_le k _ ih =>
    apply ih (fun i hi => of_succ i (le_succ_of_le hi)) (of_succ k (lt_succ_self _) self)

@[simp]
lemma decreasingInduction_self {n} {motive : (m : ℕ) → m ≤ n → Sort*} (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self (Nat.le_refl _)) = self := by
  dsimp only [decreasingInduction]
  rw [leRec_self]

lemma decreasingInduction_succ {n} {motive : (m : ℕ) → m ≤ n + 1 → Sort*} (of_succ self)
    (mn : m ≤ n) (msn : m ≤ n + 1) :
    (decreasingInduction (motive := motive) of_succ self msn : motive m msn) =
      decreasingInduction (motive := fun m h => motive m (le_succ_of_le h))
        (fun _ _ => of_succ _ _) (of_succ _ _ self) mn := by
  dsimp only [decreasingInduction]; rw [leRec_succ]

@[simp]
lemma decreasingInduction_succ' {n} {motive : (m : ℕ) → m ≤ n + 1 → Sort*} (of_succ self) :
    decreasingInduction (motive := motive) of_succ self n.le_succ = of_succ _ _ self := by
  dsimp only [decreasingInduction]; rw [leRec_succ']

lemma decreasingInduction_trans {motive : (m : ℕ) → m ≤ k → Sort*} (hmn : m ≤ n) (hnk : n ≤ k)
    (of_succ self) :
    (decreasingInduction (motive := motive) of_succ self (Nat.le_trans hmn hnk) : motive m _) =
    decreasingInduction (fun _ _ => of_succ _ _) (decreasingInduction of_succ self hnk) hmn := by
  induction hnk with
  | refl => rw [decreasingInduction_self]
  | step hnk ih =>
      rw [decreasingInduction_succ _ _ (Nat.le_trans hmn hnk), ih, decreasingInduction_succ]

lemma decreasingInduction_succ_left {motive : (m : ℕ) → m ≤ n → Sort*} (of_succ self)
    (smn : m + 1 ≤ n) (mn : m ≤ n) :
    decreasingInduction (motive := motive) of_succ self mn =
      of_succ m smn (decreasingInduction of_succ self smn) := by
  rw [Subsingleton.elim mn (Nat.le_trans (le_succ m) smn), decreasingInduction_trans,
    decreasingInduction_succ']

/-- Given `P : ℕ → ℕ → Sort*`, if for all `m n : ℕ` we can extend `P` from the rectangle
strictly below `(m, n)` to `P m n`, then we have `P n m` for all `n m : ℕ`.
Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
def strongSubRecursion {P : ℕ → ℕ → Sort*} (H : ∀ m n, (∀ x y, x < m → y < n → P x y) → P m n) :
    ∀ n m : ℕ, P n m
  | n, m => H n m fun x y _ _ ↦ strongSubRecursion H x y

/-- Given `P : ℕ → ℕ → Sort*`, if we have `P m 0` and `P 0 n` for all `m n : ℕ`, and for any
`m n : ℕ` we can extend `P` from `(m, n + 1)` and `(m + 1, n)` to `(m + 1, n + 1)` then we have
`P m n` for all `m n : ℕ`.

Note that for non-`Prop` output it is preferable to use the equation compiler directly if possible,
since this produces equation lemmas. -/
@[elab_as_elim]
def pincerRecursion {P : ℕ → ℕ → Sort*} (Ha0 : ∀ m : ℕ, P m 0) (H0b : ∀ n : ℕ, P 0 n)
    (H : ∀ x y : ℕ, P x y.succ → P x.succ y → P x.succ y.succ) : ∀ n m : ℕ, P n m
  | m, 0 => Ha0 m
  | 0, n => H0b n
  | Nat.succ _, Nat.succ _ => H _ _ (pincerRecursion Ha0 H0b H _ _) (pincerRecursion Ha0 H0b H _ _)

/-- Decreasing induction: if `P (k+1)` implies `P k` for all `m ≤ k < n`, then `P n` implies `P m`.
Also works for functions to `Sort*`.

Weakens the assumptions of `Nat.decreasingInduction`. -/
@[elab_as_elim]
def decreasingInduction' {P : ℕ → Sort*} (h : ∀ k < n, m ≤ k → P (k + 1) → P k)
    (mn : m ≤ n) (hP : P n) : P m := by
  induction mn using decreasingInduction with
  | self => exact hP
  | of_succ k hk ih =>
    exact h _ (lt_of_succ_le hk) (Nat.le_refl _)
      (ih fun k' hk' h'' => h k' hk' <| le_of_succ_le h'')

/-- Given a predicate on two naturals `P : ℕ → ℕ → Prop`, `P a b` is true for all `a < b` if
`P (a + 1) (a + 1)` is true for all `a`, `P 0 (b + 1)` is true for all `b` and for all
`a < b`, `P (a + 1) b` is true and `P a (b + 1)` is true implies `P (a + 1) (b + 1)` is true. -/
@[elab_as_elim]
theorem diag_induction (P : ℕ → ℕ → Prop) (ha : ∀ a, P (a + 1) (a + 1)) (hb : ∀ b, P 0 (b + 1))
    (hd : ∀ a b, a < b → P (a + 1) b → P a (b + 1) → P (a + 1) (b + 1)) : ∀ a b, a < b → P a b
  | 0, _ + 1, _ => hb _
  | a + 1, b + 1, h => by
    apply hd _ _ (Nat.add_lt_add_iff_right.1 h)
    · have this : a + 1 = b ∨ a + 1 < b := by omega
      have wf : (a + 1) + b < (a + 1) + (b + 1) := by simp
      rcases this with (rfl | h)
      · exact ha _
      apply diag_induction P ha hb hd (a + 1) b h
    have _ : a + (b + 1) < (a + 1) + (b + 1) := by simp
    apply diag_induction P ha hb hd a (b + 1)
    apply Nat.lt_of_le_of_lt (Nat.le_succ _) h

/-! ### `mod`, `dvd` -/

lemma not_pos_pow_dvd {a n : ℕ} (ha : 1 < a) (hn : 1 < n) : ¬ a ^ n ∣ a :=
  not_dvd_of_pos_of_lt (Nat.lt_trans Nat.zero_lt_one ha)
    (lt_of_eq_of_lt (Nat.pow_one a).symm ((Nat.pow_lt_pow_iff_right ha).2 hn))

/-- `m` is not divisible by `n` if it is between `n * k` and `n * (k + 1)` for some `k`. -/
@[deprecated (since := "2025-06-05")] alias not_dvd_of_between_consec_multiples :=
  not_dvd_of_lt_of_lt_mul_succ

@[simp]
protected theorem not_two_dvd_bit1 (n : ℕ) : ¬2 ∣ 2 * n + 1 := by
  omega

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`. -/
@[simp] protected lemma dvd_add_self_left : m ∣ m + n ↔ m ∣ n := Nat.dvd_add_right (Nat.dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`. -/
@[simp] protected lemma dvd_add_self_right : m ∣ n + m ↔ m ∣ n := Nat.dvd_add_left (Nat.dvd_refl m)

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
@[deprecated (since := "2025-06-05")] alias not_dvd_iff_between_consec_multiples :=
  not_dvd_iff_lt_mul_succ

/-- Two natural numbers are equal if and only if they have the same multiples. -/
lemma dvd_right_iff_eq : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mpr (Nat.dvd_refl _)) ((h _).mp (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

/-- Two natural numbers are equal if and only if they have the same divisors. -/
lemma dvd_left_iff_eq : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
  ⟨fun h => Nat.dvd_antisymm ((h _).mp (Nat.dvd_refl _)) ((h _).mpr (Nat.dvd_refl _)),
    fun h n => by rw [h]⟩

/-! ### Decidability of predicates -/

instance decidableLoHi (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x < hi → P x) :=
  decidable_of_iff (∀ x < hi - lo, P (lo + x)) <| by
    refine ⟨fun al x hl hh ↦ ?_,
      fun al x h ↦ al _ (Nat.le_add_right _ _) (Nat.lt_sub_iff_add_lt'.1 h)⟩
    have := al (x - lo) ((Nat.sub_lt_sub_iff_right hl).2 hh)
    rwa [Nat.add_sub_cancel' hl] at this

instance decidableLoHiLe (lo hi : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Decidable (∀ x, lo ≤ x → x ≤ hi → P x) :=
  decidable_of_iff (∀ x, lo ≤ x → x < hi + 1 → P x) <|
    forall₂_congr fun _ _ ↦ imp_congr Nat.lt_succ_iff Iff.rfl

/-! ### `Nat.AtLeastTwo` -/

/-- A type class for natural numbers which are greater than or equal to `2`. -/
class AtLeastTwo (n : ℕ) : Prop where
  prop : 2 ≤ n

instance instAtLeastTwo {n : ℕ} : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ <| Nat.succ_le_succ <| Nat.zero_le _

instance {n : ℕ} [NeZero n] : (n + 1).AtLeastTwo := ⟨by have := NeZero.ne n; omega⟩

namespace AtLeastTwo

variable {n : ℕ} [n.AtLeastTwo]

lemma one_lt : 1 < n := prop
lemma ne_one : n ≠ 1 := Nat.ne_of_gt one_lt

end AtLeastTwo

end Nat
