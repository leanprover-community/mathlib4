/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Aaron Liu
-/

import Mathlib.Data.Nat.Basic
import Batteries.WF

/-!
# `Nat.find` and `Nat.findGreatest`
-/

variable {m n k : ℕ}

namespace Nat

section FindFrom

variable {p q : (n : ℕ) → k ≤ n → Prop} [∀ n h, Decidable (p n h)] (H : ∃ n h, p n h)

/-! ### `Nat.findFrom` -/

private def lbp (m n : { n : ℕ // k ≤ n}) : Prop :=
  m.1 = n.1 + 1 ∧ ∀ k h, k ≤ n.1 → ¬p k h

private def wf_lbp : WellFounded (@lbp k p) :=
  ⟨let ⟨n, h, pn⟩ := H
    suffices ∀ m k, n ≤ k.1 + m → Acc lbp k from fun _ => this _ _ (le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun _ kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨_, a⟩ => absurd pn (a _ _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨h, _⟩ => IH _ (by rw [h, Nat.add_right_comm]; exact kn)⟩⟩

protected def findFromX : { n // ∃ h, p n h ∧ ∀ m h, m < n → ¬p m h } :=
  @WellFounded.fix { n : ℕ // k ≤ n}
    (fun k => (∀ n h, n < k.1 → ¬p n h) → { n // ∃ h, p n h ∧ ∀ m h, m < n → ¬p m h })
    lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m.1 m.2 then ⟨m.1, m.2, pm, al⟩
      else
        have : ∀ n h, n ≤ m.1 → ¬p n h := fun n hn h =>
          Or.elim (lt_or_eq_of_le h) (al n hn) fun e => e ▸ pm
        IH ⟨m.1 + 1, le_trans m.2 (le_succ m.1)⟩ ⟨rfl, this⟩
          fun n hn h => this n hn (le_of_lt_succ h))
    ⟨k, le_rfl⟩ fun _ hn h => not_le_of_lt h hn |>.elim

/-- If `p` is a (decidable) predicate on `ℕ` that depends on `h : k ≤ n` and
`hp : ∃ (n : ℕ) (h : k ≤ n), p n h` is a proof that there exists
some natural number at least `k` satisfying `p`, then `Nat.findFrom hp` is the
smallest natural number at least `k` satisfying `p`. Note that `Nat.findFrom` is protected,
meaning that you can't just write `findFrom`, even if the `Nat` namespace is open.

The API for `Nat.findFrom` is:

* `Nat.findFrom_spec` is the proof that `Nat.findFrom hp` satisfies `p`.
* `Nat.le_findFrom` is a proof that `Nat.findFrom hp` is at least `k`.
* `Nat.findFrom_min` is the proof that if `m < Nat.findFrom hp` then `m` does not satisfy `p`.
* `Nat.findFrom_min'` is the proof that if `m` does satisfy `p` then `Nat.findFrom hp ≤ m`.

See also `Nat.find`.
-/
protected def findFrom : ℕ :=
  (Nat.findFromX H).1

protected theorem le_findFrom : k ≤ Nat.findFrom H :=
  (Nat.findFromX H).2.1

protected theorem findFrom_spec : p (Nat.findFrom H) (Nat.le_findFrom H) :=
  (Nat.findFromX H).2.2.1

protected theorem findFrom_min : ∀ {m : ℕ} h, m < Nat.findFrom H → ¬p m h :=
  @(Nat.findFromX H).2.2.2

protected theorem findFrom_min' {m} hm (h : p m hm) : Nat.findFrom H ≤ m :=
  Nat.le_of_not_lt fun l => Nat.findFrom_min H hm l h

lemma findFrom_eq_iff (h : ∃ n h, p n h) :
    Nat.findFrom h = m ↔ ∃ h, p m h ∧ ∀ n h, n < m → ¬p n h := by
  constructor
  · rintro rfl
    exact ⟨_, Nat.findFrom_spec h, fun _ ↦ Nat.findFrom_min h⟩
  · intro ⟨hm, hp, hlt⟩
    exact le_antisymm (Nat.findFrom_min' h hm hp)
      (not_lt.1 <| imp_not_comm.1 (hlt _ _) <| Nat.findFrom_spec h)

@[simp] lemma findFrom_lt_iff (h : ∃ n h, p n h) (n : ℕ) :
    Nat.findFrom h < n ↔ ∃ m h, m < n ∧ p m h :=
  ⟨fun h2 ↦ ⟨Nat.findFrom h, Nat.le_findFrom h, h2, Nat.findFrom_spec h⟩,
    fun ⟨_, hkn, hmn, hm⟩ ↦ lt_of_le_of_lt (Nat.findFrom_min' h hkn hm) hmn⟩

@[simp] lemma findFrom_le_iff (h : ∃ n h, p n h) (n : ℕ) :
    Nat.findFrom h ≤ n ↔ ∃ m h, m ≤ n ∧ p m h := by
  simp only [← Nat.lt_succ_iff, findFrom_lt_iff, exists_and_left]

@[simp] lemma le_findFrom_iff (h : ∃ n h, p n h) (n : ℕ) :
    n ≤ Nat.findFrom h ↔ ∀ m h, m < n → ¬p m h := by
  simp only [← not_lt, findFrom_lt_iff, not_exists, not_and]

@[simp] lemma lt_findFrom_iff (h : ∃ n h, p n h) (n : ℕ) :
    n < Nat.findFrom h ↔ ∀ m h, m ≤ n → ¬p m h := by
  simp only [← succ_le_iff, le_findFrom_iff, succ_le_succ_iff]

@[simp] lemma findFrom_eq_start (h : ∃ n h, p n h) : Nat.findFrom h = k ↔ p k (Nat.le_refl k) := by
  simp +contextual [findFrom_eq_iff, not_lt_of_le]

/-- If a predicate `q` holds at some `x` and implies `p` from `k` up to that `x`, then
the earliest `xq` such that `q xq` is at least the smallest `xp` where `p xp`.
The stronger version of `Nat.findFrom_mono`, since this one needs
implication only up to `Nat.findFrom _` while the other requires `q` implying `p` everywhere. -/
lemma findFrom_mono_of_le [∀ n h, Decidable (q n h)] {x : ℕ} (h : k ≤ x) (hx : q x h)
    (hpq : ∀ n h, n ≤ x → q n h → p n h) :
    Nat.findFrom ⟨x, h, show p x h from hpq x h le_rfl hx⟩ ≤ Nat.findFrom ⟨x, h, hx⟩ :=
  Nat.findFrom_min' _ _ (hpq _ _ (Nat.findFrom_min' _ h hx) (Nat.findFrom_spec ⟨x, h, hx⟩))

/-- A weak version of `Nat.findFrom_mono_of_le`, requiring `q` implies `p` everywhere.
-/
lemma findFrom_mono [∀ n h, Decidable (q n h)] (h : ∀ n h, q n h → p n h)
    {hp : ∃ n h, p n h} {hq : ∃ n h, q n h} :
    Nat.findFrom hp ≤ Nat.findFrom hq :=
  let ⟨_, _, hq⟩ := hq; findFrom_mono_of_le _ hq fun _ _ _ ↦ h _ _

/-- If a predicate `p` holds at some `x` and agrees with `q` up to that `x`, then
their `Nat.findFrom` agree. The stronger version of `Nat.findFrom_congr'`, since this one needs
agreement only up to `Nat.findFrom _` while the other requires `p = q`.
Usage of this lemma will likely be via `obtain ⟨x, h, hx⟩ := hp; apply Nat.findFrom_congr h hx`
to unify `q`, or provide it explicitly with `rw [Nat.findFrom_congr (q := q) h hx]`.
-/
lemma findFrom_congr [∀ n h, Decidable (q n h)] {x : ℕ} (h : k ≤ x) (hx : p x h)
    (hpq : ∀ n h, n ≤ x → (p n h ↔ q n h)) :
    Nat.findFrom ⟨x, h, hx⟩ = Nat.findFrom ⟨x, h, show q x h from hpq _ _ le_rfl |>.1 hx⟩ :=
  le_antisymm (findFrom_mono_of_le h (hpq _ _ le_rfl |>.1 hx) fun _ _ h ↦ (hpq _ _ h).mpr)
    (findFrom_mono_of_le h hx fun _ _ h ↦ (hpq _ _ h).mp)

/-- A weak version of `Nat.findFrom_congr`, requiring `p = q` everywhere. -/
lemma findFrom_congr' [∀ n h, Decidable (q n h)] {hp : ∃ n h, p n h} {hq : ∃ n h, q n h}
    (hpq : ∀ {n} h, p n h ↔ q n h) :
    Nat.findFrom hp = Nat.findFrom hq :=
  let ⟨_, _, hp⟩ := hp; findFrom_congr _ hp fun _ _ _ ↦ hpq _

lemma findFrom_le {h : ∃ n h, p n h} (hn : k ≤ n) (hn : p n hn) : Nat.findFrom h ≤ n :=
  (findFrom_le_iff _ _).2 ⟨n, _, le_rfl, hn⟩

lemma findFrom_comp_succ (h₁ : ∃ n h, p n h)
    (h₂ : ∃ n h, p (n + 1) (Nat.le_trans h (Nat.le_succ n)))
    (hk : ¬p k (Nat.le_refl k)) :
    Nat.findFrom h₁ = Nat.findFrom h₂ + 1 := by
  refine (findFrom_eq_iff _).2 ⟨_, Nat.findFrom_spec h₂, fun n h hn ↦ ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  cases d
  exacts [hk, Nat.findFrom_min h₂ (le_add_right k _) (succ_lt_succ_iff.1 hn)]

lemma start_lt_findFrom (h : ∃ n h, p n h) : k < Nat.findFrom h ↔ ¬p k (Nat.le_refl k) :=
  calc k < Nat.findFrom h
    _ ↔ k ≤ Nat.findFrom h ∧ k ≠ Nat.findFrom h := Nat.lt_iff_le_and_ne
    _ ↔ k ≠ Nat.findFrom h := and_iff_right (Nat.le_findFrom h)
    _ ↔ Nat.findFrom h ≠ k := ne_comm
    _ ↔ ¬p k le_rfl := (findFrom_eq_start _).not

lemma findFrom_add {hₘ : ∃ m h, p (m + n) (Nat.le_add_right_of_le h)} {hₙ : ∃ n h, p n h}
    (hn : n + k ≤ Nat.findFrom hₙ) : Nat.findFrom hₘ + n = Nat.findFrom hₙ := by
  refine le_antisymm ((le_findFrom_iff _ _).2 fun m h hm hpm => not_le.2 hm ?_) ?_
  · have hnm : n ≤ m := calc
      _ ≤ n + k := le_add_right n k
      _ ≤ Nat.findFrom hₙ := hn
      _ ≤ m := findFrom_le h hpm
    refine add_le_of_le_sub hnm (findFrom_le ?_ ?_)
    · rw [Nat.le_sub_iff_add_le' hnm]
      exact le_trans hn (Nat.findFrom_min' hₙ h hpm)
    · conv =>
        arg 1
        rw [Nat.sub_add_cancel hnm]
      exact hpm
  · rw [← Nat.sub_le_iff_le_add]
    refine (le_findFrom_iff _ _).2 fun m h hm hpm => not_le.2 hm ?_
    rw [Nat.sub_le_iff_le_add]
    exact findFrom_le _ hpm

end FindFrom

section Find

variable {p q : ℕ → Prop} [DecidablePred p] (H : ∃ n, p n)

/-! ### `Nat.find` -/

private def H' : ∃ (n : ℕ) (_ : 0 ≤ n), p n := H.imp fun n hn => ⟨zero_le n, hn⟩

protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  ⟨(Nat.findFromX (H' H)).1, (Nat.findFromX (H' H)).2.2.1,
    fun m => (Nat.findFromX (H' H)).2.2.2 m (zero_le m)⟩

/-- If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisfy `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ m`.

See also `Nat.findFrom`.
-/
protected def find : ℕ :=
  Nat.findFrom (H' H)

protected theorem find_spec : p (Nat.find H) :=
  Nat.findFrom_spec (H' H)

protected theorem find_min {m : ℕ} : m < Nat.find H → ¬p m :=
  Nat.findFrom_min (H' H) (zero_le m)

protected theorem find_min' {m : ℕ} : p m → Nat.find H ≤ m :=
  Nat.findFrom_min' (H' H) (zero_le m)

lemma find_eq_iff (h : ∃ n : ℕ, p n) : Nat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  simpa using findFrom_eq_iff (H' h)

@[simp] lemma find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h < n ↔ ∃ m < n, p m := by
  simp [Nat.find]

@[simp] lemma find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← Nat.lt_succ_iff, find_lt_iff]

@[simp] lemma le_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n ≤ Nat.find h ↔ ∀ m < n, ¬ p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]

@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < Nat.find h ↔ ∀ m ≤ n, ¬ p m := by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]

@[simp] lemma find_eq_zero (h : ∃ n : ℕ, p n) : Nat.find h = 0 ↔ p 0 := by simp [find_eq_iff]

/-- If a predicate `q` holds at some `x` and implies `p` up to that `x`, then
the earliest `xq` such that `q xq` is at least the smallest `xp` where `p xp`.
The stronger version of `Nat.find_mono`, since this one needs
implication only up to `Nat.find _` while the other requires `q` implying `p` everywhere. -/
lemma find_mono_of_le [DecidablePred q] {x : ℕ} (hx : q x) (hpq : ∀ n ≤ x, q n → p n) :
    Nat.find ⟨x, show p x from hpq _ le_rfl hx⟩ ≤ Nat.find ⟨x, hx⟩ :=
  Nat.find_min' _ (hpq _ (Nat.find_min' _ hx) (Nat.find_spec ⟨x, hx⟩))

/-- A weak version of `Nat.find_mono_of_le`, requiring `q` implies `p` everywhere.
-/
lemma find_mono [DecidablePred q] (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
    Nat.find hp ≤ Nat.find hq :=
  let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ ↦ h _

/-- If a predicate `p` holds at some `x` and agrees with `q` up to that `x`, then
their `Nat.find` agree. The stronger version of `Nat.find_congr'`, since this one needs
agreement only up to `Nat.find _` while the other requires `p = q`.
Usage of this lemma will likely be via `obtain ⟨x, hx⟩ := hp; apply Nat.find_congr hx` to unify `q`,
or provide it explicitly with `rw [Nat.find_congr (q := q) hx]`.
-/
lemma find_congr [DecidablePred q] {x : ℕ} (hx : p x) (hpq : ∀ n ≤ x, p n ↔ q n) :
    Nat.find ⟨x, hx⟩ = Nat.find ⟨x, show q x from hpq _ le_rfl |>.1 hx⟩ :=
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hx) fun _ h ↦ (hpq _ h).mpr)
    (find_mono_of_le hx fun _ h ↦ (hpq _ h).mp)

/-- A weak version of `Nat.find_congr`, requiring `p = q` everywhere. -/
lemma find_congr' [DecidablePred q] {hp : ∃ n, p n} {hq : ∃ n, q n} (hpq : ∀ {n}, p n ↔ q n) :
    Nat.find hp = Nat.find hq :=
  let ⟨_, hp⟩ := hp; find_congr hp fun _ _ ↦ hpq

lemma find_le {h : ∃ n, p n} (hn : p n) : Nat.find h ≤ n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩

lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬ p 0) :
    Nat.find h₁ = Nat.find h₂ + 1 :=
  findFrom_comp_succ (H' h₁) (H' h₂) h0

lemma find_pos (h : ∃ n : ℕ, p n) : 0 < Nat.find h ↔ ¬p 0 :=
  start_lt_findFrom (H' h)

lemma find_add {hₘ : ∃ m, p (m + n)} {hₙ : ∃ n, p n} (hn : n ≤ Nat.find hₙ) :
    Nat.find hₘ + n = Nat.find hₙ :=
  findFrom_add (hₘ := H' hₘ) (hₙ := H' hₙ) hn

end Find

/-! ### `Nat.findGreatest` -/

section FindGreatest

/-- `Nat.findGreatest P n` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
def findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else Nat.findGreatest P n

variable {P Q : ℕ → Prop} [DecidablePred P] {n : ℕ}

@[simp] lemma findGreatest_zero : Nat.findGreatest P 0 = 0 := rfl

lemma findGreatest_succ (n : ℕ) :
    Nat.findGreatest P (n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n := rfl

@[simp] lemma findGreatest_eq : ∀ {n}, P n → Nat.findGreatest P n = n
  | 0, _ => rfl
  | n + 1, h => by simp [Nat.findGreatest, h]

@[simp]
lemma findGreatest_of_not (h : ¬ P (n + 1)) : findGreatest P (n + 1) = findGreatest P n := by
  simp [Nat.findGreatest, h]

lemma findGreatest_eq_iff :
    Nat.findGreatest P k = m ↔ m ≤ k ∧ (m ≠ 0 → P m) ∧ ∀ ⦃n⦄, m < n → n ≤ k → ¬P n := by
  induction k generalizing m with
  | zero =>
    rw [eq_comm, Iff.comm]
    simp only [zero_eq, Nat.le_zero, ne_eq, findGreatest_zero, and_iff_left_iff_imp]
    rintro rfl
    exact ⟨fun h ↦ (h rfl).elim, fun n hlt heq ↦ by omega⟩
  | succ k ihk =>
    by_cases hk : P (k + 1)
    · rw [findGreatest_eq hk]
      constructor
      · rintro rfl
        exact ⟨le_refl _, fun _ ↦ hk, fun n hlt hle ↦ by omega⟩
      · rintro ⟨hle, h0, hm⟩
        rcases Decidable.eq_or_lt_of_le hle with (rfl | hlt)
        exacts [rfl, (hm hlt (le_refl _) hk).elim]
    · rw [findGreatest_of_not hk, ihk]
      constructor
      · rintro ⟨hle, hP, hm⟩
        refine ⟨le_trans hle k.le_succ, hP, fun n hlt hle ↦ ?_⟩
        rcases Decidable.eq_or_lt_of_le hle with (rfl | hlt')
        exacts [hk, hm hlt <| Nat.lt_succ_iff.1 hlt']
      · rintro ⟨hle, hP, hm⟩
        refine ⟨Nat.lt_succ_iff.1 (lt_of_le_of_ne hle ?_), hP,
          fun n hlt hle ↦ hm hlt (le_trans hle k.le_succ)⟩
        rintro rfl
        exact hk (hP k.succ_ne_zero)

lemma findGreatest_eq_zero_iff : Nat.findGreatest P k = 0 ↔ ∀ ⦃n⦄, 0 < n → n ≤ k → ¬P n := by
  simp [findGreatest_eq_iff]

@[simp] lemma findGreatest_pos : 0 < Nat.findGreatest P k ↔ ∃ n, 0 < n ∧ n ≤ k ∧ P n := by
  rw [Nat.pos_iff_ne_zero, Ne, findGreatest_eq_zero_iff]; push_neg; rfl

lemma findGreatest_spec (hmb : m ≤ n) (hm : P m) : P (Nat.findGreatest P n) := by
  by_cases h : Nat.findGreatest P n = 0
  · cases m
    · rwa [h]
    exact ((findGreatest_eq_zero_iff.1 h) (zero_lt_succ _) hmb hm).elim
  · exact (findGreatest_eq_iff.1 rfl).2.1 h

lemma findGreatest_le (n : ℕ) : Nat.findGreatest P n ≤ n :=
  (findGreatest_eq_iff.1 rfl).1

lemma le_findGreatest (hmb : m ≤ n) (hm : P m) : m ≤ Nat.findGreatest P n :=
  le_of_not_lt fun hlt => (findGreatest_eq_iff.1 rfl).2.2 hlt hmb hm

lemma findGreatest_mono_right (P : ℕ → Prop) [DecidablePred P] {m n} (hmn : m ≤ n) :
    Nat.findGreatest P m ≤ Nat.findGreatest P n := by
  induction hmn with
  | refl => simp
  | step hmk ih =>
    rw [findGreatest_succ]
    split_ifs
    · exact le_trans ih <| le_trans (findGreatest_le _) (le_succ _)
    · exact ih

lemma findGreatest_mono_left [DecidablePred Q] (hPQ : ∀ n, P n → Q n) (n : ℕ) :
    Nat.findGreatest P n ≤ Nat.findGreatest Q n := by
  induction n with
  | zero => rfl
  | succ n hn =>
    by_cases h : P (n + 1)
    · rw [findGreatest_eq h, findGreatest_eq (hPQ _ h)]
    · rw [findGreatest_of_not h]
      exact le_trans hn (Nat.findGreatest_mono_right _ <| le_succ _)

lemma findGreatest_mono [DecidablePred Q] (hPQ : ∀ n, P n → Q n) (hmn : m ≤ n) :
    Nat.findGreatest P m ≤ Nat.findGreatest Q n :=
  le_trans (Nat.findGreatest_mono_right _ hmn) (findGreatest_mono_left hPQ _)

theorem findGreatest_is_greatest (hk : Nat.findGreatest P n < k) (hkb : k ≤ n) : ¬P k :=
  (findGreatest_eq_iff.1 rfl).2.2 hk hkb

theorem findGreatest_of_ne_zero (h : Nat.findGreatest P n = m) (h0 : m ≠ 0) : P m :=
  (findGreatest_eq_iff.1 h).2.1 h0

end FindGreatest

end Nat
