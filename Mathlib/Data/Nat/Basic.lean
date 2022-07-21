import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic

namespace Nat

attribute [simp] succ_ne_zero lt_succ_self

-- TODO: in mathlib, this is done for ordered monoids
protected lemma pos_iff_ne_zero {n : ℕ} : 0 < n ↔ n ≠ 0 := by
  refine ⟨?_, Nat.pos_of_ne_zero⟩
  cases n with
  | zero   => intro h; contradiction
  | succ n => intro _; apply succ_ne_zero

protected lemma not_lt_of_le {n m : ℕ} (h₁ : m ≤ n) : ¬ n < m
| h₂ => Nat.not_le_of_gt h₂ h₁

protected lemma not_le_of_lt {n m : ℕ} : m < n → ¬ n ≤ m  := Nat.not_le_of_gt

protected lemma lt_of_not_le {a b : ℕ} : ¬ a ≤ b → b < a := (Nat.lt_or_ge b a).resolve_right

protected lemma le_of_not_lt {a b : ℕ} : ¬ a < b → b ≤ a := (Nat.lt_or_ge a b).resolve_left

protected lemma le_or_le (a b : ℕ) : a ≤ b ∨ b ≤ a := (Nat.lt_or_ge _ _).imp_left Nat.le_of_lt

protected lemma le_of_not_le {a b : ℕ} : ¬ a ≤ b → b ≤ a := (Nat.le_or_le _ _).resolve_left

protected lemma not_lt {n m : ℕ} : ¬ n < m ↔ m ≤ n :=
⟨Nat.le_of_not_lt, Nat.not_lt_of_le⟩

protected lemma not_le {n m : ℕ} : ¬ n ≤ m ↔ m < n :=
⟨Nat.lt_of_not_le, Nat.not_le_of_lt⟩

protected lemma lt_or_eq_of_le {n m : ℕ} (h : n ≤ m) : n < m ∨ n = m :=
(Nat.lt_or_ge _ _).imp_right (Nat.le_antisymm h)

theorem le_zero_iff {i : ℕ} : i ≤ 0 ↔ i = 0 :=
  ⟨Nat.eq_zero_of_le_zero, λ h => h ▸ le_refl i⟩

theorem lt_succ_iff {m n : ℕ} : m < succ n ↔ m ≤ n :=
⟨le_of_lt_succ, lt_succ_of_le⟩

/-! ### `succ` -/

lemma succ_eq_one_add (n : ℕ) : n.succ = 1 + n := by
  rw [Nat.succ_eq_add_one, Nat.add_comm]

theorem succ_inj' {n m : ℕ} : succ n = succ m ↔ n = m :=
⟨succ.inj, congr_arg _⟩

/- sub properties -/

lemma sub_lt_self {a b : ℕ} (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b := by
  apply sub_lt _ h₀
  apply Nat.lt_of_lt_of_le h₀ h₁

protected lemma add_sub_cancel' {n m : ℕ} (h : m ≤ n) : m + (n - m) = n :=
by rw [Nat.add_comm, Nat.sub_add_cancel h]

protected lemma sub_lt_sub_left : ∀ {k m n : ℕ}, k < m → k < n → m - n < m - k
| 0, m+1, n+1, _, _ => by rw [Nat.add_sub_add_right]; exact lt_succ_of_le (Nat.sub_le _ _)
| k+1, m+1, n+1, h1, h2 => by
  rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
  exact Nat.sub_lt_sub_left (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

protected lemma sub_lt_left_of_lt_add {n k m : ℕ} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this

protected lemma add_le_of_le_sub_left {n k m : ℕ} (H : m ≤ k) (h : n ≤ k - m) : m + n ≤ k :=
  Nat.not_lt.1 fun h' => Nat.not_lt.2 h (Nat.sub_lt_left_of_lt_add H h')

lemma le_sub_iff_add_le {x y k : ℕ} (h : k ≤ y) : x ≤ y - k ↔ x + k ≤ y :=
by rw [← Nat.add_sub_cancel x k, Nat.sub_le_sub_right_iff h, Nat.add_sub_cancel]

protected lemma min_comm (a b : ℕ) : Nat.min a b = Nat.min b a := by
  simp [Nat.min]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  · exact Nat.le_antisymm h₁ h₂
  · cases not_or_intro h₁ h₂ <| Nat.le_or_le _ _

protected lemma min_le_left (a b : ℕ) : Nat.min a b ≤ a := by
  simp [Nat.min]; by_cases a ≤ b <;> simp [h]
  exact Nat.le_of_not_le h

protected lemma min_eq_left (h : a ≤ b) : Nat.min a b = a :=
by simp [Nat.min, h]

protected lemma min_eq_right (h : b ≤ a) : Nat.min a b = b :=
by rw [Nat.min_comm a b]; exact Nat.min_eq_left h

protected def case_strong_rec_on {p : ℕ → Sort u} (a : ℕ)
  (hz : p 0) (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
Nat.strong_rec_on a fun | 0, _ => hz | n+1, ih => hi n (λ m w => ih m (lt_succ_of_le w))

theorem le_pred_of_lt {m n : Nat} (h : m < n) : m ≤ n - 1 :=
  Nat.sub_le_sub_right h 1

/- div -/

lemma mul_div_le (m n : ℕ) : n * (m / n) ≤ m := by
  match n, Nat.eq_zero_or_pos n with
  | _, Or.inl rfl => rw [Nat.zero_mul]; exact m.zero_le
  | n, Or.inr h => rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le h]; exact Nat.le_refl _

/- Up -/

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
def Up (ub a i : ℕ) := i < a ∧ i < ub

lemma Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.lt_succ_self _, h⟩

lemma Up.WF (ub) : WellFounded (Up ub) :=
  Subrelation.wf (h₂ := (measure (ub - .)).wf) fun ⟨ia, iu⟩ => Nat.sub_lt_sub_left iu ia

/-- A well-ordered relation for "upwards" induction on the natural numbers up to some bound `ub`. -/
def upRel (ub : ℕ) : WellFoundedRelation Nat := ⟨Up ub, Up.WF ub⟩

end Nat
