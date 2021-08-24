import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic

notation "ℕ" => Nat

namespace Nat

lemma succ_ne_self : ∀ n : ℕ, succ n ≠ n
| 0,   h => absurd h (Nat.succ_ne_zero 0)
| n+1, h => succ_ne_self n (Nat.noConfusion h id)

lemma eq_zero_of_add_eq_zero_right : ∀ {n m : ℕ}, n + m = 0 → n = 0
| 0,   m => by simp [Nat.zero_add]
| n+1, m => fun h => by
  exfalso
  rw [add_one, succ_add] at h
  apply succ_ne_zero _ h

lemma eq_zero_of_add_eq_zero_left {n m : ℕ} (h : n + m = 0) : m = 0 :=
@eq_zero_of_add_eq_zero_right m n (Nat.add_comm n m ▸ h)

@[simp] lemma pred_zero : pred 0 = 0 := rfl

@[simp] lemma pred_succ (n : ℕ) : pred (succ n) = n := rfl

protected lemma pos_of_ne_zero {n : ℕ} : n ≠ 0 → 0 < n :=
Or.resolve_left (eq_zero_or_pos n)

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

@[simp] protected lemma not_lt {n m : ℕ} : ¬ n < m ↔ m ≤ n :=
⟨Nat.le_of_not_lt, Nat.not_lt_of_le⟩

@[simp] protected lemma not_le {n m : ℕ} : ¬ n ≤ m ↔ m < n :=
⟨Nat.lt_of_not_le, Nat.not_le_of_lt⟩

protected lemma lt_or_eq_of_le {n m : ℕ} (h : n ≤ m) : n < m ∨ n = m :=
(Nat.lt_or_ge _ _).imp_right (Nat.le_antisymm h)

protected lemma lt_iff_le_not_le {m n : ℕ} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun h => Nat.gt_of_not_le h.2⟩

lemma pred_lt_pred : ∀ {n m : ℕ}, n ≠ 0 → n < m → pred n < pred m
| 0,   _,   h, _ => (h rfl).elim
| n+1, m+1, _, h => lt_of_succ_lt_succ h

protected lemma add_left_cancel_iff {n m k : ℕ} : n + m = n + k ↔ m = k :=
⟨Nat.add_left_cancel, fun | rfl => rfl⟩

protected lemma le_of_add_le_add_left {k n m : ℕ} (h : k + n ≤ k + m) : n ≤ m := by
  let ⟨w, hw⟩ := le.dest h
  rw [Nat.add_assoc, Nat.add_left_cancel_iff] at hw
  exact Nat.le.intro hw

protected lemma le_of_add_le_add_right {k n m : ℕ} : n + k ≤ m + k → n ≤ m := by
  rw [Nat.add_comm _ k, Nat.add_comm _ k]
  apply Nat.le_of_add_le_add_left

protected lemma add_le_add_iff_le_right (k n m : ℕ) : n + k ≤ m + k ↔ n ≤ m :=
⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h _⟩

protected lemma lt_of_add_lt_add_left {k n m : ℕ} (h : k + n < k + m) : n < m :=
Nat.lt_of_le_of_ne (Nat.le_of_add_le_add_left (Nat.le_of_lt h)) fun heq =>
  Nat.lt_irrefl (k + m) $ by rwa [heq] at h

protected lemma lt_add_of_pos_right {n k : ℕ} (h : 0 < k) : n < n + k :=
Nat.add_lt_add_left h n

protected lemma lt_add_of_pos_left {n k : ℕ} (h : 0 < k) : n < k + n :=
by rw [Nat.add_comm]; exact Nat.lt_add_of_pos_right h

protected lemma le_of_mul_le_mul_left {a b c : ℕ} (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
Nat.not_lt.1 fun h1 => Nat.not_le.2 (Nat.mul_lt_mul_of_pos_left h1 hc) h

lemma eq_of_mul_eq_mul_left {m k n : ℕ} (Hn : 0 < n) (H : n * m = n * k) : m = k :=
Nat.le_antisymm (Nat.le_of_mul_le_mul_left (Nat.le_of_eq H) Hn)
                (Nat.le_of_mul_le_mul_left (Nat.le_of_eq H.symm) Hn)

lemma eq_of_mul_eq_mul_right {n m k : ℕ} (Hm : 0 < m) (H : n * m = k * m) : n = k :=
by rw [Nat.mul_comm n m, Nat.mul_comm k m] at H
   exact Nat.eq_of_mul_eq_mul_left Hm H

protected lemma add_self_ne_one : ∀ (n : ℕ), n + n ≠ 1
| n+1, h =>
  have h1 : succ (succ (n + n)) = 1 := succ_add n n ▸ h
  Nat.noConfusion h1 fun.

/- sub properties -/

@[simp] protected lemma zero_sub : ∀ a : ℕ, 0 - a = 0
| 0     => rfl
| (a+1) => congr_arg pred (Nat.zero_sub a)

lemma sub_lt_succ (a b : ℕ) : a - b < succ a :=
lt_succ_of_le (sub_le a b)

protected lemma sub_le_sub_right {n m : ℕ} (h : n ≤ m) : ∀ k, n - k ≤ m - k
| 0   => h
| z+1 => pred_le_pred (Nat.sub_le_sub_right h z)

protected lemma add_sub_add_right : ∀ (n k m : ℕ), (n + k) - (m + k) = n - m
| n, 0,   m => by rw [Nat.add_zero, Nat.add_zero]
| n, k+1, m => by rw [add_succ, add_succ, succ_sub_succ, Nat.add_sub_add_right n k m]

protected lemma add_sub_add_left (k n m : ℕ) : (k + n) - (k + m) = n - m :=
by rw [Nat.add_comm k n, Nat.add_comm k m, Nat.add_sub_add_right]

protected lemma add_sub_cancel (n m : ℕ) : n + m - m = n :=
suffices n + m - (0 + m) = n by rwa [Nat.zero_add] at this
by rw [Nat.add_sub_add_right, Nat.sub_zero]

protected lemma add_sub_cancel_left (n m : ℕ) : n + m - n = m :=
show n + m - (n + 0) = m by rw [Nat.add_sub_add_left, Nat.sub_zero]

protected lemma sub_sub : ∀ (n m k : ℕ), n - m - k = n - (m + k)
| n, m, 0        => by rw [Nat.add_zero, Nat.sub_zero]
| n, m, (succ k) => by rw [add_succ, sub_succ, sub_succ, Nat.sub_sub n m k]

lemma sub_self_add (n m : ℕ) : n - (n + m) = 0 :=
show (n + 0) - (n + m) = 0 by rw [Nat.add_sub_add_left, Nat.zero_sub]

lemma sub_lt_self {a b : ℕ} (h₀ : 0 < a) (h₁ : a ≤ b) : b - a < b := by
  apply sub_lt _ h₀
  apply Nat.lt_of_lt_of_le h₀ h₁

lemma sub_one (n : ℕ) : n - 1 = pred n := rfl

lemma succ_sub_one (n : ℕ) : succ n - 1 = n := rfl

lemma succ_pred_eq_of_pos : ∀ {n : ℕ}, 0 < n → succ (pred n) = n
| n+1, _ => rfl

lemma succ_sub (h : n ≤ m) : succ m - n = succ (m - n) :=
  let ⟨k, hk⟩ := Nat.le.dest h
  by rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left]

lemma sub_eq_zero_of_le (h : n ≤ m) : n - m = 0 :=
let ⟨k, hk⟩ := Nat.le.dest h; by rw [← hk, sub_self_add]

protected lemma le_of_sub_eq_zero : {n m : ℕ} → n - m = 0 → n ≤ m
| n, 0, H => by rw [Nat.sub_zero] at H; simp [H]
| 0, m+1, H => zero_le _
| n+1, m+1, H => Nat.add_le_add_right
  (Nat.le_of_sub_eq_zero $ by simp [Nat.add_sub_add_right] at H; exact H) _

protected lemma sub_eq_zero_iff_le : n - m = 0 ↔ n ≤ m :=
⟨Nat.le_of_sub_eq_zero, Nat.sub_eq_zero_of_le⟩

lemma add_sub_of_le {n m : ℕ} (h : n ≤ m) : n + (m - n) = m :=
let ⟨k, hk⟩ := Nat.le.dest h; by rw [← hk, Nat.add_sub_cancel_left]

protected lemma sub_add_cancel {a b : ℕ} (h: a ≤ b) : b - a + a = b :=
by rw [Nat.add_comm, Nat.add_sub_of_le h]

protected lemma add_sub_cancel' {n m : ℕ} (h : m ≤ n) : m + (n - m) = n :=
by rw [Nat.add_comm, Nat.sub_add_cancel h]

protected lemma add_sub_assoc {m k : ℕ} (h : k ≤ m) (n : ℕ) : n + m - k = n + (m - k) :=
  let ⟨l, hl⟩ := Nat.le.dest h
  by rw [← hl, Nat.add_sub_cancel_left, Nat.add_comm k, ← Nat.add_assoc, Nat.add_sub_cancel]

protected lemma sub_eq_iff_eq_add {a b c : ℕ} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
⟨fun c_eq => by rw [c_eq.symm, Nat.sub_add_cancel ab],
 fun a_eq => by rw [a_eq, Nat.add_sub_cancel]⟩

protected lemma lt_of_sub_eq_succ (H : m - n = succ l) : n < m :=
Nat.not_le.1 fun H' => by simp [Nat.sub_eq_zero_of_le H'] at H

protected lemma lt_of_add_lt_add_right {a b c : ℕ} (h : a + b < c + b) : a < c :=
  Nat.lt_of_not_le fun h' => Nat.not_le_of_gt h (Nat.add_le_add_right h' _)

protected lemma sub_pos_of_lt (h : m < n) : 0 < n - m := by
  apply Nat.lt_of_add_lt_add_right (b := m)
  rw [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt h)]; exact h

protected lemma sub_lt_sub_left : ∀ {k m n : ℕ} (H : k < m) (h : k < n), m - n < m - k
| 0, m+1, n+1, _, _ => by rw [Nat.add_sub_add_right]; exact lt_succ_of_le (Nat.sub_le _ _)
| k+1, m+1, n+1, h1, h2 => by
  rw [Nat.add_sub_add_right, Nat.add_sub_add_right]
  exact Nat.sub_lt_sub_left (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)

protected lemma sub_lt_left_of_lt_add {n k m : ℕ} (H : n ≤ k) (h : k < n + m) : k - n < m := by
  have := Nat.sub_le_sub_right (succ_le_of_lt h) n
  rwa [Nat.add_sub_cancel_left, Nat.succ_sub H] at this

protected lemma add_le_of_le_sub_left {n k m : ℕ} (H : m ≤ k) (h : n ≤ k - m) : m + n ≤ k :=
  Nat.not_lt.1 fun h' => Nat.not_lt.2 h (Nat.sub_lt_left_of_lt_add H h')

lemma le_of_le_of_sub_le_sub_right {n m k : ℕ} (h₀ : k ≤ m) (h₁ : n - k ≤ m - k) : n ≤ m :=
  Nat.not_lt.1 fun h' => by
    have := Nat.add_le_of_le_sub_left h₀ h₁
    rw [Nat.add_sub_cancel'] at this; exact Nat.not_le.2 h' this
    exact Nat.le_trans h₀ (Nat.le_of_lt h')

protected lemma sub_le_sub_right_iff {n m k : ℕ} (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
⟨le_of_le_of_sub_le_sub_right h, fun h => Nat.sub_le_sub_right h k⟩

lemma le_sub_iff_add_le {x y k : ℕ} (h : k ≤ y) : x ≤ y - k ↔ x + k ≤ y :=
by rw [← Nat.add_sub_cancel x k, Nat.sub_le_sub_right_iff h, Nat.add_sub_cancel]

protected lemma min_comm (a b : ℕ) : Nat.min a b = Nat.min b a := by
  simp [Nat.min]
  by_cases h₁ : a ≤ b <;> by_cases h₂ : b ≤ a <;> simp [h₁, h₂]
  - (exact Nat.le_antisymm h₁ h₂)
  - cases not_or_intro h₁ h₂ (Nat.le_or_le _ _)

protected lemma min_le_left (a b : ℕ) : Nat.min a b ≤ a := by
  simp [Nat.min]; by_cases a ≤ b <;> simp [h]
  - (exact Nat.le_refl _)
  - exact Nat.le_of_not_le h

protected lemma min_eq_left (h : a ≤ b) : Nat.min a b = a :=
by simp [Nat.min, h]

protected lemma min_eq_right (h : b ≤ a) : Nat.min a b = b :=
by rw [Nat.min_comm a b]; exact Nat.min_eq_left h

protected lemma zero_min (a : ℕ) : Nat.min 0 a = 0 :=
Nat.min_eq_left (zero_le a)

protected lemma min_zero (a : ℕ) : Nat.min a 0 = 0 :=
Nat.min_eq_right (zero_le a)

lemma sub_eq_sub_min (n m : ℕ) : n - m = n - Nat.min n m :=
if h : n ≥ m then by rw [Nat.min_eq_right h] else by
  rw [sub_eq_zero_of_le (Nat.le_of_not_le h),
    Nat.min_eq_left (Nat.le_of_not_le h), Nat.sub_self]

@[simp] lemma sub_add_min_cancel (n m : ℕ) : n - m + Nat.min n m = n :=
by rw [sub_eq_sub_min, Nat.sub_add_cancel (Nat.min_le_left n m)]

protected def lt_wf := @Nat.ltWf

protected def strong_rec_on {p : ℕ → Sort u}
  (n : ℕ) (H : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
Nat.lt_wf.fix' H n

protected def case_strong_rec_on {p : ℕ → Sort u} (a : ℕ)
  (hz : p 0) (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
Nat.strong_rec_on a fun | 0, _ => hz | n+1, ih => hi n (λ m w => ih m (lt_succ_of_le w))

lemma mod_add_div (m k : ℕ) : m % k + k * (m / k) = m := by
  induction m, k using mod.inductionOn with rw [div_eq, mod_eq]
  | base x y h => simp [h]
  | ind x y h IH => simp [h]; rw [Nat.mul_succ, ← Nat.add_assoc, IH, Nat.sub_add_cancel h.2]

/- div -/

@[simp] protected lemma div_one (n : ℕ) : n / 1 = n :=
have this : n % 1 + 1 * (n / 1) = n := mod_add_div _ _
by rwa [mod_one, Nat.zero_add, Nat.one_mul] at this

@[simp] protected lemma div_zero (n : ℕ) : n / 0 = 0 :=
by rw [div_eq]; simp [Nat.lt_irrefl]

@[simp] protected lemma zero_div (b : ℕ) : 0 / b = 0 :=
(div_eq 0 b).trans $ if_neg $ And.rec Nat.not_le_of_gt

lemma le_div_iff_mul_le (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y := by
  induction y, k using mod.inductionOn generalizing x with
    (rw [div_eq]; simp [h]; cases x with simp [zero_le] | succ x => ?_)
  | base y k h =>
    simp [eq_false (not_succ_le_zero x), succ_mul, Nat.add_comm]
    refine Nat.lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
    exact Nat.lt_of_not_le fun h' => h ⟨k0, h'⟩
  | ind y k h IH =>
    rw [← add_one, Nat.add_le_add_iff_le_right, IH k0, succ_mul, le_sub_iff_add_le h.2]

lemma div_lt_iff_lt_mul (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← Nat.not_le, ← Nat.not_le]; apply not_congr; apply le_div_iff_mul_le Hk

lemma mul_div_le (m n : ℕ) : n * (m / n) ≤ m := by
  match n, Nat.eq_zero_or_pos n with
  | _, Or.inl rfl => rw [Nat.zero_mul]; exact m.zero_le
  | n, Or.inr h => rw [Nat.mul_comm, ← Nat.le_div_iff_mul_le h]; exact Nat.le_refl _

protected lemma div_le_of_le_mul : ∀ {k : ℕ}, m ≤ k * n → m / k ≤ n
| 0,   h => by simp [Nat.div_zero]; apply zero_le
| k+1, h => Nat.le_of_mul_le_mul_left (Nat.le_trans (mul_div_le _ _) h) (zero_lt_succ _)

protected lemma div_le_self : ∀ (m n : ℕ), m / n ≤ m
| m, 0   => by simp [Nat.div_zero]; apply zero_le
| m, n+1 => Nat.div_le_of_le_mul $ by
  have := Nat.mul_le_mul_right m (succ_pos n)
  rwa [Nat.one_mul] at this

lemma div_eq_sub_div (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; split <;> assumption

lemma div_eq_of_lt (h₀ : a < b) : a / b = 0 := by
  rw [div_eq a, if_neg]
  intro h₁
  apply Nat.not_le_of_gt h₀ h₁.right

/- successor and predecessor -/

lemma add_one_ne_zero (n : ℕ) : n + 1 ≠ 0 := succ_ne_zero _

lemma eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
by cases n <;> simp

lemma exists_eq_succ_of_ne_zero (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
⟨_, (eq_zero_or_eq_succ_pred _).resolve_left H⟩

def discriminate (H1: n = 0 → α) (H2 : ∀m, n = succ m → α) : α :=
  match e: n with
  | 0 => H1 e
  | succ m => H2 m e

lemma one_succ_zero : 1 = succ 0 := rfl

def two_step_induction {P : ℕ → Sort u} (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : (a : ℕ) → P a
| 0   => H1
| 1   => H2
| n+2 => H3 _ (two_step_induction H1 H2 H3 _) (two_step_induction H1 H2 H3 _)

def sub_induction {P : ℕ → ℕ → Sort u} (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : (n m : ℕ) → P n m
| 0,   m   => H1 _
| n+1, 0   => H2 _
| n+1, m+1 => H3 _ _ (sub_induction H1 H2 H3 n m)

/- addition -/

lemma succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
by simp [succ_add, add_succ]

lemma one_add (n : ℕ) : 1 + n = succ n := by simp [Nat.add_comm]

lemma eq_zero_of_add_eq_zero (H : n + m = 0) : n = 0 ∧ m = 0 :=
⟨Nat.eq_zero_of_add_eq_zero_right H, Nat.eq_zero_of_add_eq_zero_left H⟩

lemma eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
| 0,   m, _ => Or.inl rfl
| n+1, m, h => by rw [succ_mul] at h; exact Or.inr (eq_zero_of_add_eq_zero_left h)

/- properties of inequality -/

lemma le_succ_of_pred_le : pred n ≤ m → n ≤ succ m :=
match n with | 0 => fun _ => zero_le _ | a+1 => succ_le_succ

lemma le_lt_antisymm {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : False :=
Nat.lt_irrefl n (Nat.lt_of_le_of_lt h₁ h₂)

lemma lt_le_antisymm {n m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : False :=
le_lt_antisymm h₂ h₁

protected lemma lt_asymm {n m : ℕ} (h₁ : n < m) : ¬ m < n :=
le_lt_antisymm (Nat.le_of_lt h₁)

protected def lt_ge_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
if h : a < b then h₁ h else h₂ (Nat.not_lt.1 h)

protected def lt_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : a = b → C)
  (h₃ : b < a → C) : C :=
Nat.lt_ge_by_cases h₁ fun h₁ =>
  Nat.lt_ge_by_cases h₃ fun h => h₂ (Nat.le_antisymm h h₁)

protected lemma lt_trichotomy (a b : ℕ) : a < b ∨ a = b ∨ b < a :=
Nat.lt_by_cases Or.inl (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)

protected lemma eq_or_lt_of_not_lt {a b : ℕ} (hnlt : ¬ a < b) : a = b ∨ b < a :=
(Nat.lt_trichotomy a b).resolve_left hnlt

lemma lt_succ_of_lt (h : a < b) : a < succ b := le_succ_of_le h

lemma one_pos : 0 < 1 := Nat.zero_lt_one

/- subtraction -/

protected lemma sub_le_sub_left (k : ℕ) (h : n ≤ m) : k - m ≤ k - n :=
  match m, le.dest h with
  | _, ⟨a, rfl⟩ => by rw [← Nat.sub_sub]; apply sub_le

protected lemma sub.right_comm (m n k : ℕ) : m - n - k = m - k - n :=
by rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

lemma succ_sub_sub_succ (n m k : ℕ) : succ n - m - succ k = n - m - k :=
by rw [sub.right_comm, succ_sub_succ, sub.right_comm]

lemma mul_pred_left : ∀ (n m : ℕ), pred n * m = n * m - m
| 0,   m => by simp [Nat.zero_sub, pred_zero, Nat.zero_mul]
| n+1, m => by rw [pred_succ, succ_mul, Nat.add_sub_cancel]

lemma mul_pred_right (n m : ℕ) : n * pred m = n * m - n :=
by rw [Nat.mul_comm, mul_pred_left, Nat.mul_comm]

protected lemma mul_sub_right_distrib (n) : ∀ (m k : ℕ), (n - m) * k = n * k - m * k
| 0,   k => by simp [Nat.sub_zero, Nat.zero_mul]
| m+1, k => by rw [Nat.sub_succ, mul_pred_left, Nat.mul_sub_right_distrib, succ_mul, Nat.sub_sub]

protected lemma mul_sub_left_distrib (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by rw [Nat.mul_comm, Nat.mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]

protected lemma mul_self_sub_mul_self_eq (a b : Nat) : a * a - b * b = (a + b) * (a - b) :=
by rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a, Nat.add_comm (a*a) (a*b),
       Nat.add_sub_add_left]

lemma succ_mul_succ_eq (a b : Nat) : succ a * succ b = a*b + a + b + 1 := by
  rw [mul_succ, succ_mul, Nat.add_right_comm _ a]; rfl

protected lemma sub_sub_self {n m : ℕ} (h : m ≤ n) : n - (n - m) = m :=
(Nat.sub_eq_iff_eq_add (Nat.sub_le _ _)).2 (add_sub_of_le h).symm

protected lemma sub_add_comm {n m k : ℕ} (h : k ≤ n) : n + m - k = n - k + m :=
(Nat.sub_eq_iff_eq_add (Nat.le_trans h (Nat.le_add_right _ _))).2
  (by rwa [Nat.add_right_comm, Nat.sub_add_cancel])

lemma sub_one_sub_lt (h : i < n) : n - 1 - i < n := by
  rw [Nat.sub_sub]
  apply Nat.sub_lt
  apply Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) h
  rw [Nat.add_comm]
  apply Nat.zero_lt_succ

lemma pred_inj : ∀ {a b : ℕ}, 0 < a → 0 < b → Nat.pred a = Nat.pred b → a = b
| a+1, b+1, ha, hb, h => by rw [show a = b from h]
| a+1, 0,   ha, hb, h => absurd hb (Nat.lt_irrefl _)
| 0,   b+1, ha, hb, h => absurd ha (Nat.lt_irrefl _)
| 0,   0,   ha, hb, h => rfl

/- find -/

section find
variable (p : ℕ → Prop)

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

private def wf_lbp : WellFounded (lbp p) := by
  refine ⟨let ⟨n, pn⟩ := H; ?_⟩
  suffices ∀ m k, n ≤ k + m → Acc (lbp p) k from fun a => this _ _ (Nat.le_add_left _ _)
  intro m
  induction m with refine fun k kn => ⟨_, fun | _, ⟨rfl, a⟩ => ?_⟩
  | zero => exact absurd pn (a _ kn)
  | succ m IH => exact IH _ (by rw [Nat.add_right_comm]; exact kn)

protected def find_x : {n // p n ∧ ∀ m, m < n → ¬p m} :=
(wf_lbp p H).fix' (C := fun k => (∀n, n < k → ¬p n) → {n // p n ∧ ∀ m, m < n → ¬p m})
  (fun m IH al => if pm : p m then ⟨m, pm, al⟩ else
      have this : ∀ n, n ≤ m → ¬p n := fun n h =>
        (Nat.lt_or_eq_of_le h).elim (al n) fun e => by rw [e]; exact pm
      IH _ ⟨rfl, this⟩ fun n h => this n $ Nat.le_of_succ_le_succ h)
  0 fun n h => absurd h (Nat.not_lt_zero _)

/--
If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `nat.find hp` is the
smallest natural number satisfying `p`. Note that `nat.find` is protected,
meaning that you can't just write `find`, even if the `nat` namespace is open.

The API for `nat.find` is:

* `nat.find_spec` is the proof that `nat.find hp` satisfies `p`.
* `nat.find_min` is the proof that if `m < nat.find hp` then `m` does not satisfy `p`.
* `nat.find_min'` is the proof that if `m` does satisfy `p` then `nat.find hp ≤ m`.
-/
protected def find : ℕ := (Nat.find_x p H).1

protected lemma find_spec : p (Nat.find p H) := (Nat.find_x p H).2.1

protected lemma find_min : ∀ {m : ℕ}, m < Nat.find p H → ¬p m := @(Nat.find_x p H).2.2

protected lemma find_min' {m : ℕ} (h : p m) : Nat.find p H ≤ m :=
Nat.not_lt.1 fun l => Nat.find_min p H l h

end find

/- Up -/

/-- A well-ordered relation for "upwards" induction on the ℕural numbers up to some bound `ub`. -/
def Up (ub a i : ℕ) := i < a ∧ i < ub

lemma Up.next {ub i} (h : i < ub) : Up ub (i+1) i := ⟨Nat.lt_succ_self _, h⟩

lemma Up.WF (ub) : WellFounded (Up ub) :=
  Subrelation.wf (h₂ := measureWf (ub - .)) @fun a i ⟨ia, iu⟩ => Nat.sub_lt_sub_left iu ia

/- mod -/

@[simp] lemma add_mod_right (x z : ℕ) : (x + z) % z = x % z :=
by rw [mod_eq_sub_mod (Nat.le_add_left _ _), Nat.add_sub_cancel]

@[simp] lemma add_mod_left (x z : ℕ) : (x + z) % x = z % x :=
by rw [Nat.add_comm, add_mod_right]

@[simp] lemma add_mul_mod_self_left (x y z : ℕ) : (x + y * z) % y = x % y := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero]
  | succ z ih => rw [mul_succ, ← Nat.add_assoc, add_mod_right, ih]

@[simp] lemma add_mul_mod_self_right (x y z : ℕ) : (x + y * z) % z = x % z :=
by rw [Nat.mul_comm, add_mul_mod_self_left]

@[simp] lemma mul_mod_right (m n : ℕ) : (m * n) % m = 0 :=
by rw [← Nat.zero_add (m*n), add_mul_mod_self_left, zero_mod]

@[simp] lemma mul_mod_left (m n : ℕ) : (m * n) % n = 0 :=
by rw [Nat.mul_comm, mul_mod_right]

lemma mul_mod_mul_left (z x y : ℕ) : (z * x) % (z * y) = z * (x % y) :=
if y0 : y = 0 then
  by rw [y0, Nat.mul_zero, mod_zero, mod_zero]
else if z0 : z = 0 then
  by rw [z0, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul, mod_zero]
else by
  induction x using Nat.strong_rec_on with
  | _ n IH =>
    have y0 : y > 0 := Nat.pos_of_ne_zero y0
    have z0 : z > 0 := Nat.pos_of_ne_zero z0
    cases Nat.lt_or_ge n y with
    | inl yn => rw [mod_eq_of_lt yn, mod_eq_of_lt (Nat.mul_lt_mul_of_pos_left yn z0)]
    | inr yn =>
      rw [mod_eq_sub_mod yn, mod_eq_sub_mod (Nat.mul_le_mul_left z yn),
        ← Nat.mul_sub_left_distrib]
      exact IH _ (sub_lt (Nat.lt_of_lt_of_le y0 yn) y0)

lemma mul_mod_mul_right (z x y : ℕ) : (x * z) % (y * z) = (x % y) * z :=
by rw [Nat.mul_comm x z, Nat.mul_comm y z, Nat.mul_comm (x % y) z]; apply mul_mod_mul_left

lemma sub_mul_mod (x k n : ℕ) (h₁ : n*k ≤ x) : (x - n*k) % n = x % n := by
  induction k with
  | zero => rw [Nat.mul_zero, Nat.sub_zero]
  | succ k IH =>
    have h₂ : n * k ≤ x := by
      rw [mul_succ] at h₁
      apply Nat.le_trans _ h₁
      apply le_add_right _ n
    have h₄ : x - n * k ≥ n := by
      apply Nat.le_of_add_le_add_right (k := n*k)
      rw [Nat.sub_add_cancel h₂]
      simp [mul_succ, Nat.add_comm] at h₁; simp [h₁]
    rw [mul_succ, ← Nat.sub_sub, ← mod_eq_sub_mod h₄, IH h₂]

/- div -/

lemma sub_mul_div (x n p : ℕ) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p := by
  cases eq_zero_or_pos n with
  | inl h₀ => rw [h₀, Nat.div_zero, Nat.div_zero, Nat.zero_sub]
  | inr h₀ => induction p with
    | zero => rw [Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    | succ p IH =>
      have h₂ : n*p ≤ x := by
        transitivity
        - (apply Nat.mul_le_mul_left; apply le_succ)
        - apply h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        apply h₁
      rw [sub_succ, ← IH h₂]
      rw [div_eq_sub_div h₀ h₃]
      simp [add_one, pred_succ, mul_succ, Nat.sub_sub]

lemma div_mul_le_self : ∀ (m n : ℕ), m / n * n ≤ m
| m, 0   => by simp; apply zero_le
| m, n+1 => (le_div_iff_mul_le (Nat.succ_pos _)).1 (Nat.le_refl _)

@[simp] lemma add_div_right (x : ℕ) {z : ℕ} (H : 0 < z) : (x + z) / z = succ (x / z) :=
by rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]

@[simp] lemma add_div_left (x : ℕ) {z : ℕ} (H : 0 < z) : (z + x) / z = succ (x / z) :=
by rw [Nat.add_comm, add_div_right x H]

@[simp] lemma mul_div_right (n : ℕ) {m : ℕ} (H : 0 < m) : m * n / m = n :=
by induction n <;> simp_all [mul_succ]

@[simp] lemma mul_div_left (m : ℕ) {n : ℕ} (H : 0 < n) : m * n / n = m :=
by rw [Nat.mul_comm, mul_div_right _ H]

protected lemma div_self (H : 0 < n) : n / n = 1 :=
let t := add_div_right 0 H; by rwa [Nat.zero_add, Nat.zero_div] at t

lemma add_mul_div_left (x z : ℕ) {y : ℕ} (H : 0 < y) : (x + y * z) / y = x / y + z := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ z ih => rw [mul_succ, ← Nat.add_assoc, add_div_right _ H, ih]; rfl

lemma add_mul_div_right (x y : ℕ) {z : ℕ} (H : 0 < z) : (x + y * z) / z = x / z + y :=
by rw [Nat.mul_comm, add_mul_div_left _ _ H]

protected lemma mul_div_cancel (m : ℕ) {n : ℕ} (H : 0 < n) : m * n / n = m :=
let t := add_mul_div_right 0 m H; by rwa [Nat.zero_add, Nat.zero_div, Nat.zero_add] at t

protected lemma mul_div_cancel_left (m : ℕ) {n : ℕ} (H : 0 < n) : n * m / n = m :=
by rw [Nat.mul_comm, Nat.mul_div_cancel _ H]

protected lemma div_eq_of_eq_mul_left (H1 : 0 < n) (H2 : m = k * n) : m / n = k :=
by rw [H2, Nat.mul_div_cancel _ H1]

protected lemma div_eq_of_eq_mul_right (H1 : 0 < n) (H2 : m = n * k) : m / n = k :=
by rw [H2, Nat.mul_div_cancel_left _ H1]

protected lemma div_eq_of_lt_le
  (lo : k * n ≤ m) (hi : m < succ k * n) : m / n = k :=
have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun hn => by
  rw [hn, Nat.mul_zero] at hi lo; exact absurd lo (Nat.not_le_of_gt hi)
Nat.le_antisymm
  (le_of_lt_succ ((Nat.div_lt_iff_lt_mul npos).2 hi))
  ((Nat.le_div_iff_mul_le npos).2 lo)

lemma mul_sub_div (x n p : ℕ) (h₁ : x < n*p) : (n * p - succ x) / n = p - succ (x / n) := by
  have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun n0 => by
    rw [n0, Nat.zero_mul] at h₁; exact not_lt_zero _ h₁
  (apply Nat.div_eq_of_lt_le)
  - rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
    apply Nat.sub_le_sub_left
    (exact (div_lt_iff_lt_mul npos).1 (lt_succ_self _))
  - change succ (pred (n * p - x)) ≤ (succ (pred (p - x / n))) * n
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
      fun h => succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)] -- TODO: why is the function needed?
    - rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
      (apply Nat.sub_le_sub_left; apply div_mul_le_self)
    - apply (div_lt_iff_lt_mul npos).2; rwa [Nat.mul_comm]

protected lemma div_div_eq_div_mul (m n k : ℕ) : m / n / k = m / (n * k) := by
  cases eq_zero_or_pos k with
  | inl k0 => rw [k0, Nat.mul_zero, Nat.div_zero, Nat.div_zero] | inr kpos => ?_
  cases eq_zero_or_pos n with
  | inl n0 => rw [n0, Nat.zero_mul, Nat.div_zero, Nat.zero_div] | inr npos => ?_
  (apply Nat.le_antisymm)
  - apply (le_div_iff_mul_le (Nat.mul_pos npos kpos)).2
    rw [Nat.mul_comm n k, ← Nat.mul_assoc]
    apply (le_div_iff_mul_le npos).1
    apply (le_div_iff_mul_le kpos).1
    (apply Nat.le_refl)
  - apply (le_div_iff_mul_le kpos).2
    apply (le_div_iff_mul_le npos).2
    rw [Nat.mul_assoc, Nat.mul_comm n k]
    apply (le_div_iff_mul_le (Nat.mul_pos kpos npos)).1
    apply Nat.le_refl

protected lemma mul_div_mul {m : ℕ} (n k : ℕ) (H : 0 < m) : m * n / (m * k) = n / k :=
by rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]

protected lemma mul_le_mul_of_nonneg_left {a b c : ℕ} (h₁ : a ≤ b) : c * a ≤ c * b := by
  by_cases hba: b ≤ a; { simp [Nat.le_antisymm hba h₁]; apply Nat.le_refl }
  by_cases hc0 : c ≤ 0; { simp [Nat.le_antisymm hc0 (zero_le c), Nat.zero_mul] }
  exact Nat.le_of_lt (Nat.mul_lt_mul_of_pos_left (Nat.not_le.1 hba) (Nat.not_le.1 hc0))

protected lemma mul_le_mul_of_nonneg_right {a b c : ℕ} (h₁ : a ≤ b) : a * c ≤ b * c := by
  by_cases hba : b ≤ a; { simp [Nat.le_antisymm hba h₁]; apply Nat.le_refl }
  by_cases hc0 : c ≤ 0; { simp [Nat.le_antisymm hc0 (zero_le c), Nat.mul_zero] }
  exact Nat.le_of_lt (Nat.mul_lt_mul_of_pos_right (Nat.not_le.1 hba) (Nat.not_le.1 hc0))

protected lemma mul_lt_mul (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) : a * b < c * d :=
Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hac pos_b) (Nat.mul_le_mul_of_nonneg_left hbd)

protected lemma mul_lt_mul' (h1 : a ≤ c) (h2 : b < d) (h3 : 0 < c) : a * b < c * d :=
Nat.lt_of_le_of_lt (Nat.mul_le_mul_of_nonneg_right h1) (Nat.mul_lt_mul_of_pos_left h2 h3)

lemma div_lt_self (h₁ : 0 < n) (h₂ : 1 < m) : n / m < n := by
  have m_pos : 0 < m := Nat.lt_trans Nat.zero_lt_one h₂
  suffices 1 * n < m * n by
    rw [Nat.one_mul, Nat.mul_comm] at this
    exact (Nat.div_lt_iff_lt_mul m_pos).2 this
  exact Nat.mul_lt_mul h₂ (Nat.le_refl _) h₁

end Nat
