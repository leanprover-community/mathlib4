/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Algebra.Functions

universe u

namespace Nat

lemma succ_ne_self : ∀ n : ℕ, succ n ≠ n
| 0,   h => absurd h (Nat.succ_ne_zero 0)
| n+1, h => succ_ne_self n (Nat.noConfusion h id)

protected lemma eq_zero_of_add_eq_zero_right : ∀ {n m : ℕ}, n + m = 0 → n = 0
| 0,   m => by simp [Nat.zero_add]
| n+1, m => fun h => by
  exfalso
  rw [add_one, succ_add] at h
  apply succ_ne_zero _ h

protected lemma eq_zero_of_add_eq_zero_left {n m : ℕ} (h : n + m = 0) : m = 0 :=
@Nat.eq_zero_of_add_eq_zero_right m n (Nat.add_comm n m ▸ h)

attribute [simp] Nat.pred_zero Nat.pred_succ

/-

private meta def sort_add :=
`[simp [nat.add_assoc, nat.add_comm, nat.add_left_comm]]
-/

/- properties of inequality -/

protected lemma pos_of_ne_zero {n : ℕ} : n ≠ 0 → 0 < n :=
Or.resolve_left (eq_zero_or_pos n)

protected lemma lt_iff_le_not_le {m n : ℕ} : m < n ↔ m ≤ n ∧ ¬ n ≤ m :=
⟨fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩, fun h => Nat.gt_of_not_le h.2⟩

instance : LinearOrder ℕ :=
{ le := Nat.le,
  le_refl := @Nat.le_refl,
  le_trans := @Nat.le_trans,
  le_antisymm := @Nat.le_antisymm,
  le_total := @Nat.le_total,
  lt := Nat.lt,
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le,
  decidable_lt               := inferInstance,
  decidable_le               := inferInstance,
  decidable_eq               := inferInstance }

lemma pred_lt_pred : ∀ {n m : ℕ}, n ≠ 0 → n < m → pred n < pred m
| 0,   _,   h, _ => (h rfl).elim
| n+1, m+1, _, h => lt_of_succ_lt_succ h

-- Port note: this lemma was not present in Lean 3
protected lemma add_left_cancel_iff {n m k : ℕ} : n + m = n + k ↔ m = k :=
⟨Nat.add_left_cancel, fun | rfl => rfl⟩

protected lemma add_le_add_iff_le_right (k n m : ℕ) : n + k ≤ m + k ↔ n ≤ m :=
⟨Nat.le_of_add_le_add_right, fun h => Nat.add_le_add_right h _⟩

protected lemma lt_of_add_lt_add_left {k n m : ℕ} (h : k + n < k + m) : n < m :=
Nat.lt_of_le_of_ne (Nat.le_of_add_le_add_left (Nat.le_of_lt h)) fun heq =>
  Nat.lt_irrefl (k + m) $ by rwa [heq] at h

protected lemma lt_of_add_lt_add_right {a b c : ℕ} (h : a + b < c + b) : a < c :=
  Nat.lt_of_add_lt_add_left ((by rwa [Nat.add_comm b a, Nat.add_comm b c]): b + a < b + c)

protected lemma lt_add_right (a b c : Nat) : a < b -> a < b + c :=
  fun h => lt_of_lt_of_le h (Nat.le_add_right _ _)

protected lemma lt_add_of_pos_right {n k : ℕ} (h : 0 < k) : n < n + k :=
Nat.add_lt_add_left h n

protected lemma lt_add_of_pos_left {n k : ℕ} (h : 0 < k) : n < k + n :=
by rw [Nat.add_comm]; exact Nat.lt_add_of_pos_right h

/- sub properties -/

attribute [simp] Nat.zero_sub

lemma sub_lt_succ (a b : ℕ) : a - b < succ a :=
lt_succ_of_le (sub_le a b)

protected lemma sub_le_sub_right {n m : ℕ} (h : n ≤ m) : ∀ k, n - k ≤ m - k
| 0   => h
| z+1 => pred_le_pred (Nat.sub_le_sub_right h z)

-- port note: bit0/bit1 items have been omitted.

protected lemma add_self_ne_one : ∀ (n : ℕ), n + n ≠ 1
| n+1, h =>
  have h1 : succ (succ (n + n)) = 1 := succ_add n n ▸ h
  Nat.noConfusion h1 fun.

/- subtraction -/

protected lemma le_of_le_of_sub_le_sub_right {n m k : ℕ} (h₀ : k ≤ m) (h₁ : n - k ≤ m - k) : n ≤ m := by
  revert k m
  induction n with intros m k h₀ h₁
  | zero => exact m.zero_le
  | succ pn hpn => cases k with
       | zero => apply h₁
       | succ k => cases m with
          | zero => cases not_succ_le_zero k h₀
          | succ m => simp [succ_sub_succ] at h₁
                      apply succ_le_succ
                      apply hpn _ h₁
                      apply le_of_succ_le_succ h₀

protected lemma sub_le_sub_right_iff {n m k : ℕ} (h : k ≤ m) : n - k ≤ m - k ↔ n ≤ m :=
⟨Nat.le_of_le_of_sub_le_sub_right h, fun h => Nat.sub_le_sub_right h k⟩

protected theorem add_le_to_le_sub (x : ℕ) {y k : ℕ}
  (h : k ≤ y)
: x + k ≤ y ↔ x ≤ y - k :=
by rw [← Nat.add_sub_cancel x k, Nat.sub_le_sub_right_iff h, Nat.add_sub_cancel]

protected lemma sub_lt_of_pos_le (a b : ℕ) (h₀ : 0 < a) (h₁ : a ≤ b)
: b - a < b :=
by apply Nat.sub_lt _ h₀
   apply lt_of_lt_of_le h₀ h₁

protected theorem sub_one (n : ℕ) : n - 1 = pred n :=
rfl

theorem succ_sub_one (n : ℕ) : succ n - 1 = n :=
rfl

theorem succ_pred_eq_of_pos : ∀ {n : ℕ}, 0 < n → succ (pred n) = n
| succ k, h => rfl

protected theorem le_of_sub_eq_zero : ∀{n m : ℕ}, n - m = 0 → n ≤ m
| n, 0, H => by rw [Nat.sub_zero] at H; simp [H]
| 0, m+1, H => Nat.zero_le (m + 1)
| n+1, m+1, H => Nat.add_le_add_right
  (Nat.le_of_sub_eq_zero (by simp [Nat.add_sub_add_right] at H; exact H)) _

protected theorem eq_zero_of_nonpos : ∀ (n : Nat), ¬0 < n -> n = 0
| 0 => fun _ => rfl
| n+1 => fun h => absurd (Nat.zero_lt_succ n) h

protected lemma sub_eq_zero_iff_le : n - m = 0 ↔ n ≤ m :=
⟨Nat.le_of_sub_eq_zero, Nat.sub_eq_zero_of_le⟩

protected lemma sub_eq_iff_eq_add {a b c : ℕ} (ab : b ≤ a) : a - b = c ↔ a = c + b :=
⟨fun c_eq => by rw [c_eq.symm, Nat.sub_add_cancel ab],
 fun a_eq => by rw [a_eq, Nat.add_sub_cancel]⟩

protected lemma lt_of_sub_eq_succ (H : m - n = succ l) : n < m :=
not_le.1 fun H' => by simp [Nat.sub_eq_zero_of_le H'] at H

@[simp] protected lemma min_eq_min (a : ℕ) : Nat.min a b = min a b := rfl

protected lemma zero_min (a : ℕ) : min 0 a = 0 :=
min_eq_left (zero_le a)

protected lemma min_zero (a : ℕ) : min a 0 = 0 :=
min_eq_right (zero_le a)

-- Distribute succ over min
theorem min_succ_succ (x y : ℕ) : min (succ x) (succ y) = succ (min x y) :=
have f : x ≤ y → min (succ x) (succ y) = succ (min x y) := by
  intro p
  have h1 : min (succ x) (succ y) = succ x := if_pos (succ_le_succ p)
  have h2 : succ x = succ (min x y) := congr_arg succ (Eq.symm (if_pos p))
  rwa [←h2]
have g : ¬ (x ≤ y) → min (succ x) (succ y) = succ (min x y) := by
  intro p
  have h1 : min (succ x) (succ y) = succ y :=
    if_neg (λeq => let hp : pred (succ x) ≤ pred (succ y) := (pred_le_pred eq)
                   let hp2 : x ≤ y := hp
                   p hp)
  have h2 : succ y = succ (min x y) := congr_arg succ (Eq.symm (if_neg p))
  rwa [←h2]
Decidable.by_cases f g

theorem sub_eq_sub_min (n m : ℕ) : n - m = n - min n m :=
if h : n ≥ m then by rw [min_eq_right h]
else by rw [Nat.sub_eq_zero_of_le (le_of_not_ge h), min_eq_left (le_of_not_ge h), Nat.sub_self]

@[simp] protected theorem sub_add_min_cancel (n m : ℕ) : n - m + min n m = n :=
by rw [sub_eq_sub_min, Nat.sub_add_cancel (min_le_left n m)]

/- TODO(Leo): sub + inequalities -/

protected def strong_rec_on {p : ℕ → Sort u}
  (n : ℕ) (H : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
Nat.lt_wfRel.wf.fix' H n

protected lemma strong_induction_on {p : Nat → Prop} (n : Nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
Nat.strong_rec_on n h

protected lemma case_strong_induction_on {p : Nat → Prop} (a : Nat)
  (hz : p 0)
  (hi : ∀ n, (∀ m, m ≤ n → p m) → p (succ n)) : p a :=
Nat.strong_induction_on a $ λ n =>
  match n with
  | 0     => λ _ => hz
  | (n+1) => λ h₁ => hi n (λ m h₂ => h₁ _ (lt_succ_of_le h₂))

/- mod -/

-- TODO mod_core_congr, mod_def

lemma mod_two_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 :=
match n % 2, @Nat.mod_lt n 2 (by simp) with
| 0,   _ => Or.inl rfl
| 1,   _ => Or.inr rfl
| k+2, h => absurd h (λ h => not_lt_zero k (lt_of_succ_lt_succ (lt_of_succ_lt_succ h)))

/- div & mod -/

-- TODO div_core_congr, div_def

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
    exact not_le.1 fun h' => h ⟨k0, h'⟩
  | ind y k h IH =>
    rw [← add_one, Nat.add_le_add_iff_le_right, IH k0, succ_mul,
        ← Nat.add_sub_cancel (x*k) k, Nat.sub_le_sub_right_iff h.2, Nat.add_sub_cancel]

protected lemma div_le_of_le_mul {m n : ℕ} : ∀ {k}, m ≤ k * n → m / k ≤ n
| 0,      h => by simp [Nat.div_zero, n.zero_le]
| succ k, h =>
  suffices succ k * (m / succ k) ≤ succ k * n from Nat.le_of_mul_le_mul_left this (zero_lt_succ _)
  by have h1 : succ k * (m / succ k) ≤ m % succ k + succ k * (m / succ k) := Nat.le_add_left _ _
     have h2 : m % succ k + succ k * (m / succ k) = m := by rw [mod_add_div]
     have h3 : m ≤ succ k * n := h
     rw [←h2] at h3
     exact le_trans h1 h3

protected lemma div_le_self : ∀ (m n : ℕ), m / n ≤ m
| m, 0   => by simp [Nat.div_zero]
| m, n+1 => Nat.div_le_of_le_mul $ by
  have := Nat.mul_le_mul_right m (succ_pos n)
  rwa [Nat.one_mul] at this

lemma div_eq_sub_div (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; constructor <;> assumption

lemma div_eq_of_lt (h₀ : a < b) : a / b = 0 := by
  rw [div_eq a, if_neg]
  intro h₁
  apply Nat.not_le_of_gt h₀ h₁.right

lemma div_lt_iff_lt_mul (Hk : 0 < k) : x / k < y ↔ x < y * k := by
  rw [← not_le, ← not_le]; apply not_congr; apply le_div_iff_mul_le Hk

def iterate {α : Sort u} (op : α → α) : ℕ → α → α
 | 0,      a => a
 | succ k, a => iterate op k (op a)

notation f "^["n"]" => iterate f n

/- successor and predecessor -/

theorem add_one_ne_zero (n : ℕ) : n + 1 ≠ 0 := succ_ne_zero _

lemma eq_zero_or_eq_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
by cases n <;> simp

theorem exists_eq_succ_of_ne_zero {n : ℕ} (H : n ≠ 0) : ∃k : ℕ, n = succ k :=
⟨_, (eq_zero_or_eq_succ_pred _).resolve_left H⟩


def discriminate (H1: n = 0 → α) (H2 : ∀m, n = succ m → α) : α :=
  match n with
  | 0 => H1 rfl
  | succ m => H2 m rfl

lemma one_eq_succ_zero : 1 = succ 0 := rfl

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

theorem succ_add_eq_succ_add (n m : ℕ) : succ n + m = n + succ m :=
by simp [succ_add, add_succ]

theorem one_add (n : ℕ) : 1 + n = succ n := by simp [Nat.add_comm]

lemma eq_zero_of_add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
⟨Nat.eq_zero_of_add_eq_zero_right H, Nat.eq_zero_of_add_eq_zero_left H⟩

lemma eq_zero_of_mul_eq_zero : ∀ {n m : ℕ}, n * m = 0 → n = 0 ∨ m = 0
| 0,   m, _ => Or.inl rfl
| n+1, m, h => by rw [succ_mul] at h; exact Or.inr (Nat.eq_zero_of_add_eq_zero_left h)

/- properties of inequality -/

lemma le_succ_of_pred_le {n m : ℕ} : pred n ≤ m → n ≤ succ m :=
match n with | 0 => fun _ => zero_le _ | a+1 => succ_le_succ

lemma le_lt_antisymm {n m : ℕ} (h₁ : n ≤ m) (h₂ : m < n) : False :=
Nat.lt_irrefl n (Nat.lt_of_le_of_lt h₁ h₂)

lemma lt_le_antisymm {n m : ℕ} (h₁ : n < m) (h₂ : m ≤ n) : False :=
le_lt_antisymm h₂ h₁

protected lemma lt_asymm {n m : ℕ} (h₁ : n < m) : ¬ m < n :=
le_lt_antisymm (Nat.le_of_lt h₁)

protected def lt_ge_by_cases {a b : ℕ} {C : Sort u} (h₁ : a < b → C) (h₂ : b ≤ a → C) : C :=
if h : a < b then h₁ h else h₂ (not_lt.1 h)

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


protected lemma sub_add_eq_max {a b : Nat} : a - b + b = max a b := by
cases (@le_total Nat Nat.instLinearOrderNat a b) with
| inl hl => rw [max_eq_right hl, Nat.sub_eq_zero_iff_le.mpr hl, Nat.zero_add]
| inr hr => rw [max_eq_left hr, Nat.sub_add_cancel hr]

protected lemma sub_le_sub_left (k : ℕ) (h : n ≤ m) : k - m ≤ k - n :=
  match m, le.dest h with
  | _, ⟨a, rfl⟩ => by rw [← Nat.sub_sub]; apply sub_le

theorem succ_sub_sub_succ (n m k : ℕ) : succ n - m - succ k = n - m - k :=
by rw [Nat.sub_sub, Nat.sub_sub, add_succ, succ_sub_succ]

protected lemma sub.right_comm (m n k : ℕ) : m - n - k = m - k - n :=
by rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]

protected lemma mul_self_sub_mul_self_eq (a b : Nat) : a * a - b * b = (a + b) * (a - b) :=
by rw [Nat.mul_sub_left_distrib, Nat.right_distrib, Nat.right_distrib, Nat.mul_comm b a, Nat.add_comm (a*a) (a*b),
       Nat.add_sub_add_left]

lemma succ_mul_succ_eq (a b : Nat) : succ a * succ b = a*b + a + b + 1 := by
  rw [mul_succ, succ_mul, Nat.add_right_comm _ a]; rfl

theorem succ_sub {m n : ℕ} (h : n ≤ m) : succ m - n = succ (m - n) :=
Exists.elim (Nat.le.dest h)
  (λ k => λ hk : n + k = m =>
    by rw [← hk, Nat.add_sub_cancel_left, ← add_succ, Nat.add_sub_cancel_left])

protected lemma sub_pos_of_lt (h : m < n) : 0 < n - m := by
  apply Nat.lt_of_add_lt_add_right (b := m)
  rw [Nat.zero_add, Nat.sub_add_cancel (Nat.le_of_lt h)]; exact h

protected lemma sub_sub_self {n m : ℕ} (h : m ≤ n) : n - (n - m) = m :=
(Nat.sub_eq_iff_eq_add (Nat.sub_le _ _)).2 (Nat.add_sub_of_le h).symm

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
        (lt_or_eq_of_le h).elim (al n) fun e => by rw [e]; exact pm
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
not_lt.1 fun l => Nat.find_min p H l h

end find

/- mod -/

lemma le_of_mod_lt {a b : Nat} (h : a % b < a) : b <= a :=
  Decidable.byContradiction $ fun hf =>
  have h0 : a % b = a := Nat.mod_eq_of_lt ((Nat.lt_or_ge a b).resolve_right hf)
  have h1 : a % b ≠ a := ne_of_lt h
  False.elim (h1 h0)

@[simp] theorem add_mod_right (x z : ℕ) : (x + z) % z = x % z :=
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

@[simp] theorem mul_mod_left (m n : ℕ) : (m * n) % n = 0 :=
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

-- TODO cont_to_bool_mod_two

lemma sub_mul_mod (x k n : ℕ) (h₁ : n*k ≤ x) : (x - n*k) % n = x % n := by
  induction k with
  | zero => rw [Nat.mul_zero, Nat.sub_zero]
  | succ k IH =>
    have h₂ : n * k ≤ x := by
      rw [mul_succ] at h₁
      apply Nat.le_trans _ h₁
      apply le_add_right _ n
    have h₄ : x - n * k ≥ n := by
      apply Nat.le_of_add_le_add_right (b := n*k)
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
        · apply Nat.mul_le_mul_left; apply le_succ
        · apply h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        apply h₁
      rw [sub_succ, ← IH h₂]
      rw [div_eq_sub_div h₀ h₃]
      simp [add_one, Nat.pred_succ, mul_succ, Nat.sub_sub]

lemma div_mul_le_self : ∀ (m n : ℕ), m / n * n ≤ m
| m, 0   => by simp
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
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
    apply Nat.sub_le_sub_left
    exact (div_lt_iff_lt_mul npos).1 (lt_succ_self _)
  · change succ (pred (n * p - x)) ≤ (succ (pred (p - x / n))) * n
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
      fun h => succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)] -- TODO: why is the function needed?
    · rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
      apply Nat.sub_le_sub_left; apply div_mul_le_self
    · apply (div_lt_iff_lt_mul npos).2; rwa [Nat.mul_comm]

protected lemma div_div_eq_div_mul (m n k : ℕ) : m / n / k = m / (n * k) := by
  cases eq_zero_or_pos k with
  | inl k0 => rw [k0, Nat.mul_zero, Nat.div_zero, Nat.div_zero] | inr kpos => ?_
  cases eq_zero_or_pos n with
  | inl n0 => rw [n0, Nat.zero_mul, Nat.div_zero, Nat.zero_div] | inr npos => ?_
  apply Nat.le_antisymm
  · apply (le_div_iff_mul_le (Nat.mul_pos npos kpos)).2
    rw [Nat.mul_comm n k, ← Nat.mul_assoc]
    apply (le_div_iff_mul_le npos).1
    apply (le_div_iff_mul_le kpos).1
    (apply Nat.le_refl)
  · apply (le_div_iff_mul_le kpos).2
    apply (le_div_iff_mul_le npos).2
    rw [Nat.mul_assoc, Nat.mul_comm n k]
    apply (le_div_iff_mul_le (Nat.mul_pos kpos npos)).1
    apply Nat.le_refl

protected lemma mul_div_mul {m : ℕ} (n k : ℕ) (H : 0 < m) : m * n / (m * k) = n / k :=
by rw [← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ H]

/- dvd -/

protected theorem dvd_mul_right (a b : ℕ) : a ∣ a * b := ⟨b, rfl⟩

protected theorem dvd_trans {a b c : ℕ} (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
match h₁, h₂ with
| ⟨d, (h₃ : b = a * d)⟩, ⟨e, (h₄ : c = b * e)⟩ =>
  ⟨d * e, show c = a * (d * e) by simp[h₃,h₄, Nat.mul_assoc]⟩

protected theorem eq_zero_of_zero_dvd {a : ℕ} (h : 0 ∣ a) : a = 0 :=
Exists.elim h (λ c (H' : a = 0 * c) => Eq.trans H' (Nat.zero_mul c))

protected theorem dvd_add {a b c : ℕ} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Exists.elim h₁ (λ d hd => Exists.elim h₂ (λ e he => ⟨d + e, by simp[Nat.left_distrib, hd, he]⟩))

protected theorem dvd_add_iff_right {k m n : ℕ} (h : k ∣ m) : k ∣ n ↔ k ∣ m + n :=
  ⟨Nat.dvd_add h,
   Exists.elim h $ λd hd =>
     match m, hd with
     | _, rfl => λh₂ => Exists.elim h₂ $ λe he =>
          ⟨e - d, by rw [Nat.mul_sub_left_distrib, ←he, Nat.add_sub_cancel_left]⟩⟩

protected theorem dvd_add_iff_left {k m n : ℕ} (h : k ∣ n) : k ∣ m ↔ k ∣ m + n :=
  by rw [Nat.add_comm]
     exact Nat.dvd_add_iff_right h

theorem dvd_sub {k m n : ℕ} (H : n ≤ m) (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
  (Nat.dvd_add_iff_left h₂).mpr $ by rw [Nat.sub_add_cancel H]
                                        exact h₁

theorem dvd_mod_iff {k m n : ℕ} (h: k ∣ n) : k ∣ m % n ↔ k ∣ m :=
  let t := @Nat.dvd_add_iff_left _ (m % n) _ (Nat.dvd_trans h (Nat.dvd_mul_right n (m / n)))
  by rwa [mod_add_div] at t

theorem le_of_dvd {m n : ℕ} (h : 0 < n) : m ∣ n → m ≤ n :=
 λ⟨k,e⟩ => by
   revert h
   rw [e]
   match k with
   | 0 => intro hn
          simp at hn
   | pk+1 => intro _
             let t := Nat.mul_le_mul_left m (succ_pos pk)
             rwa [Nat.mul_one] at t

theorem dvd_antisymm : ∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
| m,     0, h₁, h₂ => Nat.eq_zero_of_zero_dvd h₂
| 0,     n, h₁, h₂ => (Nat.eq_zero_of_zero_dvd h₁).symm
| m+1, n+1, h₁, h₂ => Nat.le_antisymm (le_of_dvd (succ_pos _) h₁) (le_of_dvd (succ_pos _) h₂)

theorem pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : 0 < n) : 0 < m :=
Nat.pos_of_ne_zero $ λ m0 =>
  by rw [m0] at H1
     rw [Nat.eq_zero_of_zero_dvd H1] at H2
     exact Nat.lt_irrefl _ H2

theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
  Nat.le_antisymm
   (le_of_dvd (of_decide_eq_true (by trivial)) H)
   (pos_of_dvd_of_pos H (of_decide_eq_true (by trivial)))

theorem dvd_of_mod_eq_zero {m n : ℕ} (H : n % m = 0) : m ∣ n :=
Exists.intro
  (n / m)
  (by have t := (mod_add_div n m).symm
      rwa [H, Nat.zero_add] at t)

theorem mod_eq_zero_of_dvd {m n : ℕ} (H : m ∣ n) : n % m = 0 :=
Exists.elim H (λ z H1 => by rw [H1, mul_mod_right])

theorem dvd_iff_mod_eq_zero (m n : ℕ) : m ∣ n ↔ n % m = 0 :=
Iff.intro mod_eq_zero_of_dvd dvd_of_mod_eq_zero

instance decidable_dvd : @DecidableRel ℕ (·∣·) :=
λm n => decidable_of_decidable_of_iff (dvd_iff_mod_eq_zero _ _).symm

protected theorem mul_div_cancel' {m n : ℕ} (H : n ∣ m) : n * (m / n) = m :=
 let t := mod_add_div m n
 by rwa [mod_eq_zero_of_dvd H, Nat.zero_add] at t

protected theorem div_mul_cancel {m n : ℕ} (H: n ∣ m) : m / n * n = m :=
  by rw [Nat.mul_comm, Nat.mul_div_cancel' H]

protected theorem mul_div_assoc (m : ℕ) {n k : ℕ} (H : k ∣ n) : m * n / k = m * (n / k) :=
match Nat.eq_zero_or_pos k with
| Or.inl h0 => by rw [h0, Nat.div_zero, Nat.div_zero, Nat.mul_zero]
| Or.inr hpos => by have h1 : m * n / k = m *(n / k * k) / k := by rw [Nat.div_mul_cancel H]
                    rw [h1, ← Nat.mul_assoc, Nat.mul_div_cancel _ hpos]

protected theorem dvd_of_mul_dvd_mul_left {m n k : ℕ} (kpos : 0 < k) (H : k * m ∣ k * n) : m ∣ n :=
Exists.elim H (λ l H1 => by rw [Nat.mul_assoc] at H1
                            exact ⟨_, Nat.eq_of_mul_eq_mul_left kpos H1⟩)

protected theorem dvd_of_mul_dvd_mul_right {m n k : ℕ} (kpos : 0 < k) (H : m * k ∣ n * k) : m ∣ n :=
by rw [Nat.mul_comm m k, Nat.mul_comm n k] at H; exact Nat.dvd_of_mul_dvd_mul_left kpos H

/- --- -/

protected lemma mul_le_mul_of_nonneg_left {a b c : ℕ} (h₁ : a ≤ b) : c * a ≤ c * b := by
  by_cases hba: b ≤ a; { simp [Nat.le_antisymm hba h₁] }
  by_cases hc0 : c ≤ 0; { simp [Nat.le_antisymm hc0 (zero_le c), Nat.zero_mul] }
  exact Nat.le_of_lt (Nat.mul_lt_mul_of_pos_left (not_le.1 hba) (not_le.1 hc0))

protected lemma mul_le_mul_of_nonneg_right {a b c : ℕ} (h₁ : a ≤ b) : a * c ≤ b * c := by
  by_cases hba : b ≤ a; { simp [Nat.le_antisymm hba h₁] }
  by_cases hc0 : c ≤ 0; { simp [Nat.le_antisymm hc0 (zero_le c), Nat.mul_zero] }
  exact Nat.le_of_lt (Nat.mul_lt_mul_of_pos_right (not_le.1 hba) (not_le.1 hc0))

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

@[simp] theorem mod_mod (a n : ℕ) : (a % n) % n = a % n :=
(eq_zero_or_pos n).elim
  (λ n0 => by simp [n0, mod_zero])
  (λ npos => Nat.mod_eq_of_lt (mod_lt _ npos))


lemma mul_mod (a b n : ℕ) : (a * b) % n = ((a % n) * (b % n)) % n := by
    let hy := (a * b) % n
    have hx : (a * b) % n = hy := rfl
    rw [←mod_add_div a n, ←mod_add_div b n, Nat.right_distrib, Nat.left_distrib, Nat.left_distrib,
        Nat.mul_assoc, Nat.mul_assoc, ←Nat.left_distrib n _ _, add_mul_mod_self_left,
        Nat.mul_comm _ (n * (b / n)), Nat.mul_assoc, add_mul_mod_self_left] at hx
    rw [hx]
    done

@[simp] theorem mod_add_mod (m n k : ℕ) : (m % n + k) % n = (m + k) % n := by
   have := (add_mul_mod_self_left (m % n + k) n (m / n)).symm
   rwa [Nat.add_right_comm, mod_add_div] at this

@[simp] theorem add_mod_mod (m n k : ℕ) : (m + n % k) % k = (m + n) % k :=
by rw [Nat.add_comm, mod_add_mod, Nat.add_comm]

lemma add_mod (a b n : ℕ) : (a + b) % n = ((a % n) + (b % n)) % n :=
by rw [add_mod_mod, mod_add_mod]

lemma to_digits_core_lens_eq_aux (b f : Nat)
  : ∀ (n : Nat) (l1 l2 : List Char) (h0 : l1.length = l2.length), (Nat.toDigitsCore b f n l1).length = (Nat.toDigitsCore b f n l2).length := by
induction f with
  simp only [Nat.toDigitsCore, List.length] <;> intro n l1 l2 hlen
| zero => assumption
| succ f ih =>
  by_cases hx : n / b = 0
  case pos => simp only [hx, if_true, List.length, congrArg (fun l => l + 1) hlen]
  case neg =>
    simp only [hx, if_false]
    specialize ih (n / b) (Nat.digitChar (n % b) :: l1) (Nat.digitChar (n % b) :: l2)
    simp only [List.length, congrArg (fun l => l + 1) hlen] at ih
    exact ih trivial

lemma to_digits_core_lens_eq (b f : Nat) : ∀ (n : Nat) (c : Char) (tl : List Char), (Nat.toDigitsCore b f n (c :: tl)).length = (Nat.toDigitsCore b f n tl).length + 1 := by
induction f with
  intro n c tl <;> simp only [Nat.toDigitsCore, List.length]
| succ f ih =>
  by_cases hnb : (n / b) = 0
  case pos => simp only [hnb, if_true, List.length]
  case neg =>
    generalize hx: Nat.digitChar (n % b) = x
    simp only [hx, hnb, if_false] at ih
    simp only [hnb, if_false]
    specialize ih (n / b) c (x :: tl)
    rw [<- ih]
    have lens_eq : (x :: (c :: tl)).length = (c :: x :: tl).length := by simp
    apply to_digits_core_lens_eq_aux
    exact lens_eq

lemma nat_repr_len_aux (n b e : Nat) (h_b_pos : 0 < b) :  n < b ^ e.succ -> n / b < b ^ e := by
simp only [Nat.pow_succ]
exact (@Nat.div_lt_iff_lt_mul b n (b ^ e) h_b_pos).mpr

/-- The String representation produced by toDigitsCore has the proper length relative to
the number of digits in `n < e` for some base `b`. Since this works with any base greater
than one, it can be used for binary, decimal, and hex. -/
lemma to_digits_core_length (b : Nat) (h : 2 <= b) (f n e : Nat) (hlt : n < b ^ e) (h_e_pos: 0 < e) : (Nat.toDigitsCore b f n []).length <= e := by
induction f generalizing n e hlt h_e_pos with
  simp only [Nat.toDigitsCore, List.length, Nat.zero_le]
| succ f ih =>
  cases e with
  | zero => exact False.elim (Nat.lt_irrefl 0 h_e_pos)
  | succ e =>
    by_cases h_pred_pos : 0 < e
    case pos =>
      have _ : 0 < b := Nat.lt_trans (by decide) h
      specialize ih (n / b) e (nat_repr_len_aux n b e ‹0 < b› hlt) h_pred_pos
      by_cases hdiv_ten : n / b = 0
      case pos => simp only [hdiv_ten]; exact Nat.le.step h_pred_pos
      case neg =>
        simp only [hdiv_ten, to_digits_core_lens_eq b f (n / b) (Nat.digitChar $ n % b), if_false]
        exact Nat.succ_le_succ ih
    case neg =>
      have _ : e = 0 := Nat.eq_zero_of_nonpos e h_pred_pos
      rw [‹e = 0›]
      have _ : b ^ 1 = b := by simp only [pow_succ, pow_zero, Nat.one_mul]
      have _ : n < b := ‹b ^ 1 = b› ▸ (‹e = 0› ▸ hlt : n < b ^ Nat.succ 0)
      simp only [(@Nat.div_eq_of_lt n b ‹n < b› : n / b = 0), if_true, List.length]

/-- The core implementation of `Nat.repr` returns a String with length less than or equal to the
number of digits in the decimal number (represented by `e`). For example, the decimal string
representation of any number less than 1000 (10 ^ 3) has a length less than or equal to 3. -/
lemma repr_length (n e : Nat) : 0 < e -> n < 10 ^ e -> (Nat.repr n).length <= e := by
cases n with
  intro _ _ <;> simp only [Nat.repr, Nat.toDigits, String.length, List.asString]
| zero => assumption
| succ n =>
  by_cases hterm : n.succ / 10 = 0
  case pos => simp only [hterm, Nat.toDigitsCore]; assumption
  case neg =>
    simp only [hterm]
    exact to_digits_core_length 10 (by decide) (Nat.succ n + 1) (Nat.succ n) e ‹n.succ < 10 ^ e› ‹0 < e›

lemma Nat.pow_succ' {m n : Nat} : m ^ n.succ = m * m ^ n := by
  rw [Nat.pow_succ, Nat.mul_comm]

@[simp] lemma Nat.pow_eq {m n : Nat} : m.pow n = m ^ n := rfl

end Nat
