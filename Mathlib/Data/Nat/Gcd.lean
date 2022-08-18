/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Dvd

/-!
# Definitions and properties of `gcd`, `lcm`, and `coprime`

-/

namespace Nat

--- TODO all of these dvd preliminaries belong elsewhere.

protected theorem dvd_mul_left (a b : ℕ) : a ∣ b * a := Exists.intro b (Nat.mul_comm b a)
protected theorem dvd_refl (a : ℕ) : a ∣ a := Exists.intro 1 (by simp)
protected theorem dvd_zero (a : ℕ) : a ∣ 0 := Exists.intro 0 (by simp)

protected theorem mul_dvd_mul : ∀ {a b c d : ℕ}, a ∣ b → c ∣ d → a * c ∣ b * d
| a, b, c, d, ⟨e, he⟩, ⟨f, hf⟩ => ⟨e * f, by rw [he, hf,
                                                 Nat.mul_assoc a _,
                                                 ←Nat.mul_assoc e _,
                                                 Nat.mul_comm e c,
                                                 Nat.mul_assoc a c _,
                                                 Nat.mul_assoc c e _,]⟩

protected theorem mul_dvd_mul_left (a : ℕ) {b c : ℕ} (h : b ∣ c) : a * b ∣ a * c :=
Nat.mul_dvd_mul (Nat.dvd_refl a) h

protected theorem mul_dvd_mul_right {a b : ℕ} (h: a ∣ b) (c : ℕ) : a * c ∣ b * c :=
Nat.mul_dvd_mul h (Nat.dvd_refl c)

----
-- Here's where we get into the main gcd results

theorem gcd_rec (m n : ℕ) : gcd m n = gcd (n % m) m :=
  match m with
  | 0 => by have := (mod_zero n).symm
            rwa [gcd_zero_right]
  | pm + 1 => by simp [gcd_succ]

@[elabAsElim]
theorem gcd.induction
  {P : ℕ → ℕ → Prop}
  (m n : ℕ)
  (H0 : ∀n, P 0 n)
  (H1 : ∀ m n, 0 < m → P (n % m) m → P m n) :
  P m n :=
  @WellFounded.induction _ _ lt_wfRel.wf (λ m => ∀ n, P m n) m
    (fun
    | 0, _ => H0
    | _+1, IH => λ _ => H1 _ _ (succ_pos _) (IH _ (mod_lt _ (succ_pos _)) _) )
    n

def lcm (m n : ℕ) : ℕ := m * n / gcd m n

@[reducible] def coprime (m n : ℕ) : Prop := gcd m n = 1

---

theorem gcd_dvd (m n : ℕ) : (gcd m n ∣ m) ∧ (gcd m n ∣ n) :=
gcd.induction m n
  (λ n => by rw [gcd_zero_left]; exact ⟨Nat.dvd_zero n, Nat.dvd_refl n⟩)
  (λ m n _ => by rw [←gcd_rec]; exact λ ⟨IH₁, IH₂⟩ => ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩)

theorem gcd_dvd_left (m n : ℕ) : gcd m n ∣ m := (gcd_dvd m n).left

theorem gcd_dvd_right (m n : ℕ) : gcd m n ∣ n := (gcd_dvd m n).right

theorem gcd_le_left {m} (n) (h : 0 < m) : gcd m n ≤ m := le_of_dvd h $ gcd_dvd_left m n

theorem gcd_le_right {m} (n) (h : 0 < n) : gcd m n ≤ n := le_of_dvd h $ gcd_dvd_right m n

theorem dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n :=
gcd.induction m n
  (λ n _ kn => by rw [gcd_zero_left]; exact kn)
  (λ n m _ IH H1 H2 => by rw [gcd_rec]; exact IH ((dvd_mod_iff H1).2 H2) H1)

theorem dvd_gcd_iff {m n k : ℕ} : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n :=
Iff.intro (λ h => And.intro (Nat.dvd_trans h (gcd_dvd m n).left) (Nat.dvd_trans h (gcd_dvd m n).right))
          (λ h => dvd_gcd h.left h.right)

theorem gcd_comm (m n : ℕ) : gcd m n = gcd n m :=
  dvd_antisymm
    (dvd_gcd (gcd_dvd_right m n) (gcd_dvd_left m n))
    (dvd_gcd (gcd_dvd_right n m) (gcd_dvd_left n m))

theorem gcd_eq_left_iff_dvd {m n :ℕ} : m ∣ n ↔ gcd m n = m :=
Iff.intro
  (λ h => by rw [gcd_rec, mod_eq_zero_of_dvd h, gcd_zero_left])
  (λ h => h ▸ gcd_dvd_right m n)

theorem gcd_eq_right_iff_dvd {m n : ℕ} : m ∣ n ↔ gcd n m = m :=
by rw [gcd_comm]
   apply gcd_eq_left_iff_dvd

theorem gcd_assoc (m n k : ℕ) : gcd (gcd m n) k = gcd m (gcd n k) :=
dvd_antisymm
  (dvd_gcd
    (Nat.dvd_trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_left m n))
    (dvd_gcd (Nat.dvd_trans (gcd_dvd_left (gcd m n) k) (gcd_dvd_right m n))
      (gcd_dvd_right (gcd m n) k)))
  (dvd_gcd
    (dvd_gcd (gcd_dvd_left m (gcd n k)) (Nat.dvd_trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_left n k)))
    (Nat.dvd_trans (gcd_dvd_right m (gcd n k)) (gcd_dvd_right n k)))

@[simp] theorem gcd_one_right (n : ℕ) : gcd n 1 = 1 :=
Eq.trans (gcd_comm n 1) $ gcd_one_left n

theorem gcd_mul_left (m n k : ℕ) : gcd (m * n) (m * k) = m * gcd n k := by
  induction n, k using gcd.induction with
  | H0 k => simp
  | H1 n k _ IH => rwa [←mul_mod_mul_left, ←gcd_rec, ←gcd_rec] at IH

theorem gcd_mul_right (m n k : ℕ) : gcd (m * n) (k * n) = gcd m k * n :=
by rw [Nat.mul_comm m n, Nat.mul_comm k n, Nat.mul_comm (gcd m k) n, gcd_mul_left]

theorem gcd_pos_of_pos_left {m : ℕ} (n : ℕ) (mpos : 0 < m) : 0 < gcd m n :=
pos_of_dvd_of_pos (gcd_dvd_left m n) mpos

theorem gcd_pos_of_pos_right (m : ℕ) {n : ℕ} (npos : 0 < n) : 0 < gcd m n :=
pos_of_dvd_of_pos (gcd_dvd_right m n) npos

theorem eq_zero_of_gcd_eq_zero_left {m n : ℕ} (H : gcd m n = 0) : m = 0 :=
match eq_zero_or_pos m with
| Or.inl H0 => H0
| Or.inr H1 => absurd (Eq.symm H) (ne_of_lt (gcd_pos_of_pos_left _ H1))

theorem eq_zero_of_gcd_eq_zero_right {m n : ℕ} (H : gcd m n = 0) : n = 0 :=
by rw [gcd_comm] at H
   exact eq_zero_of_gcd_eq_zero_left H

theorem gcd_div {m n k : ℕ} (H1 : k ∣ m) (H2 : k ∣ n) :
  gcd (m / k) (n / k) = gcd m n / k :=
match eq_zero_or_pos k with
| Or.inl H0 => by rw [H0, Nat.div_zero, Nat.div_zero, Nat.div_zero, gcd_zero_right]
| Or.inr H3 =>
  Nat.eq_of_mul_eq_mul_right H3 $ by rw [Nat.div_mul_cancel (dvd_gcd H1 H2), ←gcd_mul_right,
                                         Nat.div_mul_cancel H1, Nat.div_mul_cancel H2]

theorem gcd_dvd_gcd_of_dvd_left {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd m n ∣ gcd k n :=
dvd_gcd (Nat.dvd_trans (gcd_dvd_left m n) H) (gcd_dvd_right m n)

theorem gcd_dvd_gcd_of_dvd_right {m k : ℕ} (n : ℕ) (H : m ∣ k) : gcd n m ∣ gcd n k :=
dvd_gcd (gcd_dvd_left n m) (Nat.dvd_trans (gcd_dvd_right n m) H)

theorem gcd_dvd_gcd_mul_left (m n k : ℕ) : gcd m n ∣ gcd (k * m) n :=
gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right (m n k : ℕ) : gcd m n ∣ gcd (m * k) n :=
gcd_dvd_gcd_of_dvd_left _ (Nat.dvd_mul_right _ _)

theorem gcd_dvd_gcd_mul_left_right (m n k : ℕ) : gcd m n ∣ gcd m (k * n) :=
gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right (m n k : ℕ) : gcd m n ∣ gcd m (n * k) :=
gcd_dvd_gcd_of_dvd_right _ (Nat.dvd_mul_right _ _)

theorem gcd_eq_left {m n : ℕ} (H : m ∣ n) : gcd m n = m :=
dvd_antisymm (gcd_dvd_left _ _) (dvd_gcd (Nat.dvd_refl _) H)

theorem gcd_eq_right {m n : ℕ} (H : n ∣ m) : gcd m n = n :=
by rw [gcd_comm, gcd_eq_left H]

@[simp] lemma gcd_mul_left_left (m n : ℕ) : gcd (m * n) n = n :=
dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (Nat.dvd_mul_left _ _) (Nat.dvd_refl _))

@[simp] lemma gcd_mul_left_right (m n : ℕ) : gcd n (m * n) = n :=
by rw [gcd_comm, gcd_mul_left_left]

@[simp] lemma gcd_mul_right_left (m n : ℕ) : gcd (n * m) n = n :=
by rw [Nat.mul_comm, gcd_mul_left_left]

@[simp] lemma gcd_mul_right_right (m n : ℕ) : gcd n (n * m) = n :=
by rw [gcd_comm, gcd_mul_right_left]

@[simp] lemma gcd_gcd_self_right_left (m n : ℕ) : gcd m (gcd m n) = gcd m n :=
dvd_antisymm (gcd_dvd_right _ _) (dvd_gcd (gcd_dvd_left _ _) (Nat.dvd_refl _))

@[simp] lemma gcd_gcd_self_right_right (m n : ℕ) : gcd m (gcd n m) = gcd n m :=
by rw [gcd_comm n m, gcd_gcd_self_right_left]

@[simp] lemma gcd_gcd_self_left_right (m n : ℕ) : gcd (gcd n m) m = gcd n m :=
by rw [gcd_comm, gcd_gcd_self_right_right]

@[simp] lemma gcd_gcd_self_left_left (m n : ℕ) : gcd (gcd m n) m = gcd m n :=
by rw [gcd_comm m n, gcd_gcd_self_left_right]

lemma gcd_add_mul_self (m n k : ℕ) : gcd m (n + k * m) = gcd m n :=
by simp [gcd_rec m (n + k * m), gcd_rec m n]

theorem gcd_eq_zero_iff {i j : ℕ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 :=
Iff.intro
  (λ h => ⟨eq_zero_of_gcd_eq_zero_left h, eq_zero_of_gcd_eq_zero_right h⟩)
  (λ h => by rw [h.1, h.2]
             exact Nat.gcd_zero_right _)

/-! ### `lcm` -/

theorem lcm_comm (m n : ℕ) : lcm m n = lcm n m :=
by have h1 : lcm m n = m * n / gcd m n := rfl
   have h2 : lcm n m = n * m / gcd n m := rfl
   rw [h1, h2, Nat.mul_comm n m, gcd_comm n m]

@[simp]
theorem lcm_zero_left (m : ℕ) : lcm 0 m = 0 :=
by have h : lcm 0 m = 0 * m / gcd 0 m := rfl
   simp [h]

@[simp]
theorem lcm_zero_right (m : ℕ) : lcm m 0 = 0 := lcm_comm 0 m ▸ lcm_zero_left m

@[simp]
theorem lcm_one_left (m : ℕ) : lcm 1 m = m :=
by have h : lcm 1 m = 1 * m / gcd 1 m := rfl
   simp [h]

@[simp]
theorem lcm_one_right (m : ℕ) : lcm m 1 = m := lcm_comm 1 m ▸ lcm_one_left m

@[simp]
theorem lcm_self (m : ℕ) : lcm m m = m :=
match eq_zero_or_pos m with
| Or.inl h => by rw [h, lcm_zero_left]
| Or.inr h => by have h1 : lcm m m = m * m / gcd m m := rfl
                 simp [h1, Nat.mul_div_cancel _ h]

theorem dvd_lcm_left (m n : ℕ) : m ∣ lcm m n :=
Exists.intro (n / gcd m n)
             (by rw [← Nat.mul_div_assoc m (Nat.gcd_dvd_right m n)]
                 rfl)

theorem dvd_lcm_right (m n : ℕ) : n ∣ lcm m n :=
lcm_comm n m ▸ dvd_lcm_left n m

theorem gcd_mul_lcm (m n : ℕ) : gcd m n * lcm m n = m * n :=
by have h1 : lcm m n = m * n / gcd m n := rfl
   rw [h1]
   rw [Nat.mul_div_cancel' (Nat.dvd_trans (gcd_dvd_left m n) (Nat.dvd_mul_right m n))]

theorem lcm_dvd {m n k : ℕ} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k :=
match eq_zero_or_pos k with
| Or.inl h => by rw [h]
                 exact Nat.dvd_zero _
| Or.inr kpos => Nat.dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos)) $
                   by rw [gcd_mul_lcm, ←gcd_mul_right, Nat.mul_comm n k];
                      exact dvd_gcd (Nat.mul_dvd_mul_left _ H2) (Nat.mul_dvd_mul_right H1 _)

theorem lcm_assoc (m n k : ℕ) : lcm (lcm m n) k = lcm m (lcm n k) :=
dvd_antisymm
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left m (lcm n k)) (Nat.dvd_trans (dvd_lcm_left n k) (dvd_lcm_right m (lcm n k))))
    (Nat.dvd_trans (dvd_lcm_right n k) (dvd_lcm_right m (lcm n k))))
  (lcm_dvd
    (Nat.dvd_trans (dvd_lcm_left m n) (dvd_lcm_left (lcm m n) k))
    (lcm_dvd (Nat.dvd_trans (dvd_lcm_right m n) (dvd_lcm_left (lcm m n) k))
      (dvd_lcm_right (lcm m n) k)))

theorem lcm_ne_zero {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 :=
by intro h
   have h1 := gcd_mul_lcm m n
   rw [h, Nat.mul_zero] at h1
   match eq_zero_of_mul_eq_zero h1.symm with
   | Or.inl hm1 => exact hm hm1
   | Or.inr hn1 => exact hn hn1

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.coprime m n`.
-/

instance (m n : ℕ) : Decidable (coprime m n) :=
  if h: gcd m n = 1 then isTrue h else isFalse h

theorem coprime_iff_gcd_eq_one {m n : ℕ} : coprime m n ↔ gcd m n = 1 := Iff.rfl

theorem coprime.gcd_eq_one {m n : ℕ} : coprime m n → gcd m n = 1 := id

theorem coprime.symm {m n : ℕ} : coprime n m → coprime m n := (gcd_comm m n).trans

theorem coprime_comm {m n : ℕ} : coprime n m ↔ coprime m n := ⟨coprime.symm, coprime.symm⟩

theorem coprime.dvd_of_dvd_mul_right {m n k : ℕ} (H1 : coprime k n) (H2 : k ∣ m * n) : k ∣ m :=
let t := dvd_gcd (Nat.dvd_mul_left k m) H2
by rwa [gcd_mul_left, H1.gcd_eq_one, Nat.mul_one] at t

theorem coprime.dvd_of_dvd_mul_left {m n k : ℕ} (H1 : coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
by rw [Nat.mul_comm] at H2
   exact H1.dvd_of_dvd_mul_right H2

theorem coprime.gcd_mul_left_cancel {k : ℕ} (m : ℕ) {n : ℕ} (H : coprime k n) :
   gcd (k * m) n = gcd m n :=
let H1 : coprime (gcd (k * m) n) k :=
   by have h1 : coprime (gcd (k * m) n) k = (gcd (gcd (k * m) n) k = 1) := rfl
      rw [h1, Nat.gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
dvd_antisymm
  (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
  (gcd_dvd_gcd_mul_left _ _ _)

theorem coprime.gcd_mul_right_cancel (m : ℕ) {k n : ℕ} (H : coprime k n) :
   gcd (m * k) n = gcd m n :=
by rw [Nat.mul_comm m k, H.gcd_mul_left_cancel m]

theorem coprime.gcd_mul_left_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (k * n) = gcd m n :=
by rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem coprime.gcd_mul_right_cancel_right {k m : ℕ} (n : ℕ) (H : coprime k m) :
   gcd m (n * k) = gcd m n :=
by rw [Nat.mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd {m n : ℕ} (H : 0 < gcd m n) :
  coprime (m / gcd m n) (n / gcd m n) :=
by rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_self H]

theorem not_coprime_of_dvd_of_dvd {m n d : ℕ} (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) :
  ¬ coprime m n :=
λ co => by have hd : ¬ d ≤ 1 := Nat.not_le_of_gt dgt1
           have := (Nat.le_of_dvd Nat.zero_lt_one $ by rw [←co.gcd_eq_one]; exact dvd_gcd Hm Hn)
           exact hd this

theorem exists_coprime {m n : ℕ} (H : 0 < gcd m n) :
  ∃ m' n', coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
⟨_, _, coprime_div_gcd_div_gcd H,
  (Nat.div_mul_cancel (gcd_dvd_left m n)).symm,
  (Nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' {m n : ℕ} (H : 0 < gcd m n) :
  ∃ g m' n', 0 < g ∧ coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprime H
  ⟨_, m', n', H, h⟩

theorem coprime.mul {m n k : ℕ} (H1 : coprime m k) (H2 : coprime n k) : coprime (m * n) k :=
(H1.gcd_mul_left_cancel n).trans H2

theorem coprime.mul_right {k m n : ℕ} (H1 : coprime k m) (H2 : coprime k n) : coprime k (m * n) :=
(H1.symm.mul H2.symm).symm

theorem coprime.coprime_dvd_left {m k n : ℕ} (H1 : m ∣ k) (H2 : coprime k n) : coprime m n :=
by apply eq_one_of_dvd_one
   have h1 : coprime k n = (gcd k n = 1) := rfl
   rw [h1] at H2
   have := @Nat.gcd_dvd_gcd_of_dvd_left m k n H1
   rwa [←H2]

theorem coprime.coprime_dvd_right {m k n : ℕ} (H1 : n ∣ m) (H2 : coprime k m) : coprime k n :=
(H2.symm.coprime_dvd_left H1).symm

theorem coprime.coprime_mul_left {k m n : ℕ} (H : coprime (k * m) n) : coprime m n :=
H.coprime_dvd_left (Nat.dvd_mul_left _ _)

theorem coprime.coprime_mul_right {k m n : ℕ} (H : coprime (m * k) n) : coprime m n :=
H.coprime_dvd_left (Nat.dvd_mul_right _ _)

theorem coprime.coprime_mul_left_right {k m n : ℕ} (H : coprime m (k * n)) : coprime m n :=
H.coprime_dvd_right (Nat.dvd_mul_left _ _)

theorem coprime.coprime_mul_right_right {k m n : ℕ} (H : coprime m (n * k)) : coprime m n :=
H.coprime_dvd_right (Nat.dvd_mul_right _ _)

theorem coprime.coprime_div_left {m n a : ℕ} (cmn : coprime m n) (dvd : a ∣ m) :
  coprime (m / a) n :=
match eq_zero_or_pos a with
| Or.inl h0 => by rw [h0] at dvd
                  rw [Nat.eq_zero_of_zero_dvd dvd]
                  rw [Nat.eq_zero_of_zero_dvd dvd] at cmn
                  simp
                  assumption
| Or.inr hpos =>
   match dvd with
   | ⟨k, hk⟩ => by rw [hk, Nat.mul_div_cancel_left _ hpos]
                   rw [hk] at cmn
                   exact coprime.coprime_mul_left cmn

theorem coprime.coprime_div_right {m n a : ℕ} (cmn : coprime m n) (dvd : a ∣ n) :
  coprime m (n / a) :=
(coprime.coprime_div_left cmn.symm dvd).symm

lemma coprime_mul_iff_left {k m n : ℕ} : coprime (m * n) k ↔ coprime m k ∧ coprime n k :=
⟨λ h => ⟨coprime.coprime_mul_right h, coprime.coprime_mul_left h⟩,
  λ ⟨h, _⟩ => by rwa [coprime_iff_gcd_eq_one, coprime.gcd_mul_left_cancel n h]⟩

lemma coprime_mul_iff_right {k m n : ℕ} : coprime k (m * n) ↔ coprime k m ∧ coprime k n :=
by rw [@coprime_comm (m*n) k, @coprime_comm m k, @coprime_comm n k, coprime_mul_iff_left]

lemma coprime.gcd_left (k : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime (gcd k m) n :=
hmn.coprime_dvd_left $ gcd_dvd_right k m

lemma coprime.gcd_right (k : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime m (gcd k n) :=
hmn.coprime_dvd_right $ gcd_dvd_right k n

lemma coprime.gcd_both (k l : ℕ) {m n : ℕ} (hmn : coprime m n) : coprime (gcd k m) (gcd l n) :=
(hmn.gcd_left k).gcd_right l

lemma coprime.mul_dvd_of_dvd_of_dvd {a n m : ℕ} (hmn : coprime m n)
  (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨_, hk⟩ := hm
  hk.symm ▸ Nat.mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

theorem coprime_one_left : ∀ n, coprime 1 n := gcd_one_left

theorem coprime_one_right : ∀ n, coprime n 1 := gcd_one_right

theorem coprime.pow_left {m k : ℕ} (n : ℕ) (H1 : coprime m k) : coprime (m ^ n) k :=
by induction n with
   | zero => exact coprime_one_left _
   | succ n ih => have hm := H1.mul ih
                  have : m ^ succ n = m * m ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
                  rwa [this]

theorem coprime.pow_right {m k : ℕ} (n : ℕ) (H1 : coprime k m) : coprime k (m ^ n) :=
(H1.symm.pow_left n).symm

theorem coprime.pow {k l : ℕ} (m n : ℕ) (H1 : coprime k l) : coprime (k ^ m) (l ^ n) :=
(H1.pow_left _).pow_right _

theorem coprime.eq_one_of_dvd {k m : ℕ} (H : coprime k m) (d : k ∣ m) : k = 1 :=
by rw [← H.gcd_eq_one, gcd_eq_left d]

@[simp] theorem coprime_zero_left (n : ℕ) : coprime 0 n ↔ n = 1 :=
by simp [coprime]

@[simp] theorem coprime_zero_right (n : ℕ) : coprime n 0 ↔ n = 1 :=
by simp [coprime]

@[simp] theorem coprime_one_left_iff (n : ℕ) : coprime 1 n ↔ true :=
by simp [coprime]

@[simp] theorem coprime_one_right_iff (n : ℕ) : coprime n 1 ↔ true :=
by simp [coprime]

@[simp] theorem coprime_self (n : ℕ) : coprime n n ↔ n = 1 :=
by simp [coprime]

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`. -/
def prod_dvd_and_dvd_of_dvd_prod {m n k : ℕ} (H : k ∣ m * n) :
  { d : {m' // m' ∣ m} × {n' // n' ∣ n} // k = d.1.val * d.2.val } :=
by cases h0 : gcd k m with
   | zero => have : k = 0 := eq_zero_of_gcd_eq_zero_left h0
             subst this
             have : m = 0 := eq_zero_of_gcd_eq_zero_right h0
             subst this
             exact ⟨⟨⟨0, Nat.dvd_refl 0⟩, ⟨n, Nat.dvd_refl n⟩⟩, (Nat.zero_mul n).symm⟩
   | succ p => have hpos : 0 < gcd k m := h0.symm ▸ Nat.zero_lt_succ _;
               clear h0
               have hd : gcd k m * (k / gcd k m) = k := (Nat.mul_div_cancel' (gcd_dvd_left k m))
               have hn : (k / gcd k m) ∣ n := by apply Nat.dvd_of_mul_dvd_mul_left hpos
                                                 rw [hd, ← gcd_mul_right]
                                                 exact Nat.dvd_gcd (Nat.dvd_mul_right _ _) H
               exact ⟨⟨⟨gcd k m,  gcd_dvd_right k m⟩, ⟨k / gcd k m, hn⟩⟩, hd.symm⟩

theorem gcd_mul_dvd_mul_gcd (k m n : ℕ) : gcd k (m * n) ∣ gcd k m * gcd k n :=
match (prod_dvd_and_dvd_of_dvd_prod $ gcd_dvd_right k (m * n)) with
| ⟨⟨⟨m', hm'⟩, ⟨n', hn'⟩⟩, h⟩ =>
  by have h' : gcd k (m * n) = m' * n' := h
     rw [h']
     have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
     exact Nat.mul_dvd_mul
       (by have hm'k : m' ∣ k := Nat.dvd_trans (Nat.dvd_mul_right m' n') hm'n'
           exact dvd_gcd hm'k hm')
       (by have hn'k : n' ∣ k := Nat.dvd_trans (Nat.dvd_mul_left n' m') hm'n'
           exact dvd_gcd hn'k hn')

theorem coprime.gcd_mul (k : ℕ) {m n : ℕ} (h : coprime m n) : gcd k (m * n) = gcd k m * gcd k n :=
dvd_antisymm
  (gcd_mul_dvd_mul_gcd k m n)
  ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd
    (gcd_dvd_gcd_mul_right_right _ _ _)
    (gcd_dvd_gcd_mul_left_right _ _ _))

-- TODO: pow_dvd_pow_iff

lemma gcd_mul_gcd_of_coprime_of_mul_eq_mul {a b c d : ℕ} (cop : c.coprime d) (h : a * b = c * d) :
  a.gcd c * b.gcd c = c :=
dvd_antisymm
  (by apply Nat.coprime.dvd_of_dvd_mul_right (Nat.coprime.mul (cop.gcd_left _) (cop.gcd_left _))
      rw [← h]
      apply Nat.mul_dvd_mul (gcd_dvd _ _).1 (gcd_dvd _ _).1)
  (by rw [gcd_comm a _, gcd_comm b _]
      have h1 : c ∣ gcd c (a * b) :=
        by rw [h, gcd_mul_right_right d c]
           exact Nat.dvd_refl _
      have h2 : gcd c (a * b) ∣ gcd c a * gcd c b :=
        by apply gcd_mul_dvd_mul_gcd
      exact Nat.dvd_trans h1 h2)
