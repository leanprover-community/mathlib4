/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

## Main definitions and results

* `Principal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
  any other typically excluded edge cases for simplicity.
* `not_bddAbove_principal`: Principal ordinals (under any operation) are unbounded.
* `principal_add_iff_zero_or_omega0_opow`: The main characterization theorem for additive principal
  ordinals.
* `principal_mul_iff_le_two_or_omega0_opow_opow`: The main characterization theorem for
  multiplicative principal ordinals.

## TODO

* Prove that exponential principal ordinals are 0, 1, 2, ω, or epsilon numbers, i.e. fixed points
  of `fun x ↦ ω ^ x`.
-/

universe u

open Order

namespace Ordinal

variable {a b c o : Ordinal.{u}}

section Arbitrary

variable {op : Ordinal → Ordinal → Ordinal}

/-! ### Principal ordinals -/

/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard `0` as principal. -/
def Principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_swap_iff : Principal (Function.swap op) o ↔ Principal op o := by
  constructor <;> exact fun h a b ha hb => h hb ha

theorem not_principal_iff : ¬ Principal op o ↔ ∃ a < o, ∃ b < o, o ≤ op a b := by
  simp [Principal]

theorem principal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    Principal op o ↔ ∀ a < o, op a a < o := by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_gt a b
  · exact (h₂ b hab).trans_lt <| H b hb
  · exact (h₁ a hba.le).trans_lt <| H a ha

theorem not_principal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    ¬ Principal op o ↔ ∃ a < o, o ≤ op a a := by
  simp [principal_iff_of_monotone h₁ h₂]

theorem principal_zero : Principal op 0 := fun a _ h =>
  (Ordinal.not_lt_zero a h).elim

@[simp]
theorem principal_one_iff : Principal op 1 ↔ op 0 0 = 0 := by
  refine ⟨fun h => ?_, fun h a b ha hb => ?_⟩
  · rw [← lt_one_iff_zero]
    exact h zero_lt_one zero_lt_one
  · rwa [lt_one_iff_zero, ha, hb] at *

theorem Principal.iterate_lt (hao : a < o) (ho : Principal op o) (n : ℕ) : (op a)^[n] a < o := by
  induction n with
  | zero => rwa [Function.iterate_zero]
  | succ n hn =>
    rw [Function.iterate_succ']
    exact ho hao hn

theorem op_eq_self_of_principal (hao : a < o) (H : IsNormal (op a))
    (ho : Principal op o) (ho' : IsSuccLimit o) : op a o = o := by
  apply H.le_apply.antisymm'
  rw [← IsNormal.bsup_eq.{u, u} H ho', bsup_le_iff]
  exact fun b hbo => (ho hao hbo).le

theorem nfp_le_of_principal (hao : a < o) (ho : Principal op o) : nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

end Arbitrary

/-! ### Principal ordinals are unbounded -/

/-- We give an explicit construction for a principal ordinal larger or equal than `o`. -/
private theorem principal_nfp_iSup (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2)) o) := by
  intro a b ha hb
  rw [lt_nfp_iff] at *
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  obtain h | h := le_total
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[m] o)
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2))^[n] o)
  · use n + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ ↦ succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod (ha.trans_le h) hb⟩
  · use m + 1
    rw [Function.iterate_succ']
    apply (lt_succ _).trans_le
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ Set.Iio _ ↦ succ (op y.1.1 y.1.2))
      ⟨_, Set.mk_mem_prod ha (hb.trans_le h)⟩

/-- Principal ordinals under any operation are unbounded. -/
theorem not_bddAbove_principal (op : Ordinal → Ordinal → Ordinal) :
    ¬ BddAbove { o | Principal op o } := by
  rintro ⟨a, ha⟩
  exact ((le_nfp _ _).trans (ha (principal_nfp_iSup op (succ a)))).not_gt (lt_succ a)

/-! #### Additive principal ordinals -/

theorem principal_add_one : Principal (· + ·) 1 :=
  principal_one_iff.2 <| zero_add 0

theorem principal_add_of_le_one (ho : o ≤ 1) : Principal (· + ·) o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact principal_zero
  · exact principal_add_one

theorem isSuccLimit_of_principal_add (ho₁ : 1 < o) (ho : Principal (· + ·) o) : IsSuccLimit o := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  exact ⟨ho₁.ne_bot, fun _ ha ↦ ho ha ho₁⟩

@[deprecated (since := "2025-07-08")]
alias isLimit_of_principal_add := isSuccLimit_of_principal_add

theorem principal_add_iff_add_left_eq_self : Principal (· + ·) o ↔ ∀ a < o, a + o = o := by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases lt_or_ge 1 o with ho₁ | ho₁
    · exact op_eq_self_of_principal hao (isNormal_add_right a) ho
        (isSuccLimit_of_principal_add ho₁ ho)
    · rcases le_one_iff.1 ho₁ with (rfl | rfl)
      · exact (Ordinal.not_lt_zero a hao).elim
      · rw [lt_one_iff_zero] at hao
        rw [hao, zero_add]
  · rw [← h a hao]
    exact (isNormal_add_right a).strictMono hbo

theorem exists_lt_add_of_not_principal_add (ha : ¬ Principal (· + ·) a) :
    ∃ b < a, ∃ c < a, b + c = a := by
  rw [not_principal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le, hab] at H
  exact H.not_gt hc

theorem principal_add_iff_add_lt_ne_self : Principal (· + ·) a ↔ ∀ b < a, ∀ c < a, b + c ≠ a :=
  ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra! ha
    rcases exists_lt_add_of_not_principal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

theorem principal_add_omega0 : Principal (· + ·) ω :=
  principal_add_iff_add_left_eq_self.2 fun _ => add_omega0

theorem add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b := by
  refine le_antisymm ?_ (le_add_left _ a)
  induction b using limitRecOn with
  | zero =>
    rw [opow_zero, ← succ_zero, lt_succ_iff, Ordinal.le_zero] at h
    rw [h, zero_add]
  | succ =>
    rw [opow_succ] at h
    rcases (lt_mul_iff_of_isSuccLimit isSuccLimit_omega0).1 h with ⟨x, xo, ax⟩
    apply (add_le_add_right ax.le _).trans
    rw [opow_succ, ← mul_add, add_omega0 xo]
  | limit b l IH =>
    rcases (lt_opow_of_isSuccLimit omega0_ne_zero l).1 h with ⟨x, xb, ax⟩
    apply (((isNormal_add_right a).trans <| isNormal_opow one_lt_omega0).limit_le l).2
    intro y yb
    calc a + ω ^ y ≤ a + ω ^ max x y :=
      add_le_add_left (opow_le_opow_right omega0_pos (le_max_right x y)) _
    _ ≤ ω ^ max x y :=
      IH _ (max_lt xb yb) <| ax.trans_le <| opow_le_opow_right omega0_pos <| le_max_left x y
    _ ≤ ω ^ b :=
      opow_le_opow_right omega0_pos <| (max_lt xb yb).le

theorem principal_add_omega0_opow (o : Ordinal) : Principal (· + ·) (ω ^ o) :=
  principal_add_iff_add_left_eq_self.2 fun _ => add_omega0_opow

/-- The main characterization theorem for additive principal ordinals. -/
theorem principal_add_iff_zero_or_omega0_opow :
    Principal (· + ·) o ↔ o = 0 ∨ o ∈ Set.range (ω ^ · : Ordinal → Ordinal) := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · simp only [principal_zero, Or.inl]
  · rw [principal_add_iff_add_left_eq_self]
    simp only [ho, false_or]
    refine
      ⟨fun H => ⟨_, ((lt_or_eq_of_le (opow_log_le_self _ ho)).resolve_left fun h => ?_)⟩,
        fun ⟨b, e⟩ => e.symm ▸ fun a => add_omega0_opow⟩
    have := H _ h
    have := lt_opow_succ_log_self one_lt_omega0 o
    rw [opow_succ, lt_mul_iff_of_isSuccLimit isSuccLimit_omega0] at this
    rcases this with ⟨a, ao, h'⟩
    rcases lt_omega0.1 ao with ⟨n, rfl⟩
    clear ao
    revert h'
    apply not_lt_of_ge
    suffices e : ω ^ log ω o * n + o = o by
      simpa only [e] using le_add_right (ω ^ log ω o * ↑n) o
    induction n with
    | zero => simp [Nat.cast_zero, mul_zero, zero_add]
    | succ n IH => simp only [Nat.cast_succ, mul_add_one, add_assoc, this, IH]

theorem principal_add_opow_of_principal_add {a} (ha : Principal (· + ·) a) (b : Ordinal) :
    Principal (· + ·) (a ^ b) := by
  rcases principal_add_iff_zero_or_omega0_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact principal_add_one
    · rwa [zero_opow hb]
  · rw [← opow_mul]
    exact principal_add_omega0_opow _

theorem add_absorp (h₁ : a < ω ^ b) (h₂ : ω ^ b ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le h₂, ← add_assoc, add_omega0_opow h₁]

theorem principal_add_mul_of_principal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : Principal (· + ·) b) : Principal (· + ·) (a * b) := by
  rcases eq_zero_or_pos a with (rfl | _)
  · rw [zero_mul]
    exact principal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact principal_zero
    · rw [← succ_le_iff, succ_zero] at hb₁'
      intro c d hc hd
      rw [lt_mul_iff_of_isSuccLimit
        (isSuccLimit_of_principal_add (lt_of_le_of_ne hb₁' hb₁.symm) hb)] at *
      rcases hc with ⟨x, hx, hx'⟩
      rcases hd with ⟨y, hy, hy'⟩
      use x + y, hb hx hy
      rw [mul_add]
      exact Left.add_lt_add hx' hy'

/-! #### Multiplicative principal ordinals -/

theorem principal_mul_one : Principal (· * ·) 1 := by
  rw [principal_one_iff]
  exact zero_mul _

theorem principal_mul_two : Principal (· * ·) 2 := by
  intro a b ha hb
  rw [← succ_one, lt_succ_iff] at *
  convert mul_le_mul' ha hb
  exact (mul_one 1).symm

theorem principal_mul_of_le_two (ho : o ≤ 2) : Principal (· * ·) o := by
  rcases lt_or_eq_of_le ho with (ho | rfl)
  · rw [← succ_one, lt_succ_iff] at ho
    rcases lt_or_eq_of_le ho with (ho | rfl)
    · rw [lt_one_iff_zero.1 ho]
      exact principal_zero
    · exact principal_mul_one
  · exact principal_mul_two

theorem principal_add_of_principal_mul (ho : Principal (· * ·) o) (ho₂ : o ≠ 2) :
    Principal (· + ·) o := by
  rcases lt_or_gt_of_ne ho₂ with ho₁ | ho₂
  · replace ho₁ : o < succ 1 := by rwa [succ_one]
    rw [lt_succ_iff] at ho₁
    exact principal_add_of_le_one ho₁
  · refine fun a b hao hbo => lt_of_le_of_lt ?_ (ho (max_lt hao hbo) ho₂)
    dsimp only
    rw [← one_add_one_eq_two, mul_add, mul_one]
    exact add_le_add (le_max_left a b) (le_max_right a b)

theorem isSuccLimit_of_principal_mul (ho₂ : 2 < o) (ho : Principal (· * ·) o) : IsSuccLimit o :=
  isSuccLimit_of_principal_add ((lt_succ 1).trans (succ_one ▸ ho₂))
    (principal_add_of_principal_mul ho (ne_of_gt ho₂))

@[deprecated (since := "2025-07-08")]
alias isLimit_of_principal_mul := isSuccLimit_of_principal_mul

theorem principal_mul_iff_mul_left_eq : Principal (· * ·) o ↔ ∀ a, 0 < a → a < o → a * o = o := by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases le_or_gt o 2 with ho | ho
    · convert one_mul o
      apply le_antisymm
      · rw [← lt_succ_iff, succ_one]
        exact hao.trans_le ho
      · rwa [← succ_le_iff, succ_zero] at ha₀
    · exact op_eq_self_of_principal hao (isNormal_mul_right ha₀) h
        (isSuccLimit_of_principal_mul ho h)
  · rcases eq_or_ne a 0 with (rfl | ha)
    · dsimp only; rwa [zero_mul]
    rw [← Ordinal.pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (isNormal_mul_right ha).strictMono hbo

theorem principal_mul_omega0 : Principal (· * ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply nat_lt_omega0

theorem mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω :=
  principal_mul_iff_mul_left_eq.1 principal_mul_omega0 a a0 ha

theorem natCast_mul_omega0 {n : ℕ} (hn : 0 < n) : n * ω = ω :=
  mul_omega0 (mod_cast hn) (nat_lt_omega0 n)

theorem mul_lt_omega0_opow (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω) : a * b < ω ^ c := by
  rcases zero_or_succ_or_isSuccLimit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irrefl _).elim c0
  · rw [opow_succ] at ha
    obtain ⟨n, hn, an⟩ :=
      ((isNormal_mul_right <| opow_pos _ omega0_pos).limit_lt isSuccLimit_omega0).1 ha
    apply (mul_le_mul_right' (le_of_lt an) _).trans_lt
    rw [opow_succ, mul_assoc, mul_lt_mul_iff_left (opow_pos _ omega0_pos)]
    exact principal_mul_omega0 hn hb
  · rcases ((isNormal_opow one_lt_omega0).limit_lt l).1 ha with ⟨x, hx, ax⟩
    refine (mul_le_mul' (le_of_lt ax) (le_of_lt hb)).trans_lt ?_
    rw [← opow_succ, opow_lt_opow_iff_right one_lt_omega0]
    exact l.succ_lt hx

theorem mul_omega0_opow_opow (a0 : 0 < a) (h : a < ω ^ ω ^ b) : a * ω ^ ω ^ b = ω ^ ω ^ b := by
  obtain rfl | b0 := eq_or_ne b 0
  · rw [opow_zero, opow_one] at h ⊢
    exact mul_omega0 a0 h
  · apply le_antisymm
    · obtain ⟨x, xb, ax⟩ :=
        (lt_opow_of_isSuccLimit omega0_ne_zero (isSuccLimit_opow_left isSuccLimit_omega0 b0)).1 h
      apply (mul_le_mul_right' (le_of_lt ax) _).trans
      rw [← opow_add, add_omega0_opow xb]
    · conv_lhs => rw [← one_mul (ω ^ _)]
      exact mul_le_mul_right' (one_le_iff_pos.2 a0) _

theorem principal_mul_omega0_opow_opow (o : Ordinal) : Principal (· * ·) (ω ^ ω ^ o) :=
  principal_mul_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

theorem principal_add_of_principal_mul_opow (hb : 1 < b) (ho : Principal (· * ·) (b ^ o)) :
    Principal (· + ·) o := by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

/-- The main characterization theorem for multiplicative principal ordinals. -/
theorem principal_mul_iff_le_two_or_omega0_opow_opow :
    Principal (· * ·) o ↔ o ≤ 2 ∨ o ∈ Set.range (ω ^ ω ^ · : Ordinal → Ordinal) := by
  refine ⟨fun ho => ?_, ?_⟩
  · rcases le_or_gt o 2 with ho₂ | ho₂
    · exact Or.inl ho₂
    · rcases principal_add_iff_zero_or_omega0_opow.1 (principal_add_of_principal_mul ho ho₂.ne')
        with (rfl | ⟨a, rfl⟩)
      · exact (Ordinal.not_lt_zero 2 ho₂).elim
      · rcases principal_add_iff_zero_or_omega0_opow.1
          (principal_add_of_principal_mul_opow one_lt_omega0 ho) with (rfl | ⟨b, rfl⟩)
        · simp
        · exact Or.inr ⟨b, rfl⟩
  · rintro (ho₂ | ⟨a, rfl⟩)
    · exact principal_mul_of_le_two ho₂
    · exact principal_mul_omega0_opow_opow a

theorem mul_omega0_dvd (a0 : 0 < a) (ha : a < ω) : ∀ {b}, ω ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by rw [← mul_assoc, mul_omega0 a0 ha]

theorem mul_eq_opow_log_succ (ha : a ≠ 0) (hb : Principal (· * ·) b) (hb₂ : 2 < b) :
    a * b = b ^ succ (log b a) := by
  apply le_antisymm
  · have hbl := isSuccLimit_of_principal_mul hb₂ hb
    rw [← (isNormal_mul_right (Ordinal.pos_iff_ne_zero.2 ha)).bsup_eq hbl, bsup_le_iff]
    intro c hcb
    have hb₁ : 1 < b := one_lt_two.trans hb₂
    have hbo₀ : b ^ log b a ≠ 0 := Ordinal.pos_iff_ne_zero.1 (opow_pos _ (zero_lt_one.trans hb₁))
    apply (mul_le_mul_right' (le_of_lt (lt_mul_succ_div a hbo₀)) c).trans
    rw [mul_assoc, opow_succ]
    refine mul_le_mul_left' (hb (hbl.succ_lt ?_) hcb).le _
    rw [div_lt hbo₀, ← opow_succ]
    exact lt_opow_succ_log_self hb₁ _
  · rw [opow_succ]
    exact mul_le_mul_right' (opow_log_le_self b ha) b

/-! #### Exponential principal ordinals -/

theorem principal_opow_omega0 : Principal (· ^ ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    simp_rw [← natCast_opow]
    apply nat_lt_omega0

theorem opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω :=
  ((opow_le_of_isSuccLimit (one_le_iff_ne_zero.1 <| le_of_lt a1) isSuccLimit_omega0).2 fun _ hb =>
      (principal_opow_omega0 h hb).le).antisymm
  (right_le_opow _ a1)

theorem natCast_opow_omega0 {n : ℕ} (hn : 1 < n) : n ^ ω = ω :=
  opow_omega0 (mod_cast hn) (nat_lt_omega0 n)

end Ordinal
