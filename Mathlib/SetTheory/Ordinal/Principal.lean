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
* `unbounded_principal`: Principal ordinals are unbounded.
* `principal_add_iff_zero_or_omega_opow`: The main characterization theorem for additive principal
  ordinals.
* `principal_mul_iff_le_two_or_omega_opow_opow`: The main characterization theorem for
  multiplicative principal ordinals.

## TODO
* Prove that exponential principal ordinals are 0, 1, 2, ω, or epsilon numbers, i.e. fixed points
  of `fun x ↦ ω ^ x`.
-/

universe u

open Order

namespace Ordinal

section Arbitrary

variable {op : Ordinal → Ordinal → Ordinal}

/-! ### Principal ordinals -/


/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard `0` as principal. -/
def Principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_swap_iff {o : Ordinal} : Principal (Function.swap op) o ↔ Principal op o := by
  constructor <;> exact fun h a b ha hb => h hb ha

@[deprecated principal_swap_iff (since := "2024-08-18")]
theorem principal_iff_principal_swap {o : Ordinal} :
    Principal op o ↔ Principal (Function.swap op) o :=
  principal_swap_iff

theorem not_principal_iff {o : Ordinal} : ¬ Principal op o ↔ ∃ a < o, ∃ b < o, o ≤ op a b := by
  simp [Principal]

theorem principal_zero : Principal op 0 := fun a _ h =>
  (Ordinal.not_lt_zero a h).elim

@[simp]
theorem principal_one_iff : Principal op 1 ↔ op 0 0 = 0 := by
  refine ⟨fun h => ?_, fun h a b ha hb => ?_⟩
  · rw [← lt_one_iff_zero]
    exact h zero_lt_one zero_lt_one
  · rwa [lt_one_iff_zero, ha, hb] at *

theorem Principal.iterate_lt {a o : Ordinal} (hao : a < o) (ho : Principal op o) (n : ℕ) :
    (op a)^[n] a < o := by
  induction' n with n hn
  · rwa [Function.iterate_zero]
  · rw [Function.iterate_succ']
    exact ho hao hn

theorem op_eq_self_of_principal {a o : Ordinal.{u}} (hao : a < o) (H : IsNormal (op a))
    (ho : Principal op o) (ho' : IsLimit o) : op a o = o := by
  refine le_antisymm ?_ (H.self_le _)
  rw [← IsNormal.bsup_eq.{u, u} H ho', bsup_le_iff]
  exact fun b hbo => (ho hao hbo).le

theorem nfp_le_of_principal {a o : Ordinal} (hao : a < o) (ho : Principal op o) :
    nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

end Arbitrary

/-! ### Principal ordinals are unbounded -/

#adaptation_note /-- 2024-04-23
After https://github.com/leanprover/lean4/pull/3965,
we need to write `lt_blsub₂.{u}` twice below,
where previously the universe annotation was not necessary.
This appears to be correct behaviour, as `lt_blsub₂.{0}` also works. -/
theorem principal_nfp_blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b)) o) := by
  intro a b ha hb
  rw [lt_nfp] at *
  cases' ha with m hm
  cases' hb with n hn
  cases' le_total
    ((fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b))^[m] o)
    ((fun o' => blsub₂.{u, u, u} o' o' (@fun a _ b _ => op a b))^[n] o) with h h
  · use n + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ (@fun a _ b _ => op a b) (hm.trans_le h) hn
  · use m + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ (@fun a _ b _ => op a b) hm (hn.trans_le h)

/-- Principal ordinals under any operation form a ZFC proper class. -/
theorem unbounded_principal (op : Ordinal → Ordinal → Ordinal) :
    Set.Unbounded (· < ·) { o | Principal op o } := fun o =>
  ⟨_, principal_nfp_blsub₂ op o, (le_nfp _ o).not_lt⟩

/-! #### Additive principal ordinals -/


theorem principal_add_one : Principal (· + ·) 1 :=
  principal_one_iff.2 <| zero_add 0

theorem principal_add_of_le_one {o : Ordinal} (ho : o ≤ 1) : Principal (· + ·) o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact principal_zero
  · exact principal_add_one

theorem principal_add_isLimit {o : Ordinal} (ho₁ : 1 < o) (ho : Principal (· + ·) o) :
    o.IsLimit := by
  refine ⟨fun ho₀ => ?_, fun a hao => ?_⟩
  · rw [ho₀] at ho₁
    exact not_lt_of_gt zero_lt_one ho₁
  · rcases eq_or_ne a 0 with ha | ha
    · rw [ha, succ_zero]
      exact ho₁
    · refine lt_of_le_of_lt ?_ (ho hao hao)
      rwa [← add_one_eq_succ, add_le_add_iff_left, one_le_iff_ne_zero]

theorem principal_add_iff_add_left_eq_self {o : Ordinal} :
    Principal (· + ·) o ↔ ∀ a < o, a + o = o := by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · cases' lt_or_le 1 o with ho₁ ho₁
    · exact op_eq_self_of_principal hao (add_isNormal a) ho (principal_add_isLimit ho₁ ho)
    · rcases le_one_iff.1 ho₁ with (rfl | rfl)
      · exact (Ordinal.not_lt_zero a hao).elim
      · rw [lt_one_iff_zero] at hao
        rw [hao, zero_add]
  · rw [← h a hao]
    exact (add_isNormal a).strictMono hbo

theorem exists_lt_add_of_not_principal_add {a} (ha : ¬Principal (· + ·) a) :
    ∃ b < a, ∃ c < a, b + c = a := by
  rw [not_principal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le, hab] at H
  exact H.not_lt hc

theorem principal_add_iff_add_lt_ne_self {a} :
    Principal (· + ·) a ↔ ∀ b < a, ∀ c < a, b + c ≠ a :=
  ⟨fun ha b hb c hc => (ha hb hc).ne, fun H => by
    by_contra! ha
    rcases exists_lt_add_of_not_principal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

theorem add_omega {a : Ordinal} (h : a < ω) : a + ω = ω := by
  rcases lt_omega.1 h with ⟨n, rfl⟩
  clear h; induction' n with n IH
  · rw [Nat.cast_zero, zero_add]
  · rwa [Nat.cast_succ, add_assoc, one_add_of_omega_le (le_refl _)]

theorem principal_add_omega : Principal (· + ·) ω :=
  principal_add_iff_add_left_eq_self.2 fun _ => add_omega

theorem add_omega_opow {a b : Ordinal} (h : a < ω ^ b) : a + ω ^ b = ω ^ b := by
  refine le_antisymm ?_ (le_add_left _ a)
  induction' b using limitRecOn with b _ b l IH
  · rw [opow_zero, ← succ_zero, lt_succ_iff, Ordinal.le_zero] at h
    rw [h, zero_add]
  · rw [opow_succ] at h
    rcases (lt_mul_of_limit omega_isLimit).1 h with ⟨x, xo, ax⟩
    apply (add_le_add_right ax.le _).trans
    rw [opow_succ, ← mul_add, add_omega xo]
  · rcases (lt_opow_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩
    apply (((add_isNormal a).trans <| opow_isNormal one_lt_omega).limit_le l).2
    intro y yb
    calc a + ω ^ y ≤ a + ω ^ max x y :=
      add_le_add_left (opow_le_opow_right omega_pos (le_max_right x y)) _
    _ ≤ ω ^ max x y :=
      IH _ (max_lt xb yb) <| ax.trans_le <| opow_le_opow_right omega_pos <| le_max_left x y
    _ ≤ ω ^ b :=
      opow_le_opow_right omega_pos <| (max_lt xb yb).le

theorem principal_add_omega_opow (o : Ordinal) : Principal (· + ·) (ω ^ o) :=
  principal_add_iff_add_left_eq_self.2 fun _ => add_omega_opow

/-- The main characterization theorem for additive principal ordinals. -/
theorem principal_add_iff_zero_or_omega_opow {o : Ordinal} :
    Principal (· + ·) o ↔ o = 0 ∨ o ∈ Set.range (ω ^ · : Ordinal → Ordinal) := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · simp only [principal_zero, Or.inl]
  · rw [principal_add_iff_add_left_eq_self]
    simp only [ho, false_or_iff]
    refine
      ⟨fun H => ⟨_, ((lt_or_eq_of_le (opow_log_le_self _ ho)).resolve_left fun h => ?_)⟩,
        fun ⟨b, e⟩ => e.symm ▸ fun a => add_omega_opow⟩
    have := H _ h
    have := lt_opow_succ_log_self one_lt_omega o
    rw [opow_succ, lt_mul_of_limit omega_isLimit] at this
    rcases this with ⟨a, ao, h'⟩
    rcases lt_omega.1 ao with ⟨n, rfl⟩
    clear ao
    revert h'
    apply not_lt_of_le
    suffices e : ω ^ log ω o * n + o = o by
      simpa only [e] using le_add_right (ω ^ log ω o * ↑n) o
    induction' n with n IH
    · simp [Nat.cast_zero, mul_zero, zero_add]
    · simp only [Nat.cast_succ, mul_add_one, add_assoc, this, IH]

theorem opow_principal_add_of_principal_add {a} (ha : Principal (· + ·) a) (b : Ordinal) :
    Principal (· + ·) (a ^ b) := by
  rcases principal_add_iff_zero_or_omega_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact principal_add_one
    · rwa [zero_opow hb]
  · rw [← opow_mul]
    exact principal_add_omega_opow _

theorem add_absorp {a b c : Ordinal} (h₁ : a < ω ^ b) (h₂ : ω ^ b ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le h₂, ← add_assoc, add_omega_opow h₁]

theorem mul_principal_add_is_principal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : Principal (· + ·) b) : Principal (· + ·) (a * b) := by
  rcases eq_zero_or_pos a with (rfl | _)
  · rw [zero_mul]
    exact principal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact principal_zero
    · rw [← succ_le_iff, succ_zero] at hb₁'
      intro c d hc hd
      rw [lt_mul_of_limit (principal_add_isLimit (lt_of_le_of_ne hb₁' hb₁.symm) hb)] at *
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

theorem principal_mul_of_le_two {o : Ordinal} (ho : o ≤ 2) : Principal (· * ·) o := by
  rcases lt_or_eq_of_le ho with (ho | rfl)
  · rw [← succ_one, lt_succ_iff] at ho
    rcases lt_or_eq_of_le ho with (ho | rfl)
    · rw [lt_one_iff_zero.1 ho]
      exact principal_zero
    · exact principal_mul_one
  · exact principal_mul_two

theorem principal_add_of_principal_mul {o : Ordinal} (ho : Principal (· * ·) o) (ho₂ : o ≠ 2) :
    Principal (· + ·) o := by
  cases' lt_or_gt_of_ne ho₂ with ho₁ ho₂
  · replace ho₁ : o < succ 1 := by simpa using ho₁
    rw [lt_succ_iff] at ho₁
    exact principal_add_of_le_one ho₁
  · refine fun a b hao hbo => lt_of_le_of_lt ?_ (ho (max_lt hao hbo) ho₂)
    dsimp only
    rw [← one_add_one_eq_two, mul_add, mul_one]
    exact add_le_add (le_max_left a b) (le_max_right a b)

theorem principal_mul_isLimit {o : Ordinal.{u}} (ho₂ : 2 < o) (ho : Principal (· * ·) o) :
    o.IsLimit :=
  principal_add_isLimit ((lt_succ 1).trans (by simpa using ho₂))
    (principal_add_of_principal_mul ho (ne_of_gt ho₂))

theorem principal_mul_iff_mul_left_eq {o : Ordinal} :
    Principal (· * ·) o ↔ ∀ a, 0 < a → a < o → a * o = o := by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · cases' le_or_gt o 2 with ho ho
    · convert one_mul o
      apply le_antisymm
      · have : a < succ 1 := hao.trans_le (by simpa using ho)
        rwa [lt_succ_iff] at this
      · rwa [← succ_le_iff, succ_zero] at ha₀
    · exact op_eq_self_of_principal hao (mul_isNormal ha₀) h (principal_mul_isLimit ho h)
  · rcases eq_or_ne a 0 with (rfl | ha)
    · dsimp only; rwa [zero_mul]
    rw [← Ordinal.pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (mul_isNormal ha).strictMono hbo

theorem principal_mul_omega : Principal (· * ·) ω := fun a b ha hb =>
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply nat_lt_omega

theorem mul_omega {a : Ordinal} (a0 : 0 < a) (ha : a < ω) : a * ω = ω :=
  principal_mul_iff_mul_left_eq.1 principal_mul_omega a a0 ha

theorem mul_lt_omega_opow {a b c : Ordinal} (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω) :
    a * b < ω ^ c := by
  rcases zero_or_succ_or_limit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irrefl _).elim c0
  · rw [opow_succ] at ha
    rcases ((mul_isNormal <| opow_pos _ omega_pos).limit_lt omega_isLimit).1 ha with ⟨n, hn, an⟩
    apply (mul_le_mul_right' (le_of_lt an) _).trans_lt
    rw [opow_succ, mul_assoc, mul_lt_mul_iff_left (opow_pos _ omega_pos)]
    exact principal_mul_omega hn hb
  · rcases ((opow_isNormal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩
    refine (mul_le_mul' (le_of_lt ax) (le_of_lt hb)).trans_lt ?_
    rw [← opow_succ, opow_lt_opow_iff_right one_lt_omega]
    exact l.2 _ hx

theorem mul_omega_opow_opow {a b : Ordinal} (a0 : 0 < a) (h : a < ω ^ ω ^ b) :
    a * ω ^ ω ^ b = ω ^ ω ^ b := by
  obtain rfl | b0 := eq_or_ne b 0
  · rw [opow_zero, opow_one] at h ⊢
    exact mul_omega a0 h
  · apply le_antisymm
    · obtain ⟨x, xb, ax⟩ :=
        (lt_opow_of_limit omega_ne_zero (opow_isLimit_left omega_isLimit b0)).1 h
      apply (mul_le_mul_right' (le_of_lt ax) _).trans
      rw [← opow_add, add_omega_opow xb]
    · conv_lhs => rw [← one_mul (ω ^ _)]
      exact mul_le_mul_right' (one_le_iff_pos.2 a0) _

theorem principal_mul_omega_opow_opow (o : Ordinal) : Principal (· * ·) (ω ^ ω ^ o) :=
  principal_mul_iff_mul_left_eq.2 fun _ => mul_omega_opow_opow

theorem principal_add_of_principal_mul_opow {o b : Ordinal} (hb : 1 < b)
    (ho : Principal (· * ·) (b ^ o)) : Principal (· + ·) o := by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

/-- The main characterization theorem for multiplicative principal ordinals. -/
theorem principal_mul_iff_le_two_or_omega_opow_opow {o : Ordinal} :
    Principal (· * ·) o ↔ o ≤ 2 ∨ o ∈ Set.range (ω ^ ω ^ · : Ordinal → Ordinal) := by
  refine ⟨fun ho => ?_, ?_⟩
  · rcases le_or_lt o 2 with ho₂ | ho₂
    · exact Or.inl ho₂
    · rcases principal_add_iff_zero_or_omega_opow.1 (principal_add_of_principal_mul ho ho₂.ne') with
      (rfl | ⟨a, rfl⟩)
      · exact (Ordinal.not_lt_zero 2 ho₂).elim
      · rcases principal_add_iff_zero_or_omega_opow.1
          (principal_add_of_principal_mul_opow one_lt_omega ho) with (rfl | ⟨b, rfl⟩)
        · simp
        · exact Or.inr ⟨b, rfl⟩
  · rintro (ho₂ | ⟨a, rfl⟩)
    · exact principal_mul_of_le_two ho₂
    · exact principal_mul_omega_opow_opow a

theorem mul_omega_dvd {a : Ordinal} (a0 : 0 < a) (ha : a < ω) : ∀ {b}, ω ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by rw [← mul_assoc, mul_omega a0 ha]

theorem mul_eq_opow_log_succ {a b : Ordinal.{u}} (ha : a ≠ 0) (hb : Principal (· * ·) b)
    (hb₂ : 2 < b) : a * b = b ^ succ (log b a) := by
  apply le_antisymm
  · have hbl := principal_mul_isLimit hb₂ hb
    rw [← IsNormal.bsup_eq.{u, u} (mul_isNormal (Ordinal.pos_iff_ne_zero.2 ha)) hbl, bsup_le_iff]
    intro c hcb
    have hb₁ : 1 < b := (lt_succ 1).trans (by rwa [succ_one])
    have hbo₀ : b ^ log b a ≠ 0 := Ordinal.pos_iff_ne_zero.1 (opow_pos _ (zero_lt_one.trans hb₁))
    apply (mul_le_mul_right' (le_of_lt (lt_mul_succ_div a hbo₀)) c).trans
    rw [mul_assoc, opow_succ]
    refine mul_le_mul_left' (hb (hbl.2 _ ?_) hcb).le _
    rw [div_lt hbo₀, ← opow_succ]
    exact lt_opow_succ_log_self hb₁ _
  · rw [opow_succ]
    exact mul_le_mul_right' (opow_log_le_self b ha) b

/-! #### Exponential principal ordinals -/


theorem principal_opow_omega : Principal (· ^ ·) ω := fun a b ha hb =>
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    simp_rw [← natCast_opow]
    apply nat_lt_omega

theorem opow_omega {a : Ordinal} (a1 : 1 < a) (h : a < ω) : a ^ ω = ω :=
  ((opow_le_of_limit (one_le_iff_ne_zero.1 <| le_of_lt a1) omega_isLimit).2 fun _ hb =>
      (principal_opow_omega h hb).le).antisymm
  (right_le_opow _ a1)

end Ordinal
