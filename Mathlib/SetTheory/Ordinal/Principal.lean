/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPoint

import Mathlib.Order.Cofinal

/-!
# Principal ordinals

If `op` is a binary operation on ordinals, we say that an ordinal `o` is `op`-principal (or
`op`-indecomposable) whenever `a < o` and `b < o` imply `op a b < o`. Most commonly, one talks of
additive and multiplicative principal ordinals.

Additive principal ordinals were originally called "gamma numbers" by Cantor, but this term now more
commonly refers to the values given by `Ordinal.gamma`. Likewise, multiplicative principal ordinals
are sometimes known as "delta numbers". Exponential principal ordinals are (barring edge cases)
equivalent to the epsilon numbers given by `Ordinal.epsilon`.

## Main definitions and results

* `IsPrincipal`: A principal (or indecomposable) ordinal under some binary operation. We include `0`
  and other typically excluded edge cases for simplicity.
* `isCofinal_setOfPred_isPrincipal`: Principal ordinals (under any operation) are unbounded.
* `isAddPrincipal_iff_zero_or_omega0_opow`: The additive principal ordinals are
  `0` and the ordinal powers of `ω`.
* `isMulPrincipal_iff_le_two_or_omega0_opow_opow`: The multiplicative principal ordinals are
  `0`, `1`, `2`, and the ordinals `ω ^ ω ^ x`.

## Tags

additively indecomposable, multiplicatively indecomposable
-/

public section

universe u

open Order

namespace Ordinal

variable {a b c o : Ordinal.{u}}

section Arbitrary

variable {op : Ordinal → Ordinal → Ordinal}

/-! ### Principal ordinals under an arbitrary operation -/

/-- An ordinal `o` is said to be principal (or indecomposable) under an operation when `Iio o` is
closed under that operation.

For simplicity, we break usual convention and regard `0` as principal. -/
@[expose]
def IsPrincipal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem isPrincipal_swap_iff : IsPrincipal (Function.swap op) o ↔ IsPrincipal op o := by
  constructor <;> exact fun h a b ha hb => h hb ha

theorem not_isPrincipal_iff : ¬ IsPrincipal op o ↔ ∃ a < o, ∃ b < o, o ≤ op a b := by
  simp [IsPrincipal]

theorem isPrincipal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    IsPrincipal op o ↔ ∀ a < o, op a a < o := by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_gt a b
  · exact (h₂ b hab).trans_lt <| H b hb
  · exact (h₁ a hba.le).trans_lt <| H a ha

theorem not_isPrincipal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    ¬ IsPrincipal op o ↔ ∃ a < o, o ≤ op a a := by
  simp [isPrincipal_iff_of_monotone h₁ h₂]

@[simp] lemma IsPrincipal.zero : IsPrincipal op 0 := by simp [IsPrincipal]

@[deprecated (since := "2026-11-12")]
alias isPrincipal_zero := IsPrincipal.zero

@[simp] theorem isPrincipal_one_iff : IsPrincipal op 1 ↔ op 0 0 = 0 := by simp [IsPrincipal]

theorem IsPrincipal.iterate_lt (hao : a < o) (ho : IsPrincipal op o) (n : ℕ) :
    (op a)^[n] a < o := by
  induction n with
  | zero => rwa [Function.iterate_zero]
  | succ n hn =>
    rw [Function.iterate_succ']
    exact ho hao hn

theorem op_eq_self_of_isPrincipal (hao : a < o) (H : IsNormal (op a))
    (ho : IsPrincipal op o) (ho' : IsSuccLimit o) : op a o = o := by
  apply H.strictMono.le_apply.antisymm'
  rw [H.apply_of_isSuccLimit ho', Ordinal.iSup_le_iff]
  exact fun ⟨b, hbo⟩ ↦ (ho hao hbo).le

theorem nfp_le_of_isPrincipal (hao : a < o) (ho : IsPrincipal op o) : nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

protected theorem IsPrincipal.sSup {s : Set Ordinal} (H : ∀ x ∈ s, IsPrincipal op x) :
    IsPrincipal op (sSup s) := by
  have : IsPrincipal op (sSup ∅) := by simp
  by_cases hs : BddAbove s
  · obtain rfl | hs' := s.eq_empty_or_nonempty
    · assumption
    simp only [IsPrincipal, lt_csSup_iff hs hs', forall_exists_index, and_imp]
    intro x y a has ha b hbs hb
    have h : max a b ∈ s := max_rec' _ has hbs
    exact ⟨_, h, H (max a b) h (lt_max_of_lt_left ha) (lt_max_of_lt_right hb)⟩
  · rwa [csSup_of_not_bddAbove hs]

protected theorem IsPrincipal.iSup {ι} {f : ι → Ordinal} (H : ∀ i, IsPrincipal op (f i)) :
    IsPrincipal op (⨆ i, f i) := IsPrincipal.sSup (by simpa)

end Arbitrary

/-- Principal ordinals under any operation are unbounded. -/
theorem isCofinal_setOfPred_isPrincipal (op : Ordinal → Ordinal → Ordinal) :
    IsCofinal { o | IsPrincipal op o } := by
  refine fun o ↦ ⟨nfp (fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, op y.1.1 y.1.2 + 1) o, ?_, le_nfp ..⟩
  intro a b ha hb
  rw [lt_nfp_iff] at *
  obtain ⟨m, ha⟩ := ha
  obtain ⟨n, hb⟩ := hb
  obtain h | h := le_total
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, op y.1.1 y.1.2 + 1)^[m] o)
    ((fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, op y.1.1 y.1.2 + 1)^[n] o)
  · use n + 1
    rw [Function.iterate_succ', ← add_one_le_iff]
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ _ ↦ _) ⟨_, Set.mk_mem_prod (ha.trans_le h) hb⟩
  · use m + 1
    rw [Function.iterate_succ', ← add_one_le_iff]
    exact Ordinal.le_iSup (fun y : Set.Iio _ ×ˢ _ ↦ _) ⟨_, Set.mk_mem_prod ha (hb.trans_le h)⟩

@[deprecated isCofinal_setOfPred_isPrincipal +typeChanged (since := "2026-11-12")]
theorem not_bddAbove_setOfPred_isPrincipal (op : Ordinal → Ordinal → Ordinal) :
    ¬ BddAbove { o | IsPrincipal op o } :=
  (isCofinal_setOfPred_isPrincipal op).not_bddAbove

@[deprecated (since := "2026-07-09")]
alias not_bddAbove_setOf_isPrincipal := isCofinal_setOfPred_isPrincipal

/-! ### Additive principal ordinals -/

/-- An ordinal `o` is said to be additive principal when
`a < o` and `b < o` imply `a + b < o`.

Note that under this definition, `0` is considered additive principal. Every other additive
principal ordinal is a power of `ω`, see `isAddPrincipal_iff_zero_or_omega0_opow`. -/
abbrev IsAddPrincipal : Ordinal → Prop := IsPrincipal (· + ·)

theorem isAddPrincipal_iff_add_self_lt : IsAddPrincipal a ↔ ∀ b < a, b + b < a :=
  isPrincipal_iff_of_monotone
    (fun x _ _ h ↦ add_le_add_right h x) (fun x _ _ h ↦ add_le_add_left h x)

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_iff_add_self_lt := isAddPrincipal_iff_add_self_lt

theorem IsAddPrincipal.mul_natCast_lt (ho : IsAddPrincipal o) (ha : a < o) (n : ℕ) : a * n < o := by
  induction n with
  | zero => simpa using ha.pos
  | succ n h =>
    rw [Nat.cast_add_one, mul_add_one]
    exact ho h ha

@[deprecated (since := "2026-11-12")]
alias IsPrincipal.mul_natCast_lt := IsAddPrincipal.mul_natCast_lt

theorem IsAddPrincipal.one : IsAddPrincipal 1 := by simp

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_one := IsAddPrincipal.one

theorem IsAddPrincipal.of_le_one (ho : o ≤ 1) : IsAddPrincipal o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  exacts [.zero, .one]

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_of_le_one := IsAddPrincipal.of_le_one

theorem IsAddPrincipal.isSuccLimit (ho₁ : 1 < o) (ho : IsAddPrincipal o) : IsSuccLimit o := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  exact ⟨ho₁.ne_zero, fun _ ha ↦ ho ha ho₁⟩

@[deprecated (since := "2026-11-12")]
alias isSuccLimit_of_isPrincipal_add := IsAddPrincipal.isSuccLimit

theorem isAddPrincipal_iff_add_left_eq_self : IsAddPrincipal o ↔ ∀ a < o, a + o = o := by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases lt_or_ge 1 o with ho₁ | ho₁
    · exact op_eq_self_of_isPrincipal hao (isNormal_add_right a) ho (ho.isSuccLimit ho₁)
    · cases le_one_iff.1 ho₁ <;> simp_all
  · rw [← h a hao]
    exact (isNormal_add_right a).strictMono hbo

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_iff_add_left_eq_self := isAddPrincipal_iff_add_left_eq_self

theorem IsAddPrincipal.add_eq_right (ho : IsAddPrincipal o) (ha : a < o) : a + o = o :=
  isAddPrincipal_iff_add_left_eq_self.1 ho a ha

@[deprecated (since := "2026-11-12")]
alias IsPrincipal.add_eq_right := IsAddPrincipal.add_eq_right

theorem IsAddPrincipal.add_eq_right_of_le (hb : IsAddPrincipal b)
    (hab : a < b) (hbc : b ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le hbc, ← add_assoc, hb.add_eq_right hab,
    Ordinal.add_sub_cancel_of_le hbc]

@[deprecated (since := "2026-11-12")]
alias IsPrincipal.add_eq_right_of_le := IsAddPrincipal.add_eq_right_of_le

theorem exists_lt_add_of_not_isAddPrincipal (ha : ¬ IsAddPrincipal a) :
    ∃ b < a, ∃ c < a, b + c = a := by
  rw [not_isPrincipal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le, hab] at H
  exact H.not_gt hc

@[deprecated (since := "2026-11-12")]
alias exists_lt_add_of_not_isPrincipal_add := exists_lt_add_of_not_isAddPrincipal

theorem isAddPrincipal_iff_add_lt_ne_self : IsAddPrincipal a ↔ ∀ b < a, ∀ c < a, b + c ≠ a :=
  ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra ha
    rcases exists_lt_add_of_not_isAddPrincipal ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_iff_add_lt_ne_self := isAddPrincipal_iff_add_lt_ne_self

theorem IsAddPrincipal.omega0 : IsAddPrincipal ω :=
  isAddPrincipal_iff_add_left_eq_self.2 fun _ => add_omega0

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_omega0 := IsAddPrincipal.omega0

-- `add_omega0` is proven in the Arithmetic file.

theorem add_of_omega0_le : a < ω → ω ≤ b → a + b = b :=
  IsAddPrincipal.omega0.add_eq_right_of_le

theorem IsAddPrincipal.omega0_opow (o : Ordinal) : IsAddPrincipal (ω ^ o) := by
  obtain rfl | ha' := eq_or_ne o 0
  · simp
  · rw [isAddPrincipal_iff_add_self_lt]
    intro a ha
    obtain ⟨c, hc, m, hm⟩ := (lt_omega0_opow ha').1 ha
    apply (add_lt_add_of_le_of_lt hm.le hm).trans_le
    rw [← mul_add, ← Nat.cast_add]
    exact (opow_mul_lt_opow (natCast_lt_omega0 _) hc).le

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_omega0_opow := IsAddPrincipal.omega0_opow

theorem add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b :=
  (IsAddPrincipal.omega0_opow b).add_eq_right h

theorem add_of_omega0_opow_le (h₁ : a < ω ^ b) (h₂ : ω ^ b ≤ c) : a + c = c :=
  (IsAddPrincipal.omega0_opow b).add_eq_right_of_le h₁ h₂

/-- For `a ≠ 0`, the largest power of `ω` which is less or equal to it is also the smallest ordinal
`b` with `a - b < a`. -/
theorem isLeast_sub_lt_omega0_opow_log (h : a ≠ 0) : IsLeast {b | a - b < a} (ω ^ log ω a) := by
  refine ⟨sub_omega0_opow_log_lt h, fun c (hc : a - _ < _) ↦ ?_⟩
  contrapose! hc
  exact le_sub_of_add_le (add_of_omega0_opow_le hc (opow_log_le_self ω h)).le

/-- The main characterization theorem for additive principal ordinals. -/
theorem isAddPrincipal_iff_zero_or_omega0_opow :
    IsAddPrincipal o ↔ o = 0 ∨ o ∈ Set.range (ω ^ · : Ordinal → Ordinal) := by
  constructor
  · rw [or_iff_not_imp_left]
    refine fun H ho ↦ ⟨log ω o, (opow_log_le_self ω ho).eq_of_not_lt ?_⟩
    obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 o)
    exact fun h ↦ hn.not_gt <| H.mul_natCast_lt h n
  · rintro (rfl | ⟨a, rfl⟩)
    exacts [.zero, .omega0_opow a]

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_iff_zero_or_omega0_opow := isAddPrincipal_iff_zero_or_omega0_opow

protected theorem IsAddPrincipal.opow {a} (ha : IsAddPrincipal a) (b : Ordinal) :
    IsAddPrincipal (a ^ b) := by
  rcases isAddPrincipal_iff_zero_or_omega0_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · by_cases hb : b = 0 <;> simp [hb]
  · rw [← opow_mul]
    exact .omega0_opow _

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_opow_of_isPrincipal_add := IsAddPrincipal.opow

protected theorem IsAddPrincipal.mul (a : Ordinal) {b : Ordinal} (hb₁ : b ≠ 1)
    (hb : IsAddPrincipal b) : IsAddPrincipal (a * b) := by
  rcases eq_zero_or_pos a with (rfl | _)
  · simp
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · simp
    · rw [← one_le_iff_pos, hb₁.ge_iff_gt] at hb₁'
      intro c d hc hd
      rw [lt_mul_iff_of_isSuccLimit (hb.isSuccLimit hb₁')] at *
      rcases hc with ⟨x, hx, hx'⟩
      rcases hd with ⟨y, hy, hy'⟩
      use x + y, hb hx hy
      rw [mul_add]
      exact Left.add_lt_add hx' hy'

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_mul_of_isPrincipal_add := IsAddPrincipal.mul

/-! ### Multiplicative principal ordinals -/

/-- An ordinal `o` is said to be multiplicative principal when
`a < o` and `b < o` imply `a * b < o`.

Note that under this definition, `0`, `1` and `2` are considered multiplicative principal. Every
other multiplicative principal ordinal is of the form `ω ^ ω ^ x`, see
`isMulPrincipal_iff_le_two_or_omega0_opow_opow`. -/
abbrev IsMulPrincipal : Ordinal → Prop := IsPrincipal (· * ·)

theorem IsMulPrincipal.one : IsMulPrincipal 1 := by simp

@[deprecated (since := "2026-11-12")]
alias isPrincipal_mul_one := IsMulPrincipal.one

@[simp]
theorem IsMulPrincipal.two : IsMulPrincipal 2 := by
  intro a b ha hb
  rw [lt_two_iff] at *
  simpa using mul_le_mul' ha hb

@[deprecated (since := "2026-11-12")]
alias isPrincipal_mul_two := IsMulPrincipal.two

theorem IsMulPrincipal.of_le_two (ho : o ≤ 2) : IsMulPrincipal o := by
  obtain rfl | rfl | rfl := le_two_iff.1 ho
  exacts [.zero, .one, .two]

@[deprecated (since := "2026-11-12")]
alias isPrincipal_mul_of_le_two := IsMulPrincipal.of_le_two

theorem IsMulPrincipal.isAddPrincipal (ho : IsMulPrincipal o) (ho₂ : o ≠ 2) : IsAddPrincipal o := by
  rcases lt_or_gt_of_ne ho₂ with ho₁ | ho₂
  · exact .of_le_one <| lt_two_iff.mp ho₁
  · simp_rw [isAddPrincipal_iff_add_self_lt, ← Ordinal.mul_two]
    exact fun a ha ↦ ho ha ho₂

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_of_isPrincipal_mul := IsMulPrincipal.isAddPrincipal

theorem IsMulPrincipal.isSuccLimit (ho₂ : 2 < o) (ho : IsMulPrincipal o) : IsSuccLimit o :=
  (ho.isAddPrincipal ho₂.ne').isSuccLimit (one_lt_two.trans ho₂)

@[deprecated (since := "2026-11-12")]
alias isSuccLimit_of_isPrincipal_mul := IsMulPrincipal.isSuccLimit

theorem isMulPrincipal_iff_mul_left_eq : IsMulPrincipal o ↔ ∀ a, 0 < a → a < o → a * o = o := by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases le_or_gt o 2 with ho | ho
    · convert one_mul o
      apply le_antisymm
      · rw [← lt_add_one_iff, one_add_one_eq_two]
        exact hao.trans_le ho
      · rwa [one_le_iff_pos]
    · exact op_eq_self_of_isPrincipal hao (isNormal_mul_right ha₀) h (h.isSuccLimit ho)
  · rcases eq_or_ne a 0 with (rfl | ha)
    · dsimp only; rwa [zero_mul]
    rw [← pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (isNormal_mul_right ha).strictMono hbo

@[deprecated (since := "2026-11-12")]
alias isPrincipal_mul_iff_mul_left_eq := isMulPrincipal_iff_mul_left_eq

theorem IsMulPrincipal.omega0 : IsMulPrincipal ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply natCast_lt_omega0

@[deprecated (since := "2026-11-12")]
alias isPrincipal_mul_omega0 := IsMulPrincipal.omega0

theorem mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω :=
  isMulPrincipal_iff_mul_left_eq.1 .omega0 a a0 ha

theorem natCast_mul_omega0 {n : ℕ} (hn : 0 < n) : n * ω = ω :=
  mul_omega0 (mod_cast hn) (natCast_lt_omega0 n)

@[simp]
theorem ofNat_mul_omega0 (n : ℕ) [n.AtLeastTwo] : ofNat(n) * ω = ω :=
  natCast_mul_omega0 (NeZero.pos _)

-- TODO: this should generalize from `ω` to a multiplicative principal ordinal.
theorem mul_lt_omega0_opow (ha : a < ω ^ c) (hb : b < ω) : a * b < ω ^ c := by
  rcases zero_or_succ_or_isSuccLimit c with (rfl | ⟨c, rfl⟩ | l)
  · simp_all
  · rw [succ_eq_add_one, opow_add_one] at ha
    obtain ⟨n, hn, an⟩ :=
      ((isNormal_mul_right <| opow_pos _ omega0_pos).lt_iff_exists_lt isSuccLimit_omega0).1 ha
    grw [an, succ_eq_add_one, opow_add_one, mul_assoc]
    gcongr
    exacts [opow_pos _ omega0_pos, IsMulPrincipal.omega0 hn hb]
  · rcases ((isNormal_opow one_lt_omega0).lt_iff_exists_lt l).1 ha with ⟨x, hx, ax⟩
    refine (mul_le_mul' (le_of_lt ax) (le_of_lt hb)).trans_lt ?_
    rw [← opow_add_one, opow_lt_opow_iff_right one_lt_omega0]
    exact l.succ_lt hx

-- TODO: it might be easier to prove this as a corollary of the theorem below.
theorem mul_omega0_opow_opow (a0 : 0 < a) (h : a < ω ^ ω ^ b) : a * ω ^ ω ^ b = ω ^ ω ^ b := by
  obtain rfl | b0 := eq_or_ne b 0
  · rw [opow_zero, opow_one] at h ⊢
    exact mul_omega0 a0 h
  · apply le_antisymm
    · obtain ⟨x, xb, ax⟩ :=
        (lt_opow_of_isSuccLimit omega0_ne_zero (isSuccLimit_opow_left isSuccLimit_omega0 b0)).1 h
      grw [ax, ← opow_add, add_omega0_opow xb]
    · conv_lhs => rw [← one_mul (ω ^ _)]
      grw [one_le_iff_pos.2 a0]

theorem IsMulPrincipal.omega0_opow_opow (o : Ordinal) : IsMulPrincipal (ω ^ ω ^ o) :=
  isMulPrincipal_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

@[deprecated (since := "2026-11-12")]
alias isPrincipal_mul_omega0_opow_opow := IsMulPrincipal.omega0_opow_opow

theorem IsAddPrincipal.of_isMulPrincipal_opow (hb : 1 < b) (ho : IsMulPrincipal (b ^ o)) :
    IsAddPrincipal o := by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

@[deprecated (since := "2026-11-12")]
alias isPrincipal_add_of_isPrincipal_mul_opow := IsAddPrincipal.of_isMulPrincipal_opow

/-- The main characterization theorem for multiplicative principal ordinals. -/
theorem isMulPrincipal_iff_le_two_or_omega0_opow_opow :
    IsMulPrincipal o ↔ o ≤ 2 ∨ o ∈ Set.range (ω ^ ω ^ · : Ordinal → Ordinal) := by
  refine ⟨fun ho => ?_, ?_⟩
  · rw [or_iff_not_imp_left, not_le]
    intro ho₂
    rcases isAddPrincipal_iff_zero_or_omega0_opow.1
      (ho.isAddPrincipal ho₂.ne') with (rfl | ⟨a, rfl⟩)
    · exact (not_lt_zero ho₂).elim
    · rcases isAddPrincipal_iff_zero_or_omega0_opow.1
        (.of_isMulPrincipal_opow one_lt_omega0 ho) with (rfl | ⟨b, rfl⟩)
      · simp at ho₂
      · exact ⟨b, rfl⟩
  · rintro (ho₂ | ⟨a, rfl⟩)
    · exact .of_le_two ho₂
    · exact .omega0_opow_opow a

@[deprecated (since := "2026-11-12")]
alias isPrincipal_mul_iff_le_two_or_omega0_opow_opow :=
  isMulPrincipal_iff_le_two_or_omega0_opow_opow

theorem mul_omega0_dvd (a0 : 0 < a) (ha : a < ω) : ∀ {b}, ω ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by rw [← mul_assoc, mul_omega0 a0 ha]

theorem IsMulPrincipal.mul_eq_opow_log_add_one (ha : a ≠ 0) (hb : IsMulPrincipal b) (hb₂ : 2 < b) :
    a * b = b ^ (log b a + 1) := by
  apply le_antisymm
  · have hbl := hb.isSuccLimit hb₂
    rw [(isNormal_mul_right (pos_iff_ne_zero.2 ha)).apply_of_isSuccLimit hbl,
      Ordinal.iSup_le_iff]
    intro ⟨c, hcb⟩
    have hb₁ : 1 < b := one_lt_two.trans hb₂
    have hbo₀ : b ^ log b a ≠ 0 := pos_iff_ne_zero.1 (opow_pos _ hb₂.pos)
    apply (mul_le_mul_left (le_of_lt (lt_mul_succ_div a hbo₀)) c).trans
    rw [mul_assoc, opow_add_one]
    gcongr
    refine (hb (hbl.add_one_lt ?_) hcb).le
    rw [← lt_mul_iff_div_lt hbo₀, ← opow_add_one]
    simpa using lt_opow_succ_log_self hb₁ _
  · grw [opow_add_one, opow_log_le_self b ha]

@[deprecated (since := "2026-11-12")]
alias mul_eq_opow_log_succ := IsMulPrincipal.mul_eq_opow_log_add_one

/-! ### Exponential principal ordinals -/

/-- An ordinal `o` is said to be exponentially principal when
`a < o` and `b < o` imply `a ^ b < o`.

Note that under this definition, `0`, `2`, and `ω` are considered exponentially principal. Every
other exponentially principal ordinal is an epsilon number, see
`isOpowPrincipal_iff_zero_or_two_or_omega0_or_epsilon`. -/
abbrev IsOpowPrincipal : Ordinal → Prop := IsPrincipal (· ^ ·)

theorem not_isOpowPrincipal_one : ¬ IsOpowPrincipal 1 := by simp

@[simp]
theorem IsOpowPrincipal.two : IsOpowPrincipal 2 := by
  intro a b ha _
  simpa using opow_le_opow_left b (lt_two_iff.1 ha)

@[deprecated (since := "2026-11-12")]
alias isPrincipal_opow_two := IsOpowPrincipal.two

theorem IsOpowPrincipal.isMulPrincipal (ho : IsOpowPrincipal o) : IsMulPrincipal o := by
  rcases le_or_gt o 2 with ho₂ | ho₂
  · exact .of_le_two ho₂
  · refine fun a b ha hb ↦ mul_le_mul' (le_max_left a b) (le_max_right a b) |>.trans_lt ?_
    simpa [← one_add_one_eq_two] using ho (max_lt ha hb) ho₂

@[deprecated (since := "2026-11-12")]
alias IsPrincipal.mul_of_opow := IsOpowPrincipal.isMulPrincipal

theorem IsOpowPrincipal.isSuccLimit (ho₂ : 2 < o) (ho : IsOpowPrincipal o) : IsSuccLimit o :=
  ho.isMulPrincipal.isSuccLimit ho₂

@[deprecated (since := "2026-11-12")]
alias isSuccLimit_of_isPrincipal_opow := IsOpowPrincipal.isSuccLimit

theorem omega0_lt_of_omega0_opow_eq_self (ho : ω ^ o = o) : ω < o := by
  rcases le_or_gt o 1 with ho₁ | ho₁
  · rcases le_one_iff.1 ho₁ with rfl | rfl <;> simp [one_lt_omega0.ne'] at ho
  · grw [left_lt_opow one_lt_omega0 ho₁, ho]

theorem omega0_lt_and_isOpowPrincipal_iff : ω < o ∧ IsOpowPrincipal o ↔ ω ^ o = o := by
  refine ⟨fun ⟨hoω, ho⟩ ↦ ?_, fun ho ↦ ?_⟩
  · apply op_eq_self_of_isPrincipal hoω (isNormal_opow one_lt_omega0) ho
    exact ho.isSuccLimit ((natCast_lt_omega0 2).trans hoω)
  · have hoω : ω < o := omega0_lt_of_omega0_opow_eq_self ho
    refine ⟨hoω, fun a b ha hb ↦ ?_⟩
    have hom : IsMulPrincipal o := by simpa [ho] using IsMulPrincipal.omega0_opow_opow o
    have hol := hom.isSuccLimit ((natCast_lt_omega0 2).trans hoω)
    have ⟨c, hc, hac⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero hol).1 (ha.trans_eq ho.symm)
    refine (opow_le_opow_left b hac.le).trans_lt ?_
    grw [← opow_mul, ← ho, opow_lt_opow_iff_right one_lt_omega0, ← hom hc hb]

@[deprecated (since := "2026-11-12")]
alias omega0_lt_and_isPrincipal_opow_iff := omega0_lt_and_isOpowPrincipal_iff

/-- Above `ω`, closure under exponentiation is equivalent to being a fixed point of `ω ^ ·`. -/
theorem isOpowPrincipal_iff_omega0_opow_eq_self (hoω : ω < o) :
    IsOpowPrincipal o ↔ ω ^ o = o := by
  simp [← omega0_lt_and_isOpowPrincipal_iff, hoω]

@[deprecated (since := "2026-11-12")]
alias isPrincipal_opow_iff_omega0_opow_eq_self := isOpowPrincipal_iff_omega0_opow_eq_self

theorem IsOpowPrincipal.omega0 : IsOpowPrincipal ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by simp [← natCast_pow]

@[deprecated (since := "2026-11-12")]
alias isPrincipal_opow_omega0 := IsOpowPrincipal.omega0

/-- The exponential principal ordinals are `0`, `2`, `ω`, and the fixed points of `ω ^ ·`. -/
theorem isOpowPrincipal_iff_zero_or_two_or_omega0_or_omega0_opow_eq :
    IsOpowPrincipal o ↔ o = 0 ∨ o = 2 ∨ o = ω ∨ ω ^ o = o := by
  refine ⟨fun ho ↦ ?_, ?_⟩
  · simp_rw [or_iff_not_imp_left]
    intro ho₀ ho₂ hoω
    refine omega0_lt_and_isOpowPrincipal_iff.1 ⟨lt_of_le_of_ne' ?_ hoω, ho⟩
    refine omega0_le_of_isSuccLimit (ho.isSuccLimit ?_)
    by_contra!
    simp_all [le_two_iff]
  · rintro (rfl | rfl | rfl | ho)
    exacts [.zero, .two, .omega0, (omega0_lt_and_isOpowPrincipal_iff.2 ho).2]

@[deprecated (since := "2026-11-12")]
alias isPrincipal_opow_iff_zero_or_two_or_omega0_or_omega0_opow_eq :=
  isOpowPrincipal_iff_zero_or_two_or_omega0_or_omega0_opow_eq

theorem opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω :=
  ((opow_le_of_isSuccLimit (one_le_iff_ne_zero.1 <| le_of_lt a1) isSuccLimit_omega0).2 fun _ hb =>
      (IsOpowPrincipal.omega0 h hb).le).antisymm
  (right_le_opow _ a1)

theorem natCast_opow_omega0 {n : ℕ} (hn : 1 < n) : n ^ ω = ω :=
  opow_omega0 (mod_cast hn) (natCast_lt_omega0 n)

@[simp]
theorem ofNat_opow_omega0 (n : ℕ) [n.AtLeastTwo] : ofNat(n) ^ ω = ω :=
  natCast_opow_omega0 Nat.AtLeastTwo.one_lt

end Ordinal
