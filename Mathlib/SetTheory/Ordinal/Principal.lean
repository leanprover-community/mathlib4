/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Principal ordinals

If `op` is a binary operation on ordinals, we say that an ordinal `o` is `op`-principal or
`op`-indecomposable when the set `Iio o` is closed under the operation `op`. Most commonly, one
talks of additive and multiplicative principal ordinals.

Additive principal ordinals were originally called "gamma numbers" by Cantor, but this term now more
commonly refers to the values given by `Ordinal.gamma`. Likewise, multiplicative principal ordinals
are sometimes known as "delta numbers". Exponential principal ordinals are (barring edge cases)
equivalent to the epsilon numbers given by `Ordinal.epsilon`.

## Main definitions and results

* `IsPrincipal`: A principal (or indecomposable) ordinal under some binary operation. We include `0`
  and other typically excluded edge cases for simplicity.
* `not_bddAbove_setOf_isPrincipal`: Principal ordinals (under any operation) are unbounded.
* `principal_add_iff_zero_or_omega0_opow`: The additive principal ordinals are
  `0` and the ordinal powers of `ω`.
* `principal_mul_iff_le_two_or_omega0_opow_opow`: The multiplicative principal ordinals are
  `0`, `1`, `2`, and the ordinals `ω ^ ω ^ x`.

## TODO

* Prove that the exponential principal ordinals are `0`, `1`, `2`, `ω`, or `ε_ x`.

## Tags

additively indecomposable, multiplicatively indecomposable
-/

@[expose] public section

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
def IsPrincipal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

@[deprecated (since := "2026-03-17")]
alias Principal := IsPrincipal

theorem isPrincipal_swap_iff : IsPrincipal (Function.swap op) o ↔ IsPrincipal op o := by
  constructor <;> exact fun h a b ha hb => h hb ha

@[deprecated (since := "2026-03-17")]
alias principal_swap_iff := isPrincipal_swap_iff

theorem not_isPrincipal_iff : ¬ IsPrincipal op o ↔ ∃ a < o, ∃ b < o, o ≤ op a b := by
  simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff := not_isPrincipal_iff

theorem isPrincipal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    IsPrincipal op o ↔ ∀ a < o, op a a < o := by
  use fun h a ha => h ha ha
  intro H a b ha hb
  obtain hab | hba := le_or_gt a b
  · exact (h₂ b hab).trans_lt <| H b hb
  · exact (h₁ a hba.le).trans_lt <| H a ha

@[deprecated (since := "2026-03-17")]
alias principal_iff_of_monotone := isPrincipal_iff_of_monotone

theorem not_isPrincipal_iff_of_monotone
    (h₁ : ∀ a, Monotone (op a)) (h₂ : ∀ a, Monotone (Function.swap op a)) :
    ¬ IsPrincipal op o ↔ ∃ a < o, o ≤ op a a := by
  simp [isPrincipal_iff_of_monotone h₁ h₂]

@[deprecated (since := "2026-03-17")]
alias not_principal_iff_of_monotone := not_isPrincipal_iff_of_monotone

@[simp] lemma isPrincipal_zero : IsPrincipal op 0 := by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_zero := isPrincipal_zero

@[simp] theorem isPrincipal_one_iff : IsPrincipal op 1 ↔ op 0 0 = 0 := by simp [IsPrincipal]

@[deprecated (since := "2026-03-17")]
alias principal_one_iff := isPrincipal_one_iff

theorem IsPrincipal.iterate_lt (hao : a < o) (ho : IsPrincipal op o) (n : ℕ) :
    (op a)^[n] a < o := by
  induction n with
  | zero => rwa [Function.iterate_zero]
  | succ n hn =>
    rw [Function.iterate_succ']
    exact ho hao hn

@[deprecated (since := "2026-03-17")]
alias Principal.iterate_lt := IsPrincipal.iterate_lt

theorem op_eq_self_of_isPrincipal (hao : a < o) (H : IsNormal (op a))
    (ho : IsPrincipal op o) (ho' : IsSuccLimit o) : op a o = o := by
  apply H.strictMono.le_apply.antisymm'
  rw [H.apply_of_isSuccLimit ho', Ordinal.iSup_le_iff]
  exact fun ⟨b, hbo⟩ ↦ (ho hao hbo).le

@[deprecated (since := "2026-03-17")]
alias op_eq_self_of_principal := op_eq_self_of_isPrincipal

theorem nfp_le_of_isPrincipal (hao : a < o) (ho : IsPrincipal op o) : nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

@[deprecated (since := "2026-03-17")]
alias nfp_le_of_principal := nfp_le_of_isPrincipal

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

@[deprecated (since := "2026-03-17")]
protected alias Principal.sSup := IsPrincipal.sSup

protected theorem IsPrincipal.iSup {ι} {f : ι → Ordinal} (H : ∀ i, IsPrincipal op (f i)) :
    IsPrincipal op (⨆ i, f i) := IsPrincipal.sSup (by simpa)

@[deprecated (since := "2026-03-17")]
protected alias Principal.iSup := IsPrincipal.iSup

end Arbitrary

/-- We give an explicit construction for a principal ordinal larger or equal than `o`. -/
private theorem isPrincipal_nfp_iSup (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    IsPrincipal op (nfp (fun x ↦ ⨆ y : Set.Iio x ×ˢ Set.Iio x, succ (op y.1.1 y.1.2)) o) := by
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
theorem not_bddAbove_setOf_isPrincipal (op : Ordinal → Ordinal → Ordinal) :
    ¬ BddAbove { o | IsPrincipal op o } := by
  rintro ⟨a, ha⟩
  exact ((le_nfp _ _).trans (ha (isPrincipal_nfp_iSup op (succ a)))).not_gt (lt_succ a)

@[deprecated (since := "2026-03-17")]
alias not_bddAbove_principal := not_bddAbove_setOf_isPrincipal

/-! ### Additive principal ordinals -/

theorem isPrincipal_add_iff_add_self_lt : IsPrincipal (· + ·) a ↔ ∀ b < a, b + b < a :=
  isPrincipal_iff_of_monotone
    (fun x _ _ h ↦ add_le_add_right h x) (fun x _ _ h ↦ add_le_add_left h x)

theorem IsPrincipal.mul_natCast_lt (ho : IsPrincipal (· + ·) o) (ha : a < o) (n : ℕ) :
    a * n < o := by
  induction n with
  | zero => simpa using ha.pos
  | succ n h =>
    rw [Nat.cast_add_one, mul_add_one]
    exact ho h ha

theorem isPrincipal_add_one : IsPrincipal (· + ·) 1 := by simp

@[deprecated (since := "2026-03-17")]
alias principal_add_one := isPrincipal_add_one

theorem isPrincipal_add_of_le_one (ho : o ≤ 1) : IsPrincipal (· + ·) o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact isPrincipal_zero
  · exact isPrincipal_add_one

@[deprecated (since := "2026-03-17")]
alias principal_add_of_le_one := isPrincipal_add_of_le_one

theorem isSuccLimit_of_isPrincipal_add (ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) :
    IsSuccLimit o := by
  rw [isSuccLimit_iff, isSuccPrelimit_iff_succ_lt]
  exact ⟨ho₁.ne_bot, fun _ ha ↦ ho ha ho₁⟩

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_add := isSuccLimit_of_isPrincipal_add

theorem isPrincipal_add_iff_add_left_eq_self : IsPrincipal (· + ·) o ↔ ∀ a < o, a + o = o := by
  refine ⟨fun ho a hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases lt_or_ge 1 o with ho₁ | ho₁
    · exact op_eq_self_of_isPrincipal hao (isNormal_add_right a) ho
        (isSuccLimit_of_isPrincipal_add ho₁ ho)
    · cases le_one_iff.1 ho₁ <;> simp_all
  · rw [← h a hao]
    exact (isNormal_add_right a).strictMono hbo

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_left_eq_self := isPrincipal_add_iff_add_left_eq_self

theorem IsPrincipal.add_eq_right (ho : IsPrincipal (· + ·) o) (ha : a < o) : a + o = o :=
  isPrincipal_add_iff_add_left_eq_self.1 ho a ha

theorem IsPrincipal.add_eq_right_of_le (hb : IsPrincipal (· + ·) b)
    (hab : a < b) (hbc : b ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le hbc, ← add_assoc, hb.add_eq_right hab,
    Ordinal.add_sub_cancel_of_le hbc]

theorem exists_lt_add_of_not_isPrincipal_add (ha : ¬ IsPrincipal (· + ·) a) :
    ∃ b < a, ∃ c < a, b + c = a := by
  rw [not_isPrincipal_iff] at ha
  rcases ha with ⟨b, hb, c, hc, H⟩
  refine
    ⟨b, hb, _, lt_of_le_of_ne (sub_le_self a b) fun hab => ?_, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le, hab] at H
  exact H.not_gt hc

@[deprecated (since := "2026-03-17")]
alias exists_lt_add_of_not_principal_add := exists_lt_add_of_not_isPrincipal_add

theorem isPrincipal_add_iff_add_lt_ne_self : IsPrincipal (· + ·) a ↔ ∀ b < a, ∀ c < a, b + c ≠ a :=
  ⟨fun ha _ hb _ hc => (ha hb hc).ne, fun H => by
    by_contra ha
    rcases exists_lt_add_of_not_isPrincipal_add ha with ⟨b, hb, c, hc, rfl⟩
    exact (H b hb c hc).irrefl⟩

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_add_lt_ne_self := isPrincipal_add_iff_add_lt_ne_self

theorem isPrincipal_add_omega0 : IsPrincipal (· + ·) ω :=
  isPrincipal_add_iff_add_left_eq_self.2 fun _ => add_omega0

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0 := isPrincipal_add_omega0

-- `add_omega0` is proven in the Arithmetic file.

theorem add_of_omega0_le : a < ω → ω ≤ b → a + b = b :=
  isPrincipal_add_omega0.add_eq_right_of_le

theorem isPrincipal_add_omega0_opow (o : Ordinal) : IsPrincipal (· + ·) (ω ^ o) := by
  obtain rfl | ha' := eq_or_ne o 0
  · rw [opow_zero, isPrincipal_one_iff, add_zero]
  · rw [isPrincipal_add_iff_add_self_lt]
    intro a ha
    obtain ⟨c, hc, m, hm⟩ := (lt_omega0_opow ha').1 ha
    apply (add_lt_add_of_le_of_lt hm.le hm).trans_le
    rw [← mul_add, ← Nat.cast_add]
    exact (omega0_opow_mul_nat_lt hc _).le

@[deprecated (since := "2026-03-17")]
alias principal_add_omega0_opow := isPrincipal_add_omega0_opow

theorem add_omega0_opow (h : a < ω ^ b) : a + ω ^ b = ω ^ b :=
  (isPrincipal_add_omega0_opow b).add_eq_right h

theorem add_of_omega0_opow_le (h₁ : a < ω ^ b) (h₂ : ω ^ b ≤ c) : a + c = c :=
  (isPrincipal_add_omega0_opow b).add_eq_right_of_le h₁ h₂

@[deprecated (since := "2026-03-18")]
alias add_absorp := add_of_omega0_opow_le

/-- The main characterization theorem for additive principal ordinals. -/
theorem isPrincipal_add_iff_zero_or_omega0_opow :
    IsPrincipal (· + ·) o ↔ o = 0 ∨ o ∈ Set.range (ω ^ · : Ordinal → Ordinal) := by
  constructor
  · rw [or_iff_not_imp_left]
    refine fun H ho ↦ ⟨log ω o, (opow_log_le_self ω ho).eq_of_not_lt ?_⟩
    obtain ⟨n, hn⟩ := lt_omega0_opow_succ.1 (lt_opow_succ_log_self one_lt_omega0 o)
    exact fun h ↦ hn.not_gt <| H.mul_natCast_lt h n
  · rintro (rfl | ⟨a, rfl⟩)
    exacts [isPrincipal_zero, isPrincipal_add_omega0_opow a]

@[deprecated (since := "2026-03-17")]
alias principal_add_iff_zero_or_omega0_opow := isPrincipal_add_iff_zero_or_omega0_opow

theorem isPrincipal_add_opow_of_isPrincipal_add {a} (ha : IsPrincipal (· + ·) a) (b : Ordinal) :
    IsPrincipal (· + ·) (a ^ b) := by
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact isPrincipal_add_one
    · rwa [zero_opow hb]
  · rw [← opow_mul]
    exact isPrincipal_add_omega0_opow _

@[deprecated (since := "2026-03-17")]
alias principal_add_opow_of_principal_add := isPrincipal_add_opow_of_isPrincipal_add

theorem isPrincipal_add_mul_of_isPrincipal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : IsPrincipal (· + ·) b) : IsPrincipal (· + ·) (a * b) := by
  rcases eq_zero_or_pos a with (rfl | _)
  · rw [zero_mul]
    exact isPrincipal_zero
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact isPrincipal_zero
    · rw [← one_le_iff_pos] at hb₁'
      intro c d hc hd
      rw [lt_mul_iff_of_isSuccLimit
        (isSuccLimit_of_isPrincipal_add (lt_of_le_of_ne hb₁' hb₁.symm) hb)] at *
      rcases hc with ⟨x, hx, hx'⟩
      rcases hd with ⟨y, hy, hy'⟩
      use x + y, hb hx hy
      rw [mul_add]
      exact Left.add_lt_add hx' hy'

@[deprecated (since := "2026-03-17")]
alias principal_add_mul_of_principal_add := isPrincipal_add_mul_of_isPrincipal_add

/-! ### Multiplicative principal ordinals -/

theorem isPrincipal_mul_one : IsPrincipal (· * ·) 1 := by simp

@[deprecated (since := "2026-03-17")]
alias principal_mul_one := isPrincipal_mul_one

theorem isPrincipal_mul_two : IsPrincipal (· * ·) 2 := by
  intro a b ha hb
  rw [lt_two_iff] at *
  simpa using mul_le_mul' ha hb

@[deprecated (since := "2026-03-17")]
alias principal_mul_two := isPrincipal_mul_two

theorem isPrincipal_mul_of_le_two (ho : o ≤ 2) : IsPrincipal (· * ·) o := by
  obtain rfl | rfl | rfl := le_two_iff.1 ho
  exacts [isPrincipal_zero, isPrincipal_mul_one, isPrincipal_mul_two]

@[deprecated (since := "2026-03-17")]
alias principal_mul_of_le_two := isPrincipal_mul_of_le_two

theorem isPrincipal_add_of_isPrincipal_mul (ho : IsPrincipal (· * ·) o) (ho₂ : o ≠ 2) :
    IsPrincipal (· + ·) o := by
  rcases lt_or_gt_of_ne ho₂ with ho₁ | ho₂
  · exact isPrincipal_add_of_le_one <| lt_two_iff.mp ho₁
  · simp_rw [isPrincipal_add_iff_add_self_lt, ← Ordinal.mul_two]
    exact fun a ha ↦ ho ha ho₂

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul := isPrincipal_add_of_isPrincipal_mul

theorem isSuccLimit_of_isPrincipal_mul (ho₂ : 2 < o) (ho : IsPrincipal (· * ·) o) : IsSuccLimit o :=
  isSuccLimit_of_isPrincipal_add (one_lt_two.trans ho₂)
    (isPrincipal_add_of_isPrincipal_mul ho (ne_of_gt ho₂))

@[deprecated (since := "2026-03-17")]
alias isSuccLimit_of_principal_mul := isSuccLimit_of_isPrincipal_mul

theorem isPrincipal_mul_iff_mul_left_eq :
    IsPrincipal (· * ·) o ↔ ∀ a, 0 < a → a < o → a * o = o := by
  refine ⟨fun h a ha₀ hao => ?_, fun h a b hao hbo => ?_⟩
  · rcases le_or_gt o 2 with ho | ho
    · convert one_mul o
      apply le_antisymm
      · rw [← lt_add_one_iff, one_add_one_eq_two]
        exact hao.trans_le ho
      · rwa [one_le_iff_pos]
    · exact op_eq_self_of_isPrincipal hao (isNormal_mul_right ha₀) h
        (isSuccLimit_of_isPrincipal_mul ho h)
  · rcases eq_or_ne a 0 with (rfl | ha)
    · dsimp only; rwa [zero_mul]
    rw [← pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (isNormal_mul_right ha).strictMono hbo

@[deprecated (since := "2026-03-17")]
alias principal_mul_iff_mul_left_eq := isPrincipal_mul_iff_mul_left_eq

theorem isPrincipal_mul_omega0 : IsPrincipal (· * ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    dsimp only; rw [← natCast_mul]
    apply natCast_lt_omega0

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0 := isPrincipal_mul_omega0

theorem mul_omega0 (a0 : 0 < a) (ha : a < ω) : a * ω = ω :=
  isPrincipal_mul_iff_mul_left_eq.1 isPrincipal_mul_omega0 a a0 ha

theorem natCast_mul_omega0 {n : ℕ} (hn : 0 < n) : n * ω = ω :=
  mul_omega0 (mod_cast hn) (natCast_lt_omega0 n)

theorem mul_lt_omega0_opow (c0 : 0 < c) (ha : a < ω ^ c) (hb : b < ω) : a * b < ω ^ c := by
  rcases zero_or_succ_or_isSuccLimit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irrefl _).elim c0
  · rw [opow_succ] at ha
    obtain ⟨n, hn, an⟩ :=
      ((isNormal_mul_right <| opow_pos _ omega0_pos).lt_iff_exists_lt isSuccLimit_omega0).1 ha
    grw [an, opow_succ, mul_assoc]
    gcongr
    exacts [opow_pos _ omega0_pos, isPrincipal_mul_omega0 hn hb]
  · rcases ((isNormal_opow one_lt_omega0).lt_iff_exists_lt l).1 ha with ⟨x, hx, ax⟩
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
      grw [ax, ← opow_add, add_omega0_opow xb]
    · conv_lhs => rw [← one_mul (ω ^ _)]
      grw [one_le_iff_pos.2 a0]

theorem isPrincipal_mul_omega0_opow_opow (o : Ordinal) : IsPrincipal (· * ·) (ω ^ ω ^ o) :=
  isPrincipal_mul_iff_mul_left_eq.2 fun _ => mul_omega0_opow_opow

@[deprecated (since := "2026-03-17")]
alias principal_mul_omega0_opow_opow := isPrincipal_mul_omega0_opow_opow

theorem isPrincipal_add_of_isPrincipal_mul_opow (hb : 1 < b) (ho : IsPrincipal (· * ·) (b ^ o)) :
    IsPrincipal (· + ·) o := by
  intro x y hx hy
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  dsimp only at *
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

@[deprecated (since := "2026-03-17")]
alias principal_add_of_principal_mul_opow := isPrincipal_add_of_isPrincipal_mul_opow

/-- The main characterization theorem for multiplicative principal ordinals. -/
theorem isPrincipal_mul_iff_le_two_or_omega0_opow_opow :
    IsPrincipal (· * ·) o ↔ o ≤ 2 ∨ o ∈ Set.range (ω ^ ω ^ · : Ordinal → Ordinal) := by
  refine ⟨fun ho => ?_, ?_⟩
  · rcases le_or_gt o 2 with ho₂ | ho₂
    · exact Or.inl ho₂
    · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
        (isPrincipal_add_of_isPrincipal_mul ho ho₂.ne') with (rfl | ⟨a, rfl⟩)
      · exact (not_lt_zero ho₂).elim
      · rcases isPrincipal_add_iff_zero_or_omega0_opow.1
          (isPrincipal_add_of_isPrincipal_mul_opow one_lt_omega0 ho) with (rfl | ⟨b, rfl⟩)
        · simp
        · exact Or.inr ⟨b, rfl⟩
  · rintro (ho₂ | ⟨a, rfl⟩)
    · exact isPrincipal_mul_of_le_two ho₂
    · exact isPrincipal_mul_omega0_opow_opow a

@[deprecated (since := "2026-03-17")]
alias principal_mul_iff_le_two_or_omega0_opow_opow := isPrincipal_mul_iff_le_two_or_omega0_opow_opow

theorem mul_omega0_dvd (a0 : 0 < a) (ha : a < ω) : ∀ {b}, ω ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by rw [← mul_assoc, mul_omega0 a0 ha]

theorem mul_eq_opow_log_succ (ha : a ≠ 0) (hb : IsPrincipal (· * ·) b) (hb₂ : 2 < b) :
    a * b = b ^ succ (log b a) := by
  apply le_antisymm
  · have hbl := isSuccLimit_of_isPrincipal_mul hb₂ hb
    rw [(isNormal_mul_right (pos_iff_ne_zero.2 ha)).apply_of_isSuccLimit hbl,
      Ordinal.iSup_le_iff]
    intro ⟨c, hcb⟩
    have hb₁ : 1 < b := one_lt_two.trans hb₂
    have hbo₀ : b ^ log b a ≠ 0 := pos_iff_ne_zero.1 (opow_pos _ (zero_lt_one.trans hb₁))
    apply (mul_le_mul_left (le_of_lt (lt_mul_succ_div a hbo₀)) c).trans
    rw [mul_assoc, opow_succ]
    gcongr
    refine (hb (hbl.succ_lt ?_) hcb).le
    rw [← lt_mul_iff_div_lt hbo₀, ← opow_succ]
    exact lt_opow_succ_log_self hb₁ _
  · grw [opow_succ, opow_log_le_self b ha]

/-! #### Exponential principal ordinals -/

theorem isPrincipal_opow_omega0 : IsPrincipal (· ^ ·) ω := fun a b ha hb =>
  match a, b, lt_omega0.1 ha, lt_omega0.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by simp [← natCast_pow]

@[deprecated (since := "2026-03-17")]
alias principal_opow_omega0 := isPrincipal_opow_omega0

theorem opow_omega0 (a1 : 1 < a) (h : a < ω) : a ^ ω = ω :=
  ((opow_le_of_isSuccLimit (one_le_iff_ne_zero.1 <| le_of_lt a1) isSuccLimit_omega0).2 fun _ hb =>
      (isPrincipal_opow_omega0 h hb).le).antisymm
  (right_le_opow _ a1)

theorem natCast_opow_omega0 {n : ℕ} (hn : 1 < n) : n ^ ω = ω :=
  opow_omega0 (mod_cast hn) (natCast_lt_omega0 n)

end Ordinal
