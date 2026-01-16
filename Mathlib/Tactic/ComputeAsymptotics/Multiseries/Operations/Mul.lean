/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Add

/-!
# Multiplication for multiseries

-/

set_option linter.flexible false
set_option linter.style.longLine false

@[expose] public section

namespace ComputeAsymptotics

namespace PreMS

mutual
  noncomputable def SeqMS.mul {basis_hd : ℝ → ℝ} {basis_tl : Basis}
      (X Y : SeqMS basis_hd basis_tl) : SeqMS basis_hd basis_tl :=
    match X.destruct with
    | none => .nil
    | some (X_exp, X_coef, X_tl) =>
      let T := SeqMS basis_hd basis_tl
      let g : T → Option (ℝ × PreMS basis_tl × SeqMS basis_hd basis_tl × T) := fun Y =>
        match Y.destruct with
        | none => none
        | some (Y_exp, Y_coef, Y_tl) =>
          some (X_exp + Y_exp, X_coef.mul Y_coef, SeqMS.mulMonomial X_tl Y_coef Y_exp, Y_tl)
      SeqMS.gcorec g SeqMS.add Y

  noncomputable def SeqMS.mulMonomial {basis_hd} {basis_tl} (B : SeqMS basis_hd basis_tl)
      (M_coef : PreMS basis_tl) (M_exp : ℝ) : SeqMS basis_hd basis_tl :=
    B.map (fun exp => exp + M_exp) (fun coef => coef.mul M_coef)

  /-- Multiplication for multiseries. -/
  noncomputable def mul {basis : Basis} (X Y : PreMS basis) : PreMS basis :=
    match basis with
    | [] => ofReal (X.toReal * Y.toReal)
    | List.cons basis_hd basis_tl =>
      mk (SeqMS.mul X.seq Y.seq) (X.toFun * Y.toFun)

  /-- Multiplication by monomial, i.e. `M_coef * basis_hd ^ M_exp * B`. -/
  noncomputable def mulMonomial {basis_hd} {basis_tl} (B : PreMS (basis_hd :: basis_tl))
      (M_coef : PreMS basis_tl) (M_exp : ℝ) : PreMS (basis_hd :: basis_tl) :=
    mk (SeqMS.mulMonomial B.seq M_coef M_exp) (B.toFun * basis_hd ^ M_exp * M_coef.toFun)

end

--theorems
open Filter Asymptotics

@[simp]
theorem mul_toFun {basis : Basis} {X Y : PreMS basis} : (X.mul Y).toFun = X.toFun * Y.toFun := by
  cases basis with
  | nil =>
    simp [mul]
    rfl
  | cons basis_hd basis_tl =>
    simp [mul]

@[simp]
theorem mulMonomial_toFun {basis_hd basis_tl} {B : PreMS (basis_hd :: basis_tl)}
    {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    (mulMonomial B M_coef M_exp).toFun = B.toFun * basis_hd ^ M_exp * M_coef.toFun := by
  simp [mulMonomial]

@[simp]
theorem mul_seq {basis_hd basis_tl} {X Y : PreMS (basis_hd :: basis_tl)} :
    (X.mul Y).seq = X.seq.mul Y.seq := by
  simp [mul]

@[simp]
theorem mulMonomial_seq {basis_hd basis_tl} {B : PreMS (basis_hd :: basis_tl)}
    {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    (mulMonomial B M_coef M_exp).seq = B.seq.mulMonomial M_coef M_exp := by
  simp [mulMonomial]

@[simp]
theorem SeqMS.nil_mul {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} :
    mul nil ms = nil := by
  simp [mul]

@[simp]
theorem SeqMS.mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} :
    mul ms nil = nil := by
  simp only [mul]
  cases ms <;> simp only [destruct_nil, destruct_cons]
  rw [gcorec_nil]
  simp

@[simp]
theorem SeqMS.mulMonomial_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {M_exp : ℝ}
    {M_coef : PreMS basis_tl} :
    mulMonomial (basis_hd := basis_hd) nil M_coef M_exp = nil := by
  simp [mulMonomial]

@[simp]
theorem SeqMS.mulMonomial_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp M_exp : ℝ}
    {X_coef M_coef : PreMS basis_tl} {X_tl : SeqMS basis_hd basis_tl} :
    (cons X_exp X_coef X_tl).mulMonomial M_coef M_exp =
    cons (X_exp + M_exp) (X_coef.mul M_coef) (SeqMS.mulMonomial X_tl M_coef M_exp) := by
  simp [SeqMS.mulMonomial]

@[simp]
theorem SeqMS.mulMonomial_leadingExp {basis_hd} {basis_tl} {B : SeqMS basis_hd basis_tl}
    {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    (mulMonomial B M_coef M_exp).leadingExp = B.leadingExp + M_exp := by
  cases B <;> simp

-- theorem SeqMS.mul_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
--     {tl X Y : SeqMS basis_hd basis_tl} (h : X.mul Y = cons exp coef tl) :
--     ∃ X_exp X_coef X_tl Y_exp Y_coef Y_tl, X = cons X_exp X_coef X_tl ∧
--       Y = cons Y_exp Y_coef Y_tl := by
--   cases X with
--   | nil => simp at h
--   | cons X_exp X_coef X_tl =>
--   cases Y with
--   | nil => simp at h
--   | cons Y_exp Y_coef Y_tl => use X_exp, X_coef, X_tl, Y_exp, Y_coef, Y_tl

@[simp]
theorem SeqMS.mul_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp Y_exp : ℝ}
    {X_coef Y_coef : PreMS basis_tl} {X_tl Y_tl : SeqMS basis_hd basis_tl} :
    (cons X_exp X_coef X_tl).mul (cons Y_exp Y_coef Y_tl) =
    cons (X_exp + Y_exp) (X_coef.mul Y_coef) ((mulMonomial X_tl Y_coef Y_exp) +
      ((cons X_exp X_coef X_tl).mul Y_tl)) := by
  simp only [mul, destruct_cons]
  rw [gcorec_some, add_def]
  simp

@[simp]
theorem SeqMS.mul_leadingExp {basis_hd} {basis_tl} {X Y : SeqMS basis_hd basis_tl} :
    (mul X Y).leadingExp = X.leadingExp + Y.leadingExp := by
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl => simp

-- Note: the condition `X.WellOrdered` is necessary.
-- Counterexample: `X = [1, 2]`, `Y = [1]` (well-ordered).
-- Then `lhs = [1, 2]` while `rhs = [2, 1]`.
theorem SeqMS.mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_exp : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl X : SeqMS basis_hd basis_tl}
    (hX_wo : (cons Y_exp Y_coef Y_tl).WellOrdered) :
    X.mul (cons Y_exp Y_coef Y_tl) = (mulMonomial X Y_coef Y_exp) + X.mul Y_tl := by
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
    simp only [mul_cons_cons, mulMonomial_cons]
    rw [add_cons_left]
    simp
    obtain ⟨_, hX_comp, hX_tail_wo⟩ := WellOrdered_cons hX_wo
    cases Y_tl
    · simp
    · simp at hX_comp ⊢
      norm_cast
      linarith

theorem SeqMS.mul_eq_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X Y : SeqMS basis_hd basis_tl} (h : X.mul Y = nil) :
    X = nil ∨ Y = nil := by
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl =>
  simp at h

-- @[simp]
-- theorem mul_one' {basis : Basis} {ms : PreMS basis} : mul ms (one basis) = ms := by
--   cases basis with
--   | nil => simp [mul, one, const]
--   | cons basis_hd basis_tl =>
--     let motive (X Y : PreMS (basis_hd :: basis_tl)) : Prop :=
--       X = Y.mul (one _)
--     apply eq_of_bisim motive
--     · simp only [motive]
--     rintro X Y rfl
--     cases Y with
--     | nil => simp
--     | cons exp coef tl =>
--     simpa [one, const, motive, mul_cons (WellOrdered.cons_nil const_WellOrdered)] using mul_one'

mutual

@[simp]
theorem SeqMS.one_mul' {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} :
    SeqMS.mul SeqMS.one ms = ms := by
  let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
    X = SeqMS.mul SeqMS.one Y
  apply SeqMS.eq_of_bisim motive
  · simp only [motive]
  rintro A B rfl
  cases B with
  | nil => simp
  | cons exp coef tl =>
  simp [motive]
  simp [SeqMS.one, SeqMS.const]
  exact one_mul'

@[simp]
theorem one_mul' {basis : Basis} {ms : PreMS basis} :
    mul one ms = ms := by
  cases basis with
  | nil => simp [mul, one, const, ofReal, toReal]
  | cons basis_hd basis_tl =>
    simp [ms_eq_ms_iff_mk_eq_mk]
    rw [SeqMS.one_mul']

end

mutual
  theorem SeqMS.mulMonomial_mulConst_right {basis_hd : ℝ → ℝ} {basis_tl : Basis}
      {B : SeqMS basis_hd basis_tl} {M_coef : PreMS basis_tl} {M_exp c : ℝ} :
      B.mulMonomial (M_coef.mulConst c) M_exp = (B.mulMonomial M_coef M_exp).mulConst c := by
    let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (B : SeqMS basis_hd basis_tl),
        X = B.mulMonomial (M_coef.mulConst c) M_exp ∧
        Y = (B.mulMonomial M_coef M_exp).mulConst c
    apply SeqMS.eq_of_bisim motive
    · simp only [motive]
      use B
    · intro X Y ih
      simp only [motive] at ih ⊢
      obtain ⟨B, hX, hY⟩ := ih
      subst hX hY
      cases B with
      | nil => simp
      | cons B_exp B_coef B_tl =>
      right
      simp only [↓existsAndEq, SeqMS.mulMonomial_cons, SeqMS.cons_eq_cons, SeqMS.mulConst_cons, and_self, and_true,
        true_and]
      use B_tl
      simp [mul_mulConst_right (basis := basis_tl)]

  theorem SeqMS.mul_mulConst_right {basis_hd basis_tl} {X Y : SeqMS basis_hd basis_tl} {c : ℝ} :
      X.mul (Y.mulConst c) = (X.mul Y).mulConst c := by
    let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (Y : SeqMS basis_hd basis_tl),
        A = X.mul (Y.mulConst c) ∧
        B = (X.mul Y).mulConst c
    apply SeqMS.eq_of_bisim_add motive
    · simp only [motive]
      use Y
    · rintro A B ⟨Y, rfl, rfl⟩
      cases X with
      | nil => simp
      | cons X_exp X_coef X_tl =>
      cases Y with
      | nil => simp
      | cons Y_exp Y_coef Y_tl =>
      right
      simp only [SeqMS.mulConst_cons, SeqMS.mul_cons_cons, SeqMS.cons_eq_cons, SeqMS.add_mulConst, exists_and_left,
        ↓existsAndEq, and_true, true_and, motive]
      refine ⟨_, _, rfl, ?_⟩
      constructor
      · rw [mul_mulConst_right]
      · rw [SeqMS.mulMonomial_mulConst_right]

  theorem mul_mulConst_right {basis} {X Y : PreMS basis} {c : ℝ} :
      X.mul (Y.mulConst c) = (X.mul Y).mulConst c := by
    cases basis with
    | nil =>
      simp [mul, mulConst, ofReal, toReal]
      ring_nf
    | cons basis_hd basis_tl =>
      simp [ms_eq_ms_iff_mk_eq_mk]
      rw [SeqMS.mul_mulConst_right]

end

theorem mulMonomial_mulConst_right {basis_hd basis_tl} {B : PreMS (basis_hd :: basis_tl)}
    {M_coef : PreMS basis_tl} {M_exp c : ℝ} :
    B.mulMonomial (M_coef.mulConst c) M_exp = (B.mulMonomial M_coef M_exp).mulConst c := by
  simp [ms_eq_ms_iff_mk_eq_mk]
  apply SeqMS.mulMonomial_mulConst_right

mutual
  theorem SeqMS.mulMonomial_mulConst_left {basis_hd : ℝ → ℝ} {basis_tl : Basis}
      {B : SeqMS basis_hd basis_tl} {M_coef : PreMS basis_tl} {M_exp c : ℝ} :
      (B.mulConst c).mulMonomial M_coef M_exp = (B.mulMonomial M_coef M_exp).mulConst c := by
    -- copypaste from left version
    let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (B : SeqMS basis_hd basis_tl),
        X = (B.mulConst c).mulMonomial M_coef M_exp ∧
        Y = (B.mulMonomial M_coef M_exp).mulConst c
    apply SeqMS.eq_of_bisim motive
    · simp only [motive]
      use B
    · intro X Y ih
      simp only [motive] at ih ⊢
      obtain ⟨B, rfl, rfl⟩ := ih
      cases B with
      | nil => simp
      | cons B_exp B_coef B_tl =>
      right
      simp only [↓existsAndEq, SeqMS.mulConst_cons, SeqMS.mulMonomial_cons, SeqMS.cons_eq_cons, and_self, and_true,
        true_and]
      exact ⟨B_tl, rfl, mul_mulConst_left.symm, rfl⟩

  theorem SeqMS.mul_mulConst_left {basis_hd basis_tl} {X Y : SeqMS basis_hd basis_tl} {c : ℝ} :
      (X.mulConst c).mul Y = (X.mul Y).mulConst c := by
    let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (Y : SeqMS basis_hd basis_tl),
        A = (X.mulConst c).mul Y ∧
        B = (X.mul Y).mulConst c
    apply SeqMS.eq_of_bisim_add motive
    · use Y
    · rintro A B ⟨Y, rfl, rfl⟩
      cases X with
      | nil => simp
      | cons X_exp X_coef X_tl =>
      cases Y with
      | nil => simp
      | cons Y_exp Y_coef Y_tl =>
      right
      simp only [SeqMS.mulConst_cons, SeqMS.mul_cons_cons, SeqMS.cons_eq_cons, SeqMS.add_mulConst, exists_and_left,
        ↓existsAndEq, and_true, true_and, motive]
      refine ⟨_, _, rfl, ?_⟩
      constructor
      · rw [mul_mulConst_left]
      · rw [SeqMS.mulMonomial_mulConst_left]

  theorem mul_mulConst_left {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
      (X.mulConst c).mul Y = (X.mul Y).mulConst c := by
    cases basis with
    | nil =>
      simp [mul, mulConst, ofReal, toReal]
      ring_nf
    | cons basis_hd basis_tl =>
      simp [ms_eq_ms_iff_mk_eq_mk]
      apply SeqMS.mul_mulConst_left

end

theorem mulMonomial_mulConst_left {basis_hd basis_tl} {B : PreMS (basis_hd :: basis_tl)}
    {M_coef : PreMS basis_tl} {M_exp c : ℝ} :
    (B.mulConst c).mulMonomial M_coef M_exp = (B.mulMonomial M_coef M_exp).mulConst c := by
  simp [ms_eq_ms_iff_mk_eq_mk]
  apply SeqMS.mulMonomial_mulConst_left

theorem SeqMS.mulMonomial_neg_left {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {B : SeqMS basis_hd basis_tl} {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    B.mulMonomial M_coef.neg M_exp = (B.mulMonomial M_coef M_exp).neg := by
  simp [PreMS.neg, SeqMS.neg, SeqMS.mulMonomial_mulConst_right]

theorem mulMonomial_neg_left {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {B : PreMS (basis_hd :: basis_tl)} {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    B.mulMonomial M_coef.neg M_exp = (B.mulMonomial M_coef M_exp).neg := by
  simp [neg, mulMonomial_mulConst_right]

theorem SeqMS.mul_neg_left {basis_hd basis_tl} {X Y : SeqMS basis_hd basis_tl} :
    X.neg.mul Y = (X.mul Y).neg := by
  simp [neg, mul_mulConst_left]

theorem mul_neg_left {basis : Basis} {X Y : PreMS basis} :
    X.neg.mul Y = (X.mul Y).neg := by
  simp [neg, mul_mulConst_left]

theorem SeqMS.mulMonomial_neg_right {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {B : SeqMS basis_hd basis_tl} {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    B.neg.mulMonomial M_coef M_exp = (B.mulMonomial M_coef M_exp).neg := by
  simp [SeqMS.neg, SeqMS.mulMonomial_mulConst_left]

theorem mulMonomial_neg_right {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {B : PreMS (basis_hd :: basis_tl)} {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    B.neg.mulMonomial M_coef M_exp = (B.mulMonomial M_coef M_exp).neg := by
  simp [neg, mulMonomial_mulConst_left]

theorem SeqMS.mul_neg_right {basis_hd basis_tl} {X Y : SeqMS basis_hd basis_tl} :
    X.mul Y.neg = (X.mul Y).neg := by
  simp [neg, mul_mulConst_right]

theorem mul_neg_right {basis : Basis} {X Y : PreMS basis} :
    X.mul Y.neg = (X.mul Y).neg := by
  simp [neg, mul_mulConst_right]

mutual
  @[simp]
  theorem SeqMS.add_mulMonomial_left {basis_hd} {basis_tl} {B : SeqMS basis_hd basis_tl}
      {M_coef1 M_coef2 : PreMS basis_tl} {M_exp : ℝ} :
      (B.mulMonomial (M_coef1 + M_coef2) M_exp) =
      (B.mulMonomial M_coef1 M_exp) + (B.mulMonomial M_coef2 M_exp) := by
    let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (B : SeqMS basis_hd basis_tl),
      X = B.mulMonomial (M_coef1 + M_coef2) M_exp ∧
      Y = B.mulMonomial M_coef1 M_exp + B.mulMonomial M_coef2 M_exp
    apply SeqMS.eq_of_bisim motive
    · simp only [motive]
      use B
    · intro X Y ih
      simp only [motive] at ih
      obtain ⟨B, rfl, rfl⟩ := ih
      cases B with
      | nil => simp
      | cons B_exp B_coef B_tl =>
      · right
        simp only [SeqMS.mulMonomial_cons, SeqMS.cons_eq_cons, SeqMS.add_cons_cons, lt_self_iff_false, ↓reduceIte,
          exists_and_left, ↓existsAndEq, and_true, exists_eq_left', true_and]
        constructor
        · rw [add_mul_left']
        simp only [motive]
        use ?_

  @[simp]
  theorem SeqMS.add_mul_left' {basis_hd basis_tl} {X Y Z : SeqMS basis_hd basis_tl} :
      Z.mul (X + Y) = Z.mul X + Z.mul Y := by
    let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (X Y : SeqMS basis_hd basis_tl),
        A = Z.mul (X + Y) ∧
        B = Z.mul X + Z.mul Y
    apply SeqMS.eq_of_bisim_add motive
    · simp only [motive]
      use X, Y
    rintro A B ⟨X, Y, rfl, rfl⟩
    cases Z with
    | nil => simp
    | cons Z_exp Z_coef Z_tl =>
    cases X with
    | nil => simp
    | cons X_exp X_coef X_tl =>
    cases Y with
    | nil => simp
    | cons Y_exp Y_coef Y_tl =>
    right
    simp [SeqMS.add_cons_cons, motive]
    split_ifs with h1 h2
    · simp
      refine ⟨_, _, _, rfl, ?_⟩
      simp [SeqMS.mul_cons_cons]
      abel
    · simp
      refine ⟨_, _, _, rfl, ?_⟩
      simp [SeqMS.mul_cons_cons]
      abel
    · have : X_exp = Y_exp := by linarith
      subst this
      simp
      refine ⟨_, _, _, rfl, ?_, ?_⟩
      · rw [add_mul_left']
      · simp [SeqMS.add_mulMonomial_left (basis_tl := basis_tl)]
        abel

  @[simp]
  theorem add_mul_left' {basis : Basis} {X Y Z : PreMS basis} :
      Z.mul (X + Y) = Z.mul X + Z.mul Y := by
    cases basis with
    | nil =>
      simp [mul, ofReal, toReal]
      ring_nf
    | cons basis_hd basis_tl =>
      simp [ms_eq_ms_iff_mk_eq_mk]
      constructor
      · apply SeqMS.add_mul_left'
      · ext t
        simp
        ring

end

theorem add_mulMonomial_left {basis_hd basis_tl} {B : PreMS (basis_hd :: basis_tl)}
    {M_coef1 M_coef2 : PreMS basis_tl} {M_exp : ℝ} :
    (B.mulMonomial (M_coef1 + M_coef2) M_exp) =
    (B.mulMonomial M_coef1 M_exp) + (B.mulMonomial M_coef2 M_exp) := by
  simp [ms_eq_ms_iff_mk_eq_mk]
  ext t
  simp
  ring

mutual

  theorem SeqMS.add_mulMonomial_right {basis_hd} {basis_tl} {A B : SeqMS basis_hd basis_tl}
      {M_coef : PreMS basis_tl} {M_exp : ℝ}
      (m_wo : M_coef.WellOrdered) :
      (SeqMS.mulMonomial (A + B) M_coef M_exp) =
      (SeqMS.mulMonomial A M_coef M_exp) + (SeqMS.mulMonomial B M_coef M_exp) := by
    let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (A B : SeqMS basis_hd basis_tl),
      X = (A + B).mulMonomial M_coef M_exp ∧
      Y = A.mulMonomial M_coef M_exp + B.mulMonomial M_coef M_exp
    apply SeqMS.eq_of_bisim_strong motive
    · simp only [motive]
      use A, B
    · intro X Y ih
      simp only [motive] at ih
      obtain ⟨A, B, rfl, rfl⟩ := ih
      cases A with
      | nil => simp
      | cons A_exp A_coef A_tl =>
      cases B with
      | nil => simp
      | cons B_exp B_coef B_tl =>
      right
      simp [motive, SeqMS.add_cons_cons]
      split_ifs with h1 h2
      · simp
        refine ⟨_, _, rfl, ?_⟩
        simp [SeqMS.mulMonomial_cons]
      · simp
        refine ⟨_, _, rfl, ?_⟩
        simp [SeqMS.mulMonomial_cons]
      · have : A_exp = B_exp := by linarith
        subst this
        simp
        refine ⟨_, _, rfl, ?_, rfl⟩
        rw [add_mul_right' m_wo]

  -- Note: `Z.WellOrdered` is necessary. Counterexample: `X = [0]`, `Y = [1]`, `Z = [0, 2]`.
  -- Then `lhs = [0, 2] * [1, 0] = [1, 3, 2, 0]` while `rhs = [0, 2] + [1, 3] = [1, 3, 0, 2]`.
  theorem SeqMS.add_mul_right' {basis_hd basis_tl} {X Y Z : SeqMS basis_hd basis_tl}
      (hZ_wo : Z.WellOrdered) :
      (X + Y).mul Z = X.mul Z + Y.mul Z := by
    let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (Z : SeqMS basis_hd basis_tl),
        A = (X + Y).mul Z ∧
        B = X.mul Z + Y.mul Z ∧
        Z.WellOrdered
    apply SeqMS.eq_of_bisim_add' motive
    · use Z
    rintro A B ⟨Z, rfl, rfl, hZ_wo⟩
    cases Z with
    | nil => simp
    | cons Z_exp Z_coef Z_tl =>
    by_cases hX : X = .nil
    · simp [hX]
    by_cases hY : Y = .nil
    · simp [hY]
    right
    obtain ⟨hZ_coef_wo, hZ_comp, hZ_tl_wo⟩ := WellOrdered_cons hZ_wo
    simp [motive, SeqMS.mul_cons hZ_wo, SeqMS.add_mulMonomial_right hZ_coef_wo]
    use (X + Y).mulMonomial Z_coef Z_exp, Z_tl
    simp [SeqMS.add_mulMonomial_right hZ_coef_wo, SeqMS.add_leadingExp,
      SeqMS.mulMonomial_leadingExp, lt_sup_iff, true_and]
    constructorm* _ ∧ _
    · abel
    · rw [← SeqMS.leadingExp_eq_bot] at hX
      grind [WithBot.add_lt_add_of_le_of_lt]
    · rw [← SeqMS.leadingExp_eq_bot] at hY hX
      grind [WithBot.add_lt_add_of_le_of_lt]
    · rw [← SeqMS.leadingExp_eq_bot] at hY hX
      grind [WithBot.add_lt_add_of_le_of_lt]
    · assumption

  -- Note: `Z.WellOrdered` is necessary. Counterexample: `X = [0]`, `Y = [1]`, `Z = [0, 2]`.
  -- Then `lhs = [0, 2] * [1, 0] = [1, 3, 2, 0]` while `rhs = [0, 2] + [1, 3] = [1, 3, 0, 2]`.
  theorem add_mul_right' {basis : Basis} {X Y Z : PreMS basis}
      (hZ_wo : Z.WellOrdered) :
      (X + Y).mul Z = X.mul Z + Y.mul Z := by
    cases basis with
    | nil =>
      simp [mul, ofReal, toReal]
      ring_nf
    | cons basis_hd basis_tl =>
      simp [ms_eq_ms_iff_mk_eq_mk]
      constructor
      · apply SeqMS.add_mul_right' (by simpa using hZ_wo)
      · ext t
        simp
        ring

end

theorem add_mulMonomial_right {basis_hd basis_tl} {A B : PreMS (basis_hd :: basis_tl)}
    {M_coef : PreMS basis_tl} {M_exp : ℝ} (m_wo : M_coef.WellOrdered) :
    (A + B).mulMonomial M_coef M_exp =
    A.mulMonomial M_coef M_exp + B.mulMonomial M_coef M_exp := by
  simp [ms_eq_ms_iff_mk_eq_mk, SeqMS.add_mulMonomial_right m_wo]
  ext t
  simp
  ring

mutual

  theorem SeqMS.mulMonomial_mul {basis_hd} {basis_tl} {B : SeqMS basis_hd basis_tl}
      {M_coef1 M_coef2 : PreMS basis_tl} {M_exp1 M_exp2 : ℝ}
      (h_coef2_wo : M_coef2.WellOrdered) :
      (B.mulMonomial M_coef1 M_exp1).mulMonomial M_coef2 M_exp2 =
      B.mulMonomial (M_coef1.mul M_coef2) (M_exp1 + M_exp2) := by
    simp only [SeqMS.mulMonomial, ← SeqMS.map_comp, comp_add_right]
    congr 1
    eta_expand
    simp only [Function.comp_apply]
    ext coef
    rw [mul_assoc']
    exact h_coef2_wo

  theorem SeqMS.mul_mulMonomial {basis_hd} {basis_tl} {A B : SeqMS basis_hd basis_tl}
      {M_coef : PreMS basis_tl} {M_exp : ℝ}
      (hM_wo : M_coef.WellOrdered) :
      A.mul (B.mulMonomial M_coef M_exp) =
      (A.mul B).mulMonomial M_coef M_exp := by
    let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (B : SeqMS basis_hd basis_tl),
        X = A.mul (B.mulMonomial M_coef M_exp) ∧
        Y = (A.mul B).mulMonomial M_coef M_exp
    apply SeqMS.eq_of_bisim_add motive
    · use B
    rintro X Y ⟨B, rfl, rfl⟩
    cases A with
    | nil => simp
    | cons A_exp A_coef A_tl =>
    cases B with
    | nil => simp
    | cons B_exp B_coef B_tl =>
    right
    simp only [SeqMS.mulMonomial_cons, SeqMS.mul_cons_cons, SeqMS.cons_eq_cons, exists_and_left, ↓existsAndEq,
      and_true, true_and, motive]
    refine ⟨_, _, rfl, ?_⟩
    constructorm* _ ∧ _
    · ring
    · apply mul_assoc' hM_wo
    · rw [SeqMS.add_mulMonomial_right hM_wo, SeqMS.mulMonomial_mul hM_wo]

  theorem SeqMS.mul_assoc' {basis_hd basis_tl} {X Y Z : SeqMS basis_hd basis_tl}
      (hZ_wo : Z.WellOrdered) :
      (X.mul Y).mul Z = X.mul (Y.mul Z) := by
    let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
      ∃ Z : SeqMS basis_hd basis_tl,
        A = (X.mul Y).mul Z ∧
        B = X.mul (Y.mul Z) ∧
        Z.WellOrdered
    apply SeqMS.eq_of_bisim_add' motive
    · use Z
    rintro A B ⟨Z, rfl, rfl, hZ_wo⟩
    cases Z with
    | nil => simp
    | cons Z_exp Z_coef Z_tl =>
    by_cases hX : X = .nil
    · simp [hX]
    by_cases hY : Y = .nil
    · simp [hY]
    right
    obtain ⟨hZ_coef_wo, hZ_comp, hZ_tl_wo⟩ := WellOrdered_cons hZ_wo
    simp only [SeqMS.mul_cons hZ_wo, SeqMS.add_mul_left', exists_and_left, ↓existsAndEq, SeqMS.mul_leadingExp,
      true_and, motive]
    use (X.mul Y).mulMonomial Z_coef Z_exp, Z_tl
    simp only [SeqMS.mul_mulMonomial hZ_coef_wo, add_assoc, SeqMS.mulMonomial_leadingExp, SeqMS.mul_leadingExp,
      hZ_tl_wo, and_true, and_self, true_and]
    apply WithBot.add_lt_add_of_le_of_lt (by simp [hX]) (by rfl)
    apply WithBot.add_lt_add_of_le_of_lt (by simp [hY]) (by rfl) hZ_comp

  -- TODO: update example
  -- Note: `Z.WellOrdered` is necessary. Counterexample: `basis = [f, g]`.
  -- `Z = f^0 * (g^0 + g^2)`
  -- `Y = f^0 * g^0 + f^(-1) * g^1` (well-ordered)
  -- `X = f^2 * g^(-1) + f^1 * g^1` (well-ordered)
  -- Then
  -- `lhs = f^2 * (g^(-1) + g) + f^1 * (g^1 + g^3 + g^0 + g^2) + f^0 * (g^2 + g^4)`
  -- `rhs = f^2 * (g^(-1) + g) + f^1 * (g^1 + g^3 + g^2 + g^0) + f^0 * (g^2 + g^4)`
  -- There is a difference in the second coefficient.
  -- It is enough, however, if all coefs of `Z` is well-ordered.
  theorem mul_assoc' {basis : Basis} {X Y Z : PreMS basis}
      (hZ_wo : Z.WellOrdered) :
      (X.mul Y).mul Z = X.mul (Y.mul Z) := by
    cases basis with
    | nil =>
      simp [mul, ofReal, toReal]
      ring_nf
    | cons basis_hd basis_tl =>
      simp [ms_eq_ms_iff_mk_eq_mk, SeqMS.mul_assoc' (by simpa using hZ_wo)]
      ext t
      ring_nf

end

mutual

  theorem SeqMS.mulMonomial_WellOrdered {basis_hd} {basis_tl} {B : SeqMS basis_hd basis_tl}
      {M_coef : PreMS basis_tl} {M_exp : ℝ}
      (hB_wo : B.WellOrdered) (hM_wo : M_coef.WellOrdered) :
      (B.mulMonomial M_coef M_exp).WellOrdered := by
    let motive (X : SeqMS basis_hd basis_tl) : Prop :=
      ∃ (B : SeqMS basis_hd basis_tl), X = B.mulMonomial M_coef M_exp ∧
      B.WellOrdered
    apply SeqMS.WellOrdered.coind motive
    · simp only [motive]
      use B
    · intro exp coef tl ih
      simp only [motive] at ih
      obtain ⟨B, h_eq, hB_wo⟩ := ih
      cases B with
      | nil => simp at h_eq
      | cons B_exp B_coef B_tl =>
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := SeqMS.WellOrdered_cons hB_wo
      simp only [SeqMS.mulMonomial_cons, SeqMS.cons_eq_cons] at h_eq
      simp only [h_eq, SeqMS.mulMonomial_leadingExp, WithBot.coe_add, motive]
      constructorm* _ ∧ _
      · apply mul_WellOrdered h_coef_wo hM_wo
      · apply WithBot.add_lt_add_right
        · simp
        · assumption
      use B_tl

  theorem SeqMS.mul_WellOrdered {basis_hd basis_tl} {X Y : SeqMS basis_hd basis_tl}
      (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) :
      (X.mul Y).WellOrdered := by
    let motive (ms : SeqMS basis_hd basis_tl) : Prop :=
      ∃ Y : SeqMS basis_hd basis_tl,
        ms = X.mul Y ∧ Y.WellOrdered
    apply SeqMS.WellOrdered.add_coind' motive
    · use Y
    rintro ms ⟨Y, rfl, hY_wo⟩
    cases Y with
    | nil => simp
    | cons Y_exp Y_coef Y_tl =>
    by_cases hX : X = .nil
    · simp [hX]
    obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := SeqMS.WellOrdered_cons hY_wo
    right
    simp only [SeqMS.mul_cons hY_wo]
    refine ⟨_, _, rfl, ?_⟩
    simp only [SeqMS.mul_leadingExp, SeqMS.mulMonomial_leadingExp, motive]
    constructorm* _ ∧ _
    · apply SeqMS.mulMonomial_WellOrdered hX_wo hY_coef_wo
    · apply WithBot.add_lt_add_left
      · simpa
      · exact hY_comp
    · use Y_tl

  theorem mul_WellOrdered {basis : Basis} {X Y : PreMS basis}
      (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) :
      (X.mul Y).WellOrdered := by
    cases basis with
    | nil => constructor
    | cons basis_hd basis_tl =>
      simp at *
      exact SeqMS.mul_WellOrdered hX_wo hY_wo

end

mutual

  theorem mulMonomial_Approximates {basis_hd} {basis_tl}
        {B : PreMS (basis_hd :: basis_tl)}
        {M_coef : PreMS basis_tl} {M_exp : ℝ}
        (h_basis : WellFormedBasis (basis_hd :: basis_tl))
        (hB_approx : B.Approximates)
        (hM_approx : M_coef.Approximates) :
      (mulMonomial B M_coef M_exp).Approximates := by
    let motive (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (B : PreMS (basis_hd :: basis_tl)),
        ms ≈ B.mulMonomial M_coef M_exp ∧
        B.Approximates ∧ M_coef.Approximates
    apply Approximates.coind motive
    · simp only [motive]
      use B
    rintro ms ⟨B, ⟨h_seq_eq, hf_eq⟩, hB_approx, hM_approx⟩
    cases B with
    | nil fB =>
      left
      apply Approximates_nil at hB_approx
      simp at hf_eq
      simp [h_seq_eq]
      grw [hf_eq, hB_approx]
      simp
    | cons B_exp B_coef B_tl fB =>
    obtain ⟨h_coef_approx, h_maj, h_tl_approx⟩ := Approximates_cons hB_approx
    right
    simp [motive, h_seq_eq]
    simp at hf_eq
    constructorm* _ ∧ _
    · apply mul_Approximates (h_basis.tail) h_coef_approx hM_approx
    · apply majorated_of_EventuallyEq hf_eq
      rw [show B_exp + M_exp = B_exp + M_exp + 0 by simp]
      apply mul_majorated
      · apply mul_majorated
        · exact h_maj
        · apply majorated_self
          apply basis_tendsto_top h_basis
          simp
        · exact basis_head_eventually_pos h_basis
      · exact Approximates_coef_majorated_head hM_approx h_basis
      · exact basis_head_eventually_pos h_basis
    use mk B_tl (fB - basis_hd ^ B_exp * B_coef.toFun)
    simp [hM_approx, h_tl_approx]
    apply (hf_eq.and (basis_head_eventually_pos h_basis)).mono
    intro t ⟨hf_eq, h_pos⟩
    simp [hf_eq, Real.rpow_add h_pos]
    ring_nf

  theorem mul_Approximates {basis : Basis} {X Y : PreMS basis}
      (h_basis : WellFormedBasis basis)
      (hX_approx : X.Approximates) (hY_approx : Y.Approximates) :
      (X.mul Y).Approximates := by
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      let motive (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
        ∃ (Y : PreMS (basis_hd :: basis_tl)),
          ms ≈ X.mul Y ∧ Y.Approximates
      apply Approximates.add_coind motive
      · use Y
      rintro ms ⟨Y, ⟨h_seq_eq, hf_eq⟩, hY_approx⟩
      cases X with
      | nil fX =>
        apply Approximates_nil at hX_approx
        simp at hf_eq
        simp [h_seq_eq]
        grw [hf_eq, hX_approx]
        simp
      | cons X_exp X_coef X_tl fX =>
      cases Y with
      | nil fY =>
        simp at hf_eq
        apply Approximates_nil at hY_approx
        simp [h_seq_eq]
        grw [hf_eq, hY_approx]
        simp
      | cons Y_exp Y_coef Y_tl fY =>
      right
      obtain ⟨hX_coef_approx, hX_maj, hX_tl_approx⟩ := Approximates_cons hX_approx
      obtain ⟨hY_coef_approx, hY_maj, hY_tl_approx⟩ := Approximates_cons hY_approx
      simp at hf_eq
      simp [h_seq_eq]
      use (mk X_tl (fX - basis_hd ^ X_exp * X_coef.toFun)).mulMonomial Y_coef Y_exp,
        (SeqMS.cons X_exp X_coef X_tl).mul Y_tl
      constructorm* _ ∧ _
      · simp
      · exact mul_Approximates (h_basis.tail) hX_coef_approx hY_coef_approx
      · apply majorated_of_EventuallyEq hf_eq
        apply mul_majorated hX_maj hY_maj
        apply basis_head_eventually_pos h_basis
      · apply mulMonomial_Approximates h_basis hX_tl_approx hY_coef_approx
      simp [motive]
      use mk Y_tl (fY - basis_hd ^ Y_exp * Y_coef.toFun)
      constructorm* _ ∧ _
      · simp
      · simp
        grw [hf_eq]
        apply (basis_head_eventually_pos h_basis).mono
        intro t h
        simp [Real.rpow_add h]
        ring_nf
      · assumption

end

instance {basis_hd basis_tl} :
    SeqMS.FriendOperationClass (@SeqMS.mul basis_hd basis_tl) := by
  apply SeqMS.FriendOperationClass.mk'
  intro c
  cases c with
  | nil =>
    convert SeqMS.FriendOperation.const (s := .nil)
    simp
  | cons c_exp c_coef c_tl =>
  let motive (op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) : Prop :=
    op = SeqMS.mul (.cons c_exp c_coef c_tl)
  apply SeqMS.FriendOperation.coind_comp_friend_left motive
  · rfl
  rintro _ ⟨rfl⟩
  use fun hd? ↦ match hd? with
  | none => none
  | some (exp, coef) =>
    some (c_exp + exp, c_coef.mul coef,
      ⟨SeqMS.add (SeqMS.mulMonomial c_tl coef exp), SeqMS.FriendOperationClass.FriendOperation _⟩,
      ⟨SeqMS.mul (.cons c_exp c_coef c_tl), rfl⟩)
  intro x
  cases x with
  | nil => simp
  | cons x_exp x_coef x_tl =>
  simp [SeqMS.mul_cons_cons, SeqMS.add_def]

theorem SeqMS.WellOrdered.mul_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → Prop) (h_base : motive ms)
    (h_step :
      ∀ (exp : ℝ) (coef : PreMS basis_tl) (tl : SeqMS basis_hd basis_tl),
        motive (.cons exp coef tl) → coef.WellOrdered ∧ tl.leadingExp < exp ∧
        ∃ (A B : SeqMS basis_hd basis_tl), tl = A.mul B ∧ A.WellOrdered ∧ motive B) :
    ms.WellOrdered := by
  apply WellOrdered.coind_friend' (@SeqMS.mul basis_hd basis_tl) motive SeqMS.WellOrdered
  · intros
    apply mul_WellOrdered <;> assumption
  · assumption
  · grind

theorem Approximates.mul_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (motive : PreMS (basis_hd :: basis_tl) → Prop)
    (h_wo : ms.WellOrdered)
    (h_base : motive ms)
    (h_step :
      ∀ (ms : PreMS (basis_hd :: basis_tl)),
        motive ms →
        ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0 ∨
        ∃ exp coef tl,
          ms.seq = .cons exp coef tl ∧ coef.Approximates ∧ majorated ms.toFun basis_hd exp ∧
          ∃ (A B : PreMS (basis_hd :: basis_tl)),
          tl = (A.mul B).seq ∧
          ms.toFun =ᶠ[atTop] (basis_hd ^ exp * coef.toFun + A.toFun * B.toFun) ∧
          A.Approximates ∧ B.WellOrdered ∧ motive B) :
    ms.Approximates := by
  let motive' (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ A B, ms ≈ PreMS.mul A B ∧ A.Approximates ∧ B.WellOrdered ∧ motive B
  apply Approximates.add_coind motive'
  · use one, ms
    simp at h_wo
    simp [h_base, one_Approximates h_basis, h_wo]
  rintro ms ⟨A, B, ⟨h_seq_eq, hf_eq⟩, hA, hB_wo, hB⟩
  cases A with
  | nil fA =>
    apply Approximates_nil at hA
    simp at hf_eq
    simp [h_seq_eq]
    grw [hf_eq, hA]
    simp
  | cons A_exp A_coef A_tl fA =>
  specialize h_step _ hB
  obtain ⟨hB_seq, hB_fun⟩ | ⟨B_exp, B_coef, B_tl, hB_seq, hB_coef, hB_maj,
    X, Y, rfl, hfB, hX, hY_wo, hY⟩ := h_step
  · simp [h_seq_eq, hB_seq]
    simp at hf_eq
    grw [hf_eq, hB_fun]
    simp
  right
  simp at hf_eq
  simp [h_seq_eq, hB_seq]
  obtain ⟨hA_coef, hA_maj, hA_tl⟩ := Approximates_cons hA
  use (mk A_tl (fA - basis_hd ^ A_exp * A_coef.toFun)).mulMonomial B_coef B_exp,
    (SeqMS.cons A_exp A_coef A_tl).mul (X.seq.mul Y.seq)
  simp
  constructorm* _ ∧ _
  · apply mul_Approximates (h_basis.tail) hA_coef hB_coef
  · apply majorated_of_EventuallyEq hf_eq
    apply mul_majorated hA_maj hB_maj
    apply basis_head_eventually_pos h_basis
  · apply mulMonomial_Approximates h_basis hA_tl hB_coef
  simp [motive']
  use (mk (.cons A_exp A_coef A_tl) fA).mul X, Y
  constructorm* _ ∧ _
  · simp
    rw [SeqMS.mul_assoc' (by simpa using hY_wo)]
  · grw [hf_eq, hfB]
    apply (basis_head_eventually_pos h_basis).mono
    intro t ht
    simp
    rw [Real.rpow_add ht]
    ring
  · apply mul_Approximates h_basis hA hX
  · simpa using hY_wo
  · exact hY

end PreMS

end ComputeAsymptotics
