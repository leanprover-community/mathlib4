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

@[expose] public section

set_option linter.flexible false

namespace ComputeAsymptotics

namespace PreMS

mutual
  /-- Multiplication for multiseries. -/
  noncomputable def mul {basis : Basis} (X Y : PreMS basis) : PreMS basis :=
    match basis with
    | [] => X.toReal * Y.toReal
    | List.cons basis_hd basis_tl =>
      match destruct X with
      | none => nil
      | some (X_exp, X_coef, X_tl) =>
        let T := (PreMS (basis_hd :: basis_tl))
        let g : T → Option (ℝ × PreMS basis_tl × PreMS (basis_hd :: basis_tl) × T) := fun Y =>
          match destruct Y with
          | none => none
          | some (Y_exp, Y_coef, Y_tl) =>
            some (X_exp + Y_exp, X_coef.mul Y_coef, mulMonomial X_tl Y_coef Y_exp, Y_tl)
        gcorec g add Y

  /-- Multiplication by monomial, i.e. `M_coef * basis_hd ^ M_exp * B`. -/
  noncomputable def mulMonomial {basis_hd} {basis_tl} (B : PreMS (basis_hd :: basis_tl))
      (M_coef : PreMS basis_tl) (M_exp : ℝ) : PreMS (basis_hd :: basis_tl) :=
    B.map (fun exp => exp + M_exp) (fun coef => coef.mul M_coef)
end

--theorems
open Filter Asymptotics

@[simp]
theorem nil_mul {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    mul nil ms = nil := by
  simp [mul]

@[simp]
theorem mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    mul ms nil = nil := by
  simp only [mul]
  cases ms <;> simp only [destruct_nil, destruct_cons]
  rw [gcorec_nil]
  simp

@[simp]
theorem mulMonomial_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {M_exp : ℝ}
    {M_coef : PreMS basis_tl} :
    mulMonomial (basis_hd := basis_hd) nil M_coef M_exp = nil := by
  simp [mulMonomial]

@[simp]
theorem mulMonomial_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp M_exp : ℝ}
    {X_coef M_coef : PreMS basis_tl} {X_tl : PreMS (basis_hd :: basis_tl)} :
    (cons X_exp X_coef X_tl).mulMonomial M_coef M_exp =
    cons (X_exp + M_exp) (X_coef.mul M_coef) (mulMonomial X_tl M_coef M_exp) := by
  simp [mulMonomial]

@[simp]
theorem mulMonomial_leadingExp {basis_hd} {basis_tl} {B : PreMS (basis_hd :: basis_tl)}
    {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    (mulMonomial B M_coef M_exp).leadingExp = B.leadingExp + M_exp := by
  cases B <;> simp

theorem mul_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ} {coef : PreMS basis_tl}
    {tl X Y : PreMS (basis_hd :: basis_tl)} (h : X.mul Y = cons exp coef tl) :
    ∃ X_exp X_coef X_tl Y_exp Y_coef Y_tl, X = cons X_exp X_coef X_tl ∧
      Y = cons Y_exp Y_coef Y_tl := by
  cases X with
  | nil => simp at h
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp at h
  | cons Y_exp Y_coef Y_tl => use X_exp, X_coef, X_tl, Y_exp, Y_coef, Y_tl

@[simp]
theorem mul_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp Y_exp : ℝ}
    {X_coef Y_coef : PreMS basis_tl} {X_tl Y_tl : PreMS (basis_hd :: basis_tl)} :
    (cons X_exp X_coef X_tl).mul (cons Y_exp Y_coef Y_tl) =
    cons (X_exp + Y_exp) (X_coef.mul Y_coef) ((mulMonomial X_tl Y_coef Y_exp) +
      ((cons X_exp X_coef X_tl).mul Y_tl)) := by
  simp only [mul, destruct_cons]
  rw [gcorec_some, add_def]
  simp

@[simp]
theorem mul_leadingExp {basis_hd} {basis_tl} {X Y : PreMS (basis_hd :: basis_tl)} :
    (mul X Y).leadingExp = X.leadingExp + Y.leadingExp := by
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl =>
  simp [leadingExp_of_head]

-- Note: the condition `X.WellOrdered` is necessary.
-- Counterexample: `X = [1, 2]`, `Y = [1]` (well-ordered).
-- Then `lhs = [1, 2]` while `rhs = [2, 1]`.
theorem mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_exp : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl X : PreMS (basis_hd :: basis_tl)}
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

theorem mul_eq_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X Y : PreMS (basis_hd :: basis_tl)} (h : X.mul Y = nil) :
    X = nil ∨ Y = nil := by
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl =>
  simp at h

@[simp]
theorem mul_one' {basis : Basis} {ms : PreMS basis} : mul ms (one basis) = ms := by
  cases basis with
  | nil => simp [mul, one, const]
  | cons basis_hd basis_tl =>
    let motive (X Y : PreMS (basis_hd :: basis_tl)) : Prop :=
      X = Y.mul (one _)
    apply eq_of_bisim motive
    · simp only [motive]
    rintro X Y rfl
    cases Y with
    | nil => simp
    | cons exp coef tl =>
    simpa [one, const, motive, mul_cons (WellOrdered.cons_nil const_WellOrdered)] using mul_one'

@[simp]
theorem one_mul' {basis : Basis} {ms : PreMS basis} : mul (one basis) ms = ms := by
  cases basis with
  | nil => simp [mul, one, const]
  | cons basis_hd basis_tl =>
    let motive (X Y : PreMS (basis_hd :: basis_tl)) : Prop :=
      X = (one _).mul Y
    apply eq_of_bisim motive
    · simp only [motive]
    rintro A B rfl
    cases B with
    | nil => simp
    | cons exp coef tl =>
    simpa [one, const, motive] using one_mul'

mutual
  theorem mulMonomial_mulConst_right {basis_hd : ℝ → ℝ} {basis_tl : Basis}
      {B : PreMS (basis_hd :: basis_tl)} {M_coef : PreMS basis_tl} {M_exp c : ℝ} :
      B.mulMonomial (M_coef.mulConst c) M_exp = (B.mulMonomial M_coef M_exp).mulConst c := by
    let motive (X Y : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (B : PreMS (basis_hd :: basis_tl)),
        X = B.mulMonomial (M_coef.mulConst c) M_exp ∧
        Y = (B.mulMonomial M_coef M_exp).mulConst c
    apply eq_of_bisim motive
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
      simp only [↓existsAndEq, mulMonomial_cons, cons_eq_cons, mulConst_cons, and_self, and_true,
        true_and]
      use B_tl
      simp [mul_mulConst_right (basis := basis_tl)]

  theorem mul_mulConst_right {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
      X.mul (Y.mulConst c) = (X.mul Y).mulConst c := by
    cases basis with
    | nil =>
      simp [mul, mulConst]
      ring_nf
    | cons basis_hd basis_tl =>
      let motive (A B : PreMS (basis_hd :: basis_tl)) : Prop :=
        ∃ (Y : PreMS (basis_hd :: basis_tl)),
          A = X.mul (Y.mulConst c) ∧
          B = (X.mul Y).mulConst c
      apply eq_of_bisim_add motive
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
        simp only [mulConst_cons, mul_cons_cons, cons_eq_cons, add_mulConst, exists_and_left,
          ↓existsAndEq, and_true, true_and, motive]
        refine ⟨_, _, rfl, ?_⟩
        constructor
        · rw [mul_mulConst_right]
        · rw [mulMonomial_mulConst_right]
end

mutual
  theorem mulMonomial_mulConst_left {basis_hd : ℝ → ℝ} {basis_tl : Basis}
      {B : PreMS (basis_hd :: basis_tl)} {M_coef : PreMS basis_tl} {M_exp c : ℝ} :
      (B.mulConst c).mulMonomial M_coef M_exp = (B.mulMonomial M_coef M_exp).mulConst c := by
    -- copypaste from left version
    let motive (X Y : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (B : PreMS (basis_hd :: basis_tl)),
        X = (B.mulConst c).mulMonomial M_coef M_exp ∧
        Y = (B.mulMonomial M_coef M_exp).mulConst c
    apply eq_of_bisim motive
    · simp only [motive]
      use B
    · intro X Y ih
      simp only [motive] at ih ⊢
      obtain ⟨B, rfl, rfl⟩ := ih
      cases B with
      | nil => simp
      | cons B_exp B_coef B_tl =>
      right
      simp only [↓existsAndEq, mulConst_cons, mulMonomial_cons, cons_eq_cons, and_self, and_true,
        true_and]
      exact ⟨B_tl, rfl, mul_mulConst_left.symm, rfl⟩


  theorem mul_mulConst_left {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
      (X.mulConst c).mul Y = (X.mul Y).mulConst c := by
    cases basis with
    | nil =>
      simp [mul, mulConst]
      ring_nf
    | cons basis_hd basis_tl =>
      let motive (A B : PreMS (basis_hd :: basis_tl)) : Prop :=
        ∃ (Y : PreMS (basis_hd :: basis_tl)),
          A = (X.mulConst c).mul Y ∧
          B = (X.mul Y).mulConst c
      apply eq_of_bisim_add motive
      · use Y
      · rintro A B ⟨Y, rfl, rfl⟩
        cases X with
        | nil => simp
        | cons X_exp X_coef X_tl =>
        cases Y with
        | nil => simp
        | cons Y_exp Y_coef Y_tl =>
        right
        simp only [mulConst_cons, mul_cons_cons, cons_eq_cons, add_mulConst, exists_and_left,
          ↓existsAndEq, and_true, true_and, motive]
        refine ⟨_, _, rfl, ?_⟩
        constructor
        · rw [mul_mulConst_left]
        · rw [mulMonomial_mulConst_left]

end

theorem mulMonomial_neg_left {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {B : PreMS (basis_hd :: basis_tl)} {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    B.mulMonomial M_coef.neg M_exp = (B.mulMonomial M_coef M_exp).neg := by
  simp [neg, mulMonomial_mulConst_right]

theorem mul_neg_left {basis : Basis} {X Y : PreMS basis} :
    X.neg.mul Y = (X.mul Y).neg := by
  simp [neg, mul_mulConst_left]

theorem mulMonomial_neg_right {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {B : PreMS (basis_hd :: basis_tl)} {M_coef : PreMS basis_tl} {M_exp : ℝ} :
    B.neg.mulMonomial M_coef M_exp = (B.mulMonomial M_coef M_exp).neg := by
  simp [neg, mulMonomial_mulConst_left]

theorem mul_neg_right {basis : Basis} {X Y : PreMS basis} :
    X.mul Y.neg = (X.mul Y).neg := by
  simp [neg, mul_mulConst_right]

mutual
  @[simp]
  theorem add_mulMonomial_left {basis_hd} {basis_tl} {B : PreMS (basis_hd :: basis_tl)}
      {M_coef1 M_coef2 : PreMS basis_tl} {M_exp : ℝ} :
      (B.mulMonomial (M_coef1 + M_coef2) M_exp) =
      (B.mulMonomial M_coef1 M_exp) + (B.mulMonomial M_coef2 M_exp) := by
    let motive (X Y : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (B : PreMS (basis_hd :: basis_tl)),
      X = B.mulMonomial (M_coef1 + M_coef2) M_exp ∧
      Y = B.mulMonomial M_coef1 M_exp + B.mulMonomial M_coef2 M_exp
    apply eq_of_bisim motive
    · simp only [motive]
      use B
    · intro X Y ih
      simp only [motive] at ih
      obtain ⟨B, rfl, rfl⟩ := ih
      cases B with
      | nil => simp
      | cons B_exp B_coef B_tl =>
      · right
        simp only [mulMonomial_cons, cons_eq_cons, add_cons_cons, lt_self_iff_false, ↓reduceIte,
          exists_and_left, ↓existsAndEq, and_true, exists_eq_left', true_and]
        constructor
        · rw [add_mul_left']
        simp only [motive]
        use ?_

  @[simp]
  theorem add_mul_left' {basis : Basis} {X Y Z : PreMS basis} :
      Z.mul (X + Y) = Z.mul X + Z.mul Y := by
    cases basis with
    | nil =>
      simp [mul]
      ring_nf
    | cons basis_hd basis_tl =>
      let motive (A B : PreMS (basis_hd :: basis_tl)) : Prop :=
        ∃ (X Y : PreMS (basis_hd :: basis_tl)),
          A = Z.mul (X + Y) ∧
          B = Z.mul X + Z.mul Y
      apply eq_of_bisim_add motive
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
      simp only [add_cons_cons, mul_cons_cons, add_lt_add_iff_left, exists_and_left, ↓existsAndEq,
        and_true, motive]
      split_ifs with h1 h2
      · use ?_, ?_, ?_, X_tl, cons Y_exp Y_coef Y_tl
        constructor
        · simp [-cons_eq_cons]
          rfl
        simp
        abel
      · use ?_, ?_, ?_, cons X_exp X_coef X_tl, Y_tl
        constructor
        · simp [-cons_eq_cons]
          rfl
        congr 1
        simp
        abel
      · have : X_exp = Y_exp := by linarith
        subst this
        use ?_, ?_, ?_, X_tl, Y_tl
        constructor
        · simp [-cons_eq_cons]
          rfl
        congr 1
        · rw [add_mul_left']
        · simp [add_mulMonomial_left (basis_tl := basis_tl)]
          abel

end

mutual
  theorem add_mulMonomial_right {basis_hd} {basis_tl} {A B : PreMS (basis_hd :: basis_tl)}
      {M_coef : PreMS basis_tl} {M_exp : ℝ}
      (m_wo : M_coef.WellOrdered) :
      (mulMonomial (A + B) M_coef M_exp) =
      (mulMonomial A M_coef M_exp) + (mulMonomial B M_coef M_exp) := by
    let motive (X Y : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (A B : PreMS (basis_hd :: basis_tl)),
      X = (A + B).mulMonomial M_coef M_exp ∧
      Y = A.mulMonomial M_coef M_exp + B.mulMonomial M_coef M_exp
    apply eq_of_bisim_strong motive
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
      rw [add_cons_cons]
      split_ifs with h1 h2
      · simp only [mulMonomial_cons, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
          exists_eq_left', motive]
        use A_tl, cons B_exp B_coef B_tl
        simp [add_cons_cons, h1]
      · simp only [mulMonomial_cons, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
          exists_eq_left', motive]
        use cons A_exp A_coef A_tl, B_tl
        simp [add_cons_cons, h1, h2]
      · have : A_exp = B_exp := by linarith
        subst this
        simp only [mulMonomial_cons, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
          exists_eq_left', motive]
        use A_tl, B_tl
        simp only [add_cons_cons, lt_self_iff_false, ↓reduceIte, cons_eq_cons, and_true, true_and]
        rw [add_mul_right' m_wo]

  -- Note: `Z.WellOrdered` is necessary. Counterexample: `X = [0]`, `Y = [1]`, `Z = [0, 2]`.
  -- Then `lhs = [0, 2] * [1, 0] = [1, 3, 2, 0]` while `rhs = [0, 2] + [1, 3] = [1, 3, 0, 2]`.
  theorem add_mul_right' {basis : Basis} {X Y Z : PreMS basis}
      (hZ_wo : Z.WellOrdered) :
      (X + Y).mul Z = X.mul Z + Y.mul Z := by
    cases basis with
    | nil =>
      simp [mul]
      ring_nf
    | cons basis_hd basis_tl =>
      let motive (A B : PreMS (basis_hd :: basis_tl)) : Prop :=
        ∃ (Z : PreMS (basis_hd :: basis_tl)),
          A = (X + Y).mul Z ∧
          B = X.mul Z + Y.mul Z ∧
          Z.WellOrdered
      apply eq_of_bisim_add' motive
      · use Z
      intro A B ih
      obtain ⟨Z, rfl, rfl, hZ_wo⟩ := ih
      cases Z with
      | nil => simp
      | cons Z_exp Z_coef Z_tl =>
      by_cases hX : X = nil
      · simp [hX]
      by_cases hY : Y = nil
      · simp [hY]
      right
      simp only [mul_cons hZ_wo, exists_and_left, ↓existsAndEq, add_leadingExp, mul_leadingExp,
        sup_lt_iff, true_and, motive]
      obtain ⟨hZ_coef_wo, hZ_comp, hZ_tl_wo⟩ := WellOrdered_cons hZ_wo
      use (X + Y).mulMonomial Z_coef Z_exp, Z_tl
      simp only [mulMonomial_leadingExp, add_leadingExp, true_and]
      constructorm* _ ∧ _
      · rw [add_mulMonomial_right hZ_coef_wo]
        abel
      · apply WithBot.add_lt_add_of_le_of_lt
        · simp [hX]
        all_goals order
      · apply WithBot.add_lt_add_of_le_of_lt
        · simp [hX]
        all_goals order
      · apply WithBot.add_lt_add_of_le_of_lt
        · simp [hY]
        all_goals order
      · assumption

end

mutual
  theorem mulMonomial_mul {basis_hd} {basis_tl} {B : PreMS (basis_hd :: basis_tl)}
      {M_coef1 M_coef2 : PreMS basis_tl} {M_exp1 M_exp2 : ℝ}
      (h_coef2_wo : M_coef2.WellOrdered) :
      (B.mulMonomial M_coef1 M_exp1).mulMonomial M_coef2 M_exp2 =
      B.mulMonomial (M_coef1.mul M_coef2) (M_exp1 + M_exp2) := by
    simp only [mulMonomial, ← map_comp, comp_add_right]
    congr 1
    eta_expand
    simp only [Function.comp_apply]
    ext coef
    rw [mul_assoc']
    exact h_coef2_wo

  theorem mul_mulMonomial {basis_hd} {basis_tl} {A B : PreMS (basis_hd :: basis_tl)}
      {M_coef : PreMS basis_tl} {M_exp : ℝ}
      (hM_wo : M_coef.WellOrdered) :
      A.mul (B.mulMonomial M_coef M_exp) =
      (A.mul B).mulMonomial M_coef M_exp := by
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun X Y =>
      ∃ (B : PreMS (basis_hd :: basis_tl)),
        X = A.mul (B.mulMonomial M_coef M_exp) ∧
        Y = (A.mul B).mulMonomial M_coef M_exp
    apply eq_of_bisim_add motive
    · use B
    rintro X Y ⟨B, rfl, rfl⟩
    cases A with
    | nil => simp
    | cons A_exp A_coef A_tl =>
    cases B with
    | nil => simp
    | cons B_exp B_coef B_tl =>
    right
    simp only [mulMonomial_cons, mul_cons_cons, cons_eq_cons, exists_and_left, ↓existsAndEq,
      and_true, true_and, motive]
    refine ⟨_, _, rfl, ?_⟩
    constructorm* _ ∧ _
    · ring
    · apply mul_assoc' hM_wo
    · rw [add_mulMonomial_right hM_wo, mulMonomial_mul hM_wo]

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
      simp [mul]
      ring_nf
    | cons basis_hd basis_tl =>
      let motive (A B : PreMS (basis_hd :: basis_tl)) : Prop :=
        ∃ Z : PreMS (basis_hd :: basis_tl),
          A = (X.mul Y).mul Z ∧
          B = X.mul (Y.mul Z) ∧
          Z.WellOrdered
      apply eq_of_bisim_add' motive
      · use Z
      rintro A B ⟨Z, rfl, rfl, hZ_wo⟩
      cases Z with
      | nil => simp
      | cons Z_exp Z_coef Z_tl =>
      by_cases hX : X = nil
      · simp [hX]
      by_cases hY : Y = nil
      · simp [hY]
      right
      obtain ⟨hZ_coef_wo, hZ_comp, hZ_tl_wo⟩ := WellOrdered_cons hZ_wo
      simp only [mul_cons hZ_wo, add_mul_left', exists_and_left, ↓existsAndEq, mul_leadingExp,
        true_and, motive]
      use (X.mul Y).mulMonomial Z_coef Z_exp, Z_tl
      simp only [mul_mulMonomial hZ_coef_wo, add_assoc, mulMonomial_leadingExp, mul_leadingExp,
        hZ_tl_wo, and_true, and_self, true_and]
      apply WithBot.add_lt_add_of_le_of_lt (by simp [hX]) (by rfl)
      apply WithBot.add_lt_add_of_le_of_lt (by simp [hY]) (by rfl) hZ_comp

end

mutual
  theorem mulMonomial_WellOrdered {basis_hd} {basis_tl} {B : PreMS (basis_hd :: basis_tl)}
      {M_coef : PreMS basis_tl} {M_exp : ℝ}
      (hB_wo : B.WellOrdered) (hM_wo : M_coef.WellOrdered) :
      (mulMonomial B M_coef M_exp).WellOrdered := by
    let motive (X : PreMS (basis_hd :: basis_tl)) : Prop :=
      ∃ (B : PreMS (basis_hd :: basis_tl)), X = B.mulMonomial M_coef M_exp ∧
      B.WellOrdered
    apply WellOrdered.coind motive
    · simp only [motive]
      use B
    · intro exp coef tl ih
      simp only [motive] at ih
      obtain ⟨B, h_eq, hB_wo⟩ := ih
      cases B with
      | nil => simp at h_eq
      | cons B_exp B_coef B_tl =>
      obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons hB_wo
      simp only [mulMonomial_cons, cons_eq_cons] at h_eq
      simp only [h_eq, mulMonomial_leadingExp, WithBot.coe_add, motive]
      constructorm* _ ∧ _
      · apply mul_WellOrdered h_coef_wo hM_wo
      · apply WithBot.add_lt_add_right
        · simp
        · assumption
      use B_tl

  theorem mul_WellOrdered {basis : Basis} {X Y : PreMS basis}
      (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) :
      (X.mul Y).WellOrdered := by
    cases basis with
    | nil => constructor
    | cons basis_hd basis_tl =>
      let motive (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
        ∃ Y : PreMS (basis_hd :: basis_tl),
          ms = X.mul Y ∧ Y.WellOrdered
      apply WellOrdered.add_coind' motive
      · use Y
      rintro ms ⟨Y, rfl, hY_wo⟩
      cases Y with
      | nil => simp
      | cons Y_exp Y_coef Y_tl =>
      by_cases hX : X = nil
      · simp [hX]
      obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
      right
      simp only [mul_cons hY_wo]
      refine ⟨_, _, rfl, ?_⟩
      simp only [mul_leadingExp, mulMonomial_leadingExp, motive]
      constructorm* _ ∧ _
      · apply mulMonomial_WellOrdered hX_wo hY_coef_wo
      · apply WithBot.add_lt_add_left
        · simpa
        · exact hY_comp
      · use Y_tl

end

mutual

  theorem mulMonomial_Approximates {basis_hd} {basis_tl} {fB fM : ℝ → ℝ}
        {B : PreMS (basis_hd :: basis_tl)}
        {M_coef : PreMS basis_tl} {M_exp : ℝ}
        (h_basis : WellFormedBasis (basis_hd :: basis_tl))
        (hB_approx : B.Approximates fB)
        (hM_approx : M_coef.Approximates fM) :
      (mulMonomial B M_coef M_exp).Approximates (fun t ↦ (fB t) * (basis_hd t)^M_exp * (fM t)) := by
    let motive (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) : Prop :=
      ∃ (B : PreMS (basis_hd :: basis_tl)) (fB fM : ℝ → ℝ),
        ms = B.mulMonomial M_coef M_exp ∧
        f =ᶠ[atTop] (fun t ↦ (fB t) * (basis_hd t) ^ M_exp * (fM t)) ∧
        B.Approximates fB ∧ M_coef.Approximates fM
    apply Approximates.coind motive
    · simp only [motive]
      use B, fB, fM
    intro f ms ih
    simp only [motive] at ih
    obtain ⟨B, fB, fM, h_ms_eq, hf_eq, hB_approx, hM_approx⟩ := ih
    subst h_ms_eq
    cases B with
    | nil =>
      left
      apply Approximates_nil at hB_approx
      simp
      grw [hf_eq]
      push fun _ ↦ _
      grw [hB_approx]
      simp
    | cons B_exp B_coef B_tl =>
      obtain ⟨fC, h_coef_approx, h_maj, h_tl_approx⟩ := Approximates_cons hB_approx
      right
      simp [motive]
      refine ⟨_, mul_Approximates (h_basis.tail) h_coef_approx hM_approx, ?_⟩
      constructor
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
      refine ⟨_, rfl, _, _, ?_, h_tl_approx, hM_approx⟩
      apply (hf_eq.and (basis_head_eventually_pos h_basis)).mono
      intro t ⟨hf_eq, h_pos⟩
      simp only [hf_eq, Real.rpow_add h_pos, Pi.mul_apply]
      ring_nf

  theorem mul_Approximates {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
      (h_basis : WellFormedBasis basis)
      (hX_approx : X.Approximates fX) (hY_approx : Y.Approximates fY) :
      (X.mul Y).Approximates (fX * fY) := by
    cases basis with
    | nil =>
      simp only [Approximates_const_iff, mul] at *
      exact hX_approx.mul hY_approx
    | cons basis_hd basis_tl =>
      let motive (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) : Prop :=
        ∃ (Y : PreMS (basis_hd :: basis_tl)) (fY : ℝ → ℝ),
          ms = X.mul Y ∧ f =ᶠ[atTop] fX * fY ∧ Y.Approximates fY
      apply Approximates.add_coind motive
      · use Y, fY
      rintro ms f ⟨Y, fY, rfl, hf_eq, hY_approx⟩
      cases X with
      | nil =>
        apply Approximates_nil at hX_approx
        simp only [nil_mul, true_and, ↓existsAndEq, nil_ne_cons, false_and, exists_const, or_false]
        grw [hf_eq, hX_approx]
        simp
      | cons X_exp X_coef X_tl =>
      cases Y with
      | nil =>
        simp only [mul_nil, true_and, ↓existsAndEq, nil_ne_cons, false_and, exists_const, or_false]
        apply Approximates_nil at hY_approx
        grw [hf_eq, hY_approx]
        simp
      | cons Y_exp Y_coef Y_tl =>
      right
      obtain ⟨fXC, hX_coef_approx, hX_maj, hX_tl_approx⟩ := Approximates_cons hX_approx
      obtain ⟨fYC, hY_coef_approx, hY_maj, hY_tl_approx⟩ := Approximates_cons hY_approx
      simp only [↓existsAndEq, mul_cons_cons, cons_eq_cons, true_and, exists_and_left]
      use fXC * fYC
      refine ⟨_, _, rfl, ?_⟩
      constructorm* _ ∧ _
      · exact mul_Approximates (h_basis.tail) hX_coef_approx hY_coef_approx
      · apply majorated_of_EventuallyEq hf_eq
        apply mul_majorated hX_maj hY_maj
        apply basis_head_eventually_pos h_basis
      refine ⟨_, mulMonomial_Approximates h_basis hX_tl_approx hY_coef_approx, ?_⟩
      simp only [exists_and_left, Pi.mul_apply, motive]
      refine ⟨_, rfl, _, ?_, hY_tl_approx⟩
      push fun _ ↦ _
      grw [hf_eq]
      apply (basis_head_eventually_pos h_basis).mono
      intro t h
      simp [Real.rpow_add h]
      ring_nf

end

instance {basis_hd basis_tl} :
    FriendOperationClass (mul (basis := basis_hd :: basis_tl)) := by
  sorry

theorem WellOrdered.mul_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → Prop) (h_base : motive ms)
    (h_step :
      ∀ (exp : ℝ) (coef : PreMS basis_tl) (tl : PreMS (basis_hd :: basis_tl)),
        motive (PreMS.cons exp coef tl) → coef.WellOrdered ∧ tl.leadingExp < ↑exp ∧
        ∃ (A B : PreMS (basis_hd :: basis_tl)), tl = A.mul B ∧ A.WellOrdered ∧ motive B) :
    ms.WellOrdered := by
  apply WellOrdered.coind_friend' (mul (basis := basis_hd :: basis_tl)) motive PreMS.WellOrdered
  · intros
    apply mul_WellOrdered <;> assumption
  · assumption
  · grind

theorem Approximates.mul_coind {f basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (motive : PreMS (basis_hd :: basis_tl) → (ℝ → ℝ) → Prop)
    (h_wo : ms.WellOrdered)
    (h_base : motive ms f)
    (h_step :
      ∀ (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ),
        motive ms f →
        ms = PreMS.nil ∧ f =ᶠ[atTop] 0 ∨
        ∃ exp coef tl fC,
          ms = PreMS.cons exp coef tl ∧ coef.Approximates fC ∧ majorated f basis_hd exp ∧
          ∃ (A B : PreMS (basis_hd :: basis_tl)) (fA fB : ℝ → ℝ), tl = A.mul B ∧
          f =ᶠ[atTop] (fun t ↦ basis_hd t ^ exp * fC t + fA t * fB t) ∧
          A.Approximates fA ∧ B.WellOrdered ∧ motive B fB) :
    ms.Approximates f := by
  let motive' (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) : Prop :=
    ∃ A B fA fB, ms = PreMS.mul A B ∧ A.Approximates fA ∧ f =ᶠ[atTop] fA * fB ∧
      B.WellOrdered ∧ motive B fB
  apply Approximates.add_coind motive'
  · use one _, ms, 1, f
    simp [one_mul', h_wo, h_base]
    apply one_Approximates h_basis
  rintro ms f ⟨A, B, fA, fB, rfl, hA, hf_eq, hB_wo, hB⟩
  cases A with
  | nil =>
    apply Approximates_nil at hA
    simp
    grw [hf_eq, hA]
    simp
  | cons A_exp A_coef A_tl =>
  specialize h_step _ _ hB
  obtain ⟨rfl, hfB⟩ | ⟨B_exp, B_coef, B_tl, fBC, rfl, hB_coef, hB_maj,
    X, Y, fX, fY, rfl, hfB, hX, hY_wo, hY⟩ := h_step
  · simp
    grw [hf_eq, hfB]
    simp
  right
  simp
  obtain ⟨fAC, hA_coef, hA_maj, hA_tl⟩ := Approximates_cons hA
  refine ⟨fAC * fBC, _, _, rfl, ?_⟩
  constructorm* _ ∧ _
  · apply mul_Approximates (h_basis.tail) hA_coef hB_coef
  · apply majorated_of_EventuallyEq hf_eq
    apply mul_majorated hA_maj hB_maj
    apply basis_head_eventually_pos h_basis
  simp [motive']
  refine ⟨_, mulMonomial_Approximates h_basis hA_tl hB_coef, ?_⟩
  use (PreMS.cons A_exp A_coef A_tl).mul X, Y
  constructor
  · rw [mul_assoc' hY_wo]
  refine ⟨_, mul_Approximates h_basis hA hX, fY, ?_, hY_wo, hY⟩
  push fun _ ↦ _
  grw [hf_eq, hfB]
  apply (basis_head_eventually_pos h_basis).mono
  intro t ht
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
  rw [Real.rpow_add ht]
  ring

end PreMS

end ComputeAsymptotics
