import Mathlib.Tactic.Tendsto.Multiseries.Operations.Merge

set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.longFile 0

namespace TendstoTactic

namespace PreMS

open Stream' Seq

mutual
  noncomputable def mul {basis : Basis} (a b : PreMS basis) : PreMS basis :=
    match basis with
    | [] => a * b
    | List.cons basis_hd basis_tl =>
      let ab := a.map fun (deg, coef) => mulMonomial b coef deg
      merge1 ab

  noncomputable def mulMonomial {basis_hd : _} {basis_tl : _} (b : PreMS (basis_hd :: basis_tl))
      (m_coef : PreMS basis_tl) (m_deg : ℝ)
      : PreMS (basis_hd :: basis_tl) :=
    b.map fun (deg, coef) => (m_deg + deg, mul m_coef coef)
end

--theorems
open Filter Asymptotics

@[simp]
theorem nil_mul {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    mul Seq.nil ms = .nil := by
  simp [mul, merge1_nil]

@[simp]
theorem mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    mul ms Seq.nil = .nil := by
  simp [mul, mulMonomial]
  apply ms.recOn <;> simp

@[simp]
theorem mulMonomial_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {m_deg : ℝ} {m_coef : PreMS basis_tl} :
    mulMonomial (basis_hd := basis_hd) Seq.nil m_coef m_deg = .nil := by
  simp [mulMonomial]

@[simp]
theorem mulMonomial_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg m_deg : ℝ} {x_coef m_coef : PreMS basis_tl}
    {x_tl : PreMS (basis_hd :: basis_tl)} :
    mulMonomial (basis_hd := basis_hd) (Seq.cons (x_deg, x_coef) x_tl) m_coef m_deg =
    .cons (m_deg + x_deg, mul m_coef x_coef) (mulMonomial x_tl m_coef m_deg) := by
  simp [mulMonomial]

@[simp]
theorem mulMonomial_leadingExp {basis_hd : _} {basis_tl : _} {b : PreMS (basis_hd :: basis_tl)}
    {m_coef : PreMS basis_tl} {m_deg : ℝ} :
    (mulMonomial b m_coef m_deg).leadingExp = m_deg + b.leadingExp := by
  apply b.recOn
  · simp
  · intro (b_deg, b_coef) b_tl
    simp

theorem mul_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl X Y : PreMS (basis_hd :: basis_tl)} (h : X.mul Y = .cons (deg, coef) tl) :
    ∃ X_deg X_coef X_tl Y_deg Y_coef Y_tl, X = .cons (X_deg, X_coef) X_tl ∧ Y = .cons (Y_deg, Y_coef) Y_tl := by
  revert h
  apply X.recOn
  · simp
  · intro (X_deg, X_coef) X_tl
    apply Y.recOn
    · simp
    · intro (Y_deg, Y_coef) Y_tl h
      use X_deg
      use X_coef
      use X_tl
      use Y_deg
      use Y_coef
      use Y_tl

@[simp]
theorem mul_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg y_deg : ℝ} {x_coef y_coef : PreMS basis_tl}
    {x_tl y_tl : PreMS (basis_hd :: basis_tl)} :
    mul (basis := basis_hd :: basis_tl) (Seq.cons (x_deg, x_coef) x_tl) (Seq.cons (y_deg, y_coef) y_tl) =
    Seq.cons (x_deg + y_deg, x_coef.mul y_coef) ((mulMonomial y_tl x_coef x_deg) +
      (x_tl.mul (Seq.cons (y_deg, y_coef) y_tl))) := by
  simp [mul]

-- Note: the condition `x.WellOrdered` is required. Counterexample: `x = [1, 2]`, `y = [1]` (well-ordered).
-- Then `lhs = [1, 2]` while `rhs = [2, 1]`.
@[simp]
theorem mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg : ℝ} {x_coef : PreMS basis_tl}
    {x_tl y : PreMS (basis_hd :: basis_tl)} (hx_wo : WellOrdered (basis := basis_hd :: basis_tl) (Seq.cons (x_deg, x_coef) x_tl)) :
    mul (Seq.cons (x_deg, x_coef) x_tl) y = (mulMonomial y x_coef x_deg) + (x_tl.mul y) := by
  by_cases hy : y.leadingExp = ⊥
  · rw [← leadingExp_eq_bot] at hy
    simp [hy]
  simp [mul]
  rw [merge1_cons]
  rw [← Seq.map_cons (x_deg, x_coef) x_tl (f := fun x ↦ y.mulMonomial x.2 x.1)]
  generalize (Seq.cons (x_deg, x_coef) x_tl) = x at hx_wo
  let motive : Seq (PreMS (basis_hd :: basis_tl)) → Prop := fun a =>
    ∃ (x : PreMS (basis_hd :: basis_tl)), a = (Seq.map (fun x ↦ y.mulMonomial x.2 x.1) x) ∧
    x.WellOrdered
  apply Seq.Sorted.coind motive (r := fun x1 x2 ↦ x1 > x2)
  · simp [motive]
    use x
  · intro hd tl ih
    simp only [motive] at ih
    obtain ⟨x, ih, hx_wo⟩ := ih
    revert ih hx_wo
    apply x.recOn
    · intro ih hx_wo
      simp at ih
    intro (x_deg, x_coef) x_tl ih hx_wo
    obtain ⟨hx_coef_wo, hx_comp, hx_tail_wo⟩ := WellOrdered_cons hx_wo
    simp [Seq.cons_eq_cons] at ih
    rw [ih.left, ih.right]
    constructor
    · revert hx_comp
      apply x_tl.recOn
      · intro hx_comp
        simp
      · intro (x_tl_deg, x_tl_coef) x_tl_tl hx_comp
        simp [lt_iff_lt]
        apply WithBot.add_lt_add_right hy
        simpa using hx_comp
    · simp only [motive]
      use x_tl

@[simp]
theorem mul_leadingExp {basis_hd : _} {basis_tl : _} {x y : PreMS (basis_hd :: basis_tl)} :
    (mul x y).leadingExp = x.leadingExp + y.leadingExp := by
  apply x.recOn
  · simp
  intro (x_deg, x_coef) x_tl
  apply y.recOn
  · simp
  intro (y_deg, y_coef) y_tl
  have : Seq.head (mul (basis := basis_hd :: basis_tl) (Seq.cons (x_deg, x_coef) x_tl) (Seq.cons (y_deg, y_coef) y_tl)) = .some ?_ := by
    simp
    exact Eq.refl _
  simp [leadingExp_of_head, this]

theorem mul_eq_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X Y : PreMS (basis_hd :: basis_tl)} (h : X.mul Y = Seq.nil) :
    X = .nil ∨ Y = .nil := by
  revert h
  apply X.recOn
  · simp
  · intro (X_deg, X_coef) X_tl
    apply Y.recOn
    · simp
    · intro (Y_deg, Y_coef) Y_tl h
      apply_fun Seq.head at h
      simp at h

-- TODO : can be proven without coinduction?
@[simp]
theorem mul_one' {basis : Basis} {ms : PreMS basis} : mul ms (one basis) = ms := by
  cases basis with
  | nil => simp [mul, one, const]
  | cons basis_hd basis_tl =>
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      x = y.mul (one (basis_hd :: basis_tl))
    apply Seq.Eq.coind motive
    · simp only [motive]
    · intro a b ih
      simp only [motive] at ih
      subst ih
      apply b.recOn
      · right
        simp
      · intro (deg, coef) tl
        left
        use ?_
        use ?_
        use ?_
        use ?_
        constructor
        · congr <;> exact Eq.refl _
        simp only [motive]
        · exact Eq.refl _
        · simp [one, const, Seq.cons_eq_cons]
          apply mul_one'

@[simp]
theorem one_mul' {basis : Basis} {ms : PreMS basis} : mul (one basis) ms = ms := by
  cases basis with
  | nil => simp [mul, one, const]
  | cons basis_hd basis_tl =>
    simp [one, const, mul]
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      x = y.mulMonomial (const 1 basis_tl) 0
    apply Seq.Eq.coind motive
    · simp only [motive]
    · intro x y ih
      subst ih
      apply y.recOn
      · simp
      · intro (deg, coef) tl
        left
        use ?_, ?_, ?_
        simp [Seq.cons_eq_cons]
        constructor
        · constructor <;> exact Eq.refl _
        · constructor
          · constructor
            · congr
              symm
              apply one_mul'
            · exact Eq.refl _
          · simp only [motive]

-- Is not needed so far
-- theorem mulMonomial_mulConst {basis_hd : ℝ → ℝ} {basis_tl : Basis}
--     {b : PreMS (basis_hd :: basis_tl)} {m_coef : PreMS basis_tl} {m_deg c : ℝ} :
--     (b.mulConst c).mulMonomial m_coef m_deg = (b.mulMonomial m_coef m_deg).mulConst c := by
--   sorry

mutual
  theorem mulMonomial_mulConst_coef {basis_hd : ℝ → ℝ} {basis_tl : Basis}
      {b : PreMS (basis_hd :: basis_tl)} {m_coef : PreMS basis_tl} {m_deg c : ℝ} :
      b.mulMonomial (m_coef.mulConst c) m_deg = (b.mulMonomial m_coef m_deg).mulConst c := by
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      ∃ (b : PreMS (basis_hd :: basis_tl)),
        x = b.mulMonomial (m_coef.mulConst c) m_deg ∧
        y = (b.mulMonomial m_coef m_deg).mulConst c
    apply Seq.Eq.coind motive
    · simp only [motive]
      use b
    · intro x y ih
      simp only [motive] at ih ⊢
      obtain ⟨b, hx, hy⟩ := ih
      subst hx hy
      apply b.recOn
      · simp
      intro (b_deg, b_coef) b_tl
      left
      use ?_, ?_, ?_
      constructor
      · simp
        exact Eq.refl _
      constructor
      · simp [Seq.cons_eq_cons]
        constructor
        · rw [mul_mulConst]
        · exact Eq.refl _
      use b_tl

  theorem mul_mulConst {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
      (X.mulConst c).mul Y = (X.mul Y).mulConst c := by
    cases basis with
    | nil => simp [mul, mulConst]; ring
    | cons basis_hd basis_tl =>
      let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
        ∃ (X Y S : PreMS (basis_hd :: basis_tl)), a = S + (X.mulConst c).mul Y ∧ b = S + (X.mul Y).mulConst c
      apply Seq.Eq.coind_strong motive
      · simp only [motive]
        use X, Y, 0
        simp
      · intro a b ih
        simp only [motive] at ih ⊢
        obtain ⟨X, Y, S, ha, hb⟩ := ih
        subst ha hb
        apply X.recOn
        · simp
        intro (X_deg, X_coef) X_tl
        apply Y.recOn
        · simp
        intro (Y_deg, Y_coef) Y_tl
        right
        apply S.recOn
        · use ?_, ?_, ?_
          constructor
          · simp
            exact Eq.refl _
          constructor
          · simp [Seq.cons_eq_cons]
            constructor
            · rw [mul_mulConst]
            · exact Eq.refl _
          use ?_, ?_, ?_
          constructor
          · exact Eq.refl _
          · rw [add_mulConst, mulMonomial_mulConst_coef]
        intro (S_deg, S_coef) S_tl
        simp only [mulConst_cons, mul_cons_cons]
        rw [add_cons_cons, add_cons_cons]
        split_ifs
        · use ?_, ?_, ?_
          constructor
          · exact Eq.refl _
          constructor
          · exact Eq.refl _
          use Seq.cons (X_deg, X_coef) X_tl, Seq.cons (Y_deg, Y_coef) Y_tl, S_tl
          constructor
          · simp
          · simp
        · use ?_, ?_, ?_
          constructor
          · exact Eq.refl _
          constructor
          · simp [Seq.cons_eq_cons]
            constructor
            · rw [mul_mulConst]
            · exact Eq.refl _
          use ?_, ?_, ?_
          constructor
          · rw [← add_assoc]
            exact Eq.refl _
          · rw [add_assoc]
            rw [add_mulConst, mulMonomial_mulConst_coef]
        · use ?_, ?_, ?_ -- Copypaste
          constructor
          · exact Eq.refl _
          constructor
          · simp [Seq.cons_eq_cons]
            constructor
            · rw [mul_mulConst]
            · exact Eq.refl _
          use ?_, ?_, ?_
          constructor
          · rw [← add_assoc]
            exact Eq.refl _
          · rw [add_assoc]
            rw [add_mulConst, mulMonomial_mulConst_coef]
end

mutual
  @[simp]
  theorem add_mulMonomial_right {basis_hd : _} {basis_tl : _} {b : PreMS (basis_hd :: basis_tl)}
      {m_coef1 m_coef2 : PreMS basis_tl} {m_deg : ℝ} :
      (mulMonomial b (m_coef1 + m_coef2) m_deg) = (mulMonomial b m_coef1 m_deg) + (mulMonomial b m_coef2 m_deg) := by
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      ∃ (b : PreMS (basis_hd :: basis_tl)),
      x = b.mulMonomial (m_coef1 + m_coef2) m_deg ∧
      y = b.mulMonomial m_coef1 m_deg + b.mulMonomial m_coef2 m_deg
    apply Seq.Eq.coind motive
    · simp [motive]
      use b
    · intro x y ih
      simp only [motive] at ih
      obtain ⟨b, hx, hy⟩ := ih
      subst hx hy
      apply b.recOn
      · right
        simp
      · intro (b_deg, b_coef) b_tl
        left
        use ?_, ?_, ?_
        constructor
        · simp [Seq.cons_eq_cons]
          constructor
          · exact Eq.refl _
          · exact Eq.refl _
        constructor
        · simp [add_cons_cons, Seq.cons_eq_cons]
          constructor
          · symm
            apply add_mul_right'
          · exact Eq.refl _
        simp only [motive]
        use ?_
        constructor
        · exact Eq.refl _
        · rfl

  -- TODO : lots of similar cases. Can simplify?
  @[simp]
  theorem add_mul_right' {basis : Basis} {X Y Z : PreMS basis} :
      (X + Y).mul Z = (X.mul Z) + (Y.mul Z) := by
    cases basis with
    | nil => simp [mul]; ring
    | cons basis_hd basis_tl =>
      apply Z.recOn
      · simp
      intro (Z_deg, Z_coef) Z_tl
      let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
        ∃ (S X Y : PreMS (basis_hd :: basis_tl)),
          a = S + ((X + Y).mul (.cons (Z_deg, Z_coef) Z_tl)) ∧
          b = S + ((X.mul (.cons (Z_deg, Z_coef) Z_tl)) + (Y.mul (.cons (Z_deg, Z_coef) Z_tl)))
      apply Seq.Eq.coind_strong motive
      · simp only [motive]
        use 0, X, Y
        simp
      · intro a b ih
        obtain ⟨S, X, Y, ha, hb⟩ := ih
        subst ha hb
        apply X.recOn
        · left
          simp
        intro (X_deg, X_coef) X_tl
        apply Y.recOn
        · left
          simp
        intro (Y_deg, Y_coef) Y_tl
        right
        apply S.recOn
        · simp
          rw [add_cons_cons, add_cons_cons]
          split_ifs <;> (try exfalso; linarith)
          · use ?_, ?_, ?_
            constructor
            · simp [Seq.cons_eq_cons]
              constructor
              · constructor <;> exact Eq.refl _
              · exact Eq.refl _
            use ?_
            constructor
            · simp [Seq.cons_eq_cons]
              exact Eq.refl _
            simp [motive]
            use ?_, ?_, ?_
            constructor
            · exact Eq.refl _
            · simp
              abel
          · use ?_, ?_, ?_
            constructor
            · simp [Seq.cons_eq_cons]
              constructor
              · constructor <;> exact Eq.refl _
              · exact Eq.refl _
            use ?_
            constructor
            · exact Eq.refl _
            simp [motive]
            use ?_, ?_, ?_
            constructor
            · exact Eq.refl _
            · simp
              abel
          · have : X_deg = Y_deg := by linarith
            subst this
            use ?_, ?_, ?_
            constructor
            · simp [Seq.cons_eq_cons]
              constructor
              · constructor <;> exact Eq.refl _
              · exact Eq.refl _
            use ?_
            constructor
            · simp [Seq.cons_eq_cons]
              constructor
              · symm
                apply add_mul_right'
              · exact Eq.refl _
            simp [motive]
            use ?_, ?_, ?_
            constructor
            · exact Eq.refl _
            · rw [add_mulMonomial_right]
              abel
        · intro (S_deg, S_coef) S_tl
          simp only [mul_cons_cons]
          rw [add_cons_cons, add_cons_cons]
          split_ifs <;> (first | exfalso; linarith | rw [add_cons_cons]; split_ifs)
          · use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp [motive]
            use ?_, (.cons (X_deg, X_coef) X_tl), (.cons (Y_deg, Y_coef) Y_tl)
            constructor
            · congr
              · exact Eq.refl _
              · rw [add_cons_cons]
                split_ifs
                simp
            · simp
              rw [add_cons_cons]
              split_ifs
              abel
          · use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp [motive]
            use (.cons (S_deg, S_coef) S_tl) + mulMonomial Z_tl X_coef X_deg, X_tl, (.cons (Y_deg, Y_coef) Y_tl)
            constructor
            · abel
            · simp
              abel
          · use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp [motive]
            use mulMonomial Z_tl X_coef X_deg + S_tl, X_tl, (.cons (Y_deg, Y_coef) Y_tl)
            constructor
            · abel
            · simp
              abel

          · use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp [motive]
            use ?_, (.cons (X_deg, X_coef) X_tl), (.cons (Y_deg, Y_coef) Y_tl)
            constructor
            · congr
              · exact Eq.refl _
              · rw [add_cons_cons]
                split_ifs
                simp
            · simp
              rw [add_cons_cons]
              split_ifs
              abel
          · use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp [motive]
            use (.cons (S_deg, S_coef) S_tl) + mulMonomial Z_tl Y_coef Y_deg, (.cons (X_deg, X_coef) X_tl), Y_tl
            constructor
            · abel
            · simp
              abel
          · use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp [motive]
            use mulMonomial Z_tl Y_coef Y_deg + S_tl, (.cons (X_deg, X_coef) X_tl), Y_tl
            constructor
            · abel
            · simp
              abel

          · use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp [motive]
            use ?_, (.cons (X_deg, X_coef) X_tl), (.cons (Y_deg, Y_coef) Y_tl)
            constructor
            · congr
              · exact Eq.refl _
              · rw [add_cons_cons]
                split_ifs
                simp
            · simp
              rw [add_cons_cons]
              split_ifs
              abel
          · have : X_deg = Y_deg := by linarith
            subst this
            use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · congr
              · symm
                apply add_mul_right'
              · exact Eq.refl _
            simp [motive]
            use (.cons (S_deg, S_coef) S_tl) + mulMonomial Z_tl X_coef X_deg + mulMonomial Z_tl Y_coef X_deg, X_tl, Y_tl
            constructor
            · rw [add_mulMonomial_right]
              abel
            · abel
          · have : X_deg = Y_deg := by linarith
            subst this
            have : S_deg = X_deg + Z_deg := by linarith
            subst this
            use ?_, ?_, ?_
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs
              exact Eq.refl _
            constructor
            · congr
              · symm
                apply add_mul_right'
              · exact Eq.refl _
            simp [motive]
            use mulMonomial Z_tl X_coef X_deg + mulMonomial Z_tl Y_coef X_deg + S_tl, X_tl, Y_tl
            constructor
            · rw [add_mulMonomial_right]
              abel
            · abel
end

mutual
  @[simp]
  theorem add_mulMonomial_left {basis_hd : _} {basis_tl : _} {b1 b2 : PreMS (basis_hd :: basis_tl)}
      {m_coef : PreMS basis_tl} {m_deg : ℝ}
      (m_wo : m_coef.WellOrdered) :
      (mulMonomial (b1 + b2) m_coef m_deg) = (mulMonomial b1 m_coef m_deg) + (mulMonomial b2 m_coef m_deg) := by
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      ∃ (b1 b2 : PreMS (basis_hd :: basis_tl)),
      x = (b1 + b2).mulMonomial m_coef m_deg ∧
      y = b1.mulMonomial m_coef m_deg + b2.mulMonomial m_coef m_deg
    apply Seq.Eq.coind_strong motive
    · simp [motive]
      use b1, b2
    · intro x y ih
      simp only [motive] at ih
      obtain ⟨b1, b2, hx, hy⟩ := ih
      subst hx hy
      apply b1.recOn
      · left
        simp
      intro (b1_deg, b1_coef) b1_tl
      apply b2.recOn
      · left
        simp
      intro (b2_deg, b2_coef) b2_tl
      right
      rw [add_cons_cons]
      split_ifs with h1 h2
      · use ?_, ?_, ?_
        constructor
        · simp only [mulMonomial_cons, Seq.cons_eq_cons]
          constructor
          · exact Eq.refl _
          · exact Eq.refl _
        constructor
        · simp [add_cons_cons]
          split_ifs
          congr
          exact Eq.refl _
        simp only [motive]
        use ?_, ?_
        constructor
        · exact Eq.refl _
        · simp
      · use ?_, ?_, ?_
        constructor
        · simp only [mulMonomial_cons, Seq.cons_eq_cons]
          constructor
          · exact Eq.refl _
          · exact Eq.refl _
        constructor
        · simp [add_cons_cons]
          split_ifs
          congr
          exact Eq.refl _
        simp only [motive]
        use ?_, ?_
        constructor
        · exact Eq.refl _
        · simp
      · have : b1_deg = b2_deg := by linarith
        subst this
        use ?_, ?_, ?_
        constructor
        · simp only [mulMonomial_cons, Seq.cons_eq_cons]
          constructor
          · exact Eq.refl _
          · exact Eq.refl _
        constructor
        · simp [add_cons_cons]
          congr
          · symm
            apply add_mul_left' m_wo
          · exact Eq.refl _
        simp only [motive]
        use ?_, ?_
        constructor
        · exact Eq.refl _
        · simp

  -- Note: `Z.WellOrdered` is necessary. Counterexample: `X = [0]`, `Y = [1]`, `Z = [0, 2]`.
  -- Then `lhs = [0, 2] * [1, 0] = [1, 3, 2, 0]` while `rhs = [0, 2] + [1, 3] = [1, 3, 0, 2]`.
  -- TODO : lots of similar cases. Can simplify?
  @[simp]
  theorem add_mul_left' {basis : Basis} {X Y Z : PreMS basis}
      (hZ_wo : Z.WellOrdered) :
      Z.mul (X + Y) = (Z.mul X) + (Z.mul Y) := by
    cases basis with
    | nil => simp [mul]; ring
    | cons basis_hd basis_tl =>
      apply X.recOn
      · simp
      intro (X_deg, X_coef) X_tl
      apply Y.recOn
      · simp
      intro (Y_deg, Y_coef) Y_tl
      let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
        ∃ (Z S : PreMS (basis_hd :: basis_tl)),
          a = S + Z.mul (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) (Seq.cons (Y_deg, Y_coef) Y_tl)) ∧
          b = S + (Z.mul (Seq.cons (X_deg, X_coef) X_tl)) + Z.mul (Seq.cons (Y_deg, Y_coef) Y_tl) ∧
          Z.WellOrdered
      apply Seq.Eq.coind_strong motive
      · simp only [motive]
        use Z, 0
        simpa
      · intro a b ih
        simp only [motive] at ih
        obtain ⟨Z, S, ha, hb, hZ_wo⟩ := ih
        subst ha hb
        revert hZ_wo
        apply Z.recOn
        · intro
          left
          simp
        intro (Z_deg, Z_coef) Z_tl hZ_wo
        obtain ⟨hZ_coef_wo, hZ_comp, hZ_tl_wo⟩ := WellOrdered_cons hZ_wo
        right
        apply S.recOn
        · rw [add_cons_cons]
          split_ifs
          · use ?_, ?_, ?_
            constructor
            · simp
              exact Eq.refl _
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs <;> (try exfalso; linarith)
              exact Eq.refl _
            simp only [motive]
            use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl (Seq.cons (Y_deg, Y_coef) Y_tl)).mulMonomial Z_coef Z_deg
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · conv => rhs; rw [add_mulMonomial_left hZ_coef_wo]
              conv => lhs; rw [← mul_cons_cons, mul_cons hZ_wo]
              · abel
            · exact hZ_tl_wo
          · use ?_, ?_, ?_
            constructor
            · simp
              exact Eq.refl _
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs <;> (try exfalso; linarith)
              exact Eq.refl _
            simp only [motive]
            use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) Y_tl).mulMonomial Z_coef Z_deg
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · conv => rhs; rw [add_mulMonomial_left hZ_coef_wo]
              conv => lhs; rw [← mul_cons_cons, mul_cons hZ_wo]
              · abel
            · exact hZ_tl_wo
          · use ?_, ?_, ?_
            constructor
            · simp
              exact Eq.refl _
            constructor
            · simp
              rw [add_cons_cons]
              split_ifs <;> (try exfalso; linarith)
              congr
              · symm
                exact add_mul_left' hZ_coef_wo
              · exact Eq.refl _
            simp only [motive]
            use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl Y_tl).mulMonomial Z_coef Z_deg
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · conv => rhs; rw [add_mulMonomial_left hZ_coef_wo]
              · abel
            · exact hZ_tl_wo
        · intro (S_deg, S_coef) S_tl
          rw [add_cons_cons]
          split_ifs <;> (
            rw [mul_cons_cons, mul_cons_cons, mul_cons_cons, add_cons_cons];
            split_ifs <;> (
              conv => arg 1; ext; arg 1; ext; arg 1; ext; arg 2; arg 1; lhs; rw [add_assoc]
              rw [add_cons_cons]
              split_ifs <;> (try exfalso; linarith)
              rw [add_cons_cons]
              split_ifs
              use ?_, ?_, ?_
              constructor
              · exact Eq.refl _
              constructor
              · first | exact Eq.refl _ | rw [add_mul_left' hZ_coef_wo]; exact Eq.refl _
              simp only [motive]
            )
          )
          · use (Seq.cons (Z_deg, Z_coef) Z_tl), S_tl
            constructor
            · rw [add_cons_cons]
              split_ifs
              rw [mul_cons_cons]
            constructor
            · simp only [mul_cons_cons]
              conv => rhs; rw [add_assoc]
              rw [add_cons_cons]
              split_ifs
              rfl
            · assumption
          · use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl (Seq.cons (Y_deg, Y_coef) Y_tl)).mulMonomial Z_coef Z_deg + (Seq.cons (S_deg, S_coef) S_tl)
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · rw [add_mulMonomial_left hZ_coef_wo]
              rw [← mul_cons_cons, mul_cons hZ_wo]
              abel
            · assumption
          · have : S_deg = Z_deg + X_deg := by linarith
            subst this
            use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl (Seq.cons (Y_deg, Y_coef) Y_tl)).mulMonomial Z_coef Z_deg + S_tl
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · rw [add_mulMonomial_left hZ_coef_wo]
              rw [← mul_cons_cons, mul_cons hZ_wo]
              abel
            · assumption

          · use (Seq.cons (Z_deg, Z_coef) Z_tl), S_tl
            constructor
            · rw [add_cons_cons]
              split_ifs
              rw [mul_cons_cons]
            constructor
            · simp only [mul_cons_cons]
              conv => rhs; rw [add_assoc]
              rw [add_cons_cons]
              split_ifs
              rfl
            · assumption
          · use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) Y_tl).mulMonomial Z_coef Z_deg + (Seq.cons (S_deg, S_coef) S_tl)
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · rw [add_mulMonomial_left hZ_coef_wo]
              rw [← mul_cons_cons, mul_cons hZ_wo]
              abel
            · assumption
          · have : S_deg = Z_deg + Y_deg := by linarith
            subst this
            use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) Y_tl).mulMonomial Z_coef Z_deg + S_tl
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · rw [add_mulMonomial_left hZ_coef_wo]
              rw [← mul_cons_cons, mul_cons hZ_wo]
              abel
            · assumption

          · use (Seq.cons (Z_deg, Z_coef) Z_tl), S_tl
            constructor
            · rw [add_cons_cons]
              split_ifs
              rw [mul_cons_cons]
            constructor
            · simp only [mul_cons_cons]
              conv => rhs; rw [add_assoc]
              rw [add_cons_cons]
              split_ifs
              rfl
            · assumption
          · have : X_deg = Y_deg := by linarith
            subst this
            use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl Y_tl).mulMonomial Z_coef Z_deg + (Seq.cons (S_deg, S_coef) S_tl)
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · rw [add_mulMonomial_left hZ_coef_wo]
              abel
            · assumption
          · have : X_deg = Y_deg := by linarith
            subst this
            have : S_deg = Z_deg + X_deg := by linarith
            subst this
            use Z_tl, (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl Y_tl).mulMonomial Z_coef Z_deg + S_tl
            constructor
            · rw [add_cons_cons]
              split_ifs
              abel
            constructor
            · rw [add_mulMonomial_left hZ_coef_wo]
              abel
            · assumption

end

mutual
  @[simp]
  theorem mulMonomial_mul {basis_hd : _} {basis_tl : _} {b : PreMS (basis_hd :: basis_tl)}
      {m_coef1 m_coef2 : PreMS basis_tl} {m_deg1 m_deg2 : ℝ}
      (h_coef2_wo : m_coef2.WellOrdered) :
      (b.mulMonomial m_coef1 m_deg1).mulMonomial m_coef2 m_deg2 =
      b.mulMonomial (m_coef2.mul m_coef1) (m_deg2 + m_deg1) := by
    simp [mulMonomial]
    rw [← Seq.map_comp]
    congr
    eta_expand
    simp
    ext x
    · obtain ⟨deg, coef⟩ := x
      simp
      ring
    · obtain ⟨deg, coef⟩ := x
      simp
      symm
      apply mul_assoc'
      exact h_coef2_wo

  @[simp]
  theorem mul_mulMonomial {basis_hd : _} {basis_tl : _} {b c : PreMS (basis_hd :: basis_tl)}
      {m_coef : PreMS basis_tl} {m_deg : ℝ}
      (hm_wo : m_coef.WellOrdered) :
      (b.mulMonomial m_coef m_deg).mul c =
      (b.mul c).mulMonomial m_coef m_deg := by
    apply c.recOn
    · simp
    intro (c_deg, c_coef) c_tl
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      ∃ (S b : PreMS (basis_hd :: basis_tl)),
        x = S + (b.mulMonomial m_coef m_deg).mul (Seq.cons (c_deg, c_coef) c_tl) ∧
        y = S + (b.mul (Seq.cons (c_deg, c_coef) c_tl)).mulMonomial m_coef m_deg
    apply Seq.Eq.coind_strong motive
    · use 0, b
      simp
    · intro x y ih
      simp only [motive] at ih
      obtain ⟨S, b, hx, hy⟩ := ih
      subst hx hy
      apply b.recOn
      · left
        simp
      intro (b_deg, b_coef) b_tl
      right
      apply S.recOn
      · use ?_, ?_, ?_
        simp
        constructor
        · exact Eq.refl _
        constructor
        · congr 2
          · abel
          · symm
            apply mul_assoc'
            exact hm_wo
          · exact Eq.refl _
        simp only [motive]
        use mulMonomial c_tl (m_coef.mul b_coef) (m_deg + b_deg), b_tl
        constructor
        · simp
        · rw [add_mulMonomial_left hm_wo, mulMonomial_mul hm_wo]
      · intro (S_deg, S_coef) S_tl
        simp only [mulMonomial_cons, mul_cons_cons]
        rw [add_cons_cons, ← add_assoc m_deg, add_cons_cons]
        split_ifs
        · use ?_, ?_, ?_
          constructor
          · congr
            · exact Eq.refl _
            · exact Eq.refl _
          constructor
          · congr
            exact Eq.refl _
          simp only [motive]
          use S_tl, (.cons (b_deg, b_coef) b_tl)
          constructor
          · simp
          · simp
            abel_nf
        · use ?_, ?_, ?_
          constructor
          · congr
            · exact Eq.refl _
            · exact Eq.refl _
          constructor
          · congr 2
            · symm
              apply mul_assoc' hm_wo
            · exact Eq.refl _
          simp only [motive]
          use mulMonomial c_tl (m_coef.mul b_coef) (m_deg + b_deg) + (.cons (S_deg, S_coef) S_tl)
          use b_tl
          constructor
          · abel
          · rw [add_mulMonomial_left hm_wo, mulMonomial_mul hm_wo]
            abel
        · use ?_, ?_, ?_
          constructor
          · congr
            · exact Eq.refl _
            · exact Eq.refl _
          constructor
          · congr 3
            · symm
              apply mul_assoc' hm_wo
            · exact Eq.refl _
          simp only [motive]
          use mulMonomial c_tl (m_coef.mul b_coef) (m_deg + b_deg) + S_tl
          use b_tl
          constructor
          · abel
          · rw [add_mulMonomial_left hm_wo, mulMonomial_mul hm_wo]
            abel

  -- Note: `X.WellOrdered` is necessary. Counterexample: `basis = [x, y]`.
  -- `X = x^0 * (y^0 + y^2)`
  -- `Y = x^0 * y^0 + x^(-1) * y^1` (well-ordered)
  -- `Z = x^2 * y^(-1) + x^1 * y^1` (well-ordered)
  -- Then
  -- `lhs = x^2 * (y^(-1) + y) + x^1 * (y^1 + y^3 + y^0 + y^2) + x^0 * (y^2 + y^4)`
  -- `rhs = x^2 * (y^(-1) + y) + x^1 * (y^1 + y^3 + y^2 + y^0) + x^0 * (y^2 + y^4)`
  -- There is a difference in the second coefficient.
  -- It is enough, however, if all coefs of `X` is well-ordered, i.e. `X.all WellOrdered`
  @[simp]
  theorem mul_assoc' {basis : Basis} {X Y Z : PreMS basis}
      (hX_wo : X.WellOrdered) :
      (X.mul Y).mul Z = X.mul (Y.mul Z) := by
    cases basis with
    | nil => simp [mul]; ring
    | cons basis_hd basis_tl =>
      apply Y.recOn
      · simp
      intro (Y_deg, Y_coef) Y_tl
      apply Z.recOn
      · simp
      intro (Z_deg, Z_coef) Z_tl
      let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
        ∃ (X S : PreMS (basis_hd :: basis_tl)),
          a = S + (X.mul (Seq.cons (Y_deg, Y_coef) Y_tl)).mul (Seq.cons (Z_deg, Z_coef) Z_tl) ∧
          b = S + X.mul (mul (Seq.cons (Y_deg, Y_coef) Y_tl) (Seq.cons (Z_deg, Z_coef) Z_tl)) ∧
          X.WellOrdered
      apply Seq.Eq.coind_strong motive
      · simp only [motive]
        use X, 0
        simp
        exact hX_wo
      · intro a b ih
        obtain ⟨X, S, ha, hb, hX_wo⟩ := ih
        subst ha hb
        revert hX_wo
        apply X.recOn
        · intro
          simp
        intro (X_deg, X_coef) X_tl hX_wo
        obtain ⟨hX_coef_wo, _, hX_tl_wo⟩ := WellOrdered_cons hX_wo
        right
        apply S.recOn
        · use ?_, ?_, ?_
          simp only [mul_cons_cons, nil_add]
          constructor
          · exact Eq.refl _
          constructor
          · congr 2
            · ring
            · rw [mul_assoc' hX_coef_wo]
            · exact Eq.refl _
          simp only [motive]
          use X_tl, mulMonomial Z_tl (X_coef.mul Y_coef) (X_deg + Y_deg) + (mulMonomial (mul (basis := basis_hd :: basis_tl) Y_tl (Seq.cons (Z_deg, Z_coef) Z_tl)) X_coef X_deg)
          constructor
          · rw [add_mul_right', mul_mulMonomial hX_coef_wo]
            abel
          constructor
          · rw [add_mulMonomial_left hX_coef_wo, mulMonomial_mul hX_coef_wo, mul_cons_cons]
          · exact hX_tl_wo
        · intro (S_deg, S_coef) S_tl
          simp only [mul_cons_cons, add_cons_cons, ← add_assoc X_deg Y_deg Z_deg]
          split_ifs
          · use ?_, ?_, ?_
            constructor
            · exact Eq.refl _
            constructor
            · exact Eq.refl _
            simp only [motive]
            use Seq.cons (X_deg, X_coef) X_tl, S_tl
            constructor
            · simp
            constructor
            · simp [← add_assoc X_deg Y_deg Z_deg]
            · exact hX_wo
          · use ?_, ?_, ?_
            constructor
            · exact Eq.refl _
            constructor
            · congr 2
              · rw [mul_assoc' hX_coef_wo]
              · exact Eq.refl _
            simp only [motive]
            use X_tl, mulMonomial Z_tl (X_coef.mul Y_coef) (X_deg + Y_deg) + (mulMonomial (mul (basis := basis_hd :: basis_tl) Y_tl (Seq.cons (Z_deg, Z_coef) Z_tl)) X_coef X_deg) + Seq.cons (S_deg, S_coef) S_tl
            constructor
            · rw [add_mul_right', mul_mulMonomial hX_coef_wo]
              abel
            constructor
            · rw [add_mulMonomial_left hX_coef_wo, mulMonomial_mul hX_coef_wo, mul_cons_cons]
              abel
            · exact hX_tl_wo
          · use ?_, ?_, ?_
            constructor
            · exact Eq.refl _
            constructor
            · congr 2
              · rw [mul_assoc' hX_coef_wo]
              · exact Eq.refl _
            simp only [motive]
            use X_tl, mulMonomial Z_tl (X_coef.mul Y_coef) (X_deg + Y_deg) + (mulMonomial (mul (basis := basis_hd :: basis_tl) Y_tl (Seq.cons (Z_deg, Z_coef) Z_tl)) X_coef X_deg) + S_tl
            constructor
            · rw [add_mul_right', mul_mulMonomial hX_coef_wo]
              abel
            constructor
            · rw [add_mulMonomial_left hX_coef_wo, mulMonomial_mul hX_coef_wo, mul_cons_cons]
              abel
            · exact hX_tl_wo
end

-- Is not needed so far
-- @[simp]
-- theorem merge1_mul_comm_left {basis_hd : ℝ → ℝ} {basis_tl : Basis}
--     {s : Seq (PreMS (basis_hd :: basis_tl))} {X : PreMS (basis_hd :: basis_tl)} :
--     merge1 (s.map (X.mul ·)) = X.mul (merge1 s) := by
--   sorry

@[simp]
theorem merge1_mul_comm_right {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s : Seq (PreMS (basis_hd :: basis_tl))} {X : PreMS (basis_hd :: basis_tl)} :
    merge1 (s.map (·.mul X)) = (merge1 s).mul X := by
  apply X.recOn
  · simp
    apply s.recOn
    · simp
    · simp
  intro (X_deg, X_coef) X_tl
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
    ∃ Y s,
      a = Y + merge1 (Seq.map (fun x ↦ x.mul (.cons (X_deg, X_coef) X_tl)) s) ∧
      b = Y + (merge1 s).mul (.cons (X_deg, X_coef) X_tl)
  apply Seq.Eq.coind_strong motive
  · simp only [motive]
    use 0, s
    simp
  · intro a b ih
    simp only [motive] at ih ⊢
    obtain ⟨Y, s, ha, hb⟩ := ih
    subst ha hb
    apply s.recOn
    · simp
    intro s_hd s_tl
    apply s_hd.recOn
    · simp
    intro (s_hd_deg, s_hd_coef) s_hd_tl
    right
    apply Y.recOn
    · use ?_, ?_, ?_
      constructor
      · simp
        exact Eq.refl _
      constructor
      · simp
        exact Eq.refl _
      use ?_, s_tl
      constructor
      · exact Eq.refl _
      · rw [add_mul_right']
        abel
    intro (Y_deg, Y_coef) Y_tl
    simp only [Seq.map_cons, mul_cons_cons, merge1_cons_head_cons]
    rw [add_cons_cons, add_cons_cons]
    split_ifs
    · use ?_, ?_, ?_
      constructor
      · exact Eq.refl _
      constructor
      · exact Eq.refl _
      use ?_, Seq.cons (Seq.cons (s_hd_deg, s_hd_coef) s_hd_tl) s_tl
      constructor
      · rw [Seq.map_cons, mul_cons_cons, merge1_cons_head_cons]
        exact Eq.refl _
      · simp
    · use ?_, ?_, ?_
      constructor
      · exact Eq.refl _
      constructor
      · exact Eq.refl _
      use ?_, s_tl
      constructor
      · rw [← add_assoc]
        exact Eq.refl _
      · rw [add_mul_right']
        abel
    · use ?_, ?_, ?_
      constructor
      · exact Eq.refl _
      constructor
      · exact Eq.refl _
      use ?_, s_tl
      constructor
      · rw [← add_assoc]
        exact Eq.refl _
      · rw [add_mul_right']
        abel

noncomputable def longAdd {basis : Basis} {k : ℕ} (args : Fin k → PreMS basis) : PreMS basis :=
  match k with
  | 0 => 0
  | m + 1 =>
    let args' : Fin m → PreMS basis := fun i ↦ args i.castSucc
    (longAdd args') + (args m)

-- TODO: to another file
universe u v in
@[simp]
theorem Finset.sup'_eq_bot {α : Type u} {β : Type v} [SemilatticeSup α] [OrderBot α] {s : Finset β}
    {H : s.Nonempty} {f : β → α} :
    s.sup' H f = ⊥ ↔ ∀ b ∈ s, f b = ⊥ := by
  constructor
  · intro h b hb
    have := Finset.le_sup' (f := f) hb
    rw [h] at this
    exact le_bot_iff.mp this
  · intro h
    apply le_bot_iff.mp
    apply (Finset.sup'_le_iff H f).mpr
    intro b hb
    exact (h _ hb).le

theorem longAdd_one {basis : Basis} {args : Fin 1 → PreMS basis} : longAdd args = args 0 := by
  simp [longAdd]

theorem longAdd_zeros {basis : Basis} {k : ℕ} : longAdd (fun (i : Fin k) ↦ 0) = (0 : PreMS basis) := by
  induction k with
  | zero => simp [longAdd]
  | succ k ih => simp [longAdd, ih]

theorem longAdd_nils {basis_hd : ℝ → ℝ} {basis_tl : Basis} {k : ℕ} : longAdd (fun (i : Fin k) ↦ Seq.nil) = (0 : PreMS (basis_hd :: basis_tl)) := by
  rw [show Seq.nil = (0 : PreMS (basis_hd :: basis_tl)) by rfl, longAdd_zeros]

noncomputable def longAdd' {basis_hd : ℝ → ℝ} {basis_tl : Basis} {k : ℕ}
    (args : Fin k → PreMS (basis_hd :: basis_tl)) : PreMS (basis_hd :: basis_tl) :=
  match k with
  | 0 => .nil
  | k + 1 =>
    have inst : Nonempty (Fin (k + 1)) := by apply Fin.pos_iff_nonempty.mp (by omega)
    let deg? := Finset.univ.sup' Finset.univ_nonempty (fun i ↦ (args i).leadingExp)
    match deg? with
    | none => .nil -- ⊥
    | some deg =>
      let coef_tl_args : (Fin (k + 1)) → (PreMS basis_tl × PreMS (basis_hd :: basis_tl)) := fun i =>
        if h : (args i).leadingExp = deg then
          (leadingExp_eq_coe h).choose
        else
          (0, args i)

      let coef := longAdd fun i ↦(coef_tl_args i).1
      let tl := longAdd fun i ↦(coef_tl_args i).2
      .cons (deg, coef) tl

theorem longAdd_eq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {k : ℕ}
    {args : Fin k → PreMS (basis_hd :: basis_tl)} :
    longAdd args = longAdd' args := by
  induction k with
  | zero => simp [longAdd, longAdd']; rfl
  | succ k ih =>
    simp [longAdd']
    -- наводим красоту
    generalize_proofs inst _
    generalize h_deg : (Finset.univ.sup' inst fun i ↦ (args i).leadingExp) = deg?
    -- навели
    cases deg? with
    | bot =>
      simp
      apply Finset.sup'_eq_bot.mp at h_deg
      simp at h_deg
      have : args = fun _ ↦ .nil := by
        ext1 i
        specialize h_deg i
        exact leadingExp_eq_bot.mpr h_deg
      rw [this]
      exact longAdd_nils
    | coe deg =>
      -- наводим красоту
      simp
      generalize_proofs h_coefs_tls
      generalize h_coef_tl_args : (fun i ↦ (if h : (args i).leadingExp = ↑deg then (h_coefs_tls i h).choose else (0, args i))) = coef_tl_args
      generalize h_coef : longAdd (fun i ↦ (coef_tl_args i).1) = coef
      generalize h_tl : longAdd (fun i ↦ (coef_tl_args i).2) = tl
      rw [show longAdd (fun i ↦ (if h : (args i).leadingExp = ↑deg then (h_coefs_tls i h).choose else (0, args i)).1) =
        coef by rw [← h_coef, ← h_coef_tl_args]]
      rw [show longAdd (fun i ↦ (if h : (args i).leadingExp = ↑deg then (h_coefs_tls i h).choose else (0, args i)).2) =
        tl by rw [← h_tl, ← h_coef_tl_args]]
      -- навели
      simp only [longAdd]
      rw [ih]
      cases k with
      | zero =>
        simp [longAdd']
        simp at h_deg
        simp [longAdd, ← h_coef_tl_args, h_deg] at h_coef h_tl
        rw [← h_coef, ← h_tl]
        apply (h_coefs_tls 0 h_deg).choose_spec
      | succ k =>
        simp only [longAdd']
        -- наводим красоту
        generalize_proofs inst2 h_coefs_tls_
        generalize h_deg' : (Finset.univ.sup' inst2 fun i ↦ (args i.castSucc).leadingExp) = deg?'
        -- навели
        cases deg?' with
        | bot =>
          simp only [nil_add]
          apply Finset.sup'_eq_bot.mp at h_deg'
          simp at h_deg'

          have h_last : (args (Fin.last (k + 1))).leadingExp = deg := by
            have := Finset.exists_mem_eq_sup' inst fun i ↦ (args i).leadingExp
            simp at this
            simp_rw [h_deg] at this
            obtain ⟨i, hi⟩ := this
            cases i using Fin.lastCases with
            | last =>
              exact hi.symm
            | cast i =>
              simp [h_deg' i] at hi
          have : ∀ (i : Fin (k + 1)), args i.castSucc = .nil := by
            intro i
            specialize h_deg' i
            exact leadingExp_eq_bot.mpr h_deg'
          simp only [longAdd, ← h_coef_tl_args, this, leadingExp_nil, WithBot.bot_ne_coe, ↓reduceDIte,
            longAdd_zeros, Fin.natCast_eq_last, add_zero, Nat.cast_one, zero_add,
            longAdd_nils, add_nil, h_last] at h_coef h_tl
          rw [← h_coef, ← h_tl, nil_add]
          generalize_proofs h1 h2
          have : h1 = h2 := by rfl
          subst this
          convert h1.choose_spec
          simp only [← Fin.natCast_eq_last]
        | coe deg' =>
          simp only
          -- наводим красоту
          generalize_proofs h_coefs_tls'
          generalize h_coef_tl_args' : (fun i ↦
            (if h : (args i.castSucc).leadingExp = ↑deg' then (h_coefs_tls' i h).choose
              else (0, args i.castSucc))) = coef_tl_args'
          generalize h_coef' : longAdd (fun i ↦ (coef_tl_args' i).1) = coef'
          generalize h_tl' : longAdd (fun i ↦ (coef_tl_args' i).2) = tl'
          rw [show longAdd (fun i ↦
            (if h : (args i.castSucc).leadingExp = ↑deg' then (h_coefs_tls' i h).choose
              else (0, args i.castSucc)).1) =
            coef' by rw [← h_coef', ← h_coef_tl_args']]
          rw [show (longAdd fun i ↦
            (if h : (args i.castSucc).leadingExp = ↑deg' then (h_coefs_tls' i h).choose
              else (0, args i.castSucc)).2) =
            tl' by rw [← h_tl', ← h_coef_tl_args']]
          -- навели
          have h_left_eq : (longAdd fun i ↦ args i.castSucc) = Seq.cons (deg', coef') tl' := by
            rw [ih]
            simp [longAdd']
            have : ∀ i h, h_coefs_tls_ deg' i h = h_coefs_tls' i h := by
              intro i h
              rfl
            generalize_proofs
            simp [h_deg']
            congr
            · conv in fun h ↦ (h_coefs_tls_ deg' _ h).choose => -- very inconvinient
                ext h
                rw [this i h]
              simp [← h_coef', ← h_coef_tl_args']
            · conv in fun h ↦ (h_coefs_tls_ deg' _ h).choose => -- very inconvinient
                ext h
                rw [this i h]
              simp [← h_tl', ← h_coef_tl_args']

          replace h_deg : deg = (args ↑(k + 1)).leadingExp ⊔ deg' := by
            have hs : (Finset.map Fin.castSuccEmb (Finset.univ : Finset (Fin (k + 1)))).Nonempty := by
              simpa
            have : (Finset.map Fin.castSuccEmb Finset.univ).sup' hs (fun i ↦ (args i).leadingExp) =
                Finset.univ.sup' (Finset.map_nonempty.mp hs) ((fun i ↦ (args i).leadingExp) ∘ ⇑Fin.castSuccEmb) := by
              apply Finset.sup'_map
            simp only [Fin.coe_castSuccEmb, Function.comp_apply] at this
            generalize_proofs at this
            rw [h_deg'] at this
            rw [← h_deg, ← this]
            have : (Finset.univ : Finset (Fin (k + 1 + 1))) = insert (↑(k + 1) : Fin (k + 1 + 1)) (Finset.map Fin.castSuccEmb (Finset.univ : Finset (Fin (k + 1)))) := by
              ext x
              simp only [Finset.mem_univ, Finset.mem_insert,
                Finset.mem_map, true_and, true_iff]
              cases x using Fin.lastCases with
              | last =>
                left
                simp only [← Fin.natCast_eq_last]
              | cast j =>
                right
                use j
                rfl
            simp_rw [this]
            apply Finset.sup'_insert

          cases lt_trichotomy (args ↑(k + 1)).leadingExp ↑deg' with
          | inl h_lt =>
            rw [sup_eq_right.mpr h_lt.le] at h_deg
            simp at h_deg
            subst h_deg
            unfold longAdd at h_coef h_tl
            simp only at h_coef h_tl
            conv at h_coef =>
              arg 1; arg 2;
              rw [← h_coef_tl_args]
              simp only [h_lt.ne]
            simp at h_coef
            conv at h_tl =>
              arg 1; arg 2;
              rw [← h_coef_tl_args]
              simp only [h_lt.ne]
            simp only [↓reduceDIte] at h_tl

            have h_coef_tl_args'_eq : ∀ i, coef_tl_args' i = coef_tl_args i.castSucc := by
              intro i
              rw [← h_coef_tl_args, ← h_coef_tl_args']

            simp_rw [← h_coef_tl_args'_eq] at h_tl h_coef
            rw [h_coef'] at h_coef
            rw [h_tl'] at h_tl
            symm at h_tl
            subst h_coef
            subst h_tl
            rw [add_cons_left h_lt]
          | inr h =>
          cases h with
          | inl h_eq =>
            rw [sup_eq_right.mpr h_eq.le] at h_deg
            simp at h_deg
            subst h_deg

            unfold longAdd at h_coef h_tl
            simp only at h_coef h_tl
            conv at h_coef =>
              arg 1; arg 2
              simp only [← h_coef_tl_args, h_eq, ↓reduceDIte]
            conv at h_tl =>
              arg 1; arg 2
              simp only [← h_coef_tl_args, h_eq, ↓reduceDIte]

            have h_coef_tl_args'_eq : ∀ i, coef_tl_args' i = coef_tl_args i.castSucc := by
              intro i
              rw [← h_coef_tl_args, ← h_coef_tl_args']

            simp_rw [← h_coef_tl_args'_eq] at h_tl h_coef
            rw [h_coef'] at h_coef
            rw [h_tl'] at h_tl
            generalize_proofs h1 at h_coef h_tl

            revert h_eq h1
            generalize (args ↑(k + 1)) = a at *
            apply a.recOn
            · intro h_eq h1 h_coef h_tl
              simp at h_eq
            · intro (a_deg, a_coef) a_tl h_eq h1 h_tl h_coef
              simp at h_eq
              subst h_eq
              rw [add_cons_cons]
              simp
              congr
              · have := h1.choose_spec
                rw [Seq.cons_eq_cons] at this
                simp at this
                simp [← h_coef]
                congr
                exact this.left
              · have := h1.choose_spec
                rw [Seq.cons_eq_cons] at this
                simp [← h_tl]
                congr
                exact this.right
          | inr h_lt =>
            rw [sup_eq_left.mpr h_lt.le] at h_deg
            have : ∀ (i : Fin (k + 1)), (args i.castSucc).leadingExp ≠ deg := by
              intro i
              apply ne_of_lt
              apply lt_of_le_of_lt (b := ↑deg')
              · rw [← h_deg']
                exact Finset.le_sup' (s := Finset.univ (α := Fin (k + 1))) (fun i ↦ (args i.castSucc).leadingExp) (b := i) (by simp) -- ugly
              · rwa [h_deg]
            unfold longAdd at h_coef h_tl
            simp only at h_coef h_tl
            conv at h_coef =>
              arg 1; arg 1
              simp only [← h_coef_tl_args, this]
            simp only [↓reduceDIte, longAdd_zeros, zero_add] at h_coef
            conv at h_tl =>
              arg 1; arg 1;
              simp only [← h_coef_tl_args, this]
            simp only [↓reduceDIte] at h_tl
            simp only [← h_coef_tl_args, h_deg, ↓reduceDIte] at h_coef h_tl
            generalize_proofs h1 at h_coef h_tl
            rw [h_left_eq] at h_tl
            rw [← h_coef, ← h_tl]
            revert h_deg h1 h_lt
            generalize (args ↑(k + 1)) = a at *
            apply a.recOn
            · intro h_deg
              simp at h_deg
            · intro (a_deg, a_coef) a_tl h_deg h_lt h1 h_coef h_tl
              simp at h_deg h_lt
              subst h_deg
              rw [add_cons_right]
              · congr
                · have := h1.choose_spec
                  apply Seq.cons_eq_cons.mp at this
                  simp only [Prod.mk.injEq, true_and] at this
                  exact this.left
                · have := h1.choose_spec
                  apply Seq.cons_eq_cons.mp at this
                  simp only [Prod.mk.injEq, true_and] at this
                  exact this.right
              · simpa

theorem longAdd_WellOrdered {basis : Basis} {k : ℕ} {args : Fin k → PreMS basis}
    (h_wo : ∀ i, (args i).WellOrdered) : (longAdd args).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    induction k with
    | zero => simp [longAdd]; exact WellOrdered.nil
    | succ k ih =>
      unfold longAdd
      apply add_WellOrdered
      · apply ih
        intro i
        apply h_wo
      · apply h_wo

theorem longAdd_Approximates {basis : Basis} {k : ℕ} {args : Fin k → PreMS basis}
    {F : Fin k → (ℝ → ℝ)}
    (h_approx : ∀ i, (args i).Approximates (F i) basis) :
    (longAdd args).Approximates (fun x ↦ ∑ i, F i x) := by
  cases basis with
  | nil =>
    simp [Approximates] at *
    induction k with
    | zero => simp [longAdd, zero]
    | succ l ih =>
      conv =>
        lhs
        ext x
        rw [Fin.sum_univ_castSucc]
      simp [longAdd, add]
      apply EventuallyEq.add
      · apply ih
        intro i
        apply h_approx
      · apply h_approx
  | cons basis_hd basis_tl =>
    induction k with
    | zero =>
      simp [longAdd, zero]
      apply Approximates.nil
      rfl
    | succ k ih =>
      conv =>
        arg 1
        ext x
        rw [Fin.sum_univ_castSucc]
      unfold longAdd
      apply add_Approximates
      · apply ih
        intro i
        apply h_approx
      · simp only [Fin.natCast_eq_last]
        apply h_approx

noncomputable def longAdd_mulMonomial_tail_BM {basis_hd : _} {basis_tl : _} {k : ℕ}
    (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)) (deg : ℝ) :
    Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ) :=
  match k with
  | 0 => default
  | l + 1 =>
    have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg →
        ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
        (BM i).1 = Seq.cons (deg - (BM i).2.2, a.1) a.2 := by
      intro i hi
      simp at hi
      have : (BM i).1.leadingExp = ↑(deg - (BM i).2.2) := by
        generalize (BM i).1.leadingExp = x at hi
        cases x with
        | bot => simp at hi
        | coe x =>
          simp [← WithBot.coe_add] at hi ⊢
          linarith
      exact leadingExp_eq_coe this
    (fun i ↦
      if h : ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg then ((h_BM_cons i h).choose.2, (BM i).2.1, (BM i).2.2)
        else BM i)


theorem longAdd_mulMonomial_tail_eq {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)}
    {deg : ℝ} {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    (h_eq_cons : (longAdd <| (fun (B, M_coef, M_deg) => B.mulMonomial M_coef M_deg) ∘ BM) =
    Seq.cons (deg, coef) tl) :
    tl =
    (longAdd <| (fun (B, M_coef, M_deg) => B.mulMonomial M_coef M_deg) ∘ (longAdd_mulMonomial_tail_BM BM deg)) := by
  rw [longAdd_eq] at h_eq_cons
  simp [longAdd'] at h_eq_cons
  cases k with
  | zero => simp at h_eq_cons
  | succ l =>
    simp at h_eq_cons
    generalize_proofs inst h_coef_tl_args at h_eq_cons
    generalize h_deg? : (Finset.univ.sup' inst fun x ↦ ↑(BM x).2.2 + (BM x).1.leadingExp) = deg? at h_eq_cons
    cases deg? with
    | bot => simp at h_eq_cons
    | coe deg' =>
      simp [Seq.cons_eq_cons] at h_eq_cons
      obtain ⟨⟨h_deg, _⟩, h_tl_eq⟩ := h_eq_cons
      subst h_deg

      rw [← h_tl_eq]
      simp [longAdd_mulMonomial_tail_BM]
      congr 1
      ext1 i
      simp
      split_ifs with h_if
      · generalize_proofs h1 h2

        have hh := h1.choose_spec -- ugly
        generalize h1.choose = a1 at *
        replace h1 := hh
        clear hh

        have hh := h2.choose_spec -- ugly
        generalize h2.choose = a2 at *
        replace h2 := hh
        clear hh

        rw [h2] at h1
        simp [Seq.cons_eq_cons] at h1
        exact h1.right.symm
      · simp

theorem longAdd_mulMonomial_tail_B_WellOrdered {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    (h_wo : ∀ j, (BM j).1.WellOrdered) :
    ∀ j, (longAdd_mulMonomial_tail_BM BM deg j).1.WellOrdered := by
  intro j
  cases k with
  | zero =>
    fin_cases j
  | succ l =>
    simp [longAdd_mulMonomial_tail_BM]
    split_ifs
    · simp
      generalize_proofs h
      have hh := h.choose_spec
      have := h_wo j
      rw [hh] at this
      have := WellOrdered_cons this
      exact this.2.2
    · exact h_wo j

theorem longAdd_mulMonomial_tail_M_WellOrdered {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    (h_wo : ∀ j, (BM j).2.1.WellOrdered) :
    ∀ j, (longAdd_mulMonomial_tail_BM BM deg j).2.1.WellOrdered := by
  intro j
  cases k with
  | zero =>
    fin_cases j
  | succ l =>
    simp [longAdd_mulMonomial_tail_BM]
    split_ifs with h
    · simp
      exact h_wo j
    · exact h_wo j

theorem longAdd_mulMonomial_tail_BM_WellOrdered {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    (h_wo : ∀ j, (BM j).1.WellOrdered ∧ (BM j).2.1.WellOrdered) :
    ∀ j, (longAdd_mulMonomial_tail_BM BM deg j).1.WellOrdered ∧
      (longAdd_mulMonomial_tail_BM BM deg j).2.1.WellOrdered := by
  intro j
  constructor
  · apply longAdd_mulMonomial_tail_B_WellOrdered
    exact fun j ↦ (h_wo j).left
  · apply longAdd_mulMonomial_tail_M_WellOrdered
    exact fun j ↦ (h_wo j).right

noncomputable def longAdd_mulMonomial_tail_fB {basis_hd : _} {basis_tl : _} {k : ℕ}
    (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)) (deg : ℝ)
    {fB : Fin k → (ℝ → ℝ)}
    (hB_approx : ∀ j, (BM j).1.Approximates (fB j) (basis_hd :: basis_tl)) :
    Fin k → (ℝ → ℝ) :=
  match k with
  | 0 => default
  | l + 1 =>
    have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg →
        ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
        (BM i).1 = Seq.cons (deg - (BM i).2.2, a.1) a.2 := by
      intro i hi
      simp at hi
      have : (BM i).1.leadingExp = ↑(deg - (BM i).2.2) := by
        generalize (BM i).1.leadingExp = x at hi
        cases x with
        | bot => simp at hi
        | coe x =>
          simp [← WithBot.coe_add] at hi ⊢
          linarith
      exact leadingExp_eq_coe this
    fun i ↦
      if h : ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg then
        by
          have h' := (h_BM_cons i h).choose_spec
          specialize hB_approx i
          rw [h'] at hB_approx
          apply Approximates_cons at hB_approx
          let C := hB_approx.choose
          exact fun x ↦ fB i x - basis_hd x ^ (deg - (BM i).2.2) * C x
      else
        fB i

theorem longAdd_mulMonomial_tail_B_Approximates {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    {fB : Fin k → (ℝ → ℝ)}
    {hB_approx : ∀ j, (BM j).1.Approximates (fB j) (basis_hd :: basis_tl)} : ∀ (j : Fin k),
    Approximates (longAdd_mulMonomial_tail_fB BM deg hB_approx j) (basis_hd :: basis_tl)
      (longAdd_mulMonomial_tail_BM BM deg j).1 := by
  intro j
  cases k with
  | zero =>
    fin_cases j
  | succ l =>
    simp [longAdd_mulMonomial_tail_BM, longAdd_mulMonomial_tail_fB]
    split_ifs
    · simp
      generalize_proofs _ h
      exact h.choose_spec.right.right
    · apply hB_approx

noncomputable def longAdd_mulMonomial_fC {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} (deg : ℝ)
    {fB fM : Fin k → (ℝ → ℝ)}
    (hB_approx : ∀ j , (BM j).1.Approximates (fB j) (basis_hd :: basis_tl))
    (hM_approx : ∀ j , (BM j).2.1.Approximates (fM j) basis_tl) :
    ℝ → ℝ :=
  match k with
  | 0 => default
  | l + 1 =>
    have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg →
        ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
        (BM i).1 = Seq.cons (deg - (BM i).2.2, a.1) a.2 := by
      intro i hi
      simp at hi
      have : (BM i).1.leadingExp = ↑(deg - (BM i).2.2) := by
        generalize (BM i).1.leadingExp = x at hi
        cases x with
        | bot => simp at hi
        | coe x =>
          simp [← WithBot.coe_add] at hi ⊢
          linarith
      exact leadingExp_eq_coe this
    fun x ↦ ∑ i, (
      if h : ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg then
        by
          have h' := (h_BM_cons i h).choose_spec
          specialize hB_approx i
          rw [h'] at hB_approx
          apply Approximates_cons at hB_approx
          let fBC := hB_approx.choose
          exact (fM i x) * (fBC x)
      else
        0
    )

mutual
  theorem mulMonomial_WellOrdered {basis_hd : _} {basis_tl : _} {b : PreMS (basis_hd :: basis_tl)}
      {m_coef : PreMS basis_tl} {m_deg : ℝ}
      (hb_wo : b.WellOrdered) (hm_wo : m_coef.WellOrdered) :
      (mulMonomial b m_coef m_deg).WellOrdered := by
    let motive : PreMS (basis_hd :: basis_tl) → Prop := fun x =>
      ∃ (b : PreMS (basis_hd :: basis_tl)), x = b.mulMonomial m_coef m_deg ∧
      b.WellOrdered
    apply WellOrdered.coind motive
    · simp only [motive]
      use b
    · intro ms ih
      simp only [motive] at ih
      obtain ⟨b, h_eq, hb_wo⟩ := ih
      subst h_eq
      revert hb_wo
      apply b.recOn
      · intro
        left
        simp
      · intro (deg, coef) tl h_wo
        have h_wo' := WellOrdered_cons h_wo
        obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := h_wo'
        right
        use ?_
        use ?_
        use ?_
        constructor
        · simp only [mulMonomial_cons]
          congr <;> exact Eq.refl _
        constructor
        · apply mul_WellOrdered hm_wo h_coef_wo
        constructor
        · simp
          apply WithBot.add_lt_add_left
          · simp
          · exact h_comp
        simp only [motive]
        use tl

  -- TODO: maybe use `merge1_WellOrdered`?
  -- TODO: very ugly. rewrite
  theorem mul_WellOrdered {basis : Basis} {X Y : PreMS basis}
      (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) :
      (X.mul Y).WellOrdered := by
    cases basis with
    | nil => constructor
    | cons basis_hd basis_tl =>
      let motive : PreMS (basis_hd :: basis_tl) → Prop := fun x =>
        ∃ (k : ℕ) (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ))
          (X Y : PreMS (basis_hd :: basis_tl)),
          x = (longAdd <| (fun (B, M_coef, M_deg) => B.mulMonomial M_coef M_deg) ∘ BM) + (X.mul Y) ∧
          (∀ j , (BM j).1.WellOrdered ∧ (BM j).2.1.WellOrdered) ∧
          X.WellOrdered ∧ Y.WellOrdered
      apply WellOrdered.coind motive
      · simp only [motive]
        use 0
        use default
        use X
        use Y
        simp [longAdd, zero]
        constructor <;> assumption
      · intro ms ih
        simp only [motive] at ih
        obtain ⟨k, BM, X, Y, h_eq, h_BM, hX_wo, hY_wo⟩ := ih
        generalize h_left_eq : (longAdd ((fun x ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM)) = left at h_eq
        generalize h_right_eq : X.mul Y = right at h_eq

        have h_left_wo : left.WellOrdered := by
          rw [← h_left_eq]
          apply longAdd_WellOrdered
          intro i
          simp
          apply mulMonomial_WellOrdered
          · exact (h_BM i).left
          · exact (h_BM i).right
        subst h_eq
        revert h_left_eq h_left_wo
        apply left.recOn
        · intro h_left_eq h_left_wo
          simp
          revert h_right_eq
          apply right.recOn
          · simp
          · intro (right_deg, right_coef) right_tl h_right_eq
            simp
            use right_deg
            use right_coef
            use right_tl
            simp
            obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
            subst hX_eq hY_eq
            obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
            obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
            simp only [mul_cons_cons, Seq.cons_eq_cons, Prod.mk.injEq] at h_right_eq
            obtain ⟨⟨h_deg, h_coef⟩, h_tl⟩ := h_right_eq
            subst h_deg h_coef h_tl
            constructor
            · apply mul_WellOrdered hX_coef_wo hY_coef_wo
            constructor
            · simp
              constructor
              · apply WithBot.add_lt_add_left
                · simp
                ·  exact hY_comp
              · apply WithBot.add_lt_add_right
                · simp
                · exact hX_comp
            simp only [motive]
            use 1
            use fun _ ↦ (Y_tl, X_coef, X_deg)
            use X_tl
            use .cons (Y_deg, Y_coef) Y_tl
            simp
            constructor
            · simp [longAdd_one]
            constructor
            · constructor
              · exact hY_tl_wo
              · exact hX_coef_wo
            · constructor
              · exact hX_tl_wo
              · apply WellOrdered.cons <;> assumption
        · intro (left_deg, left_coef) left_tl h_left_eq h_left_wo
          obtain ⟨h_left_coef_wo, h_left_comp, h_left_tl_wo⟩ := WellOrdered_cons h_left_wo
          right
          have h_left_tl_eq := longAdd_mulMonomial_tail_eq h_left_eq
          have h_left_eq' := h_left_eq
          rw [longAdd_eq] at h_left_eq'
          simp [longAdd'] at h_left_eq'
          cases k with
          | zero => simp at h_left_eq'
          | succ l =>
            simp only at h_left_eq'
            generalize_proofs inst h_coef_tl_args at h_left_eq'
            generalize h_deg? : (Finset.univ.sup' inst fun i ↦ (((fun (x : PreMS (basis_hd :: basis_tl) × PreMS basis_tl × ℝ) ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM) i).leadingExp) = deg? at h_left_eq'
            cases deg? with
            | bot => simp at h_left_eq'
            | coe deg' =>
              simp only [Seq.cons_eq_cons, Prod.mk.injEq] at h_left_eq'
              obtain ⟨⟨h_deg', h_left_coef_eq⟩, h_left_tl_eq'⟩ := h_left_eq'
              have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg' →
                  ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
                  (BM i).1 = Seq.cons (deg' - (BM i).2.2, a.1) a.2 := by
                intro i hi
                simp at hi
                have : (BM i).1.leadingExp = ↑(deg' - (BM i).2.2) := by -- there is no `Sub` for `WithBot ℝ` :(
                  generalize (BM i).1.leadingExp = x at hi
                  cases x with
                  | bot => simp at hi
                  | coe x =>
                    simp [← WithBot.coe_add] at hi ⊢
                    linarith
                exact leadingExp_eq_coe this
              revert h_right_eq
              apply right.recOn
              · intro h_right_eq
                use left_deg
                use left_coef
                use left_tl
                constructor
                · simp
                constructor
                · exact h_left_coef_wo
                constructor
                · exact h_left_comp
                simp only [motive]
                use (l + 1) -- =k
                use ?_
                use .nil
                use .nil
                constructor
                · simp
                  exact h_left_tl_eq
                constructor
                · exact longAdd_mulMonomial_tail_BM_WellOrdered h_BM
                · constructor <;> exact WellOrdered.nil
              · intro (right_deg, right_coef) right_tl h_right_eq
                rw [add_cons_cons]
                split_ifs with h1 h2
                · use ?_; use ?_; use ?_
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · exact h_left_coef_wo
                  constructor
                  · simp
                    constructor
                    · exact h_left_comp
                    · exact h1
                  simp only [motive]
                  use (l + 1) -- l + 1 = k
                  use ?_
                  use X
                  use Y
                  constructor
                  · rw [h_right_eq]
                    congr 1
                    exact h_left_tl_eq
                  constructor
                  · exact longAdd_mulMonomial_tail_BM_WellOrdered h_BM
                  constructor
                  · exact hX_wo
                  · exact hY_wo
                · obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
                  subst hX_eq hY_eq
                  obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
                  obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
                  simp only [mul_cons_cons, Seq.cons_eq_cons, Prod.mk.injEq] at h_right_eq
                  use ?_; use ?_; use ?_
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · rw [← h_right_eq.1.2]
                    apply mul_WellOrdered hX_coef_wo hY_coef_wo
                  constructor
                  · simp
                    constructor
                    · simpa
                    · rw [← h_right_eq.2, ← h_right_eq.1.1]
                      simp
                      constructor
                      · apply WithBot.add_lt_add_left
                        · simp
                        · exact hY_comp
                      · apply WithBot.add_lt_add_right
                        · simp
                        · exact hX_comp
                  rw [← h_left_eq, ← h_right_eq.2, ← add_assoc]
                  simp only [motive]
                  use (l + 2) -- l + 2 = k + 1
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (Y_tl, X_coef, X_deg)
                  | cast j => exact BM j
                  use X_tl
                  use Seq.cons (Y_deg, Y_coef) Y_tl
                  constructor
                  · congr 1
                    conv => rhs; unfold longAdd
                    simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.natCast_eq_last]
                    congr 1
                    simp
                  constructor
                  · intro j
                    cases j using Fin.lastCases with
                    | last =>
                      simp
                      exact ⟨hY_tl_wo, hX_coef_wo⟩
                    | cast j =>
                      simp
                      exact h_BM j
                  constructor
                  · exact hX_tl_wo
                  · exact hY_wo
                · have h_deg : right_deg = left_deg := by linarith
                  subst h_deg h_deg'
                  clear h1 h2
                  obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
                  subst hX_eq hY_eq
                  obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
                  obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
                  simp only [mul_cons_cons, Seq.cons_eq_cons, Prod.mk.injEq] at h_right_eq
                  use ?_; use ?_; use ?_
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · apply add_WellOrdered
                    · exact h_left_coef_wo
                    · rw [← h_right_eq.1.2]
                      apply mul_WellOrdered hX_coef_wo hY_coef_wo
                  constructor
                  · simp
                    constructor
                    · exact h_left_comp
                    · rw [← h_right_eq.2, ← h_right_eq.1.1] -- copypaste
                      simp
                      constructor
                      · apply WithBot.add_lt_add_left
                        · simp
                        ·  exact hY_comp
                      · apply WithBot.add_lt_add_right
                        · simp
                        · exact hX_comp
                  rw [← h_left_tl_eq', ← h_right_eq.2, ← add_assoc]
                  simp only [motive]
                  use l + 2
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (Y_tl, X_coef, X_deg)
                  | cast j => exact longAdd_mulMonomial_tail_BM BM deg' j
                  use X_tl
                  use Seq.cons (Y_deg, Y_coef) Y_tl
                  constructor
                  · congr 1
                    conv => rhs; unfold longAdd
                    simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.natCast_eq_last]
                    congr 1
                    · simp
                      congr 1
                      ext1 i
                      split_ifs with h1
                      · simp [longAdd_mulMonomial_tail_BM] -- copypaste
                        split_ifs
                        generalize_proofs h2 h3

                        have hh := h2.choose_spec -- ugly
                        generalize h2.choose = a2 at *
                        replace h2 := hh
                        clear hh

                        have hh := h3.choose_spec -- ugly
                        generalize h3.choose = a3 at *
                        replace h3 := hh
                        clear hh

                        rw [h3] at h2
                        simp [Seq.cons_eq_cons] at h2
                        exact h2.right.symm
                      · simp [longAdd_mulMonomial_tail_BM] -- copypaste
                        split_ifs
                        rfl
                    · simp
                  constructor
                  · intro j
                    cases j using Fin.lastCases with
                    | last =>
                      simp
                      exact ⟨hY_tl_wo, hX_coef_wo⟩
                    | cast j =>
                      simp
                      exact longAdd_mulMonomial_tail_BM_WellOrdered h_BM j
                  constructor
                  · exact hX_tl_wo
                  · exact hY_wo

end

set_option maxHeartbeats 400000 in -- TODO : very slow. How to speed up?
mutual

  theorem mulMonomial_Approximates {basis_hd : _} {basis_tl : _} {B M : ℝ → ℝ} {b : PreMS (basis_hd :: basis_tl)}
        {m_coef : PreMS basis_tl} {m_deg : ℝ}
        (h_basis : MS.WellOrderedBasis (basis_hd :: basis_tl))
        (hb_approx : b.Approximates B (basis_hd :: basis_tl))
        (hm_approx : m_coef.Approximates M basis_tl) :
      (mulMonomial b m_coef m_deg).Approximates (fun x ↦ (M x) * (basis_hd x)^m_deg * (B x)) := by
    let motive : (ℝ → ℝ) → PreMS (basis_hd :: basis_tl) → Prop := fun f ms =>
      ∃ (b : PreMS (basis_hd :: basis_tl)) (B M : ℝ → ℝ),
      ms = b.mulMonomial m_coef m_deg ∧
      f =ᶠ[atTop] (fun x ↦ (M x) * (basis_hd x)^m_deg * (B x)) ∧
      b.Approximates B (basis_hd :: basis_tl) ∧ m_coef.Approximates M basis_tl
    apply Approximates.coind motive
    · simp only [motive]
      use b
      use B
      use M
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨b, B, M, h_ms_eq, hf_eq, hb_approx, hm_approx⟩ := ih
      subst h_ms_eq
      revert hb_approx
      apply b.recOn
      · intro hb_approx
        apply Approximates_nil at hb_approx
        left
        simp
        conv => rhs; ext x; simp; rw [← mul_zero (M x * basis_hd x ^ m_deg)]
        trans
        · exact hf_eq
        apply EventuallyEq.mul (by rfl) hb_approx
      · intro (b_deg, b_coef) b_tl hb_approx
        have hb_approx' := Approximates_cons hb_approx
        obtain ⟨C, h_coef_approx, h_comp, h_tl_approx⟩ := hb_approx'
        right
        use ?_
        use ?_
        use ?_
        use M * C
        constructor
        · simp only [mulMonomial_cons]
          congr <;> exact Eq.refl _
        constructor
        · apply mul_Approximates (MS.WellOrderedBasis_tail h_basis) hm_approx h_coef_approx
        constructor
        · apply majorated_of_EventuallyEq hf_eq
          rw [show m_deg + b_deg = 0 + m_deg + b_deg by simp]
          apply mul_majorated
          · apply mul_majorated
            · exact Approximates_coef_isLittleO_head hm_approx h_basis
            · apply majorated_self
              apply MS.basis_tendsto_top h_basis
              simp
            · exact MS.basis_head_eventually_pos h_basis
          · exact h_comp
          · exact MS.basis_head_eventually_pos h_basis
        simp only [motive]
        use ?_
        use ?_
        use ?_
        constructor
        · congr 1
          exact Eq.refl _
        constructor
        swap
        · constructor
          · exact h_tl_approx
          · exact hm_approx
        · simp only [EventuallyEq] at hf_eq ⊢
          apply Eventually.mono <| hf_eq.and (MS.basis_head_eventually_pos h_basis)
          intro x ⟨hf_eq, h_pos⟩
          simp [Real.rpow_add h_pos, hf_eq]
          ring_nf

  theorem longAdd_mulMonomial_cons_Approximates_coef {basis_hd : _} {basis_tl : _} {k : ℕ}
      {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
      {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
      {fB fM : Fin k → (ℝ → ℝ)}
      (h_basis : MS.WellOrderedBasis (basis_hd :: basis_tl))
      (hB_approx : ∀ j, (BM j).1.Approximates (fB j) (basis_hd :: basis_tl))
      (hM_approx : ∀ j, (BM j).2.1.Approximates (fM j) basis_tl)
      (h_cons : (longAdd ((fun x ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM)) = Seq.cons (deg, coef) tl) :
      coef.Approximates (longAdd_mulMonomial_fC deg hB_approx hM_approx) basis_tl := by
    induction k generalizing deg coef with
    | zero =>
      simp [longAdd] at h_cons
    | succ l ih =>
      rw [longAdd_eq] at h_cons
      simp [longAdd'] at h_cons
      generalize_proofs inst h_coef_tl_args at h_cons
      generalize h_deg? : (Finset.univ.sup' inst fun x ↦ ↑(BM x).2.2 + (BM x).1.leadingExp) = deg? at h_cons
      cases deg? with
      | bot => simp at h_cons
      | coe deg' =>
        simp [Seq.cons_eq_cons] at h_cons
        obtain ⟨⟨h_deg, h_coef⟩, h_tl⟩ := h_cons
        subst h_deg
        rw [← h_coef]
        apply longAdd_Approximates
        intro i
        simp only [mulMonomial_leadingExp]
        split_ifs with h_if
        · generalize_proofs h1 h2 h3

          have hh := h1.choose_spec
          generalize h1.choose = a at *
          obtain ⟨coef1, tl1⟩ := a
          replace h1 := hh
          clear hh

          have hh := h3.choose_spec
          generalize h3.choose = a at *
          obtain ⟨coef2, tl2⟩ := a
          replace h3 := hh
          clear hh

          simp only at h1 h2 h3 ⊢
          generalize_proofs

          have hh := h2.choose_spec
          generalize h2.choose = C at *
          replace h2 := hh
          clear hh

          rw [h1] at h3
          simp [Seq.cons_eq_cons] at h3
          rw [← h3.left]
          apply mul_Approximates (MS.WellOrderedBasis_tail h_basis)
          · apply hM_approx
          · exact h2.left
        · simp
          exact zero_Approximates_zero

  theorem mul_Approximates {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
      (h_basis : MS.WellOrderedBasis basis)
      (hX_approx : X.Approximates fX basis) (hY_approx : Y.Approximates fY basis) :
      (X.mul Y).Approximates (fX * fY) basis := by
    cases basis with
    | nil =>
      simp [Approximates, mul] at *
      apply EventuallyEq.mul hX_approx hY_approx
    | cons basis_hd basis_tl =>
      let motive : (ℝ → ℝ) → PreMS (basis_hd :: basis_tl) → Prop := fun f ms =>
        ∃ (k : ℕ) (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ))
          (fB fM : Fin k → (ℝ → ℝ))
          (X Y : PreMS (basis_hd :: basis_tl))
          (fX fY : ℝ → ℝ),
          ms = (longAdd <| (fun (B, M_coef, M_deg) => B.mulMonomial M_coef M_deg) ∘ BM) + (X.mul Y) ∧
          f =ᶠ[atTop] (fun x ↦ (∑ i, (fM i x) * (basis_hd x)^(BM i).2.2 * (fB i x)) + (fX x) * (fY x)) ∧ -- I am here. Need finite sum of BM
          (∀ j , (BM j).1.Approximates (fB j) (basis_hd :: basis_tl)) ∧
          (∀ j , (BM j).2.1.Approximates (fM j) basis_tl) ∧
          X.Approximates fX (basis_hd :: basis_tl) ∧
          Y.Approximates fY (basis_hd :: basis_tl)
      apply Approximates.coind motive
      · simp only [motive]
        use 0
        use default
        use 1
        use 1
        use X
        use Y
        use fX
        use fY
        simp [longAdd]
        constructor
        · rfl
        constructor
        · exact hX_approx
        · exact hY_approx
      · intro f ms ih
        simp only [motive] at ih
        obtain ⟨k, BM, fB, fM, X, Y, fX, fY, h_ms_eq, hf_eq, hB_approx, hM_approx, hX_approx, hY_approx⟩ := ih
        generalize h_left_eq : (longAdd ((fun x ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM)) = left at h_ms_eq
        generalize h_right_eq : X.mul Y = right at h_ms_eq

        have h_mul_eq_nil : X.mul Y = .nil → fX * fY =ᶠ[atTop] 0 := by
          intro h
          cases mul_eq_nil h with
          | inl hX =>
            subst hX
            apply Approximates_nil at hX_approx
            conv => rhs; ext x; simp; rw [← zero_mul (fY x)]
            exact EventuallyEq.mul hX_approx (by rfl)
          | inr hY =>
            subst hY
            apply Approximates_nil at hY_approx
            conv => rhs; ext x; simp; rw [← mul_zero (fX x)]
            exact EventuallyEq.mul (by rfl) hY_approx

        have h_left_approx : left.Approximates
            (fun x ↦ ∑ i, (fM i x) * (basis_hd x)^(BM i).2.2 * (fB i x)) (basis_hd :: basis_tl) := by
          rw [← h_left_eq]

          apply longAdd_Approximates
          intro i
          simp
          apply mulMonomial_Approximates h_basis
          · exact hB_approx i
          · exact hM_approx i
        subst h_ms_eq
        revert h_left_eq h_left_approx
        apply left.recOn
        · intro h_left_eq h_left_approx
          apply Approximates_nil at h_left_approx
          replace hf_eq : f =ᶠ[atTop] fX * fY := by
            trans
            · exact hf_eq
            conv => rhs; ext x; simp; rw [← zero_add (fX x * fY x)]
            apply EventuallyEq.add h_left_approx (by rfl)
          simp
          revert h_right_eq
          apply right.recOn
          · simp
            intro h_right_eq
            trans
            · exact hf_eq
            · exact h_mul_eq_nil h_right_eq
          · intro (right_deg, right_coef) right_tl h_right_eq
            simp
            use right_deg
            use right_coef
            use right_tl
            simp
            obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
            subst hX_eq hY_eq
            obtain ⟨XC, hX_coef_approx, hX_comp, hX_tl_approx⟩ := Approximates_cons hX_approx
            obtain ⟨YC, hY_coef_approx, hY_comp, hY_tl_approx⟩ := Approximates_cons hY_approx
            simp only [mul_cons_cons, Seq.cons_eq_cons, Prod.mk.injEq] at h_right_eq

            obtain ⟨⟨h_deg, h_coef⟩, h_tl⟩ := h_right_eq
            subst h_deg h_coef h_tl
            use XC * YC
            constructor
            · apply mul_Approximates (MS.WellOrderedBasis_tail h_basis) hX_coef_approx hY_coef_approx
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              apply mul_majorated hX_comp hY_comp
              apply MS.basis_head_eventually_pos h_basis
            simp only [motive]
            use 1
            use fun _ ↦ (Y_tl, X_coef, X_deg)
            use fun _ ↦ (fun x ↦ fY x - basis_hd x ^ Y_deg * YC x)
            use fun _ ↦ XC
            use X_tl
            use .cons (Y_deg, Y_coef) Y_tl
            use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
            use fY
            simp
            constructor
            · simp [longAdd_one]
            constructor
            · simp only [EventuallyEq] at hf_eq ⊢
              apply Eventually.mono <| hf_eq.and (MS.basis_head_eventually_pos h_basis)
              intro x ⟨hf_eq, h_pos⟩
              rw [Real.rpow_add h_pos, hf_eq]
              simp
              ring_nf
            constructor
            · exact hY_tl_approx
            constructor
            · exact hX_coef_approx
            constructor
            · exact hX_tl_approx
            · exact hY_approx
        · intro (left_deg, left_coef) left_tl h_left_eq h_left_approx
          obtain ⟨LC', h_left_coef_approx, h_left_comp, h_left_tl_approx⟩ := Approximates_cons h_left_approx
          replace h_left_coef_approx := longAdd_mulMonomial_cons_Approximates_coef h_basis hB_approx hM_approx h_left_eq -- Nasty workaround
          generalize h_LC_eq : (longAdd_mulMonomial_fC left_deg hB_approx hM_approx) = LC at h_left_coef_approx
          right
          have h_left_tl_eq := longAdd_mulMonomial_tail_eq h_left_eq
          have h_left_eq' := h_left_eq
          rw [longAdd_eq] at h_left_eq'
          simp [longAdd'] at h_left_eq'
          cases k with
          | zero => simp at h_left_eq'
          | succ l =>
            simp only at h_left_eq'
            generalize_proofs inst h_coef_tl_args at h_left_eq'
            generalize h_deg? : (Finset.univ.sup' inst fun i ↦ (((fun (x : PreMS (basis_hd :: basis_tl) × PreMS basis_tl × ℝ) ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM) i).leadingExp) = deg? at h_left_eq'
            cases deg? with
            | bot => simp at h_left_eq'
            | coe deg' =>
              simp only [Seq.cons_eq_cons, Prod.mk.injEq] at h_left_eq'
              obtain ⟨⟨h_deg', h_left_coef_eq⟩, h_left_tl_eq'⟩ := h_left_eq'
              have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg' →
                  ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
                  (BM i).1 = Seq.cons (deg' - (BM i).2.2, a.1) a.2 := by
                intro i hi
                simp at hi
                have : (BM i).1.leadingExp = ↑(deg' - (BM i).2.2) := by -- there is no `Sub` for `WithBot ℝ` :(
                  generalize (BM i).1.leadingExp = x at hi
                  cases x with
                  | bot => simp at hi
                  | coe x =>
                    simp [← WithBot.coe_add] at hi ⊢
                    linarith
                exact leadingExp_eq_coe this
              revert h_right_eq
              apply right.recOn
              · intro h_right_eq
                replace hf_eq : f =ᶠ[atTop] (fun x ↦ ∑ i : Fin (l + 1), fM i x * basis_hd x ^ (BM i).2.2 * fB i x) := by
                  trans
                  · exact hf_eq
                  conv => rhs; ext x; simp; rw [← add_zero (∑ i : Fin (l + 1), fM i x * basis_hd x ^ (BM i).2.2 * fB i x)]
                  apply EventuallyEq.add (by rfl) (h_mul_eq_nil h_right_eq)
                use left_deg
                use left_coef
                use left_tl
                use ?_
                constructor
                · simp
                constructor
                · exact h_left_coef_approx
                constructor
                · apply majorated_of_EventuallyEq hf_eq
                  exact h_left_comp
                simp only [motive]
                use (l + 1) -- =k
                use ?_
                use longAdd_mulMonomial_tail_fB BM left_deg hB_approx
                use fM
                use .nil
                use .nil
                use 0
                use 0
                constructor
                · simp
                  exact h_left_tl_eq
                constructor
                · rw [← h_LC_eq]
                  simp [longAdd_mulMonomial_fC, longAdd_mulMonomial_tail_fB, longAdd_mulMonomial_tail_BM]
                  simp only [EventuallyEq] at hf_eq ⊢
                  apply Eventually.mono <| hf_eq.and (MS.basis_head_eventually_pos h_basis)
                  intro x ⟨hf_eq, h_pos⟩
                  rw [hf_eq]
                  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                  congr
                  ext i
                  split_ifs with h_if
                  · generalize_proofs h1 h2

                    have hh := h1.choose_spec
                    generalize h1.choose = a at *
                    obtain ⟨coef1, tl1⟩ := a
                    replace h1 := hh
                    clear hh

                    have hh := h2.choose_spec
                    generalize h2.choose = C at *
                    replace h2 := hh
                    clear hh

                    simp only at h1 h2 ⊢
                    rw [Real.rpow_sub h_pos]
                    field_simp
                    ring_nf
                  · ring_nf
                constructor
                · apply longAdd_mulMonomial_tail_B_Approximates
                constructor
                · intro j
                  simp [longAdd_mulMonomial_tail_BM]
                  split_ifs with h
                  · simp
                    exact hM_approx j
                  · exact hM_approx j
                constructor
                · apply Approximates.nil (by rfl)
                · apply Approximates.nil (by rfl)
              · intro (right_deg, right_coef) right_tl h_right_eq
                obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
                subst hX_eq hY_eq
                obtain ⟨XC, hX_coef_approx, hX_comp, hX_tl_approx⟩ := Approximates_cons hX_approx
                obtain ⟨YC, hY_coef_approx, hY_comp, hY_tl_approx⟩ := Approximates_cons hY_approx
                simp only [mul_cons_cons, Seq.cons_eq_cons, Prod.mk.injEq] at h_right_eq

                rw [add_cons_cons]
                split_ifs with h1 h2
                · use ?_; use ?_; use ?_; use ?_
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · exact h_left_coef_approx
                  constructor
                  · apply majorated_of_EventuallyEq hf_eq
                    rw [← sup_of_le_left h1.le]
                    apply add_majorated
                    · exact h_left_comp
                    · rw [← h_right_eq.1.1]
                      apply mul_majorated hX_comp hY_comp
                      apply MS.basis_head_eventually_pos h_basis
                    · apply MS.basis_head_eventually_pos h_basis
                  simp only [motive]
                  use (l + 1) -- l + 1 = k
                  use ?_
                  use longAdd_mulMonomial_tail_fB BM left_deg hB_approx
                  use fM
                  use Seq.cons (X_deg, X_coef) X_tl
                  use Seq.cons (Y_deg, Y_coef) Y_tl
                  use fX
                  use fY
                  constructor
                  · rw [← h_right_eq.1.1, ← h_right_eq.1.2, ← h_right_eq.2]
                    congr 1
                    · exact h_left_tl_eq
                    · rw [mul_cons_cons]
                  constructor
                  · rw [← h_LC_eq]
                    simp [longAdd_mulMonomial_fC, longAdd_mulMonomial_tail_fB, longAdd_mulMonomial_tail_BM]
                    simp only [EventuallyEq] at hf_eq ⊢
                    apply Eventually.mono <| hf_eq.and (MS.basis_head_eventually_pos h_basis)
                    intro x ⟨hf_eq, h_pos⟩
                    rw [hf_eq]
                    move_add [← fX x * fY x]
                    ring_nf
                    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
                    congr
                    ext i
                    split_ifs with h_if
                    · generalize_proofs h1 h2

                      have hh := h1.choose_spec
                      generalize h1.choose = a at *
                      obtain ⟨coef1, tl1⟩ := a
                      replace h1 := hh
                      clear hh

                      have hh := h2.choose_spec
                      generalize h2.choose = C at *
                      replace h2 := hh
                      clear hh

                      simp only at h1 h2 ⊢
                      rw [Real.rpow_sub h_pos]
                      field_simp
                      ring_nf
                    · ring_nf
                  constructor
                  · exact longAdd_mulMonomial_tail_B_Approximates
                  constructor
                  · intro j
                    simp [longAdd_mulMonomial_tail_BM]
                    split_ifs with h
                    · simp
                      exact hM_approx j
                    · exact hM_approx j
                  constructor
                  · exact hX_approx
                  · exact hY_approx
                · use ?_; use ?_; use ?_; use (XC * YC)
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · rw [← h_right_eq.1.2]
                    exact mul_Approximates (MS.WellOrderedBasis_tail h_basis) hX_coef_approx hY_coef_approx
                  constructor
                  · apply majorated_of_EventuallyEq hf_eq
                    rw [← sup_of_le_right h2.le]
                    apply add_majorated
                    · exact h_left_comp
                    · rw [← h_right_eq.1.1]
                      apply mul_majorated hX_comp hY_comp
                      apply MS.basis_head_eventually_pos h_basis
                    · apply MS.basis_head_eventually_pos h_basis
                  rw [← h_left_eq, ← h_right_eq.2, ← add_assoc]
                  simp only [motive]
                  use (l + 2) -- l + 2 = k + 1
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (Y_tl, X_coef, X_deg)
                  | cast j => exact BM j
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (fun x ↦ fY x - basis_hd x ^ Y_deg * YC x)
                  | cast j => exact fB j
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact XC
                  | cast j => exact fM j
                  use X_tl
                  use Seq.cons (Y_deg, Y_coef) Y_tl
                  use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
                  use fY
                  constructor
                  · congr 1
                    conv => rhs; unfold longAdd
                    simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.natCast_eq_last]
                    congr 1
                    simp
                  constructor
                  · simp only [EventuallyEq] at hf_eq ⊢
                    apply Eventually.mono <| hf_eq.and (MS.basis_head_eventually_pos h_basis)
                    intro x ⟨hf_eq, h_pos⟩
                    rw [hf_eq]
                    conv =>
                      rhs; rw [Fin.sum_univ_castSucc]
                    simp
                    conv =>
                      rhs
                      rw [add_assoc]
                      arg 2
                      ring_nf
                    rw [← h_right_eq.left.left, Real.rpow_add h_pos]
                    conv =>
                      lhs
                      arg 2
                      ring_nf
                    rw [add_sub_assoc]
                    congr
                    ring
                  constructor
                  · intro j
                    cases j using Fin.lastCases with
                    | last =>
                      simp
                      exact hY_tl_approx
                    | cast j =>
                      simp
                      exact hB_approx j
                  constructor
                  · intro j
                    cases j using Fin.lastCases with
                    | last =>
                      simp
                      exact hX_coef_approx
                    | cast j =>
                      simp
                      exact hM_approx j
                  constructor
                  · exact hX_tl_approx
                  · exact hY_approx
                · have h_deg : right_deg = left_deg := by linarith -- I am here
                  subst h_deg h_deg'
                  clear h1 h2
                  use ?_; use ?_; use ?_; use (LC + XC * YC)
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · apply add_Approximates
                    · exact h_left_coef_approx
                    · rw [← h_right_eq.1.2]
                      apply mul_Approximates (MS.WellOrderedBasis_tail h_basis) hX_coef_approx hY_coef_approx
                  constructor
                  · apply majorated_of_EventuallyEq hf_eq
                    rw [← sup_idem deg']
                    apply add_majorated
                    · exact h_left_comp
                    · rw [← h_right_eq.1.1]
                      apply mul_majorated hX_comp hY_comp
                      apply MS.basis_head_eventually_pos h_basis
                    · apply MS.basis_head_eventually_pos h_basis
                  rw [← h_left_tl_eq', ← h_right_eq.2, ← add_assoc]
                  simp only [motive]
                  use l + 2
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (Y_tl, X_coef, X_deg)
                  | cast j => exact longAdd_mulMonomial_tail_BM BM deg' j
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (fun x ↦ fY x - basis_hd x ^ Y_deg * YC x)
                  | cast j => exact longAdd_mulMonomial_tail_fB BM deg' hB_approx j
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact XC
                  | cast j => exact fM j
                  use X_tl
                  use Seq.cons (Y_deg, Y_coef) Y_tl
                  use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
                  use fY
                  constructor
                  · congr 1
                    conv => rhs; unfold longAdd
                    simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.natCast_eq_last]
                    congr 1
                    · simp
                      congr 1
                      ext1 i
                      split_ifs with h1
                      · simp [longAdd_mulMonomial_tail_BM] -- copypaste
                        split_ifs
                        generalize_proofs h2 h3

                        have hh := h2.choose_spec -- ugly
                        generalize h2.choose = a2 at *
                        replace h2 := hh
                        clear hh

                        have hh := h3.choose_spec -- ugly
                        generalize h3.choose = a3 at *
                        replace h3 := hh
                        clear hh

                        rw [h3] at h2
                        simp [Seq.cons_eq_cons] at h2
                        exact h2.right.symm
                      · simp [longAdd_mulMonomial_tail_BM] -- copypaste
                        split_ifs
                        rfl
                    · simp
                  constructor
                  · rw [← h_LC_eq]
                    simp [longAdd_mulMonomial_fC, longAdd_mulMonomial_tail_fB, longAdd_mulMonomial_tail_BM]
                    simp only [EventuallyEq] at hf_eq ⊢
                    apply Eventually.mono <| hf_eq.and (MS.basis_head_eventually_pos h_basis)
                    intro x ⟨hf_eq, h_pos⟩
                    rw [hf_eq]
                    conv =>
                      lhs
                      arg 2
                      rw [mul_add, Finset.mul_sum]
                    conv =>
                      lhs
                      rw [sub_add_eq_sub_sub]
                      arg 1
                      rw [add_comm, add_sub_assoc, ← Finset.sum_sub_distrib, add_comm]
                    conv =>
                      lhs
                      rw [add_sub_assoc]
                    conv =>
                      rhs
                      rw [Fin.sum_univ_castSucc]
                      simp
                      rw [add_assoc]
                      arg 2
                      ring_nf
                    congr
                    · ext1 i
                      split_ifs with h_if
                      · generalize_proofs h1 h2

                        have hh := h1.choose_spec
                        generalize h1.choose = a at *
                        obtain ⟨coef1, tl1⟩ := a
                        replace h1 := hh
                        clear hh

                        have hh := h2.choose_spec
                        generalize h2.choose = C at *
                        replace h2 := hh
                        clear hh

                        simp only at h1 h2 ⊢
                        rw [Real.rpow_sub h_pos]
                        field_simp
                        ring_nf
                      · ring_nf
                    · rw [← h_right_eq.left.left, Real.rpow_add h_pos]
                      ring
                  constructor
                  · intro j
                    cases j using Fin.lastCases with
                    | last =>
                      simp
                      exact hY_tl_approx
                    | cast j =>
                      simp
                      apply longAdd_mulMonomial_tail_B_Approximates
                  constructor
                  · intro j
                    cases j using Fin.lastCases with
                    | last =>
                      simp
                      exact hX_coef_approx
                    | cast j =>
                      simp
                      simp [longAdd_mulMonomial_tail_BM]
                      split_ifs with h
                      · simp
                        apply hM_approx
                      · apply hM_approx
                  constructor
                  · exact hX_tl_approx
                  · exact hY_approx
end

end PreMS

noncomputable def MS.mul (x y : MS) (h_basis_eq : y.basis = x.basis) (h_basis_wo : MS.WellOrderedBasis x.basis) : MS where
  basis := x.basis
  val := x.val.mul (h_basis_eq ▸ y.val)
  F := x.F * y.F
  h_wo := by
    have := y.h_wo
    apply PreMS.mul_WellOrdered x.h_wo
    generalize y.val = z at *
    generalize y.basis = b at *
    subst h_basis_eq
    simpa
  h_approx := by
    have := y.h_approx
    apply PreMS.mul_Approximates h_basis_wo x.h_approx
    generalize y.val = z at *
    generalize y.basis = b at *
    subst h_basis_eq
    simpa

end TendstoTactic
