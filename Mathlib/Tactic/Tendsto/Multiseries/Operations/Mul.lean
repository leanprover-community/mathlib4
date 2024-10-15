import Mathlib.Tactic.Tendsto.Multiseries.Operations.Merge

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

namespace PreMS

mutual
  noncomputable def mul {basis : Basis} (a b : PreMS basis) : PreMS basis :=
    match basis with
    | [] => a * b
    | basis_hd :: basis_tl =>
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
    mul CoList.nil ms = .nil := by
  simp [mul, merge1_nil]

@[simp]
theorem mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    mul ms CoList.nil = .nil := by
  simp [mul, mulMonomial]
  apply ms.casesOn <;> simp

@[simp]
theorem mulMonomial_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {m_deg : ℝ} {m_coef : PreMS basis_tl} :
    mulMonomial (basis_hd := basis_hd) CoList.nil m_coef m_deg = .nil := by
  simp [mulMonomial]

@[simp]
theorem mulMonomial_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg m_deg : ℝ} {x_coef m_coef : PreMS basis_tl}
    {x_tl : PreMS (basis_hd :: basis_tl)} :
    mulMonomial (basis_hd := basis_hd) (CoList.cons (x_deg, x_coef) x_tl) m_coef m_deg =
    .cons (m_deg + x_deg, mul m_coef x_coef) (mulMonomial x_tl m_coef m_deg) := by
  simp [mulMonomial]

theorem mul_cons_cons_head {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg y_deg : ℝ} {x_coef y_coef : PreMS basis_tl}
    {x_tl y_tl : PreMS (basis_hd :: basis_tl)} :
    (mul (basis := basis_hd :: basis_tl) (CoList.cons (x_deg, x_coef) x_tl) (CoList.cons (y_deg, y_coef) y_tl)).head =
    .some (x_deg + y_deg, x_coef.mul y_coef) := by
  simp [mul]

theorem mul_eq_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X Y : PreMS (basis_hd :: basis_tl)} (h : X.mul Y = CoList.nil) :
    X = .nil ∨ Y = .nil := by
  revert h
  apply X.casesOn
  · simp
  · intro (X_deg, X_coef) X_tl
    apply Y.casesOn
    · simp
    · intro (Y_deg, Y_coef) Y_tl h
      apply_fun CoList.head at h
      simp [mul_cons_cons_head] at h

theorem mul_eq_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ} {coef : PreMS basis_tl}
    {tl X Y : PreMS (basis_hd :: basis_tl)} (h : X.mul Y = .cons (deg, coef) tl) :
    ∃ X_deg X_coef X_tl Y_deg Y_coef Y_tl, X = .cons (X_deg, X_coef) X_tl ∧ Y = .cons (Y_deg, Y_coef) Y_tl := by
  revert h
  apply X.casesOn
  · simp
  · intro (X_deg, X_coef) X_tl
    apply Y.casesOn
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
    mul (basis := basis_hd :: basis_tl) (CoList.cons (x_deg, x_coef) x_tl) (CoList.cons (y_deg, y_coef) y_tl) =
    CoList.cons (x_deg + y_deg, x_coef.mul y_coef) ((mulMonomial y_tl x_coef x_deg).add
      (x_tl.mul (CoList.cons (y_deg, y_coef) y_tl))) := by
  simp [mul, merge1_cons_head_cons]

-- TODO: lots of copypaste from `mul_cons_cons`
-- @[simp]
-- theorem mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg : ℝ} {x_coef : PreMS basis_tl}
--     {x_tl y : PreMS (basis_hd :: basis_tl)} :
--     mul (CoList.cons (x_deg, x_coef) x_tl) y = (mulMonomial y x_coef x_deg).add (x_tl.mul y) := by
--   apply y.casesOn
--   · simp
--   · intro (y_deg, y_coef) y_tl
--     simp
--     rw [add_cons_cons]


--   by_cases hy : y = CoList.nil
--   · simp [hy]
--   replace hy : y.leadingExp ≠ ⊥ := by
--     revert hy
--     apply y.casesOn
--     · simp
--     · simp [leadingExp]
--   simp [mul]
--   obtain ⟨hx_coef_wo, hx_comp, hx_tl_wo⟩ := wellOrdered_cons hx_wo
--   rw [merge1_cons_eq_add]
--   · let motive : CoList (PreMS (basis_hd :: basis_tl)) → Prop := fun li =>
--       ∃ (z : PreMS (basis_hd :: basis_tl)), li = CoList.map (fun x ↦ y.mulMonomial x.2 x.1) z ∧
--       z.wellOrdered
--     apply CoList.Sorted.coind (r := (fun x1 x2 ↦ x1 > x2)) (motive := motive) -- why do I need to specify r?
--     · intro hd tl ih
--       simp only [motive] at ih
--       obtain ⟨z, h_eq, hz_wo⟩ := ih
--       revert h_eq hz_wo
--       apply z.casesOn
--       · simp
--       · intro (z_deg, z_coef) z_tl h_eq hz_wo
--         simp at h_eq
--         obtain ⟨hz_coef_wo, hz_comp, hz_tl_wo⟩ := wellOrdered_cons hz_wo
--         rw [h_eq.left, h_eq.right]
--         constructor
--         · revert hz_comp
--           apply z_tl.casesOn
--           · simp
--           · intro (z_tl_hd_deg, z_tl_hd_coef) z_tl_tl hz_comp
--             simp [lt_iff_lt]
--             apply WithBot.add_lt_add_right
--             · exact hy
--             · simpa [leadingExp] using hz_comp
--         · simp only [motive]
--           use z_tl
--     · simp only [motive]
--       use (CoList.cons (x_deg, x_coef) x_tl)
--       simp
--       exact hx_wo


-- TODO : can be proven without coinduction?
@[simp]
theorem mul_one' {basis : Basis} {ms : PreMS basis} : mul ms (one basis) = ms := by
  cases basis with
  | nil => simp [mul, one, const]
  | cons basis_hd basis_tl =>
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      x = y.mul (one (basis_hd :: basis_tl))
    apply CoList.Eq.coind motive
    · intro a b ih
      simp only [motive] at ih
      subst ih
      apply b.casesOn
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
        · simp [one, const]
          apply mul_one'
    · simp only [motive]

@[simp]
theorem one_mul' {basis : Basis} {ms : PreMS basis} : mul (one basis) ms = ms := by
  cases basis with
  | nil => simp [mul, one, const]
  | cons basis_hd basis_tl =>
    simp [one, const, mul]
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
      x = y.mulMonomial (const 1 basis_tl) 0
    apply CoList.Eq.coind motive
    · intro x y ih
      subst ih
      apply y.casesOn
      · simp
      · intro (deg, coef) tl
        left
        use ?_, ?_, ?_
        simp
        constructor
        · constructor <;> exact Eq.refl _
        · constructor
          · constructor
            · congr
              symm
              apply one_mul'
            · exact Eq.refl _
          · simp only [motive]
    · simp only [motive]

@[simp]
theorem mul_assoc' {basis : Basis} {X Y Z : PreMS basis} :
    (X.mul Y).mul Z = X.mul (Y.mul Z) := by
  sorry

noncomputable def longAdd {basis : Basis} {k : ℕ} (args : Fin k → PreMS basis) : PreMS basis :=
  match k with
  | 0 => zero _
  | m + 1 =>
    let args' : Fin m → PreMS basis := fun i ↦ args i.castSucc
    (longAdd args').add (args m)

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

theorem longAdd_zeros {basis : Basis} {k : ℕ} : longAdd (fun (i : Fin k) ↦ zero basis) = zero basis := by
  induction k with
  | zero => simp [longAdd]
  | succ k ih => simp [longAdd, ih]

theorem longAdd_nils {basis_hd : ℝ → ℝ} {basis_tl : Basis} {k : ℕ} : longAdd (fun (i : Fin k) ↦ CoList.nil) = zero (basis_hd :: basis_tl) := by
  rw [show CoList.nil = zero (basis_hd :: basis_tl) by simp [zero], longAdd_zeros]

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
          (zero _, args i)

      let coef := longAdd fun i ↦(coef_tl_args i).1
      let tl := longAdd fun i ↦(coef_tl_args i).2
      .cons (deg, coef) tl

theorem longAdd_eq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {k : ℕ}
    {args : Fin k → PreMS (basis_hd :: basis_tl)} :
    longAdd args = longAdd' args := by
  induction k with
  | zero => simp [longAdd, longAdd', zero]
  | succ k ih =>
    simp [longAdd']
    -- наводим красоту
    generalize_proofs inst _
    generalize h_deg : (Finset.univ.sup' inst fun i ↦ (args i).leadingExp) = deg?
    -- навели
    cases deg? with
    | bot =>
      simp
      replace h_deg := Finset.sup'_eq_bot.mp h_deg
      simp at h_deg
      have : args = fun _ ↦ .nil := by
        ext i
        specialize h_deg i
        exact leadingExp_eq_bot.mpr h_deg
      rw [this]
      exact longAdd_nils
    | coe deg =>
      -- наводим красоту
      simp
      generalize_proofs h_coefs_tls
      generalize h_coef_tl_args : (fun i ↦ (if h : (args i).leadingExp = ↑deg then (h_coefs_tls i h).choose else (zero basis_tl, args i))) = coef_tl_args
      generalize h_coef : longAdd (fun i ↦ (coef_tl_args i).1) = coef
      generalize h_tl : longAdd (fun i ↦ (coef_tl_args i).2) = tl
      rw [show longAdd (fun i ↦ (if h : (args i).leadingExp = ↑deg then (h_coefs_tls i h).choose else (zero basis_tl, args i)).1) =
        coef by rw [← h_coef, ← h_coef_tl_args]]
      rw [show longAdd (fun i ↦ (if h : (args i).leadingExp = ↑deg then (h_coefs_tls i h).choose else (zero basis_tl, args i)).2) =
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
          replace h_deg' := Finset.sup'_eq_bot.mp h_deg'
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
          simp only [longAdd, ← h_coef_tl_args, this,
            show leadingExp CoList.nil = ⊥ by simp [leadingExp], WithBot.bot_ne_coe, ↓reduceDIte,
            longAdd_zeros, Fin.natCast_eq_last, add_zero', Nat.cast_one, zero_add',
            longAdd_nils, add_nil, h_last] at h_coef h_tl
          rw [← h_coef, ← h_tl]
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
              else (zero basis_tl, args i.castSucc))) = coef_tl_args'
          generalize h_coef' : longAdd (fun i ↦ (coef_tl_args' i).1) = coef'
          generalize h_tl' : longAdd (fun i ↦ (coef_tl_args' i).2) = tl'
          rw [show longAdd (fun i ↦
            (if h : (args i.castSucc).leadingExp = ↑deg' then (h_coefs_tls' i h).choose
              else (zero basis_tl, args i.castSucc)).1) =
            coef' by rw [← h_coef', ← h_coef_tl_args']]
          rw [show (longAdd fun i ↦
            (if h : (args i.castSucc).leadingExp = ↑deg' then (h_coefs_tls' i h).choose
              else (zero basis_tl, args i.castSucc)).2) =
            tl' by rw [← h_tl', ← h_coef_tl_args']]
          -- навели
          have h_left_eq : (longAdd fun i ↦ args i.castSucc) = CoList.cons (deg', coef') tl' := by
            rw [ih]
            simp [longAdd']
            have : ∀ i h, h_coefs_tls_ deg' i h = h_coefs_tls' i h := by
              intro i h
              rfl
            generalize_proofs
            simp [h_deg']
            constructor
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
            apply cons_add h_lt
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
            apply a.casesOn
            · intro h_eq h1 h_coef h_tl
              simp [leadingExp] at h_eq
            · intro (a_deg, a_coef) a_tl h_eq h1 h_tl h_coef
              simp [leadingExp] at h_eq
              subst h_eq
              have h_out : CoList.out (add (basis := basis_hd :: basis_tl) (CoList.cons (a_deg, coef') tl') (CoList.cons (a_deg, a_coef) a_tl)) =
                ?_ := by exact add_out_eq
              simp [add_out] at h_out
              rw [CoList.out_eq_cons h_out]
              congr
              · have := h1.choose_spec
                simp at this
                simp [← h_coef]
                congr
                exact this.left
              · have := h1.choose_spec
                simp at this
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
            simp only [↓reduceDIte, longAdd_zeros, zero_add'] at h_coef
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
            apply a.casesOn
            · intro h_deg
              simp [leadingExp] at h_deg
            · intro (a_deg, a_coef) a_tl h_deg h_lt h1 h_coef h_tl
              simp [leadingExp] at h_deg h_lt
              subst h_deg
              rw [add_cons_right]
              · congr
                · have := h1.choose_spec
                  replace this := CoList.cons_eq_cons.mp this
                  simp only [Prod.mk.injEq, true_and] at this
                  exact this.left
                · have := h1.choose_spec
                  replace this := CoList.cons_eq_cons.mp this
                  simp only [Prod.mk.injEq, true_and] at this
                  exact this.right
              · simpa [leadingExp]

theorem longAdd_wellOrdered {basis : Basis} {k : ℕ} {args : Fin k → PreMS basis}
    (h_wo : ∀ i, (args i).wellOrdered) : (longAdd args).wellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    induction k with
    | zero => simp [longAdd, zero, wellOrdered.nil]
    | succ k ih =>
      unfold longAdd
      apply add_wellOrdered
      · apply ih
        intro i
        apply h_wo
      · apply h_wo

theorem longAdd_isApproximation {basis : Basis} {k : ℕ} {args : Fin k → PreMS basis}
    {F : Fin k → (ℝ → ℝ)}
    (h_approx : ∀ i, (args i).isApproximation (F i) basis) :
    (longAdd args).isApproximation (fun x ↦ ∑ i, F i x) := by
  cases basis with
  | nil =>
    simp [isApproximation] at *
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
      apply isApproximation.nil
      rfl
    | succ k ih =>
      conv =>
        arg 1
        ext x
        rw [Fin.sum_univ_castSucc]
      unfold longAdd
      apply add_isApproximation
      · apply ih
        intro i
        apply h_approx
      · simp only [Fin.natCast_eq_last]
        apply h_approx

@[simp]
theorem mulMonomial_leadingExp {basis_hd : _} {basis_tl : _} {b : PreMS (basis_hd :: basis_tl)}
    {m_coef : PreMS basis_tl} {m_deg : ℝ} :
    (mulMonomial b m_coef m_deg).leadingExp = m_deg + b.leadingExp := by
  apply b.casesOn
  · simp [leadingExp]
  · intro (b_deg, b_coef) b_tl
    simp [leadingExp]

@[simp]
theorem mul_leadingExp {basis_hd : _} {basis_tl : _} {x y : PreMS (basis_hd :: basis_tl)} :
    (mul x y).leadingExp = x.leadingExp + y.leadingExp := by
  apply x.casesOn
  · simp [leadingExp]
  intro (x_deg, x_coef) x_tl
  apply y.casesOn
  · simp [leadingExp]
  intro (y_deg, y_coef) y_tl
  have : CoList.head (mul (basis := basis_hd :: basis_tl) (CoList.cons (x_deg, x_coef) x_tl) (CoList.cons (y_deg, y_coef) y_tl)) = .some ?_ := by
    exact mul_cons_cons_head
  simp [leadingExp_of_head, this]

noncomputable def longAdd_mulMonomial_tail_BM {basis_hd : _} {basis_tl : _} {k : ℕ}
    (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)) (deg : ℝ) :
    Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ) :=
  match k with
  | 0 => default
  | l + 1 =>
    have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg →
        ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
        (BM i).1 = CoList.cons (deg - (BM i).2.2, a.1) a.2 := by
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
    CoList.cons (deg, coef) tl) :
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
      simp at h_eq_cons
      obtain ⟨⟨h_deg, _⟩, h_tl_eq⟩ := h_eq_cons
      subst h_deg

      rw [← h_tl_eq]
      simp [longAdd_mulMonomial_tail_BM]
      congr 1
      ext i
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
        simp at h1
        exact h1.right.symm
      · simp

theorem longAdd_mulMonomial_tail_B_wellOrdered {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    (h_wo : ∀ j, (BM j).1.wellOrdered) :
    ∀ j, (longAdd_mulMonomial_tail_BM BM deg j).1.wellOrdered := by
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
      have := wellOrdered_cons this
      exact this.2.2
    · exact h_wo j

theorem longAdd_mulMonomial_tail_M_wellOrdered {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    (h_wo : ∀ j, (BM j).2.1.wellOrdered) :
    ∀ j, (longAdd_mulMonomial_tail_BM BM deg j).2.1.wellOrdered := by
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

theorem longAdd_mulMonomial_tail_BM_wellOrdered {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    (h_wo : ∀ j, (BM j).1.wellOrdered ∧ (BM j).2.1.wellOrdered) :
    ∀ j, (longAdd_mulMonomial_tail_BM BM deg j).1.wellOrdered ∧
      (longAdd_mulMonomial_tail_BM BM deg j).2.1.wellOrdered := by
  intro j
  constructor
  · apply longAdd_mulMonomial_tail_B_wellOrdered
    exact fun j ↦ (h_wo j).left
  · apply longAdd_mulMonomial_tail_M_wellOrdered
    exact fun j ↦ (h_wo j).right

noncomputable def longAdd_mulMonomial_tail_fB {basis_hd : _} {basis_tl : _} {k : ℕ}
    (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)) (deg : ℝ)
    {fB : Fin k → (ℝ → ℝ)}
    (hB_approx : ∀ j, (BM j).1.isApproximation (fB j) (basis_hd :: basis_tl)) :
    Fin k → (ℝ → ℝ) :=
  match k with
  | 0 => default
  | l + 1 =>
    have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg →
        ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
        (BM i).1 = CoList.cons (deg - (BM i).2.2, a.1) a.2 := by
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
          replace hB_approx := isApproximation_cons hB_approx
          let C := hB_approx.choose
          exact fun x ↦ fB i x - basis_hd x ^ (deg - (BM i).2.2) * C x
      else
        fB i

theorem longAdd_mulMonomial_tail_B_isApproximation {basis_hd : _} {basis_tl : _} {k : ℕ}
    {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
    {fB : Fin k → (ℝ → ℝ)}
    {hB_approx : ∀ j, (BM j).1.isApproximation (fB j) (basis_hd :: basis_tl)} : ∀ (j : Fin k),
    isApproximation (longAdd_mulMonomial_tail_fB BM deg hB_approx j) (basis_hd :: basis_tl)
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
    (hB_approx : ∀ j , (BM j).1.isApproximation (fB j) (basis_hd :: basis_tl))
    (hM_approx : ∀ j , (BM j).2.1.isApproximation (fM j) basis_tl) :
    ℝ → ℝ :=
  match k with
  | 0 => default
  | l + 1 =>
    have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg →
        ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
        (BM i).1 = CoList.cons (deg - (BM i).2.2, a.1) a.2 := by
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
          replace hB_approx := isApproximation_cons hB_approx
          let fBC := hB_approx.choose
          exact (fM i x) * (fBC x)
      else
        0
    )

mutual
  theorem mulMonomial_wellOrdered {basis_hd : _} {basis_tl : _} {b : PreMS (basis_hd :: basis_tl)}
      {m_coef : PreMS basis_tl} {m_deg : ℝ}
      (hb_wo : b.wellOrdered) (hm_wo : m_coef.wellOrdered) :
      (mulMonomial b m_coef m_deg).wellOrdered := by
    let motive : PreMS (basis_hd :: basis_tl) → Prop := fun x =>
      ∃ (b : PreMS (basis_hd :: basis_tl)), x = b.mulMonomial m_coef m_deg ∧
      b.wellOrdered
    apply wellOrdered.coind motive
    · intro ms ih
      simp only [motive] at ih
      obtain ⟨b, h_eq, hb_wo⟩ := ih
      subst h_eq
      revert hb_wo
      apply b.casesOn
      · intro
        left
        simp
      · intro (deg, coef) tl h_wo
        have h_wo' := wellOrdered_cons h_wo
        obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := h_wo'
        right
        use ?_
        use ?_
        use ?_
        constructor
        · simp only [mulMonomial_cons]
          congr <;> exact Eq.refl _
        constructor
        · apply mul_wellOrdered hm_wo h_coef_wo
        constructor
        · simp
          apply WithBot.add_lt_add_left
          · simp
          · exact h_comp
        simp only [motive]
        use tl
    · simp only [motive]
      use b

  -- TODO: very ugly. rewrite
  theorem mul_wellOrdered {basis : Basis} {X Y : PreMS basis}
      (hX_wo : X.wellOrdered) (hY_wo : Y.wellOrdered) :
      (X.mul Y).wellOrdered := by
    cases basis with
    | nil => constructor
    | cons basis_hd basis_tl =>
      let motive : PreMS (basis_hd :: basis_tl) → Prop := fun x =>
        ∃ (k : ℕ) (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ))
          (X Y : PreMS (basis_hd :: basis_tl)),
          x = (longAdd <| (fun (B, M_coef, M_deg) => B.mulMonomial M_coef M_deg) ∘ BM).add (X.mul Y) ∧
          (∀ j , (BM j).1.wellOrdered ∧ (BM j).2.1.wellOrdered) ∧
          X.wellOrdered ∧ Y.wellOrdered
      apply wellOrdered.coind motive
      · intro ms ih
        simp only [motive] at ih
        obtain ⟨k, BM, X, Y, h_eq, h_BM, hX_wo, hY_wo⟩ := ih
        generalize h_left_eq : (longAdd ((fun x ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM)) = left at h_eq
        generalize h_right_eq : X.mul Y = right at h_eq

        have h_left_wo : left.wellOrdered := by
          rw [← h_left_eq]
          apply longAdd_wellOrdered
          intro i
          simp
          apply mulMonomial_wellOrdered
          · exact (h_BM i).left
          · exact (h_BM i).right
        subst h_eq
        revert h_left_eq h_left_wo
        apply left.casesOn
        · intro h_left_eq h_left_wo
          simp
          revert h_right_eq
          apply right.casesOn
          · simp
          · intro (right_deg, right_coef) right_tl h_right_eq
            simp
            use right_deg
            use right_coef
            use right_tl
            simp
            obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
            subst hX_eq hY_eq
            obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := wellOrdered_cons hX_wo
            obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := wellOrdered_cons hY_wo
            simp only [mul_cons_cons, CoList.cons_eq_cons, Prod.mk.injEq] at h_right_eq
            obtain ⟨⟨h_deg, h_coef⟩, h_tl⟩ := h_right_eq
            subst h_deg h_coef h_tl
            constructor
            · apply mul_wellOrdered hX_coef_wo hY_coef_wo
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
              · apply wellOrdered.cons <;> assumption
        · intro (left_deg, left_coef) left_tl h_left_eq h_left_wo
          obtain ⟨h_left_coef_wo, h_left_comp, h_left_tl_wo⟩ := wellOrdered_cons h_left_wo
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
              simp only [CoList.cons_eq_cons, Prod.mk.injEq] at h_left_eq'
              obtain ⟨⟨h_deg', h_left_coef_eq⟩, h_left_tl_eq'⟩ := h_left_eq'
              have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg' →
                  ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
                  (BM i).1 = CoList.cons (deg' - (BM i).2.2, a.1) a.2 := by
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
              apply right.casesOn
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
                · exact longAdd_mulMonomial_tail_BM_wellOrdered h_BM
                · constructor <;> exact wellOrdered.nil
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
                  · exact longAdd_mulMonomial_tail_BM_wellOrdered h_BM
                  constructor
                  · exact hX_wo
                  · exact hY_wo
                · obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
                  subst hX_eq hY_eq
                  obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := wellOrdered_cons hX_wo
                  obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := wellOrdered_cons hY_wo
                  simp only [mul_cons_cons, CoList.cons_eq_cons, Prod.mk.injEq] at h_right_eq
                  use ?_; use ?_; use ?_
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · rw [← h_right_eq.1.2]
                    apply mul_wellOrdered hX_coef_wo hY_coef_wo
                  constructor
                  · simp
                    constructor
                    · simpa [leadingExp]
                    · rw [← h_right_eq.2, ← h_right_eq.1.1]
                      simp
                      constructor
                      · apply WithBot.add_lt_add_left
                        · simp
                        · exact hY_comp
                      · apply WithBot.add_lt_add_right
                        · simp
                        · exact hX_comp
                  rw [← h_left_eq, ← h_right_eq.2, ← add_assoc']
                  simp only [motive]
                  use (l + 2) -- l + 2 = k + 1
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (Y_tl, X_coef, X_deg)
                  | cast j => exact BM j
                  use X_tl
                  use CoList.cons (Y_deg, Y_coef) Y_tl
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
                  obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := wellOrdered_cons hX_wo
                  obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := wellOrdered_cons hY_wo
                  simp only [mul_cons_cons, CoList.cons_eq_cons, Prod.mk.injEq] at h_right_eq
                  use ?_; use ?_; use ?_
                  constructor
                  · congr 2 <;> exact Eq.refl _
                  constructor
                  · apply add_wellOrdered
                    · exact h_left_coef_wo
                    · rw [← h_right_eq.1.2]
                      apply mul_wellOrdered hX_coef_wo hY_coef_wo
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
                  rw [← h_left_tl_eq', ← h_right_eq.2, ← add_assoc']
                  simp only [motive]
                  use l + 2
                  use fun i => by cases i using Fin.lastCases with
                  | last => exact (Y_tl, X_coef, X_deg)
                  | cast j => exact longAdd_mulMonomial_tail_BM BM deg' j
                  use X_tl
                  use CoList.cons (Y_deg, Y_coef) Y_tl
                  constructor
                  · congr 1
                    conv => rhs; unfold longAdd
                    simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.natCast_eq_last]
                    congr 1
                    · simp
                      congr 1
                      ext i
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
                        simp at h2
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
                      exact longAdd_mulMonomial_tail_BM_wellOrdered h_BM j
                  constructor
                  · exact hX_tl_wo
                  · exact hY_wo
      · simp only [motive]
        use 0
        use default
        use X
        use Y
        simp [longAdd, zero]
        constructor <;> assumption

end

set_option maxHeartbeats 400000 in -- TODO : very slow. May be speed up?
mutual

  theorem mulMonomial_isApproximation {basis_hd : _} {basis_tl : _} {B M : ℝ → ℝ} {b : PreMS (basis_hd :: basis_tl)}
        {m_coef : PreMS basis_tl} {m_deg : ℝ}
        (h_basis : MS.wellOrderedBasis (basis_hd :: basis_tl))
        (hb_approx : b.isApproximation B (basis_hd :: basis_tl))
        (hm_approx : m_coef.isApproximation M basis_tl) :
      (mulMonomial b m_coef m_deg).isApproximation (fun x ↦ (M x) * (basis_hd x)^m_deg * (B x)) := by
    let motive : (ℝ → ℝ) → PreMS (basis_hd :: basis_tl) → Prop := fun f ms =>
      ∃ (b : PreMS (basis_hd :: basis_tl)) (B M : ℝ → ℝ),
      ms = b.mulMonomial m_coef m_deg ∧
      f =ᶠ[atTop] (fun x ↦ (M x) * (basis_hd x)^m_deg * (B x)) ∧
      b.isApproximation B (basis_hd :: basis_tl) ∧ m_coef.isApproximation M basis_tl
    apply isApproximation.coind motive
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨b, B, M, h_ms_eq, hf_eq, hb_approx, hm_approx⟩ := ih
      subst h_ms_eq
      revert hb_approx
      apply b.casesOn
      · intro hb_approx
        replace hb_approx := isApproximation_nil hb_approx
        left
        simp
        conv => rhs; ext x; simp; rw [← mul_zero (M x * basis_hd x ^ m_deg)]
        trans
        · exact hf_eq
        apply EventuallyEq.mul (by rfl) hb_approx
      · intro (b_deg, b_coef) b_tl hb_approx
        have hb_approx' := isApproximation_cons hb_approx
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
        · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis) hm_approx h_coef_approx
        constructor
        · apply majorated_of_EventuallyEq hf_eq
          rw [show m_deg + b_deg = 0 + m_deg + b_deg by simp]
          apply mul_majorated
          · apply mul_majorated
            · exact isApproximation_coef_isLittleO_head hm_approx h_basis
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
    · simp only [motive]
      use b
      use B
      use M

  theorem longAdd_mulMonomial_cons_isApproximation_coef {basis_hd : _} {basis_tl : _} {k : ℕ}
      {BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ)} {deg : ℝ}
      {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
      {fB fM : Fin k → (ℝ → ℝ)}
      (h_basis : MS.wellOrderedBasis (basis_hd :: basis_tl))
      (hB_approx : ∀ j, (BM j).1.isApproximation (fB j) (basis_hd :: basis_tl))
      (hM_approx : ∀ j, (BM j).2.1.isApproximation (fM j) basis_tl)
      (h_cons : (longAdd ((fun x ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM)) = CoList.cons (deg, coef) tl) :
      coef.isApproximation (longAdd_mulMonomial_fC deg hB_approx hM_approx) basis_tl := by
    induction k generalizing deg coef with
    | zero =>
      simp [longAdd, zero] at h_cons
    | succ l ih =>
      rw [longAdd_eq] at h_cons
      simp [longAdd'] at h_cons
      generalize_proofs inst h_coef_tl_args at h_cons
      generalize h_deg? : (Finset.univ.sup' inst fun x ↦ ↑(BM x).2.2 + (BM x).1.leadingExp) = deg? at h_cons
      cases deg? with
      | bot => simp at h_cons
      | coe deg' =>
        simp at h_cons
        obtain ⟨⟨h_deg, h_coef⟩, h_tl⟩ := h_cons
        subst h_deg
        rw [← h_coef]
        apply longAdd_isApproximation
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
          simp at h3
          rw [← h3.left]
          apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis)
          · apply hM_approx
          · exact h2.left
        · simp
          exact zero_isApproximation_zero

  theorem mul_isApproximation {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
      (h_basis : MS.wellOrderedBasis basis)
      (hX_approx : X.isApproximation fX basis) (hY_approx : Y.isApproximation fY basis) :
      (X.mul Y).isApproximation (fX * fY) basis := by
    cases basis with
    | nil =>
      simp [isApproximation, mul] at *
      apply EventuallyEq.mul hX_approx hY_approx
    | cons basis_hd basis_tl =>
      let motive : (ℝ → ℝ) → PreMS (basis_hd :: basis_tl) → Prop := fun f ms =>
        ∃ (k : ℕ) (BM : Fin k → (PreMS (basis_hd :: basis_tl) × (PreMS basis_tl) × ℝ))
          (fB fM : Fin k → (ℝ → ℝ))
          (X Y : PreMS (basis_hd :: basis_tl))
          (fX fY : ℝ → ℝ),
          ms = (longAdd <| (fun (B, M_coef, M_deg) => B.mulMonomial M_coef M_deg) ∘ BM).add (X.mul Y) ∧
          f =ᶠ[atTop] (fun x ↦ (∑ i, (fM i x) * (basis_hd x)^(BM i).2.2 * (fB i x)) + (fX x) * (fY x)) ∧ -- I am here. Need finite sum of BM
          (∀ j , (BM j).1.isApproximation (fB j) (basis_hd :: basis_tl)) ∧
          (∀ j , (BM j).2.1.isApproximation (fM j) basis_tl) ∧
          X.isApproximation fX (basis_hd :: basis_tl) ∧
          Y.isApproximation fY (basis_hd :: basis_tl)
      apply isApproximation.coind motive
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
            replace hX_approx := isApproximation_nil hX_approx
            conv => rhs; ext x; simp; rw [← zero_mul (fY x)]
            exact EventuallyEq.mul hX_approx (by rfl)
          | inr hY =>
            subst hY
            replace hY_approx := isApproximation_nil hY_approx
            conv => rhs; ext x; simp; rw [← mul_zero (fX x)]
            exact EventuallyEq.mul (by rfl) hY_approx

        have h_left_approx : left.isApproximation
            (fun x ↦ ∑ i, (fM i x) * (basis_hd x)^(BM i).2.2 * (fB i x)) (basis_hd :: basis_tl) := by
          rw [← h_left_eq]

          apply longAdd_isApproximation
          intro i
          simp
          apply mulMonomial_isApproximation h_basis
          · exact hB_approx i
          · exact hM_approx i
        subst h_ms_eq
        revert h_left_eq h_left_approx
        apply left.casesOn
        · intro h_left_eq h_left_approx
          replace h_left_approx := isApproximation_nil h_left_approx
          replace hf_eq : f =ᶠ[atTop] fX * fY := by
            trans
            · exact hf_eq
            conv => rhs; ext x; simp; rw [← zero_add (fX x * fY x)]
            apply EventuallyEq.add h_left_approx (by rfl)
          simp
          revert h_right_eq
          apply right.casesOn
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
            obtain ⟨XC, hX_coef_approx, hX_comp, hX_tl_approx⟩ := isApproximation_cons hX_approx
            obtain ⟨YC, hY_coef_approx, hY_comp, hY_tl_approx⟩ := isApproximation_cons hY_approx
            simp only [mul_cons_cons, CoList.cons_eq_cons, Prod.mk.injEq] at h_right_eq

            obtain ⟨⟨h_deg, h_coef⟩, h_tl⟩ := h_right_eq
            subst h_deg h_coef h_tl
            use XC * YC
            constructor
            · apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis) hX_coef_approx hY_coef_approx
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
          obtain ⟨LC', h_left_coef_approx, h_left_comp, h_left_tl_approx⟩ := isApproximation_cons h_left_approx
          replace h_left_coef_approx := longAdd_mulMonomial_cons_isApproximation_coef h_basis hB_approx hM_approx h_left_eq -- Nasty workaround
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
              simp only [CoList.cons_eq_cons, Prod.mk.injEq] at h_left_eq'
              obtain ⟨⟨h_deg', h_left_coef_eq⟩, h_left_tl_eq'⟩ := h_left_eq'
              have h_BM_cons : ∀ i, ((BM i).1.mulMonomial (BM i).2.1 (BM i).2.2).leadingExp = ↑deg' →
                  ∃ (a : PreMS basis_tl × PreMS (basis_hd :: basis_tl)),
                  (BM i).1 = CoList.cons (deg' - (BM i).2.2, a.1) a.2 := by
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
              apply right.casesOn
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
                · apply longAdd_mulMonomial_tail_B_isApproximation
                constructor
                · intro j
                  simp [longAdd_mulMonomial_tail_BM]
                  split_ifs with h
                  · simp
                    exact hM_approx j
                  · exact hM_approx j
                constructor
                · apply isApproximation.nil (by rfl)
                · apply isApproximation.nil (by rfl)
              · intro (right_deg, right_coef) right_tl h_right_eq
                obtain ⟨X_deg, X_coef, X_tl, Y_deg, Y_coef, Y_tl, hX_eq, hY_eq⟩ := mul_eq_cons h_right_eq
                subst hX_eq hY_eq
                obtain ⟨XC, hX_coef_approx, hX_comp, hX_tl_approx⟩ := isApproximation_cons hX_approx
                obtain ⟨YC, hY_coef_approx, hY_comp, hY_tl_approx⟩ := isApproximation_cons hY_approx
                simp only [mul_cons_cons, CoList.cons_eq_cons, Prod.mk.injEq] at h_right_eq

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
                  use CoList.cons (X_deg, X_coef) X_tl
                  use CoList.cons (Y_deg, Y_coef) Y_tl
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
                  · exact longAdd_mulMonomial_tail_B_isApproximation
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
                    exact mul_isApproximation (MS.wellOrderedBasis_tail h_basis) hX_coef_approx hY_coef_approx
                  constructor
                  · apply majorated_of_EventuallyEq hf_eq
                    rw [← sup_of_le_right h2.le]
                    apply add_majorated
                    · exact h_left_comp
                    · rw [← h_right_eq.1.1]
                      apply mul_majorated hX_comp hY_comp
                      apply MS.basis_head_eventually_pos h_basis
                    · apply MS.basis_head_eventually_pos h_basis
                  rw [← h_left_eq, ← h_right_eq.2, ← add_assoc']
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
                  use CoList.cons (Y_deg, Y_coef) Y_tl
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
                  · apply add_isApproximation
                    · exact h_left_coef_approx
                    · rw [← h_right_eq.1.2]
                      apply mul_isApproximation (MS.wellOrderedBasis_tail h_basis) hX_coef_approx hY_coef_approx
                  constructor
                  · apply majorated_of_EventuallyEq hf_eq
                    rw [← sup_idem deg']
                    apply add_majorated
                    · exact h_left_comp
                    · rw [← h_right_eq.1.1]
                      apply mul_majorated hX_comp hY_comp
                      apply MS.basis_head_eventually_pos h_basis
                    · apply MS.basis_head_eventually_pos h_basis
                  rw [← h_left_tl_eq', ← h_right_eq.2, ← add_assoc']
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
                  use CoList.cons (Y_deg, Y_coef) Y_tl
                  use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
                  use fY
                  constructor
                  · congr 1
                    conv => rhs; unfold longAdd
                    simp only [Function.comp_apply, Fin.lastCases_castSucc, Fin.natCast_eq_last]
                    congr 1
                    · simp
                      congr 1
                      ext i
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
                        simp at h2
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
                    · ext i
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
                      apply longAdd_mulMonomial_tail_B_isApproximation
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
end

end PreMS

end TendstoTactic
