import Mathlib.Tactic.Tendsto.Multiseries.BasicNew
import Mathlib.Tactic.Tendsto.Multiseries.Basis

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

namespace PreMS

def mulConst {basis : Basis} (ms : PreMS basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => ms * c
  | _ :: _ =>
    CoList.map (fun (deg, coef) => (deg, mulConst coef c)) ms

def neg {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  ms.mulConst (-1)

noncomputable def add {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  match basis with
  | [] => a + b
  | basid_hd :: basis_tl =>
    let T := (PreMS (basid_hd :: basis_tl)) × (PreMS (basid_hd :: basis_tl))
    let g : T → CoList.OutType (ℝ × PreMS basis_tl) T := fun (x, y) =>
      x.casesOn'
        (nil := y.casesOn' -- just y
          (nil := .nil)
          (cons := fun (y_deg, y_coef) y_tl =>
            .cons (y_deg, y_coef) (.nil, y_tl)
          )
        )
        (cons := fun (x_deg, x_coef) x_tl =>
          y.casesOn'
          (nil := .cons (x_deg, x_coef) (x_tl, .nil)) -- just x
          (cons := fun (y_deg, y_coef) y_tl =>
            if y_deg < x_deg then
              .cons (x_deg, x_coef) (x_tl, y)
            else if x_deg < y_deg then
              .cons (y_deg, y_coef) (x, y_tl)
            else
              .cons (x_deg, x_coef.add y_coef) (x_tl, y_tl)
          )
        )
    CoList.corec g (a, b)


-- def nextAt (n : ℕ) (li : CoList (CoList ℕ)) : CoList (CoList ℕ) :=
--   match n with
--   | 0 => CoList.cons li.head.get!.tail li.tail
--   | m + 1 => CoList.cons li.head.get! (nextAt m li.tail)

/-- Collect leading terms from the list of terms. -/
noncomputable def leadingTerms {basis : Basis} (terms : List (ℝ × PreMS basis)) (shift : ℕ := 0) :
    Option (ℝ × List (PreMS basis × ℕ)) :=
  match terms with
  | [] => .none
  | (hd_deg, hd_coef) :: tl =>
    let pre := leadingTerms tl (shift := shift + 1)
    match pre with
    | none => (hd_deg, [(hd_coef, shift)])
    | some (maxDeg, ans) =>
      if maxDeg < hd_deg then
        (hd_deg, [(hd_coef, shift)])
      else if maxDeg = hd_deg then
        (hd_deg, (hd_coef, shift) :: ans)
      else
        (maxDeg, ans)

-- TODO: rename?
/-- Given CoList of PreMS (which are also CoLists), merge them into single PreMS while maintaining
the correct order. At the step `n` it considers only first `n` elements of `s`. -/
noncomputable def merge1 {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (s : CoList (PreMS (basis_hd :: basis_tl))) : PreMS (basis_hd :: basis_tl) :=
  let T := ℕ × CoList (PreMS (basis_hd :: basis_tl))
  let g : T → CoList.OutType (ℝ × PreMS basis_tl) T := fun (k, li) =>
    let heads : List (ℝ × PreMS basis_tl) :=
      let t := li.take k
      t.filterMap (·.head)
    -- for safe `List.head` below
    -- have heads_nonempty : ∀ shift deg terms, leadingTerms heads (shift := shift) = .some (deg, terms) → terms ≠ [] := by
    --   induction heads with
    --   | nil =>
    --     intro shift deg terms h
    --     simp [leadingTerms] at h
    --   | cons heads_hd heads_tl ih =>
    --     intro shift deg terms h
    --     simp [leadingTerms] at h
    --     specialize ih (shift + 1)
    --     generalize leadingTerms heads_tl (shift + 1) = s at *
    --     cases s with
    --     | none =>
    --       simp at h
    --       simp [← h.right]
    --     | some v =>
    --       obtain ⟨tl_deg, tl_terms⟩ := v
    --       simp at h
    --       split_ifs at h
    --       · simp at h
    --         simp [← h.right]
    --       · simp at h
    --         simp [← h.right]
    --       · simp at h
    --         apply ih
    --         rw [h.right]
    match leadingTerms heads with
    | .none => .nil
    | .some (deg, terms) =>
      let coef := terms.tail.foldl (init := (terms.head!).1) fun acc (curCoef, _) =>
        add acc curCoef
      let next : CoList (PreMS (basis_hd :: basis_tl)) := terms.foldl (init := li) fun acc (_, idx) =>
        acc.modify idx (·.tail)
      .cons (deg, coef) (k + 1, next)
  CoList.corec g (1, s)

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


-------------------- theorems

open Filter Asymptotics

theorem const_isApproximation_const {c : ℝ} {basis : Basis} (h_wo : MS.wellOrderedBasis basis) :
    (const c basis).isApproximation (fun _ ↦ c) basis := by
  cases basis with
  | nil => simp [isApproximation, const]
  | cons basis_hd basis_tl =>
    simp [const]
    have ih : (const c basis_tl).isApproximation (fun _ ↦ c) basis_tl := by
      simp [MS.wellOrderedBasis] at h_wo
      apply const_isApproximation_const h_wo.right.left
    apply isApproximation.cons _ ih
    · intro deg h_deg
      apply Asymptotics.isLittleO_const_left.mpr
      right
      apply Tendsto.comp tendsto_norm_atTop_atTop
      apply Tendsto.comp (tendsto_rpow_atTop h_deg)
      apply MS.basis_tendsto_top h_wo
      simp
    · apply isApproximation.nil
      simp
      rfl

theorem const_wellOrdered {c : ℝ} {basis : Basis} :
    (const c basis).wellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp [const]
    apply wellOrdered.cons
    · exact const_wellOrdered
    · apply wellOrdered.nil
    · simp

theorem one_isApproximation_one {basis : Basis} (h_wo : MS.wellOrderedBasis basis) :
    (one basis).isApproximation (fun _ ↦ 1) basis :=
  const_isApproximation_const h_wo

theorem mulConst_wellOrdered {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_wo : ms.wellOrdered) : (ms.mulConst c).wellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms' =>
      ∃ (X : PreMS (basis_hd :: basis_tl)), ms' = X.mulConst c ∧ X.wellOrdered
    apply wellOrdered_coind motive
    · intro ms ih
      simp [motive] at ih
      obtain ⟨X, h_ms_eq, hX_wo⟩ := ih
      subst h_ms_eq
      revert hX_wo
      apply X.casesOn
      · intro
        left
        simp [mulConst]
      · intro (deg, coef) tl hX_wo
        replace hX_wo := wellOrdered_cons hX_wo
        obtain ⟨hX_coef_wo, hX_tl_wo, hX_comp⟩ := hX_wo
        right
        use deg
        use coef.mulConst c
        use mulConst (basis := basis_hd :: basis_tl) tl c
        constructor
        · simp [mulConst]
        constructor
        · exact mulConst_wellOrdered hX_coef_wo
        constructor
        · intro tl_mul_deg tl_mul_coef tl_mul_tl
          revert hX_comp
          apply tl.casesOn
          · intro hX_comp h_tl_eq
            simp [mulConst] at h_tl_eq
          · intro (tl_deg, tl_coef) tl_tl hX_comp h_tl_eq
            simp [mulConst] at h_tl_eq
            specialize hX_comp tl_deg tl_coef tl_tl (by rfl)
            rwa [← h_tl_eq.left.left]
        simp [motive]
        use tl
    · simp [motive]
      use ms

theorem mulConst_isApproximation {basis : Basis} {ms : PreMS basis} {c : ℝ} {F : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) :
    (ms.mulConst c).isApproximation (fun x ↦ F x * c) basis := by
  cases basis with
  | nil =>
    simp [isApproximation, mulConst] at *
    apply EventuallyEq.mul h_approx
    rfl
  | cons basis_hd basis_tl =>
    let motive : (ℝ → ℝ) → (PreMS (basis_hd :: basis_tl)) → Prop := fun f ms' =>
      ∃ (X : PreMS (basis_hd :: basis_tl)) (fX : ℝ → ℝ),
        ms' = X.mulConst c ∧ f =ᶠ[atTop] (fun x ↦ fX x * c) ∧
        X.isApproximation fX (basis_hd :: basis_tl)
    apply isApproximation_coind motive
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨X, fX, h_ms_eq, hf_eq, hX_approx⟩ := ih
      revert h_ms_eq hX_approx
      apply X.casesOn
      · intro h_ms_eq hX_approx
        left
        replace hX_approx := isApproximation_nil hX_approx
        simp [mulConst] at h_ms_eq
        constructor
        · exact h_ms_eq
        trans
        · exact hf_eq
        conv =>
          rhs
          ext x
          simp
          rw [← zero_mul c]
        apply EventuallyEq.mul hX_approx
        rfl
      · intro (X_deg, X_coef) X_tl h_ms_eq hX_approx
        replace hX_approx := isApproximation_cons hX_approx
        obtain ⟨XC, hX_coef, hX_comp, hX_tl⟩ := hX_approx
        right
        simp [mulConst] at h_ms_eq
        use ?_
        use ?_
        use ?_
        use fun x ↦ XC x * c
        constructor
        · exact h_ms_eq
        constructor
        · exact mulConst_isApproximation hX_coef
        constructor
        · intro deg h_deg
          apply Filter.EventuallyEq.trans_isLittleO hf_eq
          simp_rw [mul_comm]
          apply IsLittleO.const_mul_left (hX_comp deg h_deg)
        simp only [motive]
        use X_tl
        use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
        constructor
        · rfl
        constructor
        · apply eventuallyEq_iff_sub.mpr
          eta_expand
          simp
          ring_nf!
          apply eventuallyEq_iff_sub.mp
          conv => rhs; ext; rw [mul_comm]
          exact hf_eq
        · exact hX_tl
    · simp only [motive]
      use ms
      use F

theorem neg_wellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.wellOrdered) : ms.neg.wellOrdered :=
  mulConst_wellOrdered h_wo

theorem neg_isApproximation {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_approx : ms.isApproximation F basis) : ms.neg.isApproximation (-F) basis := by
  rw [← mul_neg_one]
  eta_expand
  simp only [Pi.one_apply, Pi.neg_apply, Pi.mul_apply]
  apply mulConst_isApproximation h_approx

noncomputable def add_out {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (x y : PreMS (basis_hd :: basis_tl)) :
    CoList.OutType (ℝ × PreMS basis_tl) (PreMS (basis_hd :: basis_tl)) :=
  x.casesOn'
      (nil := y.casesOn' -- just y
        (nil := .nil)
        (cons := fun (y_deg, y_coef) y_tl =>
          .cons (y_deg, y_coef) (add (basis := basis_hd :: basis_tl) .nil y_tl)
        )
      )
      (cons := fun (x_deg, x_coef) x_tl =>
        y.casesOn'
        (nil := .cons (x_deg, x_coef) (add (basis := basis_hd :: basis_tl) x_tl .nil)) -- just x
        (cons := fun (y_deg, y_coef) y_tl =>
          if y_deg < x_deg then
            .cons (x_deg, x_coef) (add x_tl y)
          else if x_deg < y_deg then
            .cons (y_deg, y_coef) (add x y_tl)
          else
            .cons (x_deg, x_coef.add y_coef) (add (basis := basis_hd :: basis_tl) x_tl y_tl)
        )
      )

theorem add_out_eq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : PreMS (basis_hd :: basis_tl)} :
    (x.add y).out = add_out x y
    := by
  unfold add_out
  conv => lhs; unfold add
  rw [CoList.corec_out]
  simp [Functor.map]
  apply x.casesOn
  · apply y.casesOn
    · simp only [CoList.casesOn_nil]
    · intro (y_deg, y_coef) y_tl
      simp only [CoList.casesOn_cons, CoList.casesOn_nil, add, Prod.mk.eta]
  · apply y.casesOn
    · intros; simp only [CoList.casesOn_nil, CoList.casesOn_cons, add, Prod.mk.eta]
    · intros
      simp only [CoList.casesOn_cons]
      split_ifs <;> simp only [add, Prod.mk.eta]

-- do we need it?
theorem add_eq_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
    (h : X.add Y = .nil) : X = .nil ∧ Y = .nil := by
  have := add_out_eq (x := X) (y := Y)
  unfold add_out at this
  rw [h] at this
  simp at this
  revert this
  apply X.casesOn
  · apply Y.casesOn
    · simp
    · intro hd tl this
      simp at this
  · apply Y.casesOn
    · intro hd tl this
      simp at this
    · intro _ _ _ _ this
      simp at this
      split_ifs at this

@[simp]
theorem nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    add CoList.nil ms = ms := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
    x = add CoList.nil y
  apply CoList.Eq.coind motive
  · intro x y ih
    simp [motive] at ih
    subst ih
    apply y.casesOn
    · right
      simp [add]
    · intro (deg, coef) tl
      left
      have h_out : CoList.out (add (basis := basis_hd :: basis_tl) CoList.nil
        (CoList.cons (deg, coef) tl)) = ?_ := by exact add_out_eq
      simp [add_out] at h_out
      use ?_
      use ?_
      use (deg, coef)
      use tl
      constructor
      · have := CoList.out_eq_cons h_out
        exact this
      constructor
      · rfl
      constructor
      · rfl
      simp only [motive]
  · simp only [motive]

@[simp]
theorem zero_add' {basis : Basis} {ms : PreMS basis} :
    add (zero _) ms = ms := by
  cases basis with
  | nil => simp [add, zero]
  | cons => simp [zero]

-- copypaste from above
@[simp]
theorem add_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    add ms CoList.nil = ms := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
    x = add y CoList.nil
  apply CoList.Eq.coind motive
  · intro x y ih
    simp [motive] at ih
    subst ih
    apply y.casesOn
    · right
      simp [add]
    · intro (deg, coef) tl
      left
      have h_out : CoList.out (add (basis := basis_hd :: basis_tl)
        (CoList.cons (deg, coef) tl) CoList.nil) = ?_ := by exact add_out_eq
      simp [add_out] at h_out
      use ?_
      use ?_
      use (deg, coef)
      use tl
      constructor
      · have := CoList.out_eq_cons h_out
        exact this
      constructor
      · rfl
      constructor
      · rfl
      simp only [motive]
  · simp only [motive]

@[simp]
theorem add_zero' {basis : Basis} {ms : PreMS basis} :
    add ms (zero _) = ms := by
  cases basis with
  | nil => simp [add, zero]
  | cons => simp [zero]

theorem cons_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_deg : ℝ} {X_coef : PreMS basis_tl}
    {X_tl Y : PreMS (basis_hd :: basis_tl)} (h_lt : Y.leadingExp < X_deg) :
    add (CoList.cons (X_deg, X_coef) X_tl) Y = CoList.cons (X_deg, X_coef) (X_tl.add Y) := by
  have h_out : CoList.out (add (basis := basis_hd :: basis_tl) (CoList.cons (X_deg, X_coef) X_tl) Y) =
    ?_ := by exact add_out_eq
  simp [add_out] at h_out
  revert h_lt h_out
  apply Y.casesOn
  · simp
  · intro (Y_deg, Y_coef) Y_tl h_lt h_out
    simp [leadingExp] at h_lt
    simp at h_out
    split_ifs at h_out with h1
    · replace h_out := CoList.out_eq_cons h_out
      exact h_out
    · simp [h_lt] at h1

theorem add_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_deg : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl X : PreMS (basis_hd :: basis_tl)} (h_lt : X.leadingExp < Y_deg) :
    add X (CoList.cons (Y_deg, Y_coef) Y_tl) = CoList.cons (Y_deg, Y_coef) (X.add Y_tl) := by
  have h_out : CoList.out (add (basis := basis_hd :: basis_tl) X (CoList.cons (Y_deg, Y_coef) Y_tl)) =
    ?_ := by exact add_out_eq
  simp [add_out] at h_out
  revert h_lt h_out
  apply X.casesOn
  · simp
  · intro (X_deg, X_coef) X_tl h_lt h_out
    simp [leadingExp] at h_lt
    simp at h_out
    split_ifs at h_out with h1
    · exfalso -- why do I need it?
      linarith
    · replace h_out := CoList.out_eq_cons h_out
      exact h_out

theorem cons_add' {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_tl Y : PreMS (basis_hd :: basis_tl)}
    {X_deg : ℝ} {X_coef : PreMS basis_tl}
    (h_lt : Y.allLt X_deg)
    : add (CoList.cons (X_deg, X_coef) X_tl) Y =
    CoList.cons (X_deg, X_coef) (X_tl.add Y) := by
  apply cons_add
  revert h_lt
  apply Y.casesOn
  · intro h_lt
    simp [leadingExp]
  · intro (Y_deg, Y_coef) Y_tl h_lt
    simp [allLt] at h_lt
    simp [leadingExp, h_lt.left]

-- TODO: prove add_cons'


theorem add_assoc {basis : Basis} {X Y Z : PreMS basis}
    (hX_wo : X.wellOrdered) (hY_wo : Y.wellOrdered) (hZ_wo : Z.wellOrdered) :
    (X.add Y).add Z = X.add (Y.add Z) := by
  cases basis with
  | nil => simp [add]; ring
  | cons basis_hd basis_tl =>
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
    ∃ (X Y Z : PreMS (basis_hd :: basis_tl)), a = (X.add Y).add Z ∧ b = X.add (Y.add Z) ∧
    X.wellOrdered ∧ Y.wellOrdered ∧ Z.wellOrdered
  apply CoList.Eq.coind motive
  · intro a b ih
    simp only [motive] at ih
    obtain ⟨X, Y, Z, ha_eq, hb_eq, hX_wo, hY_wo, hZ_wo⟩ := ih
    revert ha_eq hb_eq hX_wo
    apply X.casesOn
    · intro ha_eq hb_eq _
      revert ha_eq hb_eq hY_wo
      apply Y.casesOn
      · intro _ ha_eq hb_eq
        revert ha_eq hb_eq hZ_wo
        apply Z.casesOn
        · intro _ ha_eq hb_eq
          right
          simp at ha_eq hb_eq
          constructor <;> assumption
        · intro (Z_deg, Z_coef) Z_tl hZ_wo ha_eq hb_eq
          left
          simp at ha_eq hb_eq
          use ?_
          use ?_
          use ?_
          use ?_
          constructor
          · exact ha_eq
          constructor
          · exact hb_eq
          constructor
          · rfl
          simp only [motive]
          use .nil
          use .nil
          use Z_tl
          simp
          constructor
          · exact wellOrdered.nil
          replace hZ_wo := wellOrdered_cons hZ_wo
          exact hZ_wo.right.left
      · intro (Y_deg, Y_coef) Y_tl hY_wo ha_eq hb_eq
        revert ha_eq hb_eq hZ_wo
        apply Z.casesOn
        · intro _ ha_eq hb_eq
          simp at ha_eq hb_eq
          left
          use ?_
          use ?_
          use ?_
          use ?_
          constructor
          · exact ha_eq
          constructor
          · exact hb_eq
          constructor
          · rfl
          simp only [motive]
          use .nil
          use .nil
          use Y_tl
          simp
          constructor
          · exact wellOrdered.nil
          replace hY_wo := wellOrdered_cons hY_wo
          exact hY_wo.right.left
        · intro (Z_deg, Z_coef) Z_tl hZ_wo ha_eq hb_eq
          left
          simp at ha_eq hb_eq
          have hab : a = b := by rw [ha_eq, hb_eq]
          subst hab
          clear hb_eq
          have h_out : CoList.out a =
            ?_ := by rw [ha_eq]; exact add_out_eq
          simp [add_out] at h_out
          split_ifs at h_out with h1 h2
          · replace h_out := CoList.out_eq_cons h_out
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use Y_tl
            use CoList.cons (Z_deg, Z_coef) Z_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · replace hY_wo := wellOrdered_cons hY_wo
              exact hY_wo.right.left
            constructor
            · exact hZ_wo
            · exact wellOrdered.nil
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use CoList.cons (Y_deg, Y_coef) Y_tl
            use Z_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · exact hY_wo
            constructor
            · replace hZ_wo := wellOrdered_cons hZ_wo
              exact hZ_wo.right.left
            · exact wellOrdered.nil
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use Y_tl
            use Z_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · replace hY_wo := wellOrdered_cons hY_wo
              exact hY_wo.right.left
            constructor
            · replace hZ_wo := wellOrdered_cons hZ_wo
              exact hZ_wo.right.left
            · exact wellOrdered.nil
    · intro (X_deg, X_coef) X_tl ha_eq hb_eq hX_wo
      left
      obtain ⟨hX_coef_wo, hX_tl_wo, hX_comp⟩ := wellOrdered_cons hX_wo
      revert ha_eq hb_eq hY_wo
      apply Y.casesOn
      · intro _ ha_eq hb_eq
        simp at ha_eq hb_eq
        have hab : a = b := by rw [ha_eq, hb_eq]
        subst hab
        clear hb_eq
        revert ha_eq hZ_wo
        apply Z.casesOn
        · intro _ ha_eq
          simp at ha_eq
          use ?_
          use ?_
          use ?_
          use ?_
          constructor
          · exact ha_eq
          constructor
          · exact ha_eq
          constructor
          · rfl
          simp only [motive]
          use X_tl
          use .nil
          use .nil
          simp
          constructor
          · exact hX_tl_wo
          · exact wellOrdered.nil
        · intro (Z_deg, Z_coef) Z_tl hZ_wo ha_eq
          obtain ⟨hZ_coef_wo, hZ_tl_wo, hZ_comp⟩ := wellOrdered_cons hZ_wo
          have h_out : CoList.out a =
            ?_ := by rw [ha_eq]; exact add_out_eq
          simp [add_out] at h_out
          split_ifs at h_out
          · replace h_out := CoList.out_eq_cons h_out
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use X_tl
            use CoList.cons (Z_deg, Z_coef) Z_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · exact hX_tl_wo
            constructor
            · exact hZ_wo
            · exact wellOrdered.nil
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use CoList.cons (X_deg, X_coef) X_tl
            use Z_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · exact hX_wo
            constructor
            · exact hZ_tl_wo
            · exact wellOrdered.nil
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use X_tl
            use Z_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · exact hX_tl_wo
            constructor
            · exact hZ_tl_wo
            · exact wellOrdered.nil
      · intro (Y_deg, Y_coef) Y_tl hY_wo ha_eq hb_eq
        obtain ⟨hY_coef_wo, hY_tl_wo, hY_comp⟩ := wellOrdered_cons hY_wo
        revert ha_eq hb_eq hZ_wo
        apply Z.casesOn
        · intro _ ha_eq hb_eq
          simp at ha_eq hb_eq
          have hab : a = b := by rw [ha_eq, hb_eq]
          subst hab
          clear hb_eq
          have h_out : CoList.out a =
            ?_ := by rw [ha_eq]; exact add_out_eq
          simp [add_out] at h_out
          split_ifs at h_out
          · replace h_out := CoList.out_eq_cons h_out
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use X_tl
            use CoList.cons (Y_deg, Y_coef) Y_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · exact hX_tl_wo
            constructor
            · exact hY_wo
            · exact wellOrdered.nil
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use CoList.cons (X_deg, X_coef) X_tl
            use Y_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · exact hX_wo
            constructor
            · exact hY_tl_wo
            · exact wellOrdered.nil
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            constructor
            · rfl
            simp only [motive]
            use X_tl
            use Y_tl
            use .nil
            constructor
            · simp
            constructor
            · simp
            constructor
            · exact hX_tl_wo
            constructor
            · exact hY_tl_wo
            · exact wellOrdered.nil
        · intro (Z_deg, Z_coef) Z_tl hZ_wo ha_eq hb_eq -- main case
          obtain ⟨hZ_coef_wo, hZ_tl_wo, hZ_comp⟩ := wellOrdered_cons hZ_wo
          have h_XY_out : CoList.out (add (basis := basis_hd :: basis_tl) (CoList.cons (X_deg, X_coef) X_tl) (CoList.cons (Y_deg, Y_coef) Y_tl)) = ?_ := by
            exact add_out_eq
          have h_YZ_out : CoList.out (add (basis := basis_hd :: basis_tl) (CoList.cons (Y_deg, Y_coef) Y_tl) (CoList.cons (Z_deg, Z_coef) Z_tl)) = ?_ := by
            exact add_out_eq
          simp [add_out] at h_XY_out h_YZ_out
          split_ifs at h_XY_out h_YZ_out <;> (
            replace h_XY_out := CoList.out_eq_cons h_XY_out
            replace h_YZ_out := CoList.out_eq_cons h_YZ_out
            rw [h_XY_out] at ha_eq
            rw [h_YZ_out] at hb_eq
            have ha_out : CoList.out a =
              ?_ := by rw [ha_eq]; exact add_out_eq
            have hb_out : CoList.out b =
              ?_ := by rw [hb_eq]; exact add_out_eq
            simp [add_out] at ha_out hb_out
            split_ifs at ha_out hb_out <;> (try linarith) <;> (
              replace ha_out := CoList.out_eq_cons ha_out
              replace hb_out := CoList.out_eq_cons hb_out
              use ?_
              use ?_
              use ?_
              use ?_
              constructor
              · exact ha_out
              constructor
              · exact hb_out
              constructor
              · first | rfl | (congr 1; exact add_assoc hX_coef_wo hY_coef_wo hZ_coef_wo)
              simp only [motive]
              use ?_
              use ?_
              use ?_
              constructor
              · try rw [← h_XY_out]
                try rw [← h_YZ_out]
                try (congr <;> (exact Eq.refl _))
              constructor
              · try rw [← h_XY_out]
                try rw [← h_YZ_out]
                try congr
              constructor
              · assumption
              constructor
              · assumption
              · assumption
            )
          )
  · simp only [motive]
    use X
    use Y
    use Z

theorem add_wellOrdered {basis : Basis} {x y : PreMS basis}
    (h_x_wo : x.wellOrdered) (h_y_wo : y.wellOrdered) : (x.add y).wellOrdered := by
  cases basis with
  | nil =>
    constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)),
        ms = X.add Y ∧ X.wellOrdered ∧ Y.wellOrdered
    apply wellOrdered_coind motive
    · intro ms ih
      simp only [motive] at ih
      obtain ⟨X, Y, h_ms_eq, hX_wo, hY_wo⟩ := ih
      revert h_ms_eq hX_wo
      apply X.casesOn
      · intro h_ms_eq hX_wo
        revert h_ms_eq hY_wo
        apply Y.casesOn
        · intro hY_wo h_ms_eq
          left
          simpa using h_ms_eq
        · intro (Y_deg, Y_coef) Y_tl hY_wo h_ms_eq
          replace hY_wo := wellOrdered_cons hY_wo
          obtain ⟨hY_coef_wo, hY_tl_wo, hY_comp⟩ := hY_wo
          right
          simp at h_ms_eq
          use Y_deg
          use Y_coef
          use Y_tl
          constructor
          · exact h_ms_eq
          constructor
          · exact hY_coef_wo
          constructor
          · exact hY_comp
          simp only [motive]
          use .nil
          use Y_tl
          simp only [nil_add, true_and]
          constructor
          · apply wellOrdered.nil
          · exact hY_tl_wo
      · intro (X_deg, X_coef) X_tl h_ms_eq hX_wo
        have hX_wo' := wellOrdered_cons hX_wo
        obtain ⟨hX_coef_wo, hX_tl_wo, hX_comp⟩ := hX_wo'
        right
        revert h_ms_eq hY_wo
        apply Y.casesOn
        · intro hY_wo h_ms_eq
          simp at h_ms_eq
          use X_deg
          use X_coef
          use X_tl
          constructor
          · exact h_ms_eq
          constructor
          · exact hX_coef_wo
          constructor
          · exact hX_comp
          simp only [motive]
          use .nil
          use X_tl
          simp only [nil_add, true_and]
          constructor
          · apply wellOrdered.nil
          · exact hX_tl_wo
        · intro (Y_deg, Y_coef) Y_tl hY_wo h_ms_eq
          have hY_wo' := wellOrdered_cons hY_wo
          obtain ⟨hY_coef_wo, hY_tl_wo, hY_comp⟩ := hY_wo'
          have h_out : ms.out = ?_ := by simp only [h_ms_eq]; exact add_out_eq
          simp [add_out] at h_out
          split_ifs at h_out with h1 h2
          · replace h_ms_eq := CoList.out_eq_cons h_out
            clear h_out
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_ms_eq
            constructor
            · exact hX_coef_wo
            constructor
            · intro tl_deg tl_coef tl_tl h_eq
              revert h_eq hX_comp
              apply X_tl.casesOn
              · intro _ h_eq
                simp at h_eq
                rwa [← h_eq.left.left]
              · intro (X_tl_deg, X_tl_coef) X_tl_tl hX_comp h_eq
                have h_out : (add (basis := basis_hd :: basis_tl)
                  (CoList.cons (X_tl_deg, X_tl_coef) X_tl_tl)
                  (CoList.cons (Y_deg, Y_coef) Y_tl)).out = ?_ := by exact add_out_eq
                simp [add_out] at h_out
                split_ifs at h_out with h1 h2
                · have h_eq' := CoList.out_eq_cons h_out
                  clear h_out
                  rw [h_eq'] at h_eq
                  simp at h_eq
                  rw [← h_eq.left.left]
                  exact hX_comp _ _ _ (by rfl)
                · have h_eq' := CoList.out_eq_cons h_out
                  clear h_out
                  rw [h_eq'] at h_eq
                  simp at h_eq
                  rwa [← h_eq.left.left]
                · have h_eq' := CoList.out_eq_cons h_out
                  clear h_out
                  rw [h_eq'] at h_eq
                  simp at h_eq
                  rw [← h_eq.left.left]
                  exact hX_comp _ _ _ (by rfl)
            simp only [motive]
            use X_tl
            use .cons (Y_deg, Y_coef) Y_tl
          · replace h_ms_eq := CoList.out_eq_cons h_out
            clear h_out
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_ms_eq
            constructor
            · exact hY_coef_wo
            constructor
            · intro tl_deg tl_coef tl_tl h_eq
              revert h_eq hY_comp
              apply Y_tl.casesOn
              · intro _ h_eq
                simp at h_eq
                rwa [← h_eq.left.left]
              · intro (Y_tl_deg, Y_tl_coef) Y_tl_tl hY_comp h_eq
                have h_out : (add (basis := basis_hd :: basis_tl)
                  (CoList.cons (X_deg, X_coef) X_tl)
                  (CoList.cons (Y_tl_deg, Y_tl_coef) Y_tl_tl)).out = ?_ := by exact add_out_eq
                simp [add_out] at h_out
                split_ifs at h_out with h1 h2
                · have h_eq' := CoList.out_eq_cons h_out
                  clear h_out
                  rw [h_eq'] at h_eq
                  simp at h_eq
                  rw [← h_eq.left.left]
                  linarith
                · have h_eq' := CoList.out_eq_cons h_out
                  clear h_out
                  rw [h_eq'] at h_eq
                  simp at h_eq
                  rw [← h_eq.left.left]
                  exact hY_comp _ _ _ (by rfl)
                · have h_eq' := CoList.out_eq_cons h_out
                  clear h_out
                  rw [h_eq'] at h_eq
                  simp at h_eq
                  rw [← h_eq.left.left]
                  linarith
            simp only [motive]
            use .cons (X_deg, X_coef) X_tl
            use Y_tl
          · replace h_ms_eq := CoList.out_eq_cons h_out
            clear h_out
            have h_deg : X_deg = Y_deg := by linarith
            subst h_deg
            clear h1 h2
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_ms_eq
            constructor
            · exact add_wellOrdered hX_coef_wo hY_coef_wo
            constructor
            · intro tl_deg tl_coef tl_tl h_eq
              revert h_eq hX_comp
              apply X_tl.casesOn
              · intro _ h_eq
                revert hY_comp h_eq
                apply Y_tl.casesOn
                · intro _ h_eq
                  simp at h_eq
                · intro (Y_tl_deg, Y_tl_coef) Y_tl_tl hY_comp h_eq
                  simp at h_eq
                  rw [← h_eq.left.left]
                  exact hY_comp _ _ _ (by rfl)
              · intro (X_tl_deg, X_tl_coef) X_tl_tl hX_comp h_eq
                revert hY_comp h_eq
                apply Y_tl.casesOn
                · intro _ h_eq
                  simp at h_eq
                  rw [← h_eq.left.left]
                  exact hX_comp _ _ _ (by rfl)
                · intro (Y_tl_deg, Y_tl_coef) Y_tl_tl hY_comp h_eq
                  have h_out : (add (basis := basis_hd :: basis_tl)
                    (CoList.cons (X_tl_deg, X_tl_coef) X_tl_tl)
                    (CoList.cons (Y_tl_deg, Y_tl_coef) Y_tl_tl)).out = ?_ := by exact add_out_eq
                  simp [add_out] at h_out
                  split_ifs at h_out with h1 h2
                  · have h_eq' := CoList.out_eq_cons h_out
                    clear h_out
                    rw [h_eq'] at h_eq
                    simp at h_eq
                    rw [← h_eq.left.left]
                    exact hX_comp _ _ _ (by rfl)
                  · have h_eq' := CoList.out_eq_cons h_out
                    clear h_out
                    rw [h_eq'] at h_eq
                    simp at h_eq
                    rw [← h_eq.left.left]
                    exact hY_comp _ _ _ (by rfl)
                  · have h_eq' := CoList.out_eq_cons h_out
                    clear h_out
                    rw [h_eq'] at h_eq
                    simp at h_eq
                    rw [← h_eq.left.left]
                    exact hX_comp _ _ _ (by rfl)
            simp only [motive]
            use X_tl
            use Y_tl
    · simp only [motive]
      use x
      use y

theorem add_isApproximation {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
    (hX_approx : X.isApproximation fX basis) (hY_approx : Y.isApproximation fY basis) :
    (X.add Y).isApproximation (fX + fY) basis := by
  cases basis with
  | nil =>
    simp [isApproximation, add] at *
    exact EventuallyEq.add hX_approx hY_approx
  | cons basis_hd basis_tl =>
    let motive : (ℝ → ℝ) → (PreMS (basis_hd :: basis_tl)) → Prop := fun f ms =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)) (fX fY : ℝ → ℝ),
        ms = X.add Y ∧ f =ᶠ[atTop] fX + fY ∧ X.isApproximation fX ∧ Y.isApproximation fY
    apply isApproximation_coind motive
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨X, Y, fX, fY, h_ms_eq, hf_eq, hX_approx, hY_approx⟩ := ih
      revert h_ms_eq hX_approx
      apply X.casesOn
      · intro h_ms_eq hX_approx
        replace hX_approx := isApproximation_nil hX_approx
        revert h_ms_eq hY_approx
        apply Y.casesOn
        · intro hY_approx h_ms_eq
          replace hY_approx := isApproximation_nil hY_approx
          left
          simp at h_ms_eq
          constructor
          · exact h_ms_eq
          trans
          · exact hf_eq
          conv => rhs; ext x; simp; rw [← add_zero 0]
          apply EventuallyEq.add
          exacts [hX_approx, hY_approx]
        · intro (Y_deg, Y_coef) Y_tl hY_approx h_ms_eq
          have hY_approx' := isApproximation_cons hY_approx
          obtain ⟨YC, hY_coef, hY_comp, hY_tl⟩ := hY_approx'
          right
          simp at h_ms_eq
          replace hf_eq : f =ᶠ[atTop] fY := by
            trans
            · exact hf_eq
            conv => rhs; ext x; rw [← zero_add (fY x)]
            apply EventuallyEq.add hX_approx
            rfl
          use ?_
          use ?_
          use ?_
          use YC
          constructor
          · exact h_ms_eq
          constructor
          · exact hY_coef
          constructor
          · intro deg h_deg
            apply EventuallyEq.trans_isLittleO hf_eq
            apply hY_comp _ h_deg
          simp only [motive]
          use .nil
          use Y_tl
          use 0
          use fun x ↦ fY x - basis_hd x ^ Y_deg * YC x
          constructor
          · simp
          constructor
          · apply eventuallyEq_iff_sub.mpr
            eta_expand
            simp
            ring_nf!
            apply eventuallyEq_iff_sub.mp hf_eq
          constructor
          · apply isApproximation.nil
            rfl
          · exact hY_tl
      · intro (X_deg, X_coef) X_tl h_ms_eq hX_approx
        have hX_approx' := isApproximation_cons hX_approx
        obtain ⟨XC, hX_coef, hX_comp, hX_tl⟩ := hX_approx'
        right
        revert h_ms_eq hY_approx
        apply Y.casesOn
        · intro hY_approx h_ms_eq
          replace hY_approx := isApproximation_nil hY_approx
          simp at h_ms_eq
          replace hf_eq : f =ᶠ[atTop] fX := by
            trans
            · exact hf_eq
            conv => rhs; ext x; rw [← add_zero (fX x)]
            apply EventuallyEq.add _ hY_approx
            rfl
          use ?_
          use ?_
          use ?_
          use XC
          constructor
          · exact h_ms_eq
          constructor
          · exact hX_coef
          constructor
          · intro deg h_deg
            apply EventuallyEq.trans_isLittleO hf_eq
            apply hX_comp _ h_deg
          simp only [motive]
          use .nil
          use X_tl
          use 0
          use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
          constructor
          · simp
          constructor
          · apply eventuallyEq_iff_sub.mpr
            eta_expand
            simp
            ring_nf!
            apply eventuallyEq_iff_sub.mp hf_eq
          constructor
          · apply isApproximation.nil
            rfl
          · exact hX_tl
        · intro (Y_deg, Y_coef) Y_tl hY_approx h_ms_eq
          have hY_approx' := isApproximation_cons hY_approx
          obtain ⟨YC, hY_coef, hY_comp, hY_tl⟩ := hY_approx'
          have h_out : ms.out = ?_ := by simp only [h_ms_eq]; exact add_out_eq
          simp [add_out] at h_out
          split_ifs at h_out with h1 h2
          · replace h_ms_eq := CoList.out_eq_cons h_out
            clear h_out
            simp at h_ms_eq
            use X_deg
            use X_coef
            use ?_
            use XC
            constructor
            · exact h_ms_eq
            constructor
            · exact hX_coef
            constructor
            · intro deg h_deg
              apply EventuallyEq.trans_isLittleO hf_eq
              apply IsLittleO.add
              · exact hX_comp _ h_deg
              · apply hY_comp
                linarith
            simp only [motive]
            use X_tl
            use CoList.cons (Y_deg, Y_coef) Y_tl
            use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
            use fY
            constructor
            · rfl
            constructor
            · apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs
                ext x
                rw [show f x + (-fX x - fY x) = f x - (fX x + fY x) by ring]
              apply eventuallyEq_iff_sub.mp hf_eq
            constructor
            · exact hX_tl
            · exact hY_approx
          · replace h_ms_eq := CoList.out_eq_cons h_out
            clear h_out
            simp at h_ms_eq
            use Y_deg
            use Y_coef
            use ?_
            use YC
            constructor
            · exact h_ms_eq
            constructor
            · exact hY_coef
            constructor
            · intro deg h_deg
              apply EventuallyEq.trans_isLittleO hf_eq
              apply IsLittleO.add
              · apply hX_comp
                linarith
              · exact hY_comp _ h_deg
            simp only [motive]
            use CoList.cons (X_deg, X_coef) X_tl
            use Y_tl
            use fX
            use fun x ↦ fY x - basis_hd x ^ Y_deg * YC x
            constructor
            · rfl
            constructor
            · apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs
                ext x
                rw [show f x + (-fX x - fY x) = f x - (fX x + fY x) by ring]
              apply eventuallyEq_iff_sub.mp hf_eq
            constructor
            · exact hX_approx
            · exact hY_tl
          · have h : X_deg = Y_deg := by linarith
            subst h
            clear h1 h2
            replace h_ms_eq := CoList.out_eq_cons h_out
            clear h_out
            simp at h_ms_eq
            use X_deg
            use X_coef.add Y_coef
            use ?_
            use XC + YC
            constructor
            · exact h_ms_eq
            constructor
            · exact add_isApproximation hX_coef hY_coef
            constructor
            · intro deg h_deg
              apply EventuallyEq.trans_isLittleO hf_eq
              apply IsLittleO.add
              · exact hX_comp _ h_deg
              · exact hY_comp _ h_deg
            simp only [motive]
            use X_tl
            use Y_tl
            use fun x ↦ fX x - basis_hd x ^ X_deg * XC x
            use fun x ↦ fY x - basis_hd x ^ X_deg * YC x
            constructor
            · rfl
            constructor
            · apply eventuallyEq_iff_sub.mpr
              eta_expand
              simp
              ring_nf!
              conv =>
                lhs
                ext x
                rw [show f x + (-fX x - fY x) = f x - (fX x + fY x) by ring]
              apply eventuallyEq_iff_sub.mp hf_eq
            constructor
            · exact hX_tl
            · exact hY_tl
    · simp only [motive]
      use X
      use Y
      use fX
      use fY

theorem merge1_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    merge1 (basis_hd := basis_hd) (basis_tl := basis_tl) .nil = .nil := by
  simp [merge1]
  rw [CoList.corec_nil]
  simp [leadingTerms]

theorem megre1_cons_head_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons .nil s_tl) = .nil := by
  simp [merge1]
  rw [CoList.corec_nil]
  simp [leadingTerms]

theorem merge1_cons_head_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {deg : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)}
    {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons (.cons (deg, coef) tl) s_tl) = .cons (deg, coef) (tl.add (merge1 s_tl)) := by
  sorry

-- add here the assumption that `s.map head` is sorted
theorem merge1_cons_eq_add {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {s_hd : PreMS (basis_hd :: basis_tl)} {s_tl : CoList (PreMS (basis_hd :: basis_tl))} :
    merge1 (.cons s_hd s_tl) = add s_hd (merge1 s_tl) := by
  sorry

@[simp]
theorem nil_mul {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    mul CoList.nil ms = .nil := by
  simp [mul, merge1_nil]

@[simp]
theorem mul_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    mul ms CoList.nil = .nil := by
  simp [mul, mulMonomial]
  apply ms.casesOn
  · simp [merge1_nil]
  · intro (deg, coef) tl
    simp [merge1]
    rw [CoList.corec_nil]
    simp [leadingTerms]

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

@[simp]
theorem mul_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg y_deg : ℝ} {x_coef y_coef : PreMS basis_tl}
    {x_tl y_tl : PreMS (basis_hd :: basis_tl)} :
    mul (basis := basis_hd :: basis_tl) (CoList.cons (x_deg, x_coef) x_tl) (CoList.cons (y_deg, y_coef) y_tl) =
    CoList.cons (x_deg + y_deg, x_coef.mul y_coef) ((mulMonomial y_tl x_coef x_deg).add
      (x_tl.mul (CoList.cons (y_deg, y_coef) y_tl))) := by
  simp [mul, merge1_cons_head_cons]

@[simp]
theorem mul_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x_deg : ℝ} {x_coef : PreMS basis_tl}
    {x_tl y : PreMS (basis_hd :: basis_tl)} :
    mul (CoList.cons (x_deg, x_coef) x_tl) y = (mulMonomial y x_coef x_deg).add (x_tl.mul y) := by
  simp [mul, merge1_cons_eq_add]

@[simp]
theorem mul_one {basis : Basis} {ms : PreMS basis} : mul ms (one basis) = ms := by
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
        · simp only [one, const, mul_cons_cons, add_zero]
          congr <;> exact Eq.refl _
        constructor
        · congr <;> exact Eq.refl _
        constructor
        · congr
          exact mul_one
        simp only [motive]
        simp [mul, one, const]
    · simp only [motive]

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


theorem mul_assoc {basis : Basis} {X Y Z : PreMS basis} :
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
    -- simp [Finset.sup'] at h
    have := Finset.le_sup' (f := f) hb
    rw [h] at this
    exact le_bot_iff.mp this
  · intro h
    apply le_bot_iff.mp
    apply (Finset.sup'_le_iff H f).mpr
    intro b hb
    exact (h _ hb).le

-- theorem longAdd_zero {basis : Basis} {args : Fin 0 → PreMS basis} : longAdd args = zero _ := by
--   rfl

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
      have h_coefs_tls : ∀ i, (args i).leadingExp = deg → ∃ (v : PreMS basis_tl × (PreMS (basis_hd :: basis_tl))),
          args i = .cons (deg, v.1) v.2 := by
        intro i hi
        generalize args i = a at *
        revert hi
        apply a.casesOn
        · intro hi
          simp [leadingExp] at hi
        · intro (deg', coef') tl' hi
          simp [leadingExp] at hi
          subst hi
          use (coef', tl')
      let coef_tl_args : (Fin (k + 1)) → (PreMS basis_tl × PreMS (basis_hd :: basis_tl)) := fun i =>
        if h : (args i).leadingExp = deg then
          (h_coefs_tls i h).choose
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
              rw [add_cons]
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

mutual
  theorem mulMonomial_wellOrdered {basis_hd : _} {basis_tl : _} {b : PreMS (basis_hd :: basis_tl)}
        {m_coef : PreMS basis_tl} {m_deg : ℝ}
        (hb_wo : b.wellOrdered) (hm_wo : m_coef.wellOrdered) :
      (mulMonomial b m_coef m_deg).wellOrdered := by
    let motive : PreMS (basis_hd :: basis_tl) → Prop := fun x =>
      ∃ (b : PreMS (basis_hd :: basis_tl)), x = b.mulMonomial m_coef m_deg ∧
      b.wellOrdered
    apply wellOrdered_coind motive
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
        obtain ⟨h_coef_wo, h_tl_wo, h_comp⟩ := h_wo'
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
        · intro mtl_deg mtl_coef mtl_tl h
          revert h_comp h
          apply tl.casesOn
          · intro _ h
            simp at h
          · intro (tl_deg, tl_coef) tl_tl h_comp h
            simp at h
            rw [← h.left.left]
            specialize h_comp tl_deg tl_coef tl_tl (by rfl)
            linarith
        simp only [motive]
        use tl
    · simp only [motive]
      use b

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
      apply wellOrdered_coind motive
      ·
        intro ms ih
        simp only [motive] at ih
        obtain ⟨k, BM, X, Y, h_eq, h_BM, hX_wo, hY_wo⟩ := ih
        generalize h_left_eq : (longAdd ((fun x ↦ x.1.mulMonomial x.2.1 x.2.2) ∘ BM)) = left at h_eq
        generalize h_right_eq : X.mul Y = right at h_eq

        subst h_eq
        revert h_left_eq
        apply left.casesOn
        · intro h_left_eq
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
            obtain ⟨hX_coef_wo, hX_tl_wo, hX_comp⟩ := wellOrdered_cons hX_wo
            obtain ⟨hY_coef_wo, hY_tl_wo, hY_comp⟩ := wellOrdered_cons hY_wo
            simp only [mul_cons_cons, CoList.cons_eq_cons, Prod.mk.injEq] at h_right_eq

            obtain ⟨⟨h_deg, h_coef⟩, h_tl⟩ := h_right_eq
            subst h_deg h_coef h_tl
            constructor
            · apply mul_wellOrdered hX_coef_wo hY_coef_wo
            constructor
            · intro tl_deg tl_coef tl_tl
              sorry
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
        · sorry
      · simp only [motive]
        use 0
        use default
        use X
        use Y
        simp [longAdd, zero]
        constructor <;> assumption

end

theorem mul_isApproximation {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
    (hX_approx : X.isApproximation fX basis) (hY_approx : Y.isApproximation fY basis) :
    (X.mul Y).isApproximation (fX * fY) basis := by
  sorry

theorem mulMonomial_isApproximation {basis_hd : _} {basis_tl : _} {B M : ℝ → ℝ} (b : PreMS (basis_hd :: basis_tl))
      (m_coef : PreMS basis_tl) (m_deg : ℝ)
      (hb_approx : b.isApproximation B (basis_hd :: basis_tl))
      (hm_appxor : m_coef.isApproximation M basis_tl) :
    (mulMonomial b m_coef m_deg).isApproximation (fun x ↦ (M x) * (basis_hd x)^m_deg * (B x)) := by
  sorry

end PreMS

end TendstoTactic
