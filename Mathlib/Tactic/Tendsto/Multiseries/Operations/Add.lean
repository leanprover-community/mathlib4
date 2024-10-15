import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Basis
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Basic

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

namespace PreMS


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

-- theorems
open Filter Asymptotics


-- TODO : rewrite all API without `out`. Just `add_unfold`
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
      use (deg, coef)
      use ?_
      use tl
      constructor
      · have := CoList.out_eq_cons h_out
        exact this
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
      use (deg, coef)
      use ?_
      use tl
      constructor
      · have := CoList.out_eq_cons h_out
        exact this
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

noncomputable def add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (x y : PreMS (basis_hd :: basis_tl)) :
    (PreMS (basis_hd :: basis_tl)) :=
  x.casesOn'
  (nil := y)
  (cons := fun (x_deg, x_coef) x_tl =>
    y.casesOn'
    (nil := x)
    (cons := fun (y_deg, y_coef) y_tl =>
      if y_deg < x_deg then
        .cons (x_deg, x_coef) (add x_tl y)
      else if x_deg < y_deg then
        .cons (y_deg, y_coef) (add x y_tl)
      else
        .cons (x_deg, x_coef.add y_coef) (add (basis := basis_hd :: basis_tl) x_tl y_tl)
    )
  )

theorem add_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : PreMS (basis_hd :: basis_tl)} :
    add x y = add' x y := by
  have h_out : CoList.out (add (basis := basis_hd :: basis_tl) x y) = ?_ := by exact add_out_eq
  simp [add_out] at h_out
  revert h_out
  apply x.casesOn
  · apply y.casesOn
    · intro h_out
      simp [add']
    · intro (y_deg, y_coef) y_tl h_out
      simp [add']
  · intro (x_deg, x_coef) x_tl
    apply y.casesOn
    · intro h_out
      simp [add']
    · intro (y_deg, y_coef) y_tl
      simp [add']
      split_ifs <;> {
        intro h_out
        replace h_out := CoList.out_eq_cons h_out
        rw [h_out]
      }

-- TODO: remove `h_out` from all proofs below. Use `add_unfold` instead

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

theorem add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_deg : ℝ} {X_coef : PreMS basis_tl}
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
    · exfalso -- why do I need it?
      linarith

theorem add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_deg : ℝ} {Y_coef : PreMS basis_tl}
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

-- theorem cons_add' {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_tl Y : PreMS (basis_hd :: basis_tl)}
--     {X_deg : ℝ} {X_coef : PreMS basis_tl}
--     (h_lt : Y.allLt X_deg)
--     : add (CoList.cons (X_deg, X_coef) X_tl) Y =
--     CoList.cons (X_deg, X_coef) (X_tl.add Y) := by
--   apply cons_add
--   revert h_lt
--   apply Y.casesOn
--   · intro h_lt
--     simp [leadingExp]
--   · intro (Y_deg, Y_coef) Y_tl h_lt
--     simp [allLt] at h_lt
--     simp [leadingExp, h_lt.left]

-- TODO: prove add_cons'

theorem add_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_tl Y_tl: PreMS (basis_hd :: basis_tl)}
    {X_deg Y_deg : ℝ} {X_coef Y_coef : PreMS basis_tl}
    : add (basis := basis_hd :: basis_tl) (CoList.cons (X_deg, X_coef) X_tl) (CoList.cons (Y_deg, Y_coef) Y_tl) =
    if Y_deg < X_deg then
      CoList.cons (X_deg, X_coef) (add X_tl (CoList.cons (Y_deg, Y_coef) Y_tl))
    else if X_deg < Y_deg then
      CoList.cons (Y_deg, Y_coef) (add (CoList.cons (X_deg, X_coef) X_tl) Y_tl)
    else
      CoList.cons (X_deg, X_coef.add Y_coef) (add (basis := basis_hd :: basis_tl) X_tl Y_tl)
    := by
  rw [add_unfold, add']
  simp

theorem add_assoc' {basis : Basis} {X Y Z : PreMS basis} :
    (X.add Y).add Z = X.add (Y.add Z) := by
  cases basis with
  | nil => simp [add]; ring
  | cons basis_hd basis_tl =>
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
    ∃ (X Y Z : PreMS (basis_hd :: basis_tl)), a = (X.add Y).add Z ∧ b = X.add (Y.add Z)
  apply CoList.Eq.coind motive
  · intro a b ih
    simp only [motive] at ih
    obtain ⟨X, Y, Z, ha_eq, hb_eq⟩ := ih
    revert ha_eq hb_eq
    apply X.casesOn
    · intro ha_eq hb_eq
      revert ha_eq hb_eq
      apply Y.casesOn
      · intro ha_eq hb_eq
        revert ha_eq hb_eq
        apply Z.casesOn
        · intro ha_eq hb_eq
          right
          simp at ha_eq hb_eq
          constructor <;> assumption
        · intro (Z_deg, Z_coef) Z_tl ha_eq hb_eq
          left
          simp at ha_eq hb_eq
          use ?_
          use ?_
          use ?_
          constructor
          · exact ha_eq
          constructor
          · exact hb_eq
          simp only [motive]
          use .nil
          use .nil
          use Z_tl
          simp
      · intro (Y_deg, Y_coef) Y_tl ha_eq hb_eq
        revert ha_eq hb_eq
        apply Z.casesOn
        · intro ha_eq hb_eq
          simp at ha_eq hb_eq
          left
          use ?_
          use ?_
          use ?_
          constructor
          · exact ha_eq
          constructor
          · exact hb_eq
          simp only [motive]
          use .nil
          use .nil
          use Y_tl
          simp
        · intro (Z_deg, Z_coef) Z_tl ha_eq hb_eq
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
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use Y_tl
            use CoList.cons (Z_deg, Z_coef) Z_tl
            use .nil
            constructor
            · simp
            simp
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use CoList.cons (Y_deg, Y_coef) Y_tl
            use Z_tl
            use .nil
            constructor
            · simp
            simp
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use Y_tl
            use Z_tl
            use .nil
            constructor
            · simp
            simp
    · intro (X_deg, X_coef) X_tl ha_eq hb_eq
      left
      revert ha_eq hb_eq
      apply Y.casesOn
      · intro ha_eq hb_eq
        simp at ha_eq hb_eq
        have hab : a = b := by rw [ha_eq, hb_eq]
        subst hab
        clear hb_eq
        revert ha_eq
        apply Z.casesOn
        · intro ha_eq
          simp at ha_eq
          use ?_
          use ?_
          use ?_
          constructor
          · exact ha_eq
          constructor
          · exact ha_eq
          simp only [motive]
          use X_tl
          use .nil
          use .nil
          simp
        · intro (Z_deg, Z_coef) Z_tl ha_eq
          have h_out : CoList.out a =
            ?_ := by rw [ha_eq]; exact add_out_eq
          simp [add_out] at h_out
          split_ifs at h_out
          · replace h_out := CoList.out_eq_cons h_out
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use X_tl
            use CoList.cons (Z_deg, Z_coef) Z_tl
            use .nil
            constructor
            · simp
            simp
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use CoList.cons (X_deg, X_coef) X_tl
            use Z_tl
            use .nil
            constructor
            · simp
            simp
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use X_tl
            use Z_tl
            use .nil
            constructor
            · simp
            simp
      · intro (Y_deg, Y_coef) Y_tl ha_eq hb_eq
        revert ha_eq hb_eq
        apply Z.casesOn
        · intro ha_eq hb_eq
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
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use X_tl
            use CoList.cons (Y_deg, Y_coef) Y_tl
            use .nil
            constructor
            · simp
            simp
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use CoList.cons (X_deg, X_coef) X_tl
            use Y_tl
            use .nil
            constructor
            · simp
            simp
          · replace h_out := CoList.out_eq_cons h_out -- copypaste
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_out
            constructor
            · exact h_out
            simp only [motive]
            use X_tl
            use Y_tl
            use .nil
            constructor
            · simp
            simp
        · intro (Z_deg, Z_coef) Z_tl ha_eq hb_eq -- main case
          have h_XY_out : CoList.out (add (basis := basis_hd :: basis_tl) (CoList.cons (X_deg, X_coef) X_tl) (CoList.cons (Y_deg, Y_coef) Y_tl)) = ?_ := by
            exact add_out_eq
          have h_YZ_out : CoList.out (add (basis := basis_hd :: basis_tl) (CoList.cons (Y_deg, Y_coef) Y_tl) (CoList.cons (Z_deg, Z_coef) Z_tl)) = ?_ := by
            exact add_out_eq
          simp [add_out] at h_XY_out h_YZ_out
          split_ifs at h_XY_out h_YZ_out <;>
          (
            replace h_XY_out := CoList.out_eq_cons h_XY_out
            replace h_YZ_out := CoList.out_eq_cons h_YZ_out
            rw [h_XY_out] at ha_eq
            rw [h_YZ_out] at hb_eq
            have ha_out : CoList.out a =
              ?_ := by rw [ha_eq]; exact add_out_eq
            have hb_out : CoList.out b =
              ?_ := by rw [hb_eq]; exact add_out_eq
            simp [add_out] at ha_out hb_out
            split_ifs at ha_out hb_out <;> (try linarith) <;>
            (
              replace ha_out := CoList.out_eq_cons ha_out
              replace hb_out := CoList.out_eq_cons hb_out
              use ?_
              use ?_
              use ?_
              constructor
              · exact ha_out
              constructor
              · try rw [add_assoc']
                exact hb_out
              simp only [motive]
              use ?_
              use ?_
              use ?_
              constructor
              · try rw [← h_XY_out]
                try rw [← h_YZ_out]
                try (congr <;> (exact Eq.refl _))
              · try rw [← h_XY_out]
                try rw [← h_YZ_out]
                try congr
            )
          )
  · simp only [motive]
    use X
    use Y
    use Z

@[simp]
theorem add_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    (X.add Y).leadingExp = X.leadingExp ⊔ Y.leadingExp := by
  apply X.casesOn
  · simp [leadingExp]
  · intro (X_deg, X_coef) X_tl
    apply Y.casesOn
    · simp [leadingExp]
    intro (Y_deg, Y_coef) Y_tl
    rw [add_cons_cons]
    split_ifs <;> {
      simp [leadingExp]
      linarith
    }

theorem add_wellOrdered {basis : Basis} {x y : PreMS basis}
    (h_x_wo : x.wellOrdered) (h_y_wo : y.wellOrdered) : (x.add y).wellOrdered := by
  cases basis with
  | nil =>
    constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)),
        ms = X.add Y ∧ X.wellOrdered ∧ Y.wellOrdered
    apply wellOrdered.coind motive
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
          obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := hY_wo
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
        obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := hX_wo'
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
          obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := hY_wo'
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
            · simp
              constructor
              · exact hX_comp
              · simpa [leadingExp]
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
            · simp
              constructor
              · simpa [leadingExp]
              · exact hY_comp
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
            · simp
              constructor
              · exact hX_comp
              · exact hY_comp
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
    apply isApproximation.coind motive
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


end PreMS

end TendstoTactic
