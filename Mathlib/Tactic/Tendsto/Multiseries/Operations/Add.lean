import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Basis
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Basic

set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace TendstoTactic

namespace PreMS

open Stream' Seq

noncomputable def add {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  match basis with
  | [] => a + b
  | List.cons basid_hd basis_tl =>
    let T := (PreMS (basid_hd :: basis_tl)) × (PreMS (basid_hd :: basis_tl))
    let g : T → Option ((ℝ × PreMS basis_tl) × T) := fun (x, y) =>
      match destruct x, destruct y with
      | none, none => none
      | none, some ((y_deg, y_coef), y_tl) => some ((y_deg, y_coef), (.nil, y_tl))
      | some ((x_deg, x_coef), x_tl), none => some ((x_deg, x_coef), (x_tl, .nil))
      | some ((x_deg, x_coef), x_tl), some ((y_deg, y_coef), y_tl) =>
        if y_deg < x_deg then
          some ((x_deg, x_coef), (x_tl, y))
        else if x_deg < y_deg then
          some ((y_deg, y_coef), (x, y_tl))
        else
          some ((x_deg, x_coef.add y_coef), (x_tl, y_tl))
    Seq.corec g (a, b)

noncomputable instance instAdd {basis : List (ℝ → ℝ)} : Add (PreMS basis) where
  add := add

-- TODO: can I get rid of it?
noncomputable instance {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} : Add (PreMS (basis_hd :: basis_tl)) :=
  instAdd

-- theorems
open Filter Asymptotics

scoped instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Zero (PreMS (basis_hd :: basis_tl)) :=
  instZero

@[simp]
theorem noConfusion_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd : ℝ × PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    (Seq.cons hd tl) ≠ (0 : PreMS (basis_hd :: basis_tl)) := by
  rw [show (0 : PreMS (basis_hd :: basis_tl)) = Seq.nil by rfl]
  simp

@[simp]
theorem noConfusion_zero' {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd : ℝ × PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    (0 : PreMS (basis_hd :: basis_tl)) ≠ (Seq.cons hd tl) := by
  exact noConfusion_zero.symm

@[simp]
theorem nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) Seq.nil ms = ms := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
    x = HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) Seq.nil y
  apply Seq.Eq.coind motive
  · simp only [motive]
  · intro x y ih
    simp [motive] at ih
    subst ih
    apply y.recOn
    · right
      simp [HAdd.hAdd, Add.add, add, Seq.corec_nil]
    · intro (deg, coef) tl
      left
      use (deg, coef)
      use ?_
      use tl
      constructor
      · simp [HAdd.hAdd, Add.add, add]
        rw [corec_cons]
        pick_goal 2
        · simp
          constructor <;> exact Eq.refl _
        exact Eq.refl _
      constructor
      · rfl
      simp only [motive]
      rfl

@[simp]
private theorem zero_add' {basis : Basis} {ms : PreMS basis} :
    (zero _) + ms = ms := by
  cases basis with
  | nil => simp [zero]
  | cons => simp [zero]

-- copypaste from above
@[simp]
theorem add_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) ms Seq.nil = ms := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun x y =>
    x = HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) y Seq.nil
  apply Seq.Eq.coind motive
  · simp only [motive]
  · intro x y ih
    simp [motive] at ih
    subst ih
    apply y.recOn
    · right
      simp
    · intro (deg, coef) tl
      left
      use (deg, coef)
      use ?_
      use tl
      constructor
      · simp [HAdd.hAdd, Add.add, add]
        rw [corec_cons]
        pick_goal 2
        · simp
          constructor <;> exact Eq.refl _
        exact Eq.refl _
      constructor
      · rfl
      simp only [motive]
      rfl

@[simp]
private theorem add_zero' {basis : Basis} {ms : PreMS basis} :
    ms + (zero _) = ms := by
  cases basis with
  | nil => simp [zero]
  | cons => simp [zero]

noncomputable def add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (x y : PreMS (basis_hd :: basis_tl)) :
    (PreMS (basis_hd :: basis_tl)) :=
  match destruct x, destruct y with
  | none, _ => y
  | _, none => x
  | some ((x_deg, x_coef), x_tl), some ((y_deg, y_coef), y_tl) =>
    if y_deg < x_deg then
      Seq.cons (x_deg, x_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) x_tl y)
    else if x_deg < y_deg then
      Seq.cons (y_deg, y_coef) (x + y_tl)
    else
      Seq.cons (x_deg, x_coef + y_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) x_tl y_tl)

theorem add_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : PreMS (basis_hd :: basis_tl)} :
    x + y = add' x y := by
  apply x.recOn
  · simp [add']
  intro (x_deg, x_coef) x_tl
  apply y.recOn
  · simp [add']
  intro (y_deg, y_coef) y_tl
  simp [HAdd.hAdd, Add.add, add, add']
  split_ifs <;>
  (
    rw [Seq.corec_cons]
    simp only [destruct_cons]
    split_ifs
    rfl
  )

-- do we need it?
-- theorem add_eq_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)}
--     (h : X + Y = .nil) : X = .nil ∧ Y = .nil := by
--   have := add_out_eq (x := X) (y := Y)
--   unfold add_out at this
--   rw [h] at this
--   simp at this
--   revert this
--   apply X.casesOn
--   · apply Y.casesOn
--     · simp
--     · intro hd tl this
--       simp at this
--   · apply Y.casesOn
--     · intro hd tl this
--       simp at this
--     · intro _ _ _ _ this
--       simp at this
--       split_ifs at this

theorem add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_deg : ℝ} {X_coef : PreMS basis_tl}
    {X_tl Y : PreMS (basis_hd :: basis_tl)} (h_lt : Y.leadingExp < X_deg) :
    HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) Y = Seq.cons (X_deg, X_coef) (X_tl + Y) := by
  rw [add_unfold, add']
  revert h_lt
  apply Y.recOn
  · simp
  · intro (Y_deg, Y_coef) Y_tl h_lt
    simp at h_lt
    simp only [destruct_cons, not_lt]
    split_ifs
    · rfl
    · exfalso
      linarith

theorem add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_deg : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl X : PreMS (basis_hd :: basis_tl)} (h_lt : X.leadingExp < Y_deg) :
    X + (Seq.cons (Y_deg, Y_coef) Y_tl) = Seq.cons (Y_deg, Y_coef) (X + Y_tl) := by
  rw [add_unfold, add']
  revert h_lt
  apply X.recOn
  · simp
  · intro (X_deg, X_coef) X_tl h_lt
    simp at h_lt
    simp only [destruct_cons, not_lt]
    split_ifs
    · exfalso
      linarith
    · rfl

theorem add_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_tl Y_tl: PreMS (basis_hd :: basis_tl)}
    {X_deg Y_deg : ℝ} {X_coef Y_coef : PreMS basis_tl}
    : HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) (Seq.cons (Y_deg, Y_coef) Y_tl) =
    if Y_deg < X_deg then
      Seq.cons (X_deg, X_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl (Seq.cons (Y_deg, Y_coef) Y_tl))
    else if X_deg < Y_deg then
      Seq.cons (Y_deg, Y_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) Y_tl)
    else
      Seq.cons (X_deg, X_coef + Y_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl Y_tl)
    := by
  rw [add_unfold, add']
  simp

theorem add_mulConst {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
    (X + Y).mulConst c = (X.mulConst c) + Y.mulConst c := by
  cases basis with
  | nil => simp [mulConst]; ring
  | cons basis_hd basis_tl =>
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)), a = (X + Y).mulConst c ∧ b = X.mulConst c + Y.mulConst c
    apply Seq.Eq.coind_strong motive
    · simp only [motive]
      use X, Y
    · intro a b ih
      simp only [motive] at ih ⊢
      obtain ⟨X, Y, ha, hb⟩ := ih
      subst ha hb
      apply X.recOn
      · simp
      intro (X_deg, X_coef) X_tl
      apply Y.recOn
      · simp
      intro (Y_deg, Y_coef) Y_tl
      right
      rw [add_cons_cons]
      split_ifs
      · use ?_, ?_, ?_
        constructor
        · simp
          exact Eq.refl _
        constructor
        · simp
          rw [add_cons_cons]
          split_ifs
          exact Eq.refl _
        use ?_, ?_
        constructor
        · exact Eq.refl _
        · simp
      · use ?_, ?_, ?_
        constructor
        · simp
          exact Eq.refl _
        constructor
        · simp
          rw [add_cons_cons]
          split_ifs
          exact Eq.refl _
        use ?_, ?_
        constructor
        · exact Eq.refl _
        · simp
      · have : X_deg = Y_deg := by linarith
        subst this
        use ?_, ?_, ?_
        constructor
        · simp
          exact Eq.refl _
        constructor
        · simp
          rw [add_cons_cons]
          split_ifs
          rw [add_mulConst]
          exact Eq.refl _
        use ?_, ?_
        constructor
        · exact Eq.refl _
        · simp

private theorem add_comm' {basis : Basis} {X Y : PreMS basis} :
    X + Y = Y + X := by
  cases basis with
  | nil => simp [HAdd.hAdd, Add.add]; simp [add]; ring
  | cons basis_hd basis_tl =>
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
    ∃ (X Y : PreMS (basis_hd :: basis_tl)), a = (X + Y) ∧ b = Y + X
  apply Seq.Eq.coind_strong motive
  · simp only [motive]
    use X, Y
  · intro a b ih
    obtain ⟨X, Y, ha_eq, hb_eq⟩ := ih
    subst ha_eq hb_eq
    apply X.recOn
    · left
      simp
    intro (X_deg, X_coef) X_tl
    apply Y.recOn
    · left
      simp
    intro (Y_deg, Y_coef) Y_tl
    right
    rw [add_cons_cons, add_cons_cons]
    split_ifs with h1 h2
    · linarith
    · use ?_, ?_, ?_
      constructor
      · exact Eq.refl _
      constructor
      · exact Eq.refl _
      simp only [motive]
      use ?_, ?_
      constructor
      · exact Eq.refl _
      · rfl
    · use ?_, ?_, ?_ -- total copypaste
      constructor
      · exact Eq.refl _
      constructor
      · exact Eq.refl _
      simp only [motive]
      use ?_, ?_
      constructor
      · exact Eq.refl _
      · rfl
    · have : X_deg = Y_deg := by linarith -- almost copypaste
      subst this
      use ?_, ?_, ?_
      constructor
      · exact Eq.refl _
      constructor
      · rw [add_comm']
        exact Eq.refl _
      simp only [motive]
      use ?_, ?_
      constructor
      · exact Eq.refl _
      · rfl

private theorem add_assoc' {basis : Basis} {X Y Z : PreMS basis} :
    X + (Y + Z) = (X + Y) + Z := by
  cases basis with
  | nil => simp [HAdd.hAdd, Add.add]; simp [add]; ring
  | cons basis_hd basis_tl =>
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
    ∃ (X Y Z : PreMS (basis_hd :: basis_tl)), a = X + (Y + Z) ∧ b = (X + Y) + Z
  apply Seq.Eq.coind_strong motive
  · simp only [motive]
    use X, Y, Z
  · intro a b ih
    simp only [motive] at ih ⊢
    obtain ⟨X, Y, Z, ha_eq, hb_eq⟩ := ih
    subst ha_eq hb_eq
    apply X.recOn
    · simp
    intro (X_deg, X_coef) X_tl
    apply Y.recOn
    · simp
    intro (Y_deg, Y_coef) Y_tl
    apply Z.recOn
    · simp
    intro (Z_deg, Z_coef) Z_tl
    right
    have h_XY : HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_deg, X_coef) X_tl) (Seq.cons (Y_deg, Y_coef) Y_tl) = ?_ := by
      rw [add_unfold, add']
      simp
      exact Eq.refl _
    have h_YZ : HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (Y_deg, Y_coef) Y_tl) (Seq.cons (Z_deg, Z_coef) Z_tl) = ?_ := by
      rw [add_unfold, add']
      simp
      exact Eq.refl _
    split_ifs at h_XY h_YZ <;>
    (
      rw [h_XY, h_YZ]
      simp_rw [add_cons_cons]
      split_ifs <;> (try exfalso; linarith) <;>
      (
        use ?_, ?_, ?_
        constructor
        · exact Eq.refl _
        constructor
        · try rw [add_assoc']
          exact Eq.refl _
        use ?_, ?_, ?_
        constructor
        · try rw [← h_XY]
          try rw [← h_YZ]
          exact Eq.refl _
        · try rw [← h_XY]
          try rw [← h_YZ]
          try rfl
      )
    )

-- to be able to use `abel` tactic
noncomputable instance instAddCommMonoid (basis : List (ℝ → ℝ)) : AddCommMonoid (PreMS basis) where
  zero_add := by
    intro a
    apply zero_add'
  add_zero := by
    intro a
    apply add_zero'
  add_assoc := by
    intro a b c
    apply add_assoc'.symm
  add_comm := by
    intro a b
    apply add_comm'
  nsmul := nsmulRec

-- TODO: can I get rid of specifiyng in explicitly?
noncomputable instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : AddCommMonoid (PreMS (basis_hd :: basis_tl)) := by apply instAddCommMonoid

@[simp]
theorem add_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    (X + Y).leadingExp = X.leadingExp ⊔ Y.leadingExp := by
  apply X.recOn
  · simp
  · intro (X_deg, X_coef) X_tl
    apply Y.recOn
    · simp
    intro (Y_deg, Y_coef) Y_tl
    rw [add_cons_cons]
    split_ifs <;> {
      simp
      linarith
    }

theorem add_WellOrdered {basis : Basis} {x y : PreMS basis}
    (h_x_wo : x.WellOrdered) (h_y_wo : y.WellOrdered) : (x + y).WellOrdered := by
  cases basis with
  | nil =>
    constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)),
        ms = X + Y ∧ X.WellOrdered ∧ Y.WellOrdered
    apply WellOrdered.coind motive
    · simp only [motive]
      use x
      use y
    · intro ms ih
      simp only [motive] at ih
      obtain ⟨X, Y, h_ms_eq, hX_wo, hY_wo⟩ := ih
      revert h_ms_eq hX_wo
      apply X.recOn
      · intro h_ms_eq hX_wo
        revert h_ms_eq hY_wo
        apply Y.recOn
        · intro hY_wo h_ms_eq
          left
          simpa using h_ms_eq
        · intro (Y_deg, Y_coef) Y_tl hY_wo h_ms_eq
          replace hY_wo := WellOrdered_cons hY_wo
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
          simp
          constructor
          · apply WellOrdered.nil
          · exact hY_tl_wo
      · intro (X_deg, X_coef) X_tl h_ms_eq hX_wo
        have hX_wo' := WellOrdered_cons hX_wo
        obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := hX_wo'
        right
        revert h_ms_eq hY_wo
        apply Y.recOn
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
          simp
          constructor
          · apply WellOrdered.nil
          · exact hX_tl_wo
        · intro (Y_deg, Y_coef) Y_tl hY_wo h_ms_eq
          have hY_wo' := WellOrdered_cons hY_wo
          obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := hY_wo'
          rw [add_cons_cons] at h_ms_eq
          split_ifs at h_ms_eq with h1 h2
          · use ?_
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
              · simpa
            simp only [motive]
            use X_tl
            use .cons (Y_deg, Y_coef) Y_tl
          · use ?_
            use ?_
            use ?_
            constructor
            · exact h_ms_eq
            constructor
            · exact hY_coef_wo
            constructor
            · simp
              constructor
              · simpa
              · exact hY_comp
            simp only [motive]
            use .cons (X_deg, X_coef) X_tl
            use Y_tl
          · have h_deg : X_deg = Y_deg := by linarith
            subst h_deg
            clear h1 h2
            use ?_
            use ?_
            use ?_
            constructor
            · exact h_ms_eq
            constructor
            · exact add_WellOrdered hX_coef_wo hY_coef_wo
            constructor
            · simp
              constructor
              · exact hX_comp
              · exact hY_comp
            simp only [motive]
            use X_tl
            use Y_tl

theorem add_Approximates {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
    (hX_approx : X.Approximates fX basis) (hY_approx : Y.Approximates fY basis) :
    (X + Y).Approximates (fX + fY) basis := by
  cases basis with
  | nil =>
    simp [Approximates] at *
    exact EventuallyEq.add hX_approx hY_approx
  | cons basis_hd basis_tl =>
    let motive : (ℝ → ℝ) → (PreMS (basis_hd :: basis_tl)) → Prop := fun f ms =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)) (fX fY : ℝ → ℝ),
        ms = X + Y ∧ f =ᶠ[atTop] fX + fY ∧ X.Approximates fX ∧ Y.Approximates fY
    apply Approximates.coind motive
    · simp only [motive]
      use X
      use Y
      use fX
      use fY
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨X, Y, fX, fY, h_ms_eq, hf_eq, hX_approx, hY_approx⟩ := ih
      revert h_ms_eq hX_approx
      apply X.recOn
      · intro h_ms_eq hX_approx
        replace hX_approx := Approximates_nil hX_approx
        revert h_ms_eq hY_approx
        apply Y.recOn
        · intro hY_approx h_ms_eq
          replace hY_approx := Approximates_nil hY_approx
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
          have hY_approx' := Approximates_cons hY_approx
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
          · apply Approximates.nil
            rfl
          · exact hY_tl
      · intro (X_deg, X_coef) X_tl h_ms_eq hX_approx
        have hX_approx' := Approximates_cons hX_approx
        obtain ⟨XC, hX_coef, hX_comp, hX_tl⟩ := hX_approx'
        right
        revert h_ms_eq hY_approx
        apply Y.recOn
        · intro hY_approx h_ms_eq
          replace hY_approx := Approximates_nil hY_approx
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
          · apply Approximates.nil
            rfl
          · exact hX_tl
        · intro (Y_deg, Y_coef) Y_tl hY_approx h_ms_eq
          have hY_approx' := Approximates_cons hY_approx
          obtain ⟨YC, hY_coef, hY_comp, hY_tl⟩ := hY_approx'
          rw [add_cons_cons] at h_ms_eq
          split_ifs at h_ms_eq
          · use X_deg
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
            use Seq.cons (Y_deg, Y_coef) Y_tl
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
          · use Y_deg
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
            use Seq.cons (X_deg, X_coef) X_tl
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
          · have : X_deg = Y_deg := by linarith
            subst this
            use X_deg
            use X_coef.add Y_coef
            use ?_
            use XC + YC
            constructor
            · exact h_ms_eq
            constructor
            · exact add_Approximates hX_coef hY_coef
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

end PreMS

noncomputable def MS.add (x y : MS) (h_basis : y.basis = x.basis) : MS where
  basis := x.basis
  val := x.val.add (h_basis ▸ y.val)
  F := x.F + y.F
  h_wo := by
    have := y.h_wo
    apply PreMS.add_WellOrdered x.h_wo
    generalize y.val = z at *
    generalize y.basis = b at *
    subst h_basis
    simpa
  h_approx := by
    have := y.h_approx
    apply PreMS.add_Approximates x.h_approx
    generalize y.val = z at *
    generalize y.basis = b at *
    subst h_basis
    simpa

end TendstoTactic
