/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Basis
import Mathlib.Tactic.Tendsto.Multiseries.Operations.Basic

/-!
# Addition for multiseries

-/


namespace TendstoTactic

namespace PreMS

open Stream' Seq

/-- Addition for multiseries. It merges multiseries `x` and `y` maintaining the correct order of
exponents. It is defined corecursively as following:
* `add x [] = x`
* `add [] y = y`
* `
  add ((x_exp, x_coef) :: x_tl) ((y_exp, y_coef) :: y_tl) =
    if x_exp > y_exp then
      (x_exp, x_coef) :: (x_tl.add y)
    else if y_exp > x_exp then
      (y_exp, y_coef) :: (x.add y_tl)
    else
      (x_exp, x_coef.add y_coef) :: (x_tl.add y_tl)
  `
-/
noncomputable def add {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  match basis with
  | [] => a + b
  | List.cons basid_hd basis_tl =>
    let T := (PreMS (basid_hd :: basis_tl)) × (PreMS (basid_hd :: basis_tl))
    let g : T → Option ((ℝ × PreMS basis_tl) × T) := fun (x, y) =>
      match destruct x, destruct y with
      | none, none => none
      | none, some ((y_exp, y_coef), y_tl) => some ((y_exp, y_coef), (.nil, y_tl))
      | some ((x_exp, x_coef), x_tl), none => some ((x_exp, x_coef), (x_tl, .nil))
      | some ((x_exp, x_coef), x_tl), some ((y_exp, y_coef), y_tl) =>
        if y_exp < x_exp then
          some ((x_exp, x_coef), (x_tl, y))
        else if x_exp < y_exp then
          some ((y_exp, y_coef), (x, y_tl))
        else
          some ((x_exp, x_coef.add y_coef), (x_tl, y_tl))
    Seq.corec g (a, b)

/-- Subtraction for multiseries, defined as `a - b = a + (-b)`. -/
noncomputable def sub {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  a.add b.neg

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
noncomputable instance instAdd {basis : Basis} : Add (PreMS basis) where
  add := add

/-- This instance is copy of the previous. But without it `Add (PreMS (basis_hd :: basis_tl))` can
not be inferred. -/
noncomputable instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    Add (PreMS (basis_hd :: basis_tl)) :=
  instAdd

-- theorems
open Filter Asymptotics

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
    cases' y with hd tl
    · right
      simp [HAdd.hAdd, Add.add, add, Seq.corec_nil]
    · left
      use hd, ?_, tl
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
    cases' y with hd tl
    · right
      simp
    · left
      use hd, ?_, tl
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

/-- Auxillary definition. It is "unfolded" version of `add` without `corec` in body. In the
`add_unfold` we show that `add x y = add' x y`. -/
noncomputable def add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (x y : PreMS (basis_hd :: basis_tl)) :
    (PreMS (basis_hd :: basis_tl)) :=
  match destruct x, destruct y with
  | none, _ => y
  | _, none => x
  | some ((x_exp, x_coef), x_tl), some ((y_exp, y_coef), y_tl) =>
    if y_exp < x_exp then
      Seq.cons (x_exp, x_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) x_tl y)
    else if x_exp < y_exp then
      Seq.cons (y_exp, y_coef) (x + y_tl)
    else
      Seq.cons (x_exp, x_coef + y_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) x_tl y_tl)

theorem add_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis} {x y : PreMS (basis_hd :: basis_tl)} :
    x + y = add' x y := by
  cases' x with x_exp x_coef x_tl
  · simp [add']
  cases' y with y_exp y_coef y_tl
  · simp [add']
  simp [HAdd.hAdd, Add.add, add, add']
  split_ifs <;>
  (
    rw [Seq.corec_cons]
    simp only [destruct_cons]
    split_ifs
    rfl
  )

/-- `((X_exp, X_coef) :: X_tl) + Y = (X_exp, X_coef) :: (X_tl + Y)` when `X_exp > Y.leadingExp`. -/
theorem add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp : ℝ} {X_coef : PreMS basis_tl}
    {X_tl Y : PreMS (basis_hd :: basis_tl)} (h_lt : Y.leadingExp < X_exp) :
    HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_exp, X_coef) X_tl) Y =
    Seq.cons (X_exp, X_coef) (X_tl + Y) := by
  rw [add_unfold, add']
  cases' Y with Y_exp Y_coef Y_tl
  · simp
  · simp at h_lt
    simp only [destruct_cons, not_lt]
    split_ifs
    · rfl
    · exfalso
      linarith

/-- `X + ((Y_exp, Y_coef) :: Y_tl) = (Y_exp, Y_coef) :: (X + Y_tl)` when `Y_exp > X.leadingExp`. -/
theorem add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_exp : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl X : PreMS (basis_hd :: basis_tl)} (h_lt : X.leadingExp < Y_exp) :
    X + (Seq.cons (Y_exp, Y_coef) Y_tl) = Seq.cons (Y_exp, Y_coef) (X + Y_tl) := by
  rw [add_unfold, add']
  cases' X with X_exp X_coef X_tl
  · simp
  · simp at h_lt
    simp only [destruct_cons, not_lt]
    split_ifs
    · exfalso
      linarith
    · rfl

theorem add_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X_tl Y_tl: PreMS (basis_hd :: basis_tl)} {X_exp Y_exp : ℝ} {X_coef Y_coef : PreMS basis_tl}
    : HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_exp, X_coef) X_tl)
      (Seq.cons (Y_exp, Y_coef) Y_tl) =
    if Y_exp < X_exp then
      Seq.cons (X_exp, X_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl
        (Seq.cons (Y_exp, Y_coef) Y_tl))
    else if X_exp < Y_exp then
      Seq.cons (Y_exp, Y_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl))
        (Seq.cons (X_exp, X_coef) X_tl) Y_tl)
    else
      Seq.cons (X_exp, X_coef + Y_coef) (HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) X_tl Y_tl)
    := by
  rw [add_unfold, add']
  simp

/-- `add` commutes with `mulConst`. -/
theorem add_mulConst {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
    (X + Y).mulConst c = (X.mulConst c) + Y.mulConst c := by
  cases basis with
  | nil => simp [mulConst]; ring
  | cons basis_hd basis_tl =>
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)), a = (X + Y).mulConst c ∧
      b = X.mulConst c + Y.mulConst c
    apply Seq.Eq.coind_strong motive
    · simp only [motive]
      use X, Y
    · intro a b ih
      simp only [motive] at ih ⊢
      obtain ⟨X, Y, ha, hb⟩ := ih
      subst ha hb
      cases' X with X_exp X_coef X_tl
      · simp
      cases' Y with Y_exp Y_coef Y_tl
      · simp
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
      · have : X_exp = Y_exp := by linarith
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

/-- Addition is commutative. -/
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
    cases' X with X_exp X_coef X_tl
    · simp
    cases' Y with Y_exp Y_coef Y_tl
    · simp
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
    · have : X_exp = Y_exp := by linarith -- almost copypaste
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

/-- Addition is associative. -/
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
    cases' X with X_exp X_coef X_tl
    · simp
    cases' Y with Y_exp Y_coef Y_tl
    · simp
    cases' Z with Z_exp Z_coef Z_tl
    · simp
    right
    have h_XY : HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (X_exp, X_coef) X_tl)
        (Seq.cons (Y_exp, Y_coef) Y_tl) = ?_ := by
      rw [add_unfold, add']
      simp
      exact Eq.refl _
    have h_YZ : HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (Seq.cons (Y_exp, Y_coef) Y_tl)
        (Seq.cons (Z_exp, Z_coef) Z_tl) = ?_ := by
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

/-- This instance is necessary for using `abel` tactic later. -/
noncomputable instance instAddCommMonoid (basis : Basis) : AddCommMonoid (PreMS basis) where
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

/-- This instance is copy of the previous. But without it
`AddCommMonoid (PreMS (basis_hd :: basis_tl))` can not be inferred. -/
noncomputable instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    AddCommMonoid (PreMS (basis_hd :: basis_tl)) := by apply instAddCommMonoid

@[simp]
theorem add_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    (X + Y).leadingExp = X.leadingExp ⊔ Y.leadingExp := by
  cases' X with X_exp X_coef X_tl
  · simp
  cases' Y with Y_exp Y_coef X_tl
  · simp
  rw [add_cons_cons]
  split_ifs <;> {
    simp
    linarith
  }

/-- `X + Y` is well-ordered when `X` and `Y` are well-ordered. -/
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
      use x, y
    · intro ms ih
      simp only [motive] at ih
      obtain ⟨X, Y, h_ms_eq, hX_wo, hY_wo⟩ := ih
      cases' X with X_exp X_coef X_tl
      · cases' Y with Y_exp Y_coef Y_tl
        · left
          simpa using h_ms_eq
        · obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
          right
          simp at h_ms_eq
          use Y_exp, Y_coef, Y_tl
          constructor
          · exact h_ms_eq
          constructor
          · exact hY_coef_wo
          constructor
          · exact hY_comp
          simp only [motive]
          use .nil, Y_tl
          simp
          constructor
          · apply WellOrdered.nil
          · exact hY_tl_wo
      · obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
        right
        cases' Y with Y_exp Y_coef Y_tl
        · simp at h_ms_eq
          use X_exp, X_coef, X_tl
          constructor
          · exact h_ms_eq
          constructor
          · exact hX_coef_wo
          constructor
          · exact hX_comp
          simp only [motive]
          use .nil, X_tl
          simp
          constructor
          · apply WellOrdered.nil
          · exact hX_tl_wo
        · obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
          rw [add_cons_cons] at h_ms_eq
          split_ifs at h_ms_eq
          · use ?_, ?_, ?_
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
            use X_tl, .cons (Y_exp, Y_coef) Y_tl
          · use ?_, ?_, ?_
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
            use .cons (X_exp, X_coef) X_tl, Y_tl
          · have h_exp : X_exp = Y_exp := by linarith
            subst h_exp
            use ?_, ?_, ?_
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
            use X_tl, Y_tl

/-- If `X` approximates `FX` and `Y` approximates `FY`, then `X + Y` approximates `FX + FY`. -/
theorem add_Approximates {basis : Basis} {X Y : PreMS basis} {FX FY : ℝ → ℝ}
    (hX_approx : X.Approximates FX) (hY_approx : Y.Approximates FY) :
    (X + Y).Approximates (FX + FY) := by
  cases basis with
  | nil =>
    simp [Approximates] at *
    exact EventuallyEq.add hX_approx hY_approx
  | cons basis_hd basis_tl =>
    let motive : (ℝ → ℝ) → (PreMS (basis_hd :: basis_tl)) → Prop := fun F ms =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)) (FX FY : ℝ → ℝ),
        ms = X + Y ∧ F =ᶠ[atTop] FX + FY ∧ X.Approximates FX ∧ Y.Approximates FY
    apply Approximates.coind motive
    · simp only [motive]
      use X, Y, FX, FY
    · intro F ms ih
      simp only [motive] at ih
      obtain ⟨X, Y, FX, FY, h_ms_eq, hf_eq, hX_approx, hY_approx⟩ := ih
      cases' X with X_exp X_coef X_tl
      · apply Approximates_nil at hX_approx
        cases' Y with Y_exp Y_coef Y_tl
        · apply Approximates_nil at hY_approx
          left
          simp at h_ms_eq
          constructor
          · exact h_ms_eq
          trans
          · exact hf_eq
          conv => rhs; ext x; simp; rw [← add_zero 0]
          apply EventuallyEq.add
          exacts [hX_approx, hY_approx]
        · obtain ⟨CY, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
          right
          simp at h_ms_eq
          replace hf_eq : F =ᶠ[atTop] FY := by
            trans
            · exact hf_eq
            conv => rhs; ext x; rw [← zero_add (FY x)]
            apply EventuallyEq.add hX_approx
            rfl
          use ?_, ?_, ?_, CY
          constructor
          · exact h_ms_eq
          constructor
          · exact hY_coef
          constructor
          · apply majorated_of_EventuallyEq hf_eq
            exact hY_maj
          simp only [motive]
          use .nil, Y_tl, 0, fun x ↦ FY x - basis_hd x ^ Y_exp * CY x
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
      · obtain ⟨CX, hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
        right
        cases' Y with Y_exp Y_coef Y_tl
        · apply Approximates_nil at hY_approx
          simp at h_ms_eq
          replace hf_eq : F =ᶠ[atTop] FX := by
            trans
            · exact hf_eq
            conv => rhs; ext x; rw [← add_zero (FX x)]
            apply EventuallyEq.add _ hY_approx
            rfl
          use ?_, ?_, ?_, CX
          constructor
          · exact h_ms_eq
          constructor
          · exact hX_coef
          constructor
          · apply majorated_of_EventuallyEq hf_eq
            exact hX_maj
          simp only [motive]
          use .nil, X_tl, 0, fun x ↦ FX x - basis_hd x ^ X_exp * CX x
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
        · obtain ⟨CY, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
          rw [add_cons_cons] at h_ms_eq
          split_ifs at h_ms_eq
          · use X_exp, X_coef, ?_, CX
            constructor
            · exact h_ms_eq
            constructor
            · exact hX_coef
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
              linarith
            simp only [motive]
            use X_tl, Seq.cons (Y_exp, Y_coef) Y_tl, fun x ↦ FX x - basis_hd x ^ X_exp * CX x, FY
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
                rw [show F x + (-FX x - FY x) = F x - (FX x + FY x) by ring]
              apply eventuallyEq_iff_sub.mp hf_eq
            constructor
            · exact hX_tl
            · exact hY_approx
          · use Y_exp, Y_coef, ?_, CY
            constructor
            · exact h_ms_eq
            constructor
            · exact hY_coef
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
              linarith
            simp only [motive]
            use Seq.cons (X_exp, X_coef) X_tl, Y_tl, FX, fun x ↦ FY x - basis_hd x ^ Y_exp * CY x
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
                rw [show F x + (-FX x - FY x) = F x - (FX x + FY x) by ring]
              apply eventuallyEq_iff_sub.mp hf_eq
            constructor
            · exact hX_approx
            · exact hY_tl
          · have : X_exp = Y_exp := by linarith
            subst this
            use X_exp, X_coef + Y_coef, ?_, CX + CY
            constructor
            · exact h_ms_eq
            constructor
            · exact add_Approximates hX_coef hY_coef
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
            simp only [motive]
            use X_tl, Y_tl,
              fun x ↦ FX x - basis_hd x ^ X_exp * CX x,
              fun x ↦ FY x - basis_hd x ^ X_exp * CY x
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
                rw [show F x + (-FX x - FY x) = F x - (FX x + FY x) by ring]
              apply eventuallyEq_iff_sub.mp hf_eq
            constructor
            · exact hX_tl
            · exact hY_tl

/-- `X - Y` is well-ordered when `X` and `Y` are well-ordered. -/
theorem sub_WellOrdered {basis : Basis} {x y : PreMS basis}
    (h_x_wo : x.WellOrdered) (h_y_wo : y.WellOrdered) : (x.sub y).WellOrdered := by
  unfold sub
  apply add_WellOrdered h_x_wo
  apply neg_WellOrdered h_y_wo

/-- If `X` approximates `FX` and `Y` approximates `FY`, then `X - Y` approximates `FX - FY`. -/
theorem sub_Approximates {basis : Basis} {X Y : PreMS basis} {FX FY : ℝ → ℝ}
    (hX_approx : X.Approximates FX) (hY_approx : Y.Approximates FY) :
    (X.sub Y).Approximates (FX - FY) := by
  rw [sub_eq_add_neg]
  unfold sub
  apply add_Approximates hX_approx
  apply neg_Approximates hY_approx

end PreMS

end TendstoTactic
