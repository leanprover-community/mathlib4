/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic
import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis
import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Basic

/-!
# Addition for multiseries

-/


namespace ComputeAsymptotics

namespace PreMS

/-- Addition for multiseries. It merges multiseries `X` and `Y` maintaining the correct order of
exponents. It is defined corecursively as following:
* `add X [] = X`
* `add [] Y = Y`
* ```
  add ((X_exp, X_coef) :: X_tl) ((Y_exp, Y_coef) :: Y_tl) =
    if X_exp > Y_exp then
      (X_exp, X_coef) :: (X_tl.add Y)
    else if Y_exp > X_exp then
      (Y_exp, Y_coef) :: (X.add Y_tl)
    else
      (X_exp, X_coef.add Y_coef) :: (X_tl.add Y_tl)
  ```
-/
noncomputable def add {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  match basis with
  | [] => a.toReal + b.toReal
  | List.cons basid_hd basis_tl =>
    let T := (PreMS (basid_hd :: basis_tl)) × (PreMS (basid_hd :: basis_tl))
    let g : T → Option (ℝ × PreMS basis_tl × T) := fun (X, Y) =>
      match destruct X, destruct Y with
      | none, none => none
      | none, some (Y_exp, Y_coef, Y_tl) => some (Y_exp, Y_coef, (.nil, Y_tl))
      | some (X_exp, X_coef, X_tl), none => some (X_exp, X_coef, (X_tl, .nil))
      | some (X_exp, X_coef, X_tl), some (Y_exp, Y_coef, Y_tl) =>
        if Y_exp < X_exp then
          some (X_exp, X_coef, (X_tl, Y))
        else if X_exp < Y_exp then
          some (Y_exp, Y_coef, (X, Y_tl))
        else
          some (X_exp, X_coef.add Y_coef, (X_tl, Y_tl))
    corec g (a, b)

/-- Subtraction for multiseries, defined as `a - b = a + (-b)`. -/
noncomputable def sub {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  a.add b.neg

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
noncomputable instance instAdd {basis : Basis} : Add (PreMS basis) where
  add := add

theorem add_def {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    X + Y = add X Y := rfl

@[simp]
theorem const_add_const (X Y : PreMS []) : X + Y = X.toReal + Y.toReal :=
  rfl

-- theorems
open Filter Asymptotics

@[simp]
theorem nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} :
    HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) nil ms = ms := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun X Y =>
    X = HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) nil Y
  apply eq_of_bisim motive
  · simp only [motive]
  · intro X Y ih
    simp only [motive] at ih
    subst ih
    cases Y with
    | nil => simp [add_def, add, corec_nil]
    | cons Y_exp Y_coef Y_tl =>
    · right
      use Y_exp, Y_coef, ?_, Y_tl
      constructor
      · simp [add_def, add]
        rw [corec_cons]
        · simp
          rfl
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
    HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) ms nil = ms := by
  let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun X Y =>
    X = HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) Y nil
  apply eq_of_bisim motive
  · simp only [motive]
  · intro X Y ih
    simp only [motive] at ih
    subst ih
    cases Y with
    | nil => simp [add_def, add, corec_nil]
    | cons Y_exp Y_coef Y_tl =>
      right
      use Y_exp, Y_coef, ?_, Y_tl
      constructor
      · simp [add_def, add]
        rw [corec_cons]
        · simp
          rfl
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
`add_unfold` we show that `add X Y = add' X Y`. -/
noncomputable def add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (X Y : PreMS (basis_hd :: basis_tl)) :
    (PreMS (basis_hd :: basis_tl)) :=
  match destruct X, destruct Y with
  | none, _ => Y
  | _, none => X
  | some (X_exp, X_coef, X_tl), some (Y_exp, Y_coef, Y_tl) =>
    if Y_exp < X_exp then
      cons X_exp X_coef (X_tl + Y)
    else if X_exp < Y_exp then
      cons Y_exp Y_coef (X + Y_tl)
    else
      cons X_exp (X_coef + Y_coef) (X_tl + Y_tl)

theorem add_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    X + Y = add' X Y := by
  cases X with
  | nil => simp [add']
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp [add']
  | cons Y_exp Y_coef Y_tl =>
  simp [add_def, add, add']
  split_ifs <;>
  (
    rw [corec_cons]
    simp only [destruct_cons]
    split_ifs
    rfl
  )

/-- `((X_exp, X_coef) :: X_tl) + Y = (X_exp, X_coef) :: (X_tl + Y)` when `X_exp > Y.leadingExp`. -/
theorem add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp : ℝ} {X_coef : PreMS basis_tl}
    {X_tl Y : PreMS (basis_hd :: basis_tl)} (h_lt : Y.leadingExp < X_exp) :
    HAdd.hAdd (α := PreMS (basis_hd :: basis_tl)) (cons X_exp X_coef X_tl) Y =
    cons X_exp X_coef (X_tl + Y) := by
  rw [add_unfold, add']
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl =>
    simp only [leadingExp_cons, WithBot.coe_lt_coe] at h_lt
    simp only [destruct_cons]
    split_ifs
    · rfl
    · linarith

/-- `X + ((Y_exp, Y_coef) :: Y_tl) = (Y_exp, Y_coef) :: (X + Y_tl)` when `Y_exp > X.leadingExp`. -/
theorem add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_exp : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl X : PreMS (basis_hd :: basis_tl)} (h_lt : X.leadingExp < Y_exp) :
    X + (cons Y_exp Y_coef Y_tl) = cons Y_exp Y_coef (X + Y_tl) := by
  rw [add_unfold, add']
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
    simp only [leadingExp_cons, WithBot.coe_lt_coe] at h_lt
    simp only [destruct_cons]
    split_ifs
    · linarith
    · rfl

theorem add_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X_tl Y_tl : PreMS (basis_hd :: basis_tl)} {X_exp Y_exp : ℝ} {X_coef Y_coef : PreMS basis_tl} :
    (cons X_exp X_coef X_tl) + (cons Y_exp Y_coef Y_tl) =
    if Y_exp < X_exp then
      cons X_exp X_coef (X_tl + (cons Y_exp Y_coef Y_tl))
    else if X_exp < Y_exp then
      cons Y_exp Y_coef (cons X_exp X_coef X_tl + Y_tl)
    else
      cons X_exp (X_coef + Y_coef) (X_tl + Y_tl) := by
  rw [add_unfold, add']
  cases Y_tl with
  | nil => simp
  | cons Y_tl_exp Y_tl_coef Y_tl_tl => simp

/-- `add` commutes with `mulConst`. -/
theorem add_mulConst {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
    (X + Y).mulConst c = (X.mulConst c) + Y.mulConst c := by
  cases basis with
  | nil =>
    simp only [mulConst]
    ring_nf
  | cons basis_hd basis_tl =>
    let motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop := fun a b =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)), a = (X + Y).mulConst c ∧
      b = X.mulConst c + Y.mulConst c
    apply eq_of_bisim_strong motive
    · simp only [motive]
      use X, Y
    · intro a b ih
      simp only [motive] at ih ⊢
      obtain ⟨X, Y, ha, hb⟩ := ih
      subst ha hb
      cases X with
      | nil => simp
      | cons X_exp X_coef X_tl =>
      cases Y with
      | nil => simp
      | cons Y_exp Y_coef Y_tl =>
      right
      rw [add_cons_cons]
      split_ifs with h1 h2
      · simp [mulConst_cons]
        use ?_, ?_
        constructor
        · rfl
        · simp [add_cons_cons, h1]
      · simp [mulConst_cons]
        use ?_, ?_
        constructor
        · rfl
        · simp [add_cons_cons, h1, h2]
      · have : X_exp = Y_exp := by linarith
        subst this
        simp [mulConst_cons]
        use ?_, ?_
        constructor
        · rfl
        · simp [add_cons_cons]
          rw [add_mulConst]

/-- Addition is commutative. -/
private theorem add_comm' {basis : Basis} {X Y : PreMS basis} :
    X + Y = Y + X := by
  cases basis with
  | nil =>
    simp
    ring_nf
  | cons basis_hd basis_tl =>
  let motive (a b : PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ (X Y : PreMS (basis_hd :: basis_tl)), a = (X + Y) ∧ b = Y + X
  apply eq_of_bisim_strong motive
  · simp only [motive]
    use X, Y
  · intro a b ih
    obtain ⟨X, Y, rfl, rfl⟩ := ih
    cases X with
    | nil => simp
    | cons X_exp X_coef X_tl =>
    cases Y with
    | nil => simp
    | cons Y_exp Y_coef Y_tl =>
    right
    rw [add_cons_cons, add_cons_cons]
    split_ifs with h1 h2
    · linarith
    · simp [motive]
      use ?_, ?_
    · simp [motive]
      use ?_, ?_
    · have : X_exp = Y_exp := by linarith
      subst this
      simp
      constructor
      · rw [add_comm']
      · simp [motive]
        use ?_, ?_

/-- Addition is associative. -/
private theorem add_assoc' {basis : Basis} {X Y Z : PreMS basis} :
    X + (Y + Z) = (X + Y) + Z := by
  cases basis with
  | nil =>
    simp
    ring_nf
  | cons basis_hd basis_tl =>
  let motive (a b : PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ (X Y Z : PreMS (basis_hd :: basis_tl)), a = X + (Y + Z) ∧ b = (X + Y) + Z
  apply eq_of_bisim_strong motive
  · simp only [motive]
    use X, Y, Z
  · intro a b ih
    simp only [motive] at ih ⊢
    obtain ⟨X, Y, Z, rfl, rfl⟩ := ih
    cases X with
    | nil => simp
    | cons X_exp X_coef X_tl =>
    cases Y with
    | nil => simp
    | cons Y_exp Y_coef Y_tl =>
    cases Z with
    | nil => simp
    | cons Z_exp Z_coef Z_tl =>
    right
    have h_XY : (cons X_exp X_coef X_tl) + (cons Y_exp Y_coef Y_tl) = ?_ := by
      simp only [add_unfold]
      simp [add']
      rfl
    have h_YZ : (cons Y_exp Y_coef Y_tl) + (cons Z_exp Z_coef Z_tl) = ?_ := by
      simp only [add_unfold]
      simp [add']
      rfl
    split_ifs at h_XY h_YZ <;>
    (
      rw [h_XY, h_YZ]
      simp_rw [add_cons_cons]
      split_ifs <;> (try exfalso; linarith) <;>
      (
        simp
        use ?_, ?_, ?_
        try (
          simp [← h_XY, ← h_YZ, add_assoc' (basis := basis_tl)]
          · constructor <;> rfl
        )
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
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl =>
  rw [add_cons_cons]
  split_ifs <;> {
    simp
    linarith
  }

/-- `X + Y` is well-ordered when `X` and `Y` are well-ordered. -/
theorem add_WellOrdered {basis : Basis} {X Y : PreMS basis}
    (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) : (X + Y).WellOrdered := by
  cases basis with
  | nil =>
    constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms =>
      ∃ (X Y : PreMS (basis_hd :: basis_tl)),
        ms = X + Y ∧ X.WellOrdered ∧ Y.WellOrdered
    apply WellOrdered.coind motive
    · simp only [motive]
      use X, Y
    · intro exp coef tl ih
      simp only [motive] at ih
      obtain ⟨X, Y, h_eq, hX_wo, hY_wo⟩ := ih
      cases X with
      | nil =>
        simp at h_eq
        subst h_eq
        obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons hY_wo
        simp [h_coef_wo, h_comp, motive]
        use nil, tl
        simp [WellOrdered.nil, h_tl_wo]
      | cons X_exp X_coef X_tl =>
        obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
        cases Y with
        | nil =>
          simp at h_eq
          simp [h_eq, hX_coef_wo, hX_comp, motive]
          use nil, X_tl
          simp [WellOrdered.nil, hX_tl_wo]
        | cons Y_exp Y_coef Y_tl =>
          obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
          rw [add_cons_cons] at h_eq
          split_ifs at h_eq with h1 h2 <;> simp at h_eq;
          · simp [h_eq, hX_coef_wo, hX_comp, motive, h1]
            use ?_, ?_
          · simp [h_eq, hY_coef_wo, hY_comp, motive, h2]
            use ?_, ?_
          · have h_exp : X_exp = Y_exp := by linarith
            subst h_exp
            simp [h_eq, hX_comp, motive, hY_comp]
            constructor
            · apply add_WellOrdered <;> assumption
            · use ?_, ?_

/-- If `X` approximates `fX` and `Y` approximates `fY`, then `X + Y` approximates `fX + fY`. -/
theorem add_Approximates {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
    (hX_approx : X.Approximates fX) (hY_approx : Y.Approximates fY) :
    (X + Y).Approximates (fX + fY) := by
  cases basis with
  | nil =>
    simp only [Approximates_const_iff] at *
    exact hX_approx.add hY_approx
  | cons basis_hd basis_tl =>
    let motive (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) : Prop :=
      ∃ (X Y : PreMS (basis_hd :: basis_tl)) (fX fY : ℝ → ℝ),
        ms = X + Y ∧ f =ᶠ[atTop] fX + fY ∧ X.Approximates fX ∧ Y.Approximates fY
    apply Approximates.coind motive
    · simp only [motive]
      use X, Y, fX, fY
    · intro ms f ih
      simp only [motive] at ih
      obtain ⟨X, Y, fX, fY, rfl, hf_eq, hX_approx, hY_approx⟩ := ih
      cases X with
      | nil =>
        apply Approximates_nil at hX_approx
        cases Y with
        | nil =>
          apply Approximates_nil at hY_approx
          left
          simp
          grw [hf_eq, hX_approx, hY_approx]
          simp
        | cons Y_exp Y_coef Y_tl =>
          obtain ⟨fYC, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
          right
          grw [hX_approx] at hf_eq
          simp at hf_eq
          simp
          use fYC
          simp [hY_coef]
          constructor
          · apply majorated_of_EventuallyEq hf_eq
            assumption
          simp [motive]
          use nil, Y_tl
          simp
          use 0, fun t ↦ fY t - basis_hd t ^ Y_exp * fYC t
          constructor
          · simp
            push fun _ ↦ _
            grw [hf_eq]
          · simp [Approximates.nil, hY_tl]
      | cons X_exp X_coef X_tl =>
        obtain ⟨fXC, hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
        right
        cases Y with
        | nil =>
          apply Approximates_nil at hY_approx
          grw [hY_approx] at hf_eq
          simp
          use fXC
          simp [hX_coef]
          constructor
          · apply majorated_of_EventuallyEq hf_eq
            simpa
          simp [motive]
          use nil, X_tl
          simp
          use 0, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t
          constructor
          · simp
            push fun _ ↦ _
            grw [hf_eq]
            simp
          · simp [Approximates.nil, hX_tl]
        | cons Y_exp Y_coef Y_tl =>
          obtain ⟨fYC, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
          rw [add_cons_cons]
          split_ifs with h1 h2
          · simp
            use fXC
            simp [hX_coef]
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
              linarith
            simp only [motive]
            use X_tl, cons Y_exp Y_coef Y_tl, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t, fY
            simp [hX_tl, hY_approx]
            push fun _ ↦ _
            grw [hf_eq]
            convert EventuallyEq.refl _ _ using 1
            ext
            simp
            ring
          · simp
            use fYC
            simp [hY_coef]
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
              linarith
            simp only [motive]
            use cons X_exp X_coef X_tl, Y_tl, fX, fun t ↦ fY t - basis_hd t ^ Y_exp * fYC t
            simp [hY_tl, hX_approx]
            push fun _ ↦ _
            grw [hf_eq]
            convert EventuallyEq.refl _ _ using 1
            ext
            simp
            ring
          · have : X_exp = Y_exp := by linarith
            subst this
            simp
            use fXC + fYC
            constructorm* _ ∧ _
            · apply add_Approximates hX_coef hY_coef
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
            simp only [motive]
            use X_tl, Y_tl,
              fun t ↦ fX t - basis_hd t ^ X_exp * fXC t,
              fun t ↦ fY t - basis_hd t ^ X_exp * fYC t
            simp [hX_tl, hY_tl]
            push fun _ ↦ _
            grw [hf_eq]
            convert EventuallyEq.refl _ _ using 1
            ext
            simp
            ring

/-- `X - Y` is well-ordered when `X` and `Y` are well-ordered. -/
theorem sub_WellOrdered {basis : Basis} {X Y : PreMS basis}
    (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) : (X.sub Y).WellOrdered := by
  apply add_WellOrdered hX_wo
  apply neg_WellOrdered hY_wo

/-- If `X` approximates `fX` and `Y` approximates `fY`, then `X - Y` approximates `fX - fY`. -/
theorem sub_Approximates {basis : Basis} {X Y : PreMS basis} {fX fY : ℝ → ℝ}
    (hX_approx : X.Approximates fX) (hY_approx : Y.Approximates fY) :
    (X.sub Y).Approximates (fX - fY) := by
  apply add_Approximates hX_approx
  apply neg_Approximates hY_approx

end PreMS

end ComputeAsymptotics
