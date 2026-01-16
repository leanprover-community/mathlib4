/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Basic

/-!
# Addition for multiseries

-/


set_option linter.flexible false
set_option linter.style.longLine false

@[expose] public section

namespace ComputeAsymptotics

namespace PreMS

mutual

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
  | [] => ofReal (a.toReal + b.toReal)
  | List.cons basis_hd basis_tl =>
    mk (SeqMS.add (basis_hd := basis_hd) a.seq b.seq) (a.toFun + b.toFun)

noncomputable def SeqMS.add {basis_hd : ℝ → ℝ} {basis_tl : Basis} (X Y : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd basis_tl :=
  let T := (SeqMS basis_hd basis_tl) × (SeqMS basis_hd basis_tl)
  let g : T → Option (ℝ × PreMS basis_tl × T) := fun (X, Y) =>
    match X.destruct, Y.destruct with
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
  SeqMS.corec (basis_hd := basis_hd) g (X, Y)

end

/-- Subtraction for multiseries, defined as `a - b = a + (-b)`. -/
noncomputable def sub {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  a.add b.neg

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
noncomputable instance {basis : Basis} : Add (PreMS basis) where
  add := add

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
noncomputable instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Add (SeqMS basis_hd basis_tl) where
  add := SeqMS.add

theorem add_def {basis : Basis} {X Y : PreMS basis} :
    X + Y = add X Y := rfl

theorem SeqMS.add_def {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl} :
    X + Y = SeqMS.add X Y := rfl

@[simp]
theorem const_add_const (X Y : PreMS []) : X + Y = X.toReal + Y.toReal := by
  simp [add_def, add, ofReal, toReal]

@[simp]
theorem add_seq {basis_hd basis_tl} {X Y : PreMS (basis_hd :: basis_tl)} :
    (X + Y).seq = X.seq + Y.seq := by
  simp [add_def, SeqMS.add_def, add]

@[simp]
theorem add_toFun {basis : Basis} {X Y : PreMS basis} :
    (X + Y).toFun = X.toFun + Y.toFun := by
  rw [add_def]
  cases basis with
  | nil =>
    simp [add]
    ext
    rfl
  | cons basis_hd basis_tl =>
    simp [add]


-- theorems
open Filter Asymptotics

@[simp]
theorem SeqMS.nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} :
    nil + ms = ms := by
  let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
    X = nil + Y
  apply eq_of_bisim motive
  · simp only [motive]
  intro X Y ih
  simp only [motive] at ih
  subst ih
  cases Y with
  | nil => simp [SeqMS.add_def, SeqMS.add, corec_nil]
  | cons Y_exp Y_coef Y_tl =>
  · right
    use Y_exp, Y_coef, ?_, Y_tl
    constructor
    · simp only [add_def, add]
      rw [corec_cons]
      · simp
        rfl
    constructor
    · rfl
    simp only [motive, add_def, add]

@[simp]
private theorem SeqMS.zero_add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl} :
    0 + ms = ms := by
  simp [SeqMS.zero_def]

@[simp]
private theorem zero_add' {basis : Basis} {ms : PreMS basis} :
    0 + ms = ms := by
  cases basis with
  | nil => simp [toReal]
  | cons =>
    simp [ms_eq_ms_iff_mk_eq_mk, zero_def]
    rfl

-- copypaste from above
@[simp]
theorem SeqMS.add_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} :
    ms + nil = ms := by
  let motive (X Y : SeqMS basis_hd basis_tl) : Prop :=
    X = Y + nil
  apply eq_of_bisim motive
  · simp only [motive]
  intro X Y ih
  simp only [motive] at ih
  subst ih
  cases Y with
  | nil => simp [add_def, add, corec_nil]
  | cons Y_exp Y_coef Y_tl =>
    right
    use Y_exp, Y_coef, ?_, Y_tl
    constructor
    · simp only [add_def, add]
      rw [corec_cons]
      · simp
        rfl
    constructor
    · rfl
    simp [motive, add_def, SeqMS.add]

@[simp]
private theorem SeqMS.add_zero' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl} :
    ms + 0 = ms := by
  simp [zero_def]

@[simp]
private theorem add_zero' {basis : Basis} {ms : PreMS basis} :
    ms + 0 = ms := by
  cases basis with
  | nil => simp [toReal]
  | cons basis_hd basis_tl =>
    simp [ms_eq_ms_iff_mk_eq_mk, zero_def]
    rfl

/-- Auxillary definition. It is "unfolded" version of `add` without `corec` in body. In the
`add_unfold` we show that `add X Y = add' X Y`. -/
noncomputable def SeqMS.add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (X Y : SeqMS basis_hd basis_tl) :
    SeqMS basis_hd basis_tl :=
  match X.destruct, Y.destruct with
  | none, _ => Y
  | _, none => X
  | some (X_exp, X_coef, X_tl), some (Y_exp, Y_coef, Y_tl) =>
    if Y_exp < X_exp then
      cons X_exp X_coef (X_tl + Y)
    else if X_exp < Y_exp then
      cons Y_exp Y_coef (X + Y_tl)
    else
      cons X_exp (X_coef + Y_coef) (X_tl + Y_tl)

theorem SeqMS.add_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl} :
    X + Y = add' X Y := by
  cases X with
  | nil => simp [add']
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp [add']
  | cons Y_exp Y_coef Y_tl =>
  simp only [add_def, add, add', destruct_cons]
  split_ifs <;>
  (
    rw [corec_cons]
    simp only [destruct_cons]
    split_ifs
    rfl
  )

theorem SeqMS.add_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X_tl Y_tl : SeqMS basis_hd basis_tl} {X_exp Y_exp : ℝ} {X_coef Y_coef : PreMS basis_tl} :
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

/-- `((X_exp, X_coef) :: X_tl) + Y = (X_exp, X_coef) :: (X_tl + Y)` when `X_exp > Y.leadingExp`. -/
theorem SeqMS.add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp : ℝ} {X_coef : PreMS basis_tl}
    {X_tl Y : SeqMS basis_hd basis_tl} (h_lt : Y.leadingExp < X_exp) :
    (cons X_exp X_coef X_tl) + Y =
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
theorem SeqMS.add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_exp : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl X : SeqMS basis_hd basis_tl} (h_lt : X.leadingExp < Y_exp) :
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

mutual

/-- `add` commutes with `mulConst`. -/
@[simp]
theorem SeqMS.add_mulConst {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl} {c : ℝ} :
    (X + Y).mulConst c = (X.mulConst c) + Y.mulConst c := by
  let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
    ∃ (X Y : SeqMS basis_hd basis_tl), A = (X + Y).mulConst c ∧ B = X.mulConst c + Y.mulConst c
  apply SeqMS.eq_of_bisim_strong motive
  · use X, Y
  · rintro _ _ ⟨X, Y, rfl, rfl⟩
    cases X with
    | nil => simp
    | cons X_exp X_coef X_tl =>
    cases Y with
    | nil => simp
    | cons Y_exp Y_coef Y_tl =>
    right
    rw [SeqMS.add_cons_cons]
    simp [motive, SeqMS.add_cons_cons]
    split_ifs with h1 h2
    · simp
      refine ⟨_, _, rfl, ?_⟩
      simp
    · simp
      refine ⟨_, _, rfl, ?_⟩
      simp
    · have : X_exp = Y_exp := by linarith
      subst this
      simp
      refine ⟨_, _, rfl, ?_⟩
      rw [add_mulConst]
      simp

@[simp]
theorem add_mulConst {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
    (X + Y).mulConst c = (X.mulConst c) + (Y.mulConst c) := by
  cases basis with
  | nil =>
    simp [mulConst, add_def, add, ofReal, toReal]
    ring_nf
  | cons basis_hd basis_tl =>
    rw [ms_eq_ms_iff_mk_eq_mk]
    simp [SeqMS.add_mulConst (basis_hd := basis_hd) (basis_tl := basis_tl)]

end

mutual

private theorem SeqMS.add_comm' {basis_hd basis_tl} {X Y : SeqMS basis_hd basis_tl} :
    X + Y = Y + X := by
  let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
    ∃ (X Y : SeqMS basis_hd basis_tl), A = (X + Y) ∧ B = Y + X
  apply SeqMS.eq_of_bisim_strong motive
  · use X, Y
  rintro _ _ ⟨X, Y, rfl, rfl⟩
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl =>
  right
  rw [SeqMS.add_cons_cons, SeqMS.add_cons_cons]
  split_ifs with h1 h2
  · linarith
  · simp [motive]
    use ?_, ?_
  · simp [motive]
    use ?_, ?_
  · have : X_exp = Y_exp := by linarith
    subst this
    simp [motive]
    constructor
    · rw [add_comm']
    · use ?_, ?_

/-- Addition is commutative. -/
private theorem add_comm' {basis : Basis} {X Y : PreMS basis} :
    X + Y = Y + X := by
  cases basis with
  | nil =>
    simp
    ring_nf
  | cons basis_hd basis_tl =>
    rw [ms_eq_ms_iff_mk_eq_mk]
    simp [SeqMS.add_comm' (basis_hd := basis_hd) (basis_tl := basis_tl)]
    ring

end

mutual

private theorem SeqMS.add_assoc' {basis_hd basis_tl} {X Y Z : SeqMS basis_hd basis_tl} :
    X + (Y + Z) = (X + Y) + Z := by
  let motive (A B : SeqMS basis_hd basis_tl) : Prop :=
    ∃ (X Y Z : SeqMS basis_hd basis_tl), A = X + (Y + Z) ∧ B = (X + Y) + Z
  apply SeqMS.eq_of_bisim_strong motive
  · use X, Y, Z
  rintro _ _ ⟨X, Y, Z, rfl, rfl⟩
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
  have h_XY : (SeqMS.cons X_exp X_coef X_tl) + (SeqMS.cons Y_exp Y_coef Y_tl) = ?_ := by
    simp only [SeqMS.add_unfold]
    simp [SeqMS.add']
    rfl
  have h_YZ : (SeqMS.cons Y_exp Y_coef Y_tl) + (SeqMS.cons Z_exp Z_coef Z_tl) = ?_ := by
    simp only [SeqMS.add_unfold]
    simp [SeqMS.add']
    rfl
  split_ifs at h_XY h_YZ <;>
  (
    rw [h_XY, h_YZ]
    simp_rw [SeqMS.add_cons_cons]
    split_ifs <;> (try exfalso; linarith) <;>
    (
      simp only [add_assoc' (basis := basis_tl), SeqMS.cons_eq_cons, exists_and_left, ↓existsAndEq,
        and_true, and_self_left, exists_and_right, true_and]
      use ?_, ?_, ?_
      try (
        simp [← h_XY, ← h_YZ]
        · constructor <;> rfl
      )
    )
  )

/-- Addition is associative. -/
private theorem add_assoc' {basis : Basis} {X Y Z : PreMS basis} :
    X + (Y + Z) = (X + Y) + Z := by
  cases basis with
  | nil =>
    simp [toReal]
    ring_nf
  | cons basis_hd basis_tl =>
    rw [ms_eq_ms_iff_mk_eq_mk]
    simp [SeqMS.add_assoc' (basis_hd := basis_hd) (basis_tl := basis_tl)]
    ring

end

/-- This instance is necessary for using `abel` tactic later. -/
noncomputable instance (basis_hd basis_tl) : AddCommMonoid (SeqMS basis_hd basis_tl) where
  zero_add := by apply SeqMS.zero_add'
  add_zero := by apply SeqMS.add_zero'
  add_assoc _ _ _ := by apply SeqMS.add_assoc'.symm
  add_comm _ _ := by apply SeqMS.add_comm'
  nsmul := nsmulRec

noncomputable instance (basis : Basis) : AddCommMonoid (PreMS basis) where
  zero_add := by apply zero_add'
  add_zero := by apply add_zero'
  add_assoc _ _ _ := by apply add_assoc'.symm
  add_comm _ _ := by apply add_comm'
  nsmul := nsmulRec

@[simp]
theorem SeqMS.add_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : SeqMS basis_hd basis_tl} :
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

-- @[simp]
-- theorem add_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
--     (X + Y).leadingExp = X.leadingExp ⊔ Y.leadingExp := by
--   simp

mutual

theorem SeqMS.add_WellOrdered {basis_hd basis_tl} {X Y : SeqMS basis_hd basis_tl}
    (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) : (X + Y).WellOrdered := by
  let motive : (SeqMS basis_hd basis_tl) → Prop := fun ms =>
    ∃ (X Y : SeqMS basis_hd basis_tl),
      ms = X + Y ∧ X.WellOrdered ∧ Y.WellOrdered
  apply SeqMS.WellOrdered.coind motive
  · use X, Y
  intro exp coef tl ⟨X, Y, h_eq, hX_wo, hY_wo⟩
  cases X with
  | nil =>
    simp only [SeqMS.nil_add] at h_eq
    subst h_eq
    obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons hY_wo
    simp [motive, h_coef_wo, h_comp]
    use .nil, tl
    simp [SeqMS.WellOrdered.nil, h_tl_wo]
  | cons X_exp X_coef X_tl =>
    obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
    cases Y with
    | nil =>
      simp at h_eq
      simp only [h_eq, hX_coef_wo, hX_comp, true_and, motive]
      use .nil, X_tl
      simp [SeqMS.WellOrdered.nil, hX_tl_wo]
    | cons Y_exp Y_coef Y_tl =>
      obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
      rw [SeqMS.add_cons_cons] at h_eq
      split_ifs at h_eq with h1 h2 <;> simp at h_eq;
      · simp [motive, h_eq, hX_coef_wo, hX_comp, h1]
        use ?_, ?_
      · simp [motive, h_eq, hY_coef_wo, hY_comp, h2]
        use ?_, ?_
      · have h_exp : X_exp = Y_exp := by linarith
        subst h_exp
        simp [motive, h_eq, hX_comp, hY_comp]
        constructor
        · apply add_WellOrdered <;> assumption
        · use ?_, ?_

/-- `X + Y` is well-ordered when `X` and `Y` are well-ordered. -/
theorem add_WellOrdered {basis : Basis} {X Y : PreMS basis}
    (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) : (X + Y).WellOrdered := by
  cases basis with
  | nil =>
    constructor
  | cons basis_hd basis_tl =>
    simp at hX_wo hY_wo ⊢
    apply SeqMS.add_WellOrdered hX_wo hY_wo

end

/-- If `X` approximates `fX` and `Y` approximates `fY`, then `X + Y` approximates `fX + fY`. -/
theorem add_Approximates {basis : Basis} {X Y : PreMS basis}
    (hX_approx : X.Approximates) (hY_approx : Y.Approximates) :
    (X + Y).Approximates := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
  let motive (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ (X Y : PreMS (basis_hd :: basis_tl)),
      ms = X + Y ∧ X.Approximates ∧ Y.Approximates
  apply Approximates.coind motive
  · use X, Y
  rintro ms ⟨X, Y, rfl, hX_approx, hY_approx⟩
  cases X with
  | nil fX =>
    apply Approximates_nil at hX_approx
    cases Y with
    | nil fY =>
      apply Approximates_nil at hY_approx
      left
      simp
      grw [hX_approx, hY_approx]
      simp
    | cons Y_exp Y_coef Y_tl fY =>
      obtain ⟨hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
      right
      simp [hY_coef]
      constructor
      · apply majorated_of_EventuallyEq _ hY_maj
        grw [hX_approx]
        simp
      simp [motive]
      use mk .nil fX, mk Y_tl (fY - basis_hd ^ Y_exp * Y_coef.toFun)
      simp [hX_approx, hY_tl]
      ext t
      simp
      ring
  | cons X_exp X_coef X_tl fX =>
    obtain ⟨hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
    right
    cases Y with
    | nil fY =>
      apply Approximates_nil at hY_approx
      simp [hX_coef]
      constructor
      · apply majorated_of_EventuallyEq _ hX_maj
        grw [hY_approx]
        simp
      simp [motive]
      use mk X_tl (fX - basis_hd ^ X_exp * X_coef.toFun), mk .nil fY
      simp [hY_approx, hX_tl]
      ext t
      simp
      ring
    | cons Y_exp Y_coef Y_tl fY =>
      obtain ⟨hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
      simp
      rw [SeqMS.add_cons_cons]
      split_ifs with h1 h2
      · simp [hX_coef, add_majorated' hX_maj hY_maj (by linarith) (by linarith)]
        refine ⟨_, _, ?_, hX_tl, hY_approx⟩
        simp
        ext t
        simp
        ring
      · simp [hY_coef, add_majorated' hX_maj hY_maj (by linarith) (by linarith)]
        refine ⟨_, _, ?_, hX_approx, hY_tl⟩
        simp
        ext t
        simp
        ring
      · have : X_exp = Y_exp := by linarith
        subst this
        simp
        constructorm* _ ∧ _
        · apply add_Approximates hX_coef hY_coef
        · apply add_majorated' hX_maj hY_maj (by linarith) (by linarith)
        refine ⟨_, _, ?_, hX_tl, hY_tl⟩
        simp
        ext t
        simp
        ring

/-- `X - Y` is well-ordered when `X` and `Y` are well-ordered. -/
theorem sub_WellOrdered {basis : Basis} {X Y : PreMS basis}
    (hX_wo : X.WellOrdered) (hY_wo : Y.WellOrdered) : (X.sub Y).WellOrdered := by
  apply add_WellOrdered hX_wo
  apply neg_WellOrdered hY_wo

/-- If `X` approximates `fX` and `Y` approximates `fY`, then `X - Y` approximates `fX - fY`. -/
theorem sub_Approximates {basis : Basis} {X Y : PreMS basis}
    (hX_approx : X.Approximates) (hY_approx : Y.Approximates) :
    (X.sub Y).Approximates := by
  apply add_Approximates hX_approx
  apply neg_Approximates hY_approx

instance {basis_hd basis_tl} :
    SeqMS.FriendOperationClass (SeqMS.add (basis_hd := basis_hd) (basis_tl := basis_tl)) := by
  apply SeqMS.FriendOperationClass.mk'
  intro c
  let motive (op : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl) : Prop :=
    ∃ (c : SeqMS basis_hd basis_tl), op = SeqMS.add c
  apply SeqMS.FriendOperation.coind_comp_friend_right motive
  · use c
  rintro _ ⟨c, rfl⟩
  simp only [← SeqMS.add_def]
  cases c with
  | nil =>
    use fun hd? ↦ match hd? with
    | none => none
    | some (exp, coef) => some (exp, coef, ⟨id, SeqMS.FriendOperation.id⟩, ⟨fun x ↦ .nil + x, _, rfl⟩)
    intro x
    cases x <;> simp
  | cons c_exp c_coef c_tl =>
    use fun hd? ↦ match hd? with
    | none => some (c_exp, c_coef, ⟨fun _ ↦ c_tl, SeqMS.FriendOperation.const⟩, ⟨fun x ↦ .nil + x, _, rfl⟩)
    | some (exp, coef) =>
      if exp < c_exp then
        some (c_exp, c_coef, ⟨.cons exp coef, SeqMS.FriendOperation.cons _ _⟩,
          ⟨fun x ↦ c_tl + x, _, rfl⟩)
      else if c_exp < exp then
        some (exp, coef, ⟨id, SeqMS.FriendOperation.id⟩, ⟨fun x ↦ (.cons c_exp c_coef c_tl) + x, _, rfl⟩)
      else
        some (exp, c_coef + coef, ⟨id, SeqMS.FriendOperation.id⟩, ⟨fun x ↦ c_tl + x, _, rfl⟩)
    intro x
    cases x with
    | nil => simp
    | cons x_exp x_coef x_tl =>
      simp [SeqMS.add_cons_cons]
      split_ifs with h1 h2
      · simp
      · simp
      · simp
        linarith

theorem SeqMS.eq_of_bisim_add {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (c x' y' : SeqMS basis_hd basis_tl),
      x = .cons exp coef (c + x') ∧ y = .cons exp coef (c + y') ∧ motive x' y') :
    x = y :=
  SeqMS.eq_of_bisim_friend (op := SeqMS.add (basis_hd := basis_hd) (basis_tl := basis_tl)) motive base step

theorem SeqMS.eq_of_bisim_add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → SeqMS basis_hd basis_tl → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ (c x' y' : SeqMS basis_hd basis_tl),
      x = c + x' ∧ y = c + y' ∧ x'.leadingExp < c.leadingExp ∧ y'.leadingExp < c.leadingExp ∧
      motive x' y') :
    x = y := by
  apply eq_of_bisim_add motive
  · exact base
  intro x y ih
  obtain step | ⟨c, x', y', rfl, rfl, hx, hy, h_next⟩ := step x y ih
  · simp [step]
  cases c with
  | nil => simp at hx
  | cons c_exp c_coef c_tl =>
  cases x' with
  | nil =>
    cases y' with
    | nil => simp
    | cons y_exp y_coef y_tl =>
      right
      simp only [SeqMS.add_nil, SeqMS.cons_eq_cons, exists_and_left, ↓existsAndEq, true_and]
      use c_tl, .nil
      simp only [SeqMS.add_nil, true_and]
      use .cons y_exp y_coef y_tl
      simpa [SeqMS.add_cons_left hy]
  | cons x_exp x_coef x_tl =>
    cases y' with
    | nil =>
      right
      simp only [SeqMS.add_nil, SeqMS.cons_eq_cons, exists_and_left, ↓existsAndEq, true_and]
      use c_tl, .cons x_exp x_coef x_tl
      simp only [SeqMS.add_cons_left hx, true_and]
      use .nil
      simpa
    | cons y_exp y_coef y_tl =>
      right
      simp only [SeqMS.add_cons_left hx, SeqMS.cons_eq_cons, SeqMS.add_cons_left hy, exists_and_left, ↓existsAndEq,
        true_and]
      use c_tl, .cons x_exp x_coef x_tl
      simp only [true_and]
      use .cons y_exp y_coef y_tl

theorem SeqMS.WellOrdered.add_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → Prop) (h_base : motive ms)
    (h_step :
      ∀ (exp : ℝ) (coef : PreMS basis_tl) (tl : SeqMS basis_hd basis_tl),
        motive (.cons exp coef tl) → coef.WellOrdered ∧ tl.leadingExp < ↑exp ∧
        ∃ A B, tl = A + B ∧ A.WellOrdered ∧ motive B) :
    ms.WellOrdered :=
  SeqMS.WellOrdered.coind_friend' SeqMS.add motive SeqMS.WellOrdered
    (by apply SeqMS.add_WellOrdered) h_base h_step

theorem SeqMS.WellOrdered.add_coind' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl}
    (motive : SeqMS basis_hd basis_tl → Prop) (h_base : motive ms)
    (h_step :
      ∀ ms, motive ms → (ms = .nil) ∨ ∃ A B, ms = A + B ∧ A.WellOrdered ∧
      B.leadingExp < A.leadingExp ∧ motive B) :
    ms.WellOrdered := by
  apply WellOrdered.add_coind motive h_base
  intro exp coef tl ih
  specialize h_step _ ih
  simp only [cons_ne_nil, false_or] at h_step
  obtain ⟨A, B, h_eq, hA_wo, hBA, hB⟩ := h_step
  cases A with
  | nil => simp at hBA
  | cons A_exp A_coef A_tl =>
  obtain ⟨hA_coef_wo, hA_comp, hA_tl⟩ := WellOrdered_cons hA_wo
  cases B with
  | nil =>
    simp only [add_nil, cons_eq_cons] at h_eq
    simp only [h_eq, hA_coef_wo, hA_comp, true_and]
    use A_tl, .nil
    simp [hA_tl, hB]
  | cons B_exp B_coef B_tl =>
  simp only [add_cons_left hBA, cons_eq_cons] at h_eq
  simp only [leadingExp_cons, WithBot.coe_lt_coe] at hBA
  simp only [h_eq, hA_coef_wo, add_leadingExp, leadingExp_cons, sup_lt_iff, hA_comp,
    WithBot.coe_lt_coe, hBA, and_self, true_and]
  use A_tl, .cons B_exp B_coef B_tl

theorem Approximates.add_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → Prop) (h_base : motive ms)
    (h_step :
      ∀ (ms : PreMS (basis_hd :: basis_tl)),
        motive ms →
        ms.seq = .nil ∧ ms.toFun =ᶠ[atTop] 0 ∨
        ∃ exp coef tl,
          ms.seq = .cons exp coef tl ∧ coef.Approximates ∧ majorated ms.toFun basis_hd exp ∧
          ∃ (A : PreMS (basis_hd :: basis_tl)) (B : SeqMS basis_hd basis_tl),
            tl = A.seq + B ∧ A.Approximates ∧
            motive (mk (basis_hd := basis_hd) B (ms.toFun - basis_hd ^ exp * coef.toFun - A.toFun))) :
    ms.Approximates := by
  let motive' (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ A B, ms ≈ A + B ∧ A.Approximates ∧ motive B
  apply Approximates.coind motive'
  · use mk .nil 0, ms
    simp [h_base]
  rintro ms ⟨A, B, ⟨h_seq_eq, hf_eq⟩, hA, hB⟩
  simp [motive']
  cases A with
  | nil fA =>
    simp at hf_eq
    apply Approximates_nil at hA
    specialize h_step _ hB
    obtain ⟨hB_seq, hB_fun⟩ | ⟨exp, coef, tl, hB_seq, h_coef, h_maj, X, Y, h_tl, hX, hY⟩ := h_step
    · left
      simp [h_seq_eq, hB_seq]
      grw [hf_eq, hA, hB_fun]
      simp
    right
    use exp, coef, X, mk Y (B.toFun - basis_hd ^ exp * coef.toFun - X.toFun)
    simp [h_seq_eq, hB_seq, h_tl, h_coef, hX, hY]
    constructor
    · apply majorated_of_EventuallyEq _ h_maj
      grw [hf_eq, hA]
      simp
    grw [hf_eq, hA]
    simp
  | cons A_exp A_coef A_tl fA =>
    right
    obtain ⟨hA_coef, hA_maj, hA_tl⟩ := Approximates_cons hA
    specialize h_step _ hB
    simp at hf_eq
    obtain ⟨hB_seq, hB_fun⟩ | ⟨B_exp, B_coef, B_tl, hB_seq, hB_coef, hB_maj, X, Y, h_tl, hX, hY⟩ := h_step
    · use A_exp, A_coef, mk A_tl (fA - basis_hd ^ A_exp * A_coef.toFun), mk .nil B.toFun
      simp [h_seq_eq, hB_seq, hA_coef, hA_tl]
      constructorm* _ ∧ _
      · apply majorated_of_EventuallyEq _ hA_maj
        grw [hf_eq, hB_fun]
        simp
      · grw [hf_eq, hB_fun]
        simp
      · convert hB
        simp [hB_seq]
    -- simp [hB_seq, SeqMS.add_cons_cons] at h_seq_eq
    simp [h_seq_eq, hB_seq, SeqMS.add_cons_cons]
    split_ifs with h1 h2
    · simp
      use mk A_tl (fA - basis_hd ^ A_exp * A_coef.toFun), B
      simp [hA_coef, hB_seq, hA_tl, hB]
      constructor
      · apply majorated_of_EventuallyEq hf_eq
        apply add_majorated' hA_maj hB_maj (by rfl) (by linarith)
      grw [hf_eq]
      apply EventuallyEq.of_eq
      ext t
      simp
      ring
    · simp
      use (mk (.cons A_exp A_coef A_tl) fA) + X, mk Y (B.toFun - basis_hd ^ B_exp * B_coef.toFun - X.toFun)
      simp [h_tl, add_assoc, hB_coef, hY, add_Approximates hA hX]
      constructor
      · apply majorated_of_EventuallyEq hf_eq
        apply add_majorated' hA_maj hB_maj (by linarith) (by rfl)
      · grw [hf_eq]
        apply EventuallyEq.of_eq
        ext t
        simp
        ring
    · have : A_exp = B_exp := by linarith
      subst this
      simp
      use mk A_tl (fA - basis_hd ^ A_exp * A_coef.toFun) + X,
        mk Y (B.toFun - basis_hd ^ A_exp * B_coef.toFun - X.toFun)
      simp [h_tl, add_assoc, hY]
      constructorm* _ ∧ _
      · apply add_Approximates hA_coef hB_coef
      · apply majorated_of_EventuallyEq hf_eq
        apply add_majorated' hA_maj hB_maj (by rfl) (by rfl)
      · grw [hf_eq]
        convert EventuallyEq.refl _ _ using 1
        ext t
        simp
        ring
      · apply add_Approximates hA_tl hX

end PreMS

end ComputeAsymptotics
