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

@[expose] public section

namespace ComputeAsymptotics

namespace PreMS

open Stream'

-- noncomputable def Seq.add {basis_tl : Basis} (X Y : Seq (ℝ × PreMS basis_tl)) : Seq (ℝ × PreMS basis_tl) :=
--   let T := (Seq (ℝ × PreMS basis_tl)) × (Seq (ℝ × PreMS basis_tl))
--   let g : T → Option ((ℝ × PreMS basis_tl) × T) := fun (X, Y) =>
--     match X.destruct, Y.destruct with
--     | none, none => none
--     | none, some ((Y_exp, Y_coef), Y_tl) => some ((Y_exp, Y_coef), (.nil, Y_tl))
--     | some ((X_exp, X_coef), X_tl), none => some ((X_exp, X_coef), (X_tl, .nil))
--     | some ((X_exp, X_coef), X_tl), some ((Y_exp, Y_coef), Y_tl) =>
--       if Y_exp < X_exp then
--         some ((X_exp, X_coef), (X_tl, Y))
--       else if X_exp < Y_exp then
--         some ((Y_exp, Y_coef), (X, Y_tl))
--       else
--         some ((X_exp, Seq.add X_coef Y_coef), (X_tl, Y_tl))
--   corec g (a, b)

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
  | List.cons basis_hd basis_tl =>
    let T := (Seq (ℝ × PreMS basis_tl)) × (Seq (ℝ × PreMS basis_tl))
    let g : T → Option ((ℝ × PreMS basis_tl) × T) := fun (X, Y) =>
      match X.destruct, Y.destruct with
      | none, none => none
      | none, some ((Y_exp, Y_coef), Y_tl) => some ((Y_exp, Y_coef), (.nil, Y_tl))
      | some ((X_exp, X_coef), X_tl), none => some ((X_exp, X_coef), (X_tl, .nil))
      | some ((X_exp, X_coef), X_tl), some ((Y_exp, Y_coef), Y_tl) =>
        if Y_exp < X_exp then
          some ((X_exp, X_coef), (X_tl, Y))
        else if X_exp < Y_exp then
          some ((Y_exp, Y_coef), (X, Y_tl))
        else
          some ((X_exp, X_coef.add Y_coef), (X_tl, Y_tl))
    mk (Seq.corec g (a.seq, b.seq)) (a.toFun + b.toFun)

-- noncomputable def Seq.add {basis_tl : Basis} (X Y : Seq (ℝ × PreMS basis_tl)) : Seq (ℝ × PreMS basis_tl) :=
--   (PreMS.add (mk (basis_hd := 0) X 0) (mk Y 0)).seq

/-- Subtraction for multiseries, defined as `a - b = a + (-b)`. -/
noncomputable def sub {basis : Basis} (a b : PreMS basis) : PreMS basis :=
  a.add b.neg

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
noncomputable instance instAdd {basis : Basis} : Add (PreMS basis) where
  add := add

theorem add_def {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    X + Y = add X Y := rfl

-- @[simp]
-- theorem add_seq {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
--     (X + Y).seq = Seq.add X.seq Y.seq := rfl

@[simp]
theorem add_toFun {basis : Basis} {X Y : PreMS basis} : (X + Y).toFun = X.toFun + Y.toFun := by
  cases basis <;> rfl

@[simp]
theorem add_replaceFun_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ} :
    X.replaceFun f + Y = (X + Y).replaceFun (f + Y.toFun) :=
  rfl

@[simp]
theorem add_replaceFun_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ} :
    X + Y.replaceFun f = (X + Y).replaceFun (X.toFun + f) :=
  rfl

@[simp]
theorem const_add_const (X Y : PreMS []) : X + Y = X.toReal + Y.toReal :=
  rfl

-- theorems
open Filter Asymptotics

-- @[simp]
-- theorem nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ} :
--     mk .nil f + ms = ms.replaceFun (f + ms.toFun) := by
--   rw [ms_eq_ms_iff_mk_eq_mk]
--   simp
--   let motive (X Y: Seq (ℝ × PreMS basis_tl)) :=
--     X = (mk (basis_hd := basis_hd) .nil f + (mk (basis_hd := basis_hd) Y 0)).seq
--   apply Seq.eq_of_bisim' motive rfl
--   rintro X Y rfl
--   cases Y with
--   | nil => simp [add_def, add, Seq.corec_nil]
--   | cons Y_hd Y_tl =>
--   obtain ⟨Y_exp, Y_coef⟩ := Y_hd
--   right
--   simp [add_def, add]
--   rw [Seq.corec_cons rfl]
--   simp [motive]
--   rfl

-- theorem Seq.nil_add {basis_tl : Basis} {Y : Seq (ℝ × PreMS basis_tl)} :
--     Seq.add .nil Y = Y.replaceFun (0 + Y.toFun) := by
--   rw [ms_eq_ms_iff_mk_eq_mk]
--   simp
--   let motive (X Y: Seq (ℝ × PreMS basis_tl)) :=
--     X = (mk (basis_hd := 0) .nil 0 + (mk (basis_hd := 0) Y 0)).seq
--   apply Seq.eq_of_bisim' motive rfl
--   rintro X Y rfl
--   cases Y with

@[simp]
theorem nil_add {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ} :
    mk .nil f + ms = ms.replaceFun (f + ms.toFun) := by
  rw [ms_eq_ms_iff_mk_eq_mk]
  simp
  let motive (X Y: Seq (ℝ × PreMS basis_tl)) :=
    X = (mk (basis_hd := basis_hd) .nil f + (mk (basis_hd := basis_hd) Y 0)).seq
  apply Seq.eq_of_bisim' motive rfl
  rintro X Y rfl
  cases Y with
  | nil => simp [add_def, add, Seq.corec_nil]
  | cons Y_hd Y_tl =>
  obtain ⟨Y_exp, Y_coef⟩ := Y_hd
  right
  simp [add_def, add]
  rw [Seq.corec_cons rfl]
  simp [motive]
  rfl

@[simp]
private theorem zero_add' {basis : Basis} {ms : PreMS basis} :
    0 + ms = ms := by
  cases basis with
  | nil => simp [toReal]
  | cons =>
    simp [zero_def, ms_eq_ms_iff_mk_eq_mk]
    rfl

-- copypaste from above
@[simp]
theorem add_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ} :
    ms + mk .nil f = ms.replaceFun (ms.toFun + f) := by
  rw [ms_eq_ms_iff_mk_eq_mk]
  simp
  let motive (X Y : Seq (ℝ × PreMS basis_tl)) :=
    X = (mk (basis_hd := basis_hd) Y 0 + mk .nil f).seq
  apply Seq.eq_of_bisim' motive rfl
  rintro X Y rfl
  cases Y with
  | nil => simp [add_def, add, Seq.corec_nil]
  | cons Y_hd Y_tl =>
    obtain ⟨Y_exp, Y_coef⟩ := Y_hd
    right
    simp [add_def, add]
    rw [Seq.corec_cons rfl]
    simp [motive]
    rfl

@[simp]
private theorem add_zero' {basis : Basis} {ms : PreMS basis} :
    ms + 0 = ms := by
  cases basis with
  | nil => simp [toReal]
  | cons =>
    simp [zero_def, ms_eq_ms_iff_mk_eq_mk]
    rfl

/-- Auxillary definition. It is "unfolded" version of `add` without `corec` in body. In the
`add_unfold` we show that `add X Y = add' X Y`. -/
noncomputable def add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (X Y : PreMS (basis_hd :: basis_tl)) :
    (PreMS (basis_hd :: basis_tl)) :=
  let s := match X.seq.destruct, Y.seq.destruct with
    | none, _ => Y.seq
    | _, none => X.seq
    | some ((X_exp, X_coef), X_tl), some ((Y_exp, Y_coef), Y_tl) =>
      if Y_exp < X_exp then
        .cons (X_exp, X_coef) (mk X_tl 0 + Y).seq
      else if X_exp < Y_exp then
        .cons (Y_exp, Y_coef) (X + mk Y_tl 0).seq
      else
        .cons (X_exp, X_coef + Y_coef) (mk (basis_hd := basis_hd) X_tl 0 + mk Y_tl 0).seq
  mk s (X.toFun + Y.toFun)

theorem add_unfold {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X Y : PreMS (basis_hd :: basis_tl)} :
    X + Y = add' X Y := by
  cases X with
  | nil => simp [add']
  | cons X_exp X_coef X_tl fX =>
  cases Y with
  | nil => simp [add']
  | cons Y_exp Y_coef Y_tl fY =>
  simp [add_def, add, add']
  split_ifs <;>
  (
    rw [Seq.corec_cons]
    simp only [Seq.destruct_cons]
    split_ifs
    rfl
  )

/-- `((X_exp, X_coef) :: X_tl) + Y = (X_exp, X_coef) :: (X_tl + Y)` when `X_exp > Y.leadingExp`. -/
theorem add_cons_left {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X_exp : ℝ} {X_coef : PreMS basis_tl}
    {X_tl : Seq (ℝ × PreMS basis_tl)} {fX : ℝ → ℝ}
    {Y : PreMS (basis_hd :: basis_tl)} (h_lt : Y.leadingExp < X_exp) :
    (mk (.cons (X_exp, X_coef) X_tl) fX) + Y =
    mk (.cons (X_exp, X_coef) (mk X_tl 0 + Y).seq) (fX + Y.toFun) := by
  rw [add_unfold, add']
  cases Y with
  | nil => simp
  | cons Y_exp Y_coef Y_tl =>
    simp at h_lt
    simp [h_lt]

/-- `X + ((Y_exp, Y_coef) :: Y_tl) = (Y_exp, Y_coef) :: (X + Y_tl)` when `Y_exp > X.leadingExp`. -/
theorem add_cons_right {basis_hd : ℝ → ℝ} {basis_tl : Basis} {Y_exp : ℝ} {Y_coef : PreMS basis_tl}
    {Y_tl : Seq (ℝ × PreMS basis_tl)} {fY : ℝ → ℝ}
    {X : PreMS (basis_hd :: basis_tl)} (h_lt : X.leadingExp < Y_exp) :
    X + (mk (.cons (Y_exp, Y_coef) Y_tl) fY) = mk (.cons (Y_exp, Y_coef) (X + mk Y_tl 0).seq) (X.toFun + fY) := by
  rw [add_unfold, add']
  cases X with
  | nil => simp
  | cons X_exp X_coef X_tl =>
    simp at h_lt
    simp [h_lt]
    intro
    linarith

theorem add_cons_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {X_tl Y_tl : Seq (ℝ × PreMS basis_tl)} {X_exp Y_exp : ℝ} {X_coef Y_coef : PreMS basis_tl}
    (fX fY : ℝ → ℝ) :
    (mk (basis_hd := basis_hd) (.cons (X_exp, X_coef) X_tl) fX) + (mk (basis_hd := basis_hd) (.cons (Y_exp, Y_coef) Y_tl) fY) =
    if Y_exp < X_exp then
      mk (.cons (X_exp, X_coef) ((mk (basis_hd := basis_hd) X_tl 0) + (mk (.cons (Y_exp, Y_coef) Y_tl) fY)).seq) (fX + fY)
    else if X_exp < Y_exp then
      mk (.cons (Y_exp, Y_coef) (mk (basis_hd := basis_hd) (.cons (X_exp, X_coef) X_tl) fX + mk Y_tl 0).seq) (fX + fY)
    else
      mk (.cons (X_exp, X_coef + Y_coef) ((mk (basis_hd := basis_hd) X_tl 0) + (mk Y_tl 0)).seq) (fX + fY) := by
  rw [add_unfold, add']
  simp
  split_ifs <;> simp

/-- `add` commutes with `mulConst`. -/
@[simp]
theorem add_mulConst {basis : Basis} {X Y : PreMS basis} {c : ℝ} :
    (X + Y).mulConst c = (X.mulConst c) + Y.mulConst c := by
  cases basis with
  | nil =>
    simp only [mulConst, ofReal, toReal]
    ring_nf
  | cons basis_hd basis_tl =>
    rw [ms_eq_ms_iff_mk_eq_mk]
    simp
    let motive (A B : Seq (ℝ × PreMS basis_tl)) : Prop :=
      ∃ (X Y : PreMS (basis_hd :: basis_tl)),
        A = ((X + Y).mulConst c).seq ∧
        B = (X.mulConst c + Y.mulConst c).seq
    apply Seq.eq_of_bisim_strong motive
    · use X, Y
    rintro _ _ ⟨X, Y, rfl, rfl⟩
    cases X with
    | nil => simp
    | cons X_exp X_coef X_tl fX =>
    cases Y with
    | nil => simp
    | cons Y_exp Y_coef Y_tl fY =>
    right
    rw [add_cons_cons]
    split_ifs with h1 h2
    · simp [add_cons_cons, h1]
      refine ⟨_, _, rfl, ?_⟩
      simp
      rfl
    · simp [add_cons_cons, h1, h2]
      refine ⟨_, _, rfl, ?_⟩
      simp
      rfl
    · have : X_exp = Y_exp := by linarith
      subst this
      simp [add_cons_cons, add_mulConst]
      refine ⟨_, _, rfl, rfl⟩

/-- Addition is commutative. -/
private theorem add_comm' {basis : Basis} {X Y : PreMS basis} :
    X + Y = Y + X := by
  cases basis with
  | nil =>
    simp
    ring_nf
  | cons basis_hd basis_tl =>
  rw [ms_eq_ms_iff_mk_eq_mk]
  simp
  refine ⟨?_, by ring⟩
  let motive (A B : Seq (ℝ × PreMS basis_tl)) : Prop :=
    ∃ (X Y : PreMS (basis_hd :: basis_tl)), A = (X + Y).seq ∧ B = (Y + X).seq
  apply Seq.eq_of_bisim_strong motive
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
    · simp
      exact ⟨_, _, rfl, rfl⟩
    · simp
      exact ⟨_, _, rfl, rfl⟩
    · have : X_exp = Y_exp := by linarith
      subst this
      simp [add_comm' (basis := basis_tl)]
      exact ⟨mk X_tl 0, mk Y_tl 0, rfl, rfl⟩

/-- Addition is associative. -/
private theorem add_assoc' {basis : Basis} {X Y Z : PreMS basis} :
    X + (Y + Z) = (X + Y) + Z := by
  cases basis with
  | nil =>
    simp [ofReal, toReal]
    ring_nf
  | cons basis_hd basis_tl =>
  rw [ms_eq_ms_iff_mk_eq_mk]
  simp
  refine ⟨?_, by ring⟩
  let motive (A B : Seq (ℝ × PreMS basis_tl)) : Prop :=
    ∃ (X Y Z : PreMS (basis_hd :: basis_tl)), A = (X + (Y + Z)).seq ∧ B = ((X + Y) + Z).seq
  apply Seq.eq_of_bisim_strong motive
  · simp only [motive]
    use X, Y, Z
  · rintro _ _ ⟨X, Y, Z, rfl, rfl⟩
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
        simp only [↓existsAndEq, cons_eq_cons, and_self, and_true, true_and]
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
        simp only [nil_add] at h_eq
        subst h_eq
        obtain ⟨h_coef_wo, h_comp, h_tl_wo⟩ := WellOrdered_cons hY_wo
        simp only [h_coef_wo, h_comp, true_and, motive]
        use nil, tl
        simp [WellOrdered.nil, h_tl_wo]
      | cons X_exp X_coef X_tl =>
        obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
        cases Y with
        | nil =>
          simp at h_eq
          simp only [h_eq, hX_coef_wo, hX_comp, true_and, motive]
          use nil, X_tl
          simp [WellOrdered.nil, hX_tl_wo]
        | cons Y_exp Y_coef Y_tl =>
          obtain ⟨hY_coef_wo, hY_comp, hY_tl_wo⟩ := WellOrdered_cons hY_wo
          rw [add_cons_cons] at h_eq
          split_ifs at h_eq with h1 h2 <;> simp at h_eq;
          · simp only [h_eq, hX_coef_wo, add_leadingExp, leadingExp_cons, sup_lt_iff, hX_comp,
              WithBot.coe_lt_coe, h1, and_self, true_and, motive]
            use ?_, ?_
          · simp only [h_eq, hY_coef_wo, add_leadingExp, leadingExp_cons, sup_lt_iff,
              WithBot.coe_lt_coe, h2, hY_comp, and_self, true_and, motive]
            use ?_, ?_
          · have h_exp : X_exp = Y_exp := by linarith
            subst h_exp
            simp only [h_eq, add_leadingExp, sup_lt_iff, hX_comp, hY_comp, and_self, true_and,
              motive]
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
          simp only [add_nil, true_and]
          grw [hf_eq, hX_approx, hY_approx]
          simp
        | cons Y_exp Y_coef Y_tl =>
          obtain ⟨fYC, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
          right
          grw [hX_approx] at hf_eq
          simp only [zero_add] at hf_eq
          simp only [nil_add, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
            exists_eq_left']
          use fYC
          simp only [hY_coef, true_and]
          constructor
          · apply majorated_of_EventuallyEq hf_eq
            assumption
          simp only [exists_and_left, motive]
          use nil, Y_tl
          simp only [nil_add, true_and]
          use 0, fun t ↦ fY t - basis_hd t ^ Y_exp * fYC t
          constructor
          · simp only [zero_add]
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
          simp only [add_nil, cons_eq_cons, exists_and_left, ↓existsAndEq, and_true,
            exists_eq_left']
          use fXC
          simp only [hX_coef, true_and]
          constructor
          · apply majorated_of_EventuallyEq hf_eq
            simpa
          simp only [exists_and_left, motive]
          use nil, X_tl
          simp only [nil_add, true_and]
          use 0, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t
          constructor
          · simp only [zero_add]
            push fun _ ↦ _
            grw [hf_eq]
            simp
          · simp [Approximates.nil, hX_tl]
        | cons Y_exp Y_coef Y_tl =>
          obtain ⟨fYC, hY_coef, hY_maj, hY_tl⟩ := Approximates_cons hY_approx
          rw [add_cons_cons]
          split_ifs with h1 h2
          · simp only [cons_eq_cons, exists_and_left, ↓existsAndEq, and_true, exists_eq_left']
            use fXC
            simp only [hX_coef, true_and]
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
              linarith
            simp only [motive]
            use X_tl, cons Y_exp Y_coef Y_tl, fun t ↦ fX t - basis_hd t ^ X_exp * fXC t, fY
            simp only [hX_tl, hY_approx, and_self, and_true, true_and]
            push fun _ ↦ _
            grw [hf_eq]
            convert EventuallyEq.refl _ _ using 1
            ext
            simp
            ring
          · simp only [cons_eq_cons, exists_and_left, ↓existsAndEq, and_true, exists_eq_left']
            use fYC
            simp only [hY_coef, true_and]
            constructor
            · apply majorated_of_EventuallyEq hf_eq
              convert add_majorated hX_maj hY_maj
              simp
              linarith
            simp only [motive]
            use cons X_exp X_coef X_tl, Y_tl, fX, fun t ↦ fY t - basis_hd t ^ Y_exp * fYC t
            simp only [hX_approx, hY_tl, and_self, and_true, true_and]
            push fun _ ↦ _
            grw [hf_eq]
            convert EventuallyEq.refl _ _ using 1
            ext
            simp
            ring
          · have : X_exp = Y_exp := by linarith
            subst this
            simp only [cons_eq_cons, exists_and_left, ↓existsAndEq, and_true, exists_eq_left']
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
            simp only [Pi.add_apply, hX_tl, hY_tl, and_self, and_true, true_and]
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

instance {basis_hd basis_tl} :
    FriendOperationClass (add (basis := basis_hd :: basis_tl)) := by
  apply FriendOperationClass.mk'
  intro c
  let motive (op : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ (c : PreMS (basis_hd :: basis_tl)), op = add c
  apply FriendOperation.coind_comp_friend_right motive
  · use c
  rintro _ ⟨c, rfl⟩
  simp only [← add_def]
  cases c with
  | nil =>
    use fun hd? ↦ match hd? with
    | none => none
    | some (exp, coef) => some (exp, coef, ⟨id, FriendOperation.id⟩, ⟨fun x ↦ nil + x, _, rfl⟩)
    intro x
    cases x <;> simp
  | cons c_exp c_coef c_tl =>
    use fun hd? ↦ match hd? with
    | none => some (c_exp, c_coef, ⟨fun _ ↦ c_tl, FriendOperation.const⟩, ⟨fun x ↦ nil + x, _, rfl⟩)
    | some (exp, coef) =>
      if exp < c_exp then
        some (c_exp, c_coef, ⟨PreMS.cons exp coef, FriendOperation.cons _ _⟩,
          ⟨fun x ↦ c_tl + x, _, rfl⟩)
      else if c_exp < exp then
        some (exp, coef, ⟨id, FriendOperation.id⟩, ⟨fun x ↦ (cons c_exp c_coef c_tl) + x, _, rfl⟩)
      else
        some (exp, c_coef + coef, ⟨id, FriendOperation.id⟩, ⟨fun x ↦ c_tl + x, _, rfl⟩)
    intro x
    cases x with
    | nil => simp
    | cons x_exp x_coef x_tl =>
      simp [add_cons_cons]
      split_ifs with h1 h2
      · simp
      · simp
      · simp
        linarith

theorem eq_of_bisim_add {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ exp coef,
      ∃ (c x' y' : PreMS (basis_hd :: basis_tl)),
      x = cons exp coef (c + x') ∧ y = cons exp coef (c + y') ∧ motive x' y') :
    x = y :=
  eq_of_bisim_friend (op := add (basis := basis_hd :: basis_tl)) motive base step

theorem eq_of_bisim_add' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {x y : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → PreMS (basis_hd :: basis_tl) → Prop)
    (base : motive x y)
    (step : ∀ x y, motive x y → (x = y) ∨ ∃ (c x' y' : PreMS (basis_hd :: basis_tl)),
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
      simp only [add_nil, cons_eq_cons, exists_and_left, ↓existsAndEq, true_and]
      use c_tl, nil
      simp only [add_nil, true_and]
      use cons y_exp y_coef y_tl
      simpa [add_cons_left hy]
  | cons x_exp x_coef x_tl =>
    cases y' with
    | nil =>
      right
      simp only [add_nil, cons_eq_cons, exists_and_left, ↓existsAndEq, true_and]
      use c_tl, cons x_exp x_coef x_tl
      simp only [add_cons_left hx, true_and]
      use nil
      simpa
    | cons y_exp y_coef y_tl =>
      right
      simp only [add_cons_left hx, cons_eq_cons, add_cons_left hy, exists_and_left, ↓existsAndEq,
        true_and]
      use c_tl, cons x_exp x_coef x_tl
      simp only [true_and]
      use cons y_exp y_coef y_tl

theorem WellOrdered.add_coind {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → Prop) (h_base : motive ms)
    (h_step :
      ∀ (exp : ℝ) (coef : PreMS basis_tl) (tl : PreMS (basis_hd :: basis_tl)),
        motive (PreMS.cons exp coef tl) → coef.WellOrdered ∧ tl.leadingExp < ↑exp ∧
        ∃ A B, tl = A + B ∧ A.WellOrdered ∧ motive B) :
    ms.WellOrdered :=
  WellOrdered.coind_friend' PreMS.add motive PreMS.WellOrdered
    (by apply add_WellOrdered) h_base h_step
  -- let motive' (ms : PreMS (basis_hd :: basis_tl)) : Prop :=
  --   ∃ A B, ms = A + B ∧ A.WellOrdered ∧ motive B
  -- apply WellOrdered.coind motive'
  -- · simp [motive']
  --   use PreMS.nil, ms
  --   simp [WellOrdered.nil, h_base]
  -- intro exp coef tl ih
  -- simp [motive'] at ih
  -- obtain ⟨A, B, h_eq, hA_wo, hB⟩ := ih
  -- simp [motive']
  -- cases A with
  -- | nil =>
  --   simp at h_eq
  --   subst h_eq
  --   specialize h_step _ _ _ hB
  --   obtain ⟨h_coef_wo, h_comp, X, Y, h_tl, hX, hY⟩ := h_step
  --   simp [h_coef_wo, h_comp]
  --   use X, Y
  -- | cons A_exp A_coef A_tl =>
  -- obtain ⟨hA_coef_wo, hA_comp, hA_tl⟩ := WellOrdered_cons hA_wo
  -- cases B with
  -- | nil =>
  --   simp at h_eq
  --   simp [h_eq, hA_coef_wo, hA_comp]
  --   use A_tl, PreMS.nil
  --   simp [hA_tl, hB]
  -- | cons B_exp B_coef B_tl =>
  -- specialize h_step _ _ _ hB
  -- obtain ⟨hB_coef_wo, hB_comp, X, Y, hB_tl, hX, hY⟩ := h_step
  -- rw [add_cons_cons] at h_eq
  -- split_ifs at h_eq with h1 h2
  -- · simp at h_eq
  --   simp [h_eq, hA_coef_wo, hA_comp, h1]
  --   use A_tl, PreMS.cons B_exp B_coef B_tl
  -- · simp at h_eq
  --   simp [h_eq, hB_coef_wo, hB_comp, h2]
  --   use PreMS.cons A_exp A_coef A_tl + X, Y
  --   simp [hB_tl, add_WellOrdered hA_wo hX, hY]
  --   abel
  -- · have : A_exp = B_exp := by linarith
  --   subst this
  --   simp at h_eq
  --   simp [h_eq, hA_comp, hB_comp, add_WellOrdered hA_coef_wo hB_coef_wo]
  --   use A_tl + X, Y
  --   simp [hB_tl, add_WellOrdered hA_tl hX, hY]
  --   abel

theorem WellOrdered.add_coind' {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → Prop) (h_base : motive ms)
    (h_step :
      ∀ ms, motive ms → (ms = PreMS.nil) ∨ ∃ A B, ms = A + B ∧ A.WellOrdered ∧
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
    use A_tl, PreMS.nil
    simp [hA_tl, hB]
  | cons B_exp B_coef B_tl =>
  simp only [add_cons_left hBA, cons_eq_cons] at h_eq
  simp only [leadingExp_cons, WithBot.coe_lt_coe] at hBA
  simp only [h_eq, hA_coef_wo, add_leadingExp, leadingExp_cons, sup_lt_iff, hA_comp,
    WithBot.coe_lt_coe, hBA, and_self, true_and]
  use A_tl, PreMS.cons B_exp B_coef B_tl

theorem Approximates.add_coind {f basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)}
    (motive : PreMS (basis_hd :: basis_tl) → (ℝ → ℝ) → Prop) (h_base : motive ms f)
    (h_step :
      ∀ (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ),
        motive ms f →
        ms = PreMS.nil ∧ f =ᶠ[atTop] 0 ∨
        ∃ exp coef tl fC,
          ms = PreMS.cons exp coef tl ∧ coef.Approximates fC ∧ majorated f basis_hd exp ∧
          ∃ A B fA, tl = A + B ∧ A.Approximates fA ∧
          motive B (fun t ↦ f t - basis_hd t ^ exp * fC t - fA t)) :
    ms.Approximates f := by
  let motive' (ms : PreMS (basis_hd :: basis_tl)) (f : ℝ → ℝ) : Prop :=
    ∃ A B fA fB, ms = A + B ∧ A.Approximates fA ∧ f =ᶠ[atTop] fA + fB ∧ motive B fB
  apply Approximates.coind motive'
  · use PreMS.nil, ms, 0, f
    simp [Approximates.nil, h_base]
  intro ms f ih
  simp only [motive'] at ih
  obtain ⟨A, B, fA, fB, rfl, hA, hf_eq, hB⟩ := ih
  simp only [exists_and_left, ↓existsAndEq, true_and, motive']
  cases A with
  | nil =>
    apply Approximates_nil at hA
    specialize h_step _ _ hB
    obtain ⟨rfl, hfB⟩ | ⟨exp, coef, tl, fC, rfl, h_coef, h_maj, X, Y, fX, h_tl, hX, hY⟩ := h_step
    · simp only [add_nil, true_and, nil_ne_cons, false_and, exists_const, or_false]
      grw [hf_eq, hA, hfB]
      simp
    right
    use exp, coef, fC, X, Y
    simp only [h_tl, nil_add, h_coef, true_and]
    constructor
    · apply majorated_of_EventuallyEq _ h_maj
      grw [hf_eq, hA]
      simp
    use fX, hX, fun t ↦ fB t - basis_hd t ^ exp * fC t - fX t
    simp only [hY, and_true]
    push fun _ ↦ _
    grw [hf_eq, hA]
    convert EventuallyEq.refl _ _ using 1
    ext t
    simp
  | cons A_exp A_coef A_tl =>
    right
    obtain ⟨fAC, hA_coef, hA_maj, hA_tl⟩ := Approximates_cons hA
    specialize h_step _ _ hB
    obtain ⟨rfl, hfB⟩ |
      ⟨B_exp, B_coef, B_tl, fBC, rfl, hB_coef, hB_maj, X, Y, fX, h_tl, hX, hY⟩ := h_step
    · use A_exp, A_coef, fAC, A_tl, PreMS.nil
      simp only [add_nil, hA_coef, true_and]
      constructor
      · apply majorated_of_EventuallyEq _ hA_maj
        grw [hf_eq, hfB]
        simp
      refine ⟨_, hA_tl, fB, ?_, hB⟩
      push fun _ ↦ _
      grw [hf_eq, hfB]
      simp
    rw [add_cons_cons]
    split_ifs with h1 h2
    · use A_exp, A_coef, fAC, A_tl, PreMS.cons B_exp B_coef B_tl
      simp only [hA_coef, true_and]
      constructor
      · apply majorated_of_EventuallyEq hf_eq
        apply add_majorated' hA_maj hB_maj (by rfl) (by linarith)
      refine ⟨_, hA_tl, _, ?_, hB⟩
      push fun _ ↦ _
      grw [hf_eq]
      convert EventuallyEq.refl _ _ using 1
      ext t
      simp
      ring
    · use B_exp, B_coef, fBC, PreMS.cons A_exp A_coef A_tl + X, Y
      simp only [h_tl, cons_eq_cons, true_and]
      constructorm* _ ∧ _
      · abel
      · assumption
      · apply majorated_of_EventuallyEq hf_eq
        apply add_majorated' hA_maj hB_maj (by linarith) (by rfl)
      use fA + fX
      constructor
      · apply add_Approximates hA hX
      refine ⟨_, ?_, hY⟩
      push fun _ ↦ _
      grw [hf_eq]
      convert EventuallyEq.refl _ _ using 1
      ext t
      simp
      ring
    · have : A_exp = B_exp := by linarith
      subst this
      use A_exp, A_coef + B_coef, fAC + fBC, A_tl + X, Y
      constructorm* _ ∧ _
      · simp [h_tl]
        abel
      · apply add_Approximates hA_coef hB_coef
      · apply majorated_of_EventuallyEq hf_eq
        apply add_majorated' hA_maj hB_maj (by rfl) (by rfl)
      refine ⟨_, add_Approximates hA_tl hX, _, ?_, hY⟩
      push fun _ ↦ _
      grw [hf_eq]
      convert EventuallyEq.refl _ _ using 1
      ext t
      simp
      ring

end PreMS

end ComputeAsymptotics
