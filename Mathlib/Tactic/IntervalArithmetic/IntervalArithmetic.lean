/- # Verified Real Number Calculations: A Library for Interval Arithmetic -/

import Mathlib

open Nat

/- First Attempt : Following the paper as closely as possible! -/

structure RatInterval where
  lb : ℚ
  ub : ℚ
deriving BEq

def RatInterval.toSet (x : RatInterval) : Set ℝ := Set.Icc x.lb x.ub

@[simp] lemma RatInterval.toSet_def (x : RatInterval) : x.toSet = Set.Icc ↑x.lb ↑x.ub := rfl

def RatInterval.const (r : ℚ) : RatInterval := ⟨r,r⟩

def RatInterval.add (x : RatInterval) (y : RatInterval) : RatInterval := ⟨x.lb + y.lb, x.ub + y.ub⟩

instance : Add RatInterval := ⟨RatInterval.add⟩

@[simp] lemma RatInterval.add_lb (x : RatInterval) (y : RatInterval) :
  (x + y).lb = x.lb + y.lb := rfl

@[simp] lemma RatInterval.add_ub (x : RatInterval) (y : RatInterval) :
  (x + y).ub = x.ub + y.ub := rfl

def RatInterval.sub (x : RatInterval) (y : RatInterval) : RatInterval := ⟨x.lb - y.ub, x.ub - y.lb⟩

instance : Sub RatInterval := ⟨RatInterval.sub⟩

@[simp] lemma RatInterval.sub_lb (x : RatInterval) (y : RatInterval) :
  (x - y).lb = x.lb - y.ub := rfl

@[simp] lemma RatInterval.sub_ub (x : RatInterval) (y : RatInterval) :
  (x - y).ub = x.ub - y.lb := rfl

def RatInterval.mul (x : RatInterval) (y : RatInterval) : RatInterval :=
  ⟨x.lb * y.lb |> min (x.lb * y.ub) |> min (x.ub * y.lb) |> min (x.ub * y.ub),
   x.lb * y.lb |> max (x.lb * y.ub) |> max (x.ub * y.lb) |> max (x.ub * y.ub)⟩

instance : Mul RatInterval := ⟨RatInterval.mul⟩

@[simp] lemma RatInterval.mul_lb (x : RatInterval) (y : RatInterval) :
  (x * y).lb = (x.lb * y.lb |> min (x.lb * y.ub) |> min (x.ub * y.lb) |> min (x.ub * y.ub)) := rfl

@[simp] lemma RatInterval.mul_ub (x : RatInterval) (y : RatInterval) :
  (x * y).ub = (x.lb * y.lb |> max (x.lb * y.ub) |> max (x.ub * y.lb) |> max (x.ub * y.ub)) := rfl

/- Junk unless `y.lb * y.ub > 0` -/
def RatInterval.div (x : RatInterval) (y : RatInterval) : RatInterval := x * ⟨1 / y.ub, 1 / y.lb⟩

instance : Div RatInterval := ⟨RatInterval.div⟩

@[simp] lemma RatInterval.div_def (x : RatInterval) (y : RatInterval) :
  x / y = x * ⟨1 / y.ub, 1 / y.lb⟩ := rfl

def RatInterval.neg (x : RatInterval) : RatInterval := ⟨-x.ub, -x.lb⟩

instance : Neg RatInterval := ⟨RatInterval.neg⟩

def RatInterval.abs (x : RatInterval) : RatInterval :=
  if 0 ≤ x.lb * x.ub
  then ⟨min |x.lb| |x.ub|, max |x.lb| |x.ub|⟩
  else ⟨0, max |x.lb| |x.ub|⟩

@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(RatInterval.abs $a)

lemma RatInterval.abs_eq_of_mul_nonneg {x : RatInterval} (hx : 0 ≤ x.lb * x.ub) :
    |x| = ⟨min |x.lb| |x.ub|, max |x.lb| |x.ub|⟩ := by
  simp [RatInterval.abs, hx]

lemma RatInterval.abs_eq_of_mul_neg {x : RatInterval} (hx : x.lb * x.ub < 0) :
    |x| = ⟨0, max |x.lb| |x.ub|⟩ := by
  simp [RatInterval.abs, hx]

def RatInterval.pow (x : RatInterval) (n : ℕ) : RatInterval :=
  if n = 0 then ⟨1,1⟩
  else if 0 ≤ x.lb || Odd n then ⟨x.lb ^ n, x.ub ^ n⟩
  else if x.ub ≤ 0 then ⟨x.ub ^ n, x.lb ^ n⟩
  else ⟨0, max (x.lb ^ n) (x.ub ^ n)⟩

instance : Pow RatInterval ℕ := ⟨RatInterval.pow⟩

@[simp]
lemma RatInterval.pow_zero (x : RatInterval) : (x ^ 0) = ⟨1,1⟩ := by
  simp [HPow.hPow, Pow.pow, RatInterval.pow]

lemma RatInterval.pow_of_nonneg {x : RatInterval} (n : ℕ) (hx : 0 ≤ x.lb) :
    (x ^ n) = ⟨x.lb ^ n, x.ub ^ n⟩ := by
  match n with
  | 0 => simp
  | .succ n => simp [HPow.hPow, Pow.pow, RatInterval.pow, hx]

lemma RatInterval.pow_of_odd (x : RatInterval) {n : ℕ} (hn : Odd n) :
    (x ^ n) = ⟨x.lb ^ n, x.ub ^ n⟩ := by
  match n with
  | 0 => simp
  | .succ n => simp [HPow.hPow, Pow.pow, RatInterval.pow, hn]

lemma RatInterval.pow_of_neg_nonneg_and_even {x : RatInterval} {n : ℕ}
    (hxlb : x.lb < 0) (hxub : x.ub ≤ 0) (hn : Even n) :
    (x ^ n) = ⟨x.ub ^ n, x.lb ^ n⟩ := by
  match n with
  | 0 => simp
  | .succ n => simp [HPow.hPow, Pow.pow, RatInterval.pow, hxlb, hxub, hn]

lemma RatInterval.pow_of_contains_zero_and_nonzero_even {x : RatInterval} {n : ℕ}
    (hxlb : x.lb < 0) (hxub : 0 < x.ub) (hn : Even n) (hn' : n ≠ 0) :
    (x ^ n) = ⟨0, max (x.lb ^ n) (x.ub ^ n)⟩ := by
  simp [HPow.hPow, Pow.pow, RatInterval.pow, hn', not_le.mpr hxlb, hxub, not_odd_iff_even.mpr hn]

/- Inclusion Theorems -/

theorem const_inclusion (r : ℚ) : (r : ℝ) ∈ (RatInterval.const r).toSet := by
  simp [RatInterval.const]

theorem add_inclusion {r s : ℝ} {x y : RatInterval} (hrx : r ∈ x.toSet) (hsy : s ∈ y.toSet) :
    (r + s) ∈ (x + y).toSet := by
  simp at *
  grind

theorem sub_inclusion {r s : ℝ} {x y : RatInterval} (hrx : r ∈ x.toSet) (hsy : s ∈ y.toSet) :
    (r - s) ∈ (x - y).toSet := by
  simp at *
  grind

theorem mul_inclusion {r s : ℝ} {x y : RatInterval} (hrx : r ∈ x.toSet) (hsy : s ∈ y.toSet) :
    (r * s) ∈ (x * y).toSet := by
  simp only [RatInterval.toSet_def, Set.mem_Icc, RatInterval.mul_lb, Rat.cast_min, Rat.cast_mul,
    RatInterval.mul_ub, Rat.cast_max, inf_le_iff, le_sup_iff] at *
  constructor
  · by_cases! hxlb : 0 ≤ (x.lb : ℝ) <;> by_cases! hylb : 0 ≤ (y.lb : ℝ)
    · right; right; right; exact mul_le_mul hrx.1 hsy.1 hylb (by linarith)
    · right; left; exact mul_le_mul_of_nonneg_of_nonpos hrx.2 hsy.1 (by linarith) (by linarith)
    · right; right; left
      grw [mul_le_mul_of_nonpos_left hsy.2 (by linarith)]
      exact mul_le_mul_of_nonneg_right hrx.1 (by linarith)
    · by_cases! hr : 0 ≤ r
      · right; left; exact mul_le_mul_of_nonneg_of_nonpos hrx.2 hsy.1 hr (by linarith)
      · by_cases! hyub : 0 ≤ (y.ub : ℝ)
        · right; right; left; exact mul_le_mul_of_nonpos_of_nonneg hrx.1 hsy.2 (by linarith) hyub
        · left; exact mul_le_mul_of_nonpos_of_nonpos hrx.2 hsy.2 (by linarith) (by linarith)
  · by_cases! hxlb : 0 ≤ (x.lb : ℝ) <;> by_cases! hylb : 0 ≤ (y.lb : ℝ)
    · left; exact mul_le_mul hrx.2 hsy.2 (by linarith) (by linarith)
    · by_cases! hyub : 0 ≤ (y.ub : ℝ)
      · left
        grw [mul_le_mul_of_nonneg_left hsy.2 (by linarith)]
        exact mul_le_mul_of_nonneg_right hrx.2 hyub
      · right; right; left; exact mul_le_mul_of_nonneg_of_nonpos hrx.1 hsy.2 hxlb (by linarith)
    · by_cases! hxub : 0 ≤ (x.ub : ℝ)
      · left
        grw [mul_le_mul_of_nonneg_right hrx.2 (by linarith)]
        exact mul_le_mul_of_nonneg_left hsy.2 hxub
      · right; left; exact mul_le_mul_of_nonpos_of_nonneg hrx.2 hsy.1 (by linarith) (by linarith)
    · by_cases! hr : 0 ≤ r <;> by_cases! hs : 0 ≤ s
      · left; exact mul_le_mul hrx.2 hsy.2 hs (by linarith)
      · right; right; right; exact le_trans (b := 0) (by nlinarith) (by nlinarith)
      · right; right; right; exact le_trans (b := 0) (by nlinarith) (by nlinarith)
      · right; right; right
        exact mul_le_mul_of_nonpos_of_nonpos hrx.1 hsy.1 (by linarith) (by linarith)

theorem div_inclusion {r s : ℝ} {x y : RatInterval} (hrx : r ∈ x.toSet) (hsy : s ∈ y.toSet)
    (hy : 0 < y.lb * y.ub) : (r / s) ∈ (x / y).toSet := by
  simp only [div_eq_mul_inv, RatInterval.div_def] at *
  apply mul_inclusion hrx
  rw [mul_pos_iff] at hy
  rify at hy
  obtain ⟨hylb, hyub⟩ | ⟨hylb, hyub⟩ := hy
  · simp only [RatInterval.toSet_def, Set.mem_Icc, one_mul, Rat.cast_inv] at hsy ⊢
    rw [inv_le_inv₀ hyub (by linarith), inv_le_inv₀ (by linarith) hylb]
    simp [hsy]
  · simp only [RatInterval.toSet_def, Set.mem_Icc, one_mul, Rat.cast_inv] at hsy ⊢
    rw [inv_le_inv_of_neg hyub (by linarith), inv_le_inv_of_neg (by linarith) hylb]
    simp [hsy]

theorem neg_inclusion {r : ℝ} {x : RatInterval} (hrx : r ∈ x.toSet) : -r ∈ -x.toSet := by
  simp at *
  grind

theorem abs_inclusion {r : ℝ} {x : RatInterval} (hrx : r ∈ x.toSet) : |r| ∈ |x|.toSet := by
  by_cases! h : 0 ≤ x.lb * x.ub
  · rw [RatInterval.abs_eq_of_mul_nonneg h]
    sorry
  · rw [RatInterval.abs_eq_of_mul_neg h]
    sorry

theorem pow_inclusion {r : ℝ} {x : RatInterval} (n : ℕ) (hrx : r ∈ x.toSet) :
    (r ^ n) ∈ (x ^ n).toSet := by
  simp only [RatInterval.toSet_def, Set.mem_Icc] at hrx
  by_cases! hn' : n = 0
  · simp [hn']
  by_cases! hxlb : 0 ≤ x.lb
  · simp [RatInterval.pow_of_nonneg n hxlb]
    rify at hxlb
    simp [pow_le_pow_left₀ hxlb hrx.1, pow_le_pow_left₀ (by linarith) hrx.2]
  by_cases! hn : Odd n
  · simp [RatInterval.pow_of_odd x hn, hn.pow_le_pow, hrx.1, hrx.2]
  replace hn := not_odd_iff_even.mp hn
  by_cases! hxub : x.ub ≤ 0
  · simp [RatInterval.pow_of_neg_nonneg_and_even hxlb hxub hn]
    rify at hxub hxlb
    simp [← hn.neg_pow (x.ub : ℝ), ← hn.neg_pow r, ← hn.neg_pow (x.lb : ℝ),
      pow_le_pow_left₀ (a := -(x.ub : ℝ)) (b := -r) (by linarith) (by linarith),
      pow_le_pow_left₀ (a := -r) (b := -(x.lb : ℝ)) (by linarith) (by linarith)]
  simp only [RatInterval.pow_of_contains_zero_and_nonzero_even hxlb hxub hn hn',
    RatInterval.toSet_def, Rat.cast_zero, Set.mem_Icc, hn.pow_nonneg]
  by_cases! hr : 0 ≤ r
  · simp [pow_le_pow_left₀ hr hrx.2]
  · simp [← hn.neg_pow r, ← hn.neg_pow (x.lb : ℝ),
      pow_le_pow_left₀ (a := -r) (b := -x.lb) (by linarith) (by linarith)]

/- Interval Comparisons -/

def RatInterval.subset (x : RatInterval) (y : RatInterval) : Prop := y.lb ≤ x.lb ∧ x.ub ≤ y.ub

-- instance (x y : RatInterval) : Decidable (x.subset y) := instDecidableAnd

instance : HasSubset RatInterval := ⟨(RatInterval.subset · ·)⟩

instance (x y : RatInterval) : Decidable (x ⊆ y) := instDecidableAnd

def RatInterval.le (x : RatInterval) (r : ℝ) : Prop := x.ub ≤ r

def RatInterval.lt (x : RatInterval) (r : ℝ) : Prop := x.ub < r

def RatInterval.ge (x : RatInterval) (r : ℝ) : Prop := r ≤ x.lb

def RatInterval.gt (x : RatInterval) (r : ℝ) : Prop := r < x.lb

lemma RatInterval.le_of_le {x : RatInterval} (r s : ℝ) (hrx : r ∈ x.toSet) (hsx : x.le s) :
    r ≤ s := le_trans hrx.2 hsx

lemma RatInterval.lt_of_lt {x : RatInterval} (r s : ℝ) (hrx : r ∈ x.toSet) (hsx : x.lt s) :
    r < s := lt_of_le_of_lt hrx.2 hsx

lemma RatInterval.le_of_ge {x : RatInterval} (r s : ℝ) (hrx : r ∈ x.toSet) (hsx : x.ge s) :
    s ≤ r := le_trans hsx hrx.1

lemma RatInterval.lt_of_gt {x : RatInterval} (r s : ℝ) (hrx : r ∈ x.toSet) (hsx : x.gt s) :
    s < r := lt_of_lt_of_le hsx hrx.1

lemma RatInterval.subset_of_subset {x y : RatInterval} (hxy : x ⊆ y) : x.toSet ⊆ y.toSet := by
  intro r hr
  simp only [Subset, subset, toSet_def, Set.mem_Icc] at hxy hr ⊢
  rify at hxy
  exact ⟨by linarith, by linarith⟩

/- Define `exp` approximations -/

def exp_lower_taylor (x : ℚ) (n : ℕ) :=
  ∑ i ∈ Finset.range (2 * (n + 1) + 1), (x ^ i) / i !

def exp_upper_taylor (x : ℚ) (n : ℕ) :=
  ∑ i ∈ Finset.range (2*(n + 1)), (x ^ i) / i !

def exp_neg_lb (x : ℚ) (n : ℕ) :=
  if x < -1 then (exp_lower_taylor (x / - x.floor) n) ^ (- x.floor)
  else exp_lower_taylor x n

def exp_neg_ub (x : ℚ) (n : ℕ) :=
  if x < -1 then (exp_upper_taylor (x / - x.floor) n) ^ (- x.floor)
  else exp_upper_taylor x n

def exp_lb (x : ℚ) (n : ℕ) :=
  if x < 0 then exp_neg_lb x n
  else if x = 0 then 1
  else 1 / exp_neg_ub (-x) n

def exp_ub (x : ℚ) (n : ℕ) :=
  if x < 0 then exp_neg_ub x n
  else if x = 0 then 1
  else 1 / exp_neg_lb (-x) n

def RatInterval.exp (x : RatInterval) (n : ℕ) : RatInterval :=
  ⟨exp_lb x.lb n, exp_ub x.ub n⟩

/- ## Test 1 -/

-- example (u : ℝ) (hu : 0 ≤ u) : 0 ≤ (Real.exp u * (u - 2) + u + 2) := by

/-

## Prototype 1

Prototype 1 will assume all hypothesis come in the form `rᵢ ∈ xᵢ.toSet` exactly one for each
real variable `rᵢ` in the context.

We want to prove a goal of the form `e₁ ⋈ e₂`. We will need to rewrite this as
`e₁ - e₂ ⋈ 0` and then convert the lhs into an interval. Then compute that this is
true or false.

Perhaps we construct a proof term that `[e] ⋈ 0 → e ⋈ 0` (I think this will be easier to extend).

So to make this work we need to show that our map `e ⋈ 0` iff `[e] ⋈ 0`, then we prove
`[e] ⋈ 0` by reflection.

-/

open Lean Meta Expr Elab Tactic Std

namespace RatArithmetic

structure Result where
  interval : RatInterval
  /-- proof that `e ∈ interval` -/
  proof : Expr

#check Expr.rat?
#check Expr.fvarId?
#check add_inclusion
#check mkAppM

#check getMainGoal
/-
add_inclusion {r s : ℝ} {x y : RatInterval} (hrx : r ∈ x.toSet) (hsy : s ∈ y.toSet) :
  r + s ∈ (x + y).toSet
-/

partial def Expr.toInterval (e : Expr) (ctx : HashMap FVarId (RatInterval × Expr)) :
    MetaM RatArithmetic.Result := do
  if let some fvarid := e.fvarId? then
    if let some ⟨x, p⟩ := ctx[fvarid]? then
      return {interval := x, proof := p}
    else
      throwError "variable not in context"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, x, y]) =>
    let rx ← Expr.toInterval x ctx
    let ry ← Expr.toInterval y ctx
    let p ← mkAppM ``add_inclusion #[rx.proof, ry.proof]
    return {interval := rx.interval + ry.interval, proof := p}
  | (``HSub.hSub, #[_, _, _, _, x, y]) =>
    let rx ← Expr.toInterval x ctx
    let ry ← Expr.toInterval y ctx
    let p ← mkAppM ``sub_inclusion #[rx.proof, ry.proof]
    return {interval := rx.interval - ry.interval, proof := p}
  | (``HMul.hMul, #[_, _, _, _, x, y]) =>
    let rx ← Expr.toInterval x ctx
    let ry ← Expr.toInterval y ctx
    let p ← mkAppM ``mul_inclusion #[rx.proof, ry.proof]
    return {interval := rx.interval * ry.interval, proof := p}
  | _ => throwError "unsupported"

syntax (name := interval) "interval" : tactic

def Expr.RatInterval? (e : Expr) : Option RatInterval :=
  match e.getAppFnArgs with
  | (``RatInterval.mk, #[lb, ub]) =>
    match lb.rat?, ub.rat? with
    | some lb, some ub => some ⟨lb, ub⟩
    | _, _ => none
  | _ => none

def Expr.intervalHyp? (e : Expr) : MetaM (Option (FVarId × RatInterval)) :=
  match e.getAppFnArgs with
  | (``Membership.mem, #[_, _, .app (.const ``RatInterval.toSet []) ex, v]) => do
    match v.fvarId?, Expr.RatInterval? ex with
    | some fvarid, some x => return some ⟨fvarid, x⟩
    | _, _ => return none
  | _ => return none

def RatInterval.toExpr (x : RatInterval) : Expr :=
  mkAppN (mkConst ``RatInterval.mk) #[ToExpr.toExpr x.lb, ToExpr.toExpr x.ub]

elab "interval" : tactic => withMainContext do
  let g ← getMainGoal
  -- why do we need `:= ←`
  let ctx : HashMap FVarId (RatInterval × Expr) := ← do
    let mut ctx : HashMap FVarId (RatInterval × Expr) := {}
    for ldecl in ← getLCtx do
      if let some ⟨fvarid, x⟩ := (← Expr.intervalHyp? ldecl.type) then
        ctx := ctx.insert fvarid ⟨x, ldecl.toExpr⟩
    return ctx
  let t ← g.getType
  match t.getAppFnArgs with
  | (``Membership.mem, #[_, _, .app (.const ``RatInterval.toSet []) ex, e]) =>
    let some x := Expr.RatInterval? ex | throwError "unsupported1"
    let r ← Expr.toInterval e ctx
    if r.interval ⊆ x then
      let hrx ← mkDecideProof
        (← mkAppM ``HasSubset.Subset #[RatInterval.toExpr r.interval, RatInterval.toExpr x])
      let p := .app (← mkAppM ``RatInterval.subset_of_subset #[hrx]) r.proof
      g.assign p
      replaceMainGoal []
    else throwError "failure to bound"
  | _ => throwError "unsupported2"

/- ## Scratchpad Brainstorm

- Create a context: `Array (Name × RatInterval)`

- Convert the expression in the goal to a RatInterval. This is a map which takes the context and
  the goal as an expression and converts to a RatInterval.

-/

example {x : ℝ} (hx : x ∈ (RatInterval.mk 3 5).toSet) :
    x ∈ (RatInterval.mk 3 5).toSet := by
  interval

end RatArithmetic
