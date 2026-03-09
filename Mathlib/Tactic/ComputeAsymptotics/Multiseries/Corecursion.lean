/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Data.Seq.Defs
public import Mathlib.Tactic.ENatToNat

/-!
# Non-primitive corecursion for sequences

Primitive corecursive definition of the form
```
def foo (x : X) := hd x :: foo (tlArg x)
```
(where hd and tlArg are arbitrary functions) can be encoded via the corecursor `Seq.corec`.

It is not enough, however, to define multiplication and `powser` operation for multiseries.

This file implements a more general form of corecursion in the spirit of [blanchette2015].
This is a bare minimum that needed for the tactic, it justifies a weaker class of
corecursive definitions than [blanchette2015] does, and only works for `Seq`.

A function `f : Seq α → Seq α` is called *friendly* if for all `n : ℕ` the `n`-prefix of its result
`f s` depends only on the `n`-prefix of its input `s`.

In this file we develop a theory that justifies corecursive definitions of the form
```
def foo (x : X) := hd x :: f (foo (tlArg x))
```
where f is friendly.

## Main definitions

* `FriendlyOperation f` means that `f` is friendly.
* `FriendlyOperationClass` is a typeclass meaning that some indexed family of operations
  are friendly.
* `gcorec`: a generalization of `Seq.corec` that allows a corecursive call to be guarded by
  a friendly function.
* `FriendlyOperation.coind`, `FriendlyOperation.coind_comp_friend_left`,
  `FriendlyOperation.coind_comp_friend_right`: coinduction principles for proving that an operation
  is friendly.
* `FriendlyOperation.eq_of_bisim`: a generalisation of `Seq.eq_of_bisim'` that allows using a
  friendly operation in the tail of the sequences.

## Implementation details

To prove that the definition of the form
```
def foo (x : X) := hd x :: f (foo (tlArg x))
```
is correct we prove that there exists a function satisfying this equation. For that we employ a
Banach fixed point theorem. We treat `Seq α` as a metric space here with the metric
`d(s, t) := 2 ^ (-n)` where `n` is the minimal index where `s` and `t` differ.

Then `f` is friendly iff it is `1`-Lipschitz.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics.Seq

open Stream' Seq

open scoped UniformConvergence

variable {α β γ γ' : Type*}

/-- Metric space structure on `Stream' α` considering `α` as a discrete metric space. -/
noncomputable local instance : MetricSpace (Stream' α) :=
  @PiNat.metricSpace (fun _ ↦ α) (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)

/-- Metric space structure on `Seq α` considering `α` as a discrete metric space. -/
noncomputable local instance : MetricSpace (Seq α) :=
  Subtype.metricSpace

local instance : CompleteSpace (Stream' α) :=
  @PiNat.completeSpace _ (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)

local instance : CompleteSpace (Seq α) := by
  suffices IsClosed (X := Stream' (Option α))
      (fun x ↦ ∀ {n : ℕ}, x n = none → x (n + 1) = none) by
    apply IsClosed.completeSpace_coe
  rw [isClosed_iff_clusterPt]
  intro s hs n hn
  rw [clusterPt_principal_iff] at hs
  obtain ⟨t, hts, ht⟩ := hs (Metric.ball s ((1 / 2 : ℝ) ^ (n + 1)))
    (Metric.ball_mem_nhds _ (by positivity))
  simp only [Metric.ball, Set.mem_setOf_eq] at hts
  rw [← PiNat.apply_eq_of_dist_lt hts (by simp)] at hn
  rw [← PiNat.apply_eq_of_dist_lt hts (by rfl)]
  exact ht hn

set_option backward.isDefEq.respectTransparency false in
theorem Stream'.dist_le_one (s t : Stream' α) : dist s t ≤ 1 := by
  by_cases h : s = t
  · simp [h]
  rw [PiNat.dist_eq_of_ne h]
  bound

@[simp]
theorem dist_le_one (s t : Seq α) : dist s t ≤ 1 := PiNat.dist_le_one _ _

local instance : BoundedSpace (Stream' α) :=
  @PiNat.boundedSpace _ (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)

local instance : BoundedSpace (Seq α) :=
  instBoundedSpaceSubtype

set_option backward.isDefEq.respectTransparency false in
theorem dist_eq_two_inv_pow {s t : Seq α} (h : s ≠ t) : ∃ n, dist s t = 2⁻¹ ^ n := by
  rw [Subtype.dist_eq, PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]
  simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem dist_cons_cons (x : α) (s t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t := by
  by_cases! h : s = t
  · simp [h]
  have h' : cons x s ≠ cons x t := by
    simpa
  rw [Subtype.dist_eq, Subtype.dist_eq, PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h),
    PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h')]
  simp only [show (1 / 2 : ℝ) = 2⁻¹ by simp, ← pow_succ']
  congr
  simp only [val_cons, PiNat.firstDiff, ne_eq, Classical.dite_not, Subtype.coe_ne_coe.mpr h,
    not_false_eq_true, ↓reduceDIte, val_eq_get]
  split_ifs with h_if
  · contrapose! h'
    apply_fun Subtype.val using Subtype.val_injective
    simpa
  · convert Nat.find_comp_succ _ _ _
    simp [Stream'.cons]

theorem dist_eq_half_of_head {s t : Seq α} (h : s.head = t.head) :
    dist s t = 2⁻¹ * dist s.tail t.tail := by
  cases s <;> cases t <;> simp at h <;> simp [h]

set_option backward.isDefEq.respectTransparency false in
theorem dist_eq_one_of_head {s t : Seq α} (h : s.head ≠ t.head) : dist s t = 1 := by
  rw [Subtype.dist_eq, PiNat.dist_eq_of_ne]
  · convert pow_zero _
    simp only [PiNat.firstDiff, ne_eq, Classical.dite_not, dite_eq_left_iff,
      Nat.find_eq_zero]
    intro h'
    simpa [Stream'.cons]
  · rw [Subtype.coe_ne_coe]
    contrapose! h
    simp [h]

theorem dist_cons_cons_eq_one {x y : α} {s t : Seq α} (h : x ≠ y) :
    dist (cons x s) (cons y t) = 1 := by
  apply dist_eq_one_of_head
  simpa

@[simp]
theorem dist_cons_nil (x : α) (s : Seq α) : dist (cons x s) nil = 1 := by
  apply dist_eq_one_of_head
  simp

@[simp]
theorem dist_nil_cons (x : α) (s : Seq α) : dist nil (cons x s) = 1 := by
  rw [dist_comm]
  simp

theorem dist_le_half_iff {s t : Seq α} :
    dist s t ≤ 2⁻¹ ↔ (s = .nil ∧ t = .nil) ∨ ∃ hd s' t', s = .cons hd s' ∧ t = .cons hd t' where
  mp h := by
    cases s <;> cases t <;> norm_num at h <;> simp
    grind [dist_cons_cons_eq_one]
  mpr h := by
    obtain ⟨rfl, rfl⟩ | ⟨hd, s', t', rfl, rfl⟩ := h <;> simp

/-- A function on sequences is called a "friend" if any `n`-prefix of its output depends only on
the `n`-prefix of the input. Such functions can be used in the tail of (non-primitive) corecursive
definitions. -/
def FriendlyOperation (op : Seq α → Seq α) : Prop := LipschitzWith 1 op

/-- A family of friendly operations on sequences indexed by a type `γ`. -/
class FriendlyOperationClass (F : γ → Seq α → Seq α) : Prop where
  friend : ∀ c : γ, FriendlyOperation (F c)

theorem friendlyOperation_iff_dist_le_dist (op : Seq α → Seq α) :
    FriendlyOperation op ↔ ∀ s t, dist (op s) (op t) ≤ dist s t := by
  simp [FriendlyOperation, lipschitzWith_iff_dist_le_mul]

theorem FriendlyOperation.id : FriendlyOperation (id : Seq α → Seq α) :=
  LipschitzWith.id

theorem FriendlyOperation.comp {op op' : Seq α → Seq α}
    (h : FriendlyOperation op) (h' : FriendlyOperation op') :
    FriendlyOperation (op ∘ op') := by
  rw [FriendlyOperation] at h h' ⊢
  convert h.comp h'
  simp

theorem FriendlyOperation.const {s : Seq α} : FriendlyOperation (fun _ ↦ s) := by
  simp [friendlyOperation_iff_dist_le_dist]

theorem FriendlyOperationClass.comp (F : γ → Seq α → Seq α) (g : γ' → γ)
    [h : FriendlyOperationClass F] : FriendlyOperationClass (fun c ↦ F (g c)) := by
  grind [FriendlyOperationClass]

theorem FriendlyOperation.ite {op₁ op₂ : Seq α → Seq α}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂)
    {P : Option α → Prop} [DecidablePred P] :
    FriendlyOperation (fun s ↦ if P s.head then op₁ s else op₂ s) := by
  rw [friendlyOperation_iff_dist_le_dist] at h₁ h₂ ⊢
  intro s t
  by_cases! h_head : s.head ≠ t.head
  · simp [dist_eq_one_of_head h_head]
  grind

theorem FriendlyOperation.dist_le {op : Seq α → Seq α} (h : FriendlyOperation op)
    {s t : Seq α} : dist (op s) (op t) ≤ dist s t := by
  rw [FriendlyOperation, lipschitzWith_iff_dist_le_mul] at h
  simpa using h s t

theorem exists_fixed_point_of_contractible (F : (β →ᵤ Seq α) → (β →ᵤ Seq α))
    (h : LipschitzWith 2⁻¹ F) :
    ∃ f : β → Seq α, Function.IsFixedPt F f := by
  have hF : ContractingWith 2⁻¹ F := by
    constructor
    · norm_num
    · exact h
  let f := hF.fixedPoint _
  use f
  exact hF.fixedPoint_isFixedPt

set_option backward.isDefEq.respectTransparency false in
/-- Main theorem of this file. It shows that there exists a funcion satisfying the corecursive
definition of the form `def foo (x : X) := hd x :: op (foo (tlArg x))` where `f` is friendly. -/
theorem FriendlyOperation.exists_fixed_point (F : β → Option (α × γ × β)) (op : γ → Seq α → Seq α)
    [h : FriendlyOperationClass op] :
    ∃ f : β → Seq α, ∀ b : β,
    match F b with
    | none => f b = nil
    | some (a, c, b') => f b = Seq.cons a (op c (f b')) := by
  let T : (β →ᵤ Seq α) → (β →ᵤ Seq α) := fun f b =>
    match F b with
    | none => nil
    | some (a, c, b') => Seq.cons a (op c (f b'))
  have hT : LipschitzWith 2⁻¹ T := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro f g
    rw [UniformFun.dist_le (by positivity)]
    intro b
    simp only [UniformFun.toFun, UniformFun.ofFun, Equiv.coe_fn_symm_mk, NNReal.coe_inv,
      NNReal.coe_ofNat, T]
    cases F b with
    | none => simp
    | some v =>
      obtain ⟨a, c, b'⟩ := v
      simp
      calc
        _ ≤ dist (f b') (g b') := by
          have := h.friend c
          rw [FriendlyOperation, lipschitzWith_iff_dist_le_mul] at this
          specialize this (f b') (g b')
          simpa using this
        _ ≤ _ := by
          simp only [UniformFun.dist_def]
          apply le_ciSup (f := fun b ↦ dist (f b) (g b))
          have : ∃ C, ∀ (a b : Seq α), dist a b ≤ C := by
            rw [← Metric.boundedSpace_iff]
            infer_instance
          obtain ⟨C, hC⟩ := this
          use C
          simp [upperBounds]
          grind
  obtain ⟨f, hf⟩ := exists_fixed_point_of_contractible T hT
  use f
  intro b
  rw [← hf]
  simp only [T]
  cases hb : F b with
  | none =>
    simp
  | some v =>
    obtain ⟨a, c, b'⟩ := v
    simp only [cons_eq_cons, true_and]
    congr
    change f b' = T f b'
    rw [hf]

/-- (General) non-primitive corecursor for `Seq α` that allows using a friendly operation in the
tail of the corecursive definition. -/
noncomputable def gcorec (F : β → Option (α × γ × β)) (op : γ → Seq α → Seq α)
    [FriendlyOperationClass op] :
  β → Seq α := (FriendlyOperation.exists_fixed_point F op).choose

theorem gcorec_nil {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendlyOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using this

theorem gcorec_some {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendlyOperationClass op] {b : β}
    {a : α} {c : γ} {b' : β}
    (h : F b = some (a, c, b')) :
    gcorec F op b = Seq.cons a (op c (gcorec F op b')) := by
  have := (FriendlyOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using this

/-- The operation `cons hd ·` is friendly. -/
theorem FriendlyOperation.cons (hd : α) : FriendlyOperation (cons hd) := by
  simp only [friendlyOperation_iff_dist_le_dist, dist_cons_cons]
  intro x y
  linarith [dist_nonneg (x := x) (y := y)]

/-- The operation `(op (.cons hd ·)).tail` is friendly if `op` is friendly. -/
theorem FriendlyOperation.cons_tail {op : Seq α → Seq α} {hd : α} (h : FriendlyOperation op) :
    FriendlyOperation (fun s ↦ (op (.cons hd s)).tail) := by
  simp_rw [friendlyOperation_iff_dist_le_dist] at h ⊢
  intro x y
  specialize h (.cons hd x) (.cons hd y)
  simp only [dist_cons_cons] at h
  cases hx : op (.cons hd x) with
  | nil =>
    cases hy : op (.cons hd y) with
    | nil => simp
    | cons y_hd y_tl =>
      grw [hx, hy, dist_le_one x y] at h
      norm_num at h
  | cons x_hd x_tl =>
    cases hy : op (.cons hd y) with
    | nil =>
      grw [hx, hy, dist_le_one x y] at h
      norm_num at h
    | cons y_hd y_tl =>
      suffices h_hd : x_hd = y_hd by
        simpa [hx, hy, h_hd] using h
      contrapose! h with h_hd
      grw [hx, hy, dist_cons_cons_eq_one h_hd, dist_le_one]
      norm_num

/-- The first element of `op (a :: s)` depends only on `a`. -/
theorem FriendlyOperation.op_cons_head_eq {op : Seq α → Seq α} (h : FriendlyOperation op) {a : α}
    {s t : Seq α} : (op <| .cons a s).head = (op <| .cons a t).head := by
  rw [friendlyOperation_iff_dist_le_dist] at h
  specialize h (.cons a s) (.cons a t)
  simp only [dist_cons_cons] at h
  replace h : dist (op (.cons a s)) (op (.cons a t)) ≤ 2⁻¹ := by
    apply h.trans
    simp
  rw [dist_le_half_iff] at h
  generalize op (Seq.cons a s) = s' at *
  generalize op (Seq.cons a t) = t' at *
  obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := h <;> rfl

/-- Decomposes a friendly operation by the head of the input sequence. Returns `none` if the output
is `nil`, or `some (out_hd, op')` where `out_hd` is the head of the output and `op'` is a friendly
operation mapping the tail of the input to the tail of the output. See
`destruct_apply_eq_unfold` for the correctness statement. -/
def FriendlyOperation.unfold {op : Seq α → Seq α} (h : FriendlyOperation op) (hd? : Option α) :
    Option (α × Subtype (@FriendlyOperation α)) :=
  match hd? with
  | none =>
    let t := op nil
    match t.destruct with
    | none => none
    | some (t_hd, t_tl) =>
      some (t_hd, ⟨fun _ ↦ t_tl, FriendlyOperation.const⟩)
  | some s_hd =>
    let s := .cons s_hd nil
    let t := op s
    match t.destruct with
    | none => none
    | some (t_hd, _) =>
      some (t_hd, ⟨fun s_tl ↦ (op (.cons s_hd s_tl)).tail, FriendlyOperation.cons_tail h⟩)

/-- `unfold` correctly decomposes a friendly operation: the head of `op s` depends only on the
head of `s` (and is given by `unfold`), while the tail of `op s` is obtained by applying the
friendly operation returned by `unfold` to the tail of `s`. This gives a coinductive
characterization of `FriendlyOperation`. For the coinduction principle, see
`FriendlyOperation.coind`. -/
theorem FriendlyOperation.destruct_apply_eq_unfold {op : Seq α → Seq α} (h : FriendlyOperation op)
    {s : Seq α} :
    destruct (op s) = (h.unfold s.head).map (fun (hd, op') => (hd, op'.val s.tail)) := by
  unfold unfold
  cases s with
  | nil =>
    generalize op nil = t
    cases t <;> simp
  | cons s_hd s_tl =>
    simp only [Seq.tail_cons, Seq.head_cons]
    generalize ht0 : op (.cons s_hd nil) = t0 at *
    generalize ht : op (.cons s_hd s_tl) = t at *
    have : t0.head = t.head := by
      rw [← ht0, ← ht, FriendlyOperation.op_cons_head_eq h]
    cases t0 with
    | nil =>
      cases t with
      | nil => simp
      | cons => simp at this
    | cons =>
      cases t with
      | nil => simp at this
      | cons => simp_all

/-- If `op` is friendly, then `op s` and `op t` have the same head if `s` and `t`
have the same head. -/
theorem FriendlyOperation.op_head_eq {op : Seq α → Seq α} (h : FriendlyOperation op) {s t : Seq α}
    (h_head : s.head = t.head) : (op s).head = (op t).head := by
  simp only [head_eq_destruct, Option.map_eq_map, h.destruct_apply_eq_unfold, Option.map_map]
    at h_head ⊢
  simp [h_head]
  rfl

theorem FriendlyOperation.of_dist_le_pow {op : Seq α → Seq α}
    (h : ∀ s t n, dist s t ≤ (2⁻¹ : ℝ) ^ n → dist (op s) (op t) ≤ (2⁻¹ : ℝ) ^ n) :
    FriendlyOperation op := by
  rw [friendlyOperation_iff_dist_le_dist]
  intro s t
  by_cases hst : s = t
  · simp [hst]
  obtain ⟨n, hst⟩ := dist_eq_two_inv_pow hst
  grind

/-- Coinduction principle for proving that an operation is friendly. -/
theorem FriendlyOperation.coind (motive : (Seq α → Seq α) → Prop)
    {op : Seq α → Seq α}
    (h_base : motive op)
    (h_step : ∀ op, motive op → ∃ T : Option α → Option (α × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map (fun (hd, op') => (hd, op'.val s.tail))) :
    FriendlyOperation op := by
  apply of_dist_le_pow
  intro s t n hn
  induction n generalizing op s t with
  | zero => simp
  | succ n ih =>
  obtain ⟨T, hT⟩ := h_step _ h_base
  have h_head : s.head = t.head := by
    replace hn : dist s t ≤ 2⁻¹ := by
      apply hn.trans
      simp only [pow_succ, inv_pos, Nat.ofNat_pos, mul_le_iff_le_one_left]
      apply pow_le_one₀ <;> norm_num
    rw [dist_le_half_iff] at hn
    obtain ⟨rfl, rfl⟩ | ⟨hd, s_tl, t_tl, rfl, rfl⟩ := hn <;> rfl
  have hs := hT s
  have ht := hT t
  cases hT_head : T s.head with
  | none =>
    simp only [hT_head, Option.map_none, ← h_head] at hs ht
    simp [hs, ht, destruct_eq_none]
  | some v =>
    obtain ⟨hd, op', h_next⟩ := v
    simp only [hT_head, Option.map_some, ← h_head] at hs ht
    simp only [destruct_eq_cons hs, destruct_eq_cons ht, dist_cons_cons, pow_succ', inv_pos,
      Nat.ofNat_pos, mul_le_mul_iff_right₀, ge_iff_le]
    apply ih h_next
    simpa [dist_eq_half_of_head h_head, pow_succ'] using hn

/-- A generalisation of `FriendlyOperation.coind` which allows using `opf ∘ op'` in the tail
of `op s` where `opf` is friendly and `op'` is a function satisfying `motive`. -/
theorem FriendlyOperation.coind_comp_friend_left {op : Seq α → Seq α}
    (motive : (Seq α → Seq α) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op →
      ∃ T : Option α → Option (α × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map fun (hd, opf, op') => (hd, opf.val <| op'.val s.tail)) :
    FriendlyOperation op := by
  let motive' (op : Seq α → Seq α) : Prop :=
    ∃ opf op', op = opf ∘ op' ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  use fun hd? ↦
    match (T hd?) with
    | none => (h_opf.unfold none).map fun (hd, opf') =>
      (hd, ⟨_, fun _ ↦ opf'.val nil, op, rfl, FriendlyOperation.const, h_op⟩)
    | some (hd, opf', op') => (h_opf.unfold (some hd)).map fun (hd', opf'') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  specialize hT s
  simp only [Function.comp_apply]
  generalize op s = s' at *
  cases s' with
  | nil =>
    symm at hT
    simp at hT
    simp [hT, destruct_apply_eq_unfold h_opf]
    rfl
  | cons s_hd s_tl =>
    simp only [destruct_cons] at hT
    simp only [destruct_apply_eq_unfold h_opf, Seq.tail_cons, Seq.head_cons]
    generalize T s.head = t? at *
    cases t? with
    | none => simp at hT
    | some v =>
      obtain ⟨hd, opf', op'⟩ := v
      simp at hT
      simp [hT]
      rfl

/-- A generalisation of `FriendlyOperation.coind` that allows using `op' ∘ opf` in the tail
of `op s` where `opf` is friendly and `op'` is a function satisfying `motive`. -/
theorem FriendlyOperation.coind_comp_friend_right {op : Seq α → Seq α}
    (motive : (Seq α → Seq α) → Prop)
    (h_base : motive op)
    (h_step : ∀ op, motive op →
      ∃ T : Option α → Option (α × Subtype FriendlyOperation × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map fun (hd, opf, op') => (hd, op'.val <| opf.val s.tail)) :
    FriendlyOperation op := by
  let motive' (op : Seq α → Seq α) : Prop :=
    ∃ opf op', op = op' ∘ opf ∧ FriendlyOperation opf ∧ motive op'
  apply FriendlyOperation.coind motive'
  · exact ⟨_root_.id, op, rfl, FriendlyOperation.id, h_base⟩
  clear h_base op
  rintro _ ⟨opf, op, rfl, h_opf, h_op⟩
  obtain ⟨T, hT⟩ := h_step _ h_op
  -- obtain ⟨F, hF⟩ := FriendlyOperation.destruct h_opf
  use fun hd? ↦
    match (h_opf.unfold hd?) with
    | none => (T none).map fun (hd, opf', op') =>
      (hd, ⟨_, fun _ ↦ opf'.val nil, op', rfl, FriendlyOperation.const, op'.prop⟩)
    | some (hd, opf') => (T (some hd)).map fun (hd', opf'', op') =>
      (hd', ⟨_, opf''.val ∘ opf'.val, op'.val, rfl,
        FriendlyOperation.comp opf''.prop opf'.prop, op'.prop⟩)
  intro s
  simp only [Function.comp_apply]
  have hF := h_opf.destruct_apply_eq_unfold (s := s)
  generalize opf s = s' at *
  cases s' with
  | nil =>
    symm at hF
    simp only [destruct_nil, Option.map_eq_none_iff] at hF
    simp only [hF, Option.map_map]
    specialize hT nil
    simp only [tail_nil, head_nil] at hT
    simp [hT]
    rfl
  | cons s_hd s_tl =>
  simp only [destruct_cons] at hF
  generalize h_opf.unfold s.head = t? at *
  cases t? with
  | none => simp at hF
  | some v =>
  obtain ⟨hd, opf', op'⟩ := v
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hF
  simp only [hF, Option.map_map]
  rw [hT]
  rfl

/-- A generalisation of `Seq.eq_of_bisim'` that allows using a friendly operation in the tail
of the sequences. -/
theorem FriendlyOperationClass.eq_of_bisim {s t : Seq α} {op : γ → Seq α → Seq α}
    [FriendlyOperationClass op]
    (motive : Seq α → Seq α → Prop)
    (base : motive s t)
    (step : ∀ u v, motive u v → (u = v) ∨
      ∃ hd u' v' c, u = cons hd (op c u') ∧ v = cons hd (op c v') ∧
        motive u' v') :
    s = t := by
  suffices dist s t = 0 by simpa using this
  suffices ∀ n, dist s t ≤ (2⁻¹ : ℝ) ^ n by
    apply eq_of_le_of_ge
    · apply ge_of_tendsto' (x := Filter.atTop) _ this
      rw [tendsto_pow_atTop_nhds_zero_iff]
      norm_num
    · simp
  intro n
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
    obtain step | ⟨hd, u, v, c, rfl, rfl, h_next⟩ := step s t base
    · simp [step]
    simp only [dist_cons_cons]
    specialize ih h_next
    calc
      _ ≤ 2⁻¹ * dist u v := by
        gcongr
        exact (FriendlyOperationClass.friend _).dist_le
      _ ≤ _ := by
        grw [ih, pow_succ']

end Tactic.ComputeAsymptotics.Seq
