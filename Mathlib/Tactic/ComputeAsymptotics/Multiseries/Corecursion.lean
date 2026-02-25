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

/-- A function on sequences is called a "friend" if any `n`-prefix of its output depends only on
the `n`-prefix of the input. Such functions can be used in the tail of (non-primitive) corecursive
definitions. -/
def FriendlyOperation (op : Seq α → Seq α) : Prop := LipschitzWith 1 op

/-- A family of friendly operations on sequences indexed by a type `γ`. -/
class FriendlyOperationClass (F : γ → Seq α → Seq α) : Prop where
  friend : ∀ c : γ, FriendlyOperation (F c)

theorem FriendlyOperation.id : FriendlyOperation (id : Seq α → Seq α) :=
  LipschitzWith.id

theorem FriendlyOperation.comp {op op' : Seq α → Seq α}
    (h : FriendlyOperation op) (h' : FriendlyOperation op') :
    FriendlyOperation (op ∘ op') := by
  rw [FriendlyOperation] at h h' ⊢
  convert h.comp h'
  simp

theorem FriendlyOperation.const {s : Seq α} : FriendlyOperation (fun _ ↦ s) := by
  simp [FriendlyOperation, lipschitzWith_iff_dist_le_mul]

theorem FriendlyOperationClass.comp (F : γ → Seq α → Seq α) (g : γ' → γ)
    [h : FriendlyOperationClass F] : FriendlyOperationClass (fun c ↦ F (g c)) := by
  grind [FriendlyOperationClass]

theorem FriendlyOperation.ite {op₁ op₂ : Seq α → Seq α}
    (h₁ : FriendlyOperation op₁) (h₂ : FriendlyOperation op₂)
    {P : Option α → Prop} [DecidablePred P] :
    FriendlyOperation (fun s ↦ if P s.head then op₁ s else op₂ s) := by
  rw [FriendlyOperation, lipschitzWith_iff_dist_le_mul, NNReal.coe_one] at h₁ h₂ ⊢
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

end Tactic.ComputeAsymptotics.Seq
