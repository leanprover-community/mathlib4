/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Data.Seq.Basic

/-!
# Non-primitive corecursion for sequences

https://arxiv.org/pdf/1501.05425
-/

@[expose] public section

namespace Stream'.Seq

open scoped UniformConvergence

variable {α β γ γ' : Type*}


noncomputable local instance instMetricSpaceStream' : MetricSpace (Stream' α) :=
  @PiNat.metricSpace (fun _ ↦ α) (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)

noncomputable local instance : MetricSpace (Seq α) :=
  Subtype.metricSpace

local instance instCompleteSpaceStream' : CompleteSpace (Stream' α) :=
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

theorem Stream'.dist_le_one (s t : Stream' α) : dist s t ≤ 1 := by
  by_cases h : s = t
  · simp [h]
  rw [PiNat.dist_eq_of_ne h]
  bound

@[simp]
theorem dist_le_one (s t : Seq α) : dist s t ≤ 1 := by
  rw [Subtype.dist_eq]
  apply Stream'.dist_le_one

-- TODO: upstream to PiNat
local instance instBoundedSpaceStream' : BoundedSpace (Stream' α) := by
  rw [Metric.boundedSpace_iff]
  use 1
  apply Stream'.dist_le_one

local instance : BoundedSpace (Seq α) :=
  instBoundedSpaceSubtype

theorem dist_eq_two_inv_pow {s t : Seq α} (h : s ≠ t) : ∃ n, dist s t = 2⁻¹ ^ n := by
  rw [Subtype.dist_eq, PiNat.dist_eq_of_ne (Subtype.coe_ne_coe.mpr h)]
  simp

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

def FriendOperation (op : Seq α → Seq α) : Prop := LipschitzWith 1 op

class FriendOperationClass (F : γ → Seq α → Seq α) : Prop where
  friend : ∀ c : γ, FriendOperation (F c)

theorem FriendOperation.id : FriendOperation (id : Seq α → Seq α) :=
  LipschitzWith.id

theorem FriendOperation.comp {op op' : Seq α → Seq α}
    (h : FriendOperation op) (h' : FriendOperation op') :
    FriendOperation (op ∘ op') := by
  rw [FriendOperation] at h h' ⊢
  convert h.comp h'
  simp

theorem FriendOperation.const {s : Seq α} : FriendOperation (fun _ ↦ s) := by
  simp [FriendOperation, lipschitzWith_iff_dist_le_mul]

theorem FriendOperationClass.comp (F : γ → Seq α → Seq α) (g : γ' → γ)
    [h : FriendOperationClass F] : FriendOperationClass (fun c ↦ F (g c)) := by
  grind [FriendOperationClass]

theorem FriendOperation.ite {op₁ op₂ : Seq α → Seq α}
    (h₁ : FriendOperation op₁) (h₂ : FriendOperation op₂)
    {P : Option α → Prop} [DecidablePred P] :
    FriendOperation (fun s ↦ if P s.head then op₁ s else op₂ s) := by
  rw [FriendOperation, lipschitzWith_iff_dist_le_mul, NNReal.coe_one] at h₁ h₂ ⊢
  intro s t
  by_cases! h_head : s.head ≠ t.head
  · simp [dist_eq_one_of_head h_head]
  grind

theorem FriendOperation.dist_le {op : Seq α → Seq α} (h : FriendOperation op)
    {s t : Seq α} : dist (op s) (op t) ≤ dist s t := by
  rw [FriendOperation, lipschitzWith_iff_dist_le_mul] at h
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

theorem FriendOperation.exists_fixed_point (F : β → Option (α × γ × β)) (op : γ → Seq α → Seq α)
    [h : FriendOperationClass op] :
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
          rw [FriendOperation, lipschitzWith_iff_dist_le_mul] at this
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

noncomputable def gcorec (F : β → Option (α × γ × β)) (op : γ → Seq α → Seq α)
    [FriendOperationClass op] :
  β → Seq α := (FriendOperation.exists_fixed_point F op).choose

theorem gcorec_nil {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendOperationClass op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  have := (FriendOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using this

theorem gcorec_some {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendOperationClass op] {b : β}
    {a : α} {c : γ} {b' : β}
    (h : F b = some (a, c, b')) :
    gcorec F op b = Seq.cons a (op c (gcorec F op b')) := by
  have := (FriendOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using this

@[local simp]
lemma inv_two_pow_succ_lt_one (n : ℕ) : ¬ 1 ≤ (2⁻¹ : ℝ) ^ (n + 1) := by
  simp only [not_le]
  rw [pow_succ]
  refine mul_lt_one_of_nonneg_of_lt_one_right (pow_le_one₀ ?_ ?_) ?_ ?_
  all_goals norm_num

theorem FriendOperation.head_eq {op : Seq α → Seq α} (h : FriendOperation op) {a : α}
    {s t : Seq α} : head (op <| cons a s) = head (op <| cons a t) := by
  rw [FriendOperation, lipschitzWith_iff_dist_le_mul] at h
  specialize h (cons a s) (cons a t)
  simp only [NNReal.coe_one, dist_cons_cons, one_mul] at h
  replace h : dist (op (cons a s)) (op (cons a t)) ≤ 2⁻¹ := by
    apply h.trans
    simp
  cases hs : op (cons a s) with
  | nil =>
    cases ht : op (cons a t) with
    | nil => simp
    | cons t_hd t_tl => norm_num [hs, ht] at h
  | cons s_hd s_tl =>
    cases ht : op (cons a t) with
    | nil => norm_num [hs, ht] at h
    | cons t_hd t_tl =>
      simp only [head_cons, Option.some.injEq]
      by_contra! h_hd
      rw [hs, ht, dist_cons_cons_eq_one h_hd] at h
      norm_num at h

theorem FriendOperation.cons_tail {op : Seq α → Seq α} {hd : α} (h : FriendOperation op) :
    FriendOperation (fun s ↦ (op (cons hd s)).tail) := by
  simp_rw [FriendOperation, lipschitzWith_iff_dist_le_mul, NNReal.coe_one, one_mul] at h ⊢
  intro x y
  specialize h (cons hd x) (cons hd y)
  simp only [dist_cons_cons] at h
  cases hx : op (cons hd x) with
  | nil =>
    cases hy : op (cons hd y) with
    | nil => simp
    | cons y_hd y_tl =>
      contrapose! h
      grw [hx, hy, dist_le_one]
      norm_num
  | cons x_hd x_tl =>
    cases hy : op (cons hd y) with
    | nil =>
      contrapose! h
      grw [hx, hy, dist_le_one]
      norm_num
    | cons y_hd y_tl =>
      by_cases! h_hd : x_hd ≠ y_hd
      · contrapose! h
        grw [hx, hy, dist_cons_cons_eq_one h_hd, dist_le_one]
        norm_num
      simpa [hx, hy, h_hd] using h

theorem FriendOperation.destruct {op : Seq α → Seq α} (h : FriendOperation op) :
    ∃ T : Option α → Option (α × Subtype FriendOperation),
      ∀ s, destruct (op s) = (T s.head).map (fun (hd, op') => (hd, op'.val s.tail)) := by
  use fun hd? ↦
    match hd? with
    | none =>
      let t := op nil
      match t.destruct with
      | none => none
      | some (t_hd, t_tl) =>
        some (t_hd, ⟨fun _ ↦ t_tl, FriendOperation.const⟩)
    | some s_hd =>
      let s := cons s_hd nil
      let t := op s
      match t.destruct with
      | none => none
      | some (t_hd, t_tl) =>
        some (t_hd, ⟨fun s_tl ↦ (op (cons s_hd s_tl)).tail, FriendOperation.cons_tail h⟩)
  intro s
  cases s with
  | nil =>
    generalize op nil = t
    cases t <;> simp
  | cons s_hd s_tl =>
    simp only [tail_cons, head_cons]
    generalize ht0 : op (cons s_hd nil) = t0 at *
    generalize ht : op (cons s_hd s_tl) = t at *
    have : t0.head = t.head := by
      rw [← ht0, ← ht, FriendOperation.head_eq h]
    cases t0 with
    | nil =>
      cases t with
      | nil => simp
      | cons => simp at this
    | cons =>
      cases t with
      | nil => simp at this
      | cons => simp_all

theorem FriendOperation.head_eq_head {op : Seq α → Seq α} (h : FriendOperation op) {s t : Seq α}
    (h_head : s.head = t.head) : (op s).head = (op t).head := by
  obtain ⟨T, hT⟩ := FriendOperation.destruct h
  have hs := hT s
  have ht := hT t
  simp [Stream'.Seq.head_eq_destruct, hs, ht] at h_head ⊢
  simp [h_head]
  rfl

theorem FriendOperation.head_eq_head_of_cons {op : Seq α → Seq α} (h : FriendOperation op) {a : α}
    {s t : Seq α} : (op (cons a s)).head = (op (cons a t)).head := by
  apply FriendOperation.head_eq_head h
  simp

attribute [-simp] inv_pow in
theorem FriendOperation.coind (motive : (Seq α → Seq α) → Prop)
    (h_step : ∀ op, motive op → ∃ T : Option α → Option (α × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map (fun (hd, op') => (hd, op'.val s.tail)))
    (op : Seq α → Seq α)
    (h_base : motive op) :
    FriendOperation op := by
  rw [FriendOperation, lipschitzWith_iff_dist_le_mul]
  intro s t
  simp only [NNReal.coe_one, one_mul]
  suffices ∀ n, dist s t ≤ (2⁻¹ : ℝ) ^ n → dist (op s) (op t) ≤ (2⁻¹ : ℝ) ^ n by
    by_cases h : s = t
    · simp [h]
    obtain ⟨n, hst⟩ := dist_eq_two_inv_pow h
    rw [hst] at this ⊢
    apply this
    rfl
  intro n hn
  induction n generalizing op s t with
  | zero => simp
  | succ n ih =>
  specialize h_step _ h_base
  obtain ⟨T, hT⟩ := h_step
  have hs := hT s
  have ht := hT t
  by_cases! h_head : s.head ≠ t.head
  · contrapose! hn
    norm_num [pow_succ, dist_eq_one_of_head h_head]
    refine mul_lt_one_of_nonneg_of_lt_one_right (pow_le_one₀ ?_ ?_) ?_ ?_
    all_goals norm_num
  cases hT_head : T s.head with
  | none =>
    simp only [hT_head, Option.map_none, ← h_head] at hs ht
    apply Stream'.Seq.destruct_eq_none at hs
    apply Stream'.Seq.destruct_eq_none at ht
    simp [hs, ht]
  | some v =>
    obtain ⟨hd, op', h_next⟩ := v
    simp only [hT_head, Option.map_some, ← h_head] at hs ht
    apply Stream'.Seq.destruct_eq_cons at hs
    apply Stream'.Seq.destruct_eq_cons at ht
    simp only [hs, ht, dist_cons_cons, pow_succ', inv_pos, Nat.ofNat_pos, mul_le_mul_iff_right₀,
      ge_iff_le]
    apply ih _ h_next
    simpa [dist_eq_half_of_head h_head, pow_succ'] using hn

theorem FriendOperationClass.coind (motive : (Seq α → Seq α) → Prop)
    (h_step : ∀ op, motive op → ∃ T : Option α → Option (α × Subtype motive),
      ∀ s, (op s).destruct = (T s.head).map (fun (hd, op') => (hd, op'.val s.tail)))
    (op : γ → Seq α → Seq α) (h_base : ∀ c, motive (op c)) :
    FriendOperationClass op := by
  constructor
  intro c
  apply FriendOperation.coind _ h_step _ (by grind)

-- TODO: prove using eq_of_bisim
theorem FriendOperationClass.eq_of_bisim {s t : Seq α} {op : γ → Seq α → Seq α}
    [FriendOperationClass op]
    (motive : Seq α → Seq α → Prop)
    (base : motive s t)
    (step : ∀ s t, motive s t → (s = t) ∨
      ∃ hd s' t' c, s = cons hd (op c s') ∧ t = cons hd (op c t') ∧
        motive s' t') :
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
    specialize step s t base
    obtain step | ⟨hd, s', t', c, rfl, rfl, h_next⟩ := step
    · simp [step]
    simp only [dist_cons_cons]
    specialize ih h_next
    calc
      _ ≤ 2⁻¹ * dist s' t' := by
        gcongr
        apply FriendOperation.dist_le
        apply FriendOperationClass.friend
      _ ≤ _ := by
        grw [ih, pow_succ']

end Stream'.Seq
