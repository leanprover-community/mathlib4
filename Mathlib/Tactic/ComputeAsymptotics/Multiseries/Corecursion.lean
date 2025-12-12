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

theorem dist_cons_cons_eq_one {x y : α} {s t : Seq α} (h : x ≠ y) :
    dist (cons x s) (cons y t) = 1 := by
  rw [Subtype.dist_eq, PiNat.dist_eq_of_ne]
  · convert pow_zero _
    simp only [val_cons, PiNat.firstDiff, ne_eq, Classical.dite_not, dite_eq_left_iff,
      Nat.find_eq_zero]
    intro h'
    simpa [Stream'.cons]
  · rw [Subtype.coe_ne_coe, ne_eq, cons_eq_cons]
    simp [h]

@[simp]
theorem dist_cons_nil (x : α) (s : Seq α) : dist (cons x s) nil = 1 := by
  rw [Subtype.dist_eq, PiNat.dist_eq_of_ne]
  · convert pow_zero _
    simp only [val_cons, PiNat.firstDiff, ne_eq, Classical.dite_not, dite_eq_left_iff,
      Nat.find_eq_zero]
    intro h'
    simp [Stream'.cons]
  · rw [Subtype.coe_ne_coe, ne_eq]
    exact cons_ne_nil

@[simp]
theorem dist_nil_cons (x : α) (s : Seq α) : dist nil (cons x s) = 1 := by
  rw [dist_comm]
  simp

class FriendOperation (f : γ → Seq α → Seq α) : Prop where
  lipschitz : ∀ c : γ, LipschitzWith 1 (f c)

theorem FriendOperation.comp (f : γ → Seq α → Seq α) (g : γ' → γ)
    [h : FriendOperation f] : FriendOperation (fun c ↦ f (g c)) := by
  grind [FriendOperation]

theorem FriendOperation.dist_le {op : γ → Seq α → Seq α} [h : FriendOperation op]
    {c : γ} {s t : Seq α} : dist (op c s) (op c t) ≤ dist s t := by
  have := h.lipschitz c
  rw [lipschitzWith_iff_dist_le_mul] at this
  specialize this s t
  simpa using this

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
    [h : FriendOperation op] :
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
          have := h.lipschitz c
          rw [lipschitzWith_iff_dist_le_mul] at this
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
    [FriendOperation op] :
  β → Seq α := (FriendOperation.exists_fixed_point F op).choose

theorem gcorec_nil {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendOperation op] {b : β}
    (h : F b = none) :
    gcorec F op b = nil := by
  have := (FriendOperation.exists_fixed_point F op).choose_spec b
  simpa [h] using this

theorem gcorec_some {F : β → Option (α × γ × β)} {op : γ → Seq α → Seq α}
    [FriendOperation op] {b : β}
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

attribute [-simp] inv_pow in
theorem FriendOperation.coind_aux (motive : (Seq α → Seq α) → Prop)
    (h_step : ∀ op, motive op → ∃ (H : Option α → Option α) (op' : Seq α → Seq α),
      motive op' ∧ ∀ s, head (op s) = H (head s) ∧
      tail (op s) = op' (tail s)) (op : Seq α → Seq α)
    (h_base : motive op) :
    LipschitzWith 1 op := by
  rw [lipschitzWith_iff_dist_le_mul]
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
  by_cases! h : op s = op t
  · simp [h]
  obtain ⟨H, op', h_tl, h_head⟩ := h_step _ h_base
  obtain ⟨hs_head, hs_tail⟩ := h_head s
  obtain ⟨ht_head, ht_tail⟩ := h_head t
  cases s with
  | nil =>
    cases t
    · simp at h
    · simp at hn
  | cons s_hd s_tl =>
  cases t with
  | nil => simp at hn
  | cons t_hd t_tl =>
  by_cases! h_head : s_hd ≠ t_hd
  · simp [dist_cons_cons_eq_one h_head] at hn
  subst h_head
  have h_head : (op (cons s_hd s_tl)).head = (op (cons s_hd t_tl)).head := by
    simp [hs_head, ht_head]
  generalize op (cons s_hd s_tl) = x at *
  generalize op (cons s_hd t_tl) = y at *
  cases x <;> cases y <;> simp at h h_head
  rename_i x_hd x_tl y_hd y_tl
  simp only [h_head, forall_const, tail_cons, dist_cons_cons, pow_succ', inv_pos, Nat.ofNat_pos,
    mul_le_mul_iff_right₀, ge_iff_le] at h hs_tail ht_tail ⊢
  rw [hs_tail, ht_tail]
  apply ih _ h_tl
  simpa [pow_succ'] using hn

theorem FriendOperation.coind (motive : (Seq α → Seq α) → Prop)
    (h_step : ∀ op, motive op → ∃ (H : Option α → Option α) (op' : Seq α → Seq α),
      motive op' ∧ ∀ s, head (op s) = H (head s) ∧
      tail (op s) = op' (tail s)) (op : γ → Seq α → Seq α)
    (h_base : ∀ c, motive (op c)) :
    FriendOperation op := by
  constructor
  intro c
  apply FriendOperation.coind_aux _ h_step _ (by grind)

theorem FriendOperation.eq_of_bisim {s t : Seq α} {op : γ → Seq α → Seq α} [FriendOperation op]
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
      _ ≤ _ := by
        grw [ih, pow_succ']

end Stream'.Seq
