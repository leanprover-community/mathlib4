import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Data.Seq.Basic

namespace Stream'.Seq

open scoped UniformConvergence

variable {α β γ : Type*}

noncomputable local instance : MetricSpace (Stream' α) :=
  @PiNat.metricSpace (fun _ ↦ α) (fun _ ↦ ⊥) (fun _ ↦ discreteTopology_bot _)

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

-- TODO: upstream to PiNat
local instance : BoundedSpace (Stream' α) := by
  rw [Metric.boundedSpace_iff]
  use 1
  intro s t
  by_cases h : s = t
  · simp [h]
  rw [PiNat.dist_eq_of_ne h]
  bound

local instance : BoundedSpace (Seq α) :=
  instBoundedSpaceSubtype

@[simp]
theorem stream_dist_cons (x : α) (s t : Stream' α) :
    dist (Stream'.cons x s) (Stream'.cons x t) = 2⁻¹ * dist s t := by
  by_cases h : s = t
  · simp [h]
  have h' : x :: s ≠ x :: t := by
    contrapose! h
    apply Stream'.cons_injective2 at h
    simpa using h
  rw [PiNat.dist_eq_of_ne h, PiNat.dist_eq_of_ne h']
  suffices PiNat.firstDiff (x :: s) (x :: t) = PiNat.firstDiff s t + 1 by
    simp [this, pow_succ]
    field_simp
  simp [PiNat.firstDiff, h, h']
  generalize_proofs p1 p2
  convert Nat.find_comp_succ _ _ _
  simp [Stream'.cons]

@[simp]
theorem dist_cons (x : α) (s t : Seq α) : dist (cons x s) (cons x t) = 2⁻¹ * dist s t := by
  rw [Subtype.dist_eq]
  simp
  rw [Subtype.dist_eq]

class FriendOperation (f : γ → Seq α → Seq α) : Prop where
  lipschitz : ∀ c : γ, LipschitzWith 1 (f c)

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
    simp [UniformFun.toFun, UniformFun.ofFun, T]
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
          simp [UniformFun.dist_def]
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
  simp [T]
  cases hb : F b with
  | none =>
    simp
  | some v =>
    obtain ⟨a, c, b'⟩ := v
    simp
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

-- TODO
-- theorem FriendOperation.coind (M : (γ → Seq α → Seq α) → Prop)
--     (hM : ∀ op, M op → ∃ T : γ → Option α → Option ()

--     )
--     (h_head : ∀ op, M op → ∃ H : γ → Option α → Option α, ∀ c s, head (op c s) = H c (head s))
--     (h_tail : ∀ op, M op → ∃ op', M op' ∧ ∀ c s, tail (op c s) = op' c (tail s))
--     : FriendOperation op := by
--   sorry

end Stream'.Seq
