/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
# Maximal Flows on Smooth Manifolds

Generic smooth manifold flow theory: the flow semigroup property, maximal flow domains,
and Lee's Theorem 9.12 (continuity of the maximal flow).
-/

open Set Bundle ContDiff Manifold Trivialization

/-- The semigroup/cocycle property of flows: `Φ(t + s, x) = Φ(s, Φ(t, x))`.
This follows from uniqueness of integral curves. -/
theorem flow_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M]
    {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I M)))
    {Φ : ℝ → M → M}
    (hΦ : ∀ x, IsMIntegralCurve (fun t => Φ t x) X)
    (hΦ_init : ∀ x, Φ 0 x = x) :
    ∀ t s x, Φ (t + s) x = Φ s (Φ t x) := by
  intro t s x
  have h_unique : ∀ (γ γ' : ℝ → M), IsMIntegralCurve γ X → IsMIntegralCurve γ' X →
      γ 0 = γ' 0 → γ = γ' :=
    fun γ γ' a a_1 a_2 => isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hX a a_1 a_2
  specialize h_unique (fun u => Φ (u + t) x) (fun u => Φ u (Φ t x)) ?_ ?_ ?_
  · convert IsMIntegralCurve.comp_add (hΦ x) t using 1
  · exact hΦ _
  · simp [hΦ_init]
  · simpa [add_comm] using congr_fun h_unique s

section Lee912

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M]
  (V : ∀ x : M, TangentSpace I x)
  (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)))

def flowDomain (p : M) : Set ℝ :=
  ⋃ (J : Set ℝ) (_ : IsOpen J) (_ : (0 : ℝ) ∈ J) (_ : IsConnected J)
    (_ : ∃ γ : ℝ → M, γ 0 = p ∧ IsMIntegralCurveOn γ V J), J

def flowSet : Set (ℝ × M) :=
  {tp | tp.1 ∈ flowDomain V tp.2}

omit [CompleteSpace E] [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M] in
private lemma flowDomain_exists_integralCurve (p : M) (t : ℝ) (ht : t ∈ flowDomain V p) :
    ∃ γ : ℝ → M, γ 0 = p ∧ ∃ J : Set ℝ, IsOpen J ∧ (0 : ℝ) ∈ J ∧ t ∈ J ∧
    IsConnected J ∧ IsMIntegralCurveOn γ V J := by
  simp only [flowDomain, Set.mem_iUnion] at ht
  obtain ⟨J, hJ_open, h0J, hJ_conn, hJ_curve, htJ⟩ := ht
  obtain ⟨γ, hγ_init, hγ_int⟩ := hJ_curve
  exact ⟨γ, hγ_init, J, hJ_open, h0J, htJ, hJ_conn, hγ_int⟩

noncomputable def maximalFlowAt (p : M) : flowDomain V p → M :=
  fun ⟨t, ht⟩ => (flowDomain_exists_integralCurve V p t ht).choose t

omit [CompleteSpace E] in
private lemma maximalFlowAt_eq_of_isMIntegralCurveOn (p : M) (t : ℝ) (ht : t ∈ flowDomain V p)
    {γ : ℝ → M} {J : Set ℝ} (hJ_open : IsOpen J) (hJ_conn : IsConnected J)
    (h0J : (0 : ℝ) ∈ J) (htJ : t ∈ J)
    (hγ_init : γ 0 = p) (hγ_int : IsMIntegralCurveOn γ V J)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    maximalFlowAt V p ⟨t, ht⟩ = γ t := by
  set γ' := (flowDomain_exists_integralCurve V p t ht).choose with hγ'_def
  obtain ⟨hγ'_init, J', hJ'_open, h0J', htJ', hJ'_conn, hγ'_int⟩ :=
    (flowDomain_exists_integralCurve V p t ht).choose_spec
  have hJ'_sub : Icc (min 0 t) (max 0 t) ⊆ J' :=
    hJ'_conn.Icc_subset
      (by rcases min_choice 0 t with h | h <;> rw [h] <;> assumption)
      (by rcases max_choice 0 t with h | h <;> rw [h] <;> assumption)
  have hJ_sub : Icc (min 0 t) (max 0 t) ⊆ J :=
    hJ_conn.Icc_subset
      (by rcases min_choice 0 t with h | h <;> rw [h] <;> assumption)
      (by rcases max_choice 0 t with h | h <;> rw [h] <;> assumption)
  have hJJ'_open : IsOpen (J' ∩ J) := hJ'_open.inter hJ_open
  have hmin_mem : min 0 t ∈ J' ∩ J := ⟨hJ'_sub (left_mem_Icc.mpr  inf_left_le_sup_left),
                                        hJ_sub (left_mem_Icc.mpr  inf_left_le_sup_left)⟩
  have hmax_mem : max 0 t ∈ J' ∩ J := ⟨hJ'_sub (right_mem_Icc.mpr inf_left_le_sup_left),
                                        hJ_sub (right_mem_Icc.mpr inf_left_le_sup_left)⟩
  obtain ⟨l, hl, hlsub⟩ := exists_Ioc_subset_of_mem_nhds
    (hJJ'_open.mem_nhds hmin_mem) ⟨min 0 t - 1, by linarith⟩
  obtain ⟨u, hu, husub⟩ := exists_Ico_subset_of_mem_nhds
    (hJJ'_open.mem_nhds hmax_mem) ⟨max 0 t + 1, by linarith⟩
  have h0_mem : (0 : ℝ) ∈ Ioo l u :=
    ⟨lt_of_lt_of_le hl (min_le_left 0 t), lt_of_le_of_lt (le_max_left 0 t) hu⟩
  have ht_mem : t ∈ Ioo l u :=
    ⟨lt_of_lt_of_le hl (min_le_right 0 t), lt_of_le_of_lt (le_max_right 0 t) hu⟩
  have hIoo_sub : Ioo l u ⊆ J' ∩ J := by
    intro x hx
    rcases le_or_gt x (min 0 t) with h | h
    · exact hlsub ⟨hx.1, h⟩
    · rcases le_or_gt (max 0 t) x with h' | h'
      · exact husub ⟨h', hx.2⟩
      · exact ⟨hJ'_sub (Ioo_subset_Icc_self ⟨h, h'⟩),
               hJ_sub (Ioo_subset_Icc_self ⟨h, h'⟩)⟩
  have huniq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (mem_Ioo.mpr ⟨h0_mem.1, h0_mem.2⟩)
    hV
    (γ := γ') (γ' := γ)
    (hγ'_int.mono (fun x hx => (hIoo_sub hx).1))
    (hγ_int.mono (fun x hx => (hIoo_sub hx).2))
    (hγ'_init.trans hγ_init.symm)
  exact huniq ht_mem

omit [T2Space M] in
lemma zero_mem_flowDomain (p : M)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    (0 : ℝ) ∈ flowDomain V p := by
  obtain ⟨u, hu_mem, ε, hε, γ, hγ⟩ :=
    exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt
      (t₀ := 0) (x₀ := p) hV.contMDiffAt BoundarylessManifold.isInteriorPoint
  simp only [flowDomain, Set.mem_iUnion]
  have h1 := (hγ p (mem_of_mem_nhds hu_mem))
  rw [zero_sub ε, AddZeroClass.zero_add ε] at h1
  exact ⟨Ioo (-ε) ε, isOpen_Ioo, mem_Ioo.mpr ⟨neg_lt_zero.mpr hε, hε⟩,
    isConnected_Ioo (neg_lt_zero.mpr hε |>.trans hε),
    ⟨fun t => γ (p, t), h1.1, h1.2.1⟩, mem_Ioo.mpr ⟨neg_lt_zero.mpr hε, hε⟩⟩

lemma maximalFlowAt_zero (p : M)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    maximalFlowAt V p ⟨0, zero_mem_flowDomain V p hV⟩ = p := by
  obtain ⟨u, hu_mem, ε, hε, γ, hγ⟩ :=
    exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt
      (t₀ := 0) (x₀ := p) hV.contMDiffAt BoundarylessManifold.isInteriorPoint
  have hγ_init := (hγ p (mem_of_mem_nhds hu_mem)).1
  have hγ_int := (hγ p (mem_of_mem_nhds hu_mem)).2.1
  have hγ_int' : IsMIntegralCurveOn (fun x => γ (p, x)) V (Ioo (-ε) ε) := by
    rw [zero_sub ε, AddZeroClass.zero_add ε] at hγ_int
    exact hγ_int
  rw [maximalFlowAt_eq_of_isMIntegralCurveOn V p 0 (zero_mem_flowDomain V p hV)
    isOpen_Ioo
    (isConnected_Ioo (neg_lt_zero.mpr hε |>.trans hε))
    (mem_Ioo.mpr ⟨neg_lt_zero.mpr hε, hε⟩)
    (mem_Ioo.mpr ⟨neg_lt_zero.mpr hε, hε⟩)
    (γ := fun t => γ (p, t))
    (by exact hγ_init)
    (by intro t ht; exact hγ_int' t ht)
    hV]
  exact hγ_init

omit [CompleteSpace E] [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M] in
lemma isOpen_flowDomain (p : M) : IsOpen (flowDomain V p) :=
  isOpen_iUnion (fun _J => isOpen_iUnion (fun hJ_open => isOpen_iUnion (fun _ =>
    isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => hJ_open)))))

noncomputable def maximalFlowAt' (p : M) (t : ℝ) : M := by
  classical
  exact if ht : t ∈ flowDomain V p then maximalFlowAt V p ⟨t, ht⟩ else p

omit [CompleteSpace E] in
lemma maximalFlowAt_isMIntegralCurveOn (p : M)
    (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    IsMIntegralCurveOn (maximalFlowAt' V p) V (flowDomain V p) := by
  intro t ht
  have heq : maximalFlowAt' V p t = maximalFlowAt V p ⟨t, ht⟩ := by
    simp [maximalFlowAt', ht]
  obtain ⟨γ, hγ_init, J, hJ_open, h0J, htJ, hJ_conn, hγ_int⟩ :=
    flowDomain_exists_integralCurve V p t ht
  have heq2 : maximalFlowAt V p ⟨t, ht⟩ = γ t :=
    maximalFlowAt_eq_of_isMIntegralCurveOn V p t ht hJ_open hJ_conn h0J htJ hγ_init hγ_int hV
  rw [heq, heq2]
  apply ((hγ_int t htJ).mono_of_mem_nhdsWithin
      (nhdsWithin_le_nhds (hJ_open.mem_nhds htJ))).congr_of_eventuallyEq
  · filter_upwards [nhdsWithin_le_nhds (hJ_open.mem_nhds htJ)] with s hsJ
    have hsD : s ∈ flowDomain V p := by
      simp only [flowDomain, Set.mem_iUnion]
      exact ⟨J, hJ_open, h0J, hJ_conn, ⟨γ, hγ_init, hγ_int⟩, hsJ⟩
    simp only [maximalFlowAt', dif_pos hsD]
    exact maximalFlowAt_eq_of_isMIntegralCurveOn V p s hsD hJ_open hJ_conn h0J hsJ hγ_init hγ_int hV
  · simp [maximalFlowAt', dif_pos ht, heq2]

omit [CompleteSpace E] [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M] in
lemma isPreconnected_flowDomain (p : M) : IsPreconnected (flowDomain V p) := by
  have : flowDomain V p = ⋃₀ {J | IsOpen J ∧ IsConnected J ∧ (0 : ℝ) ∈ J ∧
      ∃ γ : ℝ → M, γ 0 = p ∧ IsMIntegralCurveOn γ V J} := by
    ext t
    simp only [flowDomain, Set.mem_iUnion, Set.mem_sUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨J, hJ_open, h0J, hJ_conn, ⟨γ, hγ_init, hγ_int⟩, htJ⟩
      exact ⟨J, ⟨hJ_open, hJ_conn, h0J, γ, hγ_init, hγ_int⟩, htJ⟩
    · rintro ⟨J, ⟨hJ_open, hJ_conn, h0J, γ, hγ_init, hγ_int⟩, htJ⟩
      exact ⟨J, hJ_open, h0J, hJ_conn, ⟨γ, hγ_init, hγ_int⟩, htJ⟩
  rw [this]
  apply isPreconnected_sUnion 0
  · intro s hs
    exact hs.2.2.1
  · intro s hs
    exact hs.2.1.isPreconnected

end Lee912

section Lee912_lee

/-! ### Lee Theorem 9.12 — continuity part

  We follow Lee, *Introduction to Smooth Manifolds*, proof of Theorem 9.12,
  establishing that `flowSet V` is open and `maximalFlowAt' V` is continuous on it.

  **Continuity only**: Lee proves smoothness; we prove continuity, because
  `exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt` (Winston's lemma)
  supplies only a continuous (not smooth) joint flow.  The proof structure is
  identical to Lee's.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [BoundarylessManifold I M] [T2Space M]
  (V : ∀ x : M, TangentSpace I x)
  (hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M)))

def W_lee (_hV : ContMDiff I I.tangent 1 (fun x => (⟨x, V x⟩ : TangentBundle I M))) :
    Set (ℝ × M) :=
  {tp | ∃ J : Set ℝ, ∃ U : Set M,
      IsOpen J ∧ IsConnected J ∧ IsOpen U ∧
      tp.1 ∈ J ∧ tp.2 ∈ U ∧
      (0 : ℝ) ∈ J ∧
      J ×ˢ U ⊆ flowSet V ∧
      ContinuousOn (fun q : ℝ × M => maximalFlowAt' V q.2 q.1) (J ×ˢ U)}

lemma isOpen_W_lee : IsOpen (W_lee V hV) := by
  apply isOpen_iff_mem_nhds.mpr
  intro ⟨t, p⟩ ht
  obtain ⟨J, U, hJ_open, hJ_conn, hU_open, htJ, hpU, h0J, hJU, hcont⟩ := ht
  apply Filter.mem_of_superset
    (by rw [nhds_prod_eq];
        exact Filter.prod_mem_prod (hJ_open.mem_nhds htJ) (hU_open.mem_nhds hpU))
  intro ⟨t', p'⟩ ⟨ht', hp'⟩
  exact ⟨J, U, hJ_open, hJ_conn, hU_open, ht', hp', h0J, hJU, hcont⟩

private lemma mem_W_lee_zero_lee (p : M) : (0, p) ∈ W_lee V hV := by
  obtain ⟨u, hu, ε, hε, γ, hγ⟩ :=
    exists_mem_nhds_isMIntegralCurveOn_Ioo_of_contMDiffAt
      (t₀ := 0) (x₀ := p) hV.contMDiffAt BoundarylessManifold.isInteriorPoint
  refine ⟨Ioo (-ε) ε, interior u,
      isOpen_Ioo, isConnected_Ioo (by linarith), isOpen_interior,
      mem_Ioo.mpr ⟨by linarith, hε⟩,
      mem_interior_iff_mem_nhds.mpr hu,
      mem_Ioo.mpr ⟨by linarith, hε⟩, ?_, ?_⟩
  · intro ⟨t, q⟩ ⟨ht, hq⟩
    have hq' : q ∈ u := interior_subset hq
    simp only [flowSet, Set.mem_setOf_eq, flowDomain, Set.mem_iUnion]
    exact ⟨Ioo (-ε) ε, isOpen_Ioo,
      mem_Ioo.mpr ⟨by linarith, hε⟩,
      isConnected_Ioo (by linarith),
      ⟨fun s => γ (q, s),
       by simpa using (hγ q hq').1,
       by simpa using (hγ q hq').2.1⟩,
      ht⟩
  · apply ContinuousOn.congr (f := fun q : ℝ × M => γ (q.2, q.1))
    · have hcont_γ := (hγ p (mem_of_mem_nhds hu)).2.2
      simp only [zero_sub, zero_add] at hcont_γ
      exact hcont_γ.comp (continuous_snd.prodMk continuous_fst).continuousOn
        fun ⟨t, q⟩ ⟨ht, hq⟩ => ⟨interior_subset hq, ht⟩
    · intro ⟨t, q⟩ ⟨ht, hq⟩
      simp only
      have hq' : q ∈ u := interior_subset hq
      have hD : t ∈ flowDomain V q := by
        simp only [flowDomain, Set.mem_iUnion]
        exact ⟨Ioo (-ε) ε, isOpen_Ioo,
          mem_Ioo.mpr ⟨by linarith, hε⟩,
          isConnected_Ioo (by linarith),
          ⟨fun s => γ (q, s),
           by simpa using (hγ q hq').1,
           by simpa using (hγ q hq').2.1⟩,
          ht⟩
      simp only [maximalFlowAt', dif_pos hD]
      exact (maximalFlowAt_eq_of_isMIntegralCurveOn V q t hD
        isOpen_Ioo (isConnected_Ioo (by linarith))
        (mem_Ioo.mpr ⟨by linarith, hε⟩) ht
        (show (fun s => γ (q, s)) 0 = q from by simpa using (hγ q hq').1)
        (by simpa using (hγ q hq').2.1)
        hV)

-- ---------------------------------------------------------------------------
-- Helpers for the three obligations that arise in `W_lee_eq_flowSet_lee`.
-- Each is stated as a separate lemma so the proof obligations are named and
-- can be discharged independently.
-- ---------------------------------------------------------------------------

include hV

private lemma flowDomain_extend (p : M) (t₁ : ℝ)
    (ht₁ : t₁ ∈ flowDomain V p)
    (r : ℝ)
    {J₀ : Set ℝ} (hJ₀_open : IsOpen J₀) (hJ₀_conn : IsConnected J₀)
    (h0J₀ : (0 : ℝ) ∈ J₀) (hrJ₀ : r ∈ J₀)
    {γ₀ : ℝ → M} (hγ₀_init : γ₀ 0 = maximalFlowAt' V p t₁)
    (hγ₀_int : IsMIntegralCurveOn γ₀ V J₀) :
    t₁ + r ∈ flowDomain V p := by
  classical
  obtain ⟨γ₁, hγ₁_init, J₁', hJ₁'_open, h0J₁', ht₁J₁', hJ₁'_conn, hγ₁_int⟩ :=
    flowDomain_exists_integralCurve V p t₁ ht₁
  have hγ₁_t₁ : γ₁ t₁ = maximalFlowAt' V p t₁ := by
    simp only [maximalFlowAt', dif_pos ht₁]
    exact (maximalFlowAt_eq_of_isMIntegralCurveOn V p t₁ ht₁
      hJ₁'_open hJ₁'_conn h0J₁' ht₁J₁' hγ₁_init hγ₁_int hV).symm
  set S := {t : ℝ | t - t₁ ∈ J₀} with hS_def
  have hS_open : IsOpen S := hJ₀_open.preimage (continuous_sub_right _)
  have hS_conn : IsConnected S := by
    have himg : S = (fun x => x + t₁) '' J₀ := by
      ext x; simp only [hS_def, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro h; exact ⟨x - t₁, h, by ring⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [himg]; exact hJ₀_conn.image _ (continuous_add_right _).continuousOn
  have ht₁S : t₁ ∈ S := by simp only [hS_def, Set.mem_setOf_eq, sub_self]; exact h0J₀
  have ht₁rS : t₁ + r ∈ S := by simp only [hS_def, Set.mem_setOf_eq, add_sub_cancel_left]; exact hrJ₀
  have hγ₀'_int : IsMIntegralCurveOn (fun t => γ₀ (t - t₁)) V S := by
    convert IsMIntegralCurveOn.comp_add hγ₀_int (-t₁) using 1
  have hγ₀'_t₁ : γ₀ (t₁ - t₁) = γ₁ t₁ := by simp [hγ₀_init, hγ₁_t₁]
  have hinter_conn : IsConnected (J₁' ∩ S) := by
    refine ⟨⟨t₁, ht₁J₁', ht₁S⟩, ?_⟩
    exact (isPreconnected_iff_ordConnected.mpr
      (hJ₁'_conn.isPreconnected.ordConnected.inter hS_conn.isPreconnected.ordConnected))
  have hagree : EqOn γ₁ (fun t => γ₀ (t - t₁)) (J₁' ∩ S) := by
    have : IsOpen (J₁' ∩ S) := hJ₁'_open.inter hS_open
    intro t ht
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.isOpen_iff.mp this t₁ ⟨ht₁J₁', ht₁S⟩
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.isOpen_iff.mp this t ht
    have hord : OrdConnected (J₁' ∩ S) := hinter_conn.isPreconnected.ordConnected
    rcases le_total t₁ t with hle | hle
    · have ht₀_ab : t₁ ∈ Ioo (t₁ - δ₁) (t + δ₂) := mem_Ioo.mpr ⟨by linarith, by linarith⟩
      have ht_ab : t ∈ Ioo (t₁ - δ₁) (t + δ₂) := mem_Ioo.mpr ⟨by linarith, by linarith⟩
      have hIoo_sub : Ioo (t₁ - δ₁) (t + δ₂) ⊆ J₁' ∩ S := by
        intro x ⟨hxa, hxb⟩
        rcases le_or_gt x t₁ with h | h
        · exact hδ₁ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith))
        · rcases le_or_gt x t with h' | h'
          · exact hord.out ⟨ht₁J₁', ht₁S⟩ ht ⟨le_of_lt h, h'⟩
          · exact hδ₂ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith))
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀_ab hV
        (hγ₁_int.mono (fun x hx => (hIoo_sub hx).1)) (hγ₀'_int.mono (fun x hx => (hIoo_sub hx).2))
        hγ₀'_t₁.symm ht_ab
    · have ht₀_ab : t₁ ∈ Ioo (t - δ₂) (t₁ + δ₁) := mem_Ioo.mpr ⟨by linarith, by linarith⟩
      have ht_ab : t ∈ Ioo (t - δ₂) (t₁ + δ₁) := mem_Ioo.mpr ⟨by linarith, by linarith⟩
      have hIoo_sub : Ioo (t - δ₂) (t₁ + δ₁) ⊆ J₁' ∩ S := by
        intro x ⟨hxa, hxb⟩
        rcases le_or_gt x t with h | h
        · exact hδ₂ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith))
        · rcases le_or_gt x t₁ with h' | h'
          · exact hord.out ht ⟨ht₁J₁', ht₁S⟩ ⟨le_of_lt h, h'⟩
          · exact hδ₁ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith))
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless ht₀_ab hV
        (hγ₁_int.mono (fun x hx => (hIoo_sub hx).1)) (hγ₀'_int.mono (fun x hx => (hIoo_sub hx).2))
        hγ₀'_t₁.symm ht_ab
  set γ := fun t => if t ∈ J₁' then γ₁ t else γ₀ (t - t₁) with hγ_def
  have hγ_init : γ 0 = p := by simp only [hγ_def, if_pos h0J₁']; exact hγ₁_init
  have hγ_int : IsMIntegralCurveOn γ V (J₁' ∪ S) := by
    intro t ht; rcases ht with ht1 | ht2
    · have hval : γ t = γ₁ t := by simp only [hγ_def, if_pos ht1]
      rw [show V (γ t) = V (γ₁ t) from by rw [hval]]
      exact ((hγ₁_int t ht1).hasMFDerivAt (hJ₁'_open.mem_nhds ht1)
        |>.hasMFDerivWithinAt).congr_of_eventuallyEq
        (by filter_upwards [nhdsWithin_le_nhds (hJ₁'_open.mem_nhds ht1)] with s hs
            exact (by simp only [hγ_def, if_pos hs] : γ s = γ₁ s)) hval
    · have hval : γ t = γ₀ (t - t₁) := by
        change (if t ∈ J₁' then γ₁ t else γ₀ (t - t₁)) = γ₀ (t - t₁)
        split_ifs with h
        · exact hagree ⟨h, ht2⟩
        · rfl
      rw [show V (γ t) = V (γ₀ (t - t₁)) from by rw [hval]]
      exact ((hγ₀'_int t ht2).hasMFDerivAt (hS_open.mem_nhds ht2)
        |>.hasMFDerivWithinAt).congr_of_eventuallyEq
        (by filter_upwards [nhdsWithin_le_nhds (hS_open.mem_nhds ht2)] with s hs
            show γ s = γ₀ (s - t₁)
            change (if s ∈ J₁' then γ₁ s else γ₀ (s - t₁)) = γ₀ (s - t₁)
            split_ifs with h
            · exact hagree ⟨h, hs⟩
            · exact rfl) hval
  change t₁ + r ∈ ⋃ (J : Set ℝ) (_ : IsOpen J) (_ : (0 : ℝ) ∈ J) (_ : IsConnected J)
    (_ : ∃ γ', γ' 0 = p ∧ IsMIntegralCurveOn γ' V J), J
  refine Set.mem_iUnion.mpr ⟨J₁' ∪ S, ?_⟩
  refine Set.mem_iUnion.mpr ⟨hJ₁'_open.union hS_open, ?_⟩
  refine Set.mem_iUnion.mpr ⟨Or.inl h0J₁', ?_⟩
  refine Set.mem_iUnion.mpr ⟨IsConnected.union ⟨t₁, ht₁J₁', ht₁S⟩ hJ₁'_conn hS_conn, ?_⟩
  refine Set.mem_iUnion.mpr ⟨⟨γ, hγ_init, hγ_int⟩, ?_⟩
  exact Or.inr ht₁rS

/-- **Sorry 1 — negative-time case.**
    Lee Theorem 9.12: the argument for τ < 0 is symmetric to the τ > 0 case.
    Every `(τ, p₀) ∈ flowSet V` with `τ ≤ 0` belongs to `W_lee V hV`.

    TODO: fill in by running the same induction as the τ > 0 branch but with
    time reversed (replace `t` by `-t` throughout). -/
private lemma W_lee_neg_time
    {τ : ℝ} {p₀ : M}
    (hτ : (τ, p₀) ∈ flowSet V)
    (hτneg : τ ≤ 0)
    (hτW : (τ, p₀) ∉ W_lee V hV) :
    False := by
  sorry

/-- **Sorry 2 — piecewise curve stays in `flowSet`.**
    The product set `Ioo (-δ₀) (t₁ + ε) ×ˢ U₁'` is contained in `flowSet V`.

    The proof proceeds in two pieces:
    * *Left piece* (`s < t₁`): `s ∈ J₁` (because `Ioo (-δ₀) δ₀ ⊆ J₁` by `hδ₀_sub`),
      so `(s, p) ∈ J₁ ×ˢ U₁ ⊆ flowSet V` by `hJ₁U₁` (after shrinking `U₁'` into `U₁`).
    * *Right piece* (`s > t₁ - ε`): the translated integral curve
      `u ↦ maximalFlowAt' V (maximalFlowAt' V p t₁) (u - t₁)` is an integral
      curve starting at `maximalFlowAt' V p t₁ ∈ U₀`, so `(s, p)` is in `flowSet V`
      via `hJ₀U₀`.
    * The two pieces agree on the overlap `Ioo (t₁ - ε) (t₁ + ε₁) ×ˢ U₁'` by
      uniqueness of integral curves.

    TODO: formalise the gluing argument. -/
private lemma piecewise_flow_subset_flowSet
    {t₁ δ₀ ε : ℝ}
    {J₁ J₀ : Set ℝ} {U₁ U₀ : Set M}
    (hδ₀_sub : Metric.ball (0 : ℝ) δ₀ ⊆ J₁)
    (hJ₁_c : IsConnected J₁) (h0J₁ : (0 : ℝ) ∈ J₁) (ht₁J₁ : t₁ ∈ J₁)
    (hJ₁U₁ : J₁ ×ˢ U₁ ⊆ flowSet V)
    (hJ₀U₀ : J₀ ×ˢ U₀ ⊆ flowSet V)
    (hε_sub : Metric.ball (0 : ℝ) ε ⊆ J₀) :
    Ioo (-δ₀) (t₁ + ε) ×ˢ (U₁ ∩ (fun p => maximalFlowAt' V p t₁) ⁻¹' U₀) ⊆
      flowSet V := by
  intro ⟨s, p⟩ ⟨hs, hp⟩
  have hpU₁ : p ∈ U₁ := hp.1
  have hpU₀ : maximalFlowAt' V p t₁ ∈ U₀ := hp.2
  -- Case split: s ∈ J₁ or not
  by_cases hsJ₁ : s ∈ J₁
  · exact hJ₁U₁ ⟨hsJ₁, hpU₁⟩
  · -- s ∉ J₁. Since J₁ is connected open containing (-δ₀,δ₀) and t₁,
    -- and s > -δ₀ but s ∉ J₁, we must have s > t₁.
    -- So s - t₁ ∈ (0, ε) ⊆ ball(0, ε) ⊆ J₀.
    have ht₁_flow : t₁ ∈ flowDomain V p := by
      have h : (t₁, p) ∈ flowSet V := hJ₁U₁ ⟨ht₁J₁, hpU₁⟩
      exact h
    -- s - t₁ ∈ flowDomain V (maximalFlowAt' V p t₁)
    have hs_t₁ : s - t₁ ∈ flowDomain V (maximalFlowAt' V p t₁) := by
      have : s - t₁ ∈ J₀ := by
        apply hε_sub; rw [Metric.mem_ball, Real.dist_eq]
        have hsub : s > t₁ := by
          by_contra h; push Not at h
          apply hsJ₁
          rcases le_or_gt s 0 with hs0 | hs0
          · exact hδ₀_sub (Metric.mem_ball.mpr (by
              rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith [hs.1]))
          · exact (isPreconnected_iff_ordConnected.mp hJ₁_c.isPreconnected).out h0J₁ ht₁J₁
              ⟨le_of_lt hs0, h⟩
        rw [abs_of_nonneg (by linarith)]; linarith [hs.2]
      have hs_t₁ : s - t₁ ∈ flowDomain V (maximalFlowAt' V p t₁) := by
        have h : (s - t₁, maximalFlowAt' V p t₁) ∈ flowSet V := hJ₀U₀ ⟨this, hpU₀⟩
        exact h
      exact hs_t₁
    obtain ⟨γ₀, hγ₀_init, J₀', hJ₀'_o, h0J₀', hsJ₀', hJ₀'_c, hγ₀_int⟩ :=
      flowDomain_exists_integralCurve V (maximalFlowAt' V p t₁) (s - t₁) hs_t₁
    have : t₁ + (s - t₁) ∈ flowDomain V p :=
      flowDomain_extend V hV p t₁ ht₁_flow (s - t₁) hJ₀'_o hJ₀'_c h0J₀' hsJ₀' hγ₀_init hγ₀_int
    simpa using this


-- Helper: maximalFlowAt' at time 0 returns the basepoint.
private lemma maximalFlowAt'_zero (p : M) : maximalFlowAt' V p 0 = p := by
  simp only [maximalFlowAt', dif_pos (zero_mem_flowDomain V p hV)]
  exact maximalFlowAt_zero V p hV

-- Helper: strengthened flowDomain_extend that also returns the value.
-- The proof is a copy of flowDomain_extend with the equality extracted at the end.
private lemma maximalFlowAt'_extend (p : M) (t₁ : ℝ)
    (ht₁ : t₁ ∈ flowDomain V p) (r : ℝ)
    {J₀ : Set ℝ} (hJ₀_open : IsOpen J₀) (hJ₀_conn : IsConnected J₀)
    (h0J₀ : (0 : ℝ) ∈ J₀) (hrJ₀ : r ∈ J₀)
    {γ₀ : ℝ → M} (hγ₀_init : γ₀ 0 = maximalFlowAt' V p t₁)
    (hγ₀_int : IsMIntegralCurveOn γ₀ V J₀) :
    maximalFlowAt' V p (t₁ + r) = γ₀ r := by
  classical
  obtain ⟨γ₁, hγ₁_init, J₁', hJ₁'_open, h0J₁', ht₁J₁', hJ₁'_conn, hγ₁_int⟩ :=
    flowDomain_exists_integralCurve V p t₁ ht₁
  have hγ₁_t₁ : γ₁ t₁ = maximalFlowAt' V p t₁ := by
    simp only [maximalFlowAt', dif_pos ht₁]
    exact (maximalFlowAt_eq_of_isMIntegralCurveOn V p t₁ ht₁
      hJ₁'_open hJ₁'_conn h0J₁' ht₁J₁' hγ₁_init hγ₁_int hV).symm
  set S₀ := {t : ℝ | t - t₁ ∈ J₀} with hS₀_def
  have hS₀_open : IsOpen S₀ := hJ₀_open.preimage (continuous_sub_right _)
  have hS₀_conn : IsConnected S₀ := by
    rw [show S₀ = (· + t₁) '' J₀ from by ext x; simp only [hS₀_def, mem_setOf_eq, image_add_right,
                                                           mem_preimage, sub_eq_add_neg]]
    exact hJ₀_conn.image _ (continuous_add_right _).continuousOn
  have ht₁S₀ : t₁ ∈ S₀ := by simp [hS₀_def, h0J₀]
  have ht₁rS₀ : t₁ + r ∈ S₀ := by simp [hS₀_def, hrJ₀]
  have hγ₀'_int : IsMIntegralCurveOn (fun t => γ₀ (t - t₁)) V S₀ := by
    convert IsMIntegralCurveOn.comp_add hγ₀_int (-t₁) using 1
  have hγ₀'_t₁ : γ₀ (t₁ - t₁) = γ₁ t₁ := by simp [hγ₀_init, hγ₁_t₁]
  have hinter_conn : IsConnected (J₁' ∩ S₀) :=
    ⟨⟨t₁, ht₁J₁', ht₁S₀⟩, isPreconnected_iff_ordConnected.mpr
      (hJ₁'_conn.isPreconnected.ordConnected.inter hS₀_conn.isPreconnected.ordConnected)⟩
  have hagree : EqOn γ₁ (fun t => γ₀ (t - t₁)) (J₁' ∩ S₀) := by
    intro t ht
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.isOpen_iff.mp (hJ₁'_open.inter hS₀_open) t₁ ⟨ht₁J₁', ht₁S₀⟩
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.isOpen_iff.mp (hJ₁'_open.inter hS₀_open) t ht
    have hord := hinter_conn.isPreconnected.ordConnected
    rcases le_total t₁ t with hle | hle
    · have hIoo_sub : Ioo (t₁ - δ₁) (t + δ₂) ⊆ J₁' ∩ S₀ := fun x hx => by
        rcases le_or_gt x t₁ with h | h
        · exact hδ₁ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith [hx.1]))
        · rcases le_or_gt x t with h' | h'
          · exact hord.out ⟨ht₁J₁', ht₁S₀⟩ ht ⟨h.le, h'⟩
          · exact hδ₂ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [hx.2]))
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (mem_Ioo.mpr ⟨by linarith, by linarith⟩) hV
        (hγ₁_int.mono (hIoo_sub.trans inter_subset_left))
        (hγ₀'_int.mono (hIoo_sub.trans inter_subset_right))
        hγ₀'_t₁.symm (mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    · have hIoo_sub : Ioo (t - δ₂) (t₁ + δ₁) ⊆ J₁' ∩ S₀ := fun x hx => by
        rcases le_or_gt x t with h | h
        · exact hδ₂ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith [hx.1]))
        · rcases le_or_gt x t₁ with h' | h'
          · exact hord.out ht ⟨ht₁J₁', ht₁S₀⟩ ⟨h.le, h'⟩
          · exact hδ₁ (Metric.mem_ball.mpr (by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [hx.2]))
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (mem_Ioo.mpr ⟨by linarith, by linarith⟩) hV
        (hγ₁_int.mono (hIoo_sub.trans inter_subset_left))
        (hγ₀'_int.mono (hIoo_sub.trans inter_subset_right))
        hγ₀'_t₁.symm (mem_Ioo.mpr ⟨by linarith, by linarith⟩)
  set γ := fun t => if t ∈ J₁' then γ₁ t else γ₀ (t - t₁) with hγ_def
  have hγ_init : γ 0 = p := by simp [hγ_def, h0J₁', hγ₁_init]
  have hγ_int : IsMIntegralCurveOn γ V (J₁' ∪ S₀) := by
    intro t ht; rcases ht with ht1 | ht2
    · have hval : γ t = γ₁ t := by simp [hγ_def, ht1]
      rw [show V (γ t) = V (γ₁ t) from by rw [hval]]
      exact ((hγ₁_int t ht1).hasMFDerivAt (hJ₁'_open.mem_nhds ht1)
        |>.hasMFDerivWithinAt).congr_of_eventuallyEq
        (by filter_upwards [nhdsWithin_le_nhds (hJ₁'_open.mem_nhds ht1)] with s hs
            simp [hγ_def, hs]) hval
    · have hval : γ t = γ₀ (t - t₁) := by
        simp only [hγ_def]; split_ifs with h
        · exact hagree ⟨h, ht2⟩
        · rfl
      rw [show V (γ t) = V (γ₀ (t - t₁)) from by rw [hval]]
      exact ((hγ₀'_int t ht2).hasMFDerivAt (hS₀_open.mem_nhds ht2)
        |>.hasMFDerivWithinAt).congr_of_eventuallyEq
        (by filter_upwards [nhdsWithin_le_nhds (hS₀_open.mem_nhds ht2)] with s hs
            show γ s = γ₀ (s - t₁)
            simp only [hγ_def]; split_ifs with h
            · exact hagree ⟨h, hs⟩
            · rfl) hval
  have ht₁r_domain : t₁ + r ∈ flowDomain V p := by
    simp only [flowDomain, Set.mem_iUnion]
    exact ⟨J₁' ∪ S₀, hJ₁'_open.union hS₀_open, Or.inl h0J₁',
      IsConnected.union ⟨t₁, ht₁J₁', ht₁S₀⟩ hJ₁'_conn hS₀_conn,
      ⟨γ, hγ_init, hγ_int⟩, Or.inr ht₁rS₀⟩
  simp only [maximalFlowAt', dif_pos ht₁r_domain]
  rw [maximalFlowAt_eq_of_isMIntegralCurveOn V p (t₁ + r) ht₁r_domain
      (hJ₁'_open.union hS₀_open)
      (IsConnected.union ⟨t₁, ht₁J₁', ht₁S₀⟩ hJ₁'_conn hS₀_conn)
      (Or.inl h0J₁') (Or.inr ht₁rS₀) hγ_init hγ_int hV]
  simp only [hγ_def]
  split_ifs with h
  · have := hagree ⟨h, ht₁rS₀⟩; simp only [add_sub_cancel_left] at this; exact this
  · simp only [add_sub_cancel_left]

/-- **Sorry 3 — piecewise flow is continuous.**
    `(t, p) ↦ maximalFlowAt' V p t` is continuous on
    `Ioo (-δ₀) (t₁ + ε) ×ˢ U₁'`.

    The proof glues two continuous pieces:
    * *Left piece*: the restriction of `hcont₁` to
      `Ioo (-δ₀) (t₁ + ε₁) ×ˢ U₁' ⊆ J₁ ×ˢ U₁`.
    * *Right piece*: on `Ioo (t₁ - ε) (t₁ + ε) ×ˢ U₁'` the map factors as
        `(t, p) ↦ maximalFlowAt' V (maximalFlowAt' V p t₁) (t - t₁)`,
      which is continuous by composing `hcont_p_t₁` (continuity of `p ↦ θ_{t₁}(p)`)
      with `hcont₀` (continuity of `(s, q) ↦ θ_s(q)` near `(0, q₀)`).
    * The two pieces agree on their overlap by the flow group law
      (`flow_add` / `IsMIntegralCurve.mul`).

    TODO: formalise the gluing via `ContinuousOn.congr` and `IsOpen.continuousOn_iff`. -/
private lemma piecewise_flow_continuous
    {t₁ δ₀ ε : ℝ}
    {J₁ J₀ : Set ℝ} {U₁ U₀ : Set M}
    (hδ₀_sub : Metric.ball (0 : ℝ) δ₀ ⊆ J₁)
    (hJ₁_o : IsOpen J₁) (hJ₁_c : IsConnected J₁) (h0J₁ : (0 : ℝ) ∈ J₁) (ht₁J₁ : t₁ ∈ J₁)
    (hJ₀_o : IsOpen J₀) (hJ₀_c : IsConnected J₀) (h0J₀ : (0 : ℝ) ∈ J₀)
    (hε_sub : Metric.ball (0 : ℝ) ε ⊆ J₀)
    (hJ₁U₁ : J₁ ×ˢ U₁ ⊆ flowSet V)
    (hJ₀U₀ : J₀ ×ˢ U₀ ⊆ flowSet V)
    (hcont₁ : ContinuousOn (fun q : ℝ × M => maximalFlowAt' V q.2 q.1) (J₁ ×ˢ U₁))
    (hcont₀ : ContinuousOn (fun q : ℝ × M => maximalFlowAt' V q.2 q.1) (J₀ ×ˢ U₀))
    (hcont_p_t₁ : ContinuousOn (fun p => maximalFlowAt' V p t₁) U₁) :
    ContinuousOn (fun q : ℝ × M => maximalFlowAt' V q.2 q.1)
      (Ioo (-δ₀) (t₁ + ε) ×ˢ (U₁ ∩ (fun p => maximalFlowAt' V p t₁) ⁻¹' U₀)) := by
  set U₁' := U₁ ∩ (fun p => maximalFlowAt' V p t₁) ⁻¹' U₀ with hU₁'_def
  set S := {t : ℝ | t - t₁ ∈ J₀} with hS_def
  have hS_open : IsOpen S := hJ₀_o.preimage (continuous_sub_right t₁)
  -- g(t,p) = maximalFlowAt' V (maximalFlowAt' V p t₁) (t - t₁) is ContinuousOn on S ×ˢ U₁'
  have hg_cont : ContinuousOn
      (fun q : ℝ × M => maximalFlowAt' V (maximalFlowAt' V q.2 t₁) (q.1 - t₁))
      (S ×ˢ U₁') := by
    -- Factor as composition: hcont₀ ∘ φ where φ(t,p) = (t - t₁, maximalFlowAt' V p t₁)
    apply ContinuousOn.comp hcont₀
      (f := fun q : ℝ × M => (q.1 - t₁, maximalFlowAt' V q.2 t₁))
    · -- φ is ContinuousOn on S ×ˢ U₁'
      exact ContinuousOn.prodMk
        ((continuous_fst.sub continuous_const).continuousOn)
        (hcont_p_t₁.comp continuousOn_snd (fun q hq => hq.2.1))
    · -- φ maps S ×ˢ U₁' into J₀ ×ˢ U₀
      intro q hq
      exact Set.mk_mem_prod hq.1 hq.2.2
  -- Flow additivity: f(t,p) = g(t,p) whenever t ∈ S and p ∈ U₁'
  have hflow_eq : ∀ t p, t ∈ S → p ∈ U₁' →
      maximalFlowAt' V p t = maximalFlowAt' V (maximalFlowAt' V p t₁) (t - t₁) := by
    intro t p htS hpU
    have h1 : (t₁, p) ∈ flowSet V ↔ t₁ ∈ flowDomain V p := by
      constructor
      · unfold flowSet
        intro h
        simpa using h
      · unfold flowSet
        intro h
        simpa using h
    have ht₁_domain : t₁ ∈ flowDomain V p := h1.mp (hJ₁U₁ (Set.mk_mem_prod ht₁J₁ hpU.1))
    have hJ₀_sub : J₀ ⊆ flowDomain V (maximalFlowAt' V p t₁) := by
      intro s hs
      have hpU₀ : maximalFlowAt' V p t₁ ∈ U₀ := hpU.2
      have hmem : (s, maximalFlowAt' V p t₁) ∈ flowSet V :=
        hJ₀U₀ (Set.mk_mem_prod hs hpU₀)
      simpa [flowSet] using hmem
    simpa using maximalFlowAt'_extend V hV p t₁ ht₁_domain (t - t₁)
      hJ₀_o hJ₀_c h0J₀ (show t - t₁ ∈ J₀ from htS)
      (hγ₀_init := maximalFlowAt'_zero V hV (maximalFlowAt' V p t₁))
      (hγ₀_int := (maximalFlowAt_isMIntegralCurveOn V (maximalFlowAt' V p t₁) hV).mono hJ₀_sub)
  -- Prove ContinuousOn pointwise via ContinuousWithinAt
  intro tp htp
  have ht := htp.1
  have hp := htp.2
  by_cases htJ₁ : tp.1 ∈ J₁
  · -- Left piece: nhdsWithin D ≤ nhdsWithin (J₁ ×ˢ U₁) locally, so use hcont₁
    have hmem_J₁U₁ : tp ∈ J₁ ×ˢ U₁ := ⟨htJ₁, hp.1⟩
    have h_cwat := hcont₁ tp hmem_J₁U₁
    apply h_cwat.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨J₁ ×ˢ Set.univ, (hJ₁_o.prod isOpen_univ).mem_nhds ⟨htJ₁, trivial⟩, ?_⟩
    intro ⟨s, q⟩ ⟨hmem_J₁U, hmem_D⟩
    exact Set.mk_mem_prod hmem_J₁U.1 hmem_D.2.1
  · -- Right piece: tp.1 ∈ S (same connectivity argument as piecewise_flow_subset_flowSet)
    have ht_gt : tp.1 > t₁ := by
      by_contra h; push Not at h
      apply htJ₁
      rcases le_or_gt tp.1 0 with ht0 | ht0
      · exact hδ₀_sub (Metric.mem_ball.mpr (by
            rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith [ht.1]))
      · exact (isPreconnected_iff_ordConnected.mp hJ₁_c.isPreconnected).out
            h0J₁ ht₁J₁ ⟨ht0.le, h⟩
    have htS : tp.1 ∈ S :=
      hε_sub (Metric.mem_ball.mpr (by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [ht.2]))
    -- g is ContinuousWithinAt at tp within S ×ˢ U₁'; convert to f, then weaken to D
    have hmem_SU₁ : tp ∈ S ×ˢ U₁' := ⟨htS, hp⟩
    have h_cwat := hg_cont tp hmem_SU₁
    have h_cwat' : ContinuousWithinAt
        (fun q : ℝ × M => maximalFlowAt' V q.2 q.1) (S ×ˢ U₁') tp := by
      apply h_cwat.congr
      · intro sq hsq
        exact hflow_eq sq.1 sq.2 hsq.1 hsq.2
      · exact hflow_eq tp.1 tp.2 htS hp
    apply h_cwat'.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    refine ⟨S ×ˢ Set.univ, (hS_open.prod isOpen_univ).mem_nhds ⟨htS, trivial⟩, ?_⟩
    intro ⟨s, q⟩ ⟨hmem_SU, hmem_D⟩
    exact Set.mk_mem_prod hmem_SU.1 hmem_D.2

-- ---------------------------------------------------------------------------

theorem W_lee_eq_flowSet_lee : W_lee V hV = flowSet V := by
  apply Set.eq_of_subset_of_subset
  · intro ⟨t, p⟩ ⟨J, U, _, _, _, htJ, hpU, _, hJU, _⟩
    exact hJU ⟨htJ, hpU⟩
  · intro ⟨τ, p₀⟩ hτ
    by_contra h
    wlog hτpos : τ > 0 with H_neg
    · push Not at hτpos
      exact W_lee_neg_time V hV hτ hτpos h
    let S := {t : ℝ | t > 0 ∧ (t, p₀) ∉ W_lee V hV}
    have hτS   : τ ∈ S        := ⟨hτpos, h⟩
    have hS_ne : S.Nonempty   := ⟨τ, hτS⟩
    have hS_bd : BddBelow S   := ⟨0, fun t ht => le_of_lt ht.1⟩
    let t₀ := sInf S
    have h0W : (0, p₀) ∈ W_lee V hV := mem_W_lee_zero_lee V hV p₀
    have ht₀_pos : t₀ > 0 := by
      have hW_nhds := (isOpen_W_lee (V := V) (hV := hV)).mem_nhds h0W
      rw [nhds_prod_eq] at hW_nhds
      obtain ⟨J', hJ'_mem, U', hU'_mem, hJ'U'⟩ := Filter.mem_prod_iff.mp hW_nhds
      obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.mem_nhds_iff.mp hJ'_mem
      apply lt_of_lt_of_le hδ_pos
      apply le_csInf hS_ne
      intro t ht
      by_contra hlt
      push Not at hlt
      exact ht.2 (hJ'U' ⟨hδ_sub (Metric.mem_ball.mpr
        (by simp [abs_lt]; constructor <;> linarith [ht.1])),
        mem_of_mem_nhds hU'_mem⟩)
    have ht₀_mem : t₀ ∈ flowDomain V p₀ :=
      (isPreconnected_flowDomain V p₀).ordConnected.out
        (zero_mem_flowDomain V p₀ hV) hτ
        ⟨le_of_lt ht₀_pos, csInf_le hS_bd hτS⟩
    let q₀ := maximalFlowAt' V p₀ t₀
    obtain ⟨J₀, U₀, hJ₀_o, hJ₀_c, hU₀_o, h0J₀, hq₀U₀, _, hJ₀U₀, hcont₀⟩ :=
      mem_W_lee_zero_lee V hV q₀
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.mem_nhds_iff.mp (hJ₀_o.mem_nhds h0J₀)
    have hθ_cont : ContinuousAt (fun t => maximalFlowAt' V p₀ t) t₀ := by
      have hcont : ContinuousOn (maximalFlowAt' V p₀) (flowDomain V p₀) := by
        intro t ht
        exact (maximalFlowAt_isMIntegralCurveOn (V := V) p₀ hV t ht).continuousWithinAt
      exact hcont.continuousAt ((isOpen_flowDomain V p₀).mem_nhds ht₀_mem)
    obtain ⟨δ₁, hδ₁_pos, hδ₁_sub⟩ := Metric.mem_nhds_iff.mp
      (hθ_cont.preimage_mem_nhds (hU₀_o.mem_nhds hq₀U₀))
    set t₁ := t₀ - min t₀ (min δ₁ ε) / 2 with ht₁_def
    have ht₁_lt : t₁ < t₀ := by
      simp only [ht₁_def]
      simp only [sub_lt_self_iff, Nat.ofNat_pos, div_pos_iff_of_pos_right, lt_inf_iff]
      exact ⟨ht₀_pos, hδ₁_pos, hε_pos⟩
    have ht₁_add_ε : t₁ + ε > t₀ := by
      simp [ht₁_def]; linarith [min_le_right t₀ (min δ₁ ε), min_le_right δ₁ ε, hε_pos]
    have ht₁_pos : t₁ > 0 := by
      simp [ht₁_def]; linarith [min_le_left t₀ (min δ₁ ε), ht₀_pos]
    have ht₁_U₀ : maximalFlowAt' V p₀ t₁ ∈ U₀ :=
      hδ₁_sub (Metric.mem_ball.mpr (by
        rw [Real.dist_eq, ht₁_def, abs_lt]
        refine ⟨?_, ?_⟩
        · linarith [min_le_right t₀ (min δ₁ ε), min_le_left δ₁ ε, hδ₁_pos]
        · linarith [hδ₁_pos]))
    have ht₁_W : (t₁, p₀) ∈ W_lee V hV := by
      have hnt₁S : t₁ ∉ S :=
        fun hs => absurd (csInf_le hS_bd hs) (not_le.mpr ht₁_lt)
      simp only [S, Set.mem_setOf_eq, not_and, not_not] at hnt₁S
      exact hnt₁S ht₁_pos
    obtain ⟨J₁, U₁, hJ₁_o, hJ₁_c, hU₁_o, ht₁J₁, hp₀U₁, h0J₁, hJ₁U₁, hcont₁⟩ :=
      ht₁_W
    have hcont_p_t₁ : ContinuousOn (fun p => maximalFlowAt' V p t₁) U₁ :=
      (hcont₁.comp ((continuous_const.prodMk continuous_id).continuousOn)
        (fun p hp => ⟨ht₁J₁, hp⟩)).congr (fun _ _ => rfl)
    set U₁' := U₁ ∩ (fun p => maximalFlowAt' V p t₁) ⁻¹' U₀ with hU₁'_def
    have hU₁'_o  : IsOpen U₁' := by
      rw [hU₁'_def]
      exact hcont_p_t₁.isOpen_inter_preimage hU₁_o hU₀_o
    have hp₀U₁'  : p₀ ∈ U₁' := ⟨hp₀U₁, ht₁_U₀⟩
    obtain ⟨δ₀, hδ₀_pos, hδ₀_sub⟩ := Metric.mem_nhds_iff.mp (hJ₁_o.mem_nhds h0J₁)
    -- `hV` is not a parameter of the two piecewise lemmas (it does not appear in
    -- their statements), so we pass only `V`.  Using `have` here also avoids the
    -- awkward trailing comma that would arise from inlining these calls directly
    -- inside the anonymous ⟨…⟩ constructor.
    have hsubset : Ioo (-δ₀) (t₁ + ε) ×ˢ U₁' ⊆ flowSet V :=
      piecewise_flow_subset_flowSet V hV
        hδ₀_sub hJ₁_c h0J₁ ht₁J₁
        hJ₁U₁ hJ₀U₀ hε_sub
    have hcont_pw : ContinuousOn (fun q : ℝ × M => maximalFlowAt' V q.2 q.1)
        (Ioo (-δ₀) (t₁ + ε) ×ˢ U₁') :=
      piecewise_flow_continuous V hV
        hδ₀_sub hJ₁_o hJ₁_c h0J₁ ht₁J₁
        hJ₀_o hJ₀_c h0J₀
        hε_sub hJ₁U₁ hJ₀U₀ hcont₁ hcont₀ hcont_p_t₁
    have ht₀_W : (t₀, p₀) ∈ W_lee V hV :=
      ⟨Ioo (-δ₀) (t₁ + ε), U₁',
        isOpen_Ioo,
        isConnected_Ioo (by linarith [ht₁_pos]),
        hU₁'_o,
        mem_Ioo.mpr ⟨by linarith, ht₁_add_ε⟩,
        hp₀U₁',
        mem_Ioo.mpr ⟨by linarith, by linarith [ht₁_pos]⟩,
        hsubset,
        hcont_pw⟩
    obtain ⟨J'', hJ''_mem, U'', hU''_mem, hJ''U''⟩ :=
      mem_nhds_prod_iff.mp ((isOpen_W_lee (V := V) (hV := hV)).mem_nhds ht₀_W)
    obtain ⟨η, hη_pos, hη_sub⟩ := Metric.mem_nhds_iff.mp hJ''_mem
    have hnotS : ∀ t ∈ Ioo t₀ (t₀ + η), t ∉ S :=
      fun t ht hts => hts.2 (hJ''U'' ⟨hη_sub (Metric.mem_ball.mpr
        (by simp [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])),
        mem_of_mem_nhds hU''_mem⟩)
    have hlb : ∀ t ∈ S, t₀ + η / 2 ≤ t := by
      intro t ht
      rcases (csInf_le hS_bd ht).lt_or_eq with hgt | heq
      · by_contra hlt
        push Not at hlt
        exact hnotS t ⟨hgt, by linarith⟩ ht
      · exact absurd (heq ▸ ht) (fun hs => hs.2 ht₀_W)
    linarith [le_csInf hS_ne hlb, hη_pos]

end Lee912_lee
