import Mathlib

/-! Hairer's challenge given to Kevin. -/

noncomputable section

open Metric Set MeasureTheory
open MvPolynomial hiding support
open Function hiding eval

section linear

variable {𝕜 : Type*} [Field 𝕜]
variable {E E' F  : Type*}
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

lemma exists_affineSpan_zero {ι'} (s : Submodule 𝕜 F) [FiniteDimensional 𝕜 s] [Infinite ι']
    (L : F →ₗ[𝕜] E →ₗ[𝕜] 𝕜) (x : ι' → E) (hx : LinearIndependent 𝕜 x) :
    ∃ y ∈ affineSpan 𝕜 (range x), ∀ i ∈ s, L i y = 0 := sorry

variable (𝕜) in
def nonConstantTotalDegreeLE (ι : Type*) (N : ℕ) : Submodule 𝕜 (MvPolynomial ι 𝕜) where
  carrier := { p | p.totalDegree ≤ N ∧ constantCoeff p = 0 }
  add_mem' := by
    rintro p q ⟨hp, hpc⟩ ⟨hq, hqc⟩
    exact ⟨(totalDegree_add p q).trans (max_le hp hq), by simp [hpc, hqc]⟩
  zero_mem' := by simp
  smul_mem' := by
    rintro c p ⟨hp, hpc⟩
    exact ⟨(totalDegree_smul_le _ _).trans hp, by simp [hpc]⟩

instance (ι : Type*) [Finite ι] (N : ℕ) :
  FiniteDimensional 𝕜 (nonConstantTotalDegreeLE 𝕜 ι N) := sorry

lemma affineSpan_subset_span {s : Set E} : (affineSpan 𝕜 s : Set E) ⊆ Submodule.span 𝕜 s := by
  intro x hx
  apply affineSpan_induction hx (p := fun y ↦ y ∈ Submodule.span 𝕜 s)
    (fun x hx ↦ Submodule.subset_span hx) (fun c u v w hu hv hw ↦ ?_)
  simp only [vsub_eq_sub, vadd_eq_add]
  apply Submodule.add_mem _ _ hw
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hu hv)

variable (𝕜) in
lemma support_subset_of_mem_span {α β} [Zero β] {s : Set E} {y : E} [FunLike E α (fun _ ↦ β)]
    (hy : y ∈ Submodule.span 𝕜 s) : support y ⊆ ⋃ i ∈ s, support i :=
  -- rw [← Subtype.range_coe (s := s), mem_affineSpan_iff_eq_affineCombination] at hy
  sorry

variable (𝕜) in
lemma support_subset_of_mem_affineSpan {α β} [Zero β] {s : Set E} {y : E} [FunLike E α (fun _ ↦ β)]
    (hy : y ∈ affineSpan 𝕜 s) : support y ⊆ ⋃ i ∈ s, support i :=
  support_subset_of_mem_span 𝕜 (affineSpan_subset_span hy)



end linear

section normed
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E E' F  : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- move this
theorem tsupport_add {X : Type*} [TopologicalSpace X] {α : Type*}
  [AddMonoid α] {f g : X → α} : (tsupport fun x ↦ f x + g x) ⊆ tsupport f ∪ tsupport g :=
  closure_minimal
    ((support_add f g).trans (union_subset_union (subset_tsupport _) (subset_tsupport _)))
    (isClosed_closure.union isClosed_closure)

variable (𝕜 E F) in
def SmoothSupportedOn (n : ℕ∞) (s : Set E) : Submodule 𝕜 (E → F) where
  carrier := { f : E → F | tsupport f ⊆ s ∧ ContDiff 𝕜 n f }
  add_mem' hf hg := ⟨tsupport_add.trans <| union_subset hf.1 hg.1, hf.2.add hg.2⟩
  zero_mem' :=
    ⟨(tsupport_eq_empty_iff.mpr rfl).subset.trans (empty_subset _), contDiff_const (c := 0)⟩
  smul_mem' r f hf :=
    ⟨(closure_mono <| support_smul_subset_right r f).trans hf.1, contDiff_const.smul hf.2⟩

namespace SmoothSupportedOn

variable {n : ℕ∞} {s : Set E}

instance : FunLike (SmoothSupportedOn 𝕜 E F n s) E (fun _ ↦ F) where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

@[simp]
lemma coe_mk (f : E → F) (h) : (⟨f, h⟩ : SmoothSupportedOn 𝕜 E F n s) = f := rfl

lemma tsupport_subset (f : SmoothSupportedOn 𝕜 E F n s) : tsupport f ⊆ s := f.2.1

lemma support_subset (f : SmoothSupportedOn 𝕜 E F n s) :
  support f ⊆ s := subset_tsupport _ |>.trans (tsupport_subset f)

protected lemma contDiff (f : SmoothSupportedOn 𝕜 E F n s) :
    ContDiff 𝕜 n f := f.2.2

variable (𝕜) in
lemma contDiff_of_mem_span {a : Set (SmoothSupportedOn 𝕜 E F n s)}
    {y : SmoothSupportedOn 𝕜 E F n s}
    (hy : y ∈ Submodule.span 𝕜 a) (hi : ∀ i ∈ a, ContDiff 𝕜 n i) :
    ContDiff 𝕜 n y := by
  apply Submodule.span_induction (p := fun (z : SmoothSupportedOn 𝕜 E F n s) ↦ ContDiff 𝕜 n z)
    hy hi ?_ (fun x y hx hy ↦ hx.add hy) (fun a x hx ↦ hx.const_smul a)
  change ContDiff 𝕜 n (0 : E → F)
  exact contDiff_const

variable (𝕜) in
lemma contDiff_of_mem_affineSpan {a : Set (SmoothSupportedOn 𝕜 E F n s)}
    {y : SmoothSupportedOn 𝕜 E F n s} (hy : y ∈ affineSpan 𝕜 a) (hi : ∀ i ∈ a, ContDiff 𝕜 n i) :
    ContDiff 𝕜 n y :=
  contDiff_of_mem_span 𝕜 (affineSpan_subset_span hy) hi

end SmoothSupportedOn
open SmoothSupportedOn

end normed
open SmoothSupportedOn

noncomputable section real

open scoped Topology

/-- If a point is not isolated in a metric space, then one can find countably many
disjoint balls of positive radius close to it. -/
lemma exists_disjoint_balls {E : Type*} [MetricSpace E] (x : E) [Filter.NeBot (𝓝[≠] x)]
    {c : ℝ} (hc : 0 < c) : ∃ (p : ℕ → E) (r : ℕ → ℝ),
    Pairwise (Disjoint on (fun i ↦ closedBall (p i) (r i))) ∧
    (∀ i, 0 < r i) ∧ (∀ i, closedBall (p i) (r i) ⊆ ball x c) := by
  have : Nonempty E := ⟨x⟩
  have A : ∀ r > 0, ∃ y, y ∈ ball x r \ {x} := by
    intro r hr
    have : ball x r \ {x} ∈ 𝓝[≠] x := diff_mem_nhdsWithin_compl (ball_mem_nhds x hr) {x}
    exact Filter.nonempty_of_mem this
  choose! y hy using A
  have B : ∀ r > 0, ∃ s > 0, closedBall (y r) s ⊆ ball x r \ closedBall x s ∧ s < r := by
    intro r hr
    have : dist (y r) x < r := by
      have : y r ∈ ball x r := mem_of_mem_diff (hy r hr)
      rw [mem_ball] at this
      linarith
    have : 0 < dist (y r) x := by simpa using not_mem_of_mem_diff (hy r hr)
    refine ⟨min ((r - dist (y r) x) / 2) ((dist (y r) x)/ 4), ?_, ?_, ?_⟩
    · apply lt_min
      · linarith
      · linarith
    · refine subset_diff.2 ⟨?_, ?_⟩
      · apply closedBall_subset_ball'
        linarith [min_le_left ((r - dist (y r) x) / 2) ((dist (y r) x)/ 4)]
      · apply closedBall_disjoint_closedBall
        linarith [min_le_right ((r - dist (y r) x) / 2) ((dist (y r) x)/ 4)]
    · linarith [min_le_left ((r - dist (y r) x) / 2) ((dist (y r) x)/ 4)]
  choose! s s_pos hs s_mono using B
  let F : ℕ → ℝ := fun n ↦ s^[n] c
  have F_succ n : F (n+1) = s (F n) := iterate_succ_apply' s n c
  have F_zero : F 0 = c := rfl
  have F_pos n : 0 < F n := by
    induction' n with n IH
    · simp [hc]
    · simp [F_succ, s_pos, IH]
  have F_subs n : closedBall (y (F n)) (F (n+1)) ⊆ ball x (F n) \ closedBall x (F (n+1)) := by
    rw [F_succ n]
    exact hs _ (F_pos n)
  have F_anti : StrictAnti F := by
    apply strictAnti_nat_of_succ_lt (fun n ↦ ?_)
    rw [F_succ]
    exact s_mono _ (F_pos _)
  have I m n (h : n < m) :
      Disjoint (closedBall (y (F n)) (F (n+1))) (closedBall (y (F m)) (F (m+1))) := by
    apply (Set.subset_diff.1 (F_subs n)).2.mono_right
    apply ((F_subs m).trans (diff_subset _ _)).trans (ball_subset_closedBall.trans _)
    apply closedBall_subset_closedBall (F_anti.antitone h)
  refine ⟨fun n ↦ y (F n), fun n ↦ F (n+1), ?_, fun n ↦ F_pos _, fun n ↦ ?_⟩
  · intro m n hmn
    rcases lt_or_gt_of_ne hmn with h'mn|h'mn
    · exact I n m h'mn
    · exact (I m n h'mn).symm
  · apply (F_subs n).trans ((diff_subset _ _).trans _)
    apply ball_subset_ball
    rw [← F_zero]
    exact F_anti.antitone (zero_le _)

open scoped BigOperators

lemma step (ι) [Fintype ι] [Nonempty ι] :
    ∃ f : ℕ → SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1),
    LinearIndependent ℝ f ∧ ∀ n, ∫ x, f n x = 1 := by
  obtain ⟨s, r, hs, hr, h2s⟩ : ∃ (s : ℕ → EuclideanSpace ℝ ι) (r : ℕ → ℝ),
      Pairwise (Disjoint on (fun i ↦ closedBall (s i) (r i))) ∧
      (∀ i, 0 < r i) ∧ (∀ i, closedBall (s i) (r i) ⊆ ball 0 1) :=
    exists_disjoint_balls _ zero_lt_one
  let f1 n : ContDiffBump (s n) := ⟨r n / 2, r n, half_pos (hr n), half_lt_self (hr n)⟩
  let f2 n : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1) := by
    refine ⟨(f1 n).normed volume, ⟨?_, (f1 n).contDiff_normed⟩⟩
    simpa only [ContDiffBump.tsupport_normed_eq] using (h2s n).trans ball_subset_closedBall
  refine ⟨f2, ?_, fun n ↦ (f1 n).integral_normed⟩
  rw [linearIndependent_iff']
  intro t g ht i₀ hi₀
  have A : (∑ i in t, g i • f2 i) (s i₀) = g i₀ • f2 i₀ (s i₀) := by
    have :
      ((∑ i in t, g i • f2 i : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) :
          (EuclideanSpace ℝ ι) → ℝ) = (∑ i in t, g i • f2 i : (EuclideanSpace ℝ ι) → ℝ) :=
        Submodule.coe_sum _ _ _
    rw [this, Finset.sum_apply, Finset.sum_eq_single i₀]
    · rfl
    · intro i _it hi
      have : f2 i (s i₀) = 0 := by
        change (f1 i).normed volume (s i₀) = 0
        rw [← nmem_support, (f1 i).support_normed_eq]
        have : s i₀ ∈ closedBall (s i₀) (r i₀) := mem_closedBall_self (hr i₀).le
        have T := disjoint_right.1 (hs hi) this
        contrapose! T
        exact ball_subset_closedBall T
      simp only [Pi.smul_apply, this, smul_eq_mul, mul_zero]
    · simp [hi₀]
  rw [ht, smul_eq_mul, eq_comm] at A
  change _ = 0 at A
  have : (f2 i₀) (s i₀) ≠ 0 := by
    change (f1 i₀).normed volume (s i₀) ≠ 0
    rw [← mem_support, (f1 i₀).support_normed_eq]
    exact mem_ball_self (hr i₀)
  simpa only [mul_eq_zero, this, or_false] using A

open scoped ENNReal

instance (ι : Type*) [IsEmpty ι] (p : ℝ≥0∞) (α : ι → Type*) : Subsingleton (PiLp p α) :=
  inferInstanceAs (Subsingleton ((∀ i : ι, α i)))

namespace MeasureTheory.Measure


/- Replace `pi_of_empty` by this one, which fixes conflicting instances between `Fintype`
and `IsEmpty`. -/
attribute [-instance] Fintype.ofIsEmpty in
theorem pi_of_empty' {α : Type*} [Fintype α] [IsEmpty α] {β : α → Type*} {m : ∀ a, MeasurableSpace (β a)}
    (μ : ∀ a : α, Measure (β a)) (x : ∀ a, β a := isEmptyElim) :
    Measure.pi μ = Measure.dirac x := by
  haveI : ∀ a, SigmaFinite (μ a) := isEmptyElim
  refine' pi_eq fun s _ => _
  rw [Fintype.prod_empty, dirac_apply_of_mem]
  exact isEmptyElim (α := α)

end MeasureTheory.Measure

lemma volume_pi_eq_pi (ι : Type*) [Fintype ι] :
    (volume : Measure (ι → ℝ)) = Measure.pi fun _ => volume := rfl

attribute [-instance] Fintype.ofIsEmpty in
lemma volume_pi_eq_dirac (ι : Type*) [Fintype ι] [IsEmpty ι] :
    (volume : Measure (ι → ℝ)) = Measure.dirac 0 :=
  Measure.pi_of_empty' _ _

attribute [-instance] Fintype.ofIsEmpty in
lemma volume_euclideanSpace_eq_dirac (ι : Type*) [Fintype ι] [IsEmpty ι] :
    (volume : Measure (EuclideanSpace ℝ ι)) = Measure.dirac 0 := by
  ext s hs
  have Z := EuclideanSpace.volume_preserving_measurableEquiv ι
  rw [← (Z.symm).measure_preimage hs, volume_pi_eq_dirac]
  simp only [MeasurableEquiv.measurableSet_preimage, hs, Measure.dirac_apply', Set.indicator,
    mem_preimage, Pi.one_apply]
  congr


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable [MeasurableSpace E] [BorelSpace E] {f f' : E → F} {μ : Measure E}

-- variant of ae_eq_zero_of_integral_contDiff_smul_eq_zero, not sure what we exactly need on `K`.
nonrec theorem IsClosed.ae_eq_zero_of_integral_contDiff_smul_eq_zero {K : Set E}
    (hU : IsClosed K) (hf : LocallyIntegrableOn f K μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ⊤ g → tsupport g ⊆ K → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ K → f x = 0 := by
  rw [← ae_restrict_iff'₀]
  · rw [locallyIntegrableOn_iff_locallyIntegrable_restrict hU] at hf
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hf fun g diff_g supp_g ↦ ?_

  sorry

end real

section missing_polynomial
open MvPolynomial Submodule

variable {R σ : Type*} [CommSemiring R] (n : ℕ)

lemma restrictTotalDegree_eq_span {n : ℕ} :
    restrictTotalDegree σ R n =
    span R ((fun c : σ →₀ ℕ ↦ monomial c (1 : R)) '' {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ n}) := by
  ext P; constructor <;> intro h
  · rw [← P.support_sum_monomial_coeff]
    refine sum_mem fun c hc ↦ ?_
    rw [← mul_one (coeff c P), ← smul_eq_mul, ← smul_monomial]
    rw [mem_restrictTotalDegree] at h
    exact smul_mem _ _ (subset_span <| mem_image_of_mem _ <| (le_totalDegree hc).trans h)
  · refine span_le.mpr ?_ h
    rintro x ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree]
    cases subsingleton_or_nontrivial R
    · rw [Subsingleton.elim ((fun c ↦ monomial c 1) c) 0, totalDegree_zero]; apply zero_le
    · rw [totalDegree_monomial _ one_ne_zero]; exact hc

/- Can be obtained by combining `LinearMap.proj` and `MvPolynomial.evalₗ`. -/
def evalAtₗ {R σ : Type*} [CommSemiring R] (x : σ → R) : MvPolynomial σ R →ₗ[R] R where
  toFun P := eval x P
  map_add' := by simp
  map_smul' := by simp

lemma analyticOn_eval (R σ) [Fintype σ] [NontriviallyNormedField R] (P : MvPolynomial σ R) :
    AnalyticOn R (eval · P) univ := fun x _ ↦ by
  apply P.induction_on (fun r ↦ ?_) (fun p q hp hq ↦ ?_) fun p i hp ↦ ?_
  · simp_rw [eval_C]; exact analyticAt_const
  · simp_rw [eval_add]; exact hp.add hq
  · simp_rw [eval_mul, eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := R) (φ := fun _ ↦ R) i).analyticAt _)

lemma finite_stuff' [Finite σ] (N : ℕ) : {s : Multiset σ | Multiset.card s ≤ N}.Finite := by
  classical
  have := Fintype.ofFinite σ
  let S := N • (Finset.univ.val : Multiset σ)
  apply Finset.finite_toSet (Multiset.toFinset (Multiset.powerset S)) |>.subset
  intro s hs
  rw [Set.mem_setOf] at hs
  rw [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powerset, Multiset.le_iff_count]
  intro x
  simp only [S, Multiset.count_nsmul, Multiset.count_univ, mul_one]
  exact le_trans (s.count_le_card x) hs

lemma finite_stuff [Finite σ] (N : ℕ) : {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ N}.Finite := by
  classical
  change {s : σ →₀ ℕ | s.sum (fun _ => id) ≤ N}.Finite
  simp only [← Finsupp.card_toMultiset]
  refine Set.Finite.of_finite_image ?_ (Multiset.toFinsupp.symm.injective.injOn _)
  convert finite_stuff' (σ := σ) N
  ext x
  rw [← AddEquiv.coe_toEquiv, Set.mem_image_equiv]
  simp

instance [Finite σ] : Module.Finite R (restrictTotalDegree σ R n) := by
  rw [Module.finite_def, fg_top, restrictTotalDegree_eq_span]
  exact Submodule.fg_span ((finite_stuff _).image _)

lemma totalDegree_le_of_support_subset (p q : MvPolynomial σ ℝ) (h : p.support ⊆ q.support) :
    totalDegree p ≤ totalDegree q :=
  Finset.sup_mono h

/- Move this attribute to the right file! -/
attribute [simp] MvPolynomial.coeff_zero_C

lemma totalDegree_sub_C_zero_le (p : MvPolynomial σ ℝ) :
    totalDegree (p - C (eval 0 p)) ≤ totalDegree p := by
  classical
  apply totalDegree_le_of_support_subset
  intro i hi
  rcases eq_or_ne i 0 with rfl|h'i
  · simp [constantCoeff] at hi
  · simpa [h'i.symm] using hi

end missing_polynomial

section missing_linear_algebra

open Module Submodule BigOperators

variable {K V V' ι : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
   {B : V' →ₗ[K] Dual K V} {m : ι → V'}

lemma flip_surj_of_inj (hB : Injective B) [FiniteDimensional K V'] : Surjective B.flip := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  set W : Subspace K _ := LinearMap.range B.flip
  have := W.finrank_add_finrank_dualCoannihilator_eq
  rw [Subspace.dual_finrank_eq, ← this, eq_comm, add_right_eq_self, finrank_eq_zero, eq_bot_iff]
  intro x hx
  apply hB
  ext v
  rw [Submodule.mem_dualCoannihilator] at hx
  simpa using hx _ (LinearMap.mem_range_self _ v)

/- lemma exists_predual {μ : ι → Dual K V} (hμ : LinearIndependent K μ) {s : Set ι} (hs : s.Finite)
    (i : ι) : ∃ v : V, μ i v = 1 ∧ ∀ j ∈ s, j ≠ i → μ j v = 0 := by
  have hμ := hμ.comp (_ : ↑(s ∪ {i}) → ι) Subtype.val_injective
  rw [linearIndependent_iff_injective_total] at hμ
  have : Finite ↑(s ∪ {i}) := (hs.union <| Set.finite_singleton i).to_subtype
  classical
  have ⟨v, hv⟩ := surj_of_inj hμ (Finsupp.total _ _ _ fun j ↦ if j = i then 1 else 0)
  refine ⟨v, ?_, fun j hjs hji ↦ ?_⟩
  · simpa using FunLike.congr_fun hv (Finsupp.single ⟨i, .inr rfl⟩ 1)
  · simpa [if_neg hji] using FunLike.congr_fun hv (Finsupp.single ⟨j, .inl hjs⟩ 1)

-- missing in mathlib
def LinearIndependent.fintypeIndex
    {K : Type*} {V : Type*} [DivisionRing K] [AddCommGroup V]
    [Module K V] {ι : Type u_1} [FiniteDimensional K V]
    {f : ι → V} (hf : LinearIndependent K f) :
    Fintype ι :=
  FiniteDimensional.fintypeBasisIndex <| Basis.span hf

lemma exists_predual_of_finite {μ : ι → Dual K V} [FiniteDimensional K V]
    (hμ : LinearIndependent K μ) {s : Set ι} (i : ι) :
    ∃ v : V, μ i v = 1 ∧ ∀ j ∈ s, j ≠ i → μ j v = 0 := by
  let hι := hμ.fintypeIndex
  exact exists_predual hμ (Set.toFinite s) _

lemma exists_stuff (hm : LinearIndependent K (B ∘ m)) {s : Set ι} (hs : s.Finite) (i : ι) :
    ∃ v : V, B (m i) v = 1 ∧ ∀ j ∈ s , j ≠ i → B (m j) v = 0 :=
  exists_predual hm hs i

variable (hm : LinearIndependent K (B ∘ m)) {s : Set ι} (hs : s.Finite)

def stuff (i : ι) : V := (exists_stuff hm hs i).choose

lemma stuff_eval_self (i : ι) : B (m i) (stuff hm hs i) = 1 := (exists_stuff hm hs i).choose_spec.1

lemma stuff_eval_other {i j : ι} (hj : j ∈ s) (h : j ≠ i) : B (m j) (stuff hm hs i) = 0 :=
  (exists_stuff hm hs i).choose_spec.2 j hj h

lemma foo {s : Set ι} (hs : s.Finite) (μ : V' →ₗ[K] K) :
    ∃ φ : V, ∀ v' ∈ span K (m '' s), μ v' = B v' φ := by
  use ∑ i in hs.toFinset, (μ (m i)) • stuff hm hs i
  intro v' hv'
  apply span_induction hv' (p := fun v' ↦ μ v' = B v' (∑ i in hs.toFinset, (μ (m i)) • stuff hm hs i))
  all_goals clear v' hv'
  · rintro _ ⟨i, hi, rfl⟩
    have : ∀ j ∈ hs.toFinset, j ≠ i → B (m i) (μ (m j) • stuff hm hs j) = 0 := by
      intros j _ hij
      rw [SMulHomClass.map_smul, stuff_eval_other hm hs hi hij.symm, smul_zero]
    rw [map_sum, Finset.sum_eq_single_of_mem i (hs.mem_toFinset.mpr hi) this, SMulHomClass.map_smul,
        stuff_eval_self, smul_eq_mul, mul_one]
  · simp only [_root_.map_zero, map_sum, SMulHomClass.map_smul, LinearMap.zero_apply, smul_eq_mul, mul_zero,
    Finset.sum_const_zero]
  · intros x y hx hy
    simp [map_add, hx, hy, mul_add, ← Finset.sum_add_distrib]
  · intros a v' hv'
    simp only [SMulHomClass.map_smul, hv', map_sum, smul_eq_mul, Finset.mul_sum, LinearMap.smul_apply] -/

end missing_linear_algebra

open Metric Set MeasureTheory Module
open MvPolynomial hiding support
open Function hiding eval

section normed
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E E' F  : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {n : ℕ∞} {s : Set E}

instance : FunLike (SmoothSupportedOn 𝕜 E F n s) E (fun _ ↦ F) where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective
end normed

variable {ι : Type*} [Fintype ι]
lemma MvPolynomial.continuous_eval (p: MvPolynomial ι ℝ) :
    Continuous fun x ↦ (eval x) p := by
  continuity

lemma SmoothSupportedOn.hasCompactSupport (f : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) :
    HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 1) (support_subset f)

theorem SmoothSupportedOn.continuous
    (f : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) : Continuous f :=
  ContDiff.continuous <| SmoothSupportedOn.contDiff _

theorem SmoothSupportedOn.integrable
    (f : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) :
    Integrable f :=
  Continuous.integrable_of_hasCompactSupport (continuous _) (hasCompactSupport _)

theorem SmoothSupportedOn.integrable_eval_mul (p : MvPolynomial ι ℝ)
    (f : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) :
    Integrable fun (x : EuclideanSpace ℝ ι) ↦ (eval x) p • f x := by
  simp only [smul_eq_mul]
  apply Continuous.integrable_of_hasCompactSupport
  · apply Continuous.mul
    · apply p.continuous_eval
    · apply ContDiff.continuous <| SmoothSupportedOn.contDiff _
  apply (hasCompactSupport _).mul_left

def L :
  MvPolynomial ι ℝ →ₗ[ℝ] Dual ℝ (SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) where
    toFun p :=
      { toFun := fun f ↦ ∫ x : EuclideanSpace ℝ ι, eval x p • f x
        map_add' := fun f g ↦ by
          rw [← integral_add]
          · simp only [← smul_add]; rfl
          all_goals apply SmoothSupportedOn.integrable_eval_mul
        map_smul' := fun r f ↦ by
          rw [← integral_smul]
          dsimp only [id_eq, RingHom.id_apply]
          simp only [smul_comm r]
          rfl }
    map_add' := fun p₁ p₂ ↦ by
      ext f
      dsimp only [id_eq, eq_mpr_eq_cast, AddHom.toFun_eq_coe, AddHom.coe_mk,
        RingHom.id_apply, LinearMap.coe_mk, LinearMap.add_apply]
      rw [← integral_add]
      · simp only [← add_smul, eval_add]
      all_goals apply SmoothSupportedOn.integrable_eval_mul
    map_smul' := fun r p ↦ by
      ext f
      dsimp only [id_eq, eq_mpr_eq_cast, AddHom.toFun_eq_coe, AddHom.coe_mk,
        RingHom.id_apply, LinearMap.coe_mk, LinearMap.smul_apply]
      rw [← integral_smul]
      simp only [← evalₗ_apply, SMulHomClass.map_smul, ← smul_assoc]
      rfl

open Topology
lemma inj_L (ι : Type*) [Fintype ι] : Injective (L (ι := ι)) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  suffices : ∀ᵐ x : EuclideanSpace ℝ ι, x ∈ closedBall 0 1 → eval x p = 0
  · sorry -- simp_rw [MvPolynomial.funext_iff, map_zero]
    -- Polynomial.eq_zero_of_infinite_isRoot
  -- intro x₀ hx₀
  -- by_contra hpx₀
  have h2p : LocallyIntegrable (fun x : EuclideanSpace ℝ ι ↦ eval x p) :=
    continuous_eval p |>.locallyIntegrable
  apply (ProperSpace.isCompact_closedBall _ _).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (h2p.locallyIntegrableOn _)
  intro g hg h2g
  let ϕ : SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1) :=
    ⟨g, h2g, hg⟩
  apply_fun (· ϕ) at hp
  simpa [mul_comm (g _), L] using hp

lemma hairer (N : ℕ) (ι : Type*) [Fintype ι] :
    ∃ (ρ : EuclideanSpace ℝ ι → ℝ), tsupport ρ ⊆ closedBall 0 1 ∧ ContDiff ℝ ⊤ ρ ∧
    ∀ (p : MvPolynomial ι ℝ), p.totalDegree ≤ N →
    ∫ x : EuclideanSpace ℝ ι, eval x p • ρ x = eval 0 p := by
  have := (inj_L ι).comp (restrictTotalDegree ι ℝ N).injective_subtype
  rw [← LinearMap.coe_comp] at this
  obtain ⟨⟨φ, supφ, difφ⟩, hφ⟩ := surj_of_inj this ((evalAtₗ 0).comp <| Submodule.subtype _)
  refine ⟨φ, supφ, difφ, fun P hP ↦ ?_⟩
  exact FunLike.congr_fun hφ ⟨P, (mem_restrictTotalDegree ι N P).mpr hP⟩

lemma hairer2 (N : ℕ) (ι : Type*) [Fintype ι] :
    ∃ (ρ : EuclideanSpace ℝ ι → ℝ), tsupport ρ ⊆ closedBall 0 1 ∧ ContDiff ℝ ⊤ ρ ∧
    ∀ (p : MvPolynomial ι ℝ), p.totalDegree ≤ N →
    ∫ x : EuclideanSpace ℝ ι, eval x p • ρ x = eval 0 p := by
  -- deal first with the stupid case where the index set is empty, as in this case one can't find
  -- a sequence of linearly independent functions, but the function `ρ = 1` will do
  rcases isEmpty_or_nonempty ι with hι|hι
  · refine ⟨fun _x ↦ 1, ?_, contDiff_const, ?_⟩
    · intro x _hx
      rw [show x = 0 from Subsingleton.elim _ _]
      exact mem_closedBall_self zero_le_one
    · simp [volume_euclideanSpace_eq_dirac ι]
  obtain ⟨f, hf, h2f⟩ := step ι
  obtain ⟨ρ, hρ, h2ρ⟩ := exists_affineSpan_zero (nonConstantTotalDegreeLE ℝ ι N) L f hf
  have h3ρ : ∫ x, ρ x = 1 := by
    apply affineSpan_induction hρ
    · rintro x ⟨n, rfl⟩
      exact h2f n
    · intro c u v w hu hv hw
      change ∫ (x : EuclideanSpace ℝ ι), c • (u x - v x) + w x = 1
      rw [integral_add, integral_smul, integral_sub, hu, hv, hw]
      · simp
      · exact SmoothSupportedOn.integrable _
      · exact SmoothSupportedOn.integrable _
      · exact ((SmoothSupportedOn.integrable _).sub (SmoothSupportedOn.integrable _)).smul c
      · exact SmoothSupportedOn.integrable _
  refine ⟨ρ, ?_, ?_, ?_⟩
  · refine closure_minimal ?_ isClosed_ball
    refine support_subset_of_mem_affineSpan ℝ hρ |>.trans ?_
    simp only [mem_range, iUnion_exists, iUnion_iUnion_eq', iUnion_subset_iff, support_subset,
      forall_const]
  · refine contDiff_of_mem_affineSpan ℝ hρ ?_
    simp only [mem_range, SmoothSupportedOn.contDiff, forall_exists_index, implies_true,
      forall_const, Subtype.forall]
  · intro p hp
    obtain ⟨q, r, hq, rfl, h2q⟩ : ∃ q r, constantCoeff q = 0 ∧ p = q + C r ∧ totalDegree q ≤ N := by
      refine ⟨p - C (eval 0 p), eval 0 p, by simp, by ring, (totalDegree_sub_C_zero_le p).trans hp⟩
    simp only [map_add, eval_C, smul_eq_mul, add_mul, eval_zero, hq, constantCoeff_C, zero_add]
    rw [integral_add]
    · simp [integral_mul_left, h3ρ]
      exact h2ρ q ⟨h2q, hq⟩
    · exact SmoothSupportedOn.integrable_eval_mul _ _
    · exact (SmoothSupportedOn.integrable _).const_mul _
