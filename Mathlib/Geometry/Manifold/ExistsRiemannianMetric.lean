/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Dominic Steinitz
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.LocallyConvex.BilinearFormBounded

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove the existence of a smooth Riemannian metric.

The idea is that there are two equivalent ways of defining a bilinear positive definite form:

  1) pull back the inner product on `F` via the inverse trivialisation
  2) push forward vectors and then apply the inner product on `F`

It turns out that using (1) makes proving smoothness straightforward and
`g_bilin_smooth_on_chart` proves that locally `g_bilin i` is smooth (the trick is to make
the set on which this is true small enough hence the intersection:
`((trivializationAt F E i).baseSet ∩ (chartAt HB i).source)`).
This can then be used to prove global smoothness via a partition of unity.

However it is not so clear how one uses (1) to prove positive definiteness.
This is where (2) comes in. With this definition, it is straightforward to prove
positivity, definiteness and symmetry.

We then prove that the two definitions are equal, which allows us to prove that (1) is symmetric,
positive and definite.

But one is still not done. Mathlib's definition requires von Neumann boundedness,
which holds because `F` is finite-dimensional.

-/

open Set Bundle ContDiff Manifold Trivialization SmoothPartitionOfUnity

/-
`E` is a vector bundle over `B` with model fiber `F`. The `InnerProductSpace` assumption also
implies the `NormedSpace` assumption required by `VectorBundle`.
-/
variable {B : Type*} {F : Type*} {E : B → Type*}
  [TopologicalSpace B]
  [NormedAddCommGroup F] [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [InnerProductSpace ℝ F] [VectorBundle ℝ F E]

-- The usual setup for a manifold `B` modelled on `HB` with model-with-corners `IB` into `EB`.
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB]
  [ChartedSpace HB B]
  {IB : ModelWithCorners ℝ EB HB}

/-! ### Definition (1): pulling back the inner product along the inverse trivialisation

This is the definition for which smoothness is straightforward. Nothing here needs the fibers
to be anything beyond topological vector spaces, and nothing here needs `F` to be
finite-dimensional.
-/

noncomputable section

variable [ContMDiffVectorBundle ω F E IB]

def g_bilin (i b : B) :
 (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
             (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ)) :=
  ⟨b, (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
        (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i).symm b (innerSL ℝ)⟩

lemma inCoordinates_apply_eq₂_spec
    {x₀ x : B} {ϕ : E x →L[ℝ] E x →L[ℝ] ℝ} {v w : F}
    (h₁x : x ∈ (trivializationAt F E x₀).baseSet) :
    ContinuousLinearMap.inCoordinates F E (F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] ℝ) x₀ x x₀ x ϕ v w =
    ϕ ((trivializationAt F E x₀).symm x v) ((trivializationAt F E x₀).symm x w) := by
  rw [inCoordinates_apply_eq₂ h₁x h₁x (by simp [Trivial.fiberBundle_trivializationAt'])]
  simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization]

lemma inCoordinates_apply_eq₂_spec_symm
    (x₀ x : B) (hb : x ∈ (trivializationAt F E x₀).baseSet)
    (ϕ : F →L[ℝ] F →L[ℝ] ℝ) (u v : E x) :
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x₀).symm x ϕ u v =
    ϕ (trivializationAt F E x₀ |>.continuousLinearMapAt ℝ x u)
      (trivializationAt F E x₀ |>.continuousLinearMapAt ℝ x v) := by
  letI ψ := FiberBundle.trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
      (fun (x : B) ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x₀
  letI χ := trivializationAt F E x₀
  letI w := ψ.symm x ϕ
  have hc : x ∈ ψ.baseSet := by
    rw [hom_trivializationAt_baseSet]
    simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
    Trivial.trivialization_baseSet, inter_univ, inter_self]
    exact mem_of_subset_of_mem (fun ⦃a⦄ a_1 ↦ a_1) hb
  have h1 : ∀ u v,
      (((continuousLinearMapAt ℝ ψ x) (ψ.symmL ℝ x ϕ)) u) v = ϕ u v :=
    fun u v => by rw [continuousLinearMapAt_symmL ψ hc]
  have h2 : ∀ u v, ϕ u v = w (χ.symm x u) (χ.symm x v) := fun u v => by
    rw [← h1, continuousLinearMapAt_apply, linearMapAt_apply, hom_trivializationAt_apply,
      if_pos hc, ← inCoordinates_apply_eq₂_spec hb]
    rw [symmL_apply]
    exact hc
  have h3 := symmL_continuousLinearMapAt (R := ℝ) (trivializationAt F E x₀) hb u
  rw [symmL_apply] at h3
  · have h4 := symmL_continuousLinearMapAt (R := ℝ) (trivializationAt F E x₀) hb v
    rw [symmL_apply] at h4
    · rw [show w u v = ϕ (χ.continuousLinearMapAt ℝ x u) (χ.continuousLinearMapAt ℝ x v) from by
        rw [h2 (χ.continuousLinearMapAt ℝ x u) (χ.continuousLinearMapAt ℝ x v), h3, h4]]
    · exact hb
  · exact hb

lemma g_bilin_smooth_on_chart (i : B) :
  ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (g_bilin (F := F) (E := E) i)
    ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) := by
  unfold g_bilin
  intro b hb
  letI ψ := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i
  letI innerAtP : B → F →L[ℝ] F →L[ℝ] ℝ := fun x ↦ innerSL ℝ
  have h4 : ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
    (fun c => (c, innerAtP c)) ((trivializationAt F E i).baseSet ∩ (chartAt HB i).source) :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have h5 : (trivializationAt F E i).baseSet ∩ (chartAt HB i).source ⊆
  (fun c ↦ (c, innerAtP c)) ⁻¹' ψ.target := by
    intro c hc
    simp only [Set.mem_preimage]
    rw [ψ.target_eq]
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    have baseSet_eq : (trivializationAt F E i).baseSet =
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ) (fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) i).baseSet := by
      simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
               Trivial.trivialization_baseSet, Set.inter_univ, Set.inter_self]
    rw [←baseSet_eq]
    exact hc.1
  refine (ContMDiffOn.congr ((contMDiffOn_symm _).comp h4 h5) ?_) b hb
  intro y hy
  simp only [Function.comp_apply]
  ext
  · rfl
  · simp only [innerAtP]
    rw [Trivialization.symm_apply ψ _ (innerSL ℝ)]
    · simp
    · exact (mk_mem_target ψ).mp (h5 hy)

noncomputable def g_global_bilin (f : SmoothPartitionOfUnity B IB B) (p : B) :
    E p →L[ℝ] (E p →L[ℝ] ℝ) :=
      ∑ᶠ (j : B), (f j) p • (g_bilin (F := F) j p).snd

lemma g_global_bilin_smooth (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source)) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g_global_bilin (F := F) (E := E) f x)) := by
  let s_loc : (i : B) → (b : B) → (E b →L[ℝ] (E b →L[ℝ] Trivial B ℝ b)) :=
    fun i b => (g_bilin (F := F) (E := E) i b).snd
  have hj (j : B) : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x ((f j x) • s_loc j x)) := by
    refine ContMDiffOn.smul_section_of_tsupport ?_
      ((trivializationAt F E j).open_baseSet.inter (chartAt HB j).open_source) (h_sub j)
      (g_bilin_smooth_on_chart j)
    exact ((f j).contMDiff).of_le (sup_eq_left.mp rfl) |>.contMDiffOn
  unfold g_global_bilin
  apply ContMDiff.finsum_section_of_locallyFinite ?_ hj
  apply f.locallyFinite.subset fun i x hx ↦ ?_
  exact left_ne_zero_of_smul hx

end

/-! ### Definition (2): pushing vectors forward and applying the inner product on `F`

This is the definition for which positivity, definiteness and symmetry are straightforward, and
we then show it agrees with definition (1).

The fibers are assumed to be topological vector spaces --- although this is automatic, since each
trivialization restricts to a linear homeomorphism `E x ≃ F`, Mathlib has no such instance, so it
must be given explicitly.
-/

noncomputable section

variable [FiniteDimensional ℝ F]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)] [∀ x, T2Space (E x)]

variable (F) in
noncomputable
def g_bilin_aux (i p : B) : E p →L[ℝ] (E p →L[ℝ] ℝ) := by
  let χ := trivializationAt F E i
  let φ := χ.continuousLinearMapAt ℝ p
  let bilinear : E p →ₗ[ℝ] E p →ₗ[ℝ] ℝ :=
    LinearMap.compl₁₂ (innerSL ℝ).toLinearMap₁₂ φ.toLinearMap φ.toLinearMap
  by_cases hp : p ∈ χ.baseSet
  · let tvsEquiv : E p ≃ₗ[ℝ] F := Trivialization.linearEquivAt ℝ χ p hp
    haveI : FiniteDimensional ℝ (E p) := tvsEquiv.symm.finiteDimensional
    let bilinear_cont_inner : E p →ₗ[ℝ] E p →L[ℝ] ℝ := {
      toFun := fun u => LinearMap.toContinuousLinearMap (bilinear u)
      map_add' := by simp only [map_add, implies_true]
      map_smul' := by simp only [map_smul, RingHom.id_apply, implies_true]
    }
    exact LinearMap.toContinuousLinearMap bilinear_cont_inner
  · exact 0

lemma g_nonneg {j b : B} (v : E b) :
    0 ≤ ((g_bilin_aux F j b).toFun v).toFun v := by
  unfold g_bilin_aux
  simp only
  split_ifs
  · exact inner_self_nonneg (𝕜 := ℝ)
  · simp

lemma g_pos {i b : B}
    (hb : b ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source)
    (v : E b) (hv : v ≠ 0) :
    0 < ((g_bilin_aux F i b).toFun v).toFun v := by
  unfold g_bilin_aux
  simp only
  rw [dif_pos hb.1]
  let χ := trivializationAt F E i
  let φ := χ.continuousLinearMapAt ℝ b
  have h1 : φ v ≠ 0 := by
    rw [← coe_continuousLinearEquivAt_eq χ hb.1]
    exact AddEquivClass.map_ne_zero_iff.mpr hv
  exact Std.lt_of_le_of_ne (inner_self_nonneg (𝕜 := ℝ))
    (inner_self_ne_zero.mpr h1).symm

theorem g_bilin_symm_aux (i p : B) (v w : E p) :
    ((g_bilin_aux F i p).toFun v).toFun w =
    ((g_bilin_aux F i p).toFun w).toFun v := by
  unfold g_bilin_aux
  simp only
  split_ifs
  · exact real_inner_comm _ _
  · rfl

def g_global_bilin_aux (f : SmoothPartitionOfUnity B IB B) (p : B) :
    E p →L[ℝ] (E p →L[ℝ] ℝ) :=
  ∑ᶠ (j : B), (f j) p • g_bilin_aux F j p

private def evalAt (b : B) (v w : E b) :
    (E b →L[ℝ] (E b →L[ℝ] ℝ)) →+ ℝ where
  toFun f := (f.toFun v).toFun w
  map_zero' := by simp
  map_add' _ _ := rfl

private lemma g_global_bilin_aux_support_finite (f : SmoothPartitionOfUnity B IB B) (b : B) :
    (Function.support fun j ↦ ((f j) b • (g_bilin_aux F j b) :
      E b →L[ℝ] E b →L[ℝ] ℝ)).Finite :=
  (f.locallyFinite'.point_finite b).subset (fun i hi => by
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi; exact hi.1)

set_option maxHeartbeats 800000 in
-- It times out otherwise
lemma riemannian_metric_symm_aux (f : SmoothPartitionOfUnity B IB B) (b : B)
  (v w : E b) :
  ((g_global_bilin_aux (F := F) f b).toFun v).toFun w
   =
  ((g_global_bilin_aux (F := F) f b).toFun w).toFun v := by
  unfold g_global_bilin_aux
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  have h1 := g_global_bilin_aux_support_finite (F := F) (E := E) f b
  rw [finsum_eq_sum _ h1]
  letI h : (j : B) → (E b →L[ℝ] (E b →L[ℝ] ℝ)) := fun j ↦ (f j) b • g_bilin_aux F j b
  have h2 : (Function.support h) ⊆ h1.toFinset := Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a
  have h3 : ∀ (u v : E b),
      ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun u).toFun v =
      ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun u).toFun v := by
    intros u v
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [sum_apply, sum_apply]
  calc ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun v).toFun w
      = ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun v).toFun w := (h3 v w).symm
    _ = ∑ᶠ (j : B), (((f j) b • g_bilin_aux F j b).toFun v).toFun w :=
          (map_finsum_of_support_subset (φ := (evalAt b v w : (E b →L[ℝ] (E b →L[ℝ] ℝ)) →+ ℝ))
            (f := h) (s := h1.toFinset) h2).symm
    _ = ∑ᶠ (j : B), (((f j) b • g_bilin_aux F j b).toFun w).toFun v :=
          finsum_congr (fun j ↦ congrArg (HMul.hMul ((f j) b)) (g_bilin_symm_aux j b v w))
    _ = ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun w).toFun v :=
          map_finsum_of_support_subset (evalAt b w v) (f := h) (s := h1.toFinset) h2
    _ = ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun w).toFun v := h3 w v

set_option maxHeartbeats 800000 in
-- It times out otherwise
lemma riemannian_metric_pos_def_aux (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  (b : B) {v : E b} (hv : v ≠ 0) :
  0 < g_global_bilin_aux (F := F) f b v v := by
  unfold g_global_bilin_aux
  have h1 := g_global_bilin_aux_support_finite (F := F) (E := E) f b
  rw [finsum_eq_sum _ h1]
  have h2 : ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun v).toFun v =
            ((∑ j ∈ h1.toFinset, (f j) b • g_bilin_aux F j b).toFun v).toFun v := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [sum_apply, sum_apply]
  let h : (j : B) → (E b →L[ℝ] (E b →L[ℝ] ℝ)) := fun j ↦ (f j) b • g_bilin_aux F j b
  let h' x := f x b * ((g_bilin_aux F x b).toFun v).toFun v
  have h3 : (Function.support h) ⊆ h1.toFinset := Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a
  have ⟨i, h5⟩ : ∃ i, 0 < f i b := by
    by_contra! hneg
    have : ∀ (x : B), f x b = 0 := fun x => le_antisymm (hneg x) (f.nonneg' x b)
    exact absurd ((finsum_eq_zero_of_forall_eq_zero this).symm.trans (f.sum_eq_one' b trivial))
      one_ne_zero.symm
  have h6 : b ∈ (trivializationAt F E i).baseSet ∩ (chartAt HB i).source :=
    hf i (subset_closure (Function.mem_support.mpr h5.ne'))
  have h7 : ∀ j, 0 ≤ h' j := fun j => mul_nonneg (f.nonneg' j b) (g_nonneg v)
  have h8 : ∃ j, 0 < h' j := ⟨i, mul_pos h5 (g_pos h6 v hv)⟩
  have h9 : (Function.support h').Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro x hx
    simp only [Function.support_mul, Set.mem_inter_iff, Function.mem_support, ne_eq, h'] at hx
    exact mul_ne_zero_iff.mp (mul_ne_zero_iff.mpr hx) |>.1
  have hb : ∑ᶠ i, h' i =
            ∑ j ∈ h1.toFinset, (((f j) b • g_bilin_aux F j b).toFun v).toFun v :=
    (map_finsum_of_support_subset (evalAt b v v) (f := h) (s := h1.toFinset) h3) ▸ rfl
  exact lt_of_lt_of_eq (finsum_pos h7 h8 h9) (hb.trans h2)

lemma riemannian_unit_ball_bounded_aux (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  [∀ x, FiniteDimensional ℝ (E x)] (b : B) :
    Bornology.IsVonNBounded ℝ {v : E b | g_global_bilin_aux (F := F) f b v v < 1} :=
  isVonNBounded_of_posDef (g_global_bilin_aux (F := F) f b)
    (fun v => by
      rcases eq_or_ne v (0 : E b) with rfl | hv
      · simp
      · exact le_of_lt (riemannian_metric_pos_def_aux f hf b hv))
    (riemannian_metric_symm_aux f b)
    (fun v h => by
      by_contra hv
      exact lt_irrefl 0 (h ▸ riemannian_metric_pos_def_aux f hf b hv))

/-! ### The two definitions agree

Transferring symmetry, positive definiteness and von Neumann boundedness from (2) to (1).
-/

lemma g_global_bilin_eq
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (p : B) (u v : E p) :
    g_global_bilin (F := F) (E := E) f p u v =
    g_global_bilin_aux (F := F) f p u v := by
  have : g_global_bilin (F := F) (E := E) f p = g_global_bilin_aux (F := F) f p := by
    unfold g_global_bilin g_global_bilin_aux
    congr 1
    ext j
    congr 2
    ext u v
    by_cases h : (f j) p = 0
    · have h2 : (f j) p • (g_bilin (F := F) (E := E) j p).snd = 0 :=
        smul_eq_zero_of_left h (g_bilin j p).snd
      have h3 : (f j) p • g_bilin_aux F (E := E) j p = 0 :=
        smul_eq_zero_of_left h (g_bilin_aux F j p)
      rw [h2, h3]
      rfl
    · have hp : p ∈ tsupport (f j) := by
        rw [tsupport]
        exact subset_closure h
      have hsupp : p ∈ (trivializationAt F E j).baseSet ∩ (chartAt HB j).source :=
        hf j hp
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      congr 1
      unfold g_bilin g_bilin_aux
      simp only
      rw [dif_pos hsupp.1]
      conv_lhs => rw [inCoordinates_apply_eq₂_spec_symm j p hsupp.1 (innerSL ℝ) u v]
      rfl
  rw [this]

lemma riemannian_metric_symm
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v w : E b) :
    g_global_bilin (F := F) (E := E) f b v w =
    g_global_bilin (F := F) (E := E) f b w v := by
  rw [g_global_bilin_eq f hf b v w, g_global_bilin_eq f hf b w v]
  exact (riemannian_metric_symm_aux (F := F) f b v w)

lemma riemannian_metric_pos_def
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v : E b) (hv : v ≠ 0) :
    0 < g_global_bilin (F := F) (E := E) f b v v := by
  rw [g_global_bilin_eq (F := F) (E := E) f hf b v v]
  exact riemannian_metric_pos_def_aux f hf b hv

lemma riemannian_unit_ball_bounded (f : SmoothPartitionOfUnity B IB B)
  (hf : f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source))
  [∀ x, FiniteDimensional ℝ (E x)] (b : B) :
  Bornology.IsVonNBounded ℝ
    {v : E b | g_global_bilin (F := F) (E := E) f b v v < 1} := by
  simp_rw [fun v => g_global_bilin_eq f hf b v v]
  exact riemannian_unit_ball_bounded_aux f hf b

end

/-! ### Existence -/

section

-- `FiniteDimensional ℝ EB`, `SigmaCompactSpace B` and `T2Space B` are the hypotheses of
-- `SmoothPartitionOfUnity.exists_isSubordinate`.
variable [FiniteDimensional ℝ EB] [SigmaCompactSpace B] [T2Space B]
  [FiniteDimensional ℝ F]
  [IsManifold IB ω B] [ContMDiffVectorBundle ω F E IB]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul ℝ (E x)] [∀ x, T2Space (E x)]

/--
Existence of a smooth Riemannian metric on a manifold.
-/
public theorem exists_riemannian_metric :
  Nonempty (ContMDiffRiemannianMetric (IB := IB) (n := ∞) (F := F) (E := E)) :=
  let ⟨f, hf⟩ : ∃ (f : SmoothPartitionOfUnity B IB B),
      f.IsSubordinate (fun x ↦ (trivializationAt F E x).baseSet ∩ (chartAt HB x).source) := by
    apply SmoothPartitionOfUnity.exists_isSubordinate
    · exact isClosed_univ
    · intro i
      exact IsOpen.inter (trivializationAt F E i).open_baseSet (chartAt HB i).open_source
    · intro b _
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨b, FiberBundle.mem_baseSet_trivializationAt' b, mem_chart_source HB b⟩
  ⟨{ inner := g_global_bilin (F := F) f
     symm := riemannian_metric_symm f hf
     pos := riemannian_metric_pos_def f hf
     isVonNBounded := by
      haveI : ∀ x, FiniteDimensional ℝ (E x) := fun x ↦
        (Trivialization.linearEquivAt ℝ (trivializationAt F E x) x
        (FiberBundle.mem_baseSet_trivializationAt' x)).symm.finiteDimensional
      exact riemannian_unit_ball_bounded f hf
     contMDiff := g_global_bilin_smooth f hf }⟩

end
