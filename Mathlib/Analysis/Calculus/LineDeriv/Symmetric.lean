import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

open Filter Function Set Metric AffineMap Asymptotics
open scoped unitInterval Convex Topology

variable {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E} {l : Filter α}

/-- MVT-like estimate in terms of `HasLineDerivAt`.

TODO: it should be enough to require continuity on `[a -[ℝ] a + v]`
and differentiability for `t ∈ Ioo 0 1`, i.e., on `openSegment ℝ a (a + v)`. -/
theorem norm_sub_sub_le_of_hasLineDerivAt_add_smul {a v : E} {f' : ℝ → F} {w : F} {C : ℝ}
    (h₁ : ∀ t ∈ I, HasLineDerivAt ℝ f (f' t) (a + t • v) v) (h₂ : ∀ t ∈ I, ‖f' t - w‖ ≤ C) :
    ‖f (a + v) - f a - w‖ ≤ C := by
  set g : ℝ → F := fun t ↦ f (a + t • v) - t • w
  have hg (t : ℝ) (ht : t ∈ I) : HasDerivAt g (f' t - w) t := by
    simpa [g, sub_smul, add_assoc, comp_def]
      using (h₁ t ht).sub (((hasDerivAt_id _).const_add t).smul_const w)
        |>.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  simpa [g, sub_right_comm] using norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun x hx ↦ (hg x hx).hasDerivWithinAt) (fun t ht ↦ h₂ t <| Ico_subset_Icc_self ht)

theorem norm_sub_sub_le_of_hasLineDerivAt_lineMap {a b : E} {f' : ℝ → F} {w : F} {C : ℝ}
    (h₁ : ∀ t ∈ I, HasLineDerivAt ℝ f (f' t) (lineMap a b t) (b - a))
    (h₂ : ∀ t ∈ I, ‖f' t - w‖ ≤ C) : ‖f b - f a - w‖ ≤ C := by
  simp only [lineMap_apply_module', add_comm _ a] at h₁
  simpa using norm_sub_sub_le_of_hasLineDerivAt_add_smul h₁ h₂

namespace Asymptotics.IsLittleO

/-- Given a family of functions `f a`
and a family of parallelograms with base vertex `x₀ a` and vectors `v a` and `w a` for sides,
assume that eventually along a filter `l` in the parameter space, the following properties hold:

- the function `f a` is differentiable on the sides `[x₀ a -[ℝ] x₀ a + v a]`
  and `[x₀ a + w a -[ℝ] x₀ a + w a + v a]`,
  with the corresponding line derivatives `f₁' a t` and `f₂' a t;
- the difference of these derivatives at the corresponding points
  is given by `f₂' a t - f₁' a t = f'' a + o(ε a)`,
  where `f'' a` and `ε a` do not depend on `t`.

Then the alternate sum of the values of `f a` at the vertices of the parallelogram
is given by `f'' a + o(ε a)` as well.

In the main application, `f` and `f''` do not depend on the parameter,
and `f''` is one of the mixed second derivatives of `f`.
Comparing these estimates
for the families of parallelograms with sides `(a • v, a • w)`, `a → 𝓝[>] 0`, and `(a • w, a • v)`
implies symmetry of the mixed partial derivatives.

We formulate this lemma with all objects depending on the parameter as a proof of concept.
All subsequent lemmas in this file deal with specific functions and families of parallelograms.
We may decide to generalize the other lemmas too,
if we ever need to make one of the estimates below uniform in a parameter.

Note: this lemma assumes that the function `f` is line differentiable
at every point of the two sides of the parallelogram, including the endpoints.
We can weaken the assumption to `f` being continuous on these sides
and differentiable on the open segments,
but this would require improvements to our versions of the mean value theorem
and we never need it in practice. -/
lemma alternate_sum_square_of_hasLineDerivAt_of_isLittleO
    {x₀ v w : α → E} {f₁' f₂' : α → ℝ → F} {f'' : α → F} {ε : α → ℝ} {f : α → E → F}
    (h₁ : ∀ᶠ a in l, ∀ t ∈ I, HasLineDerivAt ℝ (f a) (f₁' a t) (x₀ a + t • v a) (v a))
    (h₂ : ∀ᶠ a in l, ∀ t ∈ I, HasLineDerivAt ℝ (f a) (f₂' a t) (x₀ a + w a + t • v a) (v a))
    (h₃ : (fun (a, t) ↦ f₂' a t - f₁' a t - f'' a) =o[l ×ˢ 𝓟 I] fun (a, _) ↦ ε a) :
    (fun a ↦ f a (x₀ a + v a + w a) - f a (x₀ a + v a) - f a (x₀ a + w a) + f a (x₀ a) - f'' a)
      =o[l] ε := by
  have : ∀ᶠ a in l, ∀ t ∈ I,
      HasLineDerivAt ℝ ((f a <| · + w a) - f a) (f₂' a t - f₁' a t) (x₀ a + t • v a) (v a) := by
    filter_upwards [h₁, h₂] with a ha₁ ha₂ t ht
    unfold HasLineDerivAt at ha₁ ha₂ ⊢
    simpa [add_right_comm] using (ha₂ t ht).sub (ha₁ t ht)
  simp only [isLittleO_iff, eventually_prod_principal_iff] at h₃ ⊢
  intro c hc
  filter_upwards [this, h₃ hc] with a ha hac
  simpa [add_right_comm, sub_add] using norm_sub_sub_le_of_hasLineDerivAt_add_smul ha hac

theorem alternate_sum_square_smul_of_hasLineDerivAt_of_isLittleO
    {v w : E} {x₀ : α → E} {f' : E → F} {f'' : F} {ε δ : α → ℝ}
    (hs : ∀ x ∈ s, HasLineDerivAt ℝ f (f' x) x v)
    (h₁ : ∀ᶠ a in l, [x₀ a -[ℝ] x₀ a + ε a • v] ⊆ s)
    (h₂ : ∀ᶠ a in l, [x₀ a + δ a • w -[ℝ] x₀ a + δ a • w + ε a • v] ⊆ s)
    (h₃ : (fun (a, t) ↦ f' (x₀ a + δ a • w + t • ε a • v) - f' (x₀ a + t • ε a • v) - δ a • f'')
      =o[l ×ˢ 𝓟 I] fun (a, _) ↦ δ a) :
    (fun a ↦ f (x₀ a + ε a • v + δ a • w) - f (x₀ a + ε a • v)
      - f (x₀ a + δ a • w) + f (x₀ a) - ε a • δ a • f'') =o[l] (fun a ↦ ε a * δ a) := by
  simp only [segment_eq_image'] at h₁ h₂
  apply alternate_sum_square_of_hasLineDerivAt_of_isLittleO
  · filter_upwards [h₁] with a ha t ht
    refine (hs _ <| ha ⟨t, ht, ?_⟩).smul _
    simp
  · filter_upwards [h₂] with a ha t ht
    refine (hs _ <| ha ⟨t, ht, ?_⟩).smul _
    simp
  simpa [smul_add, smul_sub] using (isBigO_refl (ε ∘ Prod.fst) _).smul_isLittleO h₃

theorem alternate_sum_square_smul_of_hasLineDerivAt
    {x₀ v w : E} {f' f'' : E → F}
    (hs : ∀ᶠ ε : ℝ × ℝ in 𝓝[≥] 0, x₀ + ε.1 • v + ε.2 • w ∈ s)
    (hf : ∀ x ∈ s, HasLineDerivAt ℝ f (f' x) x v)
    (hf' : ∀ x ∈ s, HasLineDerivAt ℝ f' (f'' x) x w)
    (hf'' : ContinuousWithinAt f'' s x₀) :
    (fun ε : ℝ × ℝ ↦ f (x₀ + ε.1 • v + ε.2 • w) - f (x₀ + ε.1 • v) - f (x₀ + ε.2 • w) + f x₀
      - ε.1 • ε.2 • f'' x₀) =o[𝓝[≥] 0] (fun ε ↦ ε.1 * ε.2) := by
  rw [Ici_prod_eq, nhdsWithin_prod_eq, Prod.zero_eq_mk]
  have H : ∀ c > (0 : ℝ), ∃ a > (0 : ℝ), ∀ ε ∈ Icc 0 a, ∀ δ ∈ Icc 0 a,
      x₀ + ε • v + δ • w ∈ s ∧ ‖f'' (x₀ + ε • v + δ • w) - f'' x₀‖ < c := by
    intro c hc
    have htendsto := tendsto_nhdsWithin_iff.mpr
      ⟨Continuous.tendsto' (by fun_prop) 0 x₀ (by simp) |>.mono_left nhdsWithin_le_nhds, hs⟩
    have hmem : s ∩ f'' ⁻¹' (ball (f'' x₀) c) ∈ 𝓝[s] x₀ :=
      inter_mem self_mem_nhdsWithin (hf'' <| ball_mem_nhds _ hc)
    simpa only [Ici_prod_eq, nhdsWithin_prod_eq, Prod.zero_eq_mk, ← dist_eq_norm,
      nhdsGE_basis_Icc.prod_self.mem_iff, prod_subset_iff, mem_map] using htendsto hmem
  rcases H 1 one_pos with ⟨a, ha₀, ha⟩
  apply alternate_sum_square_smul_of_hasLineDerivAt_of_isLittleO hf
  · filter_upwards [tendsto_fst (Icc_mem_nhdsGE ha₀)] with ⟨ε, _⟩ ⟨hε₀, hεa⟩
    rw [segment_eq_image', image_subset_iff]
    intro θ hθ
    simpa [mul_smul] using ha (θ * ε) ⟨mul_nonneg hθ.1 hε₀,
      (mul_le_of_le_one_left hε₀ hθ.2).trans hεa⟩ 0 (by simp [ha₀.le]) |>.1
  · filter_upwards [prod_mem_prod (Icc_mem_nhdsGE ha₀) (Icc_mem_nhdsGE ha₀)] with ⟨ε, δ⟩ ⟨hε, hδ⟩
    rw [segment_eq_image', image_subset_iff]
    intro θ hθ
    simpa [mul_smul, add_right_comm] using ha (θ * ε) ⟨mul_nonneg hθ.1 hε.1,
      (mul_le_of_le_one_left hε.1 hθ.2).trans hε.2⟩ δ hδ |>.1
  · rw [isLittleO_iff]
    intro c hc
    simp only [eventually_prod_principal_iff]
    rcases H c hc with ⟨b, hb₀, hb⟩
    filter_upwards [prod_mem_prod (Icc_mem_nhdsGE hb₀) (Icc_mem_nhdsGE hb₀)]
      with ⟨ε, δ⟩ ⟨hε, hδ⟩ t ht
    simp only [smul_smul, add_right_comm _ (δ • w)] at *
    apply norm_sub_sub_le_of_hasLineDerivAt_add_smul
    · refine fun θ hθ ↦ (hf' _ ?_).smul _
      rw [smul_smul]
      exact hb _ ⟨mul_nonneg ht.1 hε.1, (mul_le_of_le_one_left hε.1 ht.2).trans hε.2⟩ _
        ⟨mul_nonneg hθ.1 hδ.1, (mul_le_of_le_one_left hδ.1 hθ.2).trans hδ.2⟩ |>.1
    · intro θ hθ
      simp only [← smul_sub, norm_smul, Real.norm_of_nonneg hδ.1, mul_comm c, smul_smul]
      refine mul_le_mul_of_nonneg_left (hb _ ?_ _ ?_).2.le hδ.1
      exacts [⟨mul_nonneg ht.1 hε.1, (mul_le_of_le_one_left hε.1 ht.2).trans hε.2⟩,
        ⟨mul_nonneg hθ.1 hδ.1, (mul_le_of_le_one_left hδ.1 hθ.2).trans hδ.2⟩]

end Asymptotics.IsLittleO

theorem tendsto_alternate_sum_square_smul_of_hasLineDerivAt
    {x₀ v w : E} {f' f'' : E → F}
    (hs : ∀ᶠ ε : ℝ × ℝ in 𝓝[≥] 0, x₀ + ε.1 • v + ε.2 • w ∈ s)
    (hf : ∀ x ∈ s, HasLineDerivAt ℝ f (f' x) x v)
    (hf' : ∀ x ∈ s, HasLineDerivAt ℝ f' (f'' x) x w)
    (hf'' : ContinuousWithinAt f'' s x₀) :
    Tendsto (fun ε : ℝ × ℝ ↦
        (ε.1 * ε.2)⁻¹ • (f (x₀ + ε.1 • v + ε.2 • w) - f (x₀ + ε.1 • v) - f (x₀ + ε.2 • w) + f x₀))
      (𝓝[Ioi 0 ×ˢ Ioi 0] 0) (𝓝 (f'' x₀)) := by
  simp only [← nhds_translation_sub (f'' x₀), tendsto_comap_iff, comp_def]
  refine IsLittleO.alternate_sum_square_smul_of_hasLineDerivAt hs hf hf' hf''
    |>.mono ?_ |>.tendsto_inv_smul_nhds_zero |>.congr' ?_
  · rw [Ici_prod_eq]
    gcongr <;> exact Ioi_subset_Ici_self
  · filter_upwards [self_mem_nhdsWithin] with ⟨ε, δ⟩ ⟨hε, hδ⟩
    simp [smul_sub, mul_smul, hε.out.ne', hδ.out.ne']

theorem symmetric_of_hasLineDerivAt_of_continuousWithinAt {x₀ v w : E} {fv fw fvw fwv : E → F}
    (hs : ∀ᶠ ε : ℝ × ℝ in 𝓝[≥] 0, x₀ + ε.1 • v + ε.2 • w ∈ s)
    (hfv : ∀ x ∈ s, HasLineDerivAt ℝ f (fv x) x v)
    (hfvw : ∀ x ∈ s, HasLineDerivAt ℝ fv (fvw x) x w)
    (hfvwc : ContinuousWithinAt fvw s x₀)
    (hfw : ∀ x ∈ s, HasLineDerivAt ℝ f (fw x) x w)
    (hfwv : ∀ x ∈ s, HasLineDerivAt ℝ fw (fwv x) x v)
    (hfwvc : ContinuousWithinAt fwv s x₀) :
    fvw x₀ = fwv x₀ := by
  have H₁ := tendsto_alternate_sum_square_smul_of_hasLineDerivAt hs hfv hfvw hfvwc
  rw [Ici_prod_eq, nhdsWithin_prod_eq, prod_comm, eventually_map, ← nhdsWithin_prod_eq,
    Ici_prod_Ici] at hs
  have H₂ := tendsto_alternate_sum_square_smul_of_hasLineDerivAt
    (by simpa only [add_right_comm] using hs) hfw hfwv hfwvc
  rw [nhdsWithin_prod_eq, prod_comm, tendsto_map'_iff, ← nhdsWithin_prod_eq] at H₂
  simp only [Prod.zero_eq_mk, nhdsWithin_prod_eq] at H₁ H₂
  refine tendsto_nhds_unique (H₁.congr fun _ ↦ ?_) H₂
  simp [mul_comm, add_right_comm, sub_right_comm]
