/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Smoothness reflects along a linear isometry with closed range

Let `Φ : E →ₗᵢ[𝕜] F` be a linear isometry with closed range (automatic when `E` is complete).
For `n : ℕ∞`, a map `f : G → E` is `C^n` as soon as `Φ ∘ f` is: `LinearIsometry.comp_contDiff_iff`.
This extends `ContinuousLinearEquiv.comp_contDiff_iff` from isomorphisms to isometric embeddings
onto closed subspaces, over any nontrivially normed field.

The derivative of `Φ ∘ f` at a point is a limit of difference quotients, all of which lie in
`range Φ`; since the range is closed, the derivative factors through `Φ`, and the factor is the
derivative of `f` because `Φ` is an isometry. Iterating, the argument recurses into the
postcomposition map `Φ.postcomp` on spaces of operators, whose range is again closed.

The analytic case `n = ω` is excluded: the induction on the order never reaches it, and the
statement is not expected to hold there in positive characteristic.

Closedness of the range cannot be dropped. For the inclusion of the finitely supported sequences
into `ℓ¹` and a bump function `χ`, the map `t ↦ ∑ₙ e^{-n} t χ(n t) eₙ` takes finitely supported
values, is `C^∞` into `ℓ¹`, but is not differentiable at `0` as a map into finitely supported
sequences: its derivative `∑ₙ e^{-n} eₙ` is not finitely supported.
-/

public section

open Set Function Filter
open scoped ContDiff

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace LinearIsometry

variable (Φ : E →ₗᵢ[𝕜] F)

/-- A continuous linear map with values in the range of a linear isometry factors through it. -/
theorem exists_comp_eq_of_forall_mem_range {L : G →L[𝕜] F} (hL : ∀ v, L v ∈ range Φ) :
    ∃ M : G →L[𝕜] E, Φ.toContinuousLinearMap.comp M = L :=
  ⟨Φ.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (L.codRestrict _ fun v ↦ LinearMap.mem_range.2 (hL v)),
    ContinuousLinearMap.ext fun _ ↦ congrArg Subtype.val (Φ.equivRange.apply_symm_apply _)⟩

/-- Postcomposition with a linear isometry with closed range has closed range. -/
theorem isClosed_range_postcomp (hΦ : IsClosed (range Φ)) :
    IsClosed (range (Φ.postcomp : (G →L[𝕜] E) →ₗᵢ[𝕜] (G →L[𝕜] F))) := by
  have : range (Φ.postcomp : (G →L[𝕜] E) →ₗᵢ[𝕜] (G →L[𝕜] F)) =
      ⋂ v, (fun L : G →L[𝕜] F ↦ L v) ⁻¹' range Φ := by
    ext L
    simp only [mem_range, mem_iInter, mem_preimage]
    exact ⟨fun ⟨M, hM⟩ v ↦ ⟨M v, by simp [← hM]⟩, Φ.exists_comp_eq_of_forall_mem_range⟩
  exact this ▸ isClosed_iInter fun v ↦ hΦ.preimage (continuous_id.clm_apply continuous_const)

/-- Postcomposition with a linear isometry preserves and reflects Fréchet derivatives. -/
theorem comp_hasFDerivAt_iff {f : G → E} {f' : G →L[𝕜] E} {x : G} :
    HasFDerivAt (Φ ∘ f) (Φ.toContinuousLinearMap.comp f') x ↔ HasFDerivAt f f' x := by
  simp [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff, ← map_sub]

/-- If `Φ` has closed range, every Fréchet derivative of `Φ ∘ f` factors through `Φ`, and the
factor is a Fréchet derivative of `f`. -/
theorem exists_hasFDerivAt_of_comp (hΦ : IsClosed (range Φ)) {f : G → E} {L : G →L[𝕜] F}
    {x : G} (h : HasFDerivAt (Φ ∘ f) L x) :
    ∃ M : G →L[𝕜] E, HasFDerivAt f M x ∧ Φ.toContinuousLinearMap.comp M = L := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
  have hcn : Tendsto (fun n : ℕ ↦ ‖c ^ n‖) atTop atTop := by
    simpa [norm_pow] using tendsto_pow_atTop_atTop_of_one_lt hc
  obtain ⟨M, rfl⟩ := Φ.exists_comp_eq_of_forall_mem_range fun v ↦ hΦ.mem_of_tendsto (h.lim v hcn)
    (.of_forall fun n ↦ ⟨c ^ n • (f (x + (c ^ n)⁻¹ • v) - f x), by simp⟩)
  exact ⟨M, Φ.comp_hasFDerivAt_iff.1 h, rfl⟩

/-- The single-universe version of `LinearIsometry.comp_contDiff_iff` for finite orders, proved by
induction. The induction step passes from `Φ` to `Φ.postcomp`, so all three spaces have to live
in the same universe. -/
private theorem contDiff_of_comp_natCast.{u} (k : ℕ) :
    ∀ {E F G : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
      [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] (Φ : E →ₗᵢ[𝕜] F),
      IsClosed (range Φ) → ∀ {f : G → E}, ContDiff 𝕜 k (Φ ∘ f) → ContDiff 𝕜 k f := by
  induction k with
  | zero =>
    intro E F G _ _ _ _ _ _ Φ _ f h
    rw [Nat.cast_zero, contDiff_zero] at h ⊢
    exact Φ.isometry.isEmbedding.continuous_iff.2 h
  | succ k ih =>
    intro E F G _ _ _ _ _ _ Φ hΦ f h
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv] at h ⊢
    obtain ⟨hd, -, hfderiv⟩ := h
    have hf : Differentiable 𝕜 f := fun x ↦
      (Φ.exists_hasFDerivAt_of_comp hΦ (hd x).hasFDerivAt).choose_spec.1.differentiableAt
    have hchain : fderiv 𝕜 (Φ ∘ f) = Φ.postcomp ∘ fderiv 𝕜 f := funext fun x ↦
      (Φ.toContinuousLinearMap.hasFDerivAt.comp x (hf x).hasFDerivAt).fderiv
    rw [hchain] at hfderiv
    exact ⟨hf, fun h ↦ absurd h (by simp), ih _ (Φ.isClosed_range_postcomp hΦ) hfderiv⟩

/-- Postcomposition with a linear isometry with closed range preserves and reflects
`C^n`-smoothness for `n : ℕ∞`. The analytic case is excluded, see the module docstring. -/
theorem comp_contDiff_iff.{uE, uF, uG} {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (Φ : E →ₗᵢ[𝕜] F) (hΦ : IsClosed (range Φ)) {n : ℕ∞} {f : G → E} :
    ContDiff 𝕜 n (Φ ∘ f) ↔ ContDiff 𝕜 n f := by
  refine ⟨fun h ↦ ?_, fun h ↦ Φ.toContinuousLinearMap.contDiff.comp h⟩
  rw [contDiff_iff_forall_nat_le] at h ⊢
  intro k hk
  -- Lift everything to a common universe, where the inductive argument applies.
  let eE : ULift.{max uF uG, uE} E ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.ulift 𝕜 E
  let eF : ULift.{max uE uG, uF} F ≃ₗᵢ[𝕜] F := LinearIsometryEquiv.ulift 𝕜 F
  let eG : ULift.{max uE uF, uG} G ≃ₗᵢ[𝕜] G := LinearIsometryEquiv.ulift 𝕜 G
  have hΨ : IsClosed (range (eF.symm.toLinearIsometry.comp (Φ.comp eE.toLinearIsometry))) := by
    rw [coe_comp, coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.coe_toLinearIsometry, range_comp, eE.surjective.range_comp]
    exact eF.symm.toHomeomorph.isClosed_image.2 hΦ
  have := contDiff_of_comp_natCast k _ hΨ (f := eE.symm ∘ f ∘ eG) <| by
    simpa [comp_def] using
      (eF.symm.toContinuousLinearEquiv.comp_contDiff_iff.2 (h k hk)).comp
        eG.toContinuousLinearEquiv.contDiff
  simpa [comp_def] using (eE.toContinuousLinearEquiv.comp_contDiff_iff.2 this).comp
    eG.symm.toContinuousLinearEquiv.contDiff

/-- Postcomposition with a linear isometry from a complete space preserves and reflects
`C^n`-smoothness for `n : ℕ∞`. -/
theorem comp_contDiff_iff_of_completeSpace [CompleteSpace E] {n : ℕ∞} {f : G → E} :
    ContDiff 𝕜 n (Φ ∘ f) ↔ ContDiff 𝕜 n f :=
  Φ.comp_contDiff_iff Φ.isometry.isClosedEmbedding.isClosed_range

end LinearIsometry
