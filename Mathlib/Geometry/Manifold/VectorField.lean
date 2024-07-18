import Mathlib.Geometry.Manifold.PoincareConjecture

/- Glouglou -/

noncomputable section

section LieBracketVectorField

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

lemma lieBracket_eq (V W : E → E) :
    lieBracket 𝕜 V W = fun x ↦ fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x) := rfl

def lieDeriv (V : E → E) (f : E → F) (x : E) : F := fderiv 𝕜 f x (V x)

lemma lieDeriv_eq (V : E → E) (f : E → F) : lieDeriv 𝕜 V f = fun x ↦ fderiv 𝕜 f x (V x) := rfl

lemma sub_eq_lieDeriv_lieBracket (V W : E → E) (f : E → F) (x : E)
    (hf : ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v)
    (h'f : ContDiffAt 𝕜 2 f x) (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieDeriv 𝕜 V (lieDeriv 𝕜 W f) x - lieDeriv 𝕜 W (lieDeriv 𝕜 V f) x =
      lieDeriv 𝕜 (lieBracket 𝕜 V W) f x := by
  have A : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    (h'f.fderiv_right (m := 1) le_rfl).differentiableAt le_rfl
  simp only [lieDeriv_eq, lieBracket_eq]
  rw [fderiv_clm_apply A hV, fderiv_clm_apply A hW]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, map_sub, hf]
  abel

open Classical in
def pullback (f : E → F) (V : F → F) (x : E) : E :=
  if h : ∃ M : E ≃L[𝕜] F, fderiv 𝕜 f x = M then (choose h).symm (V (f x)) else 0

variable {𝕜}

lemma pullback_eq_of_fderiv_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : fderiv 𝕜 f x = M) (V : F → F) :
    pullback 𝕜 f V x = M.symm (V (f x)) := by
  have h : ∃ M : E ≃L[𝕜] F, fderiv 𝕜 f x = M := ⟨M, hf⟩
  rw [pullback, dif_pos h]
  congr
  ext y
  change ((Classical.choose h :) : E →L[𝕜] F) y = M y
  rw [← Classical.choose_spec h, hf]
  rfl


lemma pullback_eq_of_not_exists {f : E → F} {x : E}
    (h : ¬(∃ M : E ≃L[𝕜] F, fderiv 𝕜 f x = M)) (V : F → F) :
    pullback 𝕜 f V x = 0 := by
  rw [pullback, dif_neg h]

open scoped Topology Filter

theorem fderiv.comp'
    {f : E → F} {g : F → G} (x : E) (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y ↦ g (f y)) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  fderiv.comp x hg hf

open Set

open Classical in
protected def ContinuousLinearMap.inv (f : E →L[𝕜] F) : F →L[𝕜] E :=
  if h : ∃ M : E ≃L[𝕜] F, f = M then h.choose.symm else 0

variable [CompleteSpace E]

#check contDiffAt_ring_inverse

theorem contDiffAt_continuousLinearMap_inv (n : ℕ∞) (M : E ≃L[𝕜] F) :
    ContDiffAt 𝕜 n (ContinuousLinearMap.inv : (E →L[𝕜] F) → (F →L[𝕜] E)) (M : E →L[𝕜] F) := by
  have : ∀ (f : E →L[𝕜] F), f.inv = (Ring.inverse (M.symm ∘L f)) ∘L M.symm := by
    sorry



#exit

lemma foo (f : E → F) (x : E) (h'f : ContDiffAt 𝕜 2 f x) (hf : ∃ M : E ≃L[𝕜] F, fderiv 𝕜 f x = M) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) x
    ∧ ContDiffAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x
    ∧ (∀ᶠ y in 𝓝 x, fderiv 𝕜 f y = N y)
    ∧ ∀ v, fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x v
      = - (N x).symm  ∘L ((fderiv 𝕜 (fderiv 𝕜 f) x v)) ∘L (N x).symm := by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | ∃ (N : E ≃L[𝕜] F), N = fderiv 𝕜 f y}
  have : U ∈ 𝓝 x := by
    have I : range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (fderiv 𝕜 f x) := by
      rw [hM]
      exact M.nhds
    have : ContinuousAt (fderiv 𝕜 f) x := (h'f.fderiv_right (m := 1) le_rfl).continuousAt
    exact this I
  let N : E → (E ≃L[𝕜] F) := fun x ↦ if h : x ∈ U then h.choose else M
  refine ⟨N, ?_, ?_, ?_, ?_⟩


#exit

lemma glouk (f : E → F) (V W : F → F) (x : E)
    (hf : ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v)
    (h'f : ContDiffAt 𝕜 2 f x) (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x = pullback 𝕜 f (lieBracket 𝕜 V W) x := by
  by_cases h : ∃ M : E ≃L[𝕜] F, fderiv 𝕜 f x = M; swap
  · simp [pullback_eq_of_not_exists h, lieBracket_eq]
  rcases foo f x h'f h with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : fderiv 𝕜 f x = M x := (mem_of_mem_nhds hM :)
  have AV : fderiv 𝕜 (pullback 𝕜 f V) x =
      fderiv 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hM] with y hy using pullback_eq_of_fderiv_eq hy _
  have AW : fderiv 𝕜 (pullback 𝕜 f W) x =
      fderiv 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (W (f y))) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hM] with y hy using pullback_eq_of_fderiv_eq hy _
  have Af : DifferentiableAt 𝕜 f x := h'f.differentiableAt one_le_two
  simp only [lieBracket_eq, pullback_eq_of_fderiv_eq hMx, map_sub, AV, AW]
  rw [fderiv_clm_apply, fderiv_clm_apply]
  · simp [fderiv.comp' x hW Af, hMx,
      fderiv.comp' x hV Af, M_diff, hf]
  · exact M_symm_smooth.differentiableAt le_rfl
  · exact hV.comp x Af
  · exact M_symm_smooth.differentiableAt le_rfl
  · exact hW.comp x Af

lemma glouk2 (f : E → F) (V : F → F) (g : F → G) (x : E) :
    lieDeriv 𝕜 (pullback 𝕜 f V) (g ∘ f) x = lieDeriv 𝕜 V g (f x) := by






#exit














end LieBracketVectorField
