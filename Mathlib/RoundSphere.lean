import Mathlib

noncomputable section

open Metric Module Function Manifold

open scoped ContDiff RealInnerProductSpace

/-!
### An auxiliary chart on `E` adapted to the stereographic charts of the unit sphere

For a unit vector `v : E`, `Sphere.polarChart` is an analytic chart on `E`, defined on the
half-space `{z | 0 < ⟪v, z⟫ + 1}` with image the complement of the closed ray `ℝ≥0 ∙ v`.
It sends `z = w + t • v` (with `w ⊥ v`) to `(1 + t) • stereoInvFunAux v w`, so it maps the
hyperplane `(ℝ ∙ v)ᗮ` onto the sphere minus `v` by the inverse of stereographic projection.
Hence in the charts `stereographic' n (-x)` on the sphere and `(polarChart _).symm` on `E`,
the inclusion of the sphere into `E` becomes the linear inclusion `u ↦ (u, 0)`.
-/

section PolarChart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace Sphere

variable (v : E)

/-- The radial extension of the inverse of stereographic projection: it maps the hyperplane
`(ℝ ∙ v)ᗮ` to the sphere minus `v`, and the `v`-coordinate to the radius (shifted by one). -/
def polarMap (z : E) : E := (1 + ⟪v, z⟫) • stereoInvFunAux v (z - ⟪v, z⟫ • v)

/-- The inverse of `polarMap`. -/
def polarInv (y : E) : E := ((stereoToFun v (‖y‖⁻¹ • y) : (ℝ ∙ v)ᗮ) : E) + (‖y‖ - 1) • v

/-- The source of the polar chart. -/
def polarSource : Set E := {z : E | 0 < 1 + ⟪v, z⟫}

/-- The target of the polar chart: the complement of the closed ray spanned by `v`. -/
def polarTarget : Set E := {y : E | ⟪v, y⟫ < ‖y‖}

variable {v}

lemma sub_inner_smul_mem (hv : ‖v‖ = 1) (z : E) : z - ⟪v, z⟫ • v ∈ (ℝ ∙ v)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [inner_sub_right, inner_smul_right, hv]

lemma isOpen_polarSource : IsOpen (polarSource v) := by
  have : Continuous fun z : E => 1 + ⟪v, z⟫ := by fun_prop
  exact isOpen_lt continuous_const this

lemma isOpen_polarTarget : IsOpen (polarTarget v) := by
  have h1 : Continuous fun y : E => ⟪v, y⟫ := by fun_prop
  exact isOpen_lt h1 continuous_norm

lemma ne_zero_of_mem_polarTarget {y : E} (hy : y ∈ polarTarget v) : y ≠ 0 := by
  rintro rfl
  simp [polarTarget] at hy

lemma norm_normalize {y : E} (hy : y ∈ polarTarget v) : ‖‖y‖⁻¹ • y‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀]
  simpa using ne_zero_of_mem_polarTarget hy

lemma normalize_ne (hv : ‖v‖ = 1) {y : E} (hy : y ∈ polarTarget v) : ‖y‖⁻¹ • y ≠ v := by
  intro h
  have hy0 : ‖y‖ ≠ 0 := by simpa using ne_zero_of_mem_polarTarget hy
  have hyv : y = ‖y‖ • v := by rw [← h, smul_inv_smul₀ hy0]
  have h1 : ⟪v, y⟫ < ‖y‖ := hy
  have h2 : ⟪v, y⟫ = ‖y‖ := by
    conv_lhs => rw [hyv]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  exact h1.ne h2

lemma inner_polarInv (hv : ‖v‖ = 1) (y : E) : ⟪v, polarInv v y⟫ = ‖y‖ - 1 := by
  have h0 : ⟪v, ((stereoToFun v (‖y‖⁻¹ • y) : (ℝ ∙ v)ᗮ) : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp (stereoToFun v (‖y‖⁻¹ • y)).2
  rw [polarInv, inner_add_right, h0, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
  ring

lemma polarInv_sub (hv : ‖v‖ = 1) (y : E) :
    polarInv v y - ⟪v, polarInv v y⟫ • v = ((stereoToFun v (‖y‖⁻¹ • y) : (ℝ ∙ v)ᗮ) : E) := by
  rw [inner_polarInv hv]
  simp [polarInv]

lemma polarMap_polarInv (hv : ‖v‖ = 1) {y : E} (hy : y ∈ polarTarget v) :
    polarMap v (polarInv v y) = y := by
  have hy0 : ‖y‖ ≠ 0 := by simpa using ne_zero_of_mem_polarTarget hy
  have key : stereoInvFunAux v ((stereoToFun v (‖y‖⁻¹ • y) : (ℝ ∙ v)ᗮ) : E) = ‖y‖⁻¹ • y := by
    have := stereo_left_inv hv (x := ⟨‖y‖⁻¹ • y, by simpa using norm_normalize hy⟩)
      (by simpa using normalize_ne hv hy)
    exact congrArg Subtype.val this
  rw [polarMap, polarInv_sub hv, inner_polarInv hv, key]
  rw [show (1 : ℝ) + (‖y‖ - 1) = ‖y‖ by ring, smul_inv_smul₀ hy0]

lemma polarInv_polarMap (hv : ‖v‖ = 1) {z : E} (hz : z ∈ polarSource v) :
    polarInv v (polarMap v z) = z := by
  set r : ℝ := 1 + ⟪v, z⟫ with hr
  have hrpos : 0 < r := hz
  set w : E := z - ⟪v, z⟫ • v with hw
  have hwmem : w ∈ (ℝ ∙ v)ᗮ := sub_inner_smul_mem hv z
  set p : E := stereoInvFunAux v w with hp
  have hpnorm : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv hwmem)
  have hnorm : ‖polarMap v z‖ = r := by
    rw [polarMap, ← hr, ← hw, ← hp, norm_smul, hpnorm, Real.norm_eq_abs,
      abs_of_pos hrpos, mul_one]
  have hunit : ‖polarMap v z‖⁻¹ • polarMap v z = p := by
    rw [hnorm, polarMap, ← hr, ← hw, ← hp, inv_smul_smul₀ hrpos.ne']
  have hstereo : ((stereoToFun v p : (ℝ ∙ v)ᗮ) : E) = w := by
    have := stereo_right_inv hv (⟨w, hwmem⟩ : (ℝ ∙ v)ᗮ)
    have h2 : ((stereoInvFun hv (⟨w, hwmem⟩ : (ℝ ∙ v)ᗮ) : sphere (0 : E) 1) : E) = p := rfl
    rw [← h2, this]
  rw [polarInv, hunit, hstereo, hnorm, hw]
  module

lemma polarInv_stereoInvFunAux (hv : ‖v‖ = 1) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) :
    polarInv v (stereoInvFunAux v w) = w := by
  have h0 : ⟪v, w⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  have hs : w ∈ polarSource v := by
    show (0 : ℝ) < 1 + ⟪v, w⟫
    rw [h0]; norm_num
  have hm : polarMap v w = stereoInvFunAux v w := by rw [polarMap, h0]; simp
  rw [← hm, polarInv_polarMap hv hs]

lemma polarMap_mem (hv : ‖v‖ = 1) {z : E} (hz : z ∈ polarSource v) :
    polarMap v z ∈ polarTarget v := by
  set r : ℝ := 1 + ⟪v, z⟫ with hr
  have hrpos : 0 < r := hz
  have hwmem : z - ⟪v, z⟫ • v ∈ (ℝ ∙ v)ᗮ := sub_inner_smul_mem hv z
  set p : E := stereoInvFunAux v (z - ⟪v, z⟫ • v) with hp
  have hpnorm : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv hwmem)
  have hpne : p ≠ v := by
    have := stereoInvFun_ne_north_pole hv (⟨z - ⟪v, z⟫ • v, hwmem⟩ : (ℝ ∙ v)ᗮ)
    simpa [hp, Subtype.ext_iff, stereoInvFun] using this
  have hlt : ⟪v, p⟫ < 1 := (inner_lt_one_iff_real_of_norm_eq_one hv hpnorm).2 (Ne.symm hpne)
  show ⟪v, polarMap v z⟫ < ‖polarMap v z‖
  rw [polarMap, ← hr, ← hp, inner_smul_right, norm_smul, hpnorm, Real.norm_eq_abs,
    abs_of_pos hrpos, mul_one]
  nlinarith

lemma polarInv_mem (hv : ‖v‖ = 1) {y : E} (hy : y ∈ polarTarget v) :
    polarInv v y ∈ polarSource v := by
  show 0 < 1 + ⟪v, polarInv v y⟫
  rw [inner_polarInv hv]
  have : y ≠ 0 := ne_zero_of_mem_polarTarget hy
  have : 0 < ‖y‖ := norm_pos_iff.2 this
  linarith

lemma contDiff_polarMap {m : ℕ∞ω} : ContDiff ℝ m (polarMap v) := by
  have h1 : ContDiff ℝ m fun z : E => ⟪v, z⟫ := (innerSL ℝ v).contDiff
  exact (contDiff_const.add h1).smul
    (contDiff_stereoInvFunAux.comp (contDiff_id.sub (h1.smul contDiff_const)))

lemma isOpen_stereoToFun_domain : IsOpen {x : E | innerSL ℝ v x ≠ (1 : ℝ)} :=
  isOpen_ne_fun (by fun_prop) continuous_const

lemma contDiffOn_polarInv {m : ℕ∞ω} :
    ContDiffOn ℝ m (polarInv v) (polarTarget v) := by
  intro y hy
  have hy0 : y ≠ 0 := ne_zero_of_mem_polarTarget hy
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy0
  have hynpos : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hnorm : ContDiffAt ℝ m (fun z : E => ‖z‖) y := contDiffAt_norm ℝ hy0
  have hu : ContDiffAt ℝ m (fun z : E => ‖z‖⁻¹ • z) y := (hnorm.inv hyn).smul contDiffAt_id
  have hmem : (‖y‖⁻¹ • y) ∈ {x : E | innerSL ℝ v x ≠ (1 : ℝ)} := by
    have hlt : ⟪v, y⟫ < ‖y‖ := hy
    have : ⟪v, ‖y‖⁻¹ • y⟫ < 1 := by
      rw [real_inner_smul_right]
      rw [inv_mul_lt_one₀ hynpos]
      exact hlt
    exact this.ne
  have hst : ContDiffAt ℝ m (fun z : E => ((stereoToFun v z : (ℝ ∙ v)ᗮ) : E)) (‖y‖⁻¹ • y) :=
    ((ℝ ∙ v)ᗮ.subtypeL.contDiff.comp_contDiffOn
      (contDiffOn_stereoToFun (v := v) (n := m))).contDiffAt
        (isOpen_stereoToFun_domain.mem_nhds hmem)
  have hcomp : ContDiffAt ℝ m (fun z : E => ((stereoToFun v (‖z‖⁻¹ • z) : (ℝ ∙ v)ᗮ) : E)) y :=
    ContDiffAt.comp (f := fun z : E => ‖z‖⁻¹ • z) y hst hu
  exact (hcomp.add ((hnorm.sub contDiffAt_const).smul contDiffAt_const)).contDiffWithinAt

/-- The polar chart on `E` around a unit vector `v`: it maps a neighbourhood of the hyperplane
`(ℝ ∙ v)ᗮ` onto the complement of the closed ray `ℝ≥0 ∙ v`, taking `(ℝ ∙ v)ᗮ` onto the sphere
minus `v` via the inverse of stereographic projection. -/
def polarChart (hv : ‖v‖ = 1) : OpenPartialHomeomorph E E where
  toFun := polarMap v
  invFun := polarInv v
  source := polarSource v
  target := polarTarget v
  map_source' _ hz := polarMap_mem hv hz
  map_target' _ hy := polarInv_mem hv hy
  left_inv' _ hz := polarInv_polarMap hv hz
  right_inv' _ hy := polarMap_polarInv hv hy
  open_source := isOpen_polarSource
  open_target := isOpen_polarTarget
  continuousOn_toFun := (contDiff_polarMap (m := 0)).continuous.continuousOn
  continuousOn_invFun := (contDiffOn_polarInv (m := 0)).continuousOn

section Equiv

variable (n : ℕ)

/-- The continuous linear equivalence `EuclideanSpace ℝ (Fin n) × ℝ ≃L[ℝ] E` splitting `E`
as `(ℝ ∙ v)ᗮ ⊕ ℝ ∙ v`. -/
def polarLinearEquiv [Fact (finrank ℝ E = n + 1)] (hv : ‖v‖ = 1)
    (U : (ℝ ∙ v)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] E :=
  have : FiniteDimensional ℝ E := FiniteDimensional.of_fact_finrank_eq_succ n
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p => ((U.symm p.1 : (ℝ ∙ v)ᗮ) : E) + p.2 • v
      map_add' := by intro p q; simp [add_smul]; module
      map_smul' := by intro r p; simp [mul_smul]
      invFun := fun z => (U ⟨z - ⟪v, z⟫ • v, sub_inner_smul_mem hv z⟩, ⟪v, z⟫)
      left_inv := by
        rintro ⟨u, t⟩
        have h0 : ⟪v, ((U.symm u : (ℝ ∙ v)ᗮ) : E)⟫ = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp (U.symm u).2
        have hi : ⟪v, ((U.symm u : (ℝ ∙ v)ᗮ) : E) + t • v⟫ = t := by
          rw [inner_add_right, h0, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
          ring
        ext <;> simp [hi]
      right_inv := by
        intro z
        simp }

@[simp]
lemma polarLinearEquiv_apply_zero [Fact (finrank ℝ E = n + 1)] (hv : ‖v‖ = 1)
    (U : (ℝ ∙ v)ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (u : EuclideanSpace ℝ (Fin n)) :
    polarLinearEquiv n hv U (u, 0) = ((U.symm u : (ℝ ∙ v)ᗮ) : E) := by
  simp [polarLinearEquiv]

end Equiv

end Sphere

open Sphere

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

theorem isImmersionOfComplement_coe_sphere :
    IsImmersionOfComplement ℝ (𝓡 n) 𝓘(ℝ, E) ω ((↑) : sphere (0 : E) 1 → E) := by
  intro x
  have hv : ‖((-x : sphere (0 : E) 1) : E)‖ = 1 := norm_eq_of_mem_sphere (-x)
  set U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere (-x))).repr with hU
  refine IsImmersionAtOfComplement.mk_of_continuousAt (I := 𝓡 n) (J := 𝓘(ℝ, E))
    (M := sphere (0 : E) 1) (N := E) ?_ (polarLinearEquiv n hv U)
    (stereographic' n (-x)) (polarChart hv).symm ?_ ?_ ?_ ?_ ?_
  · exact continuous_subtype_val.continuousAt
  · exact mem_chart_source _ x
  · show ⟪((-x : sphere (0 : E) 1) : E), (x : E)⟫ < ‖(x : E)‖
    have hx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
    simp [inner_neg_left, hx]
  · exact IsManifold.chart_mem_maximalAtlas x
  · exact OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
      contDiffOn_polarInv.contMDiffOn contDiff_polarMap.contDiffOn.contMDiffOn
  · intro u hu
    simp only [Function.comp_apply, mfld_simps, polarLinearEquiv_apply_zero]
    exact polarInv_stereoInvFunAux hv (U.symm u).2

end PolarChart

section thing_two

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def RoundSphere (n : ℕ) [Fact (finrank ℝ E = n + 1)] : Type _ := sphere (0 : E) 1
  deriving TopologicalSpace, ChartedSpace (EuclideanSpace ℝ (Fin n)),
  IsManifold (𝓡 n) ω

variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

example (x : E) (hx : dist x 0 = 1) : RoundSphere E n := ⟨x, hx⟩

namespace RoundSphere

instance : Neg (RoundSphere E n) where
  neg x := ⟨-x.1, by
    obtain ⟨v, hv⟩ := x
    simpa using hv⟩

instance : IsManifold (𝓡 n) ω (RoundSphere E n) :=
  inferInstanceAs (IsManifold (𝓡 n) ω (sphere (0 : E) 1))

instance : RegularSpace (RoundSphere E n) :=
  inferInstanceAs (RegularSpace (sphere (0 : E) 1))

def inclusion : RoundSphere E n → E := fun x ↦ x.1

theorem inclusion_isImmersion : IsImmersion (𝓡 n) 𝓘(ℝ, E) ω (inclusion E n) :=
  isImmersionOfComplement_coe_sphere.isImmersion

end RoundSphere

end thing_two

section thing_three

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open Bundle

example : IsRiemannianManifold 𝓘(ℝ, E) E := inferInstance

end thing_three

section thing_four

open Bundle Bornology

namespace Bundle

/-- Pull back a continuous bilinear form along a continuous linear map.

`T` must *not* be assumed normed here: a tangent space carries only a topological vector space
structure (no `NormedAddCommGroup`/`NormedSpace` instance) unless a Riemannian structure is
already present. -/
def ContinuousBilinearForm.comap {T V : Type*}
    [AddCommGroup T] [Module ℝ T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul ℝ T]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul ℝ V]
    (b : V →L[ℝ] V →L[ℝ] ℝ) (e : T →L[ℝ] V) : T →L[ℝ] T →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ e).comp (b.comp e)

@[simp] lemma ContinuousBilinearForm.comap_apply {T V : Type*}
    [AddCommGroup T] [Module ℝ T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [ContinuousConstSMul ℝ T]
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul ℝ V]
    (b : V →L[ℝ] V →L[ℝ] ℝ) (e : T →L[ℝ] V) (x y : T) :
    ContinuousBilinearForm.comap b e x y = b (e x) (e y) := rfl

end Bundle

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {f : M → N}
  {n : ℕ∞ω}

/-- Continuity of the pullback of a bilinear form, in the normed setting where it is used to
express the pullback metric in local coordinates. -/
lemma ContinuousAt.bilinComap {X : Type*} [TopologicalSpace X] {x₀ : X}
    {b : X → (E'' →L[ℝ] E'' →L[ℝ] ℝ)} {e : X → (E →L[ℝ] E'')}
    (hb : ContinuousAt b x₀) (he : ContinuousAt e x₀) :
    ContinuousAt (fun x ↦ Bundle.ContinuousBilinearForm.comap (b x) (e x)) x₀ := by
  have key : (fun x ↦ Bundle.ContinuousBilinearForm.comap (b x) (e x))
      = fun x ↦ ((ContinuousLinearMap.compL ℝ E E'' ℝ).flip (e x)).comp ((b x).comp (e x)) := by
    ext x v w
    rfl
  rw [key]
  exact ContinuousAt.clm_comp
    (((ContinuousLinearMap.compL ℝ E E'' ℝ).flip).continuous.continuousAt.comp he)
    (hb.clm_comp he)

namespace Bundle

/-- Pull back a continuous Riemannian metric along an immersion. -/
def ContinuousRiemannianMetric.comap (hf : IsImmersion I J n f) (hn : n ≠ 0)
    (g : ContinuousRiemannianMetric E'' (fun (y : N) ↦ TangentSpace J y)) :
    ContinuousRiemannianMetric E (fun (x : M) ↦ TangentSpace I x) where
  inner x := ContinuousBilinearForm.comap (g.inner (f x)) (mfderiv% f x)
  symm x v w := g.symm (f x) _ _
  pos x v hv := g.pos (f x) _ fun h ↦
    hv (hf.injective_mfderiv hn x (h.trans (map_zero _).symm))
  isVonNBounded x := by
    obtain ⟨L, hL⟩ := hf.isDiffImmersionAt hn x
    refine IsVonNBounded.subset ?_ ((g.isVonNBounded (f x)).image L)
    rintro v hv
    exact ⟨(mfderiv% f x) v, hv, hL v⟩
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x₀
    rw [continuousAt_hom_bundle]
    refine ⟨continuousAt_id, ?_⟩
    -- the derivative of `f`, read in tangent coordinates around `x₀` and `f x₀`
    set a : M → (E →L[ℝ] E'') :=
      inTangentCoordinates I J id f (fun x ↦ mfderiv% f x) x₀ with ha
    -- the metric on `N`, read in coordinates around `f x₀`
    set Γ : M → (E'' →L[ℝ] E'' →L[ℝ] ℝ) := fun x ↦
      ContinuousLinearMap.inCoordinates E'' (TangentSpace J) (E'' →L[ℝ] ℝ)
        (fun y ↦ TangentSpace J y →L[ℝ] ℝ) (f x₀) (f x) (f x₀) (f x) (g.inner (f x)) with hΓ
    have hfc : ContinuousAt f x₀ := (hf.isImmersionAt x₀).continuousAt
    have hΓc : ContinuousAt Γ x₀ := by
      have h : ContinuousAt (fun x ↦ TotalSpace.mk' (E'' →L[ℝ] E'' →L[ℝ] ℝ)
          (E := fun y : N ↦ (TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ))
          (f x) (g.inner (f x))) x₀ :=
        g.continuous.continuousAt.comp hfc
      rw [continuousAt_hom_bundle] at h
      exact h.2
    have h1n : (0 : ℕ∞ω) + 1 ≤ n := by
      simpa using ENat.one_le_iff_ne_zero_withTop.mpr hn
    have hac : ContinuousAt a x₀ :=
      (ContMDiffAt.mfderiv_const (I := I) (I' := J) (m := 0) hf.contMDiff.contMDiffAt
        h1n).continuousAt
    have key : (fun x ↦ ContinuousBilinearForm.comap (Γ x) (a x)) =ᶠ[nhds x₀]
        fun x ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] ℝ) x₀ x x₀ x
          (ContinuousBilinearForm.comap (g.inner (f x)) (mfderiv% f x)) := by
      have hA : ∀ᶠ x in nhds x₀, x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
        (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' x₀)
      have hB : ∀ᶠ x in nhds x₀, f x ∈ (trivializationAt E'' (TangentSpace J) (f x₀)).baseSet :=
        hfc ((trivializationAt E'' (TangentSpace J) (f x₀)).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (f x₀)))
      filter_upwards [hA, hB] with x hx1 hx2
      -- the derivative, read in coordinates, is the derivative conjugated by the trivialisations
      have hstep : ∀ u : E, (trivializationAt E'' (TangentSpace J) (f x₀)).symm (f x) (a x u)
          = (mfderiv% f x) ((trivializationAt E (TangentSpace I) x₀).symm x u) := by
        intro u
        rw [ha]
        simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
          ContinuousLinearMap.comp_apply, id_eq]
        rw [← Trivialization.symmL_apply (R := ℝ) _ hx2,
          Trivialization.symmL_continuousLinearMapAt _ hx2,
          Trivialization.symmL_apply (R := ℝ) _ hx1]
      ext v w
      rw [inCoordinates_apply_eq₂ hx1 hx1 (by simp)]
      simp only [ContinuousBilinearForm.comap_apply, hΓ]
      rw [inCoordinates_apply_eq₂ hx2 hx2 (by simp), hstep, hstep]
      simp
    exact (hΓc.bilinComap hac).congr key

/-- The Riemannian bundle structure on `M` obtained by pulling back a continuous Riemannian
metric on `N` along an immersion `f : M → N`.

Because this is built from a `ContinuousRiemannianMetric`, it automatically registers an
`IsContinuousRiemannianBundle` instance as well. -/
@[instance_reducible]
def RiemannianBundle.comap (hf : IsImmersion I J n f) (hn : n ≠ 0)
    (g : ContinuousRiemannianMetric E'' (fun (y : N) ↦ TangentSpace J y)) :
    RiemannianBundle (fun (x : M) ↦ TangentSpace I x) :=
  ⟨(ContinuousRiemannianMetric.comap hf hn g).toRiemannianMetric⟩

end Bundle

/-- Pulling back a Riemannian metric along an immersion and equipping `M` with the associated
Riemannian distance makes `M` a Riemannian manifold.

Note that this is true by definition: `IsRiemannianManifold` asserts the compatibility of a
*pre-existing* extended distance with the metric, and here the distance is defined to be the
Riemannian one. The immersion hypothesis is used to build the metric, not the compatibility. -/
theorem IsRiemannianManifold.comap [RegularSpace M] (hf : IsImmersion I J n f) (hn : n ≠ 0)
    (g : ContinuousRiemannianMetric E'' (fun (y : N) ↦ TangentSpace J y)) :
    letI : RiemannianBundle (fun (x : M) ↦ TangentSpace I x) := RiemannianBundle.comap hf hn g
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M :=
  inferInstance

end

end thing_four

section thing_five

open Bundle

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]

/-- The round sphere, with the metric pulled back from the ambient inner product space. -/
noncomputable instance :
    RiemannianBundle (fun (x : RoundSphere E n) ↦ TangentSpace (𝓡 n) x) :=
  RiemannianBundle.comap (RoundSphere.inclusion_isImmersion E n) (by simp)
    (riemannianMetricVectorSpace E).toContinuousRiemannianMetric

/-- The associated Riemannian distance on the round sphere. -/
noncomputable instance : PseudoEMetricSpace (RoundSphere E n) :=
  PseudoEMetricSpace.ofRiemannianMetric (𝓡 n) (RoundSphere E n)

example : IsRiemannianManifold (𝓡 n) (RoundSphere E n) := inferInstance

end thing_five

end
