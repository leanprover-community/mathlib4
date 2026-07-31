/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.Sobolev

/-! # Bessel potential spaces

We define the Bessel potential space or Fourier-theoretic Sobolev space. Informally, this space is
given as the set of all tempered distributions `u` such that `𝓕⁻ (1 + ‖ξ‖ ^ 2) ^ (s / 2) 𝓕 u` is
an `Lp` function.

### Implementation notes

In `Mathlib.Analysis.Distribution.Sobolev` the unbundled version `TemperedDistribution.MemSobolev`
is defined as `∃ v : Lp, besselPotential E F s u = v`. While it would be possible to define
the bundled space in the same way, the eliminating the existence quantifier makes proving theorems
more involved and hence we bundle the `Lp` function `v` into the structure.

We also note that since every `Lp` function uniquely defines a distribution via
`u = besselPotential E F (-s) v`, it would be possible to define the Bessel potential space
as a one-field structure of `Lp`. The approach of having both `u` and `v` as part of the structure
gives better definitional equalities.
-/

public noncomputable section

variable {E F : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace F]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

variable (E F) in
/-- The Bessel potential space of order `s : ℝ` and `p : ℝ≥0∞`, also known as the Sobolev space and
usually denoted by `H^{s,p}`.

It is defined as the set of all tempered distributions `u` such that
`𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 u` can be represented by a `Lp` function `v`. Both `u` and `v` are
stored as data to avoid using `Classical.choose`. -/
structure BesselPotentialSpace [NormedSpace ℂ F] (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] where
  /-- The underlying tempered distribution -/
  toDistr : 𝓢'(E, F)
  /-- The underlying `Lp` function -/
  sobFn : Lp F p (volume : Measure E)
  /-- The Sobolev function is given by applying the Bessel potential operator to the distribution -/
  bessel_toDistr_eq_sobFn : besselPotential E F s toDistr = sobFn

attribute [coe] BesselPotentialSpace.toDistr

namespace BesselPotentialSpace

section NormedSpace

variable [NormedSpace ℂ F]

variable {s s' : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

instance : CoeHead (BesselPotentialSpace E F s p) 𝓢'(E, F) where
  coe f := f.toDistr

theorem ext' {f g : BesselPotentialSpace E F s p}
    (h₁ : f.toDistr = g.toDistr) (h₂ : f.sobFn = g.sobFn) : f = g := by
  cases f; cases g; congr

theorem memSobolev_toDistr (f : BesselPotentialSpace E F s p) : f.toDistr.MemSobolev s p  :=
  ⟨f.sobFn, f.bessel_toDistr_eq_sobFn⟩

@[simp]
theorem besselPotential_neg_sobFn_eq {f : BesselPotentialSpace E F s p} :
    besselPotential E F (-s) f.sobFn = f := by
  simp [← f.bessel_toDistr_eq_sobFn]

@[ext]
theorem ext {f g : BesselPotentialSpace E F s p} (h₁ : f.toDistr = g.toDistr) : f = g := by
  apply ext' h₁
  apply_fun MeasureTheory.Lp.toTemperedDistribution; swap
  · apply LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
  calc
    f.sobFn = besselPotential E F s f.toDistr := f.bessel_toDistr_eq_sobFn.symm
    _ = besselPotential E F s g.toDistr := by congr
    _ = g.sobFn := g.bessel_toDistr_eq_sobFn

/-- Transfer a Sobolev function in `H^{s,p}` to `H^{s', p}` given that `s = s'`. -/
def copy (hs : s = s') (f : BesselPotentialSpace E F s p) : BesselPotentialSpace E F s' p where
  toDistr := f.toDistr
  sobFn := f.sobFn
  bessel_toDistr_eq_sobFn := by
    rw [← hs]
    exact f.bessel_toDistr_eq_sobFn

@[simp]
theorem toDistr_copy (f : BesselPotentialSpace E F s p) (hs : s = s') :
  (f.copy hs).toDistr = f := by rfl

@[simp]
theorem sobFn_copy (f : BesselPotentialSpace E F s p) (hs : s = s') :
  (f.copy hs).sobFn = f.sobFn := by rfl

variable (E F s p) in
theorem injective_sobFn :
    Function.Injective (sobFn (s := s) (p := p) (E := E) (F := F)) := by
  intro f g hfg
  refine ext' ?_ hfg
  calc
    f.toDistr = besselPotential E F (-s) f.sobFn := by simp
    _ = besselPotential E F (-s) g.sobFn := by congr
    _ = g.toDistr := by simp

instance instZero : Zero (BesselPotentialSpace E F s p) where
  zero := {
    toDistr := 0
    sobFn := 0
    bessel_toDistr_eq_sobFn := by simp [← Lp.toTemperedDistributionCLM_apply] }

@[simp, norm_cast]
theorem toDistr_zero : (0 : BesselPotentialSpace E F s p).toDistr = 0 := rfl

@[simp]
theorem sobFn_zero : (0 : BesselPotentialSpace E F s p).sobFn = 0 := rfl

instance instAdd : Add (BesselPotentialSpace E F s p) where
  add f g := {
    toDistr := f + g
    sobFn := f.sobFn + g.sobFn
    bessel_toDistr_eq_sobFn := by simp [← Lp.toTemperedDistributionCLM_apply, map_add,
      f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp, norm_cast]
theorem toDistr_add (f g : BesselPotentialSpace E F s p) : (f + g).toDistr = f + g := rfl

@[simp]
theorem sobFn_add (f g : BesselPotentialSpace E F s p) : (f + g).sobFn = f.sobFn + g.sobFn := rfl

instance instSub : Sub (BesselPotentialSpace E F s p) where
  sub f g := {
    toDistr := f - g
    sobFn := f.sobFn - g.sobFn
    bessel_toDistr_eq_sobFn := by simp [← Lp.toTemperedDistributionCLM_apply, map_sub,
      f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp, norm_cast]
theorem toDistr_sub (f g : BesselPotentialSpace E F s p) : (f - g).toDistr = f - g := rfl

@[simp]
theorem sobFn_sub (f g : BesselPotentialSpace E F s p) : (f - g).sobFn = f.sobFn - g.sobFn := rfl

instance instNeg : Neg (BesselPotentialSpace E F s p) where
  neg f := {
    toDistr := -f.toDistr
    sobFn := -f.sobFn
    bessel_toDistr_eq_sobFn := by
      simp [← Lp.toTemperedDistributionCLM_apply, map_neg, f.bessel_toDistr_eq_sobFn] }

@[simp, norm_cast]
theorem toDistr_neg (f : BesselPotentialSpace E F s p) : (-f).toDistr = -f := rfl

@[simp]
theorem sobFn_neg (f : BesselPotentialSpace E F s p) : (-f).sobFn = -f.sobFn := rfl

variable {R : Type*} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
  [SMul R ℂ] [SMul R 𝓢'(E, F)] [SMul R (Lp F p (μ := (volume : Measure E)))]
  [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F p (μ := (volume : Measure E)))]

instance instSMul : SMul R (BesselPotentialSpace E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      simp [← Lp.toTemperedDistributionCLM_apply, f.bessel_toDistr_eq_sobFn] }

@[simp, norm_cast]
theorem toDistr_smul (c : R) (f : BesselPotentialSpace E F s p) : (c • f).toDistr = c • f := rfl

@[simp]
theorem sobFn_smul (c : R) (f : BesselPotentialSpace E F s p) : (c • f).sobFn = c • f.sobFn := rfl

instance instAddCommGroup : AddCommGroup (BesselPotentialSpace E F s p) :=
  fast_instance% (injective_sobFn E F s p).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

variable (E F s p) in
/-- Coercion as an additive homomorphism. -/
def coeAddMonoidHom : BesselPotentialSpace E F s p →+ 𝓢'(E, F) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeAddMonoidHom_injective : Function.Injective (coeAddMonoidHom E F s p) := by
  apply ext

instance instModule : Module ℂ (BesselPotentialSpace E F s p) :=
  fast_instance% coeAddMonoidHom_injective.module ℂ (coeAddMonoidHom E F s p) fun _ _ => by rfl

variable (E F s p) in
/-- The map `u ↦ 𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 u` as a linear map from `H^{s,p}` to `Lp`.

This definition is mainly used to define the norm and inner product on `H^{s,p}` and `H^s`,
respectively. -/
def toLpₗ : BesselPotentialSpace E F s p →ₗ[ℂ] Lp F p (volume : Measure E) where
  toFun := sobFn
  map_add' f g := by rfl
  map_smul' c f := by rfl

variable (s) in
/-- Every `Lp` function defines a Sobolev function by `f ↦ besselPotential E F (-s) f`. -/
def ofLp (f : Lp F p (volume : Measure E)) : BesselPotentialSpace E F s p where
  toDistr := besselPotential E F (-s) f
  sobFn := f
  bessel_toDistr_eq_sobFn := by simp

@[simp]
theorem sobFn_ofLp (f : Lp F p (volume : Measure E)) :
    (ofLp s f).sobFn = f := by rfl

@[simp]
theorem toDistr_ofLp (f : Lp F p (volume : Measure E)) :
    (ofLp s f).toDistr = besselPotential E F (-s) f := by rfl

@[simp]
theorem ofLp_sobFn (f : BesselPotentialSpace E F s p) :
    ofLp s f.sobFn = f :=
  injective_sobFn E F s p rfl

@[simp]
theorem toLpₗ_apply (f : BesselPotentialSpace E F s p) :
    toLpₗ E F s p f = sobFn f := by rfl

instance instNormedAddCommGroup :
    NormedAddCommGroup (BesselPotentialSpace E F s p) :=
  fast_instance% NormedAddCommGroup.induced (BesselPotentialSpace E F s p)
    (Lp F p (volume : Measure E)) (toLpₗ E F s p) (by exact injective_sobFn E F s p)

@[simp]
theorem norm_sobFn_eq (f : BesselPotentialSpace E F s p) : ‖f.sobFn‖ = ‖f‖ := by rfl

instance instNormedSpace : NormedSpace ℂ (BesselPotentialSpace E F s p) where
  norm_smul_le c f := by
    simp [← norm_sobFn_eq, ← norm_smul]

variable (E F s p) in
/-- The linear isometry between `H^{s,p}` and `Lp`. -/
def toLpₗᵢ : BesselPotentialSpace E F s p ≃ₗᵢ[ℂ] Lp F p (volume : Measure E) where
  __ := toLpₗ E F s p
  invFun := ofLp s
  left_inv f := by simp
  right_inv f := by simp
  norm_map' _ := rfl

@[simp]
theorem toLpₗᵢ_apply (f : BesselPotentialSpace E F s p) :
    toLpₗᵢ E F s p f = sobFn f := by rfl

@[simp]
theorem toLpₗᵢ_symm_apply (f : Lp F p (volume : Measure E)) :
    (toLpₗᵢ E F s p).symm f = besselPotential E F (-s) f := by rfl

instance instCompleteSpace : CompleteSpace (BesselPotentialSpace E F s p) :=
  (toLpₗᵢ E F s p).toIsometryEquiv.completeSpace

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℂ F]

variable {s : ℝ}

theorem norm_fourier_sobFn_eq (f : BesselPotentialSpace E F s 2) : ‖𝓕 f.sobFn‖ = ‖f‖ :=
  LinearIsometryEquiv.norm_map' _ _

instance instInnerProductSpace (s : ℝ) :
    InnerProductSpace ℂ (BesselPotentialSpace E F s 2) where
  inner f g := inner ℂ f.sobFn g.sobFn
  norm_sq_eq_re_inner f := by exact norm_sq_eq_re_inner f.sobFn
  conj_inner_symm f g := by simp
  add_left f g h := by simp [inner_add_left]
  smul_left f g c := by simp [inner_smul_left]

end InnerProductSpace

end BesselPotentialSpace
