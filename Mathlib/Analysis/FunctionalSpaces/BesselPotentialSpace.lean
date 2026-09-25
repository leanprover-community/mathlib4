/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.Sobolev

/-! # Bessel potential spaces

We define the Bessel potential space or Fourier-theoretic Sobolev space, with smoothness parameter
`s` and integrability parameter `p`. Informally, this space is given as the set of all tempered
distributions `u` such that `𝓕⁻ (1 + ‖ξ‖ ^ 2) ^ (s / 2) 𝓕 u` is an `Lp` function.

### Implementation notes

In `Mathlib.Analysis.Distribution.Sobolev` the unbundled version `TemperedDistribution.MemSobolev`
is defined as `∃ v : Lp, besselPotential E F s u = v`. While it would be possible to define
the bundled space in the same way, the existence quantifier makes proving theorems more involved and
hence we bundle the `Lp` function `v` into the structure.

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
  toLp : Lp F p (volume : Measure E)
  /-- The `Lp` function is obtained by applying the Bessel potential operator to the distribution -/
  bessel_toDistr_eq_toLp : besselPotential E F s toDistr = toLp

attribute [coe] BesselPotentialSpace.toDistr

namespace BesselPotentialSpace

@[inherit_doc] scoped notation "H^{" s ", " p "}(" E ", " F ")" => BesselPotentialSpace E F s p
@[inherit_doc] scoped notation "H^{" s ", " p "}(" E ")" => BesselPotentialSpace E ℂ s p
@[inherit_doc] scoped notation "H^{" s "}(" E ", " F ")" => BesselPotentialSpace E F s 2
@[inherit_doc] scoped notation "H^{" s "}(" E ")" => BesselPotentialSpace E ℂ s 2

section NormedSpace

variable [NormedSpace ℂ F]

variable {s s' : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

instance : CoeHead H^{s, p}(E, F) 𝓢'(E, F) where
  coe f := f.toDistr

private theorem ext' {f g : H^{s, p}(E, F)}
    (h₁ : f.toDistr = g.toDistr) (h₂ : f.toLp = g.toLp) : f = g := by
  cases f; cases g; congr

theorem memSobolev_toDistr (f : H^{s, p}(E, F)) : f.toDistr.MemSobolev s p  :=
  ⟨f.toLp, f.bessel_toDistr_eq_toLp⟩

@[simp]
theorem besselPotential_neg_toLp_eq {f : H^{s, p}(E, F)} :
    besselPotential E F (-s) f.toLp = f := by
  simp [← f.bessel_toDistr_eq_toLp]

@[ext]
theorem ext {f g : H^{s, p}(E, F)} (h₁ : f.toDistr = g.toDistr) : f = g := by
  apply ext' h₁ (LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot _)
  calc
    f.toLp = besselPotential E F s f.toDistr := f.bessel_toDistr_eq_toLp.symm
    _ = besselPotential E F s g.toDistr := by congr
    _ = g.toLp := g.bessel_toDistr_eq_toLp

/-- Transfer a Sobolev function in `H^{s,p}` to `H^{s', p}` given that `s = s'`. -/
def copy (s' : ℝ) (f : H^{s, p}(E, F)) (hs : s = s' := by grind) : H^{s', p}(E, F) where
  toDistr := f.toDistr
  toLp := f.toLp
  bessel_toDistr_eq_toLp := by
    rw [← hs]
    exact f.bessel_toDistr_eq_toLp

@[simp]
theorem toDistr_copy (f : H^{s, p}(E, F)) (hs : s = s') :
  (f.copy s').toDistr = f := by rfl

@[simp]
theorem toLp_copy (f : H^{s, p}(E, F)) (hs : s = s') :
  (f.copy s').toLp = f.toLp := by rfl

variable (E F s p) in
theorem injective_toLp :
    Function.Injective (toLp (s := s) (p := p) (E := E) (F := F)) := by
  intro f g hfg
  refine ext' ?_ hfg
  calc
    f.toDistr = besselPotential E F (-s) f.toLp := by simp
    _ = besselPotential E F (-s) g.toLp := by congr
    _ = g.toDistr := by simp

instance : Zero H^{s, p}(E, F) where
  zero := {
    toDistr := 0
    toLp := 0
    bessel_toDistr_eq_toLp := by simp [← Lp.toTemperedDistributionCLM_apply] }

@[simp, norm_cast]
theorem toDistr_zero : (0 : H^{s, p}(E, F)).toDistr = 0 := rfl

@[simp]
theorem toLp_zero : (0 : H^{s, p}(E, F)).toLp = 0 := rfl

instance : Add H^{s, p}(E, F) where
  add f g := {
    toDistr := f + g
    toLp := f.toLp + g.toLp
    bessel_toDistr_eq_toLp := by simp [← Lp.toTemperedDistributionCLM_apply, map_add,
      f.bessel_toDistr_eq_toLp, g.bessel_toDistr_eq_toLp] }

@[simp, norm_cast]
theorem toDistr_add (f g : H^{s, p}(E, F)) : (f + g).toDistr = f + g := rfl

@[simp]
theorem toLp_add (f g : H^{s, p}(E, F)) : (f + g).toLp = f.toLp + g.toLp := rfl

instance : Sub H^{s, p}(E, F) where
  sub f g := {
    toDistr := f - g
    toLp := f.toLp - g.toLp
    bessel_toDistr_eq_toLp := by simp [← Lp.toTemperedDistributionCLM_apply, map_sub,
      f.bessel_toDistr_eq_toLp, g.bessel_toDistr_eq_toLp] }

@[simp, norm_cast]
theorem toDistr_sub (f g : H^{s, p}(E, F)) : (f - g).toDistr = f - g := rfl

@[simp]
theorem toLp_sub (f g : H^{s, p}(E, F)) : (f - g).toLp = f.toLp - g.toLp := rfl

instance : Neg H^{s, p}(E, F) where
  neg f := {
    toDistr := -f.toDistr
    toLp := -f.toLp
    bessel_toDistr_eq_toLp := by
      simp [← Lp.toTemperedDistributionCLM_apply, map_neg, f.bessel_toDistr_eq_toLp] }

@[simp, norm_cast]
theorem toDistr_neg (f : H^{s, p}(E, F)) : (-f).toDistr = -f := rfl

@[simp]
theorem toLp_neg (f : H^{s, p}(E, F)) : (-f).toLp = -f.toLp := rfl

variable {R : Type*} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
  [SMul R ℂ] [SMul R 𝓢'(E, F)] [SMul R (Lp F p (μ := (volume : Measure E)))]
  [IsScalarTower R ℂ 𝓢'(E, F)] [IsScalarTower R ℂ (Lp F p (μ := (volume : Measure E)))]

instance : SMul R H^{s, p}(E, F) where
  smul c f := {
    toDistr := c • f.toDistr
    toLp := c • f.toLp
    bessel_toDistr_eq_toLp := by
      simp [← Lp.toTemperedDistributionCLM_apply, f.bessel_toDistr_eq_toLp] }

@[simp, norm_cast]
theorem toDistr_smul (c : R) (f : H^{s, p}(E, F)) : (c • f).toDistr = c • f := rfl

@[simp]
theorem toLp_smul (c : R) (f : H^{s, p}(E, F)) : (c • f).toLp = c • f.toLp := rfl

instance : AddCommGroup H^{s, p}(E, F) :=
  fast_instance% (injective_toLp E F s p).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

variable (E F s p) in
/-- Coercion to tempered distributions as an additive homomorphism. -/
def coeAddMonoidHom : H^{s, p}(E, F) →+ 𝓢'(E, F) where
  toFun f := f
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeAddMonoidHom_injective : Function.Injective (coeAddMonoidHom E F s p) := by
  apply ext

instance : Module ℂ H^{s, p}(E, F) :=
  fast_instance% coeAddMonoidHom_injective.module ℂ (coeAddMonoidHom E F s p) fun _ _ => by rfl

variable (E F s p) in
/-- The map `u ↦ 𝓕⁻ (1 + ‖x‖ ^ 2) ^ (s / 2) 𝓕 u` as a linear map from `H^{s,p}` to `Lp`.

See `toLpₗᵢ` for the linear isometry equivalence. -/
def toLpₗ : H^{s, p}(E, F) →ₗ[ℂ] Lp F p (volume : Measure E) where
  toFun := toLp
  map_add' f g := by rfl
  map_smul' c f := by rfl

variable (s) in
/-- Every `Lp` function defines a Sobolev function by `f ↦ besselPotential E F (-s) f`. -/
def ofLp (f : Lp F p (volume : Measure E)) : H^{s, p}(E, F) where
  toDistr := besselPotential E F (-s) f
  toLp := f
  bessel_toDistr_eq_toLp := by simp

@[simp]
theorem toLp_ofLp (f : Lp F p (volume : Measure E)) :
    (ofLp s f).toLp = f := by rfl

@[simp]
theorem toDistr_ofLp (f : Lp F p (volume : Measure E)) :
    (ofLp s f).toDistr = besselPotential E F (-s) f := by rfl

@[simp]
theorem ofLp_toLp (f : H^{s, p}(E, F)) :
    ofLp s f.toLp = f :=
  injective_toLp E F s p rfl

@[simp]
theorem toLpₗ_apply (f : H^{s, p}(E, F)) :
    toLpₗ E F s p f = toLp f := by rfl

instance : NormedAddCommGroup H^{s, p}(E, F) :=
  fast_instance% NormedAddCommGroup.induced H^{s, p}(E, F)
    (Lp F p (volume : Measure E)) (toLpₗ E F s p) (by exact injective_toLp E F s p)

@[simp]
theorem norm_toLp_eq (f : H^{s, p}(E, F)) : ‖f.toLp‖ = ‖f‖ := by rfl

instance : NormedSpace ℂ H^{s, p}(E, F) where
  norm_smul_le c f := by
    simp [← norm_toLp_eq, ← norm_smul]

variable (E F s p) in
/-- The linear isometry between `H^{s,p}` and `Lp`. -/
def toLpₗᵢ : H^{s, p}(E, F) ≃ₗᵢ[ℂ] Lp F p (volume : Measure E) where
  __ := toLpₗ E F s p
  invFun := ofLp s
  left_inv f := by simp
  right_inv f := by simp
  norm_map' _ := rfl

@[simp]
theorem toLpₗᵢ_apply (f : H^{s, p}(E, F)) :
    toLpₗᵢ E F s p f = toLp f := by rfl

@[simp]
theorem toLpₗᵢ_symm_apply (f : Lp F p (volume : Measure E)) :
    (toLpₗᵢ E F s p).symm f = besselPotential E F (-s) f := by rfl

instance : CompleteSpace H^{s, p}(E, F) :=
  (toLpₗᵢ E F s p).toIsometryEquiv.completeSpace

end NormedSpace

section InnerProductSpace

variable [InnerProductSpace ℂ F]

variable {s : ℝ}

theorem norm_fourier_toLp_eq (f : H^{s}(E, F)) : ‖𝓕 f.toLp‖ = ‖f‖ :=
  LinearIsometryEquiv.norm_map' _ _

instance (s : ℝ) : InnerProductSpace ℂ H^{s}(E, F) where
  inner f g := inner ℂ f.toLp g.toLp
  norm_sq_eq_re_inner f := by exact norm_sq_eq_re_inner f.toLp
  conj_inner_symm f g := by simp
  add_left f g h := by simp [inner_add_left]
  smul_left f g c := by simp [inner_smul_left]

end InnerProductSpace

end BesselPotentialSpace

namespace TemperedDistribution

open scoped BesselPotentialSpace

variable [NormedSpace ℂ F]

variable {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

/-- Every unbundled Sobolev tempered distribution defines an element in `H^{s, p}`. -/
def MemSobolev.toBesselPotentialSpace {f : 𝓢'(E, F)} (hf : f.MemSobolev s p) : H^{s, p}(E, F) where
  toDistr := f
  toLp := hf.choose
  bessel_toDistr_eq_toLp := hf.choose_spec

@[simp]
theorem MemSobolev.toBesselPotentialSpace_toDistr {f : 𝓢'(E, F)} (hf : f.MemSobolev s p) :
    hf.toBesselPotentialSpace.toDistr = f := by rfl

theorem MemSobolev.toBesselPotentialSpace_injective {f g : 𝓢'(E, F)} (hf : f.MemSobolev s p)
    (hg : g.MemSobolev s p) (h : hf.toBesselPotentialSpace = hg.toBesselPotentialSpace) :
    f = g := by
  rw [← hf.toBesselPotentialSpace_toDistr, ← hg.toBesselPotentialSpace_toDistr, h]

end TemperedDistribution
