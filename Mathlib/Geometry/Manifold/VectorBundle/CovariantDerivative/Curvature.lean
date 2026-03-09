/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-! # Curvature of an affine connection

We define the curvature tensor of an affine connection, i.e. a covariant derivative on the tangent
bundle `TM` of some manifold `M`.

## Main definitions and results

TODO!

-/

@[expose] public section

open Bundle Set NormedSpace
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

/-! A preliminary lemma about -/
section prelim

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

-- FIXME: does this require real bundles?
lemma exists_contMDiff_of_one_form {k : WithTop ℕ∞}
    {σ : Π x : M, V x} (hσ : CMDiffAt k (T% σ) x) :
    ∃ σ' : (Π x : M, V x),
      CMDiff k (T% σ') ∧ σ' x = σ x ∧ mfderiv% (T% σ') x = mfderiv% (T% σ) x := by
  /- proof idea: assuming smooth bump functions, this becomes a local question
  locally, convolve σ with a bump function of small support; should preserve σ x and mfderiv
  does mathlib have this already? (Moritz Doll proved something similar, I think!)
  -/
  sorry

-- We need one level more of agreement!

-- TODO: might be a better definition of smoothness; proving the equivalence requires more work!
variable {F} in
lemma ContMDiffCovariantDerivativeOn.contMDiff' [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    {k : WithTop ℕ∞} {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
    (hcov : IsCovariantDerivativeOn F cov) [hcov' : ContMDiffCovariantDerivativeOn F k cov univ]
    {σ : Π x : M, V x} (hσ :CMDiffAt (k + 1) (T% σ) x) :
    letI cov (x : M) : TotalSpace (E →L[𝕜] F) fun x ↦ TangentSpace I x →L[𝕜] V x := ⟨x, cov σ x⟩
    ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] F)) k cov x := by
  obtain ⟨σ', hσ', heqs, hdiffx⟩ := exists_contMDiff_of_one_form F hσ
  have aux := contMDiffOn_univ.mp (hcov'.contMDiff hσ'.contMDiffOn)
  -- know: ∇ σ and ∇ σ' agree at x
  have aux' := hcov.congr_of_eq_one_jet (Filter.univ_mem)
    (hσ.mdifferentiableAt (by simp)) (hσ'.mdifferentiableAt (by simp))
    heqs.symm hdiffx.symm -- TODO: choose direction for both equalities!
  -- we need one more level, though!
  sorry

end prelim

/-! ## Curvature tensor of an unbundled covariant derivative on `TM` on a set `s` -/
namespace IsCovariantDerivativeOn

variable (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x))

variable {X X' Y : (Π x : M, TangentSpace I x)}

/-- Local notation for a covariant derivative on a vector bundle acting on a vector field and a
section. -/
local syntax "∇" term:arg term : term
local macro_rules | `(∇ $X $σ) => `(fun (x : M) ↦ cov $σ x ($X x))

example {x} : (∇ X Y) x = cov Y x (X x) := by rfl

/-- The Riemannian curvature endomorphism of a covariant derivative on the tangent bundle `TM`,
as a bare function. Prefer to use `IsCovariantDerivativeOn.curvatureTensor`
(which is a (3,1)-tensor) instead. -/
noncomputable def curvatureTensorAux :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x) :=
  fun X Y Z ↦ (∇ X (∇ Y Z)) - ∇ Y (∇ X Z) - ∇ (VectorField.mlieBracket I X Y) Z

variable [IsManifold I 2 M] [CompleteSpace E]
  {cov cov' : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {X X' Y Z : Π x : M, TangentSpace I x}

-- TODO: generalise further and try to find in the library!
lemma temp
    {cov : ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x}
    (hcov : IsCovariantDerivativeOn E cov)
    {x : M} {X σ : (x : M) → TangentSpace I x}
    (hσ : CMDiff 2 T% σ) (hZ : CMDiff 2 T% X)
    (aux : ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E) x (cov X x)) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) 1 (fun x ↦ TotalSpace.mk' E x ((cov X x) (σ x))) x := by
  sorry

lemma temp' -- I suspect this one will also work!
    {cov : ((x : M) → TangentSpace I x) → (x : M) → TangentSpace I x →L[𝕜] TangentSpace I x}
    (hcov : IsCovariantDerivativeOn E cov)
    {x : M} {X σ : (x : M) → TangentSpace I x}
    -- XXX: I suspect σ being C¹ will suffice, and no extra hypotheses on X are necessary
    (hσ : CMDiffAt 1 (T% σ) x)
    (aux : ContMDiffAt I (I.prod 𝓘(𝕜, E →L[𝕜] E)) 1
      (fun x ↦ TotalSpace.mk' (E →L[𝕜] E) x (cov X x)) x) :
    ContMDiffAt I (I.prod 𝓘(𝕜, E)) 1 (fun x ↦ TotalSpace.mk' E x ((cov X x) (σ x))) x := by
  sorry

/- Lessons learned from the experiment below:
- we need the lemma temp (or perhaps just temp'); is this in mathlib already?
- the curvature tensor needs a C¹ connection, and a manifold of order 3 and minSmoothness k 2 or so
- we can only prove tensoriality for C² sections (at a point, I hope! to be confirmed),
  so need new tensoriality lemmas
- `mdifferentiableAt` lemmas for C^k covariant derivatives would be nice API addition
-/

variable [IsManifold I (2 + 1) M] [IsManifold I (minSmoothness 𝕜 2) M]

lemma aux
    (hcov : IsCovariantDerivativeOn E cov) [hcov' : ContMDiffCovariantDerivativeOn E 1 cov univ]
    {x : M} {Y Z σ : (x : M) → TangentSpace I x}
    (hσ : CMDiffAt 2 (T% σ) x) (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    (MDiffAt fun x ↦ TotalSpace.mk' E x ((cov Z x) (VectorField.mlieBracket I σ Y x))) x := by
  apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
  apply temp' hcov ?_ (hcov'.contMDiff' hcov hZ)
  apply ContMDiffAt.mlieBracket_vectorField hσ hY _
  simp; sorry -- want sth with minSmoothness instead; otherwise too weak for general 𝕜

theorem curvatureTensorAux_tensorial₁ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    [hcov' : ContMDiffCovariantDerivativeOn E 1 cov univ]
    (Y Z : (Π x : M, TangentSpace I x)) :
    TensorialAt I E (curvatureTensorAux cov · Y Z x) x where
  smul {f X} hf hX := by
    unfold curvatureTensorAux
    dsimp
    sorry
  add {σ σ'} hσ hσ' := by
    unfold curvatureTensorAux
    simp only [Pi.add_apply, map_add, Pi.sub_apply]
    --rw [VectorField.mlieBracket_add_left hσ hσ']
    have : VectorField.mlieBracket I (σ + σ') Y x =
        VectorField.mlieBracket I σ Y x + VectorField.mlieBracket I σ' Y x := by
      rw [VectorField.mlieBracket_add_left hσ hσ']
    set A := cov (fun x ↦ (cov Z x) (Y x)) x (σ x)
    set B := cov (fun x ↦ (cov Z x) (Y x)) x (σ' x)
    --erw [ContinuousLinearMap.add_apply]
    -- TODO: need stronger assumptions on σ, σ' and Z!
    have hσ : CMDiff 2 (T% σ) := sorry
    have hσ' : CMDiff 2 (T% σ') := sorry
    have hY : CMDiffAt 2 (T% Y) x := sorry
    have hZ : CMDiff 2 (T% Z) := sorry
    have hZ' : CMDiffAt 2 (T% Z) x := sorry
    -- corollaries, which occur as side goals several times
    have hZσ : MDiffAt (fun x ↦ TotalSpace.mk' E x (cov Z x (σ x))) x := by
      apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
      exact temp hcov hσ hZ (hcov'.contMDiff' hcov hZ')
    have hZσ' : MDiffAt (fun x ↦ TotalSpace.mk' E x (cov Z x (σ' x))) x := by
      apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
      exact temp hcov hσ' hZ (hcov'.contMDiff' hcov hZ')
    have missing :
      (cov (fun x ↦ (cov Z x) (VectorField.mlieBracket I (σ + σ') Y x)) x) (Y x) =
        (cov (fun x ↦ (cov Z x) (VectorField.mlieBracket I σ Y x)) x) (Y x)
        + (cov (fun x ↦ (cov Z x) (VectorField.mlieBracket I σ' Y x)) x) (Y x) := by
      trans (cov (fun x ↦ (
          cov Z x (VectorField.mlieBracket I σ Y x)) + cov Z x (VectorField.mlieBracket I σ' Y x)
          ) x) (Y x)
      · congr 1
        sorry -- missing tensoriality lemma; first arguments are equal at x
      · erw [hcov.add (aux hcov (hσ x) hY hZ') (aux hcov (hσ' x) hY hZ')]
        simp
    rw [hcov.sub]
    rotate_left
    · exact mdifferentiableAt_add_section hZσ hZσ'
    · apply ContMDiffAt.mdifferentiableAt _ one_ne_zero
      apply temp' hcov ?_ (hcov'.contMDiff' hcov hZ')
      apply ContMDiffAt.mlieBracket_vectorField (ContMDiff.add_section hσ hσ' ..) hY
      simp; sorry -- want sth with minSmoothness instead; otherwise too weak for general k
    rw [hcov.sub hZσ (aux hcov (hσ x) hY hZ')]
    dsimp
    erw [hcov.add hZσ hZσ']
    simp only [ContinuousLinearMap.add_apply]
    --set C := cov (fun x ↦ (cov Z x) (σ x)) x
    --set D := cov (fun x ↦ (cov Z x) (σ' x)) x
    rw [hcov.sub hZσ' ((aux hcov (hσ' x) hY hZ'))]
    rw [missing]
    --set E := (cov (fun x ↦ (cov Z x) (VectorField.mlieBracket I σ Y x)) x) (Y x)
    dsimp
    --set F := (cov (fun x ↦ (cov Z x) (VectorField.mlieBracket I σ' Y x)) x) (Y x)
    abel

-- update hypotheses to match lemma above, once proven!
theorem curvatureTensorAux_tensorial₂ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    [hcov' : ContMDiffCovariantDerivativeOn E 1 cov univ]
    (X Z : (Π x : M, TangentSpace I x)) :
    TensorialAt I E (curvatureTensorAux cov X · Z x) x :=
  -- proof is analogous to the version in X
  sorry

-- update hypotheses to match lemma above, once proven!
theorem curvatureTensorAux_tensorial₃ (hcov : IsCovariantDerivativeOn E cov) (x : M)
    [hcov' : ContMDiffCovariantDerivativeOn E 1 cov univ]
    (X Y : (Π x : M, TangentSpace I x)) :
    TensorialAt I E (curvatureTensorAux cov X Y · x) x :=
  -- linearity should be "easy" also, scalar multiplication is a different proof
  sorry

end IsCovariantDerivativeOn
