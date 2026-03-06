/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.MfDerivSMul
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.TrivPrelim

/-!
# Everything you always wanted to know about covariant derivatives on the trivial bundle

Don't be afraid to ask. TODO!

-/

open Bundle Filter Module Topology Set
open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section -- TODO: think if we want to expose all definitions!

open Bundle Filter Module Topology Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V]
  [IsManifold I 1 M]

namespace IsCovariantDerivativeOn

section trivial_bundle

set_option backward.isDefEq.respectTransparency false in
variable (I M F) in
@[simps]
noncomputable def trivial [IsManifold I 1 M] :
    IsCovariantDerivativeOn F (V := Trivial M F)
      (fun s x ↦ mfderiv I 𝓘(𝕜, F) s x) univ where
  add {σ σ' x} hσ hσ' hx := by
    rw [mdifferentiableAt_section_trivial_iff] at hσ hσ'
    rw [mfderiv_add hσ hσ']
  leibniz {σ f x} hσ hf hx := by
    rw [mdifferentiableAt_section] at hσ
    ext1 X₀
    exact mfderiv_smul hσ hf X₀

lemma of_endomorphism (A : (x : M) → F →L[𝕜] TangentSpace I x →L[𝕜] F) :
    IsCovariantDerivativeOn F
      (fun (s : M → F) x ↦
        letI d : TangentSpace I x →L[𝕜] F := mfderiv I 𝓘(𝕜, F) s x
        d + A x (s x)) univ :=
  trivial I M F |>.add_one_form A

end trivial_bundle

end IsCovariantDerivativeOn

namespace CovariantDerivative

section trivial_bundle

set_option backward.isDefEq.respectTransparency false in
variable (I M F) in
@[simps]
noncomputable def trivial [IsManifold I 1 M] : CovariantDerivative I F (Trivial M F) where
  toFun s x := mfderiv I 𝓘(𝕜, F) s x
  isCovariantDerivativeOnUniv := -- TODO use previous work
  { add {σ σ' x} hσ hσ' hx := by
      rw [mdifferentiableAt_section_trivial_iff] at hσ hσ'
      rw [mfderiv_add hσ hσ']
    leibniz {σ f x} hσ hf hx := by
      rw [mdifferentiableAt_section] at hσ
      ext1 X₀
      exact mfderiv_smul hσ hf X₀ }

end trivial_bundle


variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

-- TODO: does it make sense to speak of analytic connections? if so, change the definition of
-- regularity and use ∞ from `open scoped ContDiff` instead.

/-- The trivial connection on the trivial bundle is smooth -/
lemma trivial_isSmooth :
    ContMDiffCovariantDerivative (𝕜 := 𝕜) (trivial 𝓘(𝕜, E) E E') (⊤ : ℕ∞) where
  contMDiff := by -- {X σ} hX hσ
    sorry /-
    -- except for local trivialisations, contDiff_infty_iff_fderiv covers this well
    simp only [trivial]
    -- use a local trivialisation
    intro x
    specialize hX x
    -- TODO: use contMDiffOn instead, to get something like
    -- have hX' : ContMDiffOn 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) (∞ + 1)
    --  (T% σ) (trivializationAt x).baseSet := hX.contMDiffOn
    -- then want a version contMDiffOn_totalSpace
    rw [contMDiffAt_totalSpace] at hX ⊢
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
    refine ⟨contMDiff_id _, ?_⟩
    obtain ⟨h₁, h₂⟩ := hX
    -- ... hopefully telling me
    -- have h₂scifi : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') ∞
    --   (fun x ↦ σ x) (trivializationAt _).baseSet_ := sorry
    simp at h₂
    -- now use ContMDiffOn.congr and contDiff_infty_iff_fderiv,
    -- or perhaps a contMDiffOn version of this lemma?
    sorry -/

noncomputable def of_endomorphism (A : E → E' →L[𝕜] E →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Trivial E E') where
  toFun σ := fun x ↦ fderiv 𝕜 σ x + A x (σ x)
  isCovariantDerivativeOnUniv := by
    convert IsCovariantDerivativeOn.of_endomorphism (I := 𝓘(𝕜, E)) A
    ext f x v
    rw [mfderiv_eq_fderiv]

end CovariantDerivative

section

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  -- `V` vector bundle

namespace IsCovariantDerivativeOn

-- The classification of real connections over a trivial bundle
section classification

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [IsManifold I 1 M]

/-- Classification of covariant derivatives over a trivial vector bundle: every connection
is of the form `D + A`, where `D` is the trivial covariant derivative, and `A` a zeroth-order term
-/
lemma exists_one_form {cov : (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    ∃ (A : (x : M) → F →L[𝕜] TangentSpace I x →L[𝕜] F),
    ∀ σ : M → F, ∀ x ∈ s, MDiffAt (T% σ) x →
    letI d : TangentSpace I x →L[𝕜] F := mfderiv I 𝓘(𝕜, F) σ x
    cov σ x = d + A x (σ x) := by
  use hcov.difference (trivial I M F |>.mono <| subset_univ s)
  intro σ x hx hσ
  rw [hcov.difference_apply _ (by trivial) hσ]
  module

noncomputable def one_form {cov : (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    Π x : M, F →L[𝕜] TangentSpace I x →L[𝕜] F :=
  hcov.exists_one_form.choose

lemma eq_one_form {cov : (M → F) → (Π x : M, TangentSpace I x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ : M → F}
    {x : M} (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    letI d : TangentSpace I x →L[𝕜] F := mfderiv I 𝓘(𝕜, F) σ x
    cov σ x = d + hcov.one_form x (σ x) :=
  hcov.exists_one_form.choose_spec σ x hx hσ

lemma _root_.CovariantDerivative.exists_one_form
    (cov : CovariantDerivative I F (Bundle.Trivial M F)) :
    ∃ (A : (x : M) → F →L[𝕜] TangentSpace I x →L[𝕜] F),
    ∀ σ : M → F, ∀ x, MDiffAt (T% σ) x →
    letI d : TangentSpace I x →L[𝕜] F := mfderiv I 𝓘(𝕜, F) σ x
    cov σ x = d + A x (σ x) := by
  simpa using cov.isCovariantDerivativeOnUniv.exists_one_form

end classification

end IsCovariantDerivativeOn
