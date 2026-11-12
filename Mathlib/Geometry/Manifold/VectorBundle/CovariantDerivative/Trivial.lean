/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.TrivPrelim

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Everything you always wanted to know about covariant derivatives on the trivial bundle

Don't be afraid to ask. TODO!

-/

open Bundle Filter Module NormedSpace Topology Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V]

namespace IsCovariantDerivativeOn

section trivial_bundle

set_option backward.isDefEq.respectTransparency false in
variable (I M F) in
@[simps]
lemma trivial :
    IsCovariantDerivativeOn F (V := Trivial M F) (fun s x ↦ mvfderiv I s x) univ where
  add hσ hσ' hx := by
    rw [mdifferentiableAt_section_trivial_iff] at hσ hσ'
    rw [mvfderiv_add hσ hσ']
  leibniz hσ hg hx := by
    rw [mdifferentiableAt_section] at hσ
    ext1 X₀
    simp at hσ
    simp [mvfderiv_smul hg hσ]

lemma of_endomorphism (A : (x : M) → F →L[𝕜] TangentSpace% x →L[𝕜] F) :
    IsCovariantDerivativeOn F (fun (s : M → F) x ↦ d% s x + A x (s x)) univ :=
  trivial I M F |>.add_one_form A

end trivial_bundle

end IsCovariantDerivativeOn

namespace CovariantDerivative

section trivial_bundle

variable (I M F) in
@[simps]
noncomputable def trivial : CovariantDerivative I F (Trivial M F) where
  toFun s x := mfderiv I 𝓘(𝕜, F) s x
  isCovariantDerivativeOnUniv := IsCovariantDerivativeOn.trivial ..

end trivial_bundle

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

-- TODO: does it make sense to speak of analytic connections? if so, change the definition of
-- regularity and use ∞ from `open scoped ContDiff` instead.

/-- The trivial connection on the trivial bundle is smooth -/
lemma trivial_isSmooth : ContMDiffCovariantDerivative (trivial 𝓘(𝕜, E) E E') (⊤ : ℕ∞) where
  contMDiff := ⟨by
    intro σ hσ
    dsimp only [trivial]
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
    sorry -/⟩

noncomputable def of_endomorphism (A : E → E' →L[𝕜] E →L[𝕜] E') :
    CovariantDerivative 𝓘(𝕜, E) E' (Trivial E E') where
  toFun σ := fun x ↦ fderiv 𝕜 σ x + A x (σ x)
  isCovariantDerivativeOnUniv := by
    convert IsCovariantDerivativeOn.of_endomorphism (I := 𝓘(𝕜, E)) A
    simp_rw [mvfderiv_eq_fderiv]
    rfl

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

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]

/-- Classification of covariant derivatives over a trivial vector bundle: every connection
is of the form `D + A`, where `D` is the trivial covariant derivative, and `A` a zeroth-order term
-/
lemma exists_one_form {cov : (M → F) → (Π x : M, TangentSpace% x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    ∃ (A : (x : M) → F →L[𝕜] TangentSpace% x →L[𝕜] F),
    ∀ σ : M → F, ∀ x ∈ s, MDiffAt (T% σ) x → cov σ x = d% σ x + A x (σ x) := by
  use hcov.difference (trivial I M F |>.mono <| subset_univ s)
  intro σ x hx hσ
  rw [hcov.difference_apply _ (by trivial) hσ]
  simp only [mvfderiv]
  module

noncomputable def one_form {cov : (M → F) → (Π x : M, TangentSpace% x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s) :
    Π x : M, F →L[𝕜] TangentSpace% x →L[𝕜] F :=
  hcov.exists_one_form.choose

lemma eq_one_form {cov : (M → F) → (Π x : M, TangentSpace% x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ : M → F} {x : M} (hσ : MDiffAt (T% σ) x) (hx : x ∈ s := by trivial) :
    cov σ x = d% σ x + hcov.one_form x (σ x) :=
  hcov.exists_one_form.choose_spec σ x hx hσ

-- TODO: do we want this version instead?
lemma eq_one_form_lemming {cov : (M → F) → (Π x : M, TangentSpace% x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    {σ : M → F} {x : M} (hσ : MDiffAt[s] (T% σ) x) (hx : x ∈ s := by trivial) :
    cov σ x = d% σ x + hcov.one_form x (σ x) :=
  sorry -- hcov.exists_one_form.choose_spec σ x hx hσ

lemma _root_.CovariantDerivative.exists_one_form
    (cov : CovariantDerivative I F (Bundle.Trivial M F)) :
    ∃ (A : (x : M) → F →L[𝕜] TangentSpace% x →L[𝕜] F),
    ∀ σ : M → F, ∀ x, MDiffAt (T% σ) x →
    cov σ x = d% σ x + A x (σ x) := by
  simpa using! cov.isCovariantDerivativeOnUniv.exists_one_form

#click_suggestions

lemma _root_.mvfderivWithin_of_mem_nhds {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set M} (g : M → F) {x : M} (hx : s ∈ 𝓝 x)
    : d[s] g x = d% g x := by
  ext v
  change fromTangentSpace (g x) ((mfderiv[s] g x v)) = _
  rw [mfderivWithin_of_mem_nhds hx]
  rfl

lemma _root_.IsOpen.mvfderivWithin {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set M} (hs : IsOpen s) {g : M → F} {x : M} (hx : x ∈ s)
    : d[s] g x = d% g x :=
  mvfderivWithin_of_mem_nhds g <| hs.mem_nhds hx

lemma Bundle.Trivial.contMDiffWithinAt_section_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    {s : B → F} {a : Set B} {x₀ : B} {n : ℕ∞ω}
    : CMDiffAt[a] n (T% s) x₀ ↔ CMDiffAt[a] n s x₀ := by
  rw [Bundle.contMDiffWithinAt_section_iff]
  rfl

lemma Bundle.Trivial.contMDiffAt_section_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    {s : B → F} {x₀ : B} {n : ℕ∞ω}
    : CMDiffAt n (T% s) x₀ ↔ CMDiffAt n s x₀ := by
  rw [Bundle.contMDiffAt_section_iff]
  rfl

lemma _root_.ContMDiffWithinAt.mvfderiv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    [IsManifold IB 1 B] [IsManifold IB (n + 1) B] -- Aaaargggh
    {s : B → F} {a : Set B} {x₀ : B} (ha : IsOpen a) (hx₀ : x₀ ∈ a)
    (hs : ContMDiffWithinAt IB 𝓘(𝕜, F) (n + 1) s a x₀)
    : ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, EB →L[𝕜] F)) n
        (fun x : B ↦ TotalSpace.mk' (EB →L[𝕜] F) x (d% s x)) a x₀ := by
  have : IsManifold IB n B := IsManifold.of_le (by norm_num : n ≤ n + 1)
  have : ContMDiffVectorBundle n EB (fun x : B ↦ TangentSpace IB x) IB :=
    TangentBundle.contMDiffVectorBundle -- TODO: understand why this is needed
  rw [← Bundle.Trivial.contMDiffWithinAt_section_iff] at hs
  let φ : (x : B) → TangentSpace IB x →L[𝕜] Trivial B F x := d% s
  have := @ContMDiffWithinAt.clm_bundle_of_apply' (B := B) (IB := IB) (F₁ := EB) (F₂ := F)
    (E₁ := TangentSpace IB) (E₂ := Trivial B F) (k := n) (φ := φ) (l := n)
  apply this<;> clear this
  · assumption
  · assumption
  intro X hX
  unfold φ
  rw [Bundle.Trivial.contMDiffWithinAt_section_iff] at hs
  have foo {X : Π x : B, TangentSpace% x} := hs.mvfderivWithin (X := X) (m := n)
  specialize foo (X := X) hX.self_of_nhds le_rfl ha.uniqueMDiffOn hx₀
  suffices ContMDiffWithinAt IB 𝓘(𝕜, F) n (fun x ↦ (d% s x) (X x)) a x₀ by
    exact contMDiffWithinAt_section_iff.mpr this
  apply foo.congr
  · intro y hy
    symm
    rw [ha.mvfderivWithin hy]
  · rw [ha.mvfderivWithin hx₀]


lemma _root_.ContMDiffAt.mvfderiv'
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [FiniteDimensional 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    [IsManifold IB 1 B] [IsManifold IB (n + 1) B] -- Aaaargggh
    {s : B → F} {x₀ : B}
    (hs : ContMDiffAt IB 𝓘(𝕜, F) (n + 1) s x₀)
    : ContMDiffAt IB (IB.prod 𝓘(𝕜, EB →L[𝕜] F)) n
        (fun x : B ↦ TotalSpace.mk' (EB →L[𝕜] F) x (d% s x)) x₀ :=
  ContMDiffWithinAt.mvfderiv isOpen_univ (mem_univ x₀) hs

lemma contMDiffOn_one_form [IsManifold I 1 M] [IsManifold I (n + 1) M] [FiniteDimensional 𝕜 E]
    {cov : (M → F) → (Π x : M, TangentSpace% x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : ContMDiffCovariantDerivativeOn' F n cov s) (hs : IsOpen s) {x : M} (hx : x ∈ s) :
    letI V : M → Type _ := fun m ↦ F →L[𝕜] TangentSpace% m →L[𝕜] F
    CMDiffAt n (fun m ↦ TotalSpace.mk' (E := V) (F →L[𝕜] E →L[𝕜] F) m (hcov.one_form m)) x := by
  have : ContMDiffVectorBundle n E (fun x : M ↦ TangentSpace I x) I :=
    TangentBundle.contMDiffVectorBundle -- TODO: understand why this is needed
  apply ContMDiffAt.clm_bundle_of_apply' (n+1)
  intro σ hσ
  apply ContMDiffAt.contMDiffWithinAt
  let V := TotalSpace (E →L[𝕜] F) fun x : M ↦ TangentSpace I x →L[𝕜] F
  have : ∀ᶠ x' in 𝓝 x, cov σ x' = d% σ x' + (hcov.one_form x') (σ x') := by
    filter_upwards [hσ, hs.mem_nhds hx] with x' hσx' hx'
    exact hcov.eq_one_form (hσx'.mdifferentiableAt <| by simp)
  have : ∀ᶠ x' in 𝓝 x,
      (TotalSpace.mk' (E →L[𝕜] F) x' (hcov.one_form x' (σ x')) : V) =
      TotalSpace.mk' (E →L[𝕜] F) x' (cov σ x' - d% σ x') := by
    filter_upwards [this] with x' hx'
    simp [hx']
  apply ContMDiffAt.congr_of_eventuallyEq _ this
  apply ContMDiffWithinAt.sub_section
  · -- FIXME: awful delaborator bug!
    have := hcov'.contMDiffWithinAt (x := x) (σ := σ) hx
    rw [hs.nhdsWithin_eq hx] at this
    have := this (hσ.mono fun y hy ↦ hy.contMDiffWithinAt)
    apply this.contMDiffAt <| hs.mem_nhds hx
  · have := hσ.self_of_nhds
    rw [Bundle.Trivial.contMDiffAt_section_iff] at this
    exact this.mvfderiv'

lemma contMDiffOn_one_form' [IsManifold I 1 M] [IsManifold I (n + 1) M] [FiniteDimensional 𝕜 E]
    {cov : (M → F) → (Π x : M, TangentSpace% x →L[𝕜] F)}
    {s : Set M} (hcov : IsCovariantDerivativeOn F cov s)
    (hcov' : ContMDiffCovariantDerivativeOn' F n cov s) (hs : IsOpen s) :
    letI V : M → Type _ := fun m ↦ F →L[𝕜] TangentSpace% m →L[𝕜] F
    CMDiff[s] n (fun m ↦ TotalSpace.mk' (E := V) (F →L[𝕜] E →L[𝕜] F) m (hcov.one_form m)) := by
  have : ContMDiffVectorBundle n E (fun x : M ↦ TangentSpace I x) I :=
    TangentBundle.contMDiffVectorBundle -- TODO: understand why this is needed
  apply ContMDiffOn.clm_bundle_of_apply' (n+1)
  intro σ x hx hσ
  have hσ' : ∀ᶠ b in 𝓝[s] x, ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) (n + 1) (T% σ) s b :=
    eventually_nhdsWithin_of_eventually_nhds hσ
  have : ∀ᶠ x' in 𝓝[s] x, cov σ x' = d% σ x' + (hcov.one_form x') (σ x') := by
    filter_upwards [hσ', eventually_mem_nhdsWithin] with x' hx' Hx'
    exact hcov.eq_one_form_lemming (hx'.mdifferentiableWithinAt (by simp))
  let V := TotalSpace (E →L[𝕜] F) fun x : M ↦ TangentSpace I x →L[𝕜] F
  have : ∀ᶠ x' in 𝓝[s] x,
      (TotalSpace.mk' (E →L[𝕜] F) x' (hcov.one_form x' (σ x')) : V) =
      TotalSpace.mk' (E →L[𝕜] F) x' (cov σ x' - d% σ x') := by
    filter_upwards [this] with x' hx'
    simp [hx']
  apply ContMDiffWithinAt.congr_of_eventuallyEq _ this (this.self_of_nhdsWithin hx)
  apply ContMDiffWithinAt.sub_section
  · -- FIXME: awful delaborator bug!
    exact hcov'.contMDiffWithinAt hx hσ'
  · have := hσ.self_of_nhds
    rw [Bundle.Trivial.contMDiffWithinAt_section_iff] at this
    exact this.mvfderiv hs hx

-- TODO: add global variant!

end classification

end IsCovariantDerivativeOn
