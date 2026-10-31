/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The musical isomorphism preserves smoothness

TODO: once all proofs are complete, generalise them appropriately
(e.g., to any field, more general vector bundles)
and move these lemmas to their proper locations
-/

open Bundle FiberBundle Function NormedSpace

open scoped Manifold ContDiff

public section

-- Let E be a C^k vector bundle over a C^k manifold B.
variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [IsManifold IB 1 B] {k : ℕ∞ω} [IsManifold IB (k + 1) B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [ContMDiffVectorBundle k F E IB]
  [IsContMDiffRiemannianBundle IB k F E]

variable [RiemannianBundle (fun (x : B) ↦ TangentSpace IB x)] [CompleteSpace EB]
  [∀ (x : B), CompleteSpace (TangentSpace IB x)]

noncomputable section

local instance : ContMDiffVectorBundle k EB (TangentSpace (M := B) IB) IB :=
  TangentBundle.contMDiffVectorBundle (M := B) (I := IB) (n := k)

section simpler


/-
given a section s : (x : M) → TangentSpace I x →L[ℝ] ℝ,
we get an induced section (x : M) → TangentSpace I x via the musical isomorphism
-/
def musicalIsoSimple (s : (x : B) → TangentSpace IB x →L[ℝ] ℝ) :
    (x : B) → TangentSpace IB x :=
  fun x ↦ (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap (s x)

variable [IsContMDiffRiemannianBundle IB k EB (fun (x : B) ↦ TangentSpace IB x)]

#check TangentBundle IB B

variable (IB B) in
def CotangentBundle := Bundle.TotalSpace EB (fun x : B ↦ (TangentSpace (M := B) IB x →L[ℝ] ℝ))

-- idea: write the musical iso as a map from the tangent to the cotangent bundle,
-- prove that is a smooth embedding and be happy
def foo : TangentBundle IB B → CotangentBundle IB B :=
  fun X ↦
    let a := (InnerProductSpace.toDual ℝ (TangentSpace IB X.1))
    TotalSpace.mk' EB X.1 (a.toLinearEquiv sorry)

-- lemma verysimple : True := by
--   let f : (TangentBundle IB B) →
--     (Bundle.TotalSpace EB (fun x : B ↦ (TangentSpace (M := B) IB x →L[ℝ] ℝ))) := sorry

-- Same workaround as for the Levi-Civita file.
variable {I} in
omit [IsManifold IB (k + 1) B] [CompleteSpace EB] [∀ (x : B), CompleteSpace (TangentSpace IB x)] in
lemma _root_.ContMDiffAt.inner_bundle' {X Y : Π x : B, TangentSpace IB x} {x : B}
    (hX : CMDiffAt k (T% X) x) (hY : CMDiffAt k (T% Y) x) :
    CMDiffAt k (fun x ↦ inner ℝ (X x) (Y x)) x :=
  ContMDiffAt.inner_bundle hX hY

-- TODO: review if the shape of h is right, and generalise this a lot
lemma ContMDiffAt.of_inner_bundle_apply
    {s : (x : B) → TangentSpace IB x} {x : B}
    (h : ∀ {t : (x : B) → TangentSpace IB x},
      CMDiffAt k (T% t) x → CMDiffAt k (fun x ↦ inner ℝ (s x) (t x)) x) :
    CMDiffAt k (T% s) x := by
  let ψ : (x : B) → TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ :=
    fun x ↦ innerSL ℝ --sorry
  let φ : (x : B) → TangentSpace IB x → ℝ :=
    fun x X ↦ ψ x (s x) X
  let φ : (x : B) → TangentSpace IB x →L[ℝ] ℝ := sorry -- φ modulo stuff

  -- this should be ContMDiffAt.clm_bundle_of_apply₂
  #check ContMDiffAt.clm_bundle_of_apply
  sorry

-- TODO: generalise to any Riemannian bundle
/-- If `B` has a `C^k` Riemannian metric, then a vector field `s` of `B` is `C^k` at `x`
if and only if its pairing with any `C^k` vector field is `C^k` at `x`. -/
lemma ContMDiffAt.inner_bundle_iff_apply {s : (x : B) → TangentSpace IB x} {x : B} :
    CMDiffAt k (T% s) x ↔ (∀ {t : (x : B) → TangentSpace IB x},
      CMDiffAt k (T% t) x → CMDiffAt k (fun x ↦ inner ℝ (s x) (t x)) x) :=
  ⟨fun hs _t ht ↦ hs.inner_bundle' ht, fun h ↦ ContMDiffAt.of_inner_bundle_apply h⟩

-- TODO: add also the corresponding WithinAt, On and unrestricted versions of these lemmas

lemma fooAt_simple {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ} {x : B}
    (hs : CMDiffAt k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x)) x) :
    CMDiffAt k (T% (musicalIsoSimple s)) x := by
  simp only [musicalIsoSimple, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  -- XXX: is there a better approach than "pair with any smooth section"?
  --rw [contMDiffAt_iff]
  rw [contMDiffAt_section]
  have (x₀ : B) (e : HB) :
      fderivWithin ℝ ((IB ∘ (chartAt HB x₀)) ∘ (chartAt HB x₀).symm ∘ IB.symm) (Set.range ↑IB) (IB e) =
    fderivWithin ℝ id (Set.range IB) (IB e) := sorry
  conv =>
    enter [4, x']
    rw [TangentBundle.trivializationAt_apply (E := EB) (I := IB) (x := x)]
    simp
  let echart (x' : B) := extChartAt IB x'
  let p (x' : B) := (InnerProductSpace.toDual ℝ (TangentSpace IB x')).symm (s x')
  have h1 (x') : MDiffAt[Set.univ] (echart x) ((echart x').symm ((echart x') x')) := sorry
  have h2 (x') : MDiffAt[Set.range IB] (echart x').symm ((echart x') x') := by
    sorry
  have h3 (x') : UniqueMDiffAt[Set.range IB] ((echart x') x') := sorry
  have h4 (x') : ((echart x').symm ((echart x') x')) = x' := by simp [echart]
  let A (x') := mfderiv% (echart x) x' -- ((echart x').symm ((echart x') x'))
  let Bl (x') := mfderiv[Set.range IB] (echart x').symm ((echart x') x')

  let Bp (x') := Bl x' (p x') -- from B into TB
  have aux'' : ContMDiffAt IB 𝓘(ℝ, EB) k (fun x' ↦ ((A x') ∘SL (Bl x')) (p x')) x := sorry

  have aux' : ContMDiffAt IB 𝓘(ℝ, EB) k
      (fun x' ↦ (mfderiv[Set.range IB] ((echart x) ∘ (echart x').symm) (echart x' x')) (p x'))
      x := by
    conv =>
      enter [4, x']
      rw [mfderivWithin_comp (I' := IB) (u := Set.univ) _ (h1 x') (h2 x') (by simp) (h3 x'),
        mfderivWithin_univ, h4 x']
    sorry
  have aux : ContMDiffAt IB 𝓘(ℝ, EB) k
    (fun x' ↦ (fderivWithin ℝ ((echart x) ∘ (echart x').symm) (Set.range IB) (echart x' x')) (p x'))
    x := by
    convert! aux'
    sorry
  apply aux.congr
  · intro y hy
    simp [p, echart]
  · simp [p, echart]
  -- alternative proof, using orthonormal frames
  -- rw [ContMDiffAt.inner_bundle_iff_apply (IB := IB)]
  -- intro t ht
  -- simp [hs.clm_bundle_apply_trivial_target ht]

#exit
lemma foo_simple {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ}
    (hs : CMDiff k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x))) :
    CMDiff k (T% (musicalIsoSimple s)) :=
  fun x ↦ fooAt_simple (hs x)

end simpler

/-
given a section s : (x : M) → E x →L[ℝ] TangentSpace I x →L[ℝ] ℝ,
we get an induced section (x : M) → E x →L[ℝ] TangentSpace I x via the musical isomorphism
-/
def musicalIso (s : (x : B) → E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) :
    (x : B) → E x →L[ℝ] TangentSpace IB x :=
  fun x ↦ (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (s x)

-- lemma musicalIso_apply (s : (x : B) → E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) (x : B) :
--   musicalIso s x =
--     (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (s x) := by
--   rfl

-- Suppose s is a C^k section, then its musical isomorphism is also C^k.
-- TODO: prove point-wise within at version of all these
omit [IsContMDiffRiemannianBundle IB k F E] in -- temporarily omitted to silence a warning
lemma foo [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F]
    {s : (x : B) → E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ}
    (hs : CMDiff k (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] (EB →L[ℝ] ℝ))
      (E := fun (x : B) ↦ E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) x (s x))) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] EB)) k
      (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] EB) (E := fun x ↦ E x →L[ℝ] TangentSpace IB x) x
        (musicalIso s x)) := by
  have : IsManifold IB k B := IsManifold.of_le (by simp : k ≤ k + 1)
  apply ContMDiff.clm_bundle_of_apply
  intro σ x hσ
  apply fooAt_simple
  simp only [ContinuousLinearMap.coe_coe]
  exact (hs _).clm_bundle_apply hσ.self_of_nhds
