/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The musical isomorphism preserves smoothness

TODO: once all proofs are complete, generalise them appropriately
(e.g., to any field, more general vector bundles)
and move these lemmas to their proper locations
-/

open Bundle FiberBundle Function NormedSpace VectorField

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

-- TODO: generalise to any Riemannian bundle; does this exist already?
/-- If `B` has a `C^k` Riemannian metric, then a vector field `s` of `B` is `C^k` at `x`
if and only if its pairing with any `C^k` vector field is `C^k` at `x`. -/
lemma hogeAt {s : (x : B) → TangentSpace IB x} {x : B} :
    CMDiffAt k (T% s) x ↔ (∀ {t : (x : B) → TangentSpace IB x},
      CMDiffAt k (T% t) x → CMDiffAt k (fun x ↦ inner ℝ (s x) (t x)) x) := by
  refine ⟨fun hs t ht ↦ ?_, fun h ↦ ?_⟩
  · let ψ : (x : B) → TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] Bundle.Trivial B ℝ x :=
      fun x ↦ innerSL ℝ (E := TangentSpace IB x)
    have hψ : ContMDiffAt IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) k
      (fun m ↦ TotalSpace.mk' (E := fun x ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
        (EB →L[ℝ] EB →L[ℝ] ℝ) m (innerSL ℝ)) x := by
      sorry -- Riemannian metric is C^k
    let aux := ContMDiffAt.clm_bundle_apply₂ (F₃ := ℝ) hψ hs ht
    -- Remaining: reduce `aux` to this statement
    sorry
  · sorry

/-- If `B` has a `C^k` Riemannian metric, then a vector field `s` of `B` is `C^k`
if and only if its pairing with any `C^k` vector field is `C^k`. -/
lemma hoge {s : (x : B) → TangentSpace IB x} :
    CMDiff k (T% s) ↔ (∀ {t : (x : B) → TangentSpace IB x},
      CMDiff k (T% t) → ContMDiff IB 𝓘(ℝ) k (fun x ↦ inner ℝ (s x) (t x))) := by
  refine ⟨fun hs t ht x ↦ hogeAt.mp (hs x) (ht x), ?_⟩
  intro ht x
  -- TODO: needs a slightly different proof, but should be the same in both cases
  sorry

lemma fooAt_simple {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ} {x : B}
    (hs : CMDiffAt k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x)) x) :
    CMDiffAt k (T% (musicalIsoSimple s)) x := by
  simp only [musicalIsoSimple, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  rw [hogeAt (IB := IB)]
  intro t ht
  simp [hs.clm_bundle_apply_trivial_target ht]

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
