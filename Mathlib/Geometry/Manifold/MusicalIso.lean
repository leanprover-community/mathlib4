/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

import Aesop.BuiltinRules
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.OrthonormalFrame
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

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

variable [RiemannianBundle (fun (x : B) ↦ TangentSpace IB x)]

noncomputable section

attribute [local instance] TangentBundle.contMDiffVectorBundle

variable [IsContMDiffRiemannianBundle IB k EB (fun (x : B) ↦ TangentSpace IB x)]

section prereqs

variable [FiniteDimensional ℝ EB]

-- TODO: this needs analogous lemmas about orthonormal frames first
-- currently, it's unused (but would generalise the next lemma)
open Module in
/-- A vector field on a Riemannian manifold `(M, g)` is `C^n` at `x` if if its pairing
with any `C^n` vector field at `x` is `C^n` at `x`.
This version assumes `M` is a `C^{n+1}`-manifold with a `C^n` metric. -/
lemma contMDiffWithinAt_of_inner_bundle_apply
    {W : (x : B) → TangentSpace% x} {s : Set B} {x : B}
    (hW : ∀ {Z : (x : B) → TangentSpace% x},
      CMDiffAt[s] k (T% Z) x → CMDiffAt[s] k (fun x ↦ inner ℝ (W x) (Z x)) x) :
    CMDiffAt[s] k (T% W) x := by
  nontriviality EB
  -- Take an orthonormal frame.
  let b := Basis.ofVectorSpace ℝ EB
  let t := trivializationAt EB (TangentSpace IB : B → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ EB) := b.index_nonempty
  -- The linear ordering on the indexing set of `b` is only used in this proof,
  -- so our choice does not matter.
  have : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ EB) := by
    choose r wo using exists_wellFoundedLT _
    exact r
  have : OrderBot ↑(Basis.ofVectorSpaceIndex ℝ EB) := WellFoundedLT.toOrderBot _
  have : LocallyFiniteOrder ↑(Basis.ofVectorSpaceIndex ℝ EB) := Fintype.toLocallyFiniteOrder
  -- Choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  let frame := b.orthonormalFrame t
  have hs := t.isOrthonormalFrameOn_orthonormalFrame_baseSet (n := k) b (IB := IB)
  sorry /- rw [hs.contMDiffWithinAt_iff_inner (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt' x))]
  intro i
  simp_rw [real_inner_comm]
  exact hW (contMDiffAt_orthonormalFrame_of_mem b t i hx) -/

open Module in
/-- A vector field on a Riemannian manifold `(M, g)` is `C^n` at `x` if if its pairing
with any `C^n` vector field at `x` is `C^n` at `x`.
This version assumes `M` is a `C^{n+1}`-manifold with a `C^n` metric. -/
lemma ContMDiffAt.of_inner_bundle_apply
    {W : (x : B) → TangentSpace% x} {x : B}
    (hW : ∀ {Z : (x : B) → TangentSpace% x},
      CMDiffAt k (T% Z) x → CMDiffAt k (fun x ↦ inner ℝ (W x) (Z x)) x) :
    CMDiffAt k (T% W) x := by
  nontriviality EB
  -- Take an orthonormal frame.
  let b := Basis.ofVectorSpace ℝ EB
  let t := trivializationAt EB (TangentSpace IB : B → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have : Nonempty ↑(Basis.ofVectorSpaceIndex ℝ EB) := b.index_nonempty
  -- The linear ordering on the indexing set of `b` is only used in this proof,
  -- so our choice does not matter.
  have : LinearOrder ↑(Basis.ofVectorSpaceIndex ℝ EB) := by
    choose r wo using exists_wellFoundedLT _
    exact r
  have : OrderBot ↑(Basis.ofVectorSpaceIndex ℝ EB) := WellFoundedLT.toOrderBot _
  have : LocallyFiniteOrder ↑(Basis.ofVectorSpaceIndex ℝ EB) := Fintype.toLocallyFiniteOrder
  -- Choose an orthonormal frame (s i) near x w.r.t. to this trivialisation, and the metric g
  let frame := b.orthonormalFrame t
  have hs := t.isOrthonormalFrameOn_orthonormalFrame_baseSet (n := k) b (IB := IB)
  rw [hs.contMDiffAt_iff_inner (t.open_baseSet.mem_nhds (mem_baseSet_trivializationAt' x))]
  intro i
  simp_rw [real_inner_comm]
  exact hW (contMDiffAt_orthonormalFrame_of_mem b t i hx)

-- Same workaround as for the Levi-Civita file.
variable {I} in
omit [FiniteDimensional ℝ EB] [IsManifold IB (k + 1) B] in
lemma _root_.ContMDiffAt.inner_bundle' {X Y : Π x : B, TangentSpace IB x} {x : B}
    (hX : CMDiffAt k (T% X) x) (hY : CMDiffAt k (T% Y) x) :
    CMDiffAt k (fun x ↦ inner ℝ (X x) (Y x)) x :=
  ContMDiffAt.inner_bundle hX hY

-- TODO: generalise to any Riemannian bundle
/-- If `B` has a `C^k` Riemannian metric, then a vector field `s` of `B` is `C^k` at `x`
if and only if its pairing with any `C^k` vector field is `C^k` at `x`. -/
lemma ContMDiffAt.inner_bundle_iff_apply
    {s : (x : B) → TangentSpace IB x} {x : B} :
    CMDiffAt k (T% s) x ↔ (∀ {t : (x : B) → TangentSpace IB x},
      CMDiffAt k (T% t) x → CMDiffAt k (fun x ↦ inner ℝ (s x) (t x)) x) :=
  ⟨fun hs _t ht ↦ hs.inner_bundle' ht, fun h ↦ .of_inner_bundle_apply h⟩

-- TODO: add also the corresponding WithinAt, On and unrestricted versions of these lemmas

end prereqs

-- tinkering with the tangent and cotangent bundle: can we exhibit the musical isomorphism
-- as a diffeomorphism between them? (unconclusive; many typeclass inference failures)
section tangentcotangent

variable [∀ (x : B), CompleteSpace (TangentSpace IB x)]

#check TangentBundle IB B

variable (IB B) in
abbrev CotangentBundle := Bundle.TotalSpace EB
  (fun x : B ↦ (TangentSpace (M := B) IB x →L[ℝ] Trivial B ℝ x))

-- idea: write the musical iso as a map from the tangent to the cotangent bundle,
-- prove that is a diffeomorphism (and its own inverse) and rejoice
variable (IB B) in
def musicalIsoBundleMap : TangentBundle IB B → CotangentBundle IB B :=
    --Bundle.TotalSpace EB (fun x : B ↦ (TangentSpace (M := B) IB x →L[ℝ] ℝ)) :=
  fun X ↦
    TotalSpace.mk' EB X.1 ((InnerProductSpace.toDual ℝ (TangentSpace IB X.1)).toLinearEquiv X.2)

#synth ContMDiffVectorBundle k EB (fun x : B ↦ TangentSpace (M := B) IB x) IB

#synth ContMDiffVectorBundle k (EB →L[ℝ] ℝ)
  (fun b ↦ TangentSpace IB b →L[ℝ] Trivial B ℝ b) IB

#synth ContMDiffVectorBundle k (EB →L[ℝ] ℝ)
  (fun x : B ↦ (TangentSpace (M := B) IB x →L[ℝ] Trivial B ℝ x)) IB

-- fails
--#synth TopologicalSpace (CotangentBundle IB B)

-- fails also: that's the reason for the failure below
--#synth TopologicalSpace <|
--  Bundle.TotalSpace EB (fun x : B ↦ (TangentSpace (M := B) IB x →L[ℝ] Trivial B ℝ x))

-- #check ContMDiffVectorBundle.continuousLinearMap
--   (E₁ := fun x : B ↦ TangentSpace (M := B) IB x) (F₁ := EB) (𝕜 := ℝ) (n := k)
--   (E₂ := fun x : B ↦ Bundle.Trivial B ℝ x) (F₂ := ℝ) (IB := IB)

--#synth ContMDiffVectorBundle k EB (fun x : B ↦ TangentSpace (M := B) IB x →L[ℝ] (Bundle.Trivial B ℝ x)) IB

-- doesn't typecheck yet
--lemma contMDiff_musicalIsoBundleMap :
--    ContMDiff IB.tangent (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) k
--    (musicalIsoBundleMap IB B) := sorry

variable (IB B) in
def musicalIsoBundleMapSymm : CotangentBundle IB B → TangentBundle IB B :=
  fun X ↦ TotalSpace.mk' EB X.1 ((InnerProductSpace.toDual ℝ _).symm.toLinearEquiv X.2)

def fooeq : TangentBundle IB B ≃ CotangentBundle IB B where
  toFun := musicalIsoBundleMap IB B
  invFun := musicalIsoBundleMapSymm IB B
  left_inv := by
    intro x
    simp only [musicalIsoBundleMap, musicalIsoBundleMapSymm]
    ext
    · rfl
    simp
    sorry -- follows by basic properties...
  right_inv := sorry -- similar

-- final step: upgrade that to a diffeomorphism...

end tangentcotangent

variable [∀ (x : B), CompleteSpace (TangentSpace IB x)]

/-
given a section s : (x : M) → TangentSpace I x →L[ℝ] ℝ,
we get an induced section (x : M) → TangentSpace I x via the musical isomorphism
-/
def musicalIsoSimple (s : (x : B) → TangentSpace IB x →L[ℝ] ℝ) :
    (x : B) → TangentSpace IB x :=
  fun x ↦ (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap (s x)

-- First proof of the desired statements, using `ContMDiffAt.inner_bundle_iff_apply`
-- (proven via orthonormal frames).
section useFrames

variable [FiniteDimensional ℝ EB]

lemma fooWithinAt_simple {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ} {u : Set B} {x : B}
    (hs : CMDiffAt[u] k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x)) x) :
    CMDiffAt[u] k (T% (musicalIsoSimple s)) x := by
  simp only [musicalIsoSimple, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  sorry /- apply ContMDiffWithinAt.of_inner_bundle_apply
  intro t ht
  simp [hs.clm_bundle_apply_trivial_target ht] -/

lemma fooAt_simple {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ} {x : B}
    (hs : CMDiffAt k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x)) x) :
    CMDiffAt k (T% (musicalIsoSimple s)) x := by
  simp only [musicalIsoSimple, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  apply ContMDiffAt.of_inner_bundle_apply
  intro t ht
  simp [hs.clm_bundle_apply_trivial_target ht]

lemma foo_simple {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ}
    (hs : CMDiff k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x))) :
    CMDiff k (T% (musicalIsoSimple s)) :=
  fun x ↦ fooAt_simple (hs x)

end useFrames

section tryOtherThings

-- wait, is this actually circular now?
lemma aux {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ} {x : B}
    (hs : CMDiffAt k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x)) x) :
    letI p (x' : B) := (InnerProductSpace.toDual ℝ (TangentSpace IB x')).symm (s x')
    ContMDiff IB IB.tangent k (T% p) := by
  dsimp
  intro x₀
  rw [contMDiffAt_section_iff]
  simp_rw [TangentBundle.trivializationAt_apply']
  simp
  sorry

omit [IsManifold IB (k + 1) B]
  [IsContMDiffRiemannianBundle IB k EB fun (x : B) ↦ TangentSpace IB x]
  [RiemannianBundle fun (x : B) ↦ TangentSpace IB x]
  [∀ (x : B), CompleteSpace (TangentSpace IB x)] in
lemma goal {p : (x' : B) → TangentSpace IB x'} (hp : CMDiff k (T% p)) {x : B}
    (hx : x ∈ (chartAt HB x).source) :
    ContMDiffWithinAt IB 𝓘(ℝ, EB) k
      (fun (x' : B) ↦ (mfderiv[(chartAt HB x).source] (extChartAt IB x) x') (p x'))
      (chartAt HB x).source x := by
  convert! contMDiffAt_extChartAt.contMDiffWithinAt.mvfderivWithin
    (hp.contMDiffOn x hx) (by simp : k + 1 ≤ k + 1)
    (chartAt HB x).open_source.uniqueMDiffOn (mem_chart_source _ _)

-- playground: can we find a proof reducing to a local statement?
lemma fooAt_simple_try2 {s : (x : B) → TangentSpace IB x →L[ℝ] ℝ} {x : B}
    (hs : CMDiffAt k (fun (x : B) ↦
      TotalSpace.mk' (E := fun (x : B) ↦ TangentSpace IB x →L[ℝ] ℝ) (EB →L[ℝ] ℝ) x (s x)) x) :
    CMDiffAt k (T% (musicalIsoSimple s)) x := by
  simp only [musicalIsoSimple, LinearIsometryEquiv.toContinuousLinearEquiv_symm,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv]
  -- XXX: is there a better approach than "pair with any smooth section"?
  rw [contMDiffAt_section_iff]
  simp_rw [TangentBundle.trivializationAt_apply']
  let p (x' : B) := (InnerProductSpace.toDual ℝ (TangentSpace IB x')).symm (s x')
  have hp : ContMDiff IB IB.tangent k (T% p) := by
    sorry
  have goal : ContMDiffAt IB 𝓘(ℝ, EB) k
      (fun x' ↦ (mfderiv[(chartAt HB x).source] (extChartAt IB x) x') (p x')) x := by
    apply ContMDiffWithinAt.contMDiffAt _
      ((chartAt HB x).open_source.mem_nhds (mem_chart_source ..))
    exact goal hp (mem_chart_source _ _)
  -- TODO: need some last fiddling with the open sets, and the sorry for p: then it's done.
  apply goal.congr_of_eventuallyEq
  apply Set.EqOn.eventuallyEq_of_mem (s := (chartAt HB x).source) ?_
    ((chartAt HB x).open_source.mem_nhds (mem_chart_source HB x))
  intro y hy
  dsimp
  rw [mfderivWithin_comp (I' := IB) (u := (chartAt HB x).source)]
  on_goal 1 =>
    erw [ContinuousLinearMap.comp_apply]
    erw [mfderivWithin_range_extChartAt_symm]
    simp [p]
    congr
    simp
  -- side goals now
  · exact (mdifferentiableAt_extChartAt (by simp [hy])).mdifferentiableWithinAt
  · exact mdifferentiableWithinAt_extChartAt_symm (by simp)
  · rintro x ⟨x₀, rfl⟩
    simp
    sorry -- only true after restricting further...
  · refine UniqueDiffWithinAt.uniqueMDiffWithinAt ?_
    have aux := UniqueMDiffOn.uniqueDiffWithinAt_range_inter (I := IB) uniqueMDiffOn_univ y
    -- `simp` at aux
    simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.trans_target,
      ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm,
      PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_toPartialEquiv_symm,
      OpenPartialHomeomorph.coe_toPartialHomeomorph_symm, Set.preimage_univ, Set.subset_univ,
      inf_of_le_left, Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, and_imp,
      forall_exists_index, forall_apply_eq_imp_iff, ModelWithCorners.left_inv] at aux
    exact aux ((chartAt HB y) y) (by simp)

end tryOtherThings

/-
given a section s : (x : M) → E x →L[ℝ] TangentSpace I x →L[ℝ] ℝ,
we get an induced section (x : M) → E x →L[ℝ] TangentSpace I x via the musical isomorphism
-/
@[expose, reducible]
def musicalIso (s : (x : B) → E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) :
    (x : B) → E x →L[ℝ] TangentSpace IB x :=
  fun x ↦ (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (s x)

-- lemma musicalIso_apply (s : (x : B) → E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) (x : B) :
--   musicalIso s x =
--     (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (s x) := by
--   rfl

omit [IsContMDiffRiemannianBundle IB k F E] in
/-- Suppose `s` is a `C^k` section at `x`, then its musical isomorphism is also `C^k` at `x`. -/
lemma contMDiffAt_musicalIso_apply [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F]
    {s : (x : B) → E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ} {x : B}
    (hs : CMDiffAt k (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] (EB →L[ℝ] ℝ))
      (E := fun (x : B) ↦ E x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) x (s x)) x) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] EB)) k
      (fun (x : B) ↦ TotalSpace.mk' (F →L[ℝ] EB) (E := fun x ↦ E x →L[ℝ] TangentSpace IB x) x
        (musicalIso s x)) x := by
  have : IsManifold IB k B := IsManifold.of_le (by simp : k ≤ k + 1)
  apply ContMDiffAt.clm_bundle_of_apply
  intro σ hσ
  apply fooAt_simple
  simp only [ContinuousLinearMap.coe_coe]
  exact hs.clm_bundle_apply hσ.self_of_nhds

omit [IsContMDiffRiemannianBundle IB k F E] in
/-- Suppose `s` is a `C^k` section, then its musical isomorphism is also `C^k`. -/
lemma contMDiff_musicalIso_apply [FiniteDimensional ℝ EB] [FiniteDimensional ℝ F]
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
