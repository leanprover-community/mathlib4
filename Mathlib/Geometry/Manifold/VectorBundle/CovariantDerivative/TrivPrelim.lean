/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.SecToFun

/-!
# Supporting lemmas for CovariantDerivative.Basic trivialization stuff

TODO: PR all this to appropriate places.

-/

@[expose] public noncomputable section

open Topology

open scoped Bundle Manifold ContDiff

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

def equivTangentSpaceProd (p : M × M')
    : TangentSpace% p ≃L[𝕜] TangentSpace% p.1 × TangentSpace% p.2 :=
  ContinuousLinearEquiv.refl ..

-- TODO: redefine `equivTangentBundleProd` using the above declaration.

lemma mfderiv_of_eq (f : M → M') {x y : M} (h : x = y) :
    mfderiv% f y ∘L (tangentSpaceCast I x y).toContinuousLinearMap =
    (tangentSpaceCast I' (f x) (f y)).toContinuousLinearMap ∘L mfderiv% f x := by
  subst h
  rfl

@[simp]
lemma tangentSpaceCast_comp_symm (x y : M) : (tangentSpaceCast I x y).trans (tangentSpaceCast I y x)
= .refl _ (TangentSpace% x) := rfl
end

namespace Bundle.Trivialization

section to_trivialization
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

variable (e : Trivialization F (π F V)) [MemTrivializationAtlas e]

lemma mdifferentiableAt'
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) (v : V x) :
    MDiffAt e v :=
  e.mdifferentiableAt (IB := I) (e.coe_mem_source.mpr hx)

open NormedSpace

variable (I)

def tangentSpaceEquiv (v : TotalSpace F V)
    : TangentSpace (I.prod 𝓘(𝕜, F)) (e v) ≃L[𝕜] TangentSpace I v.proj × F :=
  (equivTangentSpaceProd I 𝓘(𝕜, F) (e v)
     |>.trans <|
   (tangentSpaceCast I (e v).1 v.proj
     |>.prodCongr <|
    fromTangentSpace (e v).2)
  )

/-- The derivative of the trivialization `e` at `v`, seen as a continuous linear
map into $T_{π(v)}M × F$ rather than $T_{e(v)}(M × F)$, by post-composing by the suitable
continuous linear equivalence.
Note: this takes a junk value if `v` is not in the source of `e` since the
`tangentSpaceCast` is meaningless in this case (see `Bundle.Trivialization.coe_fst`).
-/
def deriv (v : TotalSpace F V) : TangentSpace% v →L[𝕜] TangentSpace% v.proj × F :=
  (e.tangentSpaceEquiv I v).toContinuousLinearMap ∘L (mfderiv% e v)


/-- Casting the tangent space at `e (e.symm v)` into the one at `v`.
This has a junk value if `v` is not in `e.source`. -/
def invFunCast (v : TotalSpace F V)
    : TangentSpace% (e.toOpenPartialHomeomorph.symm (e v)) ≃L[𝕜] TangentSpace% v :=
  tangentSpaceCast (I.prod 𝓘(𝕜, F)) (e.toOpenPartialHomeomorph.symm (e v)) v

omit [(x : M) → AddCommGroup (V x)]
     [(x : M) → TopologicalSpace (V x)] [FiberBundle F V] [MemTrivializationAtlas e] in
lemma symm_comp_self {v} (hv : v ∈ e.source) :
      e.toOpenPartialHomeomorph.symm ∘ e =ᶠ[𝓝 v] id := by
    have : ∀ᶠ v' in 𝓝 v, v' ∈ e.source :=
      e.open_source.eventually_mem hv
    apply this.mono fun v' hv' ↦ ?_
    simp only [Function.comp_apply, hv', symm_apply_apply, id_eq]

-- Good
@[simp]
lemma mfderiv_symm_comp_self
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v} (hv : v ∈ e.source) :
    e.invFunCast I v ∘L mfderiv% e.toOpenPartialHomeomorph.symm (e v) ∘L mfderiv% e v
    = .id _ (TangentSpace% v) := by
  have hv'' : e v ∈ e.target := e.map_source hv -- FIXME: inlining this give a different type to D₁
  have D₁ := e.mdifferentiableAt_symm I hv''
  have D₂ : MDiffAt e v := e.mdifferentiableAt _ hv
  simp [← mfderiv_comp v D₁ D₂, (e.symm_comp_self hv).mfderiv_eq]
  rfl

omit [(x : M) → AddCommGroup (V x)]
     [(x : M) → TopologicalSpace (V x)] [FiberBundle F V] [MemTrivializationAtlas e] in
lemma self_comp_symm {v} (hv : v ∈ e.source) :
      e ∘ e.toOpenPartialHomeomorph.symm =ᶠ[𝓝 (e v)] id := by
    have : ∀ᶠ y in 𝓝 (e v), y ∈ e.target :=
      e.open_target.eventually_mem (e.map_source hv)
    apply this.mono fun v' hv' ↦ ?_
    simp [hv']

@[simp]
lemma mfderiv_self_comp_symm --FIXME bad
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
   {v} (hv : v ∈ e.source) :
   mfderiv% e (e.toOpenPartialHomeomorph.symm (e v))
    ∘L mfderiv% e.toOpenPartialHomeomorph.symm (e v) = .id 𝕜 _ := by
  have D₁ := e.mdifferentiableAt_symm I (e.map_source hv)
  have D₂ := e.mdifferentiableAt I hv
  rw [← e.symm_apply_apply hv] at D₂
  rw [← mfderiv_comp (e v) D₂ D₁, (e.self_comp_symm hv).mfderiv_eq]
  simp
  rfl

@[simp]
lemma mfderiv_invFunCast
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source) :
    mfderiv% e v ∘L (e.invFunCast I v).toContinuousLinearMap ∘L
    mfderiv% e.toOpenPartialHomeomorph.symm (e v) = .id _ (TangentSpace% (e v))  := by
  unfold invFunCast
  have D₁ := e.mdifferentiableAt_symm I (e.map_source hv)
  have D₂ := e.mdifferentiableAt I hv
  rw [← e.symm_apply_apply hv] at D₂
  rw [← ContinuousLinearMap.comp_assoc,
      mfderiv_of_eq (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) e (e.symm_apply_apply hv),
      ContinuousLinearMap.comp_assoc, ← mfderiv_comp (e v) D₂ D₁, (e.self_comp_symm hv).mfderiv_eq]
  simp

/-- The derivative of the inverse of the trivialization `e` at `v`, seen as a continuous linear
map from $T_{π(v)}M × F$ rather than $T_{e(v)}(M × F)$, by composing by the suitable
continuous linear equivalences.
Note: this takes a junk value if `v` is not in the source of `e` since the
`tangentSpaceCast` is meaningless in this case (see `Bundle.Trivialization.coe_fst`).
-/
def derivInv (v : TotalSpace F V) :
    TangentSpace% v.proj × F →L[𝕜] TangentSpace% v :=
  (e.invFunCast I v).toContinuousLinearMap
  ∘L
  (mfderiv% e.toOpenPartialHomeomorph.symm (e v))
  ∘L
  (e.tangentSpaceEquiv I v).symm.toContinuousLinearMap

variable {I}

-- #check OpenPartialHomeomorph.coe_toPartialHomeomorph_symm
-- #check PartialHomeomorph.coe_toPartialEquiv_symm
-- #check PartialEquiv.invFun_as_coe
--
-- #check Bundle.Trivialization.symm
-- #check Bundle.Trivialization.toFun'
-- #check PartialEquiv.symm
-- #check OpenPartialHomeomorph.symm
-- #check PartialHomeomorph.symm
--
-- #simp e.invFun
-- #simp e.toOpenPartialHomeomorph.symm
-- #simp e.toOpenPartialHomeomorph.symm.toFun'
-- variable {v : TotalSpace F V} in
-- #check (e.derivInv I v) ∘L (e.deriv I v)
--
-- #check PartialEquiv
-- #check e.toPartialEquiv.left_inv

-- Good
@[simp]
lemma derivInv_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source) :
    (e.derivInv I v) ∘L (e.deriv I v) = .id 𝕜 _ := by
  simp [deriv, derivInv, ← e.mfderiv_symm_comp_self I hv]
  rfl

-- Good
@[simp]
lemma derivInv_deriv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source)
    (u : TangentSpace% v) :
    (e.derivInv I v (e.deriv I v u)) = u :=
  show ((e.derivInv I v) ∘L (e.deriv I v)) u = u by simp [hv]

@[simp]
lemma mfderiv_proj_fst_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source)
    (u : TangentSpace% v) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v u = (e.deriv I v u).1 := by
  --have := e.fst_comp_eventuallyEq hv
  stop
  rw [← this.mfderiv_eq, mfderiv_comp v mdifferentiableAt_fst (e.mdifferentiableAt (I := I) hv v.2)]
  simp
  rfl -- TODO: understand why `simp` does not handle `ContinuousLinearMap.fst`

@[simp]
lemma mfderiv_proj_derivInv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source)
    (u : TangentSpace% v) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v (e.derivInv I v u) = u.1 := by
  have D₁ := e.mdifferentiableAt_symm I (e.map_source hv)
  have diff : MDiffAt (TotalSpace.proj : TotalSpace F V → M) v :=
    mdifferentiableAt_proj _
  have eq : e.toOpenPartialHomeomorph.symm (e v) = v := by simp [hv]
  rw [← eq] at diff
  have := mfderiv_comp (e v) diff D₁
  have C : (TotalSpace.proj ∘ e.toOpenPartialHomeomorph.symm) =ᶠ[𝓝 (e v)] Prod.fst := by
    have := e.baseSet_prod_univ_mem_nhds ((mem_source e).1 hv)
    filter_upwards [e.baseSet_prod_univ_mem_nhds ((mem_source e).1 hv)] with ⟨x, f⟩ ⟨hx, hf⟩
    simp [hx]
  rw [C.mfderiv_eq, eq] at this
  have := congr($this u).symm
  simpa

@[simp]
lemma deriv_derivInv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source) :
    (e.deriv I v) ∘L (e.derivInv I v) = .id 𝕜 ((TangentSpace% v.proj × F)) := by
  unfold deriv derivInv
  rw [ContinuousLinearMap.comp_assoc]
  conv =>
    enter [1, 2]
    simp only [← ContinuousLinearMap.comp_assoc, e.mfderiv_invFunCast I hv]
  simp

@[simp]
lemma deriv_derivInv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source)
    (u : TangentSpace% v.proj × F) :
    e.deriv I v (e.derivInv I v u) = u :=
  show ((e.deriv I v) ∘L (e.derivInv I v)) u = u by simp [hv]

lemma bijective_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source) :
    Function.Bijective (e.deriv I v) := by
   refine Function.bijective_iff_has_inverse.mpr ?_
   use e.derivInv I v
   constructor
   all_goals { intro u; simp [hv] }

lemma mfderiv_total_funToSec
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {s : M → F} {x : M} (hs : MDiffAt s x)
    (hx : x ∈ e.baseSet) :
    mfderiv% (T% (e.funToSec s)) x =
      e.derivInv I (e.funToSec s x) ∘L .prod (.id 𝕜 <| TangentSpace% x) (mfderiv% s x) := by
  -- TODO build a world where this proof is not pure pain.
  stop
  rw [(e.totalSpace_mk_funToSec hx s).mfderiv_eq,
      mfderiv_comp x (e.mdifferentiableAt_invFun (I := I) hx (s x))]
  · congr 2
    · stop
      simp [hx]
    · rw [mfderiv_prodMk]
      · erw [mfderiv_id]
        stop
        rfl
      · exact mdifferentiableAt_id
      · exact hs
  · exact mdifferentiableAt_id.prodMk hs


noncomputable def _root_.Bundle.vert (v : TotalSpace F V) :
    Submodule 𝕜 (TangentSpace% v) :=
  (mfderiv (I.prod 𝓘(𝕜, F)) I Bundle.TotalSpace.proj v).ker

lemma comap_vert
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v ∈ e.source) :
    Bundle.vert v = Submodule.comap (e.deriv I v).toLinearMap
      (Submodule.prod ⊥ ⊤) := by
  ext x
  stop
  have : Prod.fst ∘ e =ᶠ[𝓝 v] TotalSpace.proj := e.fst_comp_eventuallyEq hv
  unfold vert
  stop
  rw [← this.mfderiv_eq, mfderiv_comp v mdifferentiableAt_fst (e.mdifferentiableAt hv _)]
  simp
  rfl

lemma mfderiv_comp_section
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt T%σ x)
    (u : TangentSpace% x) (hx : x ∈ e.baseSet) :
    e.deriv I (σ x) ((mfderiv% T%σ x) u) = (u, mfderiv% (e.secToFun σ) x u) := by
  -- unused; could or should this be a separate lemma?
  -- have : mfderiv% (e ∘ T%σ) x = (e.deriv I (σ x)) ∘L (mfderiv% T%σ x) :=
  --  mfderiv_comp x (e.mdifferentiableAt hx _) hσ
  have : mfderiv% (e ∘ T%σ) x u = e.deriv I (σ x) ((mfderiv% T%σ x) u) := by
    rw [mfderiv_comp x (e.mdifferentiableAt' hx _) hσ]
    rfl
  erw [← this]
  rw [(e.apply_total_eventuallyEq hx _).mfderiv_eq]
  erw [mfderiv_prodMk, mfderiv_id]
  · -- TODO make sure the `change` below isn’t needed.
    -- Uncommenting the next lines is meant to help understanding the issue.
    -- have : ((ContinuousLinearMap.id 𝕜 (TangentSpace% x)).prod
    --    (mfderiv I 𝓘(𝕜, F) (e.secToFun σ) x)) u =
    --    (u, (mfderiv I 𝓘(𝕜, F) (e.secToFun σ) x) u) := sorry
    -- with_reducible exact this
    change (ContinuousLinearMap.id _ _).prod _ _ = _
    simp
  · apply mdifferentiableAt_id
  · exact (e.mdifferentiableAt_section_iff I σ hx).mp hσ

lemma mfderiv_secToFun_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {σ : (x : M) → V x} {x : M} (hσ : MDiffAt (T% σ) x) (hx : x ∈ e.baseSet)
    (u : TangentSpace% x) :
    mfderiv% (e.secToFun σ) x u =
      (e.deriv I (σ x) (mfderiv% T%σ x u)).2 :=
  congr(Prod.snd $(e.mfderiv_comp_section hσ u hx)).symm

lemma mfderiv_secToFun
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {σ : (x : M) → V x} {x : M} (hσ : MDiffAt (T% σ) x) (hx : x ∈ e.baseSet) :
    mfderiv% (e.secToFun σ) x =
      .snd 𝕜 (TangentSpace% x) F ∘L (e.deriv I (σ x)) ∘L (mfderiv% T%σ x) :=
  ContinuousLinearMap.ext fun u ↦ mfderiv_secToFun_apply e hσ hx u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

@[simp]
theorem _root_.Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDiffAt (T% σ) e ↔ DifferentiableAt 𝕜 σ e := by
  simp [mdifferentiableAt_totalSpace, mdifferentiableAt_iff_differentiableAt]

-- unused but we need all combinations at some point.
@[simp]
theorem _root_.Bundle.Trivial.contMDiffOn_iff
    {σ : (x : E) → Trivial E E' x} {s : Set E} :
    ContMDiffOn 𝓘(𝕜, E) (𝓘(𝕜, E).prod 𝓘(𝕜, E')) n (T% σ) s ↔ ContDiffOn 𝕜 n σ s := by
  sorry

end to_trivialization
end Bundle.Trivialization

section
@[simp]
lemma Bundle.TotalSpace.proj_mk' {B : Type*} {F : Type*} {E : B → Type*} (b : B) (e : E b) :
    proj (TotalSpace.mk' F b e) = b := rfl
end
