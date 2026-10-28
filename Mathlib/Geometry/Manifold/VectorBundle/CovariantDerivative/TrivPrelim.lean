/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Topology.VectorBundle.SecToFun

/-!
# Supporting lemmas for CovariantDerivative.Basic trivialization stuff

TODO: PR all this to appropriate places.

-/

@[expose] public section

open Topology

open scoped Bundle Manifold ContDiff

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

lemma mdifferentiableAt_invFun
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) (f : F) :
    MDiffAt e.invFun (x, f) := by
  apply ContMDiffAt.mdifferentiableAt ?_ zero_ne_one.symm
  exact e.contMDiffAt_symm (e.mk_mem_target.mpr hx)

-- Note: The definition below (ab)uses definitional
-- equality of `TangentSpace (I.prod 𝓘(𝕜, F)) (↑t v)`
-- which is $T_{t(v)} (M × F)$ and `TM v.proj × F`
-- which is $T_{π(v)} M × F$.
variable (I) in
noncomputable
def deriv (v : TotalSpace F V) :
    TangentSpace% v →L[𝕜] TangentSpace% v.proj × F :=
  mfderiv% e v

variable (I) in
noncomputable
def derivInv (v : TotalSpace F V) :
    TangentSpace% v.proj × F →L[𝕜] TangentSpace% v :=
  mfderiv% e.invFun (e v)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma derivInv_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    (e.derivInv I v) ∘L (e.deriv I v) = .id 𝕜 _ := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  have D₂ : MDiffAt e v := e.mdifferentiableAt' (I := I) hv v.2
  have D1' := D₁
  simp only [PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_toPartialEquiv_symm] at D1'
  rw [e.mk_proj_snd' hv] at D₁
  have comp := mfderiv_comp v D₁ D₂
  rw [(invFun_comp_eventuallyEq e hv).mfderiv_eq, mfderiv_id] at comp
  simp [deriv, derivInv]
  sorry

@[simp]
lemma derivInv_deriv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace% v) :
    (e.derivInv I v (e.deriv I v u)) = u :=
  show ((e.derivInv I v) ∘L (e.deriv I v)) u = u by simp [hv]

@[simp]
lemma mfderiv_proj_fst_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace% v) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v u = (e.deriv I v u).1 := by
  have := e.fst_comp_eventuallyEq hv
  stop
  rw [← this.mfderiv_eq, mfderiv_comp v mdifferentiableAt_fst (e.mdifferentiableAt (I := I) hv v.2)]
  simp
  rfl -- TODO: understand why `simp` does not handle `ContinuousLinearMap.fst`

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mfderiv_proj_derivInv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace% v) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v (e.derivInv I v u) = u.1 := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  rw [e.mk_proj_snd' hv] at D₁
  have diff : MDifferentiableAt (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v :=
    mdifferentiableAt_proj _
  have eq : e.invFun (e v) = v := by simp [e.mem_source.mpr hv]
  rw [← eq] at diff
  have := mfderiv_comp (e v) diff D₁
  have C : (TotalSpace.proj ∘ e.invFun) =ᶠ[𝓝 (e v)] Prod.fst := by
    filter_upwards [e.baseSet_prod_univ_mem_nhds hv] with ⟨x, f⟩ ⟨hx, hf⟩
    simp [hx]
  rw [C.mfderiv_eq, eq] at this
  have := congr($this u).symm
  change mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v _ = _ at this
  -- Why all this pain??
  convert! this
  ext x
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma deriv_derivInv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    (e.deriv I v) ∘L (e.derivInv I v) = .id 𝕜 _ := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  rw [e.mk_proj_snd' hv] at D₁
  have D₂ : MDifferentiableAt _ _ e v := e.mdifferentiableAt' (I := I) hv v.2
  have : e.invFun (e v) = v := by simp [e.mem_source.mpr hv]
  rw [← this] at D₂
  have comp := mfderiv_comp (e v) D₂ D₁
  rw [(comp_invFun_eventuallyEq e hv).mfderiv_eq, mfderiv_id] at comp
  symm
  convert! comp <;> rw [this]

@[simp]
lemma deriv_derivInv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace% v.proj × F) :
    e.deriv I v (e.derivInv I v u) = u :=
  show ((e.deriv I v) ∘L (e.derivInv I v)) u = u by simp [hv]

lemma bijective_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Function.Bijective (e.deriv I v) := by
   refine Function.bijective_iff_has_inverse.mpr ?_
   use e.derivInv I v
   constructor
   all_goals { intro u; simp [hv] }

lemma mdifferentiableAt_funToSec
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) {s : M → F}
    (hs : MDiffAt s x) :
    MDiffAt (T% (e.funToSec s)) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx]
  change MDiffAt (e.secToFun <| e.funToSec s) x
  have := e.secToFun_funToSec_eventuallyEq hx s
  exact hs.congr_of_eventuallyEq this

lemma mdifferentiableAt_funToSec'
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) {s : M → F}
    (hs : MDiffAt (T% s) x) :
    MDiffAt (T% (e.funToSec s)) x := by
  rw [mdifferentiableAt_total_trivial_iff] at hs
  apply mdifferentiableAt_funToSec _ hx hs

lemma mdifferentiableAt_secToFun
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) {σ : (x : M) → V x}
    (hσ : MDiffAt (T% σ) x) :
    MDiffAt (e.secToFun σ) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx] at hσ
  exact hσ

lemma mdifferentiableAt_total_secToFun
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) {σ : (x : M) → V x}
    (hσ : MDiffAt (T% σ) x) :
    MDiffAt (T% (e.secToFun σ)) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx] at hσ
  exact (mdifferentiableAt_section I _).mpr hσ

omit [MemTrivializationAtlas e] [(x : M) → Module 𝕜 (V x)] in
@[simp]
lemma mdifferentiableAt_total_funToSec_secToFun
    {x : M} (hx : x ∈ e.baseSet) {σ : (x : M) → V x} :
    MDiffAt (T% (e.funToSec <| e.secToFun σ)) x ↔ MDiffAt (T%σ) x := by
  rw [e.total_funToSec_secToFun_eventuallyEq hx σ |>.mdifferentiableAt_iff]

omit [(x : M) → Module 𝕜 (V x)] [(x : M) → TopologicalSpace (V x)]
  [FiberBundle F V] [MemTrivializationAtlas e] in
@[simp]
lemma mdifferentiableAt_secToFun_funToSec
    {x : M} (hx : x ∈ e.baseSet) {s : M → F} :
    MDiffAt (e.secToFun <| e.funToSec s) x ↔ MDiffAt s x :=
  e.secToFun_funToSec_eventuallyEq hx s |>.mdifferentiableAt_iff

lemma mfderiv_total_funToSec
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {s : M → F} {x : M} (hs : MDiffAt s x)
    (hx : x ∈ e.baseSet) :
    mfderiv% (T% (e.funToSec s)) x =
      e.derivInv I (e.funToSec s x) ∘L .prod (.id 𝕜 <| TangentSpace% x) (mfderiv% s x) := by
  -- TODO build a world where this proof is not pure pain.
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
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Bundle.vert v = Submodule.comap (e.deriv I v).toLinearMap
      (Submodule.prod ⊥ ⊤) := by
  ext x
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
      (e.deriv I (σ x) (mfderiv% T%σ x u)).2 := by
  -- TODO: Fix the erw
  --  instModuleTangentSpace 𝓘(𝕜, F) (e.secToFun (E := V) σ x)
  -- and
  --  NormedSpace.toModule
  -- are not defeq, but they are at default transparency.
  -- Does it mean the statement of this lemma is bad?
  erw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact congr(Prod.snd $(e.mfderiv_comp_section hσ u hx)).symm

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
