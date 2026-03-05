/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Delaborators

/-!
# Supporting lemmas for CovariantDerivative.Basic trivialization stuff

TODO: PR all this to appropriate places.

-/

@[expose] public section

open Bundle Filter Module Topology Set

open scoped Bundle Manifold ContDiff

namespace Bundle.Trivialization

section trivilization_topology

variable {B F Z : Type*} [TopologicalSpace B]
  [TopologicalSpace F]

section any_proj

variable [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj)
lemma baseSet_mem_nhds {x : B} (hx : x ∈ e.baseSet) : e.baseSet ∈ 𝓝 x :=
  e.open_baseSet.mem_nhds_iff.mpr hx

lemma baseSet_prod_univ_mem_nhds {v : Z}
    (hv : proj v ∈ e.baseSet) : e.baseSet ×ˢ univ ∈ 𝓝 (e v) := by
  rw [← e.mk_proj_snd' hv]
  exact prod_mem_nhds (e.baseSet_mem_nhds hv) univ_mem

lemma comp_invFun_eventuallyEq
    {v : Z} (hv : proj v ∈ e.baseSet) : e ∘ e.invFun =ᶠ[𝓝 (e v)] id := by
  filter_upwards [e.baseSet_prod_univ_mem_nhds hv] with p hp
  simp [(e.mem_target).2 hp.1]

end any_proj

section fiber_bundle
variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  (e : Trivialization F (π F E))

lemma proj_invFun_eventuallyEq
    {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    (TotalSpace.proj ∘ e.invFun) =ᶠ[𝓝 (e v)] Prod.fst := by
  filter_upwards [e.baseSet_prod_univ_mem_nhds hv] with ⟨x, f⟩ ⟨hx, hf⟩
  simp [hx]

lemma injective_symm [(x : B) → Zero (E x)]
  {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Function.Injective (e.symm v.proj) := by
  intro f f' hff'
  simpa [hv] using congr(e $hff')

lemma surjective_symm [(x : B) → Zero (E x)]
  {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Function.Surjective (e.symm v.proj) :=
  fun u ↦ ⟨(e u).2, by simp [hv]⟩

lemma bijective_symm [(x : B) → Zero (E x)]
  {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Function.Bijective (e.symm v.proj) :=
  ⟨e.injective_symm hv, e.surjective_symm hv⟩

/-- Turn sections of a fiber bundle into function into the model fiber using a trivialization. -/
def secToFun (σ : (b : B) → E b) : B → F :=
  fun b ↦ e (σ b) |>.2

lemma secToFun_congr {σ σ' : (b : B) → E b} {b : B} (h : σ b = σ' b) :
    e.secToFun σ b = e.secToFun σ' b := by
  simp [secToFun, h]

-- @[congr]
-- lemma secToFun_congr {σ σ' : (b : B) → E b} {b : B} (h : ∀ x, x = b → σ x = σ' x) :
--     e.secToFun σ b = e.secToFun σ' b := by
--   simp [secToFun, h]
--
-- example  {σ σ' : (b : B) → E b} {b : B} (h : ∀ x, x = b → σ x = σ' x) :
--     e.secToFun σ b = e.secToFun σ' b := by
--   simp? +contextual [h]
section
variable [(x : B) → Zero (E x)]

/-- Turn functions into the model fiber of a fiber bundle into sections using a trivialization. -/
noncomputable def funToSec (s : B → F) : (b : B) → E b :=
  fun b ↦ e.symm b (s b)

lemma funToSec_congr {s s' : B → F} {b : B} (h : s b = s' b) :
    e.funToSec s b = e.funToSec s' b := by
  simp [funToSec, h]

lemma totalSpace_mk'_funToSec {v : TotalSpace F E} (s : B → F) :
    (T% (e.funToSec s) v.proj) = e.symm v.proj (s v.proj) :=
  rfl

@[simp]
lemma secToFun_funToSec_eventuallyEq {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    e.secToFun (e.funToSec s) =ᶠ[𝓝 x] s := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma secToFun_funToSec {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    e.secToFun (e.funToSec s) x = s x :=
  (e.secToFun_funToSec_eventuallyEq hx s).eq_of_nhds
  -- TODO: understand why the following fails
  -- by
  --   have := e.secToFun_funToSec_eventuallyEq hx s
  --   apply?

@[simp]
lemma funToSec_secToFun_eventually_eq {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    ∀ᶠ x' in 𝓝 x, e.funToSec (e.secToFun σ) x' = σ x' := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma funToSec_secToFun {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    e.funToSec (e.secToFun σ) x = σ x :=
  (e.funToSec_secToFun_eventually_eq hx σ).self_of_nhds

section
variable (σ : (b : B) → E b) [(b : B) → TopologicalSpace (E b)] [FiberBundle F E]

set_option linter.unusedSectionVars false in
@[simp]
lemma total_funToSec_secToFun_eventuallyEq {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    T% (e.funToSec <| e.secToFun σ) =ᶠ[𝓝 x] T% σ := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma total_funToSec_secToFun_eq {x : B} (hx : x ∈ e.baseSet) (σ : (b : B) → E b) :
    T% (e.funToSec <| e.secToFun σ) x = T% σ x :=
  e.total_funToSec_secToFun_eventuallyEq hx σ |>.self_of_nhds

end

@[simp]
lemma total_secToFun_funToSeq_eventually_eq {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    ∀ᶠ x' in 𝓝 x, T% (e.secToFun <| e.funToSec s) x' = T% s x' := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  simp [secToFun, funToSec, hy]

@[simp]
lemma total_secToFun_funToSeq {x : B} (hx : x ∈ e.baseSet) (s : B → F) :
    T% (e.secToFun <| e.funToSec s) x = T% s x :=
  e.total_secToFun_funToSeq_eventually_eq hx s |>.self_of_nhds

end

variable [(b : B) → TopologicalSpace (E b)] [FiberBundle F E]

lemma preimage_baseSet_mem_nhds
    {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    TotalSpace.proj ⁻¹' e.baseSet ∈ 𝓝 v :=
  FiberBundle.continuous_proj F E |>.continuousAt <| e.baseSet_mem_nhds hv

lemma fst_comp_eventuallyEq
    {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    Prod.fst ∘ e =ᶠ[𝓝 v] (π F E) := by
  filter_upwards [preimage_baseSet_mem_nhds e hv] with y hy using e.coe_fst' hy

lemma invFun_comp_eventuallyEq
    {v : TotalSpace F E} (hv : v.proj ∈ e.baseSet) :
    e.invFun ∘ e =ᶠ[𝓝 v] id := by
  filter_upwards [e.preimage_baseSet_mem_nhds hv] with w hw
  simp [e.mem_source.mpr hw]

end fiber_bundle

section
variable {B F : Type*} {E : B → Type*} [TopologicalSpace B]
  [TopologicalSpace F] [TopologicalSpace (TotalSpace F E)]
  [(x : B) → Zero (E x)]
  (e : Trivialization F (π F E))

lemma eq_of {x : B} {v v' : E x} (hx : x ∈ e.baseSet) (hvv' : (e v).2 = (e v').2) :
    v = v' := by
  have := e.symm_proj_apply v hx
  rw [hvv'] at this
  grind [e.symm_proj_apply v' hx]

variable [(b : B) → TopologicalSpace (E b)] [FiberBundle F E]


-- FIXME super weird elaborator bug: removing the
-- omitted assumption from the variable line breaks the lemma
set_option linter.unusedSectionVars false in
lemma apply_total_eventuallyEq
    {x : B} (hx : x ∈ e.baseSet) (σ : Π x, E x) :
    e ∘ T%σ =ᶠ[𝓝 x] fun x ↦ (x, e.secToFun σ x) := by
  filter_upwards [e.baseSet_mem_nhds hx] with y hy
  ext
  · exact e.coe_coe_fst hy
  · simp [secToFun]

end

end trivilization_topology

section topological_vector_bundle

section
variable {R B F : Type*} {E : B → Type*} [Semiring R]
  [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  (e : Trivialization F (π F E))
  [AddCommMonoid F] [Module R F] [(x : B) → AddCommMonoid (E x)] [(x : B) → Module R (E x)]

lemma map_smul [Trivialization.IsLinear R e]
    {b : B} (hb : b ∈ e.baseSet) (a : R) (v : E b) :
    (e ⟨b, a • v⟩).2 = a • (e ⟨b, v⟩).2 :=
  e.linear R hb |>.map_smul a v

lemma secToFun_map_smul [Trivialization.IsLinear R e] {σ : (b : B) → E b}
    {b : B} (hb : b ∈ e.baseSet) (a : R) :
    e.secToFun (a • σ) b = a • e.secToFun σ b := by
  simp [secToFun, e.map_smul hb]

variable (R)

lemma map_add [Trivialization.IsLinear R e]
    {b : B} (hb : b ∈ e.baseSet) (v v' : E b) :
    (e ⟨b, v + v'⟩).2 = (e ⟨b, v⟩).2 + (e ⟨b, v'⟩).2 :=
  e.linear R hb |>.map_add v v'

lemma secToFun_map_add [Trivialization.IsLinear R e] (σ σ' : (b : B) → E b)
    {b : B} (hb : b ∈ e.baseSet) :
    e.secToFun (σ + σ') b = e.secToFun σ b + e.secToFun σ' b := by
  simp [secToFun, e.map_add R hb]

lemma map_zero [Trivialization.IsLinear R e]
    {b : B} (hb : b ∈ e.baseSet) :
    (e ⟨b, 0⟩).2 = 0 :=
  e.linear R hb |>.map_zero

lemma secToFun_map_zero [Trivialization.IsLinear R e] {b : B} (hb : b ∈ e.baseSet) :
    e.secToFun 0 b = 0 := by
  simp [secToFun, e.map_zero R hb]
end

section

variable (R : Type*) {B F : Type*} {E : B → Type*}
  [NontriviallyNormedField R] [(x : B) → AddCommMonoid (E x)]
  [(x : B) → Module R (E x)] [NormedAddCommGroup F]
  [NormedSpace R F] [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]
  [(x : B) → TopologicalSpace (E x)]
  [FiberBundle F E] (e : Trivialization F (π F E))

lemma symm_map_add [Trivialization.IsLinear R e] {x : B}
  (f f' : F) :
    e.symm x (f + f') = e.symm x f + e.symm x f' :=
  (e.symmL R x).map_add f f'

lemma funToSec_map_add [Trivialization.IsLinear R e] {s s' : B → F} :
    e.funToSec (s + s') = e.funToSec s + e.funToSec s' := by
  ext b
  simp [funToSec, e.symm_map_add R]

@[simp]
lemma symm_map_zero [Trivialization.IsLinear R e] {x : B} :
    e.symm x 0 = 0 :=
  (e.symmL R x).map_zero

@[simp]
lemma funToSec_map_zero [Trivialization.IsLinear R e] :
    e.funToSec (0 : B → F) = 0 := by
  ext b
  simp [funToSec, e.symm_map_zero R]

variable {R}

lemma symm_map_smul [Trivialization.IsLinear R e] {x : B} (a : R) (f : F) :
    e.symm x (a • f) = a • e.symm x f :=
  (e.symmL R x).map_smul a f

lemma funToSec_map_smul [Trivialization.IsLinear R e] (a : R) (s : B → F) :
    e.funToSec (a • s) = a • e.funToSec s := by
  ext b
  simp [funToSec, e.symm_map_smul]

end

end topological_vector_bundle

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

lemma mdifferentiableAt
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) (v : V x) :
    MDifferentiableAt (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) e v := by
  have : ⟨x, v⟩ ∈ e.source := e.coe_mem_source.mpr hx
  have foo := e.contMDiffOn (IB := I) (n := 1) v this
  have := foo.contMDiffAt (e.open_source.mem_nhds this)
  exact this.mdifferentiableAt zero_ne_one.symm

lemma mdifferentiableAt_invFun
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) (f : F) :
    MDifferentiableAt (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) e.invFun (x, f) := by
  have : ⟨x, f⟩ ∈ e.target := e.mk_mem_target.mpr hx
  have foo := e.contMDiffOn_symm (IB := I) (n := 1) _ this
  have := foo.contMDiffAt (e.open_target.mem_nhds this)
  exact this.mdifferentiableAt zero_ne_one.symm

-- Note: The definition below (ab)uses definitional
-- equality of `TangentSpace (I.prod 𝓘(𝕜, F)) (↑t v)`
-- which is $T_{t(v)} (M × F)$ and `TM v.proj × F`
-- which is $T_{π(v)} M × F$.
variable (I) in
noncomputable
def deriv (v : TotalSpace F V) :
    TangentSpace (I.prod 𝓘(𝕜, F)) v →L[𝕜] TangentSpace I v.proj × F :=
  mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) e v

variable (I) in
noncomputable
def derivInv (v : TotalSpace F V) :
    TangentSpace I v.proj × F →L[𝕜] TangentSpace (I.prod 𝓘(𝕜, F)) v :=
  mfderiv (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) e.invFun (e v)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma derivInv_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    (e.derivInv I v) ∘L (e.deriv I v) = .id 𝕜 _ := by
  have D₁ := e.mdifferentiableAt_invFun (I := I) hv (e v).2
  have D₂ : MDifferentiableAt _ _ e v := e.mdifferentiableAt (I := I) hv v.2
  have D1' := D₁
  simp only [PartialEquiv.invFun_as_coe, OpenPartialHomeomorph.coe_coe_symm] at D1'
  rw [e.mk_proj_snd' hv] at D₁
  have comp := mfderiv_comp v D₁ D₂
  rw [(invFun_comp_eventuallyEq e hv).mfderiv_eq, mfderiv_id] at comp
  simp [deriv, derivInv, comp]

@[simp]
lemma derivInv_deriv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    (e.derivInv I v (e.deriv I v u)) = u :=
  show ((e.derivInv I v) ∘L (e.deriv I v)) u = u by simp [hv]

@[simp]
lemma mfderiv_proj_fst_deriv
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    mfderiv (I.prod 𝓘(𝕜, F)) I TotalSpace.proj v u = (e.deriv I v u).1 := by
  have := e.fst_comp_eventuallyEq hv
  rw [← this.mfderiv_eq, mfderiv_comp v mdifferentiableAt_fst (e.mdifferentiableAt (I := I) hv v.2)]
  simp
  rfl -- TODO: understand why `simp` does not handle `ContinuousLinearMap.fst`

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mfderiv_proj_derivInv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
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
  convert this
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
  have D₂ : MDifferentiableAt _ _ e v := e.mdifferentiableAt (I := I) hv v.2
  have : e.invFun (e v) = v := by simp [e.mem_source.mpr hv]
  rw [← this] at D₂
  have comp := mfderiv_comp (e v) D₂ D₁
  rw [(comp_invFun_eventuallyEq e hv).mfderiv_eq, mfderiv_id] at comp
  symm
  convert comp <;> rw [this]

@[simp]
lemma deriv_derivInv_apply
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet)
    (u : TangentSpace I v.proj × F) :
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

lemma mdifferentiableAt_secToFun
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {x : M} (hx : x ∈ e.baseSet) {σ : (x : M) → V x}
    (hσ : MDiffAt (T% σ) x) :
    MDiffAt (e.secToFun σ) x := by
  rw [e.mdifferentiableAt_section_iff (IB := I) _ hx] at hσ
  exact hσ

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

lemma mfderiv_total_funToSec_fst_deriv {s : M → F}
    (v : TotalSpace F V) (w : TangentSpace (I.prod 𝓘(𝕜, F)) v) :
    mfderiv% (T% (e.funToSec s)) v.proj (e.deriv I v w).1 = w := by
  sorry

noncomputable def _root_.Bundle.vert (v : TotalSpace F V) :
    Submodule 𝕜 (TangentSpace (I.prod 𝓘(𝕜, F)) v) :=
  (mfderiv (I.prod 𝓘(𝕜, F)) I Bundle.TotalSpace.proj v).ker

lemma comap_vert
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {v : TotalSpace F V} (hv : v.proj ∈ e.baseSet) :
    Bundle.vert v = Submodule.comap (e.deriv I v).toLinearMap
      (Submodule.prod ⊥ ⊤) := by
  ext x
  have : Prod.fst ∘ e =ᶠ[𝓝 v] TotalSpace.proj := e.fst_comp_eventuallyEq hv
  unfold vert
  rw [← this.mfderiv_eq]
  have mdiffe : MDifferentiableAt (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) e v :=
    e.mdifferentiableAt hv _
  rw [mfderiv_comp v mdifferentiableAt_fst mdiffe]
  simp
  rfl

lemma mfderiv_comp_section
    [VectorBundle 𝕜 F V] [ContMDiffVectorBundle 1 F V I]
    {σ : Π x : M, V x} {x : M} (hσ : MDiffAt T%σ x)
    (u : TangentSpace I x) (hx : x ∈ e.baseSet) :
    (e.deriv I (σ x)).toLinearMap ((mfderiv% T%σ x) u) = (u, mfderiv% (e.secToFun σ) x u) := by
  have mdiffe : MDifferentiableAt (I.prod 𝓘(𝕜, F)) (I.prod 𝓘(𝕜, F)) e (σ x) :=
    e.mdifferentiableAt hx _
  have : mfderiv% (e ∘ T%σ) x = (e.deriv I (σ x)) ∘L (mfderiv% T%σ x) :=
    mfderiv_comp x mdiffe hσ
  have : mfderiv% (e ∘ T%σ) x u = e.deriv I (σ x) ((mfderiv% T%σ x) u) := by
    rw [this]
    rfl
  erw [← this]
  rw [(e.apply_total_eventuallyEq hx _).mfderiv_eq]
  erw [mfderiv_prodMk, mfderiv_id]
  · -- TODO make sure the `change` below isn’t needed.
    -- Uncommenting the next lines is meant to help understanding the issue.
    -- have : ((ContinuousLinearMap.id 𝕜 (TangentSpace I x)).prod
    --    (mfderiv I 𝓘(𝕜, F) (e.secToFun σ) x)) u =
    --    (u, (mfderiv I 𝓘(𝕜, F) (e.secToFun σ) x) u) := sorry
    -- with_reducible exact this
    change (ContinuousLinearMap.id _ _).prod _ _ = _
    simp
  · apply mdifferentiableAt_id
  · exact (e.mdifferentiableAt_section_iff I σ hx).mp hσ

@[simp]
lemma _root_.mdifferentiableAt_total_trivial_iff {s : M → F} {x : M} :
    MDiffAt (T% s) x ↔ MDiffAt s x := by
  rw [mdifferentiableAt_section I]
  simp

@[simp]
lemma _root_.mdifferentiableAt_section_trivial_iff {σ : (x : M) → Trivial M F x} {x : M} :
    MDiffAt (T% σ) x ↔ MDifferentiableAt I 𝓘(𝕜, F) σ x := by
  rw [mdifferentiableAt_section I]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

@[simp]
theorem Bundle.Trivial.mdifferentiableAt_iff (σ : (x : E) → Trivial E E' x) (e : E) :
    MDiffAt (T% σ) e ↔ DifferentiableAt 𝕜 σ e := by
  simp [mdifferentiableAt_totalSpace, mdifferentiableAt_iff_differentiableAt]

end to_trivialization

end Bundle.Trivialization
