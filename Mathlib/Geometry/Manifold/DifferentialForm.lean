module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContinuousAlternatingMap

-- Let `M` be a `C^(k+1)` manifold, so its tangent bundle is a C^n manifold.

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

@[expose] public noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (n : ℕ∞ω)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

variable {F n V}

-- move to ContMDiffSection, TODO ensure there are no diamonds!

instance : SMul (ContMDiffMap I 𝓘(𝕜) M 𝕜 n) Cₛ^n⟮I; F, V⟯ :=
  ⟨fun f s ↦ ⟨f.1 • s, f.2.smul_section s.contMDiff⟩⟩

variable {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

#check' writtenInExtChartAt
lemma writtenInExtChartAt_zero [Zero N]{f : M → N} {x : M} :
    writtenInExtChartAt I J x (0 : M → N) = 0 := by
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend, Pi.zero_apply,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe,
    OpenPartialHomeomorph.coe_toPartialHomeomorph, PartialEquiv.coe_trans_symm,
    PartialHomeomorph.coe_toPartialEquiv_symm, OpenPartialHomeomorph.coe_toPartialHomeomorph_symm,
    ModelWithCorners.toPartialEquiv_coe_symm, Pi.zero_comp, Pi.comp_zero, comp_apply, const_eq_zero]
  sorry

end

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {m n : ℕ} {k l : ℕ∞ω}
  [IsManifold IM 1 M]

#synth VectorBundle 𝕜 EM (fun (x : M) ↦ TangentSpace IM x)

#check TangentBundle.contMDiffVectorBundle (I := IM) (n := k)
--#synth ContMDiffVectorBundle k EM (fun (x : M) ↦ TangentSpace IM x)

#check EM [⋀^Fin m]→L[𝕜] 𝕜

#check (fun x ↦ TangentSpace IM x [⋀^(Fin m)]→L[𝕜] Bundle.Trivial M 𝕜 x)


variable (IM M n k) in
/-- `DifferentialForm IM M n k` is a differential `n`-form on the `C^k` manifold `M` (with model `IM`) -/
@[implicit_reducible] -- TODO: is this correct?
def Manifold.DifferentialForm :=
  ContMDiffSection IM (EM [⋀^Fin n]→L[𝕜] 𝕜) k
  (fun x ↦ TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x)

namespace Manifold.DifferentialForm

section setup

@[macro_inline]
instance : DFunLike (DifferentialForm IM M n k) M (fun x ↦ TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x) where
  coe := ContMDiffSection.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr

protected theorem contMDiff (σ : DifferentialForm IM M n k) :
    -- TODO: elaborators don't work well yet!
    ContMDiff IM (IM.prod 𝓘(𝕜, (EM [⋀^Fin n]→L[𝕜] 𝕜))) k
      (fun x ↦ TotalSpace.mk' (EM [⋀^Fin n]→L[𝕜] 𝕜) x (σ x)) :=
  ContMDiffSection.contMDiff σ

protected theorem mdifferentiableWithinAt (σ : DifferentialForm IM M n k) {s : Set M} {x : M} (hk : k ≠ 0) :
    -- TODO: elaborators don't work well yet!
    MDifferentiableWithinAt IM (IM.prod 𝓘(𝕜, (EM [⋀^Fin n]→L[𝕜] 𝕜)))
      (fun x ↦ TotalSpace.mk' (EM [⋀^Fin n]→L[𝕜] 𝕜) x (σ x)) s x :=
  σ.2.mdifferentiableWithinAt hk

protected theorem mdifferentiable (σ : DifferentialForm IM M n k) (hk : k ≠ 0) :
    -- TODO: elaborators don't work well yet!
    MDifferentiable IM (IM.prod 𝓘(𝕜, (EM [⋀^Fin n]→L[𝕜] 𝕜)))
      (fun x ↦ TotalSpace.mk' (EM [⋀^Fin n]→L[𝕜] 𝕜) x (σ x)) :=
  σ.2.mdifferentiable hk

theorem coe_inj ⦃s t : DifferentialForm IM M n k⦄ (h : (s : ∀ x, TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x) = t) :
    s = t :=
  DFunLike.ext' h

theorem coe_injective : Injective ((↑) : DifferentialForm IM M n k → ∀ x, TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x) :=
  coe_inj

variable {σ σ' : DifferentialForm IM M n k}

@[ext]
theorem ext (h : ∀ x, σ x = σ' x) : σ = σ' := DFunLike.ext _ _ h

instance : Zero (DifferentialForm IM M n k) := inferInstanceAs <| Zero <|
  ContMDiffSection IM (EM [⋀^Fin n]→L[𝕜] 𝕜) k
    (fun x ↦ TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x)

@[simp]
theorem coe_zero : ⇑(0 : DifferentialForm IM M n k) = 0 :=
  rfl

instance : Add (DifferentialForm IM M n k) := inferInstanceAs <| Add <|
  ContMDiffSection IM (EM [⋀^Fin n]→L[𝕜] 𝕜) k
    (fun x ↦ TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x)

@[simp]
theorem coe_add (σ σ' : DifferentialForm IM M n k) : ⇑(σ + σ') = ⇑σ + σ' :=
  rfl

instance : Sub (DifferentialForm IM M n k) := inferInstanceAs <| Sub <|
  ContMDiffSection IM (EM [⋀^Fin n]→L[𝕜] 𝕜) k
    (fun x ↦ TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x)

@[simp]
theorem coe_sub (σ σ' : DifferentialForm IM M n k) : ⇑(σ - σ') = σ - σ' :=
  rfl

instance : Neg (DifferentialForm IM M n k) := inferInstanceAs <| Neg <|
  ContMDiffSection IM (EM [⋀^Fin n]→L[𝕜] 𝕜) k
    (fun x ↦ TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x)

@[simp]
theorem coe_neg (σ : DifferentialForm IM M n k) : ⇑(-σ : DifferentialForm IM M n k) = -σ :=
  rfl

instance instNSMul : SMul ℕ (DifferentialForm IM M n k) :=
  ⟨nsmulRec⟩

@[simp]
theorem coe_nsmul (σ : DifferentialForm IM M n k) (a : ℕ) :
    ⇑(a • σ : DifferentialForm IM M n k) = a • ⇑σ :=
  ContMDiffSection.coe_nsmul σ a

instance instZSMul : SMul ℤ (DifferentialForm IM M n k) :=
  ⟨zsmulRec⟩

@[simp]
theorem coe_zsmul (σ : DifferentialForm IM M n k) (z : ℤ) :
    ⇑(z • σ : DifferentialForm IM M n k) = z • ⇑σ :=
  ContMDiffSection.coe_zsmul σ z

instance : AddCommGroup (DifferentialForm IM M n k) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance instSMul : SMul 𝕜 (DifferentialForm IM M n k) :=
  ⟨fun c s ↦ ⟨c • ⇑s, s.contMDiff.const_smul_section⟩⟩

@[simp]
theorem coe_smul_const (r : 𝕜) (σ : DifferentialForm IM M n k) :
    ⇑(r • σ : DifferentialForm IM M n k) = r • ⇑σ :=
  rfl

variable (IM M n k) in
/-- The additive morphism from `C^n` sections to dependent maps. -/
def coeAddHom :
    DifferentialForm IM M n k →+ ∀ x, TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeAddHom_apply (σ : DifferentialForm IM M n k) : coeAddHom IM M n k σ = σ := rfl

instance instModule : Module 𝕜 (DifferentialForm IM M n k) :=
  coe_injective.module 𝕜 (coeAddHom IM M n k) coe_smul_const

instance : SMul (ContMDiffMap IM 𝓘(𝕜) M 𝕜 k) (DifferentialForm IM M n k) :=
  inferInstanceAs <| SMul (ContMDiffMap IM 𝓘(𝕜) M 𝕜 k) <|
    ContMDiffSection IM (EM [⋀^Fin n]→L[𝕜] 𝕜) k
      (fun x ↦ TangentSpace IM x [⋀^(Fin n)]→L[𝕜] Bundle.Trivial M 𝕜 x)

--#check AddCommGroupWithOne
-- #check Semiring
-- instance : Module (ContMDiffMap IM 𝓘(𝕜) M 𝕜 k) (DifferentialForm IM M n k) :=
--   coe_injective.module 𝕜 (coeAddHom IM M n k) coe_smul_const

-- statement doesn't typecheck yet...
-- @[simp]
-- --theorem coe_smul {f : M → 𝕜} (hf : CMDiff k f) (s : DifferentialForm IM M n k) : ⇑(⟨f, hf⟩ • s : DifferentialForm IM M n k) = r • ⇑s :=
-- theorem coe_smul (f: ContMDiffMap IM 𝓘(𝕜) M 𝕜 k) (s : DifferentialForm IM M n k) : ⇑(f • s : DifferentialForm IM M n k) = f • ⇑s :=
--   rfl

end setup

section mextDeriv

variable [IsManifold IM (k + 1) M]

local instance : ContMDiffVectorBundle k EM (TangentSpace (M := M) IM) IM :=
  TangentBundle.contMDiffVectorBundle (I := IM) (n := k)

variable [CharZero 𝕜]

local instance : ContMDiffVectorBundle k (EM [⋀^Fin m]→L[𝕜] 𝕜)
    (fun b ↦ TangentSpace IM b [⋀^Fin m]→L[𝕜] Trivial M 𝕜 b) IM :=
  ContMDiffVectorBundle.continuousAlternatingMap (ι := Fin m) (n := k)
    (E₁ := (fun (x : M) ↦ TangentSpace IM x)) /-(F₁ := EM)-/ (E₂ := Trivial M 𝕜) (IB := IM) --(F₂ := 𝕜)

local instance temp : IsManifold IM k M := IsManifold.of_le (by simp : k ≤ k + 1)

/- Definition of the manifold exterior derivative of differential form within a set:
this definition is on the level of bare sections, i.e. assuming no regularity at all.
This ensures the exterior derivative `dα` of an `l`-form is the same as the exterior derivatives
of `α` considered as a `k`-form for `k ≤ l`. XXX is this important? don't know!
-/
def mextDerivWithinAux
    (α : ∀ x, TangentSpace IM x [⋀^(Fin m)]→L[𝕜] Bundle.Trivial M 𝕜 x) (s : Set M) (x : M) :
    TangentSpace IM x [⋀^Fin (m + 1)]→L[𝕜] Trivial M 𝕜 x :=
  (extDerivWithin (fun x' ↦ (writtenInExtChartAt IM (IM.prod 𝓘(𝕜, (EM [⋀^Fin m]→L[𝕜] 𝕜))) x
      (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α y))) x' |>.2)
    ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x)

lemma mextDerivWithinAux_add {α α' : ∀ x, TangentSpace IM x [⋀^(Fin m)]→L[𝕜] Bundle.Trivial M 𝕜 x}
    {s : Set M} {x : M} (hsx : UniqueMDiffWithinAt IM s x)
    (hα : MDifferentiableWithinAt IM (IM.prod 𝓘(𝕜, EM [⋀^Fin m]→L[𝕜] 𝕜))
        (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α y)) s x)
    (hα' : MDifferentiableWithinAt IM (IM.prod 𝓘(𝕜, EM [⋀^Fin m]→L[𝕜] 𝕜))
        (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α' y)) s x) :
    mextDerivWithinAux (α + α') s x = mextDerivWithinAux α s x + mextDerivWithinAux α' s x := by
  unfold mextDerivWithinAux
  --simp? says
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend, Pi.add_apply,
    modelWithCorners_prod_toPartialEquiv, modelWithCornersSelf_partialEquiv, PartialEquiv.coe_trans,
    PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe, PartialEquiv.refl_coe, id_eq,
    PartialHomeomorph.toFun_eq_coe, OpenPartialHomeomorph.coe_toPartialHomeomorph,
    PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_toPartialEquiv_symm,
    OpenPartialHomeomorph.coe_toPartialHomeomorph_symm, ModelWithCorners.toPartialEquiv_coe_symm,
    comp_apply, chartAt_continuousAlternatingMap, ContinuousAlternatingMap.inCoordinates_add]
  rw [extDerivWithin_fun_add]
  · rfl
  · exact hsx
  · replace hα := hα.2
    sorry -- morally done
     -- differentiability requirement
  · replace hα' := hα'.2
    sorry -- differentiability requirement

lemma mextDerivWithinAux_neg (α : ∀ x, TangentSpace IM x [⋀^(Fin m)]→L[𝕜] Bundle.Trivial M 𝕜 x)
    {s : Set M} {x : M} (hsx : UniqueMDiffWithinAt IM s x) :
    mextDerivWithinAux (-α) s x = -mextDerivWithinAux α s x := by
  unfold mextDerivWithinAux
  simp
  -- TODO: find out why the side condition cannot be passed. make ω explicit?
  rw [extDerivWithin_fun_neg]
  rfl
  exact hsx

lemma mextDerivWithinAux_sub {α α' : ∀ x, TangentSpace IM x [⋀^(Fin m)]→L[𝕜] Bundle.Trivial M 𝕜 x}
    {s : Set M} {x : M} (hsx : UniqueMDiffWithinAt IM s x)
    (hα : MDifferentiableWithinAt IM (IM.prod 𝓘(𝕜, EM [⋀^Fin m]→L[𝕜] 𝕜))
        (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α y)) s x)
    (hα' : MDifferentiableWithinAt IM (IM.prod 𝓘(𝕜, EM [⋀^Fin m]→L[𝕜] 𝕜))
        (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α' y)) s x) :
    mextDerivWithinAux (α - α') s x = mextDerivWithinAux α s x - mextDerivWithinAux α' s x := by
  rw [sub_eq_neg_add]
  rw [mextDerivWithinAux_add hsx, mextDerivWithinAux_neg α' hsx]
  · abel
  -- this would be easier for bundled sections!
  have h : MDifferentiableWithinAt IM (IM.prod 𝓘(𝕜, EM [⋀^Fin m]→L[𝕜] 𝕜))
        (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (-α' y)) s x := by
    -- convert hα'.neg
    sorry
  exacts [h, hα]

omit [CharZero 𝕜] in
@[simp]
lemma mextDerivWithinAux_zero (s : Set M) (x : M) :
    mextDerivWithinAux
      (0 : ∀ x, TangentSpace IM x [⋀^(Fin m)]→L[𝕜] Bundle.Trivial M 𝕜 x) s x = 0 := by
  unfold mextDerivWithinAux
  ext
  -- TODO: why does extDeriv_zero not trigger?
  simp [extDerivWithin]
  rfl -- different zeroes.. small defeq abuse

variable (α : DifferentialForm IM M n k)

/- Definition of the manifold exterior derivative of differential form within a set -/
def mextDerivWithin (α : DifferentialForm IM M n k) (s : Set M) : DifferentialForm IM M (n + 1) k :=
  ⟨mextDerivWithinAux α.1 s, by
    have hα := α.2
    -- TODO prove: if α is C^k, so is its exterior derivative
    sorry⟩

-- lemma mextDerivWithin_def (s : Set M) (x : M) :
--     letI := TotalSpace.isManifold (EM [⋀^Fin m]→L[𝕜] 𝕜) fun y ↦ TangentSpace IM y [⋀^Fin m]→L[𝕜] Trivial M 𝕜 y
--     mextDerivWithin α s x =
--       (extDerivWithin (fun x' ↦ (writtenInExtChartAt IM (IM.prod 𝓘(𝕜, (EM [⋀^Fin m]→L[𝕜] 𝕜))) x
--         (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α y))) x' |>.2)
--       ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x) :=
--   rfl

-- strange: putting `mextDerivWithinAux α s x` is fine;
-- inlining its definition fails instance synthesis?
omit [IsManifold IM (k + 1) M] [CharZero 𝕜] in
lemma mextDerivWithin_apply (s : Set M) (x : M) :
    mextDerivWithin α s x = mextDerivWithinAux α s x :=
  -- TODO: including the term below fails; why??
  -- (extDerivWithin (fun x' ↦ (writtenInExtChartAt IM (IM.prod 𝓘(𝕜, (EM [⋀^Fin m]→L[𝕜] 𝕜))) x
  --     (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α y))) x' |>.2)
  --   ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x) :=
  rfl

def mextDeriv (α : DifferentialForm IM M n k) : DifferentialForm IM M (n + 1) k :=
    mextDerivWithin α univ

omit [IsManifold IM (k + 1) M] [CharZero 𝕜] in
@[simp]
theorem mextDerivWithin_univ : mextDerivWithin α univ = mextDeriv α :=
  rfl

set_option linter.unusedSectionVars false in -- linter false positive
lemma mextDerivWithin_add (σ σ' : DifferentialForm IM M n k)
    {s : Set M} {x : M} (hsx : UniqueMDiffAt[s] x) (hk : k ≠ 0) :
    mextDerivWithin (σ + σ') s x = mextDerivWithin σ s x + mextDerivWithin σ' s x := by
  ext v
  simp [mextDerivWithin_apply,
    mextDerivWithinAux_add hsx (σ.mdifferentiableWithinAt hk) (σ'.mdifferentiableWithinAt hk)]

@[simp]
lemma mextDeriv_add (σ σ' : DifferentialForm IM M n k) (hk : k ≠ 0) :
    mextDeriv (σ + σ') = mextDeriv σ + mextDeriv σ' := by
  simp_rw [← mextDerivWithin_univ]
  ext v
  rw [mextDerivWithin_add σ σ' (uniqueMDiffWithinAt_univ _) hk]
  exact DFunLike.congr_fun rfl _

set_option linter.unusedSectionVars false in -- linter false positive
lemma mextDerivWithin_sub (σ σ' : DifferentialForm IM M n k)
    {s : Set M} {x : M} (hsx : UniqueMDiffAt[s] x) (hk : k ≠ 0) :
    mextDerivWithin (σ - σ') s x = mextDerivWithin σ s x - mextDerivWithin σ' s x := by
  ext v
  simp [mextDerivWithin_apply,
    mextDerivWithinAux_sub hsx (σ.mdifferentiableWithinAt hk) (σ'.mdifferentiableWithinAt hk)]

-- TODO: have applied versions of these, or fun_add, or something? the ext dance again is annoying!
@[simp]
lemma mextDeriv_sub (σ σ' : DifferentialForm IM M n k) (hk : k ≠ 0) :
    mextDeriv (σ - σ') = mextDeriv σ - mextDeriv σ' := by
  ext v
  simp [← mextDerivWithin_univ, mextDerivWithin_sub σ σ' (uniqueMDiffWithinAt_univ _) hk]

set_option linter.unusedSectionVars false in -- linter false positive
lemma mextDerivWithin_neg (σ : DifferentialForm IM M n k)
    {s : Set M} {x : M} (hsx : UniqueMDiffAt[s] x) :
    mextDerivWithin (- σ) s x = - mextDerivWithin σ s x := by
  ext v
  simp [mextDerivWithin_apply, mextDerivWithinAux_neg σ hsx]

@[simp]
lemma mextDeriv_neg (σ : DifferentialForm IM M n k) : mextDeriv (-σ) = - mextDeriv σ := by
  ext v
  simp [← mextDerivWithin_univ, mextDerivWithin_neg σ (uniqueMDiffWithinAt_univ _)]

set_option linter.unusedSectionVars false in -- linter false positive
@[simp]
lemma mextDerivWithin_zero (s : Set M) (x : M) :
    mextDerivWithin (0 : DifferentialForm IM M n k) s x =
      (0 : TangentSpace IM x [⋀^Fin (n + 1)]→L[𝕜] Trivial M 𝕜 x) := by
  ext v
  simp [mextDerivWithin_apply]

@[simp]
lemma mextDeriv_zero : mextDeriv (0 : DifferentialForm IM M n k) =
      (0 : DifferentialForm IM M (n + 1) k) := by
  ext v
  simp [← mextDerivWithin_univ]

-- -- New attempt: drop the intermediate definition
-- -- Sadly, typechecking the `writtenInExtChartAt` part fails...
-- /- Definition of the manifold exterior derivative of differential form within a set -/
-- def mextDerivWithin2 (α : DifferentialForm IM M n k) (s : Set M) : DifferentialForm IM M (n + 1) k :=
--   ⟨fun x ↦ (extDerivWithin (fun x' ↦ (writtenInExtChartAt IM (IM.prod 𝓘(𝕜, (EM [⋀^Fin m]→L[𝕜] 𝕜))) x
--       (fun y ↦ TotalSpace.mk' (EM [⋀^Fin m]→L[𝕜] 𝕜) y (α.1 y))) x' |>.2)
--     ((extChartAt IM x).symm ⁻¹' s ∩ range IM)) (extChartAt IM x x), by
--     have hα := α.2
--     -- TODO prove: if α is C^k, so is its exterior derivative
--     sorry⟩

lemma mextDeriv_smul_const (c : 𝕜) (σ : DifferentialForm IM M n k) :
    mextDeriv (c • σ) = c • mextDeriv σ := sorry

-- follows from the product rule...
lemma mextDeriv_smul (c : ContMDiffMap IM 𝓘(𝕜) M 𝕜 k) (σ : DifferentialForm IM M n k) :
  mextDeriv (c • σ) = c • mextDeriv σ := sorry

lemma mextDeriv_mextDeriv (σ : DifferentialForm IM M n k) : mextDeriv (mextDeriv σ) = 0 := sorry

end mextDeriv

variable [CharZero 𝕜] [IsManifold IM (k + 1) M]

-- This would be easy to state now. Probably don't want it, though.
def IsClosed (σ : DifferentialForm IM M n k) : Prop := mextDeriv σ = 0
def IsExact (σ : DifferentialForm IM M (n + 1) k) : Prop := ∃ τ, mextDeriv τ = σ

lemma foo (σ : DifferentialForm IM M (n + 1) k) (hσ : IsExact σ) : IsClosed σ := by
  obtain ⟨τ, rfl⟩ := hσ
  apply mextDeriv_mextDeriv

end Manifold.DifferentialForm
