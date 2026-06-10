/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import Mathlib.Geometry.Manifold.Algebra.ExpLie
import Mathlib.Geometry.Manifold.Algebra.PrincipalGBundlePrelude

/-!
# Principal Bundles (Abstract formulation)

A smooth principal G-bundle over a manifold B is a smooth manifold P equipped with:
1. A smooth right G-action on P
2. A smooth projection `proj : P → B` that is G-invariant
3. G-equivariant local trivializations

This file develops the abstract theory for an arbitrary total space `P`, replacing the
earlier formulation using `TotalSpace G E`.

Transitivity of the G-action on fibers is a consequence of equivariance and is proved
as a separate proposition.

## Main definitions

* `IsPrincipalBundle`: A smooth principal G-bundle with an arbitrary total space P
* `ConnectionForm`: A g-valued 1-form on P satisfying the two connection axioms

## Main results

* `IsPrincipalBundle.is_transitive`: The G-action is transitive on each fiber
* `yangMills_transformation`: The transformation law for Yang-Mills fields

## References

* Tu, *Differential Geometry: Connections, Curvature, and Characteristic Classes*,
  Springer, 2017, §27
* Bleecker, *Gauge Theory and Variational Principles*, §1.2
-/

open Bundle RightActions
open Set Bundle ContDiff Manifold Trivialization

noncomputable section Warmup

/-!
## Warmup: Sections, forms, and their pairing
-/

variable
  {B : Type*} [TopologicalSpace B]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E]
  [VectorBundle ℝ F E]

/-- A vector field is a smooth section of the tangent bundle -/
def VectorField := Cₛ^∞⟮IB; F, E⟯

/-- A 1-form is a smooth section of the dual bundle -/
def OneForm := Cₛ^∞⟮IB; F →L[ℝ] ℝ, fun b ↦ E b →L[ℝ] ℝ⟯

/-- A 2-form is a smooth section of the ... bundle -/
def TwoForm := Cₛ^∞⟮IB; F →L[ℝ] F →L[ℝ] ℝ, fun b ↦ E b →L[ℝ] E b →L[ℝ] ℝ⟯

def apply
  (w : OneForm (E := E) (F := F) (IB := IB))
  (X : VectorField (IB := IB) (E := E) (F := F)) (b : B) : ℝ :=
    w.toFun b (X.toFun b)

lemma apply_smooth
  (w : OneForm (E := E) (F := F) (IB := IB))
  (X : VectorField (IB := IB) (E := E) (F := F)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, ℝ)) ∞
      (fun b ↦ TotalSpace.mk' ℝ b (w.toFun b (X.toFun b))) :=
  (ContMDiffSection.contMDiff w).clm_bundle_apply
      (ContMDiffSection.contMDiff X)

lemma apply_smooth'
  (w : OneForm (E := E) (F := F) (IB := IB))
  (X : VectorField (IB := IB) (E := E) (F := F)) :
  ContMDiff IB 𝓘(ℝ, ℝ) ∞ (apply w X) := by
  intro b
  have h := (apply_smooth w X).contMDiffAt (x := b)
  rw [Trivialization.contMDiffAt_iff (e := trivializationAt ℝ (Trivial B ℝ) b) (by simp)] at h
  simpa using h.2

lemma apply_smooth''
  (w : OneForm (E := E) (F := F) (IB := IB))
  (X : VectorField (IB := IB) (E := E) (F := F)) :
  ContMDiff IB 𝓘(ℝ, ℝ) ∞ (fun b ↦ w.toFun b (X.toFun b)) := by
  intro b
  have h1 := (apply_smooth w X).contMDiffAt (x := b)
  have h2 :
    TotalSpace.mk' ℝ b ((w.toFun b) (X.toFun b)) ∈ (trivializationAt ℝ (Trivial B ℝ) b).source :=
      by simp
  have h3 := Trivialization.contMDiffAt_iff
             (n := ∞) (IB := IB) (IM := IB)
             (f := fun b ↦ TotalSpace.mk' ℝ b ((w.toFun b) (X.toFun b)))
             (e := trivializationAt ℝ (Trivial B ℝ) b) h2
  rw [h3] at h1
  have h6 : ContMDiffAt IB 𝓘(ℝ, ℝ) ∞
    (fun x ↦ ((trivializationAt ℝ (Trivial B ℝ) b)
              ((fun c ↦ TotalSpace.mk' ℝ c ((w.toFun c) (X.toFun c))) x)).2) b := h1.2
  have h4 : ∀ x,
    ((trivializationAt ℝ (Trivial B ℝ) b) (TotalSpace.mk' ℝ x ((w.toFun x) (X.toFun x)))).2 =
    (w.toFun x) (X.toFun x) := fun x ↦ by
      simp [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]
  have h5 : ContMDiffWithinAt IB 𝓘(ℝ, ℝ) ∞ (fun x ↦ (w.toFun x) (X.toFun x)) univ b :=
  ContMDiffWithinAt.congr h1.2 (fun x _ ↦ (h4 x).symm) (h4 b).symm
  exact h5

end Warmup

variable
  {B : Type*} [TopologicalSpace B]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]
  [IsManifold IB ∞ B]
  {G : Type*} [TopologicalSpace G] [T2Space G]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [Group G]
  [LieGroup IG ∞ G]
  [BoundarylessManifold IG G]
  {P : Type*}
  [TopologicalSpace P]
  [ChartedSpace (ModelProd HB HG) P]
  [IsManifold (IB.prod IG) ∞ P]
  [MulAction (MulOpposite G) P]
  [SmoothRightGAction ∞ IG (IB.prod IG) G P]
  {proj : P → B}

instance [LieGroup IG ∞ G] : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)

class IsPrincipalBundle
    {B : Type*} [TopologicalSpace B]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    {HB : Type*} [TopologicalSpace HB]
    (IB : ModelWithCorners ℝ EB HB) [ChartedSpace HB B]
    (G : Type*) [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [Group G]
    (P : Type*) [TopologicalSpace P]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    {HP : Type*} [TopologicalSpace HP]
    (IP : ModelWithCorners ℝ EP HP) [ChartedSpace HP P]
    [MulAction (MulOpposite G) P]
    (proj : P → B) where
  is_free : ∀ (p : P), MulAction.stabilizer (MulOpposite G) p = ⊥
  respects_fibres : ∀ (p : P) (g : G), proj (p <• g) = proj p
  smooth_proj : ContMDiff IP IB ∞ proj
  localTriv : P → Trivialization G proj
  mem_baseSet_localTriv : ∀ p, proj p ∈ (localTriv p).baseSet
  equivariant_localTriv : ∀ (p : P) (g : G),
    (localTriv p) (p <• g) = ⟨proj p, ((localTriv p) p).2 * g⟩

variable [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]

omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
theorem IsPrincipalBundle.is_transitive
    [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]
    (b : B) (p q : P)
    (hp : proj p = b) (hq : proj q = b) :
    q ∈ MulAction.orbit (MulOpposite G) p := by
  set φ := hPB.localTriv p
  have hmem_p : proj p ∈ φ.baseSet := hPB.mem_baseSet_localTriv p
  set g := (φ p).2⁻¹ * (φ q).2
  refine ⟨MulOpposite.op g, φ.injOn ?_ ?_ ?_⟩
  · rw [Trivialization.mem_source]
    rw [hPB.respects_fibres p g]
    exact hmem_p
  · rw [φ.mem_source]
    rw [hq]; rw [hp] at hmem_p; exact hmem_p
  · have heq := hPB.equivariant_localTriv p g
    simp only [Trivialization.coe_coe] at heq ⊢
    rw [heq, show g = (φ p).2⁻¹ * (φ q).2 from rfl, mul_inv_cancel_left]
    have hq_src : q ∈ φ.source := by
      rw [φ.mem_source, hq]; rw [hp] at hmem_p; exact hmem_p
    rw [show proj p = proj q from by rw [hp, hq], ← φ.coe_fst hq_src, Prod.mk.eta]

/-- The fundamental vector field `A#` associated to a Lie algebra element `A ∈ 𝔤` and a
point `p` in the total space of a principal `G`-bundle. -/
noncomputable def fundamentalVectorField
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    (A : GroupLieAlgebra IG G)
    (p : P) :
    TangentSpace (IB.prod IG) p :=
  haveI : LieGroup IG (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
  mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
    (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A))
    (0 : ℝ) 1

/-- The adjoint representation `Ad_g : 𝔤 → 𝔤` of `g : G`. -/
noncomputable def Ad (g : G) : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h : G ↦ g * h * g⁻¹) 1

def LieAlgebraValuedOneForm :=
  letI : NormedAddCommGroup (TangentSpace IG (1 : G)) :=
    show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (TangentSpace IG (1 : G)) :=
    show NormedSpace ℝ EG from inferInstance
  Cₛ^∞⟮IB.prod IG; (EB × EG) →L[ℝ] GroupLieAlgebra IG G,
    fun _p : P ↦ (EB × EG) →L[ℝ] GroupLieAlgebra IG G⟯

structure ConnectionForm where
  /-- The underlying Lie-algebra-valued 1-form -/
  form : LieAlgebraValuedOneForm (G := G) (IG := IG) (IB := IB) (P := P)
  /-- On fundamental vector fields, ω reproduces the Lie algebra element -/
  reproduces_fundamental :
    letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
      show NormedAddCommGroup EG from inferInstance
    letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
      show NormedSpace ℝ EG from inferInstance
    ∀ (p : P) (A : GroupLieAlgebra IG G),
    form.toFun p (fundamentalVectorField (IB := IB) (IG := IG) A p) = A
  /-- Equivariance: R_g^* ω = Ad_{g⁻¹} ∘ ω -/
  equivariant :
    letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
      show NormedAddCommGroup EG from inferInstance
    letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
      show NormedSpace ℝ EG from inferInstance
    ∀ (p : P) (g : G) (v : TangentSpace (IB.prod IG) p),
    form.toFun (p <• g) (mfderiv (IB.prod IG) (IB.prod IG) (· <• g) p v) =
      Ad g⁻¹ (form.toFun p v)

omit [IsManifold IB ∞ B] in
lemma fundamentalVectorField_mem_vertical
    (A : GroupLieAlgebra IG G) (p : P) :
    mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p
      (fundamentalVectorField A p) = 0 := by
  unfold fundamentalVectorField
  have h118 : MDifferentiableAt 𝓘(ℝ, ℝ) (IB.prod IG) (fun (t : ℝ) ↦ p <• expLie (t • A)) 0 := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) ∞ (fun t : ℝ ↦ t • (show EG from A)) :=
      (contDiff_id.smul_const (show EG from A)).contMDiff
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2) (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2) (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    have h3 : ContMDiff 𝓘(ℝ, ℝ) (IB.prod IG) (minSmoothness ℝ 2)
        (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) := by
      have hconst : ContMDiff 𝓘(ℝ, ℝ) (IB.prod IG) (minSmoothness ℝ 2)
          (fun _ : ℝ ↦ p) := contMDiff_const
      have hprod : ContMDiff 𝓘(ℝ, ℝ) ((IB.prod IG).prod IG) (minSmoothness ℝ 2)
          (fun t : ℝ ↦ (p, expLie (IG := IG) (t • A))) :=
        hconst.prodMk h2
      have hsmul : ContMDiff ((IB.prod IG).prod IG) (IB.prod IG) (minSmoothness ℝ 2)
        (fun p : P × G => p.1 <• p.2) :=
        (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG) (G := G)
          (M := P)).of_le
            (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
      exact hsmul.comp hprod
    exact h3.mdifferentiableAt (by norm_num)
  have heval : (fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = p := by
    simp [expLie_zero]
  have h121 : MDifferentiableAt (IB.prod IG) IB (fun p : P ↦ proj p)
    ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0) := by
    rw [heval]
    exact (hPB.smooth_proj).mdifferentiableAt (by norm_num)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) IB ((fun p : P ↦ proj p) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) 0 =
      (mfderiv (IB.prod IG) IB (fun p : P ↦ proj p)
        ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0)).comp
          (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun (t : ℝ) ↦ p <• expLie (t • A)) 0) :=
    mfderiv_comp (0 : ℝ) h121 h118
  have hconst : ((fun p : P ↦ proj p) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) = fun _ ↦ proj p := by
    ext t
    exact hPB.respects_fibres p (expLie (t • A))
  have hzero : mfderiv% ((fun p : P ↦ proj p) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = 0 := by
    rw [hconst]
    exact mfderiv_const
  rw [heval] at hcomp
  rw [hzero] at hcomp
  have key : (mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p).comp
      (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0) = 0 := by
    rw [← hcomp]; exact rfl
  calc mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p
        (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0 1)
      = ((mfderiv (IB.prod IG) IB (fun p : P ↦ proj p) p).comp
          (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0)) 1 := rfl
    _ = 0 := by rw [key]; simp

lemma mfderiv_expLie
  (A : GroupLieAlgebra IG G) :
    mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 1 = A := by
  have hcurve : IsMIntegralCurve (fun t ↦ expLie (IG := IG) (t • A))
                                 (mulInvariantVectorField (I := IG) A) :=
    isMIntegralCurve_expLie_smul A
  have h0 := hcurve 0
  simp only [mulInvariantVectorField] at h0
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) IG
    (fun t ↦ expLie (t • A)) (0 : ℝ)
    (ContinuousLinearMap.smulRight ((1 : ℝ →L[ℝ] ℝ))
      (((mfderiv% fun x ↦ expLie ((0 : ℝ) • A) * x) 1) A)) := h0
  rw [zero_smul, expLie_zero, one_mul] at h1
  have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ)
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (((mfderiv% fun x ↦ (1 : G) * x) 1) A)) := h1
  have hmul : mfderiv IG IG ((1 : G) * ·) 1 = ContinuousLinearMap.id ℝ (TangentSpace IG 1) := by
    have : ((1 : G) * ·) = id := by ext; simp
    rw [this, mfderiv_id]
  rw [hmul] at h2
  have h3 : HasMFDerivAt 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ)
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      ((ContinuousLinearMap.id ℝ (TangentSpace IG 1)) A)) := h2
  have h4 : (ContinuousLinearMap.id ℝ (TangentSpace IG 1)) A = A :=
    ContinuousLinearMap.id_apply A
  rw [h4] at h3
  have h5 : HasMFDerivAt 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ)
             (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) A) := h3
  have h6 : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) A) 1 = A := by
    simp
  have h7 : mfderiv 𝓘(ℝ, ℝ) IG (fun t ↦ expLie (t • A)) (0 : ℝ) =
            ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) A :=
    h5.mfderiv
  rw [h7]
  exact h6

section
open RightActions

omit [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
     [IsManifold (IB.prod IG) ∞ P] in
lemma fundamentalVectorField_eq_mfderiv_action (p : P) :
    ∀ (A : GroupLieAlgebra IG G),
    fundamentalVectorField (IB := IB) (IG := IG) A p =
    mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g) 1 A := by
  intro A
  have hg : MDifferentiableAt IG (IB.prod IG) (fun g : G ↦ p <• g)
      ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
    have h0 : ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) = 1 := by
      simp [zero_smul, expLie_zero]
    rw [h0]
    have := (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P))
    exact (this.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by norm_num)
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2) (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2) (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact h2.mdifferentiableAt (by norm_num)
  have hh : mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
        ((fun g : G ↦ p <• g) ∘ (fun t : ℝ ↦ expLie (IG := IG) (t • A))) 0 =
      (mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g)
        ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0)).comp
        (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) :=
    mfderiv_comp 0 hg hf
  have hkey : mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 1 =
      mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g) 1 A := by
    have hmfderiv : mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 =
        (mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g) 1).comp
          (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
      have h1 : ((fun (g : G) ↦ p <• g) ∘ fun (t : ℝ) ↦ expLie (IG := IG) (t • A)) =
               (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) :=
        Function.comp_def (fun g ↦ p <• g) fun t ↦ expLie (t • A)
      have h2 : (expLie ((0 : ℝ) • A)) = 1 := by simp [zero_smul, expLie_zero]
      rw [← h1, ← h2]
      exact hh
    simp only [hmfderiv]
    have h3 : ((mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A))) 0) 1 = A :=
      mfderiv_expLie (IG := IG) A
    change (((mfderiv IG (IB.prod IG) fun g ↦ p <• g) 1).comp
      ((mfderiv 𝓘(ℝ, ℝ) IG fun t ↦ expLie (IG := IG) (t • A)) 0)) 1 =
      ((mfderiv IG (IB.prod IG) fun g ↦ p <• g) 1) A
    rw [ContinuousLinearMap.comp_apply]
    exact Eq.symm (DFunLike.congr rfl (id (Eq.symm h3)))
  unfold fundamentalVectorField
  exact hkey

noncomputable def fundamentalVectorFieldLinearMap (p : P) :
    GroupLieAlgebra IG G →ₗ[ℝ] TangentSpace (IB.prod IG) p where
  toFun A := fundamentalVectorField (IB := IB) (IG := IG) A p
  map_add' A B := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_add]
    exact rfl
  map_smul' r A := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_smul, RingHom.id_apply]
    exact rfl

omit [IsManifold (IB.prod IG) ∞ P] in
lemma isMIntegralCurve_action_expLie (p : P) (A : GroupLieAlgebra IG G) :
    IsMIntegralCurve (I := IB.prod IG) (fun t ↦ p <• expLie (IG := IG) (t • A))
      (fun q : P ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) := by
  intro t
  have hflow : (fun s : ℝ ↦ p <• expLie (IG := IG) ((t + s) • A)) =
               (fun s : ℝ ↦ (p <• expLie (IG := IG) (t • A)) <• expLie (IG := IG) (s • A)) := by
    ext s
    have : expLie (IG := IG) ((t + s) • A) =
           expLie (IG := IG) (t • A) * expLie (IG := IG) (s • A) := expLie_add A t s
    rw [this, MulOpposite.op_mul, mul_smul]
  have hderiv : fundamentalVectorField (IB := IB) (IG := IG) A (p <• expLie (IG := IG) (t • A)) =
      mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun s ↦ p <• expLie (IG := IG) ((t + s) • A)) 0 1 := by
    rw [hflow]
    rfl
  simp only
  rw [hderiv]
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) (IB.prod IG) (minSmoothness ℝ 2)
      (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2)
        (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2)
        (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P)).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)).comp
      (contMDiff_const.prodMk h2)
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) (IB.prod IG)
      (fun t ↦ p <• expLie (IG := IG) (t • A)) t :=
    hsmooth.mdifferentiableAt (by norm_num)
  have hderiv2 := hmdiff.hasMFDerivAt
  convert hderiv2 using 1
  rw [← hderiv]
  simp only [fundamentalVectorField]
  ext
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
  have hshift : (fun s : ℝ ↦ (p <• expLie (IG := IG) (t • A)) <• expLie (IG := IG) (s • A)) =
                (fun s : ℝ ↦ p <• expLie (IG := IG) (t • A) <• expLie (IG := IG) (s • A)) := rfl
  rw [← hshift, ← hflow]
  have hshift2 : (fun s : ℝ ↦ p <• expLie (IG := IG) ((t + s) • A)) =
                 (fun t ↦ p <• expLie (IG := IG) (t • A)) ∘ (fun s ↦ t + s) := rfl
  rw [hshift2]
  have hmdiff_shift : MDifferentiableAt 𝓘(ℝ, ℝ) (IB.prod IG)
      (fun t ↦ p <• expLie (IG := IG) (t • A)) (t + 0) := by
    simp only [add_zero]; exact hmdiff
  rw [mfderiv_comp 0 hmdiff_shift (by
    have : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s ↦ t + s) 0 (ContinuousLinearMap.id ℝ ℝ) := by
      have h := (hasDerivAt_id (0 : ℝ)).const_add t
      rw [hasMFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
      simpa using h
    exact this.mdifferentiableAt)]
  simp only [mfderiv_eq_fderiv]
  rw [add_zero]
  have key : fderiv ℝ (HAdd.hAdd t) 0 = ContinuousLinearMap.id ℝ ℝ := by
    have h1 : fderiv ℝ (HAdd.hAdd t) 0 = fderiv ℝ (fun y ↦ t + (fun u => u) y) 0 := rfl
    have h2 : fderiv ℝ (fun y ↦ t + (fun u => u) y) 0 = fderiv ℝ (fun u => u) 0 :=
      fderiv_const_add t
    have h3 : fderiv ℝ (fun u : ℝ => u) 0 = ContinuousLinearMap.id ℝ ℝ := fderiv_id'
    rw [h1, h2, h3]
  simp only [key]
  congr 1

omit [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B] in
lemma contMDiff_fundamentalVectorField (A : GroupLieAlgebra IG G) :
    ContMDiff (IB.prod IG) (IB.prod IG).tangent (minSmoothness ℝ 1)
      (fun p : P ↦ (⟨p, fundamentalVectorField (IB := IB) (IG := IG) A p⟩ :
        TangentBundle (IB.prod IG) P)) := by
  haveI : IsManifold (IB.prod IG) 1 P := IsManifold.of_le (n := ∞) (by norm_num)
  have hsmooth : ContMDiff ((IB.prod IG).prod 𝓘(ℝ, ℝ)) (IB.prod IG) (minSmoothness ℝ 2)
      (fun (q : P × ℝ) ↦ q.1 <• expLie (IG := IG) (q.2 • A)) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2)
        (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2)
        (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P)).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)).comp
      (contMDiff_fst.prodMk (h2.comp (contMDiff_snd (I := IB.prod IG) (J := 𝓘(ℝ, ℝ)))))
  intro q
  have hq := ContMDiffAt.mfderiv
    (N := P) (M := ℝ) (M' := P)
    (J := IB.prod IG) (I := 𝓘(ℝ, ℝ)) (I' := IB.prod IG)
    (m := minSmoothness ℝ 1) (n := minSmoothness ℝ 2) (x₀ := q)
    (fun p t ↦ p <• expLie (IG := IG) (t • A))
    (fun _ ↦ (0 : ℝ))
    (hsmooth.contMDiffAt)
    (contMDiffAt_const)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl (1 + 1))
  simp only [zero_smul, expLie_zero] at hq
  simp only [MulOpposite.op_one, one_smul] at hq
  rw [contMDiffAt_section q]
  apply ContMDiffAt.congr_of_eventuallyEq (hq.clm_apply (contMDiffAt_const (c := (1 : ℝ))))
  filter_upwards [(chartAt (ModelProd HB HG) q).open_source.mem_nhds
    (mem_chart_source (ModelProd HB HG) q)] with x hx
  simp only [TangentBundle.trivializationAt_apply, fundamentalVectorField]
  simp only [OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.toFun_eq_coe, PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_coe_symm,
    ModelWithCorners.toPartialEquiv_coe_symm, Function.comp_apply]
  have hrw := inTangentCoordinates_eq (I := 𝓘(ℝ, ℝ)) (I' := IB.prod IG)
    (f := fun x ↦ (0 : ℝ)) (g := fun x ↦ x)
    (ϕ := fun x ↦ (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
      (fun (t : ℝ) ↦ x <• expLie (IG := IG) (t • A)) 0))
    (hx := ChartedSpace.mem_chart_source (0 : ℝ))
    (hy := hx)
  rw [hrw]
  simp only [tangentBundleCore_coordChange, OpenPartialHomeomorph.extend, coe_achart,
    PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
    PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_coe_symm, ModelWithCorners.toPartialEquiv_coe_symm,
    Function.comp_apply, ContinuousLinearMap.coe_comp']
  simp only [modelWithCornersSelf_coe, OpenPartialHomeomorph.refl_partialEquiv,
    PartialEquiv.refl_source,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, OpenPartialHomeomorph.refl_apply,
    CompTriple.comp_eq,
    OpenPartialHomeomorph.refl_symm, modelWithCornersSelf_coe_symm, range_id, id_eq,
    fderivWithin_univ, fderiv_id, ContinuousLinearMap.coe_id']
  rfl

end

section
open RightActions
variable
  [T2Space P]
  [BoundarylessManifold (IB.prod IG) P]

omit [IsManifold IB ∞ B] in
lemma fundamentalVectorField_zero_iff
    [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]
    (p : P) (A : GroupLieAlgebra IG G) :
    fundamentalVectorField (IB := IB) (IG := IG) A p = 0 → A = 0 := by
  intro h
  have hconst : ∀ (t : ℝ), p <• expLie (IG := IG) (t • A) = p := by
    have hcurve : IsMIntegralCurve (I := IB.prod IG) (fun t ↦ p <• expLie (IG := IG) (t • A))
        (fun q : P ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) :=
      isMIntegralCurve_action_expLie p A
    have hconstcurve : IsMIntegralCurve (I := IB.prod IG) (fun _ : ℝ ↦ p)
        (fun q : P ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) :=
      isMIntegralCurve_const h
    have heq : (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) = (fun _ ↦ p) := by
      apply isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
          (fun _ ↦ BoundarylessManifold.isInteriorPoint (I := IB.prod IG))
      · exact (contMDiff_fundamentalVectorField (IB := IB) (IG := IG) A).of_le (by norm_num)
      · exact hcurve
      · exact hconstcurve
      · simp [expLie_zero]
    exact fun t ↦ congr_fun heq t
  have hexp : ∀ (t : ℝ), expLie (IG := IG) (t • A) = 1 := by
    intro t
    have hfree := hPB.is_free p
    have hstab : MulOpposite.op (expLie (IG := IG) (t • A)) ∈
        MulAction.stabilizer (MulOpposite G) p := by
      simp [MulAction.mem_stabilizer_iff, hconst t]
    rw [hfree] at hstab
    simp only [Subgroup.mem_bot, MulOpposite.op_eq_one_iff] at hstab
    exact hstab
  have := mfderiv_expLie (IG := IG) A
  rw [show (fun t : ℝ ↦ expLie (IG := IG) (t • A)) = (fun _ ↦ (1 : G)) from
      funext hexp] at this
  simp [mfderiv_const] at this
  exact this.symm

end

section

def IsLocalSection (σ : B → P) (U : Set B) : Prop :=
  IsOpen U ∧
  ContMDiffOn IB (IB.prod IG) ∞ σ U ∧
  ∀ m ∈ U, proj (σ m) = m

omit [IsManifold IB ∞ B]
     [T2Space G]
     [CompleteSpace EG]
     [BoundarylessManifold IG G] in
lemma gaugeMap_exists
    (σ₁ σ₂ : B → P)
    (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₂ U₂)
    (m : B) (hm : m ∈ U₁ ∩ U₂) :
    ∃ g : G, σ₂ m = σ₁ m <• g := by
  have h1 : proj (σ₁ m) = m := hσ₁.2.2 m hm.1
  have h2 : proj (σ₂ m) = m := hσ₂.2.2 m hm.2
  have hmem : σ₂ m ∈ MulAction.orbit (MulOpposite G) (σ₁ m) :=
    IsPrincipalBundle.is_transitive (IB := IB) (IG := IG) (P := P) m (σ₁ m) (σ₂ m) h1 h2
  rw [MulAction.mem_orbit_iff] at hmem
  obtain ⟨g, hg⟩ := hmem
  exact ⟨MulOpposite.unop g, by rw [← hg]; simp [HSMul.hSMul]⟩

set_option linter.unusedSectionVars false in
omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma gaugeMap_unique
    [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]
    (σ₁ σ₂ : B → P)
    (m : B) (g h : G)
    (hg : σ₁ m <• g = σ₂ m)
    (hh : σ₁ m <• h = σ₂ m) :
    g = h := by
  have heq : σ₁ m <• g = σ₁ m <• h := hg.trans hh.symm
  have haction : σ₁ m <• (g * h⁻¹) = σ₁ m := by
    simp only [MulOpposite.op_mul, mul_smul]
    rw [heq]
    simp only [MulOpposite.op_inv, inv_smul_smul]
  have hone : MulOpposite.op (g * h⁻¹) ∈
      MulAction.stabilizer (MulOpposite G) (σ₁ m) := by
    simp only [MulAction.mem_stabilizer_iff, haction]
  rw [hPB.is_free (σ₁ m)] at hone
  exact eq_of_mul_inv_eq_one (MulOpposite.op_injective hone)

/-- The Maurer-Cartan form on a Lie group `G`. -/
noncomputable def maurerCartan (g : G) : TangentSpace IG g →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h ↦ g⁻¹ * h) g

/-- The Yang-Mills field associated to a local section `σ` of the principal bundle
    and a connection 1-form `ω` on `P`. -/
noncomputable def yangMillsField
    (τ : ConnectionForm (G := G) (IG := IG) (IB := IB) (P := P))
    (σ : B → P) :
    ∀ m : B, TangentSpace IB m →L[ℝ] GroupLieAlgebra IG G :=
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
    show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
    show NormedSpace ℝ EG from inferInstance
  fun m ↦ (τ.form.toFun (σ m)).comp (mfderiv IB (IB.prod IG) σ m)

omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma mfderiv_smul_section
    (m : B)
    (σ : B → P) (Ω : B → G)
    (hσ : ContMDiffAt IB (IB.prod IG) ∞ σ m)
    (hΩ : ContMDiffAt IB IG ∞ Ω m)
    (v : TangentSpace IB m) :
    mfderiv IB (IB.prod IG) (fun x ↦ σ x <• Ω x) m v =
      mfderiv (IB.prod IG) (IB.prod IG) (· <• Ω m) (σ m) (mfderiv IB (IB.prod IG) σ m v) +
      mfderiv IG (IB.prod IG) (σ m <• ·) (Ω m) (mfderiv IB IG Ω m v) := by
  have hcomp : (fun x ↦ σ x <• Ω x) = (fun p : P × G ↦ p.1 <• p.2) ∘
    (fun x ↦ (σ x, Ω x)) := rfl
  rw [hcomp]
  have hpair : ContMDiffAt IB ((IB.prod IG).prod IG) ∞ (fun x ↦ (σ x, Ω x)) m :=
    hσ.prodMk hΩ
  have hsmul : MDifferentiableAt ((IB.prod IG).prod IG) (IB.prod IG)
    (fun p : P × G ↦ p.1 <• p.2) (σ m, Ω m) :=
      (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
        (G := G) (M := P)).mdifferentiableAt (by norm_num)
  rw [mfderiv_comp m hsmul (hpair.mdifferentiableAt
       (by exact Ne.symm (not_eq_of_beq_eq_false rfl)))]
  have foo : ∀ w : TangentSpace ((IB.prod IG).prod IG) (σ m, Ω m),
      (mfderiv ((IB.prod IG).prod IG) (IB.prod IG)
        (fun p : P × G ↦ p.1 <• p.2) (σ m, Ω m)) w =
      (mfderiv (IB.prod IG) (IB.prod IG) (fun z ↦ z <• Ω m) (σ m)) w.1 +
      (mfderiv IG (IB.prod IG) (fun z ↦ σ m <• z) (Ω m)) w.2 :=
    fun w ↦ mfderiv_prod_eq_add_apply hsmul
  have hpair' : MDifferentiableAt IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m :=
    hpair.mdifferentiableAt (by norm_num)
  simp only [ContinuousLinearMap.comp_apply]
  rw [foo]
  congr 1
  · congr 1
    have hσ' : MDifferentiableAt IB (IB.prod IG) σ m := hσ.mdifferentiableAt (by norm_num)
    have hΩ' : MDifferentiableAt IB IG Ω m := hΩ.mdifferentiableAt (by norm_num)
    have hprod : mfderiv IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m =
        (mfderiv IB (IB.prod IG) σ m).prod (mfderiv IB IG Ω m) :=
      hσ'.mfderiv_prod hΩ'
    simp only [hprod]
    exact Prod.fst_eq_iff.mpr rfl
  · congr 1
    have hσ' : MDifferentiableAt IB (IB.prod IG) σ m := hσ.mdifferentiableAt (by norm_num)
    have hΩ' : MDifferentiableAt IB IG Ω m := hΩ.mdifferentiableAt (by norm_num)
    have hprod : mfderiv IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m =
        (mfderiv IB (IB.prod IG) σ m).prod (mfderiv IB IG Ω m) :=
      hσ'.mfderiv_prod hΩ'
    simp only [hprod]
    exact Prod.snd_eq_iff.mpr rfl

omit [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
     [IsManifold (IB.prod IG) ∞ P] in
lemma mfderiv_action_at_g (p : P) (g : G) (w : TangentSpace IG g) :
    mfderiv IG (IB.prod IG) (p <• ·) g w =
      fundamentalVectorField (IB := IB) (IG := IG) (maurerCartan g w) (p <• g) := by
  rw [fundamentalVectorField_eq_mfderiv_action]
  have hdecomp : (fun g' : G ↦ p <• g') = (fun h : G ↦ (p <• g) <• h) ∘ (fun g' ↦ g⁻¹ * g') := by
    calc (fun g' : G ↦ p <• g') = (fun g' : G ↦ p <• (g * (g⁻¹ * g'))) := by
          simp [mul_inv_cancel_left]
      _ = (fun g' : G ↦ (p <• g) <• (g⁻¹ * g')) := by
          ext g'
          show p <• (g * (g⁻¹ * g')) = (p <• g) <• (g⁻¹ * g')
          rw [← mul_smul, MulOpposite.op_mul]
      _ = (fun h : G ↦ (p <• g) <• h) ∘ (fun g' ↦ g⁻¹ * g') := rfl
  have hLG : MDifferentiableAt IG IG (fun g' ↦ g⁻¹ * g') g :=
    (contMDiff_mul_left (a := g⁻¹) (n := ∞)).mdifferentiableAt (by norm_num)
  have hact : MDifferentiableAt IG (IB.prod IG) (fun h : G ↦ (p <• g) <• h) 1 :=
    ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := P)).comp
      (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by norm_num)
  have hmC : mfderiv IG IG (fun g' ↦ g⁻¹ * g') g = maurerCartan g := rfl
  conv_lhs => rw [hdecomp]
  have hact' : MDifferentiableAt IG (IB.prod IG) (fun h : G ↦ (p <• g) <• h) (g⁻¹ * g) := by
    rw [inv_mul_cancel]
    exact hact
  rw [mfderiv_comp g hact' hLG, hmC]
  rw [inv_mul_cancel]
  haveI : Module ℝ (TangentSpace (IB.prod IG) (p <• g)) := inferInstance
  exact rfl

end

/-- The transition function between two local sections of a smooth principal bundle is smooth.
    TODO: prove this properly once equivariant_triv is generalized to all atlas trivializations. -/
theorem contMDiffAt_gaugeMap
    {B : Type*} [TopologicalSpace B]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    {HB : Type*} [TopologicalSpace HB]
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HB B]
    [IsManifold IB ∞ B]
    {G : Type*} [TopologicalSpace G] [T2Space G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {IG : ModelWithCorners ℝ EG HG}
    [ChartedSpace HG G]
    [Group G]
    [LieGroup IG ∞ G]
    [BoundarylessManifold IG G]
    {P : Type*}
    [TopologicalSpace P]
    [ChartedSpace (ModelProd HB HG) P]
    [IsManifold (IB.prod IG) ∞ P]
    [MulAction (MulOpposite G) P]
    [SmoothRightGAction ∞ IG (IB.prod IG) G P]
    {proj : P → B}
    [IsPrincipalBundle IB G IG P (IB.prod IG) proj]
    (σ₁ σ₂ : B → P)
    (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₂ U₂)
    (Ω : B → G)
    (hΩ : ∀ x ∈ U₁ ∩ U₂, σ₁ x <• Ω x = σ₂ x)
    (m : B) (hm : m ∈ U₁ ∩ U₂) :
    ContMDiffAt IB IG ∞ Ω m := by
  sorry

section

variable
  {B : Type*} [TopologicalSpace B]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB}
  [ChartedSpace HB B]
  [IsManifold IB ∞ B]
  {G : Type*} [TopologicalSpace G] [T2Space G]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [Group G]
  [LieGroup IG ∞ G]
  [BoundarylessManifold IG G]
  {P : Type*}
  [TopologicalSpace P]
  [ChartedSpace (ModelProd HB HG) P]
  [IsManifold (IB.prod IG) ∞ P]
  [MulAction (MulOpposite G) P]
  [SmoothRightGAction ∞ IG (IB.prod IG) G P]
  {proj : P → B}
  [hPB : IsPrincipalBundle IB G IG P (IB.prod IG) proj]

/-- The transformation law for Yang-Mills fields. -/
theorem yangMills_transformation
    (τ : ConnectionForm (G := G) (IG := IG) (IB := IB) (P := P))
    (σ₁ σ₂ : B → P) (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) (proj := proj) σ₂ U₂)
    (Ω : B → G) (hΩ : ∀ m ∈ U₁ ∩ U₂, σ₁ m <• Ω m = σ₂ m)
    (m : B) (hm : m ∈ U₁ ∩ U₂) (v : TangentSpace IB m) :
    yangMillsField (IB := IB) (IG := IG) τ σ₂ m v =
      Ad (Ω m)⁻¹ (yangMillsField (IB := IB) (IG := IG) τ σ₁ m v) +
      maurerCartan (Ω m) (mfderiv IB IG Ω m v) := by
  simp only [yangMillsField, ContinuousLinearMap.comp_apply]
  rw [← hΩ m hm]
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) := show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) := show NormedSpace ℝ EG from inferInstance
  have hmderiv_σ₂ : mfderiv IB (IB.prod IG) σ₂ m =
      mfderiv IB (IB.prod IG) (fun x ↦ σ₁ x <• Ω x) m :=
    have bar : U₁ ∩ U₂ ∈ nhds m := (hσ₁.1.inter hσ₂.1).mem_nhds hm
    Filter.EventuallyEq.mfderiv_eq (Filter.eventually_of_mem bar
      (fun x hx ↦ (hΩ x hx).symm))
  calc τ.form.toFun (σ₁ m <• Ω m) (mfderiv IB (IB.prod IG) σ₂ m v)
      = τ.form.toFun (σ₁ m <• Ω m) (mfderiv IB (IB.prod IG) (fun x ↦ σ₁ x <• Ω x) m v) := by
          congr 1; exact hmderiv_σ₂ ▸ rfl
    _ = τ.form.toFun (σ₁ m <• Ω m)
          (mfderiv (IB.prod IG) (IB.prod IG) (· <• Ω m) (σ₁ m) (mfderiv IB (IB.prod IG) σ₁ m v) +
           mfderiv IG (IB.prod IG) (σ₁ m <• ·) (Ω m) (mfderiv IB IG Ω m v)) := by
          congr 1
          have hΩ_smooth : ContMDiffAt IB IG ∞ Ω m :=
            contMDiffAt_gaugeMap σ₁ σ₂ U₁ U₂ hσ₁ hσ₂ Ω hΩ m hm
          have foo : U₁ ∈ nhds m := hσ₁.1.mem_nhds hm.1
          exact mfderiv_smul_section m σ₁ Ω (hσ₁.2.1.contMDiffAt foo) hΩ_smooth v
    _ = τ.form.toFun (σ₁ m <• Ω m)
          (mfderiv (IB.prod IG) (IB.prod IG) (· <• Ω m) (σ₁ m) (mfderiv IB (IB.prod IG) σ₁ m v)) +
        τ.form.toFun (σ₁ m <• Ω m)
          (mfderiv IG (IB.prod IG) (σ₁ m <• ·) (Ω m) (mfderiv IB IG Ω m v)) := by
          exact map_add _ _ _
    _ = Ad (Ω m)⁻¹ (τ.form.toFun (σ₁ m) (mfderiv IB (IB.prod IG) σ₁ m v)) +
          maurerCartan (Ω m) (mfderiv IB IG Ω m v) := by
          congr 1
          · exact τ.equivariant (σ₁ m) (Ω m) (mfderiv IB (IB.prod IG) σ₁ m v)
          · have hfund : mfderiv IG (IB.prod IG) (σ₁ m <• ·) (Ω m) (mfderiv IB IG Ω m v) =
                fundamentalVectorField (IB := IB) (IG := IG)
                  (maurerCartan (Ω m) (mfderiv IB IG Ω m v)) (σ₁ m <• Ω m) :=
              mfderiv_action_at_g (σ₁ m) (Ω m) (mfderiv IB IG Ω m v)
            rw [hfund, τ.reproduces_fundamental]

end
