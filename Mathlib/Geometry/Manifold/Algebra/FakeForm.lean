import Mathlib
import Mathlib.Geometry.Manifold.Algebra.PrincipalGBundle

open Set Bundle ContDiff Manifold Trivialization

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

noncomputable section

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

-- Principal bundle total space
variable
  {P : Type*} [TopologicalSpace P]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP]
  {IP : ModelWithCorners ℝ EP HP}
  [ChartedSpace HP P]
  [IsManifold IP ∞ P]
  {FP : Type*} [NormedAddCommGroup FP] [NormedSpace ℝ FP]

-- Lie group
variable
  {G : Type*} [TopologicalSpace G]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [Group G] [LieGroup IG ⊤ G]

def LieAlgebraValuedOneForm :=
  letI : NormedAddCommGroup (TangentSpace IG (1 : G)) :=
    show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (TangentSpace IG (1 : G)) :=
    show NormedSpace ℝ EG from inferInstance
  Cₛ^∞⟮IP; FP →L[ℝ] GroupLieAlgebra IG G,
           fun _p : P ↦ FP →L[ℝ] GroupLieAlgebra IG G⟯

section
open RightActions

class IsPrincipalBundle
    (G : Type*) [TopologicalSpace G] [Group G]
    (P : Type*) [TopologicalSpace P]
    (B : Type*) [TopologicalSpace B]
    [MulAction (MulOpposite G) P]
    (ρ : P → B)
    (IP : ModelWithCorners ℝ EP HP)
    (IB : ModelWithCorners ℝ EB HB)
    [ChartedSpace HP P] [ChartedSpace HB B] : Prop where
  respects_fibres : ∀ (p : P) (g : G), ρ (p <• g) = ρ p
  is_free : ∀ (p : P) (g : G), p <• g = p → g = 1
  is_transitive : ∀ (b : B) (p q : P), ρ p = b → ρ q = b →
    ∃ g : G, p <• g = q
  smooth_proj : ContMDiff IP IB ∞ ρ

variable
  [MulAction (MulOpposite G) P]
  (ρ : P → B)
  [IsPrincipalBundle G P B ρ IP IB]
  [T2Space G]
  [CompleteSpace EG]
  [BoundarylessManifold IG G]

noncomputable def fundamentalVectorField
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    (A : GroupLieAlgebra IG G)
    (p : P) :
    TangentSpace IP p :=
  mfderiv 𝓘(ℝ, ℝ) IP
    (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A))
    (0 : ℝ) 1

noncomputable def Ad (g : G) : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h : G ↦ g * h * g⁻¹) 1

structure ConnectionForm where
  /-- The underlying Lie-algebra-valued 1-form -/
  form : LieAlgebraValuedOneForm (P := P) (IP := IP) (FP := EP)
                                 (G := G) (IG := IG)
  /-- On fundamental vector fields, ω reproduces the Lie algebra element -/
  reproduces_fundamental :
    letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
      show NormedAddCommGroup EG from inferInstance
    letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
      show NormedSpace ℝ EG from inferInstance
    ∀ (p : P) (A : GroupLieAlgebra IG G),
    form.toFun p (fundamentalVectorField (HP := HP) (IP := IP) A p) = A
  /-- Equivariance: R_g^* ω = Ad_{g⁻¹} ∘ ω -/
  equivariant :
      letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
      show NormedAddCommGroup EG from inferInstance
    letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
      show NormedSpace ℝ EG from inferInstance
    ∀ (p : P) (g : G) (v : TangentSpace IP p),
    form.toFun (p <• g) (mfderiv IP IP (· <• g) p v) =
      Ad g⁻¹ (form.toFun p v)

/- TODO: `PrincipalEhresmannConnection` should be shown to be a special case of
   `EhresmannConnection`. This requires identifying the abstract total space `P`
   with `TotalSpace FP (fun _ : B ↦ G)`, i.e. showing that a principal bundle
   with structure group `G` and base `B` is a fiber bundle with fiber `G`.
   This would make `PrincipalEhresmannConnection` literally extend `EhresmannConnection`
   and the current parallel definitions would collapse into a single hierarchy:

     EhresmannConnection          (general fiber bundle)
           ↑
     PrincipalEhresmannConnection (fiber bundle + equivariance)
           ↑
     ConnectionForm               (𝔤-valued 1-form)

   See also the relationship with `FiberBundleCore` and `PrincipalBundleCore`. -/

lemma fundamentalVectorField_mem_vertical
  [SmoothRightGAction ∞ IG IP G P]
    (A : GroupLieAlgebra IG G) (p : P) :
    mfderiv IP IB ρ p (fundamentalVectorField A p) = 0 := by
  unfold fundamentalVectorField
  have h118 : MDiffAt (fun (t : ℝ) ↦ p <• expLie (t • A)) 0 := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) ∞ (fun t : ℝ ↦ t • (show EG from A)) :=
      (contDiff_id.smul_const (show EG from A)).contMDiff
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG ∞ (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    have h3 : ContMDiff 𝓘(ℝ, ℝ) IP ∞ (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) := by
      have hconst : ContMDiff 𝓘(ℝ, ℝ) IP ∞ (fun _ : ℝ ↦ p) := contMDiff_const
      have hprod : ContMDiff 𝓘(ℝ, ℝ) (IP.prod IG) ∞ (fun t : ℝ ↦ (p, expLie (IG := IG) (t • A))) :=
        hconst.prodMk h2
      exact SmoothRightGAction.smooth_smul.comp hprod
    exact h3.mdifferentiableAt (by norm_num)
  have h121 : MDiffAt ρ ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0) := by
    have : ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0) = p := by
      simp only [zero_smul]
      rw [expLie_zero, MulOpposite.op_one]
      exact MulAction.one_smul p
    rw [this]
    have h1 : ContMDiff IP IB ∞ ρ :=
      (IsPrincipalBundle.smooth_proj (G := G) (IP := IP) (IB := IB) (ρ := ρ))
    exact h1.mdifferentiableAt (by norm_num)
  have h122 : MDiffAt ρ p :=
    (IsPrincipalBundle.smooth_proj (G := G) (IP := IP) (IB := IB) (ρ := ρ)).mdifferentiableAt
      (by norm_num)
  have hcomp : mfderiv% (ρ ∘ fun (t : ℝ) ↦ p <• expLie (t • A)) 0 =
          (mfderiv% ρ ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0)).comp
            (mfderiv% (fun (t : ℝ) ↦ p <• expLie (t • A)) 0) :=
    mfderiv_comp (0 : ℝ) h121 h118
  have hconst : (ρ ∘ fun (t : ℝ) ↦ p <• expLie (t • A)) = fun _ ↦ ρ p := by
    ext t
    exact IsPrincipalBundle.respects_fibres IP IB p (expLie (t • A))
  have hzero : mfderiv% (ρ ∘ fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = 0 := by
    rw [hconst]
    exact mfderiv_const
  have heval : (fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = p := by
    simp [expLie_zero]
  rw [heval] at hcomp
  rw [hzero] at hcomp
  have key : (mfderiv% ρ p).comp (mfderiv% (fun t : ℝ ↦ p <• expLie (t • A)) 0) = 0 := by
    rw [← hcomp]
    exact rfl
  calc mfderiv% ρ p (mfderiv% (fun t : ℝ ↦ p <• expLie (t • A)) 0 1)
      = ((mfderiv% ρ p).comp (mfderiv% (fun t : ℝ ↦ p <• expLie (t • A)) 0)) 1 := rfl
    _ = 0 := by rw [key]; simp

end

lemma mfderiv_expLie [T2Space G] [BoundarylessManifold IG G] [CompleteSpace EG]
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

lemma fundamentalVectorField_eq_mfderiv_action (p : P)
     [MulAction Gᵐᵒᵖ P] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
     [SmoothRightGAction ∞ IG IP G P] :
    ∀ (A : GroupLieAlgebra IG G),
    fundamentalVectorField (HP := HP) (IP := IP) A p =
    mfderiv IG IP (fun g : G ↦ p <• g) 1 A := by
  intro A
  have hg : MDiffAt (fun g : G ↦ p <• g) ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
    have h0 : ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) = 1 := by
      simp [zero_smul, expLie_zero]
    rw [h0]
    have := SmoothRightGAction.smooth_smul (n := ∞) (I_G := IG) (I_M := IP) (G := G) (M := P)
    exact (this.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiableAt (by norm_num)
  have hf : MDiffAt (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) ∞ (fun t : ℝ ↦ t • (show EG from A)) :=
      (contDiff_id.smul_const (show EG from A)).contMDiff
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG ∞ (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact h2.mdifferentiableAt (by norm_num)
  have hh : mfderiv% ((fun g : G ↦ p <• g) ∘ (fun t : ℝ ↦ expLie (IG := IG) (t • A))) 0 =
            (mfderiv% (fun g : G ↦ p <• g) ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0)).comp
            (mfderiv% ((fun t : ℝ ↦ expLie (IG := IG) (t • A))) 0) := mfderiv_comp 0 hg hf
  have hkey : mfderiv% (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 1 =
      mfderiv% (fun g : G ↦ p <• g) 1 A := by
    have : mfderiv% (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 =
        (mfderiv% (fun g : G ↦ p <• g) 1).comp
          (mfderiv% (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
      have := hh
      simp only [Function.comp_apply] at this
      have h0 :
        mfderiv% ((fun (g : G) ↦ p <• g) ∘ fun (t : ℝ) ↦ expLie (IG := IG) (t •> A)) 0 =
        ((mfderiv% fun(g : G) ↦ p <• g) (expLie (0 •> A))).comp
          ((mfderiv% fun (t : ℝ) ↦ expLie (IG := IG) (t •> A)) 0) :=
          this
      have h1 : ((fun (g : G) ↦ p <• g) ∘ fun (t : ℝ) ↦ expLie (IG := IG) (t •> A)) =
             (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t •> A)) :=
               Function.comp_def (fun g ↦ p <• g) fun t ↦ expLie (t •> A)
      have h2 : (expLie ((0 : ℝ) •> A)) = 1 := by
        simp only [zero_smul]
        exact expLie_zero
      rw [h1, h2] at h0
      exact h0
    simp only [this]
    have h3 : ((mfderiv% fun (t : ℝ) ↦ expLie (IG := IG) (t • A)) 0) 1 = A :=
      mfderiv_expLie (IG := IG) A
    change (((mfderiv% fun (g : G) ↦ p <• g) 1).comp
      ((mfderiv% fun (t : ℝ) ↦ expLie (IG := IG) (t • A)) 0)) 1 =
      ((mfderiv% fun (g : G) ↦ p <• g) 1) A
    rw [ContinuousLinearMap.comp_apply]
    exact Eq.symm (DFunLike.congr rfl (id (Eq.symm h3)))
  unfold fundamentalVectorField
  exact hkey

noncomputable def fundamentalVectorFieldLinearMap (p : P)
    [MulAction Gᵐᵒᵖ P] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    [SmoothRightGAction ∞ IG IP G P] :
    GroupLieAlgebra IG G →ₗ[ℝ] TangentSpace IP p where
  toFun A := fundamentalVectorField (HP := HP) (IP := IP) A p
  map_add' A B := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_add]
    exact rfl
  map_smul' r A := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_smul, RingHom.id_apply]
    exact rfl

/-- The curve `t ↦ p <• expLie (t • A)` is an integral curve of the fundamental vector field
`fun q ↦ fundamentalVectorField A q` on the principal bundle `P`.

This is Proposition 27.14 from Tu, *Differential Geometry: Connections, Curvature, and
Characteristic Classes*, Springer, 2017.

TODO: A dog's dinner — maybe a more direct proof would use the fact that
the curve is the composition of the smooth right action with the one-parameter subgroup
`t ↦ expLie (t • A)`, and differentiate directly using the chain rule.
-/
lemma isMIntegralCurve_action_expLie (p : P) (A : GroupLieAlgebra IG G)
    [MulAction Gᵐᵒᵖ P] [SmoothRightGAction ∞ IG IP G P]
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] :
    IsMIntegralCurve (I := IP) (fun t ↦ p <• expLie (IG := IG) (t • A))
      (fun q : P ↦ fundamentalVectorField (HP := HP) (IP := IP) A q) := by
  intro t
  have hflow : (fun s : ℝ ↦ p <• expLie (IG := IG) ((t + s) • A)) =
               (fun s : ℝ ↦ (p <• expLie (IG := IG) (t • A)) <• expLie (IG := IG) (s • A)) := by
    ext s
    rw [expLie_add]
    simp only [MulOpposite.op_mul, mul_smul]
  have hderiv : fundamentalVectorField (HP := HP) (IP := IP) A (p <• expLie (IG := IG) (t • A)) =
      mfderiv 𝓘(ℝ, ℝ) IP (fun s ↦ p <• expLie (IG := IG) ((t + s) • A)) 0 1 := by
    rw [hflow]
    rfl
  simp only
  rw [hderiv]
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) IP ∞ (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) ∞ (fun t : ℝ ↦ t • (show EG from A)) :=
      (contDiff_id.smul_const (show EG from A)).contMDiff
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG ∞ (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact (SmoothRightGAction.smooth_smul (n := ∞) (I_G := IG) (I_M := IP) (G := G) (M := P)).comp
      (contMDiff_const.prodMk h2)
  have hmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) IP (fun t ↦ p <• expLie (IG := IG) (t • A)) t :=
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
  have : (MDiffAt fun (t : ℝ) ↦ p <• expLie (t •> A)) (t + 0) := by
    simp only [add_zero]; exact hmdiff
  rw [mfderiv_comp 0 this (by
    have : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s ↦ t + s) 0 (ContinuousLinearMap.id ℝ ℝ) := by
      have h := (hasDerivAt_id (0 : ℝ)).const_add t
      rw [hasMFDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
      simpa using h
    exact this.mdifferentiableAt)]
  simp only [mfderiv_eq_fderiv]
  rw [add_zero]
  have : (fderiv ℝ (HAdd.hAdd t) 0) = (fderiv ℝ (t + ·) 0) := rfl
  have : (fderiv ℝ (HAdd.hAdd t) 0) = (fderiv ℝ (fun s => (t + s)) 0) := rfl
  have : (fun s => (t + s)) = fun s => t + (fun u => u) s := rfl
  have : fderiv ℝ (fun y ↦ t + (fun u => u) y) 0 = fderiv ℝ (fun u => u) 0 := fderiv_const_add t
  have key : fderiv ℝ (HAdd.hAdd t) 0 = ContinuousLinearMap.id ℝ ℝ := by
    have h1 : fderiv ℝ (HAdd.hAdd t) 0 = fderiv ℝ (fun y ↦ t + (fun u => u) y) 0 := rfl
    have h2 : fderiv ℝ (fun y ↦ t + (fun u => u) y) 0 = fderiv ℝ (fun u => u) 0 :=
      fderiv_const_add t
    have h3 : fderiv ℝ (fun u : ℝ => u) 0 = ContinuousLinearMap.id ℝ ℝ := by
      exact fderiv_id'
    rw [h1, h2, h3]
  simp only [key]
  congr 1

lemma contMDiff_fundamentalVectorField
    [MulAction Gᵐᵒᵖ P] [SmoothRightGAction ∞ IG IP G P]
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    (A : GroupLieAlgebra IG G) :
    ContMDiff IP IP.tangent ∞
      (fun p : P ↦ (⟨p, fundamentalVectorField (HP := HP) (IP := IP) A p⟩ : TangentBundle IP P))
        := by
  haveI : IsManifold IP 1 P := IsManifold.of_le (n := ∞) (by norm_num)
  have hsmooth : ContMDiff (IP.prod 𝓘(ℝ, ℝ)) IP ∞
      (fun (q : P × ℝ) ↦ q.1 <• expLie (IG := IG) (q.2 • A)) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) ∞ (fun t : ℝ ↦ t • (show EG from A)) :=
      (contDiff_id.smul_const (show EG from A)).contMDiff
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG ∞ (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact (SmoothRightGAction.smooth_smul (n := ∞) (I_G := IG) (I_M := IP) (G := G) (M := P)).comp
      (contMDiff_fst.prodMk (h2.comp contMDiff_snd))
  intro q
  have hq := ContMDiffAt.mfderiv (N := P) (M := ℝ) (M' := P) (J := IP) (I := 𝓘(ℝ, ℝ)) (I' := IP)
          (m := ∞) (n := ∞) (x₀ := q)
          (fun p t ↦ p <• expLie (IG := IG) (t • A))
          (fun _ ↦ (0 : ℝ))
          (hsmooth.contMDiffAt)
          (contMDiffAt_const)
          (by norm_num)
  simp only [zero_smul, expLie_zero] at hq
  simp only [MulOpposite.op_one, one_smul] at hq
  rw [contMDiffAt_section q]
  apply ContMDiffAt.congr_of_eventuallyEq (hq.clm_apply (contMDiffAt_const (c := (1 : ℝ))))
  filter_upwards [(chartAt HP q).open_source.mem_nhds (mem_chart_source HP q)] with x hx
  simp only [TangentBundle.trivializationAt_apply, fundamentalVectorField]
  simp only [OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
   ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.toFun_eq_coe, PartialEquiv.coe_trans_symm,
     OpenPartialHomeomorph.coe_coe_symm,
    ModelWithCorners.toPartialEquiv_coe_symm, Function.comp_apply]
  have hrw := inTangentCoordinates_eq (I := 𝓘(ℝ, ℝ)) (I' := IP)
        (f := fun x ↦ (0 : ℝ)) (g := fun x ↦ x)
        (ϕ := fun x ↦ (mfderiv% fun (t : ℝ) ↦ x <• expLie (IG := IG) (t • A)) 0)
        (hx := ChartedSpace.mem_chart_source (0 : ℝ))
        (hy := hx)
  rw [hrw]
  simp only [tangentBundleCore_coordChange, OpenPartialHomeomorph.extend, coe_achart,
   PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
     PartialEquiv.coe_trans_symm,
    OpenPartialHomeomorph.coe_coe_symm, ModelWithCorners.toPartialEquiv_coe_symm,
     Function.comp_apply,
     ContinuousLinearMap.coe_comp']
  simp only [modelWithCornersSelf_coe, OpenPartialHomeomorph.refl_partialEquiv,
   PartialEquiv.refl_source,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, OpenPartialHomeomorph.refl_apply,
     CompTriple.comp_eq,
    OpenPartialHomeomorph.refl_symm, modelWithCornersSelf_coe_symm, range_id, id_eq,
     fderivWithin_univ, fderiv_id,
    ContinuousLinearMap.coe_id']
  rfl

lemma fundamentalVectorField_zero_iff (p : P) (A : GroupLieAlgebra IG G)
    [MulAction Gᵐᵒᵖ P]
    (ρ : P → B)
    [IsPrincipalBundle G P B ρ IP IB]
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    [SmoothRightGAction ∞ IG IP G P]
    [T2Space P] [BoundarylessManifold IP P] :
    fundamentalVectorField (HP := HP) (IP := IP) A p = 0 → A = 0 := by
  intro h
  have hconst : ∀ (t : ℝ), p <• expLie (IG := IG) (t • A) = p := by
    have hcurve : IsMIntegralCurve (I := IP) (fun t ↦ p <• expLie (IG := IG) (t • A))
      (fun q : P ↦ fundamentalVectorField (HP := HP) (IP := IP) A q) :=
      isMIntegralCurve_action_expLie p A
    have hconstcurve : IsMIntegralCurve (I := IP) (fun _ : ℝ ↦ p)
        (fun q : P ↦ fundamentalVectorField (HP := HP) (IP := IP) A q) :=
      isMIntegralCurve_const h
    have heq : (fun (t : ℝ) ↦ p <• expLie (IG := IG) (t • A)) = (fun _ ↦ p) := by
      apply isMIntegralCurve_eq_of_contMDiff (t₀ := 0)
          (fun _ ↦ BoundarylessManifold.isInteriorPoint (I := IP))
      · exact (contMDiff_fundamentalVectorField (P := P) (IP := IP) A).of_le (by norm_num)
      · exact hcurve
      · exact hconstcurve
      · simp [expLie_zero]
    exact fun t ↦ congr_fun heq t
  have hexp : ∀ (t : ℝ), expLie (IG := IG) (t • A) = 1 := by
    intro t
    have := IsPrincipalBundle.is_free (ρ := ρ) (IP := IP) (IB := IB) p (expLie (t • A))
    exact this (hconst t)
  have := mfderiv_expLie (IG := IG) A
  rw [show (fun t : ℝ ↦ expLie (IG := IG) (t • A)) = (fun _ ↦ (1 : G)) from
      funext hexp] at this
  simp [mfderiv_const] at this
  exact this.symm

lemma fundamentalVectorField_injective (p : P)
    [MulAction Gᵐᵒᵖ P]
    (ρ : P → B)
    [IsPrincipalBundle G P B ρ IP IB]
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    [SmoothRightGAction ∞ IG IP G P]
    [T2Space P] [BoundarylessManifold IP P] :
    Function.Injective
      (fun A : GroupLieAlgebra IG G ↦ fundamentalVectorField (HP := HP) (IP := IP) A p) := by
  intro A B h
  have hab : fundamentalVectorField (HP := HP) (IP := IP) (A - B) p = 0 := by
    have h1 := (fundamentalVectorFieldLinearMap (IP := IP) p).map_sub A B
    simp only [fundamentalVectorFieldLinearMap, LinearMap.coe_mk, AddHom.coe_mk] at h1
    simp only at h
    have h2 : fundamentalVectorField (HP := HP) (IP := IP) (A - B) p = 0 := by
      rw [h1]
      exact sub_eq_zero_of_eq h
    exact h2
  have hAB := fundamentalVectorField_zero_iff (IB := IB) p (A - B) (ρ := ρ) hab
  exact sub_eq_zero.mp hAB

end

section

open RightActions

variable
  [MulAction (MulOpposite G) P]
  (ρ : P → B)
  [IsPrincipalBundle G P B ρ IP IB]

/-- The Yang-Mills field associated to a local section `σ` of the principal bundle `ρ : P → B`
    and a connection 1-form `ω` on `P`.

    Given a smooth local section `σ : U → P` over an open set `U ⊆ B`, the Yang-Mills field
    is the pullback `σ*ω` of the connection 1-form along `σ`. At each point `m ∈ U` it is
    the Lie-algebra-valued linear map:

        (σ*ω)_m : T_mB → g
        v ↦ ω_{σ(m)}(dσ_m(v))

    i.e. first push forward `v ∈ T_mB` to `T_{σ(m)}P` via the differential `dσ_m`, then
    apply the connection form `ω_{σ(m)}`.

    In physics, this is the local gauge field or Yang-Mills potential on `U`, and it encodes
    all the local information of the connection on the trivialised patch `U`. -/
noncomputable def yangMillsField
    [MulAction (MulOpposite G) P]
    [T2Space G]
    [CompleteSpace EG]
    [BoundarylessManifold IG G]
    (ρ : P → B)
    [IsPrincipalBundle G P B ρ IP IB]
    (τ : ConnectionForm (G := G) (IG := IG) (P := P) (IP := IP) (EP := EP))
    (σ : B → P) :
    ∀ m : B, TangentSpace IB m →L[ℝ] GroupLieAlgebra IG G :=
    letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
      show NormedAddCommGroup EG from inferInstance
    letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
      show NormedSpace ℝ EG from inferInstance
    fun m ↦ (τ.form.toFun (σ m)).comp (mfderiv IB IP σ m)

/-- The Maurer-Cartan form on a Lie group `G`. At each point `g : G` it is the differential
    of left multiplication by `g⁻¹`, mapping `T_gG → T_eG = g`.

    Concretely, `Ξ_g(v) = d(L_{g⁻¹})_g(v)` where `L_{g⁻¹} : G → G` is `h ↦ g⁻¹ * h`.

    The Maurer-Cartan form is the unique left-invariant `g`-valued 1-form on `G` satisfying
    `Ξ_e = id`. -/
noncomputable def maurerCartan (g : G) : TangentSpace IG g →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h ↦ g⁻¹ * h) g

def IsLocalSection (σ : B → P) (U : Set B) : Prop :=
  IsOpen U ∧
  ContMDiffOn IB IP ∞ σ U ∧
  ∀ m ∈ U, ρ (σ m) = m

omit [IsManifold IP ∞ P] in
lemma gaugeMap_exists
    (σ₁ σ₂ : B → P)
    (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (HP := HP) (EP := EP) (IB := IB) (IP := IP) ρ σ₁ U₁)
    (hσ₂ : IsLocalSection (HP := HP) (EP := EP) (IB := IB) (IP := IP) ρ σ₂ U₂)
    (m : B) (hm : m ∈ U₁ ∩ U₂) :
    ∃ g : G, σ₂ m = σ₁ m <• g := by
  have h1 : ρ (σ₁ m) = m := hσ₁.2.2 m hm.1
  have h2 : ρ (σ₂ m) = m := hσ₂.2.2 m hm.2
  exact (IsPrincipalBundle.is_transitive (G := G) IP IB m (σ₁ m) (σ₂ m) h1 h2).imp
    (fun g hg ↦ hg.symm)

omit [IsManifold IP ∞ P] in
lemma gaugeMap_unique
    (ρ : P → B)
    [IsPrincipalBundle G P B ρ IP IB]
    (σ₁ σ₂ : B → P)
    (m : B) (g h : G)
    (hg : σ₁ m <• g = σ₂ m)
    (hh : σ₁ m <• h = σ₂ m) :
    g = h := by
  have heq : σ₁ m <• g = σ₁ m <• h := hg.trans hh.symm
  have hfree := IsPrincipalBundle.is_free (ρ := ρ) (IP := IP) (IB := IB) (σ₁ m) (g * h⁻¹)
  have haction : σ₁ m <• (g * h⁻¹) = σ₁ m := by
    simp only [MulOpposite.op_mul, mul_smul]
    rw [heq]
    simp only [MulOpposite.op_inv, inv_smul_smul]
  have hone : g * h⁻¹ = 1 := hfree haction
  exact eq_of_mul_inv_eq_one hone

/-- Theorem 22.6 (Schuller) / Theorem 1.2.5 (Bleecker): The transformation law for
    Yang-Mills fields. Given two local sections σ₁, σ₂ of the principal bundle and
    the gauge map Ω defined by σ₁(m) ◁ Ω(m) = σ₂(m), the Yang-Mills fields satisfy:

        ω^{U₂}(v) = Ad_{Ω⁻¹}(ω^{U₁}(v)) + Ξ_{Ω(m)}(dΩ_m(v)) -/
theorem yangMills_transformation
    (ρ : P → B) [IsPrincipalBundle G P B ρ IP IB]
    [SmoothRightGAction ∞ IG IP G P]
    [T2Space G]
    [CompleteSpace EG]
    [BoundarylessManifold IG G]
    (τ : ConnectionForm (IP := IP))
    (σ₁ σ₂ : B → P) (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IP := IP) (IB := IB) ρ σ₁ U₁)
    (hσ₂ : IsLocalSection (IP := IP) (IB := IB) ρ σ₂ U₂)
    (Ω : B → G) (hΩ : ∀ m ∈ U₁ ∩ U₂, σ₁ m <• Ω m = σ₂ m)
    (m : B) (hm : m ∈ U₁ ∩ U₂) (v : TangentSpace IB m) :
    yangMillsField ρ τ σ₂ m v =
      Ad (Ω m)⁻¹ (yangMillsField ρ τ σ₁ m v) +
      maurerCartan (Ω m) (mfderiv IB IG Ω m v) := by
  sorry

end

-- #check FiberBundleCore
-- #check PrincipalBundleCore

-- #check @FiberBundleCore
-- example (ι B G : Type*) [TopologicalSpace B] [TopologicalSpace G]
--     (Z : FiberBundleCore ι B G) : FiberBundle G Z.Fiber := by
--   exact Z.fiberBundle

#check @FiberBundleCore.fiberBundle
#check @FiberBundleCore.Fiber
#check @FiberBundleCore.coordChange
#check @FiberBundleCore.mem_baseSet_at

#check @Bundle.TotalSpace
