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

#check ContMDiff.clm_bundle_apply₂

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
  -- [IsPrincipalBundle G P B ρ]
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

#check @LieAlgebraValuedOneForm

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

omit [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma expLie_zero
    [BoundarylessManifold IG G] [CompleteSpace EG] :
    expLie (0 : GroupLieAlgebra IG G) = 1 := by
  have hconst : IsMIntegralCurve (fun _ ↦ (1 : G))
               (mulInvariantVectorField (0 : GroupLieAlgebra IG G)) := by
    unfold mulInvariantVectorField
    apply isMIntegralCurve_const
    simp only [map_zero]
    exact rfl
  have hγ := (IsMIntegralCurve.exists_global (0 : GroupLieAlgebra IG G)).choose_spec
  have heq : (fun _ : ℝ ↦ (1 : G)) =
             (IsMIntegralCurve.exists_global (0 : GroupLieAlgebra IG G)).choose :=
    IsMIntegralCurve.unique_global 0 _ _ hconst hγ.2 rfl hγ.1
  have := congr_fun heq 1
  simp only [expLie] at this ⊢
  exact this.symm

omit [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma expLie_add (A : GroupLieAlgebra IG G) (s t : ℝ)
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] :
    expLie (IG := IG) ((s + t) • A) = expLie (IG := IG) (s • A) * expLie (IG := IG) (t • A) :=
  IsMIntegralCurve.mul _ A (isMIntegralCurve_expLie_smul A)
    (by simp only [zero_smul]; exact expLie_zero) s t

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

#check mfderiv_comp

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

#check IsMIntegralCurveOn.comp_add
#check IsMIntegralCurve.mul

example (p : P) (g h : G) [MulAction Gᵐᵒᵖ P] : p <• (g * h) = (p <• g) <• h := by
  simp only [MulOpposite.op_mul, mul_smul]

example (p : P) (g h : G) [MulAction Gᵐᵒᵖ P] : p <• (g * h) = (p <• g) <• h := by
  show MulOpposite.op (g * h) •> p = MulOpposite.op h •> (MulOpposite.op g •> p)
  rw [MulOpposite.op_mul, mul_smul]

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
  simp?
  have hrw := inTangentCoordinates_eq (I := 𝓘(ℝ, ℝ)) (I' := IP)
        (f := fun x ↦ (0 : ℝ)) (g := fun x ↦ x)
        (ϕ := fun x ↦ (mfderiv% fun (t : ℝ) ↦ x <• expLie (IG := IG) (t • A)) 0)
        (hx := ChartedSpace.mem_chart_source (0 : ℝ))
        (hy := hx)
  rw [hrw]
  simp?
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
  -- The curve fun t ↦ p <• expLie (t • A) has zero derivative at 0
  -- so it's an integral curve of the zero vector field
  -- The constant curve fun t ↦ p is also an integral curve of the zero vector field
  -- By uniqueness, p <• expLie (t • A) = p for all t
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
      · -- hv: smoothness of fun q ↦ ⟨q, fundamentalVectorField A q⟩
        exact (contMDiff_fundamentalVectorField (P := P) (IP := IP) A).of_le (by norm_num)
      · exact hcurve
      · exact hconstcurve
      · simp [expLie_zero]
    exact fun t ↦ congr_fun heq t
  -- By freeness, expLie (t • A) = 1 for all t
  have hexp : ∀ (t : ℝ), expLie (IG := IG) (t • A) = 1 := by
    intro t
    have := IsPrincipalBundle.is_free (ρ := ρ) (IP := IP) (IB := IB) p (expLie (t • A))
    exact this (hconst t)
  -- Differentiate at t = 0 using mfderiv_expLie to get A = 0
  have := mfderiv_expLie (IG := IG) A
  rw [show (fun t : ℝ ↦ expLie (IG := IG) (t • A)) = (fun _ ↦ (1 : G)) from
      funext hexp] at this
  simp [mfderiv_const] at this
  exact this.symm

lemma fundamentalVectorField_injective (p : P)
  [MulAction Gᵐᵒᵖ P] [T2Space G] [CompleteSpace EG] [ BoundarylessManifold IG G] :
    Function.Injective
      (fun A : GroupLieAlgebra IG G ↦ fundamentalVectorField (HP := HP) (IP := IP) A p) := by
  intro A B h
  unfold fundamentalVectorField at h
  have hg : MDiffAt (fun g : G ↦ p <• g) ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := sorry
  have hf : MDiffAt (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 := sorry
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
    simp [this]
    have h3 : ((mfderiv% fun (t : ℝ) ↦ expLie (IG := IG) (t • A)) 0) 1 = A :=
      mfderiv_expLie (IG := IG) A
    change (((mfderiv% fun (g : G) ↦ p <• g) 1).comp
      ((mfderiv% fun (t : ℝ) ↦ expLie (IG := IG) (t • A)) 0)) 1 =
      ((mfderiv% fun (g : G) ↦ p <• g) 1) A
    rw [ContinuousLinearMap.comp_apply]
    exact Eq.symm (DFunLike.congr rfl (id (Eq.symm h3)))
  -- Apply chain rule to both sides
  -- fun t ↦ p <• expLie (t • A) = (fun g ↦ p <• g) ∘ (fun t ↦ expLie (t • A))
  have hA : mfderiv 𝓘(ℝ, ℝ) IP (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 1 =
      mfderiv IG IP (fun g : G ↦ p <• g) 1
        (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 1) := by
    have hcomp : mfderiv 𝓘(ℝ, ℝ) IP (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 =
        (mfderiv IG IP (fun g : G ↦ p <• g) 1).comp
          (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
      rw [show (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) =
              (fun g : G ↦ p <• g) ∘ (fun t ↦ expLie (IG := IG) (t • A)) from rfl]
      exact sorry -- mfderiv_comp 0 (sorry) (sorry)
    simp [hcomp]
    exact sorry
  have hA : mfderiv 𝓘(ℝ, ℝ) IP (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A)) 0 1 =
    mfderiv IG IP (fun g : G ↦ p <• g) (expLie (IG := IG) ((0 : ℝ) • A))
      (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0 1) := by
    rw [← mfderiv_comp (0 : ℝ) (sorry) (sorry)]
    rfl
  have hB : mfderiv 𝓘(ℝ, ℝ) IP (fun t : ℝ ↦ p <• expLie (IG := IG) (t • B)) 0 1 =
    mfderiv IG IP (fun g : G ↦ p <• g) (expLie (IG := IG) ((0 : ℝ) • B))
      (mfderiv 𝓘(ℝ, ℝ) IG (fun t : ℝ ↦ expLie (IG := IG) (t • B)) 0 1) := by
    rw [← mfderiv_comp (0 : ℝ) (sorry) (sorry)]
    rfl
  rw [zero_smul, expLie_zero, mfderiv_expLie, mfderiv_expLie] at hA hB
  -- Now hA : mfderiv IP IP (· <• 1) p A = ...
  -- and the right action by 1 is identity
  have hone : ∀ q : P, q <• (1 : G) = q := MulAction.one_smul
  sorry

end

example (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ ↦ t • a) :=
  (contDiff_id.smul_const a).contMDiff

example (a : GroupLieAlgebra IG G) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) ∞ (fun t : ℝ ↦ t • (show EG from a)) :=
  (contDiff_id.smul_const (show EG from a)).contMDiff

example : ModelWithCorners ℝ EG HG := IG

#check @TangentSpace
#check mfderiv_comp (0 : ℝ)
#check LieAlgebra.ad
#check MulAut.conj
#check SmoothRightGAction.smooth_smul
#check contDiff_id.smul_const
#check ContinuousLinearMap.smulRight
#check (inferInstance : ChartedSpace EG EG)
