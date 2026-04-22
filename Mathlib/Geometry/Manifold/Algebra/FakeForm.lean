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
