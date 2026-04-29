/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import Mathlib.Geometry.Manifold.Algebra.SmoothLieExp
import Mathlib.Geometry.Manifold.Algebra.PrincipalGBundle

/-!
# Principal Bundles

A smooth principal G-bundle over a manifold B is a smooth fiber bundle π : P → B
with fiber G such that:
1. G acts smoothly and freely on the total space P on the right
2. The fiber-preserving local trivializations φ_U : π⁻¹(U) → U × G are G-equivariant,
   where G acts on U × G on the right by (x, h) · g = (x, hg)

Transitivity of the G-action on fibers is a consequence of equivariance and is proved
as a separate proposition.

## TODO: Equivalence of definitions

### Bleecker/Tu ↔ Wikipedia
The current definition (`IsPrincipalBundle`) follows Tu §27, Definition 27.1 and Bleecker
Definition 1.1.1, using G-equivariant local trivializations as the primary condition.
Wikipedia instead takes free and transitive fiber action as the definition and derives
equivariance. These are equivalent:

* `todo`: Prove `bleecker_implies_wikipedia`: the current definition implies that the map
  `G → π⁻¹(b)` sending `g ↦ p <• g` is a homeomorphism for each `p` in the fiber over `b`.
  Injectivity follows from `is_free`, surjectivity from `is_transitive` (already proved
  as `IsPrincipalBundle.is_transitive`, which is Lee Proposition 27.6 / Tu §27 / Schuller
  Remark 19.16), and continuity of the inverse requires additional argument.

* `todo`: Prove `wikipedia_implies_bleecker`: free and transitive fiber action on a fiber
  bundle implies the existence of G-equivariant local trivializations. This is the content
  of Wikipedia's remark that `φ(p · g) = φ(p)g` for trivializations defined by local
  sections. Likely requires `ParacompactSpace B` and `T2Space B`.

### Bleecker/Tu ↔ Schuller
Schuller (Remark 19.16) notes that his definition enforces fibre-wise transitivity via the
isomorphism condition, and that requiring free + transitive explicitly would be a slight
generalisation. The precise relationship is:

* `todo`: Prove that Schuller's isomorphism condition (the bundle isomorphism
  `P ≅ B × G` locally, equivariantly) is equivalent to `equivariant_triv`.

* `todo`: Formalize `PrincipalBundleMorphism` (Schuller's definition of morphisms between
  principal bundles, Definition 19.15) and prove that bundle isomorphisms in this category
  correspond exactly to equivariant local trivializations.

### General remark
All three definitions are expected to be equivalent under mild topological hypotheses
(Hausdorff, paracompact base). The chain of implications is:

  Bleecker/Tu (equivariant trivializations, Bleecker Def 1.1.1, Tu §27 Def 27.1)
      ↕
  Wikipedia (free + transitive + fiber bundle)
      ↕
  Schuller (isomorphism condition, Schuller Def 19.14 / Remark 19.16)

## Main definitions

* `IsPrincipalBundle`: A smooth fiber bundle with a free right G-action and
  G-equivariant local trivializations
* `ConnectionForm`: A g-valued 1-form on P satisfying the two connection axioms

## Main results

* `IsPrincipalBundle.is_transitive`: The G-action is transitive on each fiber

## References

* Tu, *Differential Geometry: Connections, Curvature, and Characteristic Classes*,
  Springer, 2017, §27
* Bleecker, *Gauge Theory and Variational Principles*, §1.2
-/

open Bundle RightActions
open Set Bundle ContDiff Manifold Trivialization

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
  {E : B → Type*}
  [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace G E)]
  [MulAction (MulOpposite G) (TotalSpace G E)]
  [ChartedSpace (ModelProd HB HG) (TotalSpace G E)]
  [IsManifold (IB.prod IG) ∞ (TotalSpace G E)]
  [SmoothRightGAction ∞ IG (IB.prod IG) G (TotalSpace G E)]
  [FiberBundle G E]

instance [LieGroup IG ∞ G] : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)

/-- A smooth principal G-bundle over B is a smooth fiber bundle π : P → B with fiber G
    such that G acts smoothly and freely on the total space on the right, and the local
    trivializations are G-equivariant. Following Tu, §27, Definition 27.1.

    Note: Transitivity of the G-action on fibers follows from equivariance of the
    trivializations and is proved as `IsPrincipalBundle.is_transitive`. -/
class IsPrincipalBundle
    (G : Type*) [TopologicalSpace G] [ChartedSpace HG G] [Group G] [LieGroup IG ∞ G]
    (E : B → Type*)
    [∀ b, TopologicalSpace (E b)]
    [TopologicalSpace (TotalSpace G E)]
    [MulAction (MulOpposite G) (TotalSpace G E)]
    [ChartedSpace (ModelProd HB HG) (TotalSpace G E)]
    [IsManifold (IB.prod IG) ∞ (TotalSpace G E)]
    [SmoothRightGAction ∞ IG (IB.prod IG) G (TotalSpace G E)]
    [FiberBundle G E] where
  /-- The right G-action is free: only the identity fixes any point -/
  is_free : ∀ (p : TotalSpace G E),
    MulAction.stabilizer (MulOpposite G) p = ⊥
  /-- The right G-action preserves fibers: if p is in the fiber over b, so is p <• g -/
  respects_fibres : ∀ (p : TotalSpace G E) (g : G), (p <• g).proj = p.proj
  /-- The local trivializations are G-equivariant -/
  equivariant_triv : ∀ (p : TotalSpace G E) (g : G),
    (trivializationAt G E p.proj) (p <• g) =
      ⟨p.proj, ((trivializationAt G E p.proj) p).2 * g⟩
  /-- The projection map `π : TotalSpace G E → B` is smooth as a map between manifolds. -/
  smooth_proj : ContMDiff (IB.prod IG) IB ∞ (fun p : TotalSpace G E ↦ p.proj)

/-
In a principal G-bundle, G acts transitively on each fiber.
    This follows from equivariance of the local trivializations:
    given p, q in the fiber over b, the element g = h₁⁻¹ * h₂ (where h₁, h₂ are the
    fiber coordinates under the local trivialization) satisfies p <• g = q.
-/
omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
     [FiberBundle G E] in
theorem IsPrincipalBundle.is_transitive
    [FiberBundle G E]
    [IsPrincipalBundle (IB := IB) (IG := IG) G E]
    (b : B) (p q : TotalSpace G E)
    (hp : p.proj = b) (hq : q.proj = b) :
    q ∈ MulAction.orbit (MulOpposite G) p := by
  -- Let φ be the trivialization at b, and h₁, h₂ the fiber coordinates of p, q
  set φ := trivializationAt G E b with hφ
  set g := (φ p).2⁻¹ * (φ q).2
  -- Witness the orbit membership with g = h₁⁻¹ * h₂
  refine ⟨MulOpposite.op g, φ.injOn ?_ ?_ ?_⟩
  · -- p <• g is in φ.source
    rw [Trivialization.mem_source]
    have := IsPrincipalBundle.respects_fibres (IB := IB) (IG := IG) p g
    rw [this, hp]
    exact mem_baseSet_trivializationAt G E b
  · -- q is in φ.source
    exact φ.mem_source.mpr (hq ▸ mem_baseSet_trivializationAt G E b)
  · -- φ(p <• g) = φ(q) by equivariance and mul_inv_cancel_left
    have heq := IsPrincipalBundle.equivariant_triv (IB := IB) (IG := IG) p g
    rw [hp] at heq
    simp only [Trivialization.coe_coe] at heq ⊢
    rw [heq, show g = (φ p).2⁻¹ * (φ q).2 from rfl, mul_inv_cancel_left]
    have hq_src : q ∈ φ.source := φ.mem_source.mpr (hq ▸ mem_baseSet_trivializationAt G E b)
    rw [← hq, ← φ.coe_fst hq_src, Prod.mk.eta]

noncomputable def fundamentalVectorField
    [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
    (A : GroupLieAlgebra IG G)
    (p : TotalSpace G E) :
    TangentSpace (IB.prod IG) p :=
  haveI : LieGroup IG (minSmoothness ℝ 3) G := LieGroup.of_le (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
  mfderiv 𝓘(ℝ, ℝ) (IB.prod IG)
    (fun t : ℝ ↦ p <• expLie (IG := IG) (t • A))
    (0 : ℝ) 1

noncomputable def Ad (g : G) : GroupLieAlgebra IG G →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h : G ↦ g * h * g⁻¹) 1

def LieAlgebraValuedOneForm :=
  letI : NormedAddCommGroup (TangentSpace IG (1 : G)) :=
    show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (TangentSpace IG (1 : G)) :=
    show NormedSpace ℝ EG from inferInstance
  Cₛ^∞⟮IB.prod IG; (EB × EG) →L[ℝ] GroupLieAlgebra IG G,
    fun _p : TotalSpace G E ↦ (EB × EG) →L[ℝ] GroupLieAlgebra IG G⟯

structure ConnectionForm where
  /-- The underlying Lie-algebra-valued 1-form -/
  form : LieAlgebraValuedOneForm (G := G) (IG := IG) (IB := IB) (E := E)
  /-- On fundamental vector fields, ω reproduces the Lie algebra element -/
  reproduces_fundamental :
    letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
      show NormedAddCommGroup EG from inferInstance
    letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
      show NormedSpace ℝ EG from inferInstance
    ∀ (p : TotalSpace G E) (A : GroupLieAlgebra IG G),
    form.toFun p (fundamentalVectorField (IB := IB) (IG := IG) A p) = A
  /-- Equivariance: R_g^* ω = Ad_{g⁻¹} ∘ ω -/
  equivariant :
    letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
      show NormedAddCommGroup EG from inferInstance
    letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
      show NormedSpace ℝ EG from inferInstance
    ∀ (p : TotalSpace G E) (g : G) (v : TangentSpace (IB.prod IG) p),
    form.toFun (p <• g) (mfderiv (IB.prod IG) (IB.prod IG) (· <• g) p v) =
      Ad g⁻¹ (form.toFun p v)

variable
  [IsPrincipalBundle (IG := IG) (IB := IB) G E]

omit [IsManifold IB ∞ B] in
lemma fundamentalVectorField_mem_vertical
    (A : GroupLieAlgebra IG G) (p : TotalSpace G E) :
    mfderiv (IB.prod IG) IB (fun p : TotalSpace G E ↦ p.proj) p
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
        (fun p : TotalSpace G E × G => p.1 <• p.2) :=
        (SmoothRightGAction.smooth_smul (n := ∞) (I_G := IG) (I_M := IB.prod IG) (G := G)
          (M := TotalSpace G E)).of_le
            (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)
      exact hsmul.comp hprod
    exact h3.mdifferentiableAt (by norm_num)
  have heval : (fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = p := by
    simp [expLie_zero]
  have h121 : MDifferentiableAt (IB.prod IG) IB (fun p : TotalSpace G E ↦ p.proj)
    ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0) := by
    rw [heval]
    exact (IsPrincipalBundle.smooth_proj (G := G) (E := E)).mdifferentiableAt (by norm_num)
  have h121 : MDifferentiableAt (IB.prod IG) IB (fun p : TotalSpace G E ↦ p.proj)
    ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0) := by
    rw [heval]
    exact (IsPrincipalBundle.smooth_proj (G := G) (IB := IB) (IG := IG) (E := E)).mdifferentiableAt
      (by norm_num)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) IB ((fun p : TotalSpace G E ↦ p.proj) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) 0 =
      (mfderiv (IB.prod IG) IB (fun p : TotalSpace G E ↦ p.proj)
        ((fun (t : ℝ) ↦ p <• expLie (t • A)) 0)).comp
          (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun (t : ℝ) ↦ p <• expLie (t • A)) 0) :=
    mfderiv_comp (0 : ℝ) h121 h118
  have hconst : ((fun p : TotalSpace G E ↦ p.proj) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) = fun _ ↦ p.proj := by
    ext t
    exact IsPrincipalBundle.respects_fibres IB IG p (expLie (t • A))
  have hzero : mfderiv% ((fun p : TotalSpace G E ↦ p.proj) ∘
      fun (t : ℝ) ↦ p <• expLie (t • A)) 0 = 0 := by
    rw [hconst]
    exact mfderiv_const
  rw [heval] at hcomp
  rw [hzero] at hcomp
  have key : (mfderiv (IB.prod IG) IB (fun p : TotalSpace G E ↦ p.proj) p).comp
      (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0) = 0 := by
    rw [← hcomp]; exact rfl
  calc mfderiv (IB.prod IG) IB (fun p : TotalSpace G E ↦ p.proj) p
        (mfderiv 𝓘(ℝ, ℝ) (IB.prod IG) (fun t : ℝ ↦ p <• expLie (t • A)) 0 1)
      = ((mfderiv (IB.prod IG) IB (fun p : TotalSpace G E ↦ p.proj) p).comp
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
     [(b : B) → TopologicalSpace (E b)] [FiberBundle G E] in
lemma fundamentalVectorField_eq_mfderiv_action (p : TotalSpace G E) :
    ∀ (A : GroupLieAlgebra IG G),
    fundamentalVectorField (IB := IB) (IG := IG) A p =
    mfderiv IG (IB.prod IG) (fun g : G ↦ p <• g) 1 A := by
  intro A
  have hg : MDifferentiableAt IG (IB.prod IG) (fun g : G ↦ p <• g)
      ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) := by
    have h0 : ((fun t : ℝ ↦ expLie (IG := IG) (t • A)) 0) = 1 := by
      simp [zero_smul, expLie_zero]
    rw [h0]
    have := (SmoothRightGAction.smooth_smul (n := ∞) (I_G := IG) (I_M := IB.prod IG)
      (G := G) (M := TotalSpace G E))
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

end
