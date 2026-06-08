/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import Mathlib.Geometry.Manifold.Algebra.ExpLie
import Mathlib.Geometry.Manifold.Algebra.SmoothRightGAction

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

noncomputable section Warmup

/-!
## Warmup: Sections, forms, and their pairing

Before developing the theory of principal bundles, we warm up by working with smooth
sections of vector bundles in a simpler setting. We define vector fields, 1-forms, and
2-forms as smooth sections of the appropriate bundles over `B`, and study the pairing
of a 1-form with a vector field to produce a smooth real-valued function.

The main technical exercise is `apply_smooth''`: showing that the pointwise pairing
`b ↦ w b (X b)` is smooth as a map `B → ℝ`.

This machinery will be needed later when working with connection forms, which are
Lie-algebra-valued 1-forms on the total space of a principal bundle.
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

instance [LieGroup IG ∞ G] : LieGroup IG (minSmoothness ℝ 3) G :=
  LieGroup.of_le (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)

-- TODO: Generalize equivariant_triv to work for any trivialization e in the atlas,
-- not just trivializationAt. This would allow proving contMDiffAt_gaugeMap without
-- assuming smoothness of Ω as a hypothesis. The current statement:
--   equivariant_triv : ∀ (p : TotalSpace G E) (g : G),
--     (trivializationAt G E p.proj) (p <• g) = ⟨p.proj, ((trivializationAt G E p.proj) p).2 * g⟩
-- should become:
--   equivariant_triv : ∀ (e : Trivialization G TotalSpace.proj) [MemTrivializationAtlas e]
--     (p : TotalSpace G E) (g : G), e (p <• g) = ⟨p.proj, (e p).2 * g⟩

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

/-- The fundamental vector field `A#` associated to a Lie algebra element `A ∈ 𝔤` and a
point `p` in the total space of a principal `G`-bundle. It is defined as the tangent
vector at `t = 0` of the curve `t ↦ p ▷ exp(tA)`, i.e. the infinitesimal generator of
the one-parameter subgroup `{exp(tA)}` acting on `p` from the right.

This is Tu §27, Definition 27.8 and Bleecker §1.3. -/
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

/-- The adjoint representation `Ad_g : 𝔤 → 𝔤` of `g : G`, defined as the derivative at
the identity of conjugation `h ↦ g * h * g⁻¹`. This gives a smooth group homomorphism
`Ad : G → GL(𝔤)`, the adjoint representation of `G` on its Lie algebra. -/
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
        (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG) (G := G)
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
     [(b : B) → TopologicalSpace (E b)] [FiberBundle G E]
     [IsManifold (IB.prod IG) ∞ (TotalSpace G E)] in
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
    have := (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
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

noncomputable def fundamentalVectorFieldLinearMap (p : TotalSpace G E) :
    GroupLieAlgebra IG G →ₗ[ℝ] TangentSpace (IB.prod IG) p where
  toFun A := fundamentalVectorField (IB := IB) (IG := IG) A p
  map_add' A B := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_add]
    exact rfl
  map_smul' r A := by
    simp only [fundamentalVectorField_eq_mfderiv_action, map_smul, RingHom.id_apply]
    exact rfl

omit [IsManifold IB ∞ B] in
/-- The curve `t ↦ p <• expLie (t • A)` is an integral curve of the fundamental vector field
`fun q ↦ fundamentalVectorField A q` on the principal bundle `P`.

This is Proposition 27.14 from Tu, *Differential Geometry: Connections, Curvature, and
Characteristic Classes*, Springer, 2017.

TODO: A dog's dinner — maybe a more direct proof would use the fact that
the curve is the composition of the smooth right action with the one-parameter subgroup
`t ↦ expLie (t • A)`, and differentiate directly using the chain rule.
-/
lemma isMIntegralCurve_action_expLie (p : TotalSpace G E) (A : GroupLieAlgebra IG G) :
    IsMIntegralCurve (I := IB.prod IG) (fun t ↦ p <• expLie (IG := IG) (t • A))
      (fun q : TotalSpace G E ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) := by
  intro t
  have hflow : (fun s : ℝ ↦ p <• expLie (IG := IG) ((t + s) • A)) =
               (fun s : ℝ ↦ (p <• expLie (IG := IG) (t • A)) <• expLie (IG := IG) (s • A)) := by
    ext s
    · simp [IsPrincipalBundle.respects_fibres IB IG]
    · have : expLie (IG := IG) ((t + s) • A) =
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
      (G := G) (M := TotalSpace G E)).of_le
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

omit [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
     [(b : B) → TopologicalSpace (E b)] [FiberBundle G E] in
lemma contMDiff_fundamentalVectorField (A : GroupLieAlgebra IG G) :
    ContMDiff (IB.prod IG) (IB.prod IG).tangent (minSmoothness ℝ 1)
      (fun p : TotalSpace G E ↦ (⟨p, fundamentalVectorField (IB := IB) (IG := IG) A p⟩ :
        TangentBundle (IB.prod IG) (TotalSpace G E))) := by
  haveI : IsManifold (IB.prod IG) 1 (TotalSpace G E) := IsManifold.of_le (n := ∞) (by norm_num)
  have hsmooth : ContMDiff ((IB.prod IG).prod 𝓘(ℝ, ℝ)) (IB.prod IG) (minSmoothness ℝ 2)
      (fun (q : TotalSpace G E × ℝ) ↦ q.1 <• expLie (IG := IG) (q.2 • A)) := by
    have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EG) (minSmoothness ℝ 2)
        (fun t : ℝ ↦ t • (show EG from A)) :=
      ((contDiff_id.smul_const (show EG from A)).contMDiff).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact Std.IsPreorder.le_refl 2)
    have h2 : ContMDiff 𝓘(ℝ, ℝ) IG (minSmoothness ℝ 2)
        (fun t : ℝ ↦ expLie (IG := IG) (t • A)) :=
      contMDiff_expLie.comp h1
    exact ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := TotalSpace G E)).of_le
        (by simp only [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out)).comp
      (contMDiff_fst.prodMk (h2.comp (contMDiff_snd (I := IB.prod IG) (J := 𝓘(ℝ, ℝ)))))
  intro q
  have hq := ContMDiffAt.mfderiv
    (N := TotalSpace G E) (M := ℝ) (M' := TotalSpace G E)
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
  [T2Space (TotalSpace G E)]
  [BoundarylessManifold (IB.prod IG) (TotalSpace G E)]

omit [IsManifold IB ∞ B] in
lemma fundamentalVectorField_zero_iff (p : TotalSpace G E) (A : GroupLieAlgebra IG G) :
    fundamentalVectorField (IB := IB) (IG := IG) A p = 0 → A = 0 := by
  intro h
  have hconst : ∀ (t : ℝ), p <• expLie (IG := IG) (t • A) = p := by
    have hcurve : IsMIntegralCurve (I := IB.prod IG) (fun t ↦ p <• expLie (IG := IG) (t • A))
        (fun q : TotalSpace G E ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) :=
      isMIntegralCurve_action_expLie p A
    have hconstcurve : IsMIntegralCurve (I := IB.prod IG) (fun _ : ℝ ↦ p)
        (fun q : TotalSpace G E ↦ fundamentalVectorField (IB := IB) (IG := IG) A q) :=
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
    have hfree := IsPrincipalBundle.is_free (IG := IG) (IB := IB) p
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

def IsLocalSection (σ : B → TotalSpace G E) (U : Set B) : Prop :=
  IsOpen U ∧
  ContMDiffOn IB (IB.prod IG) ∞ σ U ∧
  ∀ m ∈ U, (σ m).proj = m

omit [IsManifold IB ∞ B]
     [T2Space G]
     [CompleteSpace EG]
     [BoundarylessManifold IG G] in
lemma gaugeMap_exists
    (σ₁ σ₂ : B → TotalSpace G E)
    (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) σ₂ U₂)
    (m : B) (hm : m ∈ U₁ ∩ U₂) :
    ∃ g : G, σ₂ m = σ₁ m <• g := by
  have h1 : (σ₁ m).proj = m := hσ₁.2.2 m hm.1
  have h2 : (σ₂ m).proj = m := hσ₂.2.2 m hm.2
  have hmem := IsPrincipalBundle.is_transitive (IB := IB) (IG := IG) m (σ₁ m) (σ₂ m) h1 h2
  rw [MulAction.mem_orbit_iff] at hmem
  obtain ⟨g, hg⟩ := hmem
  exact ⟨MulOpposite.unop g, by rw [← hg]; simp [HSMul.hSMul]⟩

set_option linter.unusedSectionVars false in
omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G] in
lemma gaugeMap_unique
    [IsPrincipalBundle (IG := IG) (IB := IB) G E]
    (σ₁ σ₂ : B → TotalSpace G E)
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
  rw [IsPrincipalBundle.is_free IB IG (σ₁ m)] at hone
  exact eq_of_mul_inv_eq_one (MulOpposite.op_injective hone)

/-- The Maurer-Cartan form on a Lie group `G`. At each point `g : G` it is the differential
    of left multiplication by `g⁻¹`, mapping `T_gG → T_eG = g`.

    Concretely, `Ξ_g(v) = d(L_{g⁻¹})_g(v)` where `L_{g⁻¹} : G → G` is `h ↦ g⁻¹ * h`.

    The Maurer-Cartan form is the unique left-invariant `g`-valued 1-form on `G` satisfying
    `Ξ_e = id`. -/
noncomputable def maurerCartan (g : G) : TangentSpace IG g →L[ℝ] GroupLieAlgebra IG G :=
  mfderiv IG IG (fun h ↦ g⁻¹ * h) g

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
    (τ : ConnectionForm (G := G) (IG := IG) (IB := IB) (E := E))
    (σ : B → TotalSpace G E) :
    ∀ m : B, TangentSpace IB m →L[ℝ] GroupLieAlgebra IG G :=
  letI : NormedAddCommGroup (GroupLieAlgebra IG G) :=
    show NormedAddCommGroup EG from inferInstance
  letI : NormedSpace ℝ (GroupLieAlgebra IG G) :=
    show NormedSpace ℝ EG from inferInstance
  fun m ↦ (τ.form.toFun (σ m)).comp (mfderiv IB (IB.prod IG) σ m)

/- TODO: Probably should be somewhere else -/
omit [IsManifold IB ∞ B] [T2Space G] [CompleteSpace EG] [BoundarylessManifold IG G]
[(b : B) → TopologicalSpace (E b)] [FiberBundle G E]
[LieGroup IG ∞ G] [IsManifold (IB.prod IG) ∞ (TotalSpace G E)] in
lemma mfderiv_smul_section
    (m : B)
    (σ : B → TotalSpace G E) (Ω : B → G)
    (hσ : ContMDiffAt IB (IB.prod IG) ∞ σ m)
    (hΩ : ContMDiffAt IB IG ∞ Ω m)
    (v : TangentSpace IB m) :
    mfderiv IB (IB.prod IG) (fun x ↦ σ x <• Ω x) m v =
      mfderiv (IB.prod IG) (IB.prod IG) (· <• Ω m) (σ m) (mfderiv IB (IB.prod IG) σ m v) +
      mfderiv IG (IB.prod IG) (σ m <• ·) (Ω m) (mfderiv IB IG Ω m v) := by
  have hcomp : (fun x ↦ σ x <• Ω x) = (fun p : TotalSpace G E × G ↦ p.1 <• p.2) ∘
    (fun x ↦ (σ x, Ω x)) := rfl
  rw [hcomp]
  have hpair : ContMDiffAt IB ((IB.prod IG).prod IG) ∞ (fun x ↦ (σ x, Ω x)) m :=
    hσ.prodMk hΩ
  have hsmul : MDifferentiableAt ((IB.prod IG).prod IG) (IB.prod IG)
    (fun p : TotalSpace G E × G ↦ p.1 <• p.2) (σ m, Ω m) :=
      (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
        (G := G) (M := TotalSpace G E)).mdifferentiableAt (by norm_num)
  rw [mfderiv_comp m hsmul (hpair.mdifferentiableAt
       (by exact Ne.symm (not_eq_of_beq_eq_false rfl)))]
  have foo : ∀ w : TangentSpace ((IB.prod IG).prod IG) (σ m, Ω m),
      (mfderiv ((IB.prod IG).prod IG) (IB.prod IG)
        (fun p : TotalSpace G E × G ↦ p.1 <• p.2) (σ m, Ω m)) w =
      (mfderiv (IB.prod IG) (IB.prod IG) (fun z ↦ z <• Ω m) (σ m)) w.1 +
      (mfderiv IG (IB.prod IG) (fun z ↦ σ m <• z) (Ω m)) w.2 :=
    fun w ↦ mfderiv_prod_eq_add_apply hsmul
  have hsmul' : MDifferentiableAt ((IB.prod IG).prod IG) (IB.prod IG)
      (fun p : TotalSpace G E × G ↦ p.1 <• p.2) (σ m, Ω m) :=
    (SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := TotalSpace G E)).mdifferentiableAt (by norm_num)
  have hpair' : MDifferentiableAt IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m :=
    hpair.mdifferentiableAt (by norm_num)
  have key : mfderiv IB (IB.prod IG) (fun x ↦ σ x <• Ω x) m v =
      (mfderiv ((IB.prod IG).prod IG) (IB.prod IG)
        (fun p : TotalSpace G E × G ↦ p.1 <• p.2) (σ m, Ω m))
        (mfderiv IB ((IB.prod IG).prod IG) (fun x ↦ (σ x, Ω x)) m v) := by
    rw [hcomp, mfderiv_comp m hsmul' hpair']
    rfl
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
     [(b : B) → TopologicalSpace (E b)] [FiberBundle G E]
     [IsManifold (IB.prod IG) ∞ (TotalSpace G E)] in
lemma mfderiv_action_at_g (p : TotalSpace G E) (g : G) (w : TangentSpace IG g) :
    mfderiv IG (IB.prod IG) (p <• ·) g w =
      fundamentalVectorField (IB := IB) (IG := IG) (maurerCartan g w) (p <• g) := by
  rw [fundamentalVectorField_eq_mfderiv_action]
  have hdecomp : (fun g' : G ↦ p <• g') = (fun h : G ↦ (p <• g) <• h) ∘ (fun g' ↦ g⁻¹ * g') := by
    calc (fun g' : G ↦ p <• g') = (fun g' : G ↦ p <• (g * (g⁻¹ * g'))) := by
          simp [mul_inv_cancel_left]
      _ = (fun g' : G ↦ (p <• g) <• (g⁻¹ * g')) := by
          ext g'
          · have key : p <• (g * (g⁻¹ * g')) = (p <• g) <• (g⁻¹ * g') := by
              rw [← mul_smul, MulOpposite.op_mul]
            rw [key]
          · have : p <• (g * (g⁻¹ * g')) = (p <• g) <• (g⁻¹ * g') := by
                rw [← mul_smul, MulOpposite.op_mul]
            rw [this]
      _ = (fun h : G ↦ (p <• g) <• h) ∘ (fun g' ↦ g⁻¹ * g') := rfl
  have hLG : MDifferentiableAt IG IG (fun g' ↦ g⁻¹ * g') g :=
    (contMDiff_mul_left (a := g⁻¹) (n := ∞)).mdifferentiableAt (by norm_num)
  have hact : MDifferentiableAt IG (IB.prod IG) (fun h : G ↦ (p <• g) <• h) 1 :=
    ((SmoothRightGAction.smooth_smul (n := ∞) (IG := IG) (IM := IB.prod IG)
      (G := G) (M := TotalSpace G E)).comp
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

/-- The transition function between two local sections of a smooth principal bundle is smooth.
    TODO: prove this properly once `equivariant_triv` is generalized to all atlas trivializations.
    The proof would use `equivariant_triv` with `trivializationAt G E m` (which is in the atlas)
    applied to points x near m, together with `Bundle.Trivialization.contMDiffOn_of_fiberBundle`. -/
axiom contMDiffAt_gaugeMap
    (σ₁ σ₂ : B → TotalSpace G E)
    (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) σ₂ U₂)
    (Ω : B → G)
    (hΩ : ∀ x ∈ U₁ ∩ U₂, σ₁ x <• Ω x = σ₂ x)
    (m : B) (hm : m ∈ U₁ ∩ U₂) :
    ContMDiffAt IB IG ∞ Ω m

/- TODO: Probably put in its own section -/
omit [IsManifold IB ∞ B] [(b : B) → TopologicalSpace (E b)] [FiberBundle G E]
[IsManifold (IB.prod IG) ∞ (TotalSpace G E)] in
/-- Theorem 22.6 (Schuller) / Theorem 1.2.5 (Bleecker): The transformation law for
    Yang-Mills fields. Given two local sections σ₁, σ₂ of the principal bundle and
    the gauge map Ω defined by σ₁(m) ◁ Ω(m) = σ₂(m), the Yang-Mills fields satisfy:

        ω^{U₂}(v) = Ad_{Ω⁻¹}(ω^{U₁}(v)) + Ξ_{Ω(m)}(dΩ_m(v)) -/
theorem yangMills_transformation
    (τ : ConnectionForm (G := G) (IG := IG) (IB := IB) (E := E))
    (σ₁ σ₂ : B → TotalSpace G E) (U₁ U₂ : Set B)
    (hσ₁ : IsLocalSection (IB := IB) (IG := IG) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := IB) (IG := IG) σ₂ U₂)
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

section FrameBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

lemma isUnit_comp_iff_of_isUnit {D : E →L[𝕜] E} (hD : IsUnit D) (A : E →L[𝕜] E) :
    IsUnit (D.comp A) ↔ IsUnit A := by
  constructor <;> intro h;
  · obtain ⟨ u, hu ⟩ := h;
    obtain ⟨ v, hv ⟩ := hD;
    refine ⟨v⁻¹ * u, ?_⟩
    simp +decide only [Units.val_mul, hu]
    exact (Units.inv_mul_eq_iff_eq_mul v).mpr
      (congrFun (congrArg ContinuousLinearMap.comp (id (Eq.symm hv))) A)
  · exact hD.mul h

open Bundle FiberBundle

lemma isUnit_conj_iff (Φ : E ≃L[𝕜] E) (f : E →L[𝕜] E) :
    IsUnit (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap) ↔ IsUnit f := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨f, Φ.symm.toContinuousLinearMap ∘L u.inv ∘L Φ.toContinuousLinearMap, ?_, ?_⟩, rfl⟩
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.one_apply]
      have hf : f = Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap := by
        have : Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap =
               Φ.symm.toContinuousLinearMap ∘L
               (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap) ∘L
               Φ.toContinuousLinearMap := by
          rw [← hu]
        rw [this]
        ext w
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [hf]
      simp only [Units.inv_eq_val_inv, ContinuousLinearMap.coe_comp',
                 ContinuousLinearEquiv.coe_coe, Function.comp_apply,
                 ContinuousLinearEquiv.apply_symm_apply]
      have : u.val (u.inv (Φ v)) = Φ v := by
        have := congr_fun (congr_arg DFunLike.coe u.val_inv) (Φ v)
        exact this
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv :=
        Eq.symm (Units.inv_eq_val_inv u)
      rw [bar, this]
      exact ContinuousLinearEquiv.symm_apply_apply Φ v
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.one_apply]
      have hf : f = Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap := by
        have : Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap =
               Φ.symm.toContinuousLinearMap ∘L
               (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap)
               ∘L Φ.toContinuousLinearMap := by
          rw [← hu]
        rw [this]
        ext w
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [hf]
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
                 Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      have : u.inv (u.val (Φ v)) = Φ v := by
        exact congr_fun (congr_arg DFunLike.coe u.inv_val) (Φ v)
      rw [this]
      exact ContinuousLinearEquiv.symm_apply_apply Φ v
  · rintro ⟨u, hu⟩
    refine ⟨⟨Φ.toContinuousLinearMap ∘L u ∘L Φ.symm.toContinuousLinearMap,
             Φ.toContinuousLinearMap ∘L u.inv ∘L Φ.symm.toContinuousLinearMap, ?_, ?_⟩,
            by simp [← hu]⟩
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe]
      have : u.val (u.inv (Φ.symm v)) = Φ.symm v := by
        have := congr_fun (congr_arg DFunLike.coe u.val_inv) (Φ.symm v)
        have foo := this
        exact this
      simp only [Units.inv_eq_val_inv, ContinuousLinearEquiv.symm_apply_apply,
                 ContinuousLinearMap.one_apply]
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv := by
        exact Eq.symm (Units.inv_eq_val_inv u)
      rw [bar, this]
      exact ContinuousLinearEquiv.apply_symm_apply Φ v
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe]
      have : u.inv (u.val (Φ.symm v)) = Φ.symm v := by
        have := congr_fun (congr_arg DFunLike.coe u.inv_val) (Φ.symm v)
        have foo := this
        exact this
      simp only [Units.inv_eq_val_inv, ContinuousLinearEquiv.symm_apply_apply,
                 ContinuousLinearMap.one_apply]
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv := by
        exact Eq.symm (Units.inv_eq_val_inv u)
      rw [bar]
      rw [this]
      exact ContinuousLinearEquiv.apply_symm_apply Φ v

instance : ∀ (p : TotalSpace (E →L[𝕜] E) fun x ↦ Trivial M E x →L[𝕜] TangentSpace I x),
  Monoid (Trivial M E p.proj →L[𝕜] TangentSpace I p.proj) := by
    intro p
    change Monoid (E →L[𝕜] E)
    haveI : Monoid (E →L[𝕜] E) := inferInstance
    exact ContinuousLinearMap.monoidWithZero.toMonoid

instance : ∀ (p : TotalSpace (E →L[𝕜] E) fun (x : M) ↦ TangentSpace I x →L[𝕜] E),
  Monoid (TangentSpace I p.proj →L[𝕜] E) := by
  intro p
  change Monoid (E →L[𝕜] E)
  haveI : Monoid (E →L[𝕜] E) := inferInstance
  exact ContinuousLinearMap.monoidWithZero.toMonoid

/-- The frame bundle of a smooth manifold `M` is the open subset of the
    Hom bundle `Hom(TM, TM)` consisting of invertible elements.
    Requires `M` to be a `C^∞` manifold to give the frame bundle a `C^∞` structure.
    (A `C^(n+1)` base gives a `C^n` frame bundle.) -/
def FrameBundle (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompleteSpace E] : TopologicalSpace.Opens
    (TotalSpace (E →L[𝕜] E) (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x)) where
  carrier := {p | IsUnit p.2}
  is_open' := by
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    set e := trivializationAt (E →L[𝕜] E)
      (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.proj
    have hpe : p ∈ e.source := mem_trivializationAt_proj_source
    refine ⟨e.source ∩ e ⁻¹' (e.baseSet ×ˢ {f : E →L[𝕜] E | IsUnit f}),
            fun q ⟨hqs, hq⟩ => ?_,
            e.continuousOn.isOpen_inter_preimage e.open_source (e.open_baseSet.prod Units.isOpen),
            ⟨hpe, ?_⟩⟩
    · simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq] at hq
      have hb := e.mem_source.mp hqs
      rw [hom_trivializationAt_apply (σ := RingHom.id 𝕜)] at hq
      have hb_triv : q.proj ∈ (trivializationAt E (Bundle.Trivial M E) p.proj).baseSet := by
        simp
      have hb_tan : q.proj ∈ (trivializationAt E (TangentSpace I) p.proj).baseSet := by
        have hbs := hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id 𝕜)
          (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) p.proj
        rw [hbs] at hb; exact hb.2
      rw [ContinuousLinearMap.inCoordinates_eq hb_triv hb_tan] at hq
      have htriv_symm : (Trivialization.continuousLinearEquivAt 𝕜
          (trivializationAt E (Bundle.Trivial M E) p.proj) q.proj hb_triv).symm =
          ContinuousLinearEquiv.refl 𝕜 E := by
        simp [Bundle.Trivial.continuousLinearEquivAt_trivialization,
              ContinuousLinearEquiv.refl_symm]
      simp only [htriv_symm, ContinuousLinearEquiv.coe_refl,
                 ContinuousLinearMap.comp_id] at hq
      have htan_unit : IsUnit
          ((Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).toContinuousLinearMap) :=
        ⟨⟨(Trivialization.continuousLinearEquivAt 𝕜
              (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).toContinuousLinearMap,
          (Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm.toContinuousLinearMap,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan)
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).apply_symm_apply x,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan) x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm_apply_apply x⟩,
          rfl⟩
      haveI : NormedAddCommGroup (TangentSpace I q.proj) := by
        change NormedAddCommGroup E; infer_instance
      exact (isUnit_comp_iff_of_isUnit htan_unit q.2).mp hq.2
    · simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
      have hb := e.mem_source.mp hpe
      rw [hom_trivializationAt_apply (σ := RingHom.id 𝕜)]
      have hb_triv : p.proj ∈ (trivializationAt E (Bundle.Trivial M E) p.proj).baseSet := by
        simp
      have hb_tan : p.proj ∈ (trivializationAt E (TangentSpace I) p.proj).baseSet := by
        have hbs := hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id 𝕜)
          (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) p.proj
        rw [hbs] at hb; exact hb.2
      refine ⟨hb, ?_⟩
      rw [ContinuousLinearMap.inCoordinates_eq hb_triv hb_tan]
      have htriv_symm : (Trivialization.continuousLinearEquivAt 𝕜
          (trivializationAt E (Bundle.Trivial M E) p.proj) p.proj hb_triv).symm =
          ContinuousLinearEquiv.refl 𝕜 E := by
        simp [Bundle.Trivial.continuousLinearEquivAt_trivialization,
              ContinuousLinearEquiv.refl_symm]
      simp only [htriv_symm, ContinuousLinearEquiv.coe_refl,
                 ContinuousLinearMap.comp_id]
      have htan_unit : IsUnit
          ((Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).toContinuousLinearMap) :=
        ⟨⟨(Trivialization.continuousLinearEquivAt 𝕜
              (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).toContinuousLinearMap,
          (Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm.toContinuousLinearMap,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan)
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).apply_symm_apply x,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan) x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm_apply_apply x⟩,
          rfl⟩
      haveI : NormedAddCommGroup (TangentSpace I p.proj) := by
        change NormedAddCommGroup E; infer_instance
      exact (isUnit_comp_iff_of_isUnit htan_unit p.2).mpr hp

instance [IsManifold I ∞ M] [CompleteSpace E] :
    IsManifold (I.prod 𝓘(𝕜, E →L[𝕜] E)) ∞ ↥(FrameBundle I M) := inferInstance

instance [CompleteSpace E] : LieGroup (modelWithCornersSelf 𝕜 (E →L[𝕜] E)) ∞
    (Units (E →L[𝕜] E)) := inferInstance

end FrameBundle

noncomputable section FrameBundlePrincipal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

open scoped Manifold Topology Bundle ContDiff
open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap

/-
The tangent bundle coordinate change is invertible as a ContinuousLinearMap.
-/
omit [CompleteSpace E] [CompleteSpace 𝕜] in
lemma tangentBundleCore_coordChange_isUnit (i j : atlas H M)
    (x : M) (hx : x ∈ i.1.source ∩ j.1.source) :
    IsUnit ((tangentBundleCore I M).coordChange i j x) := by
  have h_inv : (tangentBundleCore I M).coordChange j i x ∘L
    (tangentBundleCore I M).coordChange i j x = ContinuousLinearMap.id 𝕜 E := by
    have := ( tangentBundleCore I M ).coordChange_comp i j i x;
    ext v; exact (by
    convert this ⟨ ⟨ hx.1, hx.2 ⟩, hx.1 ⟩ v using 1;
    exact Eq.symm ( ( tangentBundleCore I M ).coordChange_self i x hx.1 v ));
  have h_inv : (tangentBundleCore I M).coordChange i j x ∘L
  (tangentBundleCore I M).coordChange j i x = ContinuousLinearMap.id 𝕜 E := by
    have := ( tangentBundleCore I M ).coordChange_comp j i j x ⟨ ⟨ hx.2, hx.1 ⟩, hx.2 ⟩;
    exact ContinuousLinearMap.ext fun v => by
     simpa using this v |> Eq.trans <| ( tangentBundleCore I M ).coordChange_self j x hx.2 v;
  exact ⟨ ⟨ _, _, h_inv, by assumption ⟩, rfl ⟩

@[reducible, nolint unusedArguments]
def FrameSpace (_I : ModelWithCorners 𝕜 E H) (_M : Type*) [TopologicalSpace _M] [ChartedSpace H _M]
    [IsManifold _I 1 _M] (_ : _M) : Type _ := (E →L[𝕜] E)ˣ

def frameBundleFiberBundleCore [CompleteSpace 𝕜] :
    FiberBundleCore (atlas H M) M (E →L[𝕜] E)ˣ where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x g := by
    by_cases hx : x ∈ i.1.source ∩ j.1.source
    · have hunit : IsUnit ((tangentBundleCore I M).coordChange i j x) :=
        tangentBundleCore_coordChange_isUnit i j x hx
      exact (hunit.unit * g)
    · exact g
  coordChange_self i x hx g := by
    simp only [show x ∈ i.1.source ∩ i.1.source from ⟨hx, hx⟩, dif_pos]
    have key := (tangentBundleCore I M).coordChange_self i x hx
    simp only at key
    ext v
    have bar : ((tangentBundleCore I M).coordChange i i x) (g.val v) = g.val v := key (g.val v)
    simp only [tangentBundleCore_coordChange, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, toFun_eq_coe, PartialEquiv.coe_trans_symm, coe_coe_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, Function.comp_apply] at bar
    exact bar
  continuousOn_coordChange i j := by
    rw [(Units.isOpenEmbedding_val (R := E →L[𝕜] E)).isEmbedding.continuousOn_iff]
    apply ContinuousOn.congr
    · change ContinuousOn
        (fun p : M × (E →L[𝕜] E)ˣ => (tangentBundleCore I M).coordChange i j p.1 ∘L p.2.val)
        ((i.1.source ∩ j.1.source) ×ˢ univ)
      apply ContinuousOn.clm_comp
      · apply ((tangentBundleCore I M).continuousOn_coordChange i j).comp
          continuousOn_fst
        intro p hp
        exact hp.1
      · exact Units.continuous_val.comp_continuousOn continuousOn_snd
    · intro p hp
      simp only [Set.mem_prod, Set.mem_univ, and_true] at hp
      simp only [Function.comp, dif_pos hp]
      simp only [Units.val_mul, IsUnit.unit_spec]
      exact mul_def ((tangentBundleCore I M).coordChange i j p.1) ↑p.2
  coordChange_comp i j k x hx g := by
    ext v
    have hjk : x ∈ (j.1).source ∩ (k.1).source := ⟨hx.1.2, hx.2⟩
    have hik : x ∈ (i.1).source ∩ (k.1).source := ⟨hx.1.1, hx.2⟩
    have hij : x ∈ (i.1).source ∩ (j.1).source := ⟨hx.1.1, hx.1.2⟩
    simp only [hij, hjk, hik, dif_pos, IsUnit.unit_spec, Units.val_mul]
    have key := (tangentBundleCore I M).coordChange_comp i j k x
      ⟨⟨hx.1.1, hx.1.2⟩, hx.2⟩ (g.val v)
    exact LinearMap.mem_eqLocus.mp key

instance frameBundleTotalSpaceTopology [CompleteSpace 𝕜] :
    TopologicalSpace (Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M)) :=
  (frameBundleFiberBundleCore (I := I) (M := M)).toTopologicalSpace

instance frameBundleFiberBundle [CompleteSpace 𝕜] :
    FiberBundle (E →L[𝕜] E)ˣ (FrameSpace I M) :=
  frameBundleFiberBundleCore.fiberBundle

def frameBundleEquiv [CompleteSpace 𝕜] [IsManifold I ∞ M] :
    ↥(FrameBundle I M) ≃ Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M) where
  toFun p := ⟨p.1.proj, p.2.unit⟩
  invFun q := ⟨⟨q.proj, q.snd.val⟩, q.snd.isUnit⟩
  left_inv p := by
    apply Subtype.ext
    apply Bundle.TotalSpace.ext
    · rfl
    · simp [IsUnit.unit_spec]
  right_inv q := by
    apply Bundle.TotalSpace.ext
    · rfl
    · simp

/-!
## Helper lemmas for the continuity proofs

The key insight is the **intertwining relation**: the hom bundle trivialization composed with
the fiber map φ(q) = ⟨q.proj, q.snd.val⟩ composed with the FBC trivialization inverse
equals `Prod.map id Units.val` on the appropriate domain.

This follows because:
- FBC trivialization inverse: `(x, g) ↦ ⟨x, coordChange i (achart H x) x g⟩`
  where
  `(coordChange i (achart H x) x g).val = tangentBundleCore.coordChange i (achart H x) x ∘L g.val`
- Hom bundle trivialization at x₀ with i = achart H x₀:
  `⟨x, f⟩ ↦ (x, tangentBundleCore.coordChange (achart H x) i x ∘L f)`
- Composition: `(x, g) ↦ (x, tangentBundleCore.coordChange (achart H x) i x ∘L
                               tangentBundleCore.coordChange i (achart H x) x ∘L g.val)
                        = (x, g.val)`
  by the coordChange inverse relation.
-/

/-
The FBC coord change, when taken as a value via Units.val, equals composition with
    the tangent bundle core coord change.
-/
lemma frameBundleFiberBundleCore_coordChange_val (i j : atlas H M) (x : M)
    (hx : x ∈ i.1.source ∩ j.1.source) (g : (E →L[𝕜] E)ˣ) :
    ((frameBundleFiberBundleCore (I := I) (M := M)).coordChange i j x g).val =
      (tangentBundleCore I M).coordChange i j x ∘L g.val := by
  unfold frameBundleFiberBundleCore; aesop;

omit [CompleteSpace 𝕜] [CompleteSpace E] in
/-
The tangent bundle coord changes are inverses.
-/
lemma tangentBundleCore_coordChange_comp_inv (i j : atlas H M) (x : M)
    (hx : x ∈ i.1.source ∩ j.1.source) :
    (tangentBundleCore I M).coordChange j i x ∘L (tangentBundleCore I M).coordChange i j x =
      ContinuousLinearMap.id 𝕜 E := by
  have := ( tangentBundleCore_coordChange_isUnit ( I := I ) ( M := M ) i j x hx );
  obtain ⟨ u, hu ⟩ := this.exists_left_inv;
  have := ( tangentBundleCore I M ).coordChange_comp j i j x;
    simp_all +decide [ ContinuousLinearMap.ext_iff ] ;
  have := ( tangentBundleCore I M ).coordChange_self j x hx.2;
    simp_all +decide [ ] ;
  grind

set_option linter.style.multiGoal false in
/-
The intertwining relation: the hom bundle trivialization composed with φ composed with
    the FBC trivialization inverse equals `Prod.map id Units.val`.
-/
lemma intertwining_forward [IsManifold I ∞ M]
    (q : Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M)) :
    let Z := frameBundleFiberBundleCore (I := I) (M := M)
    let i := Z.indexAt q.proj
    let e := Z.localTriv i
    let e' := trivializationAt (E →L[𝕜] E)
      (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) q.proj
    ∀ᶠ p in 𝓝 (e q), (e' ⟨p.1, (Z.coordChange i (Z.indexAt p.1) p.1 p.2).val⟩) =
      (p.1, p.2.val) := by
  apply Filter.eventually_of_mem ( IsOpen.mem_nhds _ _ ) _;
  exact ( frameBundleFiberBundleCore ( I := I ) ( M := M ) ).baseSet
    ( frameBundleFiberBundleCore ( I := I ) ( M := M ) |>.indexAt q.proj ) ×ˢ Set.univ;
  · exact IsOpen.prod ( frameBundleFiberBundleCore ( I := I ) ( M := M ) |>.isOpen_baseSet _ )
      isOpen_univ;
  · simp +decide [ ];
  · simp +decide only [FiberBundleCore.baseSet_at, FiberBundleCore.proj,
      FiberBundleCore.localTrivAt_def, mem_prod,
      mem_univ, and_true, hom_trivializationAt_apply,
      Prod.mk.injEq, true_and, Prod.forall]
    intro x y hx; rw [ inCoordinates_eq ] ; simp +decide only
      [Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearEquivAt_trivialization,
       ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl, comp_id];
    any_goals first | trivial | exact hx
    rw [ frameBundleFiberBundleCore_coordChange_val ];
    · convert tangentBundleCore_coordChange_comp_inv
        ( frameBundleFiberBundleCore ( I := I ) ( M := M ) |>.indexAt q.proj )
          ( frameBundleFiberBundleCore ( I := I ) ( M := M ) |>.indexAt x ) x _ |>
            fun h => congr_arg ( fun f => f.comp ( y : E →L[𝕜] E ) ) h using 1;
      exact ⟨ hx, mem_chart_source H x ⟩;
    · exact ⟨ hx, mem_chart_source H x ⟩

/-
The inclusion of the FiberBundleCore total space into the FrameBundle Opens subtype
    is continuous.
-/
lemma continuous_toFrameBundleCore [IsManifold I ∞ M] :
    Continuous (fun q : Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M) =>
      (⟨⟨q.proj, q.snd.val⟩, q.snd.isUnit⟩ : ↥(FrameBundle I M))) := by
  apply continuous_induced_rng.mpr _;
  apply continuous_iff_continuousAt.mpr _;
  intro q
  set Z := frameBundleFiberBundleCore (I := I) (M := M)
  set i := Z.indexAt q.proj
  set e := Z.localTriv i
  set e' := trivializationAt (E →L[𝕜] E)
    (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) q.proj
  have h_cont : ContinuousAt (fun p : M × (E →L[𝕜] E)ˣ =>
    (e' ⟨p.1, (Z.coordChange i (Z.indexAt p.1) p.1 p.2).val⟩)) (e q) := by
    have h_cont : ContinuousAt (fun p : M × (E →L[𝕜] E)ˣ => (p.1, p.2.val)) (e q) := by
      exact ContinuousAt.prodMk ( continuousAt_fst )
        ( Units.continuous_val.continuousAt.comp continuousAt_snd );
    exact h_cont.congr ( by filter_upwards [ intertwining_forward q ] with p hp; aesop );
  convert e.continuousAt_of_comp_right _ ( e'.continuousAt_of_comp_left _ _ _ ) using 1;
  · exact Z.mem_baseSet_at q.proj;
  · convert continuousAt_fst using 1;
  · exact FiberBundle.mem_baseSet_trivializationAt' q.proj
  · convert h_cont using 1

set_option linter.style.multiGoal false in
/-
Reverse intertwining: (id × Units.val) ∘ (FBC_triv ∘ ψ) = hom_triv ∘ Subtype.val,
    near any point p in the FrameBundle.
-/
lemma intertwining_reverse [IsManifold I ∞ M]
    (p : ↥(FrameBundle I M)) :
    let Z := frameBundleFiberBundleCore (I := I) (M := M)
    let i := Z.indexAt p.1.proj
    let e := Z.localTriv i
    let e' := trivializationAt (E →L[𝕜] E)
      (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.1.proj
    ∀ᶠ p' in 𝓝 p, Prod.map id Units.val (e ⟨p'.1.proj, p'.2.unit⟩) = e' p'.1 := by
  apply Filter.eventually_of_mem ( IsOpen.mem_nhds _ _ ) _;
  exact { x : ↥ ( FrameBundle I M ) | ( x : Bundle.TotalSpace ( E →L[𝕜] E )
    fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x ).proj ∈ ( chartAt H p.1.proj ).source };
  · -- The projection map is continuous, and the source of the chart is open, so the preimage of
    -- the source under the projection is open.
    have h_proj_cont : Continuous (fun x : Bundle.TotalSpace (E →L[𝕜] E)
     (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) => x.proj) := by
      apply_rules [ FiberBundle.continuous_proj ];
    exact h_proj_cont.isOpen_preimage _
      ( chartAt H p.1.proj |>.open_source ) |> IsOpen.preimage continuous_subtype_val;
  · exact mem_chart_source _ _;
  · simp +decide only [mem_setOf_eq, frameBundleFiberBundleCore, mem_inter_iff,
                       tangentBundleCore_coordChange,
                       OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
                      ModelWithCorners.toPartialEquiv_coe, toFun_eq_coe,
                      PartialEquiv.coe_trans_symm, coe_coe_symm,
                      ModelWithCorners.toPartialEquiv_coe_symm, Function.comp_apply,
                      FiberBundleCore.proj, Subtype.forall]
    intro a ha ha'
    change (a.proj, ((frameBundleFiberBundleCore (I := I) (M := M)).coordChange
        (achart H a.proj) (achart H (p.1).proj) a.proj ha.unit).val)
      = (trivializationAt (E →L[𝕜] E)
        (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) (p.1).proj) a
    rw [frameBundleFiberBundleCore_coordChange_val (achart H a.proj) (achart H (p.1).proj) a.proj
        ⟨mem_chart_source H a.proj, ha'⟩ ha.unit, ha.unit_spec,
      hom_trivializationAt_apply (σ := RingHom.id 𝕜)]
    rw [ inCoordinates_eq ]
    all_goals simp_all +decide [ trivializationAt ]
    congr

/-
If `Prod.map id g` composed with `f` is continuousAt and `g` is an embedding,
    then `f` is continuousAt.
-/
lemma continuousAt_of_prodMap_isEmbedding {α β γ δ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    {f : α → β × γ} {g : γ → δ} {x : α}
    (hg : Topology.IsEmbedding g) (hf : ContinuousAt (Prod.map id g ∘ f) x) :
    ContinuousAt f x := by
  rw [ ContinuousAt ] at *;
  rw [ nhds_prod_eq, Filter.tendsto_prod_iff' ] at *;
  exact ⟨ hf.1, hg.isInducing.tendsto_nhds_iff.mpr hf.2 ⟩

/-
The projection from the FrameBundle Opens subtype to the FiberBundleCore total space
    is continuous.
-/
lemma continuous_fromFrameBundleCore [IsManifold I ∞ M] :
    Continuous (fun p : ↥(FrameBundle I M) =>
      (⟨p.1.proj, p.2.unit⟩ : Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M))) := by
  -- The projection from theFrame Bundle to the Manifold is continuous because it is the
  -- composition of continuous functions.
  have h_proj_cont : Continuous (fun p : TotalSpace (E →L[𝕜] E)
    (fun x => Trivial M E x →L[𝕜] TangentSpace I x) ↦ p.proj) :=
    FiberBundle.continuous_proj (E →L[𝕜] E)
      (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x)
  apply continuous_iff_continuousAt.mpr _;
  intro p
  set Z := frameBundleFiberBundleCore (I := I) (M := M)
  set i := Z.indexAt p.1.proj
  set e := Z.localTriv i
  set e' := trivializationAt (E →L[𝕜] E)
    (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.1.proj;
  apply e.continuousAt_of_comp_left;
  · convert h_proj_cont.continuousAt.comp ( continuous_subtype_val.continuousAt ) using 1;
  · exact mem_chart_source H _;
  · have h_intertwining : ∀ᶠ p' in 𝓝 p, Prod.map id Units.val (e ⟨p'.1.proj, p'.2.unit⟩) =
      e' p'.1 := by
      convert intertwining_reverse p using 1;
    have h_cont : ContinuousAt (Prod.map id Units.val ∘
     (e ∘ (fun p : ↥(FrameBundle I M) => ⟨p.1.proj, p.2.unit⟩))) p := by
      apply ContinuousAt.congr_of_eventuallyEq _ h_intertwining;
      apply e'.continuousAt _ |> ContinuousAt.comp <| continuous_subtype_val.continuousAt;
      exact FiberBundle.mem_trivializationAt_proj_source;
    convert continuousAt_of_prodMap_isEmbedding _ h_cont using 1;
    exact Units.isOpenEmbedding_val.isEmbedding

/-- The frame bundle homeomorphism. -/
def frameBundleCoreHomeomorph [IsManifold I ∞ M] :
    Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M) ≃ₜ ↥(FrameBundle I M) where
  toEquiv := frameBundleEquiv.symm
  continuous_toFun := continuous_toFrameBundleCore
  continuous_invFun := continuous_fromFrameBundleCore

instance [IsManifold I ∞ M] :
    ChartedSpace (ModelProd H (E →L[𝕜] E))
      (Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M)) :=
  (frameBundleCoreHomeomorph (I := I) (M := M)).symm.isLocalHomeomorph.chartedSpace
    (frameBundleCoreHomeomorph (I := I) (M := M)).symm.surjective

instance [IsManifold I ∞ M] :
    MulAction (MulOpposite (Units (E →L[𝕜] E)))
      (Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M)) where
  smul g q := ⟨q.proj, q.snd * MulOpposite.unop g⟩
  one_smul q := by
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (mul_one q.snd)
  mul_smul g h q := by
    apply Bundle.TotalSpace.ext
    · rfl
    · exact heq_of_eq (mul_assoc q.snd (MulOpposite.unop h) (MulOpposite.unop g))

end FrameBundlePrincipal
