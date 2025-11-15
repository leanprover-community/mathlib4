/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.Algebra.Module.Equiv

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

import Mathlib.Analysis.Distribution.SchwartzSpace

set_option linter.unusedSectionVars false

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove the existence of a smooth Riemannian metric.
Specialized attempt.

-/

open Bundle ContDiff Manifold

-- Let E be a smooth vector bundle over a manifold E

variable
  {EB : Type*} [NormedAddCommGroup EB] [InnerProductSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, TopologicalSpace (E x)] [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB ω B] [ContMDiffVectorBundle ω F E IB]

variable [FiniteDimensional ℝ EB] [IsManifold IB ω B] [SigmaCompactSpace B] [T2Space B]

noncomputable instance : TopologicalSpace (TotalSpace EB (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) :=
  inferInstanceAs (TopologicalSpace (TangentBundle IB B))

section

variable (E) in
/-- This is the bundle `Hom_ℝ(E, T)`, where `T` is the rank one trivial bundle over `B`. -/
private def V : (b : B) → Type _ := (fun b ↦ E b →L[ℝ] Trivial B ℝ b)

noncomputable instance : (x : B) → TopologicalSpace (V E x) := by
  unfold V
  infer_instance

noncomputable instance : (x : B) → AddCommGroup (V E x) := by
  unfold V
  infer_instance

noncomputable instance (x : B) : Module ℝ (V E x) := by
  unfold V
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (F →L[ℝ] ℝ) (V E)) := by
  unfold V
  infer_instance

noncomputable instance : FiberBundle (F →L[ℝ] ℝ) (V E) := by
  unfold V
  infer_instance

noncomputable instance : VectorBundle ℝ (F →L[ℝ] ℝ) (V E) := by
  unfold V
  infer_instance

noncomputable instance :
VectorBundle ℝ (EB →L[ℝ] ℝ) (V (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) := by
  unfold V
  infer_instance

noncomputable instance : ContMDiffVectorBundle n (F →L[ℝ] ℝ) (V E) IB := by
  unfold V
  infer_instance

instance (x : B) : ContinuousAdd (V E x) := by
  unfold V
  infer_instance

instance (x : B) : ContinuousSMul ℝ (V E x) := by
  unfold V
  infer_instance

instance (x : B) : IsTopologicalAddGroup (V E x) := by
  unfold V
  infer_instance

example : ContMDiffVectorBundle n (F →L[ℝ] F →L[ℝ] ℝ) (fun b ↦ E b →L[ℝ] V E b) IB :=
  ContMDiffVectorBundle.continuousLinearMap (IB := IB) (n := n)
    (F₁ := F) (E₁ := E) (F₂ := F →L[ℝ] ℝ) (E₂ := V E)

example : ContMDiffVectorBundle n (EB →L[ℝ] EB →L[ℝ] ℝ)
(fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] V (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b)
IB :=
  ContMDiffVectorBundle.continuousLinearMap (IB := IB) (n := n)
  (F₁ := EB) (E₁ := (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) (F₂ := EB →L[ℝ] ℝ)
  (E₂ := V (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))

variable (E) in
/-- The real vector bundle `Hom(E, Hom(E, T)) = Hom(E, V)`, whose fiber at `x` is
(equivalent to) the space of continuous real bilinear maps `E x → E x → ℝ`. -/
private def W : (b : B) → Type _ := fun b ↦ E b →L[ℝ] V E b

noncomputable instance (x : B) : TopologicalSpace (W E x) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : AddCommGroup (W E x) := by
  unfold W
  infer_instance

noncomputable instance (x : B) : Module ℝ (W E x) := by
  unfold W
  infer_instance

noncomputable instance : TopologicalSpace (TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (W E)) := by
  unfold W
  infer_instance

noncomputable instance : FiberBundle (F →L[ℝ] F →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : VectorBundle ℝ (F →L[ℝ] F →L[ℝ] ℝ) (W E) := by
  unfold W
  infer_instance

noncomputable instance : ContMDiffVectorBundle n (F →L[ℝ] F →L[ℝ] ℝ) (W E) IB := by
  unfold W
  infer_instance

instance (x : B) : ContinuousAdd (W E x) := by
  unfold W
  infer_instance

instance (x : B) : ContinuousSMul ℝ (W E x) := by
  unfold W
  infer_instance

instance (x : B) : IsTopologicalAddGroup (W E x) := by
  unfold W
  infer_instance

end

noncomputable def g (i : B) (p : B) (v w : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) : ℝ :=
  letI dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  @Inner.inner ℝ EB _ (dψ v) (dψ w)

variable (IB) in
noncomputable def g' (i p : B) : TangentSpace IB p → TangentSpace IB p → ℝ := fun v w ↦
  letI dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  @Inner.inner ℝ EB _ (dψ v) (dψ w)

lemma g_nonneg (i p : B) (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) :
  0 ≤ g i p v v := by
  unfold g
  exact @inner_self_nonneg ℝ _ _ _ _ _

lemma g_pos (i p : B) (hp : p ∈ (extChartAt IB i).source)
            (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p) (hv : v ≠ 0) :
    0 < g i p v v := by
  let ψ := extChartAt IB i
  let dψ := mfderiv IB 𝓘(ℝ, EB) ψ p
  have h_invert : dψ.IsInvertible := isInvertible_mfderiv_extChartAt hp
  obtain ⟨inv, left_inv⟩ := h_invert
  have inj : Function.Injective inv := inv.injective
  have h1 : inv v = dψ v := by
    rw[← left_inv]
    exact inj (inj (inj (inj rfl)))
  have hx : dψ v ≠ 0 := by
    intro h
    have h2 : inv v = inv 0 := by simp [h, h1]
    exact hv (inj h2)
  exact real_inner_self_pos.mpr hx

noncomputable instance (p : B) : NormedAddCommGroup (TangentSpace IB p) := by
  change NormedAddCommGroup EB
  infer_instance

noncomputable instance (p : B) : NormedSpace ℝ (TangentSpace IB p) := by
  change NormedSpace ℝ EB
  infer_instance

noncomputable
def g_bilin (i p : B) :
  (TangentSpace IB) p →L[ℝ]  ((TangentSpace IB) p →L[ℝ] Trivial B ℝ p) := by
  let dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  let inner := innerSL ℝ (E := EB)
  exact inner.comp dψ |>.flip.comp dψ

noncomputable def mynorm {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
    Seminorm ℝ (TangentSpace IB x) where
  toFun v := Real.sqrt (φ v v)
  map_zero' := by simp
  add_le' r s := by
    rw [@Real.sqrt_le_iff]
    · have : ((φ r) s) * ((φ s) r) ≤ ((φ r) r) * ((φ s) s) :=
        LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le φ.toLinearMap₁₂ hpos r s
      have h1 : φ (r + s) (r + s) ≤ (Real.sqrt ((φ r) r) + Real.sqrt ((φ s) s)) ^ 2 :=
        calc φ (r + s) (r + s)
          = (φ r) r + (φ r) s + (φ s) r + (φ s) s := by
              simp
              exact Eq.symm (add_assoc ((φ r) r + (φ r) s) ((φ s) r) ((φ s) s))
        _ = (φ r) r + 2 * (φ r) s + (φ s) s := by
              rw [hsymm r s]
              ring
        _ ≤ (φ r) r + 2 * √((φ r) r * (φ s) s) + (φ s) s := by
              gcongr
              have h1 :  (φ r) s * (φ s) r ≤ (φ r) r * (φ s) s :=
                LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le φ.toLinearMap₁₂ hpos r s
              have h2 :  ((φ r) s) ^ 2 ≤ ((φ r) r * (φ s) s) := by
                rw [sq, hsymm r s]
                exact le_of_eq_of_le (congrFun (congrArg HMul.hMul (hsymm s r)) ((φ s) r)) this
              exact Real.le_sqrt_of_sq_le h2
        _ = (√((φ r) r) + √((φ s) s)) ^ 2 := by
                rw [add_sq]
                rw [Real.sq_sqrt (hpos r), Real.sq_sqrt (hpos s)]
                rw [Real.sqrt_mul (hpos r) ((φ s) s)]
                ring
      have h2 : 0 ≤ √((φ r) r) + √((φ s) s) :=
        add_nonneg (Real.sqrt_nonneg ((φ r) r)) (Real.sqrt_nonneg ((φ s) s))
      exact And.symm ⟨h1, h2⟩
  neg' r := by simp
  smul' a v := by simp [← mul_assoc, ← Real.sqrt_mul_self_eq_abs, Real.sqrt_mul (mul_self_nonneg a)]

noncomputable def aux {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  SeminormFamily ℝ (TangentSpace IB x) (Fin 1) := fun _ ↦ mynorm φ hpos hsymm

structure TangentSpaceAuy
  (x : B) where
  val : TangentSpace IB x

lemma TangentSpaceAuy.ext_iff {x : B} (u v : TangentSpaceAuy x) :
  u = v ↔ u.val = (v.val : TangentSpace IB x) := by
  cases u; cases v; simp

instance {x : B} : Zero (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  zero := ⟨0⟩

instance {x : B} : Add (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  add u v := ⟨u.val + v.val⟩

instance {x : B} : Neg (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  neg u := ⟨-u.val⟩

noncomputable
instance {x : B} : Sub (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  sub u v := ⟨u.val - v.val⟩

noncomputable
instance {x : B} : SMul ℝ (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  smul a u := ⟨a • u.val⟩

-- The norm (parametrized by φ)
noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  Norm (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  norm v := mynorm φ hpos hsymm v.val

-- Helper lemmas (assuming you have these for mynorm)
lemma mynorm_sub_self {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u)
  (v : TangentSpaceAuy x) :
  mynorm φ hpos hsymm (v.val - v.val) = 0 := by
  sorry

lemma mynorm_sub_comm {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u)
  (u v : TangentSpaceAuy x) :
  mynorm φ hpos hsymm (u.val - v.val) = mynorm φ hpos hsymm (v.val - u.val) := by
  sorry

lemma my_eq_of_dist_eq_zero {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
 ∀ {u v: TangentSpaceAuy x}, (mynorm φ hpos hsymm) (u.val - v.val) = 0 → u = v := by
    intro u v h
    rw [mynorm] at h
    have h1 : √((φ (u.val - v.val)) (u.val - v.val)) = 0 := h
    have h2 : ((φ (u.val - v.val)) (u.val - v.val)) = 0 :=
      (Real.sqrt_eq_zero (hpos (u.val - v.val))).mp h
    have h3 : u.val - v.val = 0 := (hdef (u.val - v.val)) h2
    have h4 : u.val = v.val := sub_eq_zero.mp h3
    exact (TangentSpaceAuy.ext_iff u v).mpr h4

-- NormedAddCommGroup instance
noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedAddCommGroup (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  norm := fun v => mynorm φ hpos hsymm v.val
  dist_eq := by intros; rfl
  add_assoc := fun u v w => TangentSpaceAuy.ext_iff _ _ |>.mpr (add_assoc u.val v.val w.val)
  zero_add := fun u => TangentSpaceAuy.ext_iff _ _ |>.mpr (zero_add u.val)
  add_zero := fun u => TangentSpaceAuy.ext_iff _ _ |>.mpr (add_zero u.val)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := fun u => TangentSpaceAuy.ext_iff _ _ |>.mpr (neg_add_cancel u.val)
  add_comm := fun u v => TangentSpaceAuy.ext_iff _ _ |>.mpr (add_comm u.val v.val)
  sub_eq_add_neg := fun u v => TangentSpaceAuy.ext_iff _ _ |>.mpr (sub_eq_add_neg u.val v.val)
  dist_self := mynorm_sub_self φ hpos hsymm
  dist_comm := mynorm_sub_comm φ hpos hsymm
  dist_triangle := sorry -- triangle inequality
  eq_of_dist_eq_zero := my_eq_of_dist_eq_zero φ hpos hsymm hdef

-- Module and NormedSpace instances
instance {x : B} : Module ℝ (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  one_smul u := TangentSpaceAuy.ext_iff _ _ |>.mpr (one_smul ℝ u.val)
  mul_smul a b u := TangentSpaceAuy.ext_iff _ _ |>.mpr (mul_smul a b u.val)
  smul_add a u v := TangentSpaceAuy.ext_iff _ _ |>.mpr (smul_add a u.val v.val)
  smul_zero a := TangentSpaceAuy.ext_iff _ _ |>.mpr (smul_zero a)
  zero_smul u := TangentSpaceAuy.ext_iff _ _ |>.mpr (zero_smul ℝ u.val)
  add_smul a b u := TangentSpaceAuy.ext_iff _ _ |>.mpr (add_smul a b u.val)

noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  NormedSpace ℝ (@TangentSpaceAuy EB _ _ _ _ IB B _ _ x) where
  norm_smul_le := sorry -- ‖a • u‖ ≤ |a| * ‖u‖

-- Create type synonym with mynorm
def TangentSpaceAux {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :=
  TangentSpace IB x

-- Put mynorm on the type synonym
noncomputable
instance {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  Norm (TangentSpaceAux φ hpos hsymm) where
  norm v := mynorm φ hpos hsymm v

-- (Need to prove this is actually a normed space - skipping details)
instance {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
   NormedAddCommGroup (TangentSpaceAux φ hpos hsymm) := sorry
instance {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
   NormedSpace ℝ (TangentSpaceAux φ hpos hsymm) := sorry

-- The linear equivalence
def tangentSpaceEquiv {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  TangentSpace IB x ≃ₗ[ℝ] TangentSpaceAux φ hpos hsymm where
  toFun := id
  map_add' := fun _ _ => sorry
  map_smul' := fun _ _ => sorry
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

-- It's continuous in both directions (finite dimensions!)
lemma tangentSpaceEquiv_continuous {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  Continuous (tangentSpaceEquiv φ hpos hsymm).toLinearMap :=
  letI : FiniteDimensional ℝ (TangentSpace IB x) := sorry
  LinearMap.continuous_of_finiteDimensional _

lemma tangentSpaceEquiv_continuous_symm {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  Continuous (tangentSpaceEquiv φ hpos hsymm).symm.toLinearMap :=
  letI : FiniteDimensional ℝ (TangentSpaceAux φ hpos hsymm) := sorry
  LinearMap.continuous_of_finiteDimensional _

-- Now we need the abstract lemma that uses these continuous maps
lemma withSeminorms_of_linearEquiv_finite_dim
  {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (e : E ≃ₗ[ℝ] F)
  (he : Continuous e.toLinearMap)
  (he_symm : Continuous e.symm.toLinearMap)
  : WithSeminorms (fun (i : Fin 1) => (normSeminorm ℝ F : Seminorm ℝ F)) := by
  exact norm_withSeminorms ℝ F

#check IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap
#check LinearMap.continuous_of_finiteDimensional
#check SeminormFamily.withSeminorms_of_hasBasis
#check schwartz_withSeminorms

#check norm_withSeminorms
#check LinearMap.continuous_of_finiteDimensional
#check fun (x : B) => WithSeminorms.congr (norm_withSeminorms ℝ (TangentSpace IB x))
#check Seminorm.IsBounded
#check WithSeminorms.congr
#check WithSeminorms.continuous_seminorm
#check Seminorm.bound_of_continuous
#check SeminormFamily.withSeminorms_of_hasBasis
#check schwartz_withSeminorms
#check normSeminorm

/-
Quoting
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/FiniteDimension.html

The fact that all norms are equivalent is not written explicitly,
as it would mean having two norms on a single space, which is not the way type classes work.
However, if one has a finite-dimensional vector space E with a norm,
and a copy E' of this type with another norm,
then the identities from E to E' and from E'to E are continuous thanks to
LinearMap.continuous_of_finiteDimensional. This gives the desired norm equivalence.
-/

lemma norm_pointwise {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  ∀ y : TangentSpaceAux φ hpos hsymm,
    @Norm.norm (TangentSpaceAux φ hpos hsymm)
      (instNormTangentSpaceAux φ hpos hsymm) y = mynorm φ hpos hsymm y := by
  intro y
  dsimp [instNormTangentSpaceAux, Norm.norm, mynorm]

lemma bbr {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
    WithSeminorms (aux φ hpos hsymm) := by
    letI : FiniteDimensional ℝ (TangentSpace IB x) := sorry
    letI : FiniteDimensional ℝ (TangentSpaceAux φ hpos hsymm) := sorry
    apply WithSeminorms.congr (norm_withSeminorms ℝ (TangentSpace IB x))
    · intro j
      let diagonal : TangentSpace IB x →ₗ[ℝ] TangentSpace IB x × TangentSpace IB x :=
        LinearMap.prod (LinearMap.id : TangentSpace IB x →ₗ[ℝ] TangentSpace IB x)
                       (LinearMap.id : TangentSpace IB x →ₗ[ℝ] TangentSpace IB x)
      have h_diag_cont : Continuous diagonal :=
        LinearMap.continuous_of_finiteDimensional diagonal
      let φ_bilinear : TangentSpace IB x × TangentSpace IB x → ℝ :=
        fun  p => φ p.1 p.2
      have : Continuous φ_bilinear := ContinuousLinearMap.continuous₂ φ
      have : Continuous (fun v ↦ φ v v) := this.comp h_diag_cont
      have : Continuous (fun v ↦ Real.sqrt ((φ v) v)) := Continuous.sqrt this
      have h_need : Continuous (aux φ hpos hsymm j) := by
        dsimp [aux, mynorm]
        let diagonal : TangentSpace IB x → TangentSpace IB x × TangentSpace IB x := fun v => (v, v)
        exact this
      obtain ⟨s, C, hC, hbound⟩ := Seminorm.bound_of_continuous
        (norm_withSeminorms ℝ (TangentSpace IB x))
        (aux φ hpos hsymm j)
        h_need
      use s, C
      exact hbound
    · intro j
      have he := tangentSpaceEquiv_continuous_symm φ hpos hsymm
      have h_linear : IsLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm).symm :=
        sorry
      have h_bounded : IsBoundedLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm).symm := by
        rw [← IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap]
        exact And.symm ⟨he, h_linear⟩
      obtain ⟨C, hC⟩ := h_bounded.bound
      simp
      by_cases h : C = 0
      · have : C = 0 := h
        exfalso
        have : ∃ v : TangentSpaceAux φ hpos hsymm, v ≠ 0 := by exact sorry
        obtain ⟨v, hv⟩ := this
        have : ‖(tangentSpaceEquiv φ hpos hsymm).symm v‖ ≤ 0 := by
          calc ‖(tangentSpaceEquiv φ hpos hsymm).symm v‖
              ≤ C * ‖v‖ := hC.2 v
            _ = 0 * ‖v‖ := by rw [h]
            _ = 0 := by ring
        have : (tangentSpaceEquiv φ hpos hsymm).symm v = 0 := by
          exact norm_le_zero_iff.mp this
        have : v = 0 := by
          have := LinearEquiv.injective (tangentSpaceEquiv φ hpos hsymm).symm
          exact this (by simpa using ‹(tangentSpaceEquiv φ hpos hsymm).symm v = 0›)
        exact hv this
      · have : C ≠ 0 := h
        have hC_pos : 0 < C := by exact sorry
        use {0}, ⟨C, le_of_lt hC_pos⟩
        intro v
        simp
        have hC₂ := hC.right
        have : (normSeminorm ℝ (TangentSpace IB x)) v ≤ C * (aux φ hpos hsymm j) v :=
           calc normSeminorm ℝ (TangentSpace IB x) v
            = ‖v‖ := rfl
          _ = ‖(tangentSpaceEquiv φ hpos hsymm).symm (tangentSpaceEquiv φ hpos hsymm v)‖ := by simp
          _ ≤ C * ‖tangentSpaceEquiv φ hpos hsymm v‖ := by exact sorry
          _ = C * mynorm φ hpos hsymm v := by rfl
          _ = C * aux φ hpos hsymm j v := by rfl
        exact this

lemma qux {α : Type*} [Unique α] (s : Finset α) : s = ∅ ∨ s = {default} := by
  by_cases h : s = ∅
  · simp [h]
  · rw [Finset.eq_singleton_iff_nonempty_unique_mem]
    refine Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr h, fun x hx ↦ Unique.uniq _ _⟩

lemma aux_tvs {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
   (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
    Bornology.IsVonNBounded ℝ {v | (φ v) v < 1} := by
  rw [WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded
        (p := aux φ hpos hsymm) (bbr φ hpos hsymm)]
  intro I
  letI J : Finset (Fin 1) := {1}
  suffices ∃ r > 0, ∀ x ∈ {v | (φ v) v < 1}, (J.sup (aux φ hpos hsymm)) x < r by
    obtain (rfl | h) := qux I
    · use 1; simp
    · convert this
  simp only [Set.mem_setOf_eq, Finset.sup_singleton, J]
  refine ⟨1, by norm_num, fun x h ↦ ?_⟩
  simp only [aux, mynorm]
  change Real.sqrt (φ x x) < 1
  rw [Real.sqrt_lt' (by norm_num)]
  simp [h]

@[simp]
theorem linear_flip_apply
  {𝕜 E F G : Type*}
  [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
  (f : E →L[𝕜] F →L[𝕜] G) (x : F) (y : E) :
  f.flip x y = f y x := rfl

theorem g_bilin_symm (i p : B) (v w : TangentSpace IB p) :
    ((g_bilin i p).toFun v).toFun w =
    ((g_bilin i p).toFun w).toFun v := by
  unfold g_bilin
  simp
  rw [real_inner_comm]

example (x y : EB) : (innerSL ℝ (E := EB)) x y = Inner.inner ℝ x y := rfl

example (x y : EB) : (innerSL ℝ (E := EB)).flip y x = (innerSL ℝ (E := EB)) x y := rfl

open SmoothPartitionOfUnity

noncomputable instance (x : B) : NormedAddCommGroup (W (TangentSpace IB) x) :=
  show NormedAddCommGroup (TangentSpace IB x →L[ℝ] (TangentSpace IB x →L[ℝ] ℝ)) from
    inferInstance

noncomputable instance :
  TopologicalSpace (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
                   (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) := by
    unfold W
    infer_instance

noncomputable
def g_global_bilin (f : SmoothPartitionOfUnity B IB B) (p : B) :
    W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p := ∑ᶠ (j : B), (f j) p • g_bilin j p

lemma finsum_image_eq_sum {B E F : Type*} [AddCommMonoid E] [AddCommMonoid F]
 (φ : E →+ F) (f : B → E) (h_fin : Finset B)
 (h1 : Function.support f ⊆ h_fin) :
    ∑ᶠ j, φ (f j) = ∑ j ∈ h_fin, φ (f j) := by
  apply finsum_eq_sum_of_support_subset
  have : Function.support f ⊆ ↑h_fin := h1
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj ⊢
  have hf : f j ≠ 0 := by
    contrapose! hj
    simpa using (map_zero φ).symm ▸ congrArg φ hj
  exact h1 hf

def evalAt (b : B) (v w : TangentSpace IB b) : W (TangentSpace IB) b →+ ℝ :=
  {
    toFun := fun f => (f.toFun v).toFun w
    map_zero' := by
      simp
    map_add' := by
      intro f g
      exact rfl
  }

lemma h_need (f : SmoothPartitionOfUnity B IB B) (b : B) (v w : TangentSpace IB b)
  (h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) : W (TangentSpace IB) b)).Finite) :
  ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w =
  ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v := by

    have ha : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun w =
              ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

    have ha' : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun w).toFun v =
              ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

    let h : (j : B) → W ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) b :=
      fun j ↦ (f j) b • g_bilin j b

    have h_inc : (Function.support h) ⊆ h_fin.toFinset :=
      Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a

    have hb : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun w =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun w :=
      finsum_image_eq_sum (evalAt b v w) h h_fin.toFinset h_inc

    have hb' : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun w).toFun v =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun w).toFun v :=
      finsum_image_eq_sum (evalAt b w v) h h_fin.toFinset h_inc

    have h_gbilin_symm : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun w =
                         ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun w).toFun v := by
      have h5 : ∀ (j : B), (((g_bilin j b)).toFun v).toFun w =
                           (((g_bilin j b)).toFun w).toFun v := fun j => g_bilin_symm j b v w
      have h6 : ∀ (j : B), (f j b) * ((g_bilin j b).toFun v).toFun w =
                           (f j b) * ((g_bilin j b).toFun w).toFun v :=
        fun j ↦ congrArg (HMul.hMul ((f j) b)) (h5 j)
      exact finsum_congr h6

    calc
        ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w
          = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun w := ha.symm
        _ = ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun w := hb.symm
        _ = ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun w).toFun v := h_gbilin_symm
        _ = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun w).toFun v := hb'
        _ = ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v := ha'

lemma riemannian_metric_symm (f : SmoothPartitionOfUnity B IB B) (b : B) (v w : TangentSpace IB b) :
  ((g_global_bilin f b).toFun v).toFun w = ((g_global_bilin f b).toFun w).toFun v := by
  unfold g_global_bilin
  simp
  have h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) :
                  W (TangentSpace IB) b)).Finite := by
      apply (f.locallyFinite'.point_finite b).subset
      intro i hi
      simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
      simp only [Set.mem_setOf_eq, Function.mem_support, ne_eq]
      exact hi.1
  have h6a : (∑ᶠ (j : B), (f j) b • g_bilin j b) =
            ∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b := finsum_eq_sum _ h_fin
  rw [h6a]
  have : ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun w =
         ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun w).toFun v :=
    h_need f b v w h_fin
  exact this

lemma g_global_bilin_eq_sum (f : SmoothPartitionOfUnity B IB B) (p : B) :
  g_global_bilin f p = ∑ᶠ (j : B), (f j) p • g_bilin j p := rfl

lemma g_bilin_smooth_on_chart (i : B)
 (hbase : (FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
            (fun b ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) i).baseSet =
          (extChartAt IB i).source) : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun x ↦ (TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_bilin i x) :
      TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
       (fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ]
          ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] ℝ))))
    (extChartAt IB i).source := by
  intros x hx
  let e := FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
              (fun b ↦ TangentSpace IB b →L[ℝ] (TangentSpace IB b →L[ℝ] ℝ)) i
  let F := fun (x : B) ↦ e.invFun (x, (e.toPartialEquiv.toFun ⟨x, g_bilin i x⟩).2)
  have h_eq : ∀ x ∈ (extChartAt IB i).source,
    TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_bilin i x) = F x := by
    intros x hx
    let p : TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
        fun x ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ := ⟨x, g_bilin i x⟩
    let pe := e.toPartialEquiv.toFun p
    let m := pe.2
    have hp : p ∈ e.toPartialEquiv.source := by
      have : e.baseSet = (extChartAt IB i).source := hbase
      simp [e.source_eq, this]
      exact Set.mem_of_mem_inter_left hx
    have : e.invFun (x, m) = p := by calc
      e.toPartialEquiv.invFun (x, m)
        = e.toPartialEquiv.invFun (e.toPartialEquiv.toFun p) := rfl
      _ = p := e.toPartialEquiv.left_inv' hp
    have h_er : TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_bilin i x)
              = e.toPartialEquiv.invFun (x, m) := by
      exact id (Eq.symm this)
    exact h_er

  have h_easier : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞ F
                  (extChartAt IB i).source := sorry

  apply ContMDiffOn.congr h_easier h_eq
  exact hx

lemma baseSet_eq_extChartAt_source (i : B) :
    (FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
      (fun b ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) i).baseSet =
    (extChartAt IB i).source := by
  simp only [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
      Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_univ,
      Set.inter_self, extChartAt, PartialHomeomorph.extend, PartialEquiv.trans_source,
      PartialHomeomorph.toFun_eq_coe, ModelWithCorners.source_eq, Set.preimage_univ]

lemma riemannian_metric_smooth (f : SmoothPartitionOfUnity B IB B)
        (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞ fun x ↦
    TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x
                   (∑ᶠ (j : B), (f j) x • g_bilin j x :  W (TangentSpace IB) x) := by
      have h := contMDiff_totalSpace_weighted_sum_of_local_sections
        (E := EB) (I := IB) (M := B)
        (V := fun b => TangentSpace IB b →L[ℝ] (TangentSpace IB b →L[ℝ] Trivial B ℝ b))
        (F_fiber := EB →L[ℝ] (EB →L[ℝ] ℝ))
        (n := (⊤ : ℕ∞)) (ι := B)
        (ρ := f)
        (s_loc := g_bilin)
        (U := fun x ↦ (extChartAt IB x).source)
        (by intro i; exact isOpen_extChartAt_source i)
        h_sub
        (by intro i; exact (g_bilin_smooth_on_chart i (baseSet_eq_extChartAt_source i)))
      exact h

lemma g_global_bilin_smooth (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_global_bilin f x)) := by
  simp_rw [g_global_bilin_eq_sum]
  exact (riemannian_metric_smooth f h_sub)

noncomputable
def g_global_smooth_section'
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
    ContMDiffSection (I := IB) (F := (EB →L[ℝ] EB →L[ℝ] ℝ)) (n := ∞)
      (V := (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) :=
  { toFun := g_global_bilin f
    contMDiff_toFun := g_global_bilin_smooth f h_sub}

lemma h_need' (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b)
  (h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) : W (TangentSpace IB) b)).Finite) :
  v ≠ 0 → 0 < ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun v := by

  have ha : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun v =
            ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun v := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

  let h : (j : B) → W ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) b :=
    fun j ↦ (f j) b • g_bilin j b

  let h' x := f x b * ((g_bilin x b).toFun v).toFun v

  have h_inc : (Function.support h) ⊆ h_fin.toFinset :=
      Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a

  have hb : ∑ᶠ (j : B), (((f j) b • g_bilin j b).toFun v).toFun v =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun v :=
      finsum_image_eq_sum (evalAt b v v) h h_fin.toFinset h_inc

  have : ∀ j, (((f j) b • g_bilin j b).toFun v).toFun v = h' j := by
    simp
    exact fun j ↦ rfl

  intro hv
  have h_nonneg : ∀ i, 0 ≤ f.toFun i b := fun i => f.nonneg' i b
  have ⟨i, hi_pos⟩ : ∃ i, 0 < f i b := by
    by_contra hneg
    push_neg at hneg
    have : ∀ (x : B), f x b = 0 := fun x => le_antisymm (hneg x) (h_nonneg x)
    have h1 : ∑ᶠ i, f i b = 0 := finsum_eq_zero_of_forall_eq_zero this
    have h2 : ∑ᶠ i, f i b = 1 := f.sum_eq_one' b trivial
    exact absurd (h1.symm.trans h2) one_ne_zero.symm
  have hi_chart : b ∈ (extChartAt IB i).source := by
    apply h_sub
    apply subset_closure
    exact Function.mem_support.mpr hi_pos.ne'

  have h1 : ∀ j, 0 ≤ h' j := fun j => mul_nonneg (h_nonneg j) (g_nonneg j b v)
  have h2 : ∃ j, 0 < h' j := ⟨i, mul_pos hi_pos (g_pos i b hi_chart v hv)⟩
  have h3 : (Function.support h').Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro x hx
    simp [Function.mem_support, h'] at hx
    have : f x b ≠ 0 ∧ (((g_bilin x b)).toFun v).toFun v ≠ 0 := hx
    have : (f x) b * ((g_bilin x b).toFun v).toFun v ≠ 0 := mul_ne_zero_iff.mpr this
    exact mul_ne_zero_iff.mp this |>.1
  have h4 : 0 < ∑ᶠ i, h' i := finsum_pos' h1 h2 h3

  have h5 : ∑ᶠ i, h' i  = ∑ᶠ i, (((f i) b • g_bilin i b).toFun v).toFun v := rfl
  have h6 : ∑ᶠ i, h' i  = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin j b).toFun v).toFun v := by
    rw [hb] at h5
    exact h5
  have h7 : ∑ᶠ i, h' i = ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b).toFun v).toFun v := by
    rw [ha] at h6
    exact h6

  exact lt_of_lt_of_eq h4 h7

lemma riemannian_metric_pos_def (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b) :
  v ≠ 0 → 0 < ((g_global_bilin f b).toFun v).toFun v := by
  intro hv
  unfold g_global_bilin
  have h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin j b) :
                W (TangentSpace IB) b)).Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro i hi
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
    simp only [Set.mem_setOf_eq, Function.mem_support, ne_eq]
    exact hi.1
  have h6a : (∑ᶠ (j : B), (f j) b • g_bilin j b) =
            ∑ j ∈ h_fin.toFinset, (f j) b • g_bilin j b := finsum_eq_sum _ h_fin
  rw [h6a]
  exact h_need' f h_sub b v h_fin hv

lemma riemannian_unit_ball_bounded (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ∀ (b : B), Bornology.IsVonNBounded ℝ
    {v  : TangentSpace IB b | ((g_global_bilin f b).toFun v).toFun v < 1} := by
  intro b
  have h1 : ∀ (v : TangentSpace IB b), 0 ≤ ((g_global_bilin f b).toFun v).toFun v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact le_of_lt (riemannian_metric_pos_def f h_sub b v hv)
  have h2 : ∀ (u v : TangentSpace IB b),
    ((g_global_bilin f b).toFun u).toFun v = ((g_global_bilin f b).toFun v).toFun u := by
    exact fun u v ↦ riemannian_metric_symm f b u v
  exact aux_tvs (g_global_bilin f b) h1 h2

noncomputable
def riemannian_metric_exists'
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
    ContMDiffRiemannianMetric (IB := IB) (n := ∞) (F := EB)
     (E := @TangentSpace ℝ _ _ _ _ _ _ IB B _ _) :=
  { inner := g_global_bilin f
    symm := riemannian_metric_symm f
    pos := riemannian_metric_pos_def f h_sub
    isVonNBounded := riemannian_unit_ball_bounded f h_sub
    contMDiff := (g_global_smooth_section' f h_sub).contMDiff_toFun
     }
