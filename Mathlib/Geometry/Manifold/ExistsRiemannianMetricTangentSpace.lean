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

structure TangentSpaceAux
  (x : B) (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) where
  val : TangentSpace IB x

lemma TangentSpaceAux.ext_iff {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0)
  (u v : TangentSpaceAux x φ hpos hsymm hdef) :
  u = v ↔ u.val = (v.val : TangentSpace IB x) := by
  cases u; cases v; simp

instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Zero (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  zero := ⟨0⟩

instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Add (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  add u v := ⟨u.val + v.val⟩

instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Neg (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  neg u := ⟨-u.val⟩

noncomputable
instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Sub (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  sub u v := ⟨u.val - v.val⟩

noncomputable
instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  SMul ℝ (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  smul a u := ⟨a • u.val⟩

-- The norm (parametrized by φ)
noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Norm (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  norm v := mynorm φ hpos hsymm v.val

-- Helper lemmas (assuming you have these for mynorm)
lemma mynorm_sub_self {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
  (v : TangentSpaceAux x φ hpos hsymm hdef) :
  mynorm φ hpos hsymm (v.val - v.val) = 0 := by
  unfold mynorm
  simp

lemma mynorm_sub_comm {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
  (u v : TangentSpaceAux x φ hpos hsymm hdef) :
  mynorm φ hpos hsymm (u.val - v.val) = mynorm φ hpos hsymm (v.val - u.val) := by
  unfold mynorm
  have h1 : φ (u.val - v.val) (u.val - v.val) =
         φ u.val u.val - φ u.val v.val - φ v.val u.val + φ v.val v.val := by
    rw [φ.map_sub]
    simp
    rw [@sub_add]
  have h2 : φ (v.val - u.val) (v.val - u.val) =
         φ v.val v.val - φ v.val u.val - φ u.val v.val + φ u.val u.val := by
    rw [φ.map_sub]
    simp
    rw [@sub_add]
  have h3 :  φ u.val u.val - φ u.val v.val - φ v.val u.val + φ v.val v.val =
             φ v.val v.val - φ v.val u.val - φ u.val v.val + φ u.val u.val := by ring
  have : ((φ (u.val - v.val)) (u.val - v.val)) = ((φ (v.val - u.val)) (v.val - u.val)) := by
    rw [h1, h2]
    exact h3
  have : √((φ (u.val - v.val)) (u.val - v.val)) =  √((φ (v.val - u.val)) (v.val - u.val)) := by
    exact congrArg Real.sqrt this
  exact this

lemma my_eq_of_dist_eq_zero {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  ∀ {u v: TangentSpaceAux x φ hpos hsymm hdef},
    (mynorm φ hpos hsymm) (u.val - v.val) = 0 → u = v := by
    intro u v h
    rw [mynorm] at h
    have h1 : √((φ (u.val - v.val)) (u.val - v.val)) = 0 := h
    have h2 : ((φ (u.val - v.val)) (u.val - v.val)) = 0 :=
      (Real.sqrt_eq_zero (hpos (u.val - v.val))).mp h
    have h3 : u.val - v.val = 0 := (hdef (u.val - v.val)) h2
    have h4 : u.val = v.val := sub_eq_zero.mp h3
    exact (TangentSpaceAux.ext_iff φ hpos hsymm hdef u v).mpr h4

lemma my_dist_triangle {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  ∀ (x_1 y z : TangentSpaceAux x φ hpos hsymm hdef),
    (mynorm φ hpos hsymm) (x_1.val - z.val) ≤
      (mynorm φ hpos hsymm) (x_1.val - y.val) + (mynorm φ hpos hsymm) (y.val - z.val) := by
  intro u v w
  have h1 : mynorm φ hpos hsymm ((u.val - v.val) + (v.val - w.val)) ≤
    mynorm φ hpos hsymm (u.val - v.val) + mynorm φ hpos hsymm (v.val - w.val)
    := (mynorm φ hpos hsymm).add_le' (u.val - v.val) (v.val - w.val)
  have h2 : (u.val - v.val) + (v.val - w.val) = u.val - w.val :=
    sub_add_sub_cancel u.val v.val w.val
  rw [h2] at h1
  exact h1

-- NormedAddCommGroup instance
noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedAddCommGroup (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  norm := fun v => mynorm φ hpos hsymm v.val
  dist_eq := by intros; rfl
  add_assoc := fun u v w => TangentSpaceAux.ext_iff _ _ _ _ _ _|>.mpr (add_assoc u.val v.val w.val)
  zero_add := fun u => TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (zero_add u.val)
  add_zero := fun u => TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_zero u.val)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := fun u => TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (neg_add_cancel u.val)
  add_comm := fun u v => TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_comm u.val v.val)
  sub_eq_add_neg :=
    fun u v => TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (sub_eq_add_neg u.val v.val)
  dist_self := mynorm_sub_self φ hpos hsymm hdef
  dist_comm := mynorm_sub_comm φ hpos hsymm hdef
  dist_triangle := my_dist_triangle φ hpos hsymm hdef
  eq_of_dist_eq_zero := my_eq_of_dist_eq_zero φ hpos hsymm hdef

-- Module and NormedSpace instances
noncomputable
instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Module ℝ (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  one_smul u := TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (one_smul ℝ u.val)
  mul_smul a b u := TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (mul_smul a b u.val)
  smul_add a u v := TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (smul_add a u.val v.val)
  smul_zero a := TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (smul_zero a)
  zero_smul u := TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (zero_smul ℝ u.val)
  add_smul a b u := TangentSpaceAux.ext_iff _ _ _ _ _ _ |>.mpr (add_smul a b u.val)

noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedSpace ℝ (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  norm_smul_le := by
    intro a u
    have ha : φ (a • u.val) = a • φ u.val := φ.map_smul a u.val
    have hb : (φ (a • u.val)) (a • u.val) = a * (φ u.val) (a • u.val) := by
      rw [ha]
      rfl
    have hc : (φ u.val) (a • u.val) = a * (φ u.val u.val) :=
      (φ u.val).map_smul a u.val
    have hd : φ (a • u.val) (a • u.val) = a * a * φ u.val u.val := by
      rw [hb, hc]
      ring
    have h3 : norm (a • u) = mynorm φ hpos hsymm (a • u).val := rfl
    have h7 : norm (a • u) = Real.sqrt (φ (a • u.val) (a • u.val)) := h3
    have h8 : norm (a • u) = Real.sqrt ( a * a * φ u.val u.val) := by
      rw [hd] at h7
      exact h7
    have h9 : norm (a • u) = |a| * Real.sqrt (φ u.val u.val) := by
      rw [h8]
      rw [Real.sqrt_mul' (a * a) (hpos u.val)]
      have : √(a * a) = |a| := Real.sqrt_mul_self_eq_abs a
      rw [this]
    exact le_of_eq h9

lemma bbs {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  WithSeminorms (fun (_ : Fin 1) => normSeminorm ℝ (TangentSpaceAux x φ hpos hsymm hdef)) :=
  norm_withSeminorms ℝ (TangentSpaceAux x φ hpos hsymm hdef)

/-
See
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/FiniteDimension.html
-/

-- Linear equivalence between TangentSpace and TangentSpaceAux
def tangentSpaceEquiv {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  TangentSpace IB x ≃ₗ[ℝ] TangentSpaceAux x φ hpos hsymm hdef where
  toFun v := ⟨v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun u := u.val
  left_inv _ := rfl
  right_inv _ := rfl

instance {x : B} : FiniteDimensional ℝ (TangentSpace IB x) := by
  change FiniteDimensional ℝ EB
  infer_instance

instance {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  FiniteDimensional ℝ (TangentSpaceAux x φ hpos hsymm hdef) := by
  exact LinearEquiv.finiteDimensional (tangentSpaceEquiv φ hpos hsymm hdef)

-- It's continuous (finite dimensions)
lemma tangentSpaceEquiv_continuous {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Continuous (tangentSpaceEquiv φ hpos hsymm hdef).toLinearMap :=
  LinearMap.continuous_of_finiteDimensional _

lemma tangentSpaceEquiv_continuous_symm {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
    Continuous (tangentSpaceEquiv φ hpos hsymm hdef).symm.toLinearMap :=
    LinearMap.continuous_of_finiteDimensional _

noncomputable def aux {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  SeminormFamily ℝ (TangentSpace IB x) (Fin 1) := fun _ ↦ mynorm φ hpos hsymm

lemma bbr {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  WithSeminorms (aux φ hpos hsymm) := by
    have h1 : WithSeminorms fun x_1 ↦ normSeminorm ℝ (TangentSpaceAux x φ hpos hsymm hdef) :=
      norm_withSeminorms ℝ (TangentSpaceAux x φ hpos hsymm hdef)
    have h_eq : ∀ i v, aux φ hpos hsymm i v =
                       normSeminorm ℝ (TangentSpaceAux x φ hpos hsymm hdef) ⟨v⟩ := by
      intro i v
      simp [aux, mynorm]
      rfl
    let e := tangentSpaceEquiv φ hpos hsymm hdef
    apply WithSeminorms.congr (norm_withSeminorms ℝ (TangentSpace IB x))
    · have e_cont : Continuous (tangentSpaceEquiv φ hpos hsymm hdef).toLinearMap :=
      LinearMap.continuous_of_finiteDimensional _
      have : IsBoundedLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm hdef).toLinearMap := by
        rw [← IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap]
        exact ⟨LinearMap.isLinear _, e_cont⟩
      obtain ⟨C, hC⟩ := this.bound
      intro i
      use {0}, ⟨max C 1, by positivity⟩
      intro v
      simp
      have hhave : ‖(tangentSpaceEquiv φ hpos hsymm hdef) v‖ ≤ C * ‖v‖ := hC.2 v
      have h_aux_eq : aux φ hpos hsymm i v = mynorm φ hpos hsymm v := rfl
      have h_norm_eq : ‖tangentSpaceEquiv φ hpos hsymm hdef v‖ = mynorm φ hpos hsymm v := rfl
      rw [h_aux_eq, ← h_norm_eq]
      have : mynorm φ hpos hsymm v  ≤ max C 1 * ‖v‖ := calc
        mynorm φ hpos hsymm v = ‖tangentSpaceEquiv φ hpos hsymm hdef v‖ := h_norm_eq.symm
        _ ≤ C * ‖v‖ := hhave
        _ ≤ max C 1 * ‖v‖ := by gcongr; exact le_max_left C 1
      exact this
    · have e_cont : Continuous (tangentSpaceEquiv φ hpos hsymm hdef).symm.toLinearMap :=
      LinearMap.continuous_of_finiteDimensional _
      have : IsBoundedLinearMap ℝ (tangentSpaceEquiv φ hpos hsymm hdef).symm.toLinearMap := by
        rw [← IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap]
        exact ⟨LinearMap.isLinear _, e_cont⟩
      obtain ⟨C, hC⟩ := this.bound
      intro j
      use {0}, ⟨max C 1, by positivity⟩
      intro v
      simp [Finset.sup_singleton]
      have hhave :
       ‖(tangentSpaceEquiv φ hpos hsymm hdef).symm (tangentSpaceEquiv φ hpos hsymm hdef v)‖
               ≤ C * ‖tangentSpaceEquiv φ hpos hsymm hdef v‖ := hC.2 ⟨v⟩
      simp [tangentSpaceEquiv] at hhave
      have :   ‖v‖ ≤ max C 1 * (aux φ hpos hsymm j) v :=
         calc ‖v‖ ≤ C * mynorm φ hpos hsymm v := hhave
              _ ≤ max C 1 * mynorm φ hpos hsymm v := by gcongr; exact le_max_left C 1
              _ = max C 1 * aux φ hpos hsymm j v := rfl
      exact this

lemma qux {α : Type*} [Unique α] (s : Finset α) : s = ∅ ∨ s = {default} := by
  by_cases h : s = ∅
  · simp [h]
  · rw [Finset.eq_singleton_iff_nonempty_unique_mem]
    refine Or.inr ⟨Finset.nonempty_iff_ne_empty.mpr h, fun x hx ↦ Unique.uniq _ _⟩

lemma aux_tvs {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
   (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
    Bornology.IsVonNBounded ℝ {v | (φ v) v < 1} := by
  rw [WithSeminorms.isVonNBounded_iff_finset_seminorm_bounded
        (p := aux φ hpos hsymm) (bbr φ hpos hsymm hdef)]
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
        (hρ_subord := h_sub)
        (h_smooth_s_loc := by
          intro i
          have : ContMDiffOn IB (ModelWithCorners.prod IB 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
                 (fun x ↦ TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_bilin i x))
                          (extChartAt IB i).source :=
                  (g_bilin_smooth_on_chart i (baseSet_eq_extChartAt_source i))
          exact (g_bilin_smooth_on_chart i (baseSet_eq_extChartAt_source i)))
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

lemma riemannian_metric_def (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b) :
  ((g_global_bilin f b).toFun v).toFun v = 0 → v = 0 := by
  intro h
  have hpos :  v ≠ 0 → 0 < ((((g_global_bilin f b)).toFun v)).toFun v :=
    riemannian_metric_pos_def f h_sub b v
  have h0 : ((((g_global_bilin f b)).toFun v)).toFun v = 0 := h
  by_cases h : v = 0
  · exact h
  · exfalso
    have h1 : 0 < ((((g_global_bilin f b)).toFun v)).toFun v := hpos h
    have h2 : ((((g_global_bilin f b)).toFun v)).toFun v = 0 := h0
    have h3 : (0 : ℝ) < 0 := by rw [h2] at h1; exact h1
    exact lt_irrefl 0 (h1.trans_eq h2)

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
  have h3 : ∀ (v : TangentSpace IB b), ((g_global_bilin f b).toFun v).toFun v = 0 → v = 0 :=
    riemannian_metric_def f h_sub b
  exact aux_tvs (g_global_bilin f b) h1 h2 h3

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

#synth ChartedSpace (ModelProd HB EB) (TotalSpace EB (fun (b : B) ↦ (TangentSpace IB b)))

#check (IB.prod 𝓘(ℝ, EB))

#synth IsManifold (IB.prod 𝓘(ℝ, EB)) ∞  (TotalSpace EB (fun (b : B) ↦ (TangentSpace IB b)))

#synth IsManifold (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) ∞
    (TotalSpace (EB →L[ℝ] ℝ) (fun (b : B) ↦ (TangentSpace IB b →L[ℝ] ℝ)))

lemma foo (g : Π (x : B), TangentSpace IB x →L[ℝ] ℝ) :
    ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] ℝ)) ∞
      (fun b ↦ TotalSpace.mk' (EB →L[ℝ] ℝ) b (g b)) := by
  sorry

#check TotalSpace (EB →L[ℝ] ℝ)

#check TotalSpace
  (EB →L[ℝ] EB →L[ℝ] ℝ)
  (fun (b : B) ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ)

#check IsManifold (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
  (TotalSpace
  (EB →L[ℝ] EB →L[ℝ] ℝ)
  (fun (b : B) ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ))

#synth IsManifold (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
  (TotalSpace
  (EB →L[ℝ] EB →L[ℝ] ℝ)
  (fun (b : B) ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ))

noncomputable
def g_bilim (i p : B) :
  (TangentSpace IB) p →L[ℝ]  ((TangentSpace IB) p →L[ℝ] Trivial B ℝ p) := by
  let dψ := mfderiv IB 𝓘(ℝ, EB) (extChartAt IB i) p
  let inner := innerSL ℝ (E := EB)
  exact inner.comp dψ |>.flip.comp dψ

#check fun i => FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)) i
#check Trivialization
#check FiberBundle.trivializationAt (EB →L[ℝ] ℝ) (fun (b : B) ↦ (TangentSpace IB b →L[ℝ] ℝ))
#check FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
  (fun (b : B) ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ)

#check VectorBundle
#check TangentBundle
#check extChartAt

#synth ChartedSpace (ModelProd HB EB) (TotalSpace EB (fun (b : B) ↦ (TangentSpace IB b)))

#synth ChartedSpace (ModelProd HB EB) (TangentBundle IB B)
#check (inferInstance : ChartedSpace (ModelProd HB EB) (TangentBundle IB B))
#print FiberBundle.chartedSpace

#check extChartAt (IB.prod 𝓘(ℝ, EB))
#check fun (p : TangentBundle IB B) =>
  (FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)) (p.proj)).toPartialEquiv
#check fun (i : B) => extChartAt IB i

#check (FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)))
#check (FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b))).comp
#check (FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b))).comp sorry

#check Function.comp (FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b))) sorry

#check ContMDiffVectorBundle ∞ EB (fun (b : B) ↦ (TangentSpace IB b)) IB
#synth ContMDiffVectorBundle ∞ EB (fun (b : B) ↦ (TangentSpace IB b)) IB

#check ContMDiffVectorBundle ∞ (EB →L[ℝ] ℝ) (fun (b : B) ↦ TangentSpace IB b →L[ℝ] ℝ) IB
#synth ContMDiffVectorBundle ∞ (EB →L[ℝ] ℝ) (fun (b : B) ↦ TangentSpace IB b →L[ℝ] ℝ) IB

#check ContMDiffVectorBundle ∞
  (EB →L[ℝ] EB →L[ℝ] ℝ)
  (fun b ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ)

#synth TopologicalSpace (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
                   (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)))

#synth TopologicalSpace (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
 (fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ))

#check ContMDiffVectorBundle ∞
  (EB →L[ℝ] EB →L[ℝ] ℝ)
  (fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) IB

#synth ContMDiffVectorBundle ∞
  (EB →L[ℝ] EB →L[ℝ] ℝ)
  (fun b ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) IB

#check (extChartAt IB).comp sorry

#check fun (i : B) => PartialEquiv.prod (extChartAt IB i) (extChartAt IB i)

def eek : PartialEquiv (B × EB) (EB × EB) :=
  PartialEquiv.prod (extChartAt IB sorry) (PartialEquiv.refl EB)

#check PartialEquiv.trans eek

#check fun (p : TangentBundle IB B) =>
  ((FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)) (p.proj)).toPartialEquiv)
  ≫ eek

#check FiberBundle.extChartAt

example (p : TangentBundle IB B) :
  extChartAt (IB.prod 𝓘(ℝ, EB)) p =
    (trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)) p.proj).toPartialEquiv ≫
    (extChartAt IB p.proj).prod (PartialEquiv.refl EB) :=
    FiberBundle.extChartAt p

example (p : TangentBundle IB B) :
  extChartAt (IB.prod 𝓘(ℝ, EB)) p =
  (trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)) (p.proj)).toPartialEquiv ≫
  (PartialEquiv.prod (extChartAt IB p.proj) (PartialEquiv.refl EB))
  := FiberBundle.extChartAt p

noncomputable
def g_bilin_ng (i b : B) :
 (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
             (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)) :=
  let χ : Trivialization EB TotalSpace.proj :=
   FiberBundle.trivializationAt EB (fun (x : B) ↦ (TangentSpace IB x)) i
  let innerAtP : EB →L[ℝ] EB →L[ℝ] ℝ := by
    have : (TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) = (EB →L[ℝ] EB →L[ℝ] ℝ) := rfl
    let innerOnTangent : (TangentSpace IB b) →L[ℝ] (TangentSpace IB b) →L[ℝ] ℝ :=
    { toFun := fun u => {
        toFun := fun v => innerSL ℝ (χ u).2 (χ v).2,
        map_add' := sorry,
        map_smul' := sorry,
        cont := sorry
      },
      map_add' := sorry,
      map_smul' := sorry,
      cont := sorry
    }
    exact cast this innerOnTangent
  let ψ := FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i
  ψ.invFun (b, innerAtP)

#check (FiberBundle.trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)))
#check Trivialization EB TotalSpace.proj

-- I don't think this is needed
lemma baseSet_eq_extChartAt_source' (i : B) :
    (FiberBundle.trivializationAt (EB →L[ℝ] ℝ)
      (fun b ↦ TangentSpace IB b →L[ℝ] ℝ) i).baseSet =
    (extChartAt IB i).source := by
  simp only [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
      Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_univ,
      extChartAt, PartialHomeomorph.extend, PartialEquiv.trans_source,
      PartialHomeomorph.toFun_eq_coe, ModelWithCorners.source_eq, Set.preimage_univ]

#check Trivialization.contMDiffOn

example (p : TangentBundle IB B) : ContMDiffOn (IB.prod 𝓘(ℝ, EB)) (IB.prod 𝓘(ℝ, EB)) ∞
  (trivializationAt EB (fun (b : B) ↦ TangentSpace IB b) p.proj)
  (trivializationAt EB (fun (b : B) ↦ TangentSpace IB b) p.proj).source :=
  Trivialization.contMDiffOn
    (trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)) p.proj)

example (p : TangentBundle IB B) : ContMDiffOn (IB.prod 𝓘(ℝ, EB)) (IB.prod 𝓘(ℝ, EB)) ∞
  (trivializationAt EB (fun (b : B) ↦ (TangentSpace IB b)) p.proj)
  (extChartAt (IB.prod 𝓘(ℝ, EB)) p).source := by
  exact sorry

example (i : B) :
  let ψ := FiberBundle.trivializationAt (B := B) (F := EB →L[ℝ] EB →L[ℝ] ℝ)
    (E := (fun (x : B) ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ))
    (b := i)
  ContMDiffOn (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    ψ.toPartialEquiv.symm ψ.target :=
  Trivialization.contMDiffOn_symm _

lemma g_bilin_ng_smooth_on_chart (i : B) :
  ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (g_bilin_ng (EB := EB) (IB := IB) i)
    (extChartAt IB i).source := by
  -- intro b hb
  have h0 : (trivializationAt
    (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun b ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) i).baseSet =
    (extChartAt IB i).source := baseSet_eq_extChartAt_source i

  let χ : Trivialization EB TotalSpace.proj :=
    trivializationAt EB (fun (x : B) ↦ (TangentSpace IB x)) i


  let innerAtP (c : B) (hc : c ∈ χ.baseSet) : EB →L[ℝ] EB →L[ℝ] ℝ := by
    have : (TangentSpace IB c →L[ℝ] TangentSpace IB c →L[ℝ] ℝ) = (EB →L[ℝ] EB →L[ℝ] ℝ) := rfl
    let innerOnTangent : (TangentSpace IB c) →L[ℝ] (TangentSpace IB c) →L[ℝ] ℝ :=
    { toFun := fun u => {
        toFun := fun v => innerSL ℝ (χ u).2 (χ v).2,
        map_add' := by
          have h1 := χ.linear ℝ hc
          intro x y

          have h2 : (χ { proj := c, snd := x + y }).2 =
                 (χ { proj := c, snd := x}).2 + (χ { proj := c, snd := y}).2 := h1.map_add x y
          rw [h2]
          exact ContinuousLinearMap.map_add
                 ((innerSL ℝ) (χ { proj := c, snd := u }).2)
                 (χ { proj := c, snd := x }).2 (χ { proj := c, snd := y }).2
        map_smul' := sorry,
        cont := sorry
      },
      map_add' := sorry,
      map_smul' := sorry,
      cont := sorry
    }
    exact cast this innerOnTangent

  let ψ := FiberBundle.trivializationAt (B := B) (F := EB →L[ℝ] EB →L[ℝ] ℝ)
    (E := (fun (x : B) ↦ (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ))
    (b := i)

  have h2 : ContMDiffOn (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    ψ.toPartialEquiv.symm ψ.target := Trivialization.contMDiffOn_symm _

  let foo := fun b => ψ.toPartialEquiv.symm.toFun (b, innerAtP b sorry)

  have h3 : g_bilin_ng i = foo := by
    funext b
    unfold g_bilin_ng foo innerAtP χ ψ
    simp

  have h4 : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun b => (b, innerAtP b sorry)) (extChartAt IB i).source := sorry

  exact sorry
