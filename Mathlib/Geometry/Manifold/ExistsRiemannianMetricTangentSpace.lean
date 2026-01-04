/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Dominic Steinitz
-/

import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Distribution.SchwartzSpace

/-! ## Existence of a Riemannian bundle metric

Using a partition of unity, we prove the existence of a smooth Riemannian metric.
Specialized attempt.

-/

set_option linter.unusedSectionVars false

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

noncomputable instance (p : B) : NormedAddCommGroup (TangentSpace IB p) := by
  change NormedAddCommGroup EB
  infer_instance

noncomputable instance (p : B) : NormedSpace ℝ (TangentSpace IB p) := by
  change NormedSpace ℝ EB
  infer_instance

/-
We have two definitions of a local section of bilinear forms.
Well the second is the fiber component at a point.
The first definition is "obviously" smooth: it's a pair of the identity function and a constant
function. The required properties of symmetry and positive definiteness are more easily proved
using the second definition and showing that the definitions are essentially the same.
-/
noncomputable
def g_bilin_1 (i b : B) :
 (TotalSpace (EB →L[ℝ] EB →L[ℝ] ℝ)
             (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)) := by
  let ψ := FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i
  by_cases h : (b, (fun (x : B) ↦ innerSL ℝ) b) ∈ ψ.target
  · exact ψ.invFun (b, (fun (x : B) ↦ innerSL ℝ) b)
  · exact ⟨b, 0⟩

noncomputable
def g_bilin_2 (i p : B) :
  (TangentSpace IB) p →L[ℝ]  ((TangentSpace IB) p →L[ℝ] ℝ) := by
  let χ := trivializationAt EB (TangentSpace (M := B) IB) i
  let inner := innerSL ℝ (E := EB)
  by_cases h : p ∈ χ.baseSet
  · exact (innerSL ℝ).comp (χ.continuousLinearMapAt ℝ p) |>.flip.comp (χ.continuousLinearMapAt ℝ p)
  · exact 0

/-
Overloading the use of π, let φ : π⁻¹(U) → U × ℝⁿ and ψ : π⁻¹(U) → U × (ℝⁿ ⊗ ℝⁿ →ₗ ℝ) be local
trivialisations of the tangent bundle and the bundle of bilinear forms respectively and
w ∈ π⁻¹(U) and (x, u) and (y, v) ∈ U × ℝⁿ then ψ(w)(u, v) = w(φ⁻¹(x, u), φ⁻¹(x, v))
-/
lemma trivializationAt_tangentSpace_bilinearForm_apply (x₀ x : B)
    (w : (TangentSpace (M := B) IB) x →L[ℝ] (TangentSpace (M := B) IB) x →L[ℝ] ℝ)
    (u v : EB)
    (hx : x ∈ (trivializationAt EB (TangentSpace (M := B) IB) x₀).baseSet) :
  (trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
                    (fun x ↦ (TangentSpace (M := B) IB) x →L[ℝ]
                             (TangentSpace (M := B) IB) x →L[ℝ]
                              ℝ) x₀).continuousLinearMapAt ℝ x w u v =
  w ((trivializationAt EB (TangentSpace (M := B) IB) x₀).symm x u)
    ((trivializationAt EB (TangentSpace (M := B) IB) x₀).symm x v) := by
  rw [Trivialization.continuousLinearMapAt_apply]
  rw [@Trivialization.linearMapAt_apply]
  simp only [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
      Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_univ,
      Set.inter_self]
  have hx' : x ∈ (chartAt HB x₀).source ∩ ((chartAt HB x₀).source ∩ Set.univ) := by
    simpa [Trivialization.baseSet, hx]
  rw [@hom_trivializationAt_apply]
  simp only [hx', ↓reduceIte]
  rw [inCoordinates_apply_eq₂ hx hx (by simp : x ∈ (trivializationAt ℝ (fun _ ↦ ℝ) x₀).baseSet)]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization,
      LinearMap.id_coe, id_eq]

/-
We are going to show that `(g_bilin_1 (IB := IB) i b).snd.toFun α β = (g_bilin_2 i b).toFun α β`
and given that both of these are defined by two cases (effectively if b is in the source of the
trivialisation at i) then we need 4 different cases. This is the essential case.
-/
lemma g_bilin_eq_00 (i b : B)
  (hb : b ∈ (trivializationAt EB (TangentSpace IB) i).baseSet)
  (hc : b ∈ (FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i).baseSet)
  (α β : TangentSpace IB b) :
  (((FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i).toPartialHomeomorph.symm
      (b, innerSL ℝ)).snd α) β =
    ((innerSL ℝ)
      ((Trivialization.linearMapAt ℝ (trivializationAt EB (TangentSpace (M := B) IB) i) b) β))
      ((Trivialization.linearMapAt ℝ (trivializationAt EB (TangentSpace (M := B) IB) i) b) α) := by
  simp only [innerSL_apply]
  let ψ := FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i
  let χ := trivializationAt EB (TangentSpace (M := B) IB) i
  let w := ψ.symm b (innerSL ℝ)
  have h1 : ∀ u v,
    (((Trivialization.continuousLinearMapAt ℝ ψ b) w) u) v =
     w (χ.symm b u) (χ.symm b v)
     := fun u v ↦ trivializationAt_tangentSpace_bilinearForm_apply i b w u v hb
  have h4 : ∀ u v,
    (((Trivialization.continuousLinearMapAt ℝ ψ b) (ψ.symmL ℝ b (innerSL ℝ))) u) v =
    innerSL ℝ u v := by
    intro u v
    rw [Trivialization.continuousLinearMapAt_symmL ψ hc]
  have h3 : ∀ u v, innerSL ℝ u v = w (χ.symm b u) (χ.symm b v) := by
    intro u v
    rw [<-h4]
    exact h1 u v

  have ha : χ.symm b (χ.continuousLinearMapAt ℝ b α) = α :=
    Trivialization.symmL_continuousLinearMapAt
      (trivializationAt EB (TangentSpace (M := B) IB) i) hb α

  have hb : χ.symm b (χ.continuousLinearMapAt ℝ b β) = β :=
    Trivialization.symmL_continuousLinearMapAt
      (trivializationAt EB (TangentSpace (M := B) IB) i) hb β

  have hp : (innerSL ℝ) ((Trivialization.continuousLinearMapAt ℝ χ b) α)
                     ((Trivialization.continuousLinearMapAt ℝ χ b) β) =
    w (χ.symm b ((Trivialization.continuousLinearMapAt ℝ χ b) α))
      (χ.symm b ((Trivialization.continuousLinearMapAt ℝ χ b) β)) :=
       h3 (χ.continuousLinearMapAt ℝ b α) (χ.continuousLinearMapAt ℝ b β)

  rw [ha, hb] at hp

  have hd : (innerSL ℝ) ((Trivialization.continuousLinearMapAt ℝ χ b) α)
                        ((Trivialization.continuousLinearMapAt ℝ χ b) β) =
    w α β := hp

  have he : ψ.symm b (innerSL ℝ) =
            (ψ.toPartialHomeomorph.symm (b, innerSL ℝ)).snd := by
    rw [Trivialization.symm_apply ψ hc (innerSL ℝ)]
    exact rfl

  have hf : (innerSL ℝ) ((Trivialization.continuousLinearMapAt ℝ χ b) α)
                        ((Trivialization.continuousLinearMapAt ℝ χ b) β) =
    ψ.symm b (innerSL ℝ) α β := hp

  rw [he] at hf

  have hs : (ψ.toPartialHomeomorph.symm (b, innerSL ℝ)).snd α β =
  (innerSL ℝ) ((Trivialization.linearMapAt ℝ χ b) α)
               ((Trivialization.linearMapAt ℝ χ b) β) := id (Eq.symm hf)

  have ht : (innerSL ℝ) ((Trivialization.linearMapAt ℝ χ b) α)
                        ((Trivialization.linearMapAt ℝ χ b) β) =
            (innerSL ℝ) ((Trivialization.linearMapAt ℝ χ b) β)
                        ((Trivialization.linearMapAt ℝ χ b) α) := by
    exact real_inner_comm ((Trivialization.linearMapAt ℝ χ b) β)
                          ((Trivialization.linearMapAt ℝ χ b) α)

  have hr : (ψ.toPartialHomeomorph.symm (b, innerSL ℝ)).snd α β =
  (innerSL ℝ) ((Trivialization.linearMapAt ℝ χ b) β)
              ((Trivialization.linearMapAt ℝ χ b) α) := by
    rw [<-ht]
    exact hs

  exact hr

set_option maxHeartbeats 400000 in
-- comment explaining why this is necessary
lemma g_bilin_eq (i b : B)
  (α β : TangentSpace IB b) :
  (g_bilin_1 (IB := IB) i b).snd.toFun α β = (g_bilin_2 i b).toFun α β := by
  unfold g_bilin_1 g_bilin_2

  let ψ := FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun (x : B) ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i
  let χ := trivializationAt EB (TangentSpace (M := B) IB) i
  let w := ψ.symm b (innerSL ℝ)

  simp only []
  split_ifs with hh1
  · simp only [hom_trivializationAt_target, TangentBundle.trivializationAt_baseSet,
      hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_baseSet,
      PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm, dite_eq_ite,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    split_ifs with hh2
    · have hha : (b, innerSL ℝ) ∈
        (trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
         (fun x ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i).target := hh1
      have hhb : (b, innerSL ℝ) ∈
        ((chartAt HB i).source ∩ ((chartAt HB i).source ∩ Set.univ)) ×ˢ Set.univ := hh2
      have hhc : b ∈ (chartAt HB i).source := Set.mem_of_mem_inter_left hh2.1
      have hhd : ((ψ.toPartialHomeomorph.symm (b, innerSL ℝ)).snd α) β =
        ((innerSL ℝ) ((Trivialization.linearMapAt ℝ χ b) β))
                     ((Trivialization.linearMapAt ℝ χ b) α) := g_bilin_eq_00 i b hhc hha.1 α β
      rw [if_pos hhc, if_pos hhb]
      exact hhd
    · exact False.elim (hh2 hh1)
  · simp only [hom_trivializationAt_target, TangentBundle.trivializationAt_baseSet,
      hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_baseSet,
      PartialEquiv.invFun_as_coe, PartialHomeomorph.coe_coe_symm, dite_eq_ite,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    split_ifs with hh2
    · exact False.elim (hh1 hh2)
    · have hha : (b, innerSL ℝ) ∉
        (trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
         (fun x ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i).target := hh1
      have hhb : (b, innerSL ℝ) ∉
        ((chartAt HB i).source ∩ ((chartAt HB i).source ∩ Set.univ)) ×ˢ Set.univ := hh2
      have hhc : b ∉ (chartAt HB i).source := by
        intro hcontra
        have : (b, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) ∈
          ((chartAt HB i).source ∩ ((chartAt HB i).source ∩ Set.univ)) ×ˢ Set.univ := by
          simp only [Set.inter_univ, Set.inter_self, Set.mem_prod, Set.mem_univ, and_true]
          exact hcontra
        contradiction
      rw [if_neg hhc, if_neg hhb]

lemma g_nonneg (j b : B) (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b) :
  0 ≤ ((((g_bilin_2 j b)).toFun v)).toFun v := by
    unfold g_bilin_2
    simp
    split_ifs with h
    · have : b ∈ (chartAt HB j).source := h
      simp
      let χ := (trivializationAt EB (TangentSpace IB) j)
      have h1 : ((innerSL ℝ).comp (Trivialization.continuousLinearMapAt ℝ χ b)).flip.comp
                               (Trivialization.continuousLinearMapAt ℝ χ b) v v =
             innerSL ℝ ((Trivialization.continuousLinearMapAt ℝ χ b) v)
                       ((Trivialization.continuousLinearMapAt ℝ χ b) v) := rfl
      have h2 : 0 ≤ innerSL ℝ ((Trivialization.continuousLinearMapAt ℝ χ b) v)
                       ((Trivialization.continuousLinearMapAt ℝ χ b) v) := by
        exact @inner_self_nonneg ℝ _ _ _ _ _
      rw [<-h1] at h2
      exact h2
    · simp

lemma g_pos (i b : B) (hp : b ∈ (extChartAt IB i).source)
            (v : (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) b) (hv : v ≠ 0) :
  0 < ((((g_bilin_2 i b)).toFun v)).toFun v := by
  unfold g_bilin_2
  simp
  split_ifs with hh1
  · let χ := (trivializationAt EB (TangentSpace IB) i)
    have h1 : ((innerSL ℝ).comp (Trivialization.continuousLinearMapAt ℝ χ b)).flip.comp
                               (Trivialization.continuousLinearMapAt ℝ χ b) v v =
             innerSL ℝ ((Trivialization.continuousLinearMapAt ℝ χ b) v)
                       ((Trivialization.continuousLinearMapAt ℝ χ b) v) := rfl
    have h2 : innerSL ℝ ((Trivialization.continuousLinearMapAt ℝ χ b) v)
                       ((Trivialization.continuousLinearMapAt ℝ χ b) v) ≠ 0 ↔
                       ((Trivialization.continuousLinearMapAt ℝ χ b) v) ≠ 0 := by
        exact inner_self_ne_zero

    have h3 : ((Trivialization.continuousLinearMapAt ℝ χ b) v ≠ 0 ↔ v ≠ 0) := by
      have : ((Trivialization.continuousLinearEquivAt ℝ χ b hh1) v) =
             ((Trivialization.continuousLinearMapAt ℝ χ b) v) :=
              congrArg (fun f => f v) (Trivialization.coe_continuousLinearEquivAt_eq χ hh1)
      rw [<-this]
      exact AddEquivClass.map_ne_zero_iff

    have h4 : ((Trivialization.continuousLinearMapAt ℝ χ b) v) ≠ 0 := h3.mpr hv
    have h5 : innerSL ℝ ((Trivialization.continuousLinearMapAt ℝ χ b) v)
                       ((Trivialization.continuousLinearMapAt ℝ χ b) v) ≠ 0 := h2.mpr h4
    have h6 : 0 ≤ innerSL ℝ ((Trivialization.continuousLinearMapAt ℝ χ b) v)
                       ((Trivialization.continuousLinearMapAt ℝ χ b) v) := by
      exact @inner_self_nonneg ℝ _ _ _ _ _
    exact Std.lt_of_le_of_ne h6 (id (Ne.symm h5))
  · exfalso
    apply hh1
    exact Set.mem_of_mem_inter_left hp

/-- The seminorm induced by a positive semi-definite symmetric bilinear form.

Given a bilinear form `φ : TₓB →L[ℝ] TₓB →L[ℝ] ℝ` that is positive semi-definite and symmetric,
we define the associated seminorm by `‖v‖_φ := √(φ(v,v))`.

**Why do we need this?**

To show that a Riemannian metric is smooth, we need to verify that it's compatible with
the bornology (bounded sets) of the tangent space. In mathlib, the dependency chain is:

  Norm → Bounded sets → Bornology → Smoothness works → Riemannian metric can be defined

So we need to connect our bilinear form to the existing norm structure.

**Why not just use the existing norm on `TangentSpace IB x`?**

Because we need to work with the geometry induced by `φ`, not the ambient geometry.
However, mathlib's type system doesn't let us "change" the norm on an existing type.
The solution (see `TangentSpaceAux` below) is to create a copy of the tangent space
with the φ-induced norm, then prove the two are equivalent via finite-dimensionality.

The triangle inequality follows from the Cauchy-Schwarz inequality for bilinear forms.
-/
noncomputable def seminormOfBilinearForm {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
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

/-- Auxiliary tangent space with norm induced by a bilinear form.

This is a copy of `TangentSpace IB x` with the norm `‖v‖_φ := √(φ(v,v))` from `mynorm`.

**Why create a new type?**

Mathlib's type class system doesn't support having multiple norm structures on the same type.
As the mathlib documentation states (Analysis.NormedSpace.FiniteDimension):

> "The fact that all norms are equivalent is not written explicitly, as it would mean having
> two norms on a single space, which is not the way type classes work. However, if one has a
> finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another
> norm, then the identities from `E` to `E'` and from `E'` to `E` are continuous thanks to
> `LinearMap.continuous_of_finiteDimensional`. This gives the desired norm equivalence."

What this description elides is that "this gives the desired norm equivalence" requires
creating this auxiliary type plus substantial additional work (see `tangentSpaceEquiv`,
`bbr`, and `aux_tvs`) to establish the equivalence and derive the needed `WithSeminorms`
and `IsVonNBounded` properties.

In classical mathematics, "all norms on a finite-dimensional space are equivalent" is a
one-line citation. In mathlib, making this work requires explicit construction and proof.
-/
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

noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v)
  (hsymm : ∀ u v, φ u v = φ v u)
  (hdef : ∀ v, φ v v = 0 → v = 0) :
  Norm (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  norm v := seminormOfBilinearForm φ hpos hsymm v.val

lemma seminormOfBilinearForm_sub_self {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
  (v : TangentSpaceAux x φ hpos hsymm hdef) :
  seminormOfBilinearForm φ hpos hsymm (v.val - v.val) = 0 := by
  unfold seminormOfBilinearForm
  simp

lemma seminormOfBilinearForm_sub_comm {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0)
  (u v : TangentSpaceAux x φ hpos hsymm hdef) :
  seminormOfBilinearForm φ hpos hsymm (u.val - v.val) =
  seminormOfBilinearForm φ hpos hsymm (v.val - u.val) := by
  unfold seminormOfBilinearForm
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
    (seminormOfBilinearForm φ hpos hsymm) (u.val - v.val) = 0 → u = v := by
    intro u v h
    rw [seminormOfBilinearForm] at h
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
    (seminormOfBilinearForm φ hpos hsymm) (x_1.val - z.val) ≤
      (seminormOfBilinearForm φ hpos hsymm) (x_1.val - y.val) +
      (seminormOfBilinearForm φ hpos hsymm) (y.val - z.val) := by
  intro u v w
  have h1 : seminormOfBilinearForm φ hpos hsymm ((u.val - v.val) + (v.val - w.val)) ≤
    seminormOfBilinearForm φ hpos hsymm (u.val - v.val) +
    seminormOfBilinearForm φ hpos hsymm (v.val - w.val)
    := (seminormOfBilinearForm φ hpos hsymm).add_le' (u.val - v.val) (v.val - w.val)
  have h2 : (u.val - v.val) + (v.val - w.val) = u.val - w.val :=
    sub_add_sub_cancel u.val v.val w.val
  rw [h2] at h1
  exact h1

noncomputable instance {x : B}
  (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) (hdef : ∀ v, φ v v = 0 → v = 0) :
  NormedAddCommGroup (@TangentSpaceAux EB _ _ _ _ IB B _ _ x φ hpos hsymm hdef) where
  norm := fun v => seminormOfBilinearForm φ hpos hsymm v.val
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
  dist_self := seminormOfBilinearForm_sub_self φ hpos hsymm hdef
  dist_comm := seminormOfBilinearForm_sub_comm φ hpos hsymm hdef
  dist_triangle := my_dist_triangle φ hpos hsymm hdef
  eq_of_dist_eq_zero := my_eq_of_dist_eq_zero φ hpos hsymm hdef

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
    have h3 : norm (a • u) = seminormOfBilinearForm φ hpos hsymm (a • u).val := rfl
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

/-
See
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Module/FiniteDimension.html
-/

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

noncomputable def aux {x : B} (φ : TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ)
  (hpos : ∀ v, 0 ≤ φ v v) (hsymm : ∀ u v, φ u v = φ v u) :
  SeminormFamily ℝ (TangentSpace IB x) (Fin 1) := fun _ ↦ seminormOfBilinearForm φ hpos hsymm

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
      simp [aux, seminormOfBilinearForm]
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
      have h_aux_eq : aux φ hpos hsymm i v = seminormOfBilinearForm φ hpos hsymm v := rfl
      have h_norm_eq : ‖tangentSpaceEquiv φ hpos hsymm hdef v‖ =
                       seminormOfBilinearForm φ hpos hsymm v := rfl
      rw [h_aux_eq, ← h_norm_eq]
      have : seminormOfBilinearForm φ hpos hsymm v  ≤ max C 1 * ‖v‖ := calc
        seminormOfBilinearForm φ hpos hsymm v =
        ‖tangentSpaceEquiv φ hpos hsymm hdef v‖ := h_norm_eq.symm
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
         calc ‖v‖ ≤ C * seminormOfBilinearForm φ hpos hsymm v := hhave
              _ ≤ max C 1 * seminormOfBilinearForm φ hpos hsymm v := by
                gcongr; exact le_max_left C 1
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
  simp only [aux, seminormOfBilinearForm]
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

theorem g_bilin_symm_2 (i p : B) (v w : TangentSpace IB p) :
    ((g_bilin_2 i p).toFun v).toFun w =
    ((g_bilin_2 i p).toFun w).toFun v := by
  unfold g_bilin_2
  simp only []
  split_ifs with h
  · simp
    rw [real_inner_comm]
  · simp

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
def g_global_bilin_2 (f : SmoothPartitionOfUnity B IB B) (p : B) :
    W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p := ∑ᶠ (j : B), (f j) p • g_bilin_2 j p

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
  (h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin_2 j b) : W (TangentSpace IB) b)).Finite) :
  ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun v).toFun w =
  ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun w).toFun v := by

    have ha : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun v).toFun w =
              ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun v).toFun w := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

    have ha' : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun w).toFun v =
              ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun w).toFun v := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
      rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

    let h : (j : B) → W ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) b :=
      fun j ↦ (f j) b • g_bilin_2 j b

    have h_inc : (Function.support h) ⊆ h_fin.toFinset :=
      Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a

    have hb : ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun v).toFun w =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun v).toFun w :=
      finsum_image_eq_sum (evalAt b v w) h h_fin.toFinset h_inc

    have hb' : ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun w).toFun v =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun w).toFun v :=
      finsum_image_eq_sum (evalAt b w v) h h_fin.toFinset h_inc

    have h_gbilin_symm : ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun v).toFun w =
                         ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun w).toFun v := by
      have h5 : ∀ (j : B), (((g_bilin_2 j b)).toFun v).toFun w =
                           (((g_bilin_2 j b)).toFun w).toFun v := fun j => g_bilin_symm_2 j b v w
      have h6 : ∀ (j : B), (f j b) * ((g_bilin_2 j b).toFun v).toFun w =
                           (f j b) * ((g_bilin_2 j b).toFun w).toFun v :=
        fun j ↦ congrArg (HMul.hMul ((f j) b)) (h5 j)
      exact finsum_congr h6

    calc
        ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun v).toFun w
          = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun v).toFun w := ha.symm
        _ = ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun v).toFun w := hb.symm
        _ = ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun w).toFun v := h_gbilin_symm
        _ = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun w).toFun v := hb'
        _ = ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun w).toFun v := ha'

lemma riemannian_metric_symm (f : SmoothPartitionOfUnity B IB B) (b : B) (v w : TangentSpace IB b) :
  ((g_global_bilin_2 f b).toFun v).toFun w = ((g_global_bilin_2 f b).toFun w).toFun v := by
  unfold g_global_bilin_2
  simp
  have h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin_2 j b) :
                  W (TangentSpace IB) b)).Finite := by
      apply (f.locallyFinite'.point_finite b).subset
      intro i hi
      simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
      simp only [Set.mem_setOf_eq, Function.mem_support, ne_eq]
      exact hi.1
  have h6a : (∑ᶠ (j : B), (f j) b • g_bilin_2 j b) =
            ∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b := finsum_eq_sum _ h_fin
  rw [h6a]
  have : ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun v).toFun w =
         ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun w).toFun v :=
    h_need f b v w h_fin
  exact this

lemma g_global_bilin_2_eq_sum (f : SmoothPartitionOfUnity B IB B) (p : B) :
  g_global_bilin_2 f p = ∑ᶠ (j : B), (f j) p • g_bilin_2 j p := rfl

lemma baseSet_eq_extChartAt_source (i : B) :
    (FiberBundle.trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
      (fun b ↦ TangentSpace IB b →L[ℝ] TangentSpace IB b →L[ℝ] ℝ) i).baseSet =
    (extChartAt IB i).source := by
  simp only [hom_trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
      Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.inter_univ,
      Set.inter_self, extChartAt, PartialHomeomorph.extend, PartialEquiv.trans_source,
      PartialHomeomorph.toFun_eq_coe, ModelWithCorners.source_eq, Set.preimage_univ]

lemma h_need' (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b)
  (h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin_2 j b) : W (TangentSpace IB) b)).Finite) :
  v ≠ 0 → 0 < ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun v).toFun v := by

  have ha : ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun v).toFun v =
            ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun v).toFun v := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]

  let h : (j : B) → W ((@TangentSpace ℝ _ _ _ _ _ _ IB B _ _)) b :=
    fun j ↦ (f j) b • g_bilin_2 j b

  let h' x := f x b * ((g_bilin_2 x b).toFun v).toFun v

  have h_inc : (Function.support h) ⊆ h_fin.toFinset :=
      Set.Finite.toFinset_subset.mp fun ⦃a⦄ a ↦ a

  have hb : ∑ᶠ (j : B), (((f j) b • g_bilin_2 j b).toFun v).toFun v =
           ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun v).toFun v :=
      finsum_image_eq_sum (evalAt b v v) h h_fin.toFinset h_inc

  have : ∀ j, (((f j) b • g_bilin_2 j b).toFun v).toFun v = h' j := by
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
    have : f x b ≠ 0 ∧ (((g_bilin_2 x b)).toFun v).toFun v ≠ 0 := hx
    have : (f x) b * ((g_bilin_2 x b).toFun v).toFun v ≠ 0 := mul_ne_zero_iff.mpr this
    exact mul_ne_zero_iff.mp this |>.1
  have h4 : 0 < ∑ᶠ i, h' i := finsum_pos' h1 h2 h3

  have h5 : ∑ᶠ i, h' i  = ∑ᶠ i, (((f i) b • g_bilin_2 i b).toFun v).toFun v := rfl
  have h6 : ∑ᶠ i, h' i  = ∑ j ∈ h_fin.toFinset, (((f j) b • g_bilin_2 j b).toFun v).toFun v := by
    rw [hb] at h5
    exact h5
  have h7 : ∑ᶠ i, h' i = ((∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b).toFun v).toFun v := by
    rw [ha] at h6
    exact h6

  exact lt_of_lt_of_eq h4 h7

lemma riemannian_metric_pos_def (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b) :
  v ≠ 0 → 0 < ((g_global_bilin_2 f b).toFun v).toFun v := by
  intro hv
  unfold g_global_bilin_2
  have h_fin : (Function.support fun j ↦ ((f j) b • (g_bilin_2 j b) :
                W (TangentSpace IB) b)).Finite := by
    apply (f.locallyFinite'.point_finite b).subset
    intro i hi
    simp only [Function.mem_support, ne_eq, smul_eq_zero, not_or] at hi
    simp only [Set.mem_setOf_eq, Function.mem_support, ne_eq]
    exact hi.1
  have h6a : (∑ᶠ (j : B), (f j) b • g_bilin_2 j b) =
            ∑ j ∈ h_fin.toFinset, (f j) b • g_bilin_2 j b := finsum_eq_sum _ h_fin
  rw [h6a]
  exact h_need' f h_sub b v h_fin hv

lemma riemannian_metric_def (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b) :
  ((g_global_bilin_2 f b).toFun v).toFun v = 0 → v = 0 := by
  intro h
  have hpos :  v ≠ 0 → 0 < ((((g_global_bilin_2 f b)).toFun v)).toFun v :=
    riemannian_metric_pos_def f h_sub b v
  have h0 : ((((g_global_bilin_2 f b)).toFun v)).toFun v = 0 := h
  by_cases h : v = 0
  · exact h
  · exfalso
    have h1 : 0 < ((((g_global_bilin_2 f b)).toFun v)).toFun v := hpos h
    have h2 : ((((g_global_bilin_2 f b)).toFun v)).toFun v = 0 := h0
    have h3 : (0 : ℝ) < 0 := by rw [h2] at h1; exact h1
    exact lt_irrefl 0 (h1.trans_eq h2)

lemma riemannian_unit_ball_bounded (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ∀ (b : B), Bornology.IsVonNBounded ℝ
    {v  : TangentSpace IB b | ((g_global_bilin_2 f b).toFun v).toFun v < 1} := by
  intro b
  have h1 : ∀ (v : TangentSpace IB b), 0 ≤ ((g_global_bilin_2 f b).toFun v).toFun v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact le_of_lt (riemannian_metric_pos_def f h_sub b v hv)
  have h2 : ∀ (u v : TangentSpace IB b),
    ((g_global_bilin_2 f b).toFun u).toFun v = ((g_global_bilin_2 f b).toFun v).toFun u := by
    exact fun u v ↦ riemannian_metric_symm f b u v
  have h3 : ∀ (v : TangentSpace IB b), ((g_global_bilin_2 f b).toFun v).toFun v = 0 → v = 0 :=
    riemannian_metric_def f h_sub b
  exact aux_tvs (g_global_bilin_2 f b) h1 h2 h3

theorem g_bilin_symm_1 (i b : B)
  (α β : TangentSpace IB b) :
    (g_bilin_1 (IB := IB) i b).snd.toFun α β =
    (g_bilin_1 (IB := IB) i b).snd.toFun β α := by
  calc
    (g_bilin_1 i b).snd.toFun α β = (g_bilin_2 i b).toFun α β := g_bilin_eq i b α β
    _ = (g_bilin_2 i b).toFun β α := g_bilin_symm_2 i b α β
    _ = (g_bilin_1 i b).snd.toFun β α := (g_bilin_eq i b β α).symm

lemma g_bilin_1_smooth_on_chart (i : B) :
  ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (g_bilin_1 (EB := EB) (IB := IB) i)
    (extChartAt IB i).source := by
  unfold g_bilin_1
  simp
  intro b hb
  have h0 : ((chartAt HB i).source ∩ ((chartAt HB i).source ∩ Set.univ)) ×ˢ Set.univ =
            (chartAt HB i).source ×ˢ (Set.univ : Set (EB →L[ℝ] EB →L[ℝ] ℝ)) := by
    simp
  rw [h0]
  have h1 :
    (b, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) ∈
    (chartAt HB i).source ×ˢ Set.univ := Set.mk_mem_prod hb trivial

  classical

  let ψ := trivializationAt (EB →L[ℝ] EB →L[ℝ] ℝ)
    (fun x ↦ TangentSpace IB x →L[ℝ] TangentSpace IB x →L[ℝ] ℝ) i

  have heq : ∀ x ∈ (chartAt HB i).source,
    (if (x, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) ∈ (chartAt HB i).source ×ˢ Set.univ
      then
        ψ.invFun (x, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ)))
      else
        ⟨x, 0⟩)
    =
    ψ.invFun (x, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) := by
    intro x hx
    have : (x, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) ∈
      (chartAt HB i).source ×ˢ Set.univ := Set.mk_mem_prod hx trivial
    exact if_pos this

  have hrev :
    ∀ x ∈ (chartAt HB i).source,
      ψ.invFun (x, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) =
        (if (x, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) ∈
            (chartAt HB i).source ×ˢ Set.univ
        then
           ψ.invFun (x, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ)))
        else
           ⟨x, 0⟩) :=
    by
      intro x hx
      exact (heq x hx).symm

  have h2 : ContMDiffOn (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    ψ.toPartialEquiv.symm ψ.target := Trivialization.contMDiffOn_symm _

  let innerAtP : B → EB →L[ℝ] EB →L[ℝ] ℝ := fun x ↦ innerSL ℝ

  have h4 : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun c => (c, innerAtP c)) (extChartAt IB i).source := by
      apply ContMDiffOn.prodMk
      · exact contMDiffOn_id
      · exact contMDiffOn_const

  have hmem : ∀ c ∈ (extChartAt IB i).source, (c, innerAtP c) ∈ ψ.target := by
    intro c hc
    rw [ψ.target_eq, baseSet_eq_extChartAt_source i]
    exact ⟨hc, trivial⟩

  have h5 : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (ψ.toPartialEquiv.symm ∘ fun c ↦ (c, innerAtP c)) (extChartAt IB i).source:= h2.comp h4 hmem

  have h6 : (extChartAt IB i).source = (chartAt HB i).source := extChartAt_source IB i
  rw [<-h6]

  have h7 : b ∈ (chartAt HB i).source := hb
  have : b ∈ (extChartAt IB i).source := by
    rw [<-h6] at h7
    exact h7

  refine (ContMDiffOn.congr h5 ?_) b this
  intro y hy
  simp only [Function.comp_apply]
  rw [h6] at hy
  convert heq y hy using 1
  · congr 1
    have : (chartAt HB i).source = (extChartAt IB i).source := h6.symm
    have : ((y, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) ∈ (extChartAt IB i).source ×ˢ Set.univ)
            =
           ((y, ((innerSL ℝ) : (EB →L[ℝ] EB →L[ℝ] ℝ))) ∈ (chartAt HB i).source ×ˢ Set.univ) := by
      exact congrFun (congrArg Membership.mem (congrFun (congrArg SProd.sprod h6) Set.univ))
            (y, innerSL ℝ)
    exact this

noncomputable
def g_global_bilin_1 (f : SmoothPartitionOfUnity B IB B) (p : B) :
    W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _) p :=
      ∑ᶠ (j : B), (f j) p • (g_bilin_1 (IB := IB) j p).snd

lemma g_global_bilin_1_smooth (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ContMDiff IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞
    (fun x ↦ TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) x (g_global_bilin_1 f x)) := by

  have h1 := contMDiff_totalSpace_weighted_sum_of_local_sections
    (E := EB) (I := IB) (M := B)
    (V := fun b => TangentSpace IB b →L[ℝ] (TangentSpace IB b →L[ℝ] Trivial B ℝ b))
    (F_fiber := EB →L[ℝ] (EB →L[ℝ] ℝ))
    (n := (⊤ : ℕ∞)) (ι := B)
    (ρ := f)
    (s_loc := fun i b => (g_bilin_1 (IB := IB) i b).snd)
    (U := fun x ↦ (extChartAt IB x).source)
    (hU_isOpen := by intro i; exact isOpen_extChartAt_source i)
    (hρ_subord := h_sub)
    (h_smooth_s_loc := by
      intro i
      apply ContMDiffOn.congr
      · have : ContMDiffOn IB (IB.prod 𝓘(ℝ, EB →L[ℝ] EB →L[ℝ] ℝ)) ∞  (g_bilin_1 (IB := IB) i)
                           ((fun x ↦ (extChartAt IB x).source) i) :=
          g_bilin_1_smooth_on_chart (IB := IB) i
        exact this
      · have : ∀ y ∈ (fun x ↦ (extChartAt IB x).source) i,
          TotalSpace.mk' (EB →L[ℝ] EB →L[ℝ] ℝ) y ((fun i b ↦ (g_bilin_1 (IB := IB) i b).snd) i y) =
          g_bilin_1 (IB := IB) i y := by
          unfold g_bilin_1
          intro y hy
          simp
          split_ifs with hh1
          · rw [if_pos hh1]
            exact rfl
          · rw [if_neg hh1]
        exact this)
  exact h1

noncomputable
def g_global_smooth_section_1
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
    ContMDiffSection (I := IB) (F := (EB →L[ℝ] EB →L[ℝ] ℝ)) (n := ∞)
      (V := (W (@TangentSpace ℝ _ _ _ _ _ _ IB B _ _))) :=
  { toFun := g_global_bilin_1 f
    contMDiff_toFun := g_global_bilin_1_smooth f h_sub}

lemma g_global_bilin_eq (f : SmoothPartitionOfUnity B IB B) (p : B) :
    g_global_bilin_1 f p = g_global_bilin_2 f p := by
  unfold g_global_bilin_1 g_global_bilin_2
  congr 1
  ext j
  congr 2
  ext α β
  have h1 : (((g_bilin_1 j p).snd).toFun α) β =
            (((g_bilin_2 j p)).toFun α) β := g_bilin_eq (IB := IB) j p α β
  simp
  exact congrArg (HMul.hMul ((f j) p)) h1

lemma riemannian_metric_symm_1 (f : SmoothPartitionOfUnity B IB B)
   (b : B) (v w : TangentSpace IB b) :
  ((g_global_bilin_1 f b).toFun v).toFun w = ((g_global_bilin_1 f b).toFun w).toFun v := by

  have hz : ((g_global_bilin_2 f b).toFun v).toFun w = ((g_global_bilin_2 f b).toFun w).toFun v :=
    riemannian_metric_symm f b v w

  have hy : g_global_bilin_1 f b = g_global_bilin_2 f b :=
    g_global_bilin_eq f b

  rw [<-hy] at hz
  exact hz

lemma riemannian_metric_pos_def_1 (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source))
  (b : B) (v : TangentSpace IB b) :
  v ≠ 0 → 0 < ((g_global_bilin_1 f b).toFun v).toFun v := by

  have hz : v ≠ 0 → 0 < ((g_global_bilin_2 f b).toFun v).toFun v :=
    riemannian_metric_pos_def f h_sub b v

  have hy : g_global_bilin_1 f b = g_global_bilin_2 f b :=
    g_global_bilin_eq f b

  rw [<-hy] at hz
  exact hz

lemma riemannian_unit_ball_bounded_1 (f : SmoothPartitionOfUnity B IB B)
  (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
  ∀ (b : B), Bornology.IsVonNBounded ℝ
    {v  : TangentSpace IB b | ((g_global_bilin_1 f b).toFun v).toFun v < 1} := by
    have hz :  ∀ (b : B),
      Bornology.IsVonNBounded ℝ {v | ((((g_global_bilin_2 f b)).toFun v)).toFun v < 1} :=
        riemannian_unit_ball_bounded f h_sub
    intro b
    have hy : g_global_bilin_1 f b = g_global_bilin_2 f b :=
      g_global_bilin_eq f b
    rw [hy]
    exact hz b

noncomputable
def riemannian_metric_exists_1
    (f : SmoothPartitionOfUnity B IB B)
    (h_sub : f.IsSubordinate (fun x ↦ (extChartAt IB x).source)) :
    ContMDiffRiemannianMetric (IB := IB) (n := ∞) (F := EB)
     (E := @TangentSpace ℝ _ _ _ _ _ _ IB B _ _) :=
  { inner := g_global_bilin_1 f
    symm := by
      exact riemannian_metric_symm_1 f
    pos := riemannian_metric_pos_def_1 f h_sub
    isVonNBounded := riemannian_unit_ball_bounded_1 f h_sub
    contMDiff := (g_global_bilin_1_smooth f h_sub)
     }
