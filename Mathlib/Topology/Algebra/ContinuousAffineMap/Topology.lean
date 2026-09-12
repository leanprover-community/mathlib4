/-
Copyright (c) 2026 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Topology.Algebra.ContinuousAffineEquiv
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Topology on the space of continuous affine maps

This file defines a topology on the space of continuous affine maps between topological affine
spaces. This is the coarsest topology satisfying the following two properties:
* For every point `p`, the evaluation map `fun f ↦ f p` is continuous.
* The map `fun f ↦ f.contLinear` is continuous.
-/

@[expose] public section

namespace ContinuousAffineMap

variable {R V W P Q : Type*} [NormedField R]
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [AddTorsor V P] [TopologicalSpace P]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [AddTorsor W Q] [TopologicalSpace Q]

section Affine

variable [IsTopologicalAddTorsor P] [IsTopologicalAddTorsor Q]

instance : TopologicalSpace (P →ᴬ[R] Q) :=
  haveI := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
  .induced (fun f => (⇑f, f.contLinear)) inferInstance

@[fun_prop]
theorem continuous_contLinear [IsTopologicalAddGroup W] :
    Continuous (contLinear : (P →ᴬ[R] Q) → (V →L[R] W)) :=
  (continuous_induced_dom (f := fun f : P →ᴬ[R] Q => (⇑f, f.contLinear))).snd

instance : ContinuousEvalConst (P →ᴬ[R] Q) P Q where
  continuous_eval_const p :=
    have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
    (continuous_apply p).comp
      (continuous_induced_dom (f := fun f : P →ᴬ[R] Q => (⇑f, f.contLinear))).fst

variable {α : Type*} [TopologicalSpace α]

theorem continuous_rng [IsTopologicalAddGroup W] {f : α → P →ᴬ[R] Q}
    (h₁ : ∀ p, Continuous (fun x => f x p)) (h₂ : Continuous (fun x => (f x).contLinear)) :
    Continuous f :=
  continuous_induced_rng.mpr <| (continuous_pi h₁).prodMk h₂

theorem continuous_rng_iff [IsTopologicalAddGroup W] (f : α → P →ᴬ[R] Q) :
    Continuous f ↔ (∀ p, Continuous (fun x => f x p)) ∧ Continuous (fun x => (f x).contLinear) :=
  ⟨fun h => ⟨by fun_prop, by fun_prop⟩, fun ⟨h₁, h₂⟩ => continuous_rng h₁ h₂⟩

theorem continuous_rng_of_exists [IsTopologicalAddGroup W] [ContinuousSMul R V] {f : α → P →ᴬ[R] Q}
    (h₁ : ∃ p, Continuous (fun x => f x p)) (h₂ : Continuous (fun x => (f x).contLinear)) :
    Continuous f := by
  refine continuous_rng (fun q => ?_) h₂
  obtain ⟨p, hp⟩ := h₁
  simp_rw +singlePass [← vsub_vadd q p, ContinuousAffineMap.map_vadd]
  fun_prop

@[fun_prop]
protected theorem continuous_const : Continuous (const R P (Q := Q)) :=
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
  continuous_rng (by simp_rw [coe_const]; fun_prop) (by simp_rw [const_contLinear]; fun_prop)

instance [IsTopologicalAddGroup W] : IsTopologicalAddTorsor (P →ᴬ[R] Q) where
  continuous_vadd :=
    continuous_rng (by simp_rw [vadd_apply]; fun_prop) (by simp_rw [vadd_contLinear]; fun_prop)
  continuous_vsub :=
    continuous_rng (by simp_rw [vsub_apply]; fun_prop) (by simp_rw [vsub_contLinear]; fun_prop)

instance [T0Space W] : T0Space (P →ᴬ[R] Q) :=
  t0Space_of_injective_of_continuous DFunLike.coe_injective continuous_coeFun

instance : RegularSpace (P →ᴬ[R] Q) :=
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup W Q
  inferInstance

end Affine

section LinearCodomain

variable [IsTopologicalAddTorsor P] [IsTopologicalAddGroup W]

instance : IsTopologicalAddGroup (P →ᴬ[R] W) :=
  IsTopologicalAddTorsor.to_isTopologicalAddGroup (P →ᴬ[R] W) (P →ᴬ[R] W)

instance {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
    [ContinuousConstSMul S W] : ContinuousConstSMul S (P →ᴬ[R] W) where
  continuous_const_smul _ :=
    continuous_rng (by simp_rw [coe_smul]; fun_prop) (by simp_rw [smul_contLinear]; fun_prop)

instance [ContinuousSMul R W] : ContinuousSMul R (P →ᴬ[R] W) where
  continuous_smul :=
    continuous_rng (by simp_rw [coe_smul]; fun_prop) (by simp_rw [smul_contLinear]; fun_prop)

end LinearCodomain

section Linear

variable [IsTopologicalAddGroup V] [ContinuousSMul R V] [IsTopologicalAddGroup W]

@[fun_prop]
theorem _root_.ContinuousLinearMap.continuous_toContinuousAffineMap :
    Continuous (ContinuousLinearMap.toContinuousAffineMap : (V →L[R] W) → V →ᴬ[R] W) :=
  continuous_rng
    (by simp_rw [ContinuousLinearMap.coe_toContinuousAffineMap]; fun_prop)
    (by simp_rw [ContinuousLinearMap.toContinuousAffineMap_contLinear]; fun_prop)

end Linear

variable [IsTopologicalAddGroup V] [ContinuousSMul R V]

section LinearDomain

variable (R V Q) [IsTopologicalAddGroup W] [IsTopologicalAddTorsor Q]

/-- The space of continuous affine maps from a topological vector space to a topological affine
space is homeomorphic to the product of the codomain with the space of continuous linear maps, by
taking the value of the affine map at `(0 : V)` and the linear part. -/
def decompHomeomorph : (V →ᴬ[R] Q) ≃ₜ (Q × (V →L[R] W)) where
  __ := decompEquiv R V Q
  continuous_toFun := (continuous_eval_const 0).prodMk continuous_contLinear
  continuous_invFun := continuous_rng
    (by simp_rw [Equiv.invFun_as_coe, decompEquiv_symm_apply]; fun_prop)
    (by simp_rw [Equiv.invFun_as_coe, decompEquiv_symm_contLinear]; fun_prop)

@[simp]
theorem fst_decompHomeomorph (f : V →ᴬ[R] Q) : (decompHomeomorph R V Q f).1 = f 0 :=
  rfl

@[simp]
theorem snd_decompHomeomorph (f : V →ᴬ[R] Q) : (decompHomeomorph R V Q f).2 = f.contLinear :=
  rfl

@[simp]
theorem decompHomeomorph_symm_apply (p : Q × (V →L[R] W)) (x : V) :
    (decompHomeomorph R V Q).symm p x = p.2 x +ᵥ p.1 :=
  rfl

@[simp]
theorem decompHomeomorph_symm_contLinear (p : Q × (V →L[R] W)) :
    ((decompHomeomorph R V Q).symm p).contLinear = p.2 :=
  decompEquiv_symm_contLinear ..

end LinearDomain

section Linear

variable (R V W) [IsTopologicalAddGroup W] [ContinuousConstSMul R W]

/-- The space of continuous affine maps between topological vector spaces is isomorphic (as a
topological vector space) to the product of the codomain with the space of continuous linear maps,
by taking the value of the affine map at `(0 : V)` and the linear part. -/
def decompContinuousLinearEquiv : (V →ᴬ[R] W) ≃L[R] (W × (V →L[R] W)) where
  __ := decompHomeomorph R V W
  __ := decompLinearEquiv R R V W

@[simp]
theorem fst_decompContinuousLinearEquiv (f : V →ᴬ[R] W) :
    (decompContinuousLinearEquiv R V W f).1 = f 0 :=
  rfl

@[simp]
theorem snd_decompContinuousLinearEquiv (f : V →ᴬ[R] W) :
    (decompContinuousLinearEquiv R V W f).2 = f.contLinear :=
  rfl

@[simp]
theorem decompContinuousLinearEquiv_symm_apply (p : W × (V →L[R] W)) (x : V) :
    (decompContinuousLinearEquiv R V W).symm p x = p.2 x +ᵥ p.1 :=
  rfl

@[simp]
theorem decompContinuousLinearEquiv_symm_contLinear (p : W × (V →L[R] W)) :
    ((decompContinuousLinearEquiv R V W).symm p).contLinear = p.2 :=
  decompEquiv_symm_contLinear ..

end Linear

section LinearDomain

variable (R V Q) [IsTopologicalAddGroup W] [ContinuousConstSMul R W] [IsTopologicalAddTorsor Q]

/-- The space of continuous affine maps from a topological vector space to a topological affine
space is isomorphic (as a topological affine space) to the product of the codomain with the space of
continuous linear maps, by taking the value of the affine map at `(0 : V)` and the linear part. -/
def decompContinuousAffineEquiv : (V →ᴬ[R] Q) ≃ᴬ[R] (Q × (V →L[R] W)) where
  __ := decompHomeomorph R V Q
  __ := decompAffineEquiv R R V Q

@[simp]
theorem fst_decompContinuousAffineEquiv (f : V →ᴬ[R] Q) :
    (decompContinuousAffineEquiv R V Q f).1 = f 0 :=
  rfl

@[simp]
theorem snd_decompContinuousAffineEquiv (f : V →ᴬ[R] Q) :
    (decompContinuousAffineEquiv R V Q f).2 = f.contLinear :=
  rfl

@[simp]
theorem decompContinuousAffineEquiv_symm_apply (p : Q × (V →L[R] W)) (x : V) :
    (decompContinuousAffineEquiv R V Q).symm p x = p.2 x +ᵥ p.1 :=
  rfl

@[simp]
theorem decompContinuousAffineEquiv_symm_contLinear (p : Q × (V →L[R] W)) :
    ((decompContinuousAffineEquiv R V Q).symm p).contLinear = p.2 :=
  decompHomeomorph_symm_contLinear ..

end LinearDomain

end ContinuousAffineMap
