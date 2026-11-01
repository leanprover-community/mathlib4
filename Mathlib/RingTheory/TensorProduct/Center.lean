/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
This file proves base change theorems for the center of algebras comparing the base change of the
center and the center of the base change.
-/

@[expose] public section

open TensorProduct

namespace Subalgebra

variable {S R A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Algebra R S] [Algebra R A]

variable (R S A) in
/-- The natural algebra morphism from the base change of the center to the center of the base
change. -/
@[simps! -isSimp]
def center.baseChange :
    S ⊗[R] center R A →ₐ[S] center S (S ⊗[R] A) := by
  let f := Algebra.TensorProduct.map (AlgHom.id S S) (center R A).val
  have hf (x : S ⊗[R] center R A) : f x ∈ Set.center (S ⊗[R] A) := by
    refine x.inductionOn (fun s z => Semigroup.mem_center_iff.mpr fun g => ?_) (fun x y hx hy => ?_)
    · refine g.inductionOn (fun s' z' => ?_) (fun x y hx hy => ?_)
      · simp [f, mul_comm s, Semigroup.mem_center_iff.mp z.prop]
      rw [add_mul, mul_add, hx, hy]
    simp [Set.add_mem_center hx hy]
  exact f.codRestrict _ hf

@[simp]
lemma center.coe_baseChange_tmul (s : S) (z : center R A) :
    (center.baseChange S R A (s ⊗ₜ[R] z)).val = s ⊗ₜ[R] z.val := rfl

variable {R S A : Type*} [CommRing R] [CommRing S] [Ring A] [Algebra R S] [Algebra R A]

theorem center.baseChange_injective [Module.Flat R S] :
    Function.Injective (center.baseChange S R A) :=
  fun _ _ h => Module.Flat.lTensor_preserves_injective_linearMap (center R A).val.toLinearMap
    Subtype.val_injective (congrArg Subtype.val h)

theorem center.baseChange_surjective [IsNoetherianRing R] [Module.Flat R S] [Module.Flat R A] :
    Function.Surjective (center.baseChange S R A) := by
  -- The idea is to use Noetherianness to reduce to the case where `S` is free, and then pass the
  -- commutativity to each coordinate over that basis to produce central elememnts of `A`.
  rintro ⟨x, hx⟩
  obtain ⟨N, _, hN⟩ := exists_finite_submodule_left_of_setFinite {x} (Set.finite_singleton x)
  obtain ⟨u, rfl⟩ := hN rfl
  have := Module.finitePresentation_of_finite R N
  obtain ⟨n, h, g, hg⟩ := Module.Flat.exists_factorization_of_finitePresentation N.subtype
  -- `z : A` is central iff `δ a z = a * z - z * a` vanishes for all `a`.
  let δ (a : A) : A →ₗ[R] A := LinearMap.mulLeft R a - LinearMap.mulRight R a
  -- We know `δ a u = 0` by the flatness of `A`. It follows that `δ a (h.rTensor A u) = 0`.
  have hδ (a : A) : (δ a).lTensor _ (h.rTensor A u) = 0 := by
    suffices hu : (δ a).lTensor N u = 0 by
      simpa [← LinearMap.comp_apply] using congrArg (h.rTensor A) hu
    suffices hS : (δ a).lTensor S (N.subtype.rTensor A u) = 0 by
      apply Module.Flat.rTensor_preserves_injective_linearMap (M := A) _ N.injective_subtype
      simpa [← LinearMap.comp_apply] using hS
    have : (δ a).lTensor S = .mulLeft R (1 ⊗ₜ a) - .mulRight R ((1 : S) ⊗ₜ[R] a) := by ext; simp [δ]
    simpa [this] using sub_eq_zero.mpr (mem_center_iff.mp hx (1 ⊗ₜ a))
  obtain ⟨c, hc⟩ := eq_repr_basis_left Finsupp.basisSingleOne (h.rTensor A u)
  -- Now we have `0 = δ a (h.rTensor A u) = ∑ i, e i ⊗ₜ δ a (a i)`. Freeness forces `δ a (a i) = 0`.
  have hc' (i : Fin n) : c i ∈ center R A := mem_center_iff.mpr fun a ↦ by
    have := hδ a
    simp only [← hc, map_finsuppSum, LinearMap.lTensor_tmul] at this
    have := congr(finsuppScalarLeft R A (Fin n) $this i)
    simp only [Finsupp.coe_basisSingleOne, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, map_finsuppSum, Finsupp.sum_apply,
      finsuppScalarLeft_apply_tmul_apply, Finsupp.single_apply, ite_smul, one_smul, zero_smul,
      Finsupp.sum_ite_eq', Finsupp.mem_support_iff, ne_eq, map_zero, Finsupp.coe_zero,
      Pi.zero_apply, ite_eq_right_iff, sub_eq_zero, δ] at this
    by_cases h : c i = 0 <;> simp [this, h]
  use ∑ i ∈ c.support, g (.single i 1) ⊗ₜ ⟨c i, hc' i⟩
  simp [Subtype.ext_iff, hg, LinearMap.rTensor_comp_apply, ← hc, Finsupp.sum]

end Subalgebra
