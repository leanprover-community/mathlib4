/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.Algebra.Algebra.Field
import Mathlib.Algebra.BigOperators.Field
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Liouville's theorem

A proof of Liouville's theorem. Follows
[Rosenlicht, M. Integration in finite terms][Rosenlicht_1972].

## Liouville field extension

This file defines Liouville field extensions, which are differential field extensions which satisfy
a slight generalization of Liouville's theorem. Note that this definition doesn't appear in the
literature, and we introduce it as part of the formalization of Liouville's theorem.

## Main declarations
- `IsLiouville`: A field extension being Liouville
- `isLiouville_of_finiteDimensional`: all finite dimensional field extensions
  (of a field with characteristic 0) are Liouville.

-/

open Differential algebraMap IntermediateField Finset Polynomial

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]
variable [Algebra F K] [DifferentialAlgebra F K]

/--
We say that a differential field extension `K / F` is Liouville if, whenever an element `a ∈ F` can
be written as `a = v + ∑ cᵢ * logDeriv uᵢ` for `v, cᵢ, uᵢ ∈ K` and `cᵢ` constant, it can also be
written in that way with `v, cᵢ, uᵢ ∈ F`.
-/
class IsLiouville : Prop where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ → F) (_ : ∀ x, (c₀ x)′ = 0)
      (u₀ : ι₀ → F) (v₀ : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀′

instance IsLiouville.rfl : IsLiouville F F where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → F) (v : F) (h : a = ∑ x, c x * logDeriv (u x) + v′) :=
    ⟨ι, _, c, hc, u, v, h⟩

lemma IsLiouville.trans {A : Type*} [Field A] [Algebra K A] [Algebra F A]
    [Differential A] [IsScalarTower F K A] [Differential.ContainConstants F K]
    (inst1 : IsLiouville F K) (inst2 : IsLiouville K A) : IsLiouville F A where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → A) (v : A) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    obtain ⟨ι₀, _, c₀, hc₀, u₀, v₀, h₀⟩ := inst2.isLiouville (a : K) ι
        ((↑) ∘ c)
        (fun _ ↦ by simp only [Function.comp_apply, ← coe_deriv, lift_map_eq_zero_iff, hc])
        ((↑) ∘ u) v (by simpa only [Function.comp_apply, ← IsScalarTower.algebraMap_apply])
    have hc (x : ι₀) := mem_range_of_deriv_eq_zero F (hc₀ x)
    choose c₀ hc using hc
    apply inst1.isLiouville a ι₀ c₀ _ u₀ v₀
    · rw [h₀]
      simp [hc]
    · intro
      apply_fun ((↑) : F → K)
      · simp only [Function.comp_apply, coe_deriv, hc, algebraMap.coe_zero]
        apply hc₀
      · apply FaithfulSMul.algebraMap_injective

section Algebraic
/-
The case of Liouville's theorem for algebraic extensions.
-/

variable {F K} [CharZero F]

/--
If `K` is a Liouville extension of `F` and `B` is a finite dimensional intermediate
field `K / B / F`, then it's also a Liouville extension of `F`.
-/
instance (B : IntermediateField F K)
    [FiniteDimensional F B] [inst : IsLiouville F K] :
    IsLiouville F B where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → B) (v : B) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.isLiouville a ι c hc (B.val ∘ u) (B.val v)
    dsimp only [coe_val, Function.comp_apply]
    conv =>
      rhs
      congr
      · rhs
        intro x
        rhs
        apply logDeriv_algebraMap (u x)
      · apply (deriv_algebraMap v)
    simp_rw [IsScalarTower.algebraMap_apply F B K]
    norm_cast


/--
Transfer an `IsLiouville` instance using an equivalence `K ≃ₐ[F] K'`.
Requires an algebraic `K'` to show that the equivalence commutes with the derivative.
-/
lemma IsLiouville.equiv {K' : Type*} [Field K'] [Differential K'] [Algebra F K']
    [DifferentialAlgebra F K'] [Algebra.IsAlgebraic F K']
    [inst : IsLiouville F K] (e : K ≃ₐ[F] K') : IsLiouville F K' where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K') (v : K') (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    apply inst.isLiouville a ι c hc (e.symm ∘ u) (e.symm v)
    apply_fun e.symm at h
    simpa [AlgEquiv.commutes, map_add, map_sum, map_mul, logDeriv, algEquiv_deriv'] using h

/--
A finite dimensional Galois extension of `F` is a Liouville extension.
This is private because it's generalized by all finite dimensional extensions being Liouville.
-/
private local instance isLiouville_of_finiteDimensional_galois [FiniteDimensional F K]
    [IsGalois F K] : IsLiouville F K where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
      (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) := by
    haveI : CharZero K := charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective F K)
    -- We sum `e x` over all isomorphisms `e : K ≃ₐ[F] K`.
    -- Because this is a Galois extension each of the relevant values will be in `F`.
    -- We need to divide by `Fintype.card (K ≃ₐ[F] K)` to get the original answer.
    let c₀ (i : ι) := (c i) / (Fintype.card (K ≃ₐ[F] K))
    -- logDeriv turns sums to products, so the new `u` will be the product of the old `u` over all
    -- isomorphisms
    let u₁ (i : ι) := ∏ x : (K ≃ₐ[F] K), x (u i)
    -- Each of the values of u₁ are fixed by all isomorphisms.
    have : ∀ i, u₁ i ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro i ⟨e, _⟩
      change e (u₁ i) = u₁ i
      simp only [u₁, map_prod]
      apply Fintype.prod_equiv (Equiv.mulLeft e)
      simp
    have ffb : fixedField ⊤ = ⊥ := (IsGalois.tfae.out 0 1).mp (inferInstanceAs (IsGalois F K))
    simp_rw [ffb, IntermediateField.mem_bot, Set.mem_range] at this
    -- Therefore they are all in `F`. We use `choose` to get their values in `F`.
    choose u₀ hu₀ using this
    -- We do almost the same thing for `v₁`, just with sum instead of product.
    let v₁ := (∑ x : (K ≃ₐ[F] K), x v) / (Fintype.card ((K ≃ₐ[F] K)))
    have : v₁ ∈ fixedField (⊤ : Subgroup (K ≃ₐ[F] K)) := by
      rintro ⟨e, _⟩
      change e v₁ = v₁
      simp only [v₁, map_div₀, map_sum, map_natCast]
      congr 1
      apply Fintype.sum_equiv (Equiv.mulLeft e)
      simp
    rw [ffb, IntermediateField.mem_bot] at this
    obtain ⟨v₀, hv₀⟩ := this
    exists ι, inferInstance, c₀, ?_, u₀, v₀
    · -- We need to prove that all `c₀` are constants.
      -- This is true because they are the division of a constant by
      -- a natural number (which is also constant)
      intro x
      simp [c₀, Derivation.leibniz_div, hc]
    · -- Proving that this works is mostly straightforward algebraic manipulation,
      apply_fun (algebraMap F K)
      case inj =>
        exact FaithfulSMul.algebraMap_injective F K
      simp only [map_add, map_sum, map_mul, ← logDeriv_algebraMap, hu₀, ← deriv_algebraMap, hv₀]
      unfold u₁ v₁ c₀
      clear c₀ u₁ u₀ hu₀ v₁ v₀ hv₀
      push_cast
      rw [Derivation.leibniz_div_const, smul_eq_mul, inv_mul_eq_div]
      case h => simp
      simp only [map_sum, div_mul_eq_mul_div]
      rw [← sum_div, ← add_div]
      field_simp
      -- Here we rewrite logDeriv (∏ x : K ≃ₐ[F] K, x (u i)) to ∑ x : K ≃ₐ[F] K, logDeriv (x (u i))
      conv =>
        enter [2, 1, 2, i, 2]
        equals ∑ x : K ≃ₐ[F] K, logDeriv (x (u i)) =>
          by_cases h : u i = 0 <;>
          simp [logDeriv_prod_of_eq_zero, logDeriv_prod, h]
      simp_rw [mul_sum]
      rw [sum_comm, ← sum_add_distrib]
      trans ∑ _ : (K ≃ₐ[F] K), a
      · simp [mul_comm]
      · rcongr e
        apply_fun e at h
        simp only [AlgEquiv.commutes, map_add, map_sum, map_mul] at h
        convert h using 2
        · rcongr x
          simp [logDeriv, algEquiv_deriv']
        · rw [algEquiv_deriv']

/--
We lift `isLiouville_of_finiteDimensional_galois` to non-Galois field extensions by using it for the
normal closure then obtaining it for `F`.
-/
instance isLiouville_of_finiteDimensional [FiniteDimensional F K] :
    IsLiouville F K :=
  let map := IsAlgClosed.lift (M := AlgebraicClosure F) (R := F) (S := K)
  let K' := map.fieldRange
  have : FiniteDimensional F K' :=
    LinearMap.finiteDimensional_range map.toLinearMap
  let K'' := normalClosure F K' (AlgebraicClosure F)
  let B : IntermediateField F K'' := IntermediateField.restrict
    (F := K') (IntermediateField.le_normalClosure ..)
  have kequiv : K ≃ₐ[F] ↥B := (show K ≃ₐ[F] K' from AlgEquiv.ofInjectiveField map).trans
    (IntermediateField.restrict_algEquiv _)
  IsLiouville.equiv kequiv.symm

end Algebraic
