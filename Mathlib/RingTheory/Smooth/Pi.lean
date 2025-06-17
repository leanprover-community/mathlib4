/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Smooth.Basic

/-!

# Formal-smoothness of finite products of rings

## Main result

- `Algebra.FormallySmooth.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-smooth
  if and only if each `A i` is `R`-formally-smooth.

-/

universe u v

namespace Algebra.FormallySmooth

variable {R : Type (max u v)} {I : Type u} (A : I → Type (max u v))
variable [CommRing R] [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]

theorem of_pi [FormallySmooth R (Π i, A i)] (i) :
    FormallySmooth R (A i) := by
  classical
  fapply FormallySmooth.of_split (Pi.evalAlgHom R A i)
  · apply AlgHom.ofLinearMap
      ((Ideal.Quotient.mkₐ R _).toLinearMap.comp (LinearMap.single _ _ i))
    · change Ideal.Quotient.mk _ (Pi.single i 1) = 1
      rw [← (Ideal.Quotient.mk _).map_one, ← sub_eq_zero, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      have : Pi.single i 1 - 1 ∈ RingHom.ker (Pi.evalAlgHom R A i).toRingHom := by
        simp [RingHom.mem_ker]
      convert neg_mem (Ideal.pow_mem_pow this 2) using 1
      simp [pow_two, sub_mul, mul_sub, ← Pi.single_mul]
    · intro x y
      change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ * Ideal.Quotient.mk _ _
      simp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_single, Pi.single_mul, map_mul]
  · ext x
    change (Pi.single i x) i = x
    simp

theorem pi_iff [Finite I] :
    FormallySmooth R (Π i, A i) ↔ ∀ i, FormallySmooth R (A i) := by
  classical
  cases nonempty_fintype I
  constructor
  · exact fun _ ↦ of_pi A
  · intro H
    constructor
    intros B _ _ J hJ g
    have hJ' (x) (hx : x ∈ RingHom.ker (Ideal.Quotient.mk J)) : IsNilpotent x := by
      refine ⟨2, show x ^ 2 ∈ (⊥ : Ideal B) from ?_⟩
      rw [← hJ]
      exact Ideal.pow_mem_pow (by simpa using hx) 2
    obtain ⟨e, he, he'⟩ := ((CompleteOrthogonalIdempotents.single A).map
      g.toRingHom).lift_of_isNilpotent_ker (Ideal.Quotient.mk J) hJ'
        fun _ ↦ Ideal.Quotient.mk_surjective _
    replace he' : ∀ i, Ideal.Quotient.mk J (e i) = g (Pi.single i 1) := congr_fun he'
    let iso : B ≃ₐ[R] ∀ i, B ⧸ Ideal.span {1 - e i} :=
      { __ := Pi.algHom _ _ fun i ↦ Ideal.Quotient.mkₐ R _
        __ := Equiv.ofBijective _ he.bijective_pi }
    let J' := fun i ↦ J.map (Ideal.Quotient.mk (Ideal.span {1 - e i}))
    let ι : ∀ i, (B ⧸ J →ₐ[R] (B ⧸ _) ⧸ J' i) := fun i ↦ Ideal.quotientMapₐ _
      (IsScalarTower.toAlgHom R B _) Ideal.le_comap_map
    have hι : ∀ i x, ι i x = 0 → (e i) * x = 0 := by
      intros i x hix
      have : x ∈ (Ideal.span {1 - e i}).map (Ideal.Quotient.mk J) := by
        rw [← Ideal.ker_quotientMap_mk]; exact hix
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at this
      obtain ⟨c, rfl⟩ := this
      rw [← mul_assoc, ← map_mul, mul_sub, mul_one, (he.idem i).eq, sub_self, map_zero, zero_mul]
    have : ∀ i : I, ∃ a : A i →ₐ[R] B ⧸ Ideal.span {1 - e i}, ∀ x,
        Ideal.Quotient.mk (J' i) (a x) = ι i (g (Pi.single i x)) := by
      intro i
      let g' : A i →ₐ[R] (B ⧸ _) ⧸ (J' i) := by
        apply AlgHom.ofLinearMap (((ι i).comp g).toLinearMap ∘ₗ LinearMap.single _ _ i)
        · suffices Ideal.Quotient.mk (Ideal.span {1 - e i}) (e i) = 1 by simp [ι, ← he', this]
          rw [← (Ideal.Quotient.mk _).map_one, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
            Ideal.mem_span_singleton]
        · intros x y; simp [Pi.single_mul]
      obtain ⟨a, ha⟩ := FormallySmooth.comp_surjective (I := J' i)
        (by rw [← Ideal.map_pow, hJ, Ideal.map_bot]) g'
      exact ⟨a, AlgHom.congr_fun ha⟩
    choose a ha using this
    use iso.symm.toAlgHom.comp (Pi.algHom _ _ fun i ↦ (a i).comp (Pi.evalAlgHom R A i))
    ext x; rw [← AlgHom.toLinearMap_apply, ← AlgHom.toLinearMap_apply]; congr 1
    ext i x
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_toLinearMap, AlgEquiv.toAlgHom_toLinearMap,
      LinearMap.coe_comp, LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply,
      AlgEquiv.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (a i x)
    have hy' : Ideal.Quotient.mk (Ideal.span {1 - e i}) (y * e i) = a i x := by
      have : Ideal.Quotient.mk (Ideal.span {1 - e i}) (e i) = 1 := by
        rw [← (Ideal.Quotient.mk _).map_one, eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
          Ideal.mem_span_singleton]
      rw [map_mul, this, hy, mul_one]
    trans Ideal.Quotient.mk J (y * e i)
    · congr 1; apply iso.injective; ext j
      suffices a j (Pi.single i x j) = Ideal.Quotient.mk _ (y * e i) by simpa using this
      by_cases hij : i = j
      · subst hij
        rw [Pi.single_eq_same, hy']
      · have : Ideal.Quotient.mk (Ideal.span {1 - e j}) (e i) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          refine ⟨e i, by simp [he.ortho (Ne.symm hij), sub_mul]⟩
        rw [Pi.single_eq_of_ne (Ne.symm hij), map_zero, map_mul, this, mul_zero]
    · have : ι i (Ideal.Quotient.mk J (y * e i)) = ι i (g (Pi.single i x)) := by
        rw [← ha, ← hy']
        simp only [Ideal.quotient_map_mkₐ, IsScalarTower.coe_toAlgHom',
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mkₐ_eq_mk, ι]
      rw [← sub_eq_zero, ← map_sub] at this
      replace this := hι _ _ this
      rwa [mul_sub, ← map_mul, mul_comm, mul_assoc, (he.idem i).eq, he', ← map_mul, ← Pi.single_mul,
        one_mul, sub_eq_zero] at this

instance [Finite I] [∀ i, FormallySmooth R (A i)] : FormallySmooth R (Π i, A i) :=
  (pi_iff _).mpr ‹_›

end Algebra.FormallySmooth
