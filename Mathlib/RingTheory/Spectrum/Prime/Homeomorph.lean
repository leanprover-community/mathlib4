/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Purely inseparable extensions are universal homeomorphisms

If `K` is a purely inseparable extension of `k`, the induced map `Spec K ⟶ Spec k` is a universal
homeomorphism, i.e. it stays a homeomorphism after arbitrary base change.

## Main results

- `PrimeSpectrum.isHomeomorph_comap`: if `f : R →+* S` is a ring map with locally nilpotent kernel
  such that for every `x : S`, there exists `n > 0` such that `x ^ n` is in the image of `f`,
  `Spec f` is a homeomorphism.
- `PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable`: `Spec K ⟶ Spec k` is a universal
  homeomorphism for a purely inseparable field extension `K` over `k`.
-/

open TensorProduct

variable (k K R S : Type*) [Field k] [Field K] [Algebra k K] [CommRing R] [Algebra k R] [CommRing S]

variable {R S} in
@[stacks 0BR8 "Homeomorphism part"]
lemma PrimeSpectrum.isHomeomorph_comap (f : R →+* S) (H : ∀ (x : S), ∃ n > 0, x ^ n ∈ f.range)
    (hker : RingHom.ker f ≤ nilradical R) : IsHomeomorph (PrimeSpectrum.comap f) := by
  have h1 : Function.Injective (PrimeSpectrum.comap f) := by
    intro q q' hqq'
    ext x
    by_contra! h
    wlog ha : x ∈ q.asIdeal ∧ x ∉ q'.asIdeal generalizing q q'
    · exact this hqq'.symm (Or.inl <| by tauto) (by tauto)
    obtain ⟨hxq, hxq'⟩ := ha
    obtain ⟨n, hn, y, hy⟩ := H x
    simp only [PrimeSpectrum.ext_iff, SetLike.ext'_iff, PrimeSpectrum.comap_asIdeal,
      Ideal.coe_comap] at hqq'
    have : x ^ n ∈ q'.asIdeal := by
      rw [← hy, ← SetLike.mem_coe, ← Set.mem_preimage, ← hqq', Set.mem_preimage, hy]
      exact Ideal.pow_mem_of_mem q.asIdeal hxq n hn
    exact hxq' (q'.2.mem_of_pow_mem n this)
  have hint : f.kerLift.IsIntegral := by
    intro x
    obtain ⟨n, hn, y, hy⟩ := H x
    use Polynomial.X ^ n - Polynomial.C (Ideal.Quotient.mk _ y)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, ← hy, Polynomial.eval₂_C,
      RingHom.kerLift_mk, sub_self, and_true]
    apply Polynomial.monic_X_pow_add
    simpa using lt_of_le_of_lt Polynomial.degree_C_le (by simpa using hn)
  have hbij : Function.Bijective (PrimeSpectrum.comap f) :=
    ⟨h1, (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical _ hker).2.comp <|
      hint.specComap_surjective f.kerLift_injective⟩
  refine ⟨(PrimeSpectrum.comap f).continuous, ?_, h1, hbij.2⟩
  · rw [PrimeSpectrum.isTopologicalBasis_basic_opens.isOpenMap_iff]
    rintro - ⟨s, rfl⟩
    obtain ⟨n, hn, r, hr⟩ := H s
    have : (PrimeSpectrum.comap f) '' (PrimeSpectrum.basicOpen s) = PrimeSpectrum.basicOpen r := by
      refine Set.preimage_injective.mpr hbij.2 ?_
      rw [Set.preimage_image_eq _ hbij.1, ← PrimeSpectrum.basicOpen_pow _ n hn, ← hr]
      rfl
    rw [this]
    exact PrimeSpectrum.isOpen_basicOpen

variable {R S} in
lemma PrimeSpectrum.isHomeomorph_comap_of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    IsHomeomorph (PrimeSpectrum.comap f) := by
  refine PrimeSpectrum.isHomeomorph_comap _
    (fun x ↦ ⟨1, Nat.one_pos, RingHom.range_eq_top_of_surjective f hf.2 ▸ trivial⟩) ?_
  convert bot_le
  exact (RingHom.injective_iff_ker_eq_bot _).mp hf.1

open Algebra

/-- Purely inseparable field extensions are universal homeomorphisms. -/
@[stacks 0BRA "Special case for purely inseparable field extensions"]
lemma PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable [IsPurelyInseparable k K] :
    IsHomeomorph (PrimeSpectrum.comap <| algebraMap R (R ⊗[k] K)) := by
  wlog hR : Nontrivial R
  · rw [not_nontrivial_iff_subsingleton] at hR
    exact PrimeSpectrum.isHomeomorph_comap_of_bijective
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
  let q := ringExpChar k
  refine PrimeSpectrum.isHomeomorph_comap _ (fun x ↦ ?_) ?_
  · obtain (hq|hq) := expChar_is_prime_or_one k q
    · obtain ⟨n, hn, hr⟩ : ∃ n > 0, x ^ q ^ n ∈ (algebraMap R (R ⊗[k] K)).range := by
        induction x with
        | zero => exact ⟨1, Nat.zero_lt_one, 0, by simp [zero_pow_eq, hq.ne_zero]⟩
        | add x y hx hy =>
          obtain ⟨n, hn, hx⟩ := hx
          obtain ⟨m, hm, hy⟩ := hy
          refine ⟨n + m, by simp [hn], ?_⟩
          have : ExpChar (R ⊗[k] K) q := by
            refine expChar_of_injective_ringHom
              (f := TensorProduct.includeRight.toRingHom.comp (algebraMap k K)) ?_ q
            exact (Algebra.TensorProduct.includeRight_injective (algebraMap k R).injective).comp
              (algebraMap k K).injective
          rw [add_pow_expChar_pow, pow_add]
          nth_rw 2 [mul_comm]
          rw [pow_mul, pow_mul]
          exact Subring.add_mem _ (Subring.pow_mem _ hx _) (Subring.pow_mem _ hy _)
        | tmul x y =>
          obtain ⟨n, a, ha⟩ := IsPurelyInseparable.pow_mem k q y
          refine ⟨n + 1, by simp, ?_⟩
          have : (x ^ q ^ (n + 1)) ⊗ₜ[k] (y ^ q ^ (n + 1)) =
              (x ^ q ^ (n + 1)) ⊗ₜ[k] (1 : K) * (1 : R) ⊗ₜ[k] (y ^ q ^ (n + 1)) := by
            rw [TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          rw [TensorProduct.tmul_pow, this]
          refine Subring.mul_mem _ ⟨x ^ q ^ (n + 1), rfl⟩ ⟨algebraMap k R (a ^ q), ?_⟩
          rw [pow_add, pow_mul, ← IsScalarTower.algebraMap_apply, TensorProduct.algebraMap_apply,
            TensorProduct.tmul_one_eq_one_tmul, map_pow, ha, pow_one]
      exact ⟨q ^ n, Nat.pow_pos hq.pos, hr⟩
    · have : ExpChar k 1 := ringExpChar.of_eq hq
      have : CharZero k := charZero_of_expChar_one' k
      exact ⟨1, Nat.one_pos, (Algebra.TensorProduct.includeLeft_surjective (S := R) <|
        IsPurelyInseparable.surjective_algebraMap_of_isSeparable k K) _⟩
  · convert bot_le
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap k K).injective

/-- If `L` is a purely inseparable extension of `K` over `R` and `S` is an `R`-algebra,
the induced map `Spec (L ⊗[R] S) ⟶ Spec (K ⊗[R] S)` is a homeomorphism. -/
lemma PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable [Algebra R K]
    [Algebra R S] (L : Type*) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [IsPurelyInseparable K L] :
    IsHomeomorph (PrimeSpectrum.comap <|
      (Algebra.TensorProduct.map (Algebra.ofId K L) (AlgHom.id R S)).toRingHom) := by
  let e : (L ⊗[R] S) ≃ₐ[K] L ⊗[K] (K ⊗[R] S) :=
    (Algebra.TensorProduct.cancelBaseChange R K K L S).symm
  let e2 : L ⊗[K] (K ⊗[R] S) ≃ₐ[K] (K ⊗[R] S) ⊗[K] L := Algebra.TensorProduct.comm ..
  have heq : Algebra.TensorProduct.map (Algebra.ofId K L) (AlgHom.id R S) =
      (e.symm.toAlgHom.comp e2.symm.toAlgHom).comp
        (IsScalarTower.toAlgHom K (K ⊗[R] S) ((K ⊗[R] S) ⊗[K] L)) := by
    ext; simp [e, e2]
  rw [heq]
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    AlgEquiv.toAlgHom_toRingHom, IsScalarTower.coe_toAlgHom, comap_comp, ContinuousMap.coe_comp]
  exact (PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable K L (K ⊗[R] S)).comp <|
    (PrimeSpectrum.isHomeomorph_comap_of_bijective e2.symm.bijective).comp <|
    PrimeSpectrum.isHomeomorph_comap_of_bijective e.symm.bijective
