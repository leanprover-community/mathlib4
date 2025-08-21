/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Junyan Xu
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
/-- If the kernel of `f : R →+* S` consists of nilpotent elements and for every `x : S`,
there exists `n > 0` such that `x ^ n` is in the range of `f`, then `Spec f` is a homeomorphism.
Note: This does not hold for semirings, because `ℕ →+* ℤ` satisfies these conditions, but
`Spec ℕ` has one more point than `Spec ℤ`. -/
@[stacks 0BR8 "Homeomorphism part"]
lemma PrimeSpectrum.isHomeomorph_comap (f : R →+* S) (H : ∀ (x : S), ∃ n > 0, x ^ n ∈ f.range)
    (hker : RingHom.ker f ≤ nilradical R) : IsHomeomorph (comap f) := by
  have h1 : Function.Injective (comap f) := by
    intro q q' hqq'
    ext x
    obtain ⟨n, hn, y, hy⟩ := H x
    rw [← q.2.pow_mem_iff_mem _ hn, ← q'.2.pow_mem_iff_mem _ hn, ← hy]
    rw [PrimeSpectrum.ext_iff, SetLike.ext_iff] at hqq'
    apply hqq'
  have hint : f.kerLift.IsIntegral := fun x ↦
    have ⟨n, hn, y, hy⟩ := H x
    let _ := f.kerLift.toAlgebra
    IsIntegral.of_pow hn (hy ▸ f.kerLift.isIntegralElem_map (x := ⟦y⟧))
  have hbij : Function.Bijective (comap f) :=
    ⟨h1, (comap_quotientMk_bijective_of_le_nilradical hker).2.comp <|
      hint.specComap_surjective f.kerLift_injective⟩
  refine ⟨(comap f).continuous, ?_, h1, hbij.2⟩
  rw [isTopologicalBasis_basic_opens.isOpenMap_iff]
  rintro - ⟨s, rfl⟩
  obtain ⟨n, hn, r, hr⟩ := H s
  have : (comap f) '' (basicOpen s) = basicOpen r :=
    (Set.eq_preimage_iff_image_eq hbij).mp <| by rw [← basicOpen_pow _ n hn, ← hr]; rfl
  exact this ▸ isOpen_basicOpen

/-- Purely inseparable field extensions are universal homeomorphisms. -/
@[stacks 0BRA "Special case for purely inseparable field extensions"]
lemma PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable [IsPurelyInseparable k K] :
    IsHomeomorph (comap <| algebraMap R (R ⊗[k] K)) := by
  let q := ringExpChar k
  refine isHomeomorph_comap _ (IsPurelyInseparable.exists_pow_mem_range_tensorProduct) ?_
  convert bot_le
  rw [← RingHom.injective_iff_ker_eq_bot]
  exact Algebra.TensorProduct.includeLeft_injective (S := R) (algebraMap k K).injective

/-- If `L` is a purely inseparable extension of `K` over `R` and `S` is an `R`-algebra,
the induced map `Spec (L ⊗[R] S) ⟶ Spec (K ⊗[R] S)` is a homeomorphism. -/
lemma PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable [Algebra R K]
    [Algebra R S] (L : Type*) [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [IsPurelyInseparable K L] :
    IsHomeomorph (comap (Algebra.TensorProduct.map (Algebra.ofId K L) (.id R S)).toRingHom) := by
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
  exact (isHomeomorph_comap_of_isPurelyInseparable K L (K ⊗[R] S)).comp <|
    (isHomeomorph_comap_of_bijective e2.symm.bijective).comp <|
    isHomeomorph_comap_of_bijective e.symm.bijective
