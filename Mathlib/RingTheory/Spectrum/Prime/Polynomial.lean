/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Prime spectrum of (multivariate) polynomials

Also see `AlgebraicGeometry/AffineSpace` for the affine space over arbitrary schemes.

## Main results
- `isNilpotent_tensor_residueField_iff`:
  If `A` is a finite free `R`-algebra, then `f : A` is nilpotent on `κ(𝔭) ⊗ A` for some
  prime `𝔭 ◃ R` if and only if every non-leading coefficient of `charpoly(f)` is in `𝔭`.
- `Polynomial.exists_image_comap_of_monic`:
  If `g : R[X]` is monic, the image of `Z(g) ∩ D(f) : Spec R[X]` in `Spec R` is compact open.
- `Polynomial.isOpenMap_comap_C`: The structure map `Spec R[X] → Spec R` is an open map.
- `MvPolynomial.isOpenMap_comap_C`: The structure map `Spec R[X̲] → Spec R` is an open map.

-/

open Polynomial TensorProduct PrimeSpectrum

variable {R M A} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

/-- If `A` is a finite free `R`-algebra, then `f : A` is nilpotent on `κ(𝔭) ⊗ A` for some
prime `𝔭 ◃ R` if and only if every non-leading coefficient of `charpoly(f)` is in `𝔭`. -/
lemma isNilpotent_tensor_residueField_iff
    [Module.Free R A] [Module.Finite R A] (f : A) (I : Ideal R) [I.IsPrime] :
    IsNilpotent (algebraMap A (A ⊗[R] I.ResidueField) f) ↔
      ∀ i < Module.finrank R A, (Algebra.lmul R A f).charpoly.coeff i ∈ I := by
  cases subsingleton_or_nontrivial R
  · have := (algebraMap R (A ⊗[R] I.ResidueField)).codomain_trivial
    simp [Subsingleton.elim I ⊤, Subsingleton.elim (f ⊗ₜ[R] (1 : I.ResidueField)) 0]
  have : Module.finrank I.ResidueField (I.ResidueField ⊗[R] A) = Module.finrank R A := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  rw [← IsNilpotent.map_iff (Algebra.TensorProduct.comm R A I.ResidueField).injective]
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.coe_lmul_eq_mul, Algebra.TensorProduct.comm_tmul]
  rw [← IsNilpotent.map_iff (Algebra.lmul_injective (R := I.ResidueField)),
    LinearMap.isNilpotent_iff_charpoly, ← Algebra.baseChange_lmul, LinearMap.charpoly_baseChange]
  simp_rw [this, ← ((LinearMap.mul R A) f).charpoly_natDegree]
  constructor
  · intro e i hi
    replace e := congr(($e).coeff i)
    simpa only [Algebra.coe_lmul_eq_mul, coeff_map, coeff_X_pow, hi.ne, ↓reduceIte,
      ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using e
  · intro H
    ext i
    obtain (hi | hi) := eq_or_ne i ((LinearMap.mul R A) f).charpoly.natDegree
    · simp only [Algebra.coe_lmul_eq_mul, hi, coeff_map, coeff_X_pow, ↓reduceIte]
      rw [← Polynomial.leadingCoeff, ((LinearMap.mul R A) f).charpoly_monic, map_one]
    obtain (hi | hi) := lt_or_gt_of_ne hi
    · simpa [hi.ne, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField] using H i hi
    · simp [hi.ne', coeff_eq_zero_of_natDegree_lt hi]

namespace PrimeSpectrum

/-- Let `A` be an `R`-algebra.
`𝔭 : Spec R` is in the image of `Z(I) ∩ D(f) ⊆ Spec S`
if and only if `f` is not nilpotent on `κ(𝔭) ⊗ A ⧸ I`. -/
lemma mem_image_comap_zeroLocus_sdiff (f : A) (s : Set A) (x) :
    x ∈ comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) ↔
      ¬ IsNilpotent (algebraMap A ((A ⧸ Ideal.span s) ⊗[R] x.asIdeal.ResidueField) f) := by
  constructor
  · rintro ⟨q, ⟨hqg, hqf⟩, rfl⟩ H
    simp only [mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe] at hqg hqf
    have hs : Ideal.span s ≤ RingHom.ker (algebraMap A q.asIdeal.ResidueField) := by
      rwa [Ideal.span_le, Ideal.ker_algebraMap_residueField]
    let F : (A ⧸ Ideal.span s) ⊗[R] (q.asIdeal.comap (algebraMap R A)).ResidueField →ₐ[A]
        q.asIdeal.ResidueField :=
      Algebra.TensorProduct.lift
        (Ideal.Quotient.liftₐ (Ideal.span s) (Algebra.ofId A _) hs)
        (Ideal.ResidueField.mapₐ _ _ rfl)
        fun _ _ ↦ .all _ _
    have := H.map F
    rw [AlgHom.commutes, isNilpotent_iff_eq_zero, ← RingHom.mem_ker,
      Ideal.ker_algebraMap_residueField] at this
    exact hqf this
  · intro H
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf] at H
    simp only [Set.mem_setOf_eq, Algebra.TensorProduct.algebraMap_apply,
      Ideal.Quotient.algebraMap_eq, not_forall] at H
    obtain ⟨q, hq, hfq⟩ := H
    have : ∀ a ∈ s, Ideal.Quotient.mk (Ideal.span s) a ⊗ₜ[R] 1 ∈ q := fun a ha ↦ by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ha)]
    refine ⟨comap (algebraMap A _) ⟨q, hq⟩, ⟨by simpa [Set.subset_def], by simpa⟩, ?_⟩
    rw [← comap_comp_apply, ← IsScalarTower.algebraMap_eq,
      ← Algebra.TensorProduct.includeRight.comp_algebraMap, comap_comp_apply,
      Subsingleton.elim (α := PrimeSpectrum x.asIdeal.ResidueField) (comap _ _) ⊥]
    ext a
    exact congr(a ∈ $(Ideal.ker_algebraMap_residueField _))

/-- Let `A` be an `R`-algebra.
`𝔭 : Spec R` is in the image of `D(f) ⊆ Spec S`
if and only if `f` is not nilpotent on `κ(𝔭) ⊗ A`. -/
lemma mem_image_comap_basicOpen (f : A) (x) :
    x ∈ comap (algebraMap R A) '' basicOpen f ↔
      ¬ IsNilpotent (algebraMap A (A ⊗[R] x.asIdeal.ResidueField) f) := by
  have e : A ⊗[R] x.asIdeal.ResidueField ≃ₐ[A]
      (A ⧸ (Ideal.span ∅ : Ideal A)) ⊗[R] x.asIdeal.ResidueField := by
    refine Algebra.TensorProduct.congr ?f AlgEquiv.refl
    rw [Ideal.span_empty]
    exact { __ := (RingEquiv.quotientBot A).symm, map_smul' _ _ := rfl }
  rw [← IsNilpotent.map_iff e.injective, AlgEquiv.commutes,
    ← mem_image_comap_zeroLocus_sdiff f ∅ x, zeroLocus_empty, ← Set.compl_eq_univ_diff,
    basicOpen_eq_zeroLocus_compl]

/-- Let `A` be an `R`-algebra. If `A ⧸ I` is finite free over `R`,
then the image of `Z(I) ∩ D(f) ⊆ Spec S` in `Spec R` is compact open. -/
lemma exists_image_comap_of_finite_of_free (f : A) (s : Set A)
    [Module.Finite R (A ⧸ Ideal.span s)] [Module.Free R (A ⧸ Ideal.span s)] :
    ∃ t : Finset R, comap (algebraMap R A) '' (zeroLocus s \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  classical
  use (Finset.range (Module.finrank R (A ⧸ Ideal.span s))).image
    (Algebra.lmul R (A ⧸ Ideal.span s) (Ideal.Quotient.mk _ f)).charpoly.coeff
  ext x
  rw [mem_image_comap_zeroLocus_sdiff, IsScalarTower.algebraMap_apply A (A ⧸ Ideal.span s),
    isNilpotent_tensor_residueField_iff]
  simp [Set.subset_def]

end PrimeSpectrum

namespace Polynomial

lemma mem_image_comap_C_basicOpen (f : R[X]) (x : PrimeSpectrum R) :
    x ∈ comap C '' basicOpen f ↔ ∃ i, f.coeff i ∉ x.asIdeal := by
  trans f.map (algebraMap R x.asIdeal.ResidueField) ≠ 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : R[X] ⊗[R] x.asIdeal.ResidueField ≃ₐ[R] x.asIdeal.ResidueField[X] :=
      (Algebra.TensorProduct.comm R _ _).trans (polyEquivTensor R x.asIdeal.ResidueField).symm
    rw [← IsNilpotent.map_iff e.injective, isNilpotent_iff_eq_zero]
    change (e.toAlgHom.toRingHom).comp (algebraMap _ _) f = 0 ↔ Polynomial.mapRingHom _ f = 0
    congr!
    ext1
    · ext; simp [e]
    · simp [e]
  · simp [Polynomial.ext_iff]

lemma image_comap_C_basicOpen (f : R[X]) :
    comap C '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ := by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

lemma isOpenMap_comap_C : IsOpenMap (comap (R := R) C) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

lemma comap_C_surjective : Function.Surjective (comap (R := R) C) := by
  intro x
  refine ⟨comap (evalRingHom 0) x, ?_⟩
  rw [← comap_comp_apply, (show (evalRingHom 0).comp C = .id R by ext; simp),
    comap_id, ContinuousMap.id_apply]

lemma exists_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    ∃ t : Finset R, comap C '' (zeroLocus {g} \ zeroLocus {f}) = (zeroLocus t)ᶜ := by
  apply (config := { allowSynthFailures := true }) exists_image_comap_of_finite_of_free
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis
  · exact .of_basis (AdjoinRoot.powerBasis' hg).basis

lemma isCompact_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsCompact (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht, ← (t : Set R).iUnion_of_singleton_coe, zeroLocus_iUnion, Set.compl_iInter]
  apply isCompact_iUnion
  exact fun _ ↦ by simpa using isCompact_basicOpen _

lemma isOpen_image_comap_of_monic (f g : R[X]) (hg : g.Monic) :
    IsOpen (comap C '' (zeroLocus {g} \ zeroLocus {f})) := by
  obtain ⟨t, ht⟩ := exists_image_comap_of_monic f g hg
  rw [ht]
  exact (isClosed_zeroLocus (R := R) t).isOpen_compl

end Polynomial

namespace MvPolynomial

variable {σ : Type*}

lemma mem_image_comap_C_basicOpen (f : MvPolynomial σ R) (x : PrimeSpectrum R) :
    x ∈ comap (C (σ := σ)) '' basicOpen f ↔ ∃ i, f.coeff i ∉ x.asIdeal := by
  classical
  trans f.map (algebraMap R x.asIdeal.ResidueField) ≠ 0
  · refine (mem_image_comap_basicOpen _ _).trans (not_iff_not.mpr ?_)
    let e : MvPolynomial σ R ⊗[R] x.asIdeal.ResidueField ≃ₐ[R]
        MvPolynomial σ x.asIdeal.ResidueField := scalarRTensorAlgEquiv
    rw [← IsNilpotent.map_iff e.injective, isNilpotent_iff_eq_zero]
    change (e.toAlgHom.toRingHom).comp (algebraMap _ _) f = 0 ↔ MvPolynomial.map _ f = 0
    congr!
    ext
    · simp [scalarRTensorAlgEquiv, e, coeff_map,
        Algebra.smul_def, apply_ite (f := algebraMap _ _)]
    · simp [e, scalarRTensorAlgEquiv, coeff_map, coeff_X']
  · simp [MvPolynomial.ext_iff, coeff_map]

lemma image_comap_C_basicOpen (f : MvPolynomial σ R) :
    comap (C (σ := σ)) '' basicOpen f = (zeroLocus (Set.range f.coeff))ᶜ := by
  ext p
  rw [mem_image_comap_C_basicOpen]
  simp [Set.range_subset_iff]

lemma isOpenMap_comap_C : IsOpenMap (comap (R := R) (C (σ := σ))) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := isTopologicalBasis_basic_opens.open_eq_sUnion hU
  rw [Set.image_sUnion]
  apply isOpen_sUnion
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨r, rfl⟩ := hS ht
  simp only [image_comap_C_basicOpen]
  exact (isClosed_zeroLocus _).isOpen_compl

lemma comap_C_surjective : Function.Surjective (comap (R := R) (C (σ := σ))) := by
  intro x
  refine ⟨comap (eval₂Hom (.id _) 0) x, ?_⟩
  rw [← comap_comp_apply, (show (eval₂Hom (.id _) 0).comp C = .id R by ext; simp),
    comap_id, ContinuousMap.id_apply]

end MvPolynomial
