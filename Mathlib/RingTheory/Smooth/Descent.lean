/-
Copyright (c) 2022 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.RingOfDefinition

/-!

# Descent of smooth morphisms

If `A` is a smooth `R`-algebra, there exists a subring `R₀` of `R` of finite type over `ℤ` and
a smooth `R₀`-algebra `A₀` such that `A` is `R`-isomorphic to `R ⊗[R₀] A₀`.

-/

universe u v

open TensorProduct

namespace Algebra

variable (R : Type u) [CommRing R]

lemma finiteType_of_adjoin_finite {A : Type v} [CommRing A] [Algebra R A] (T : Set A) (h : Set.Finite T) :
    FiniteType R (Algebra.adjoin R T) :=
  sorry

variable (A : Type u) [CommRing A] [Algebra R A]
variable [FormallySmooth R A] (hfp : FinitePresentation R A)

section

variable {R}

def MvPolynomial.coefficients {ι : Type*} (p : MvPolynomial ι R) : Set R := (p.coeff '' p.support)

instance {ι : Type*} (p : MvPolynomial ι R) : Finite (MvPolynomial.coefficients p) := by
  admit

def MvPolynomial.Set.coefficients {ι : Type*} (S : Set (MvPolynomial ι R)) : Set R := sorry

end

namespace Smooth

--lemma Ideal.mem_pow (I : Ideal R) (n : ℕ) (x : R) :
--  x ∈ I ^ n ↔ ∃ (S : Finset I) (f : S → R), Finset.sum S (fun i ↦ f i * i) := sorry

lemma AlgHom.apply_mvPolynomial' (σ : Type*) {S : Type*} [CommRing S] [Algebra R S]
    (f : MvPolynomial σ R →ₐ[R] S) (p : MvPolynomial σ R) :
    f p = Finset.sum
      (MvPolynomial.support p)
      fun x ↦ (MvPolynomial.coeff x p) •
        (Finsupp.prod x (fun i k ↦ (f (MvPolynomial.X i)) ^ k)) :=
  sorry

--def SetProd (S : Set R) (n : ℕ) : Set R :=
--  { r : R |  }

open Pointwise

lemma Ideal.span_pow (S : Set R) (n : ℕ) :
    Ideal.span S ^ n = Ideal.span (S ^ n) := by
  ext x
  constructor
  intro h
  admit
  admit
  --rw [Set.mem_pow (s := Ideal.span S) (a := x) (n := n)] at h

lemma Ideal.mem_span_asSum (S : Set R) (x : R) (h : x ∈ Ideal.span S) :
    ∃ (f : S →₀ R), x = Finsupp.sum f (fun s r ↦ r * s) := by
  admit

#check Ideal.mem_span_asSum

lemma Ideal.mem_span_pow (S : Set R) (r : R) (n : ℕ) :
    r ∈ Ideal.span S ^ n ↔
      ∃ (c : Fin n → (S →₀ R)), True := sorry

--lemma Ideal.mem_sq (S : Set R) (r : R) (h : r ∈ (Ideal.span S) ^ 2) :
--    ∃ (f : Fin 2 →₀ (S →₀ R)),
--      r = Finsupp.sum f := sorry

lemma Ideal.mem_sq (I : Ideal R) (S : Set R) (hsp : I = Ideal.span S) (x : R)
  (h : x ∈ I ^ 2) : ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p 2 ∧ MvPolynomial.eval Subtype.val p = x := sorry

--lemma AlgHom.apply_mvPolynomial (σ : Type*) {S : Type*} [CommRing S] [Algebra R S] (f : MvPolynomial σ R →ₐ[R] S)
--    (m : σ →₀ ℕ) (r : R) :
--    f ((MvPolynomial.monomial m) r) = r • f (MvPolynomial.monomial m 1) := sorry

/-- https://stacks.math.columbia.edu/tag/00TP -/
theorem descent : ∃ (R₀ : Subring R) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀)
    (f : A ≃ₐ[R] R ⊗[R₀] A₀),
    FiniteType ℤ R₀ ∧ FinitePresentation R₀ A₀ ∧ FormallySmooth R₀ A₀ := by
  obtain ⟨ι, hfin, f, hfsurj, S, hS⟩ := FinitePresentation.iff_quotient_mvPolynomial'.mp hfp
  have : FormallySmooth R (MvPolynomial ι R) := inferInstance
  obtain ⟨σ, hsig⟩ := (FormallySmooth.iff_split_surjection f hfsurj).mp inferInstance
  let I : Ideal (MvPolynomial ι R) := RingHom.ker f.toRingHom ^ 2
  choose h heq using (fun i ↦ Quotient.exists_rep (σ (f (MvPolynomial.X i))))
  have heq (i : ι) : Ideal.Quotient.mk I (h i) = σ (f (MvPolynomial.X i)) := heq i
  have hsigf_zero (s : S) : σ (f s) = 0 := by
    have : f s = 0 := by
      change (s : MvPolynomial ι R) ∈ RingHom.ker f.toRingHom
      rw [← hS]
      exact Submodule.subset_span s.property
    rw [this]
    simp
  let coeff (s : S) : (ι →₀ ℕ) →₀ R := s.val
  let sOfh (s : S) : MvPolynomial ι R :=
    MvPolynomial.aeval (fun j : ι => h j) (s : MvPolynomial ι R)
  have hfeq : f = MvPolynomial.aeval (f ∘ MvPolynomial.X) :=
    MvPolynomial.aeval_unique f
  have hcomp (s : S) : σ (f s) = Ideal.Quotient.mk I (sOfh s) := by
    rw [AlgHom.apply_mvPolynomial']
    simp
    dsimp [sOfh]
    conv => rhs; rw [MvPolynomial.as_sum (s : MvPolynomial ι R)]
    rw [MvPolynomial.aeval_sum]
    simp only [MvPolynomial.aeval_monomial, Algebra.smul_def]
    simp [heq]
    congr
  have hinkersq (s : S) : sOfh s ∈ RingHom.ker f.toRingHom ^ 2 := by
    change sOfh s ∈ I
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hcomp s, hsigf_zero]
  have (s : S) : ∃ (p : MvPolynomial S (MvPolynomial ι R)),
      MvPolynomial.IsHomogeneous p 2 ∧ MvPolynomial.eval Subtype.val p = sOfh s := by
    apply Ideal.mem_sq _ (RingHom.ker f.toRingHom)
    · exact hS.symm
    · exact hinkersq s
  choose p hphomog hpeval using this
  let coeffs_s : Set R := MvPolynomial.Set.coefficients (S : Set (MvPolynomial ι R))
  let coeffs_h : Set R := MvPolynomial.Set.coefficients (Set.range h)
  let coeffs_p : Set R := MvPolynomial.Set.coefficients <|
    MvPolynomial.Set.coefficients (Set.range p)
  let coeffs : Set R := coeffs_s ∪ coeffs_h ∪ coeffs_p
  let R₀ := (Algebra.adjoin ℤ coeffs).toSubring
  use R₀
  let S₀ : Set (MvPolynomial ι R₀) :=
    MvPolynomial.map (SubringClass.subtype R₀) ⁻¹' S
  have hS₀fin : Set.Finite S₀ := by
    apply Set.Finite.preimage
    · apply Set.injOn_of_injective
      apply MvPolynomial.map_injective
      simp only [SubringClass.coeSubtype]
      exact Subtype.val_injective
    · exact Finset.finite_toSet S
  let I₀ : Ideal (MvPolynomial ι R₀) := Ideal.span S₀
  let A₀ : Type _ := MvPolynomial ι R₀ ⧸ I₀
  letI : Module R₀ A₀ := Algebra.toModule
  use A₀
  use inferInstance
  use inferInstance
  let f' : (MvPolynomial ι R ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R] R ⊗[R₀] A₀ := by
    apply RingOfDefinition.baseChangeIso (T := S) (hgen := hS.symm)
    · rw [← hS]
      apply Ideal.span_preimage_le_comap
    · intro r hr
      refine ⟨⟨r, ?_⟩, rfl⟩
      apply Algebra.subset_adjoin
      apply Set.mem_union_left
      apply Set.mem_union_left
      exact hr
    · intro p hp
      exact Ideal.subset_span hp
  let is : (MvPolynomial ι R ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R] A :=
    Ideal.quotientKerAlgEquivOfSurjective hfsurj
  let f : A ≃ₐ[R] R ⊗[R₀] A₀ := is.symm.trans f'
  use f
  refine ⟨?_, ?_, ?_⟩
  · apply finiteType_of_adjoin_finite
    apply Set.Finite.union
    apply Set.Finite.union
    · apply MvPolynomial.Set.coefficients_finite_of_finite
      exact Finset.finite_toSet S
    · apply MvPolynomial.Set.coefficients_finite_of_finite
      exact Set.finite_range h
    · apply MvPolynomial.Set.coefficients_finite_of_finite
      apply MvPolynomial.Set.coefficients_finite_of_finite
      exact Set.finite_range p
  · apply FinitePresentation.quotient
    obtain ⟨S₀', hS₀'⟩ := Set.Finite.exists_finset_coe hS₀fin
    use S₀'
    rw [hS₀']
    exact FinitePresentation.mvPolynomial R₀ ι
  · fapply FormallySmooth.of_split (Ideal.Quotient.mkₐ R₀ I₀)
    · admit
    · admit

end Smooth
