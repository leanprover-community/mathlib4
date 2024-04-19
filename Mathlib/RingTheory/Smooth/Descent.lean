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

section

variable {R}

variable {S : Type v} [CommRing S] (f : R →+* S)
variable {A : Set R} {B : Set S} (hf : Set.MapsTo f A B)

def foo : MvPolynomial A R →+* S := f.comp (MvPolynomial.eval Subtype.val)
noncomputable def foo' : MvPolynomial A R →+* S :=
  (MvPolynomial.eval Subtype.val).comp ((MvPolynomial.map f).comp (MvPolynomial.rename hf.restrict).toRingHom)

lemma diag_rename_comm :
    f.comp (MvPolynomial.eval Subtype.val)
    = (MvPolynomial.eval Subtype.val).comp
      ((MvPolynomial.map f).comp (MvPolynomial.rename hf.restrict).toRingHom) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro a
    simp

lemma diag_rename_comm_apply (p : MvPolynomial A R) :
    f ((MvPolynomial.eval Subtype.val) p) =
      (MvPolynomial.eval Subtype.val) ((MvPolynomial.map f) (MvPolynomial.rename hf.restrict p)) := by
  change (f.comp (MvPolynomial.eval Subtype.val)) p
    = ((MvPolynomial.eval Subtype.val).comp
      ((MvPolynomial.map f).comp (MvPolynomial.rename hf.restrict).toRingHom)) p
  rw [diag_rename_comm]

end

lemma finiteType_of_adjoin_finite {A : Type v} [CommRing A] [Algebra R A] (T : Set A) (h : Set.Finite T) :
    FiniteType R (Algebra.adjoin R T) :=
  sorry

variable (A : Type u) [CommRing A] [Algebra R A]
variable [FormallySmooth R A] (hfp : FinitePresentation R A)

section

variable {R}

instance {ι : Type*} (p : MvPolynomial ι R) : Finite (MvPolynomial.coefficients p) := by
  admit

end

namespace Smooth

lemma AlgHom.apply_mvPolynomial' (σ : Type*) {S : Type*} [CommRing S] [Algebra R S]
    (f : MvPolynomial σ R →ₐ[R] S) (p : MvPolynomial σ R) :
    f p = Finset.sum
      (MvPolynomial.support p)
      fun x ↦ (MvPolynomial.coeff x p) •
        (Finsupp.prod x (fun i k ↦ (f (MvPolynomial.X i)) ^ k)) :=
  sorry

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

lemma Ideal.mem_sq (I : Ideal R) (S : Set R) (hsp : I = Ideal.span S) (x : R) :
  x ∈ I ^ 2 ↔ ∃ (p : MvPolynomial S R),
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
  let sOfh (s : S) : MvPolynomial ι R :=
    MvPolynomial.aeval (fun j : ι => h j) (s : MvPolynomial ι R)
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
    apply (Ideal.mem_sq _ (RingHom.ker f.toRingHom) _ hS.symm _).mp
    · exact hinkersq s
  choose p hphomog hpeval using this
  let coeffs_s : Set R := MvPolynomial.Set.coefficients (S : Set (MvPolynomial ι R))
  let coeffs_h : Set R := MvPolynomial.Set.coefficients (Set.range h)
  let coeffs_p : Set R := MvPolynomial.Set.coefficients <|
    MvPolynomial.Set.coefficients (Set.range p)
  let coeffs : Set R := coeffs_s ∪ coeffs_h ∪ coeffs_p
  let R₀ := (Algebra.adjoin ℤ coeffs).toSubring
  let h' (i : ι) : MvPolynomial ι R₀ := by
    apply RingOfDefinition.MvPolynomial.choosePreimageOfCoeffs (h i)
    apply Set.Subset.trans
    exact MvPolynomial.Set.coefficients_in (Set.range h) (h i) (Set.mem_range_self i)
    intro r hr
    refine ⟨⟨r, ?_⟩, rfl⟩
    apply Algebra.subset_adjoin
    apply Set.mem_union_left
    apply Set.mem_union_right
    exact hr
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
    · fapply Ideal.Quotient.liftₐ I₀
      · apply AlgHom.comp (Ideal.Quotient.mkₐ R₀ (RingHom.ker (Ideal.Quotient.mkₐ (↥R₀) I₀).toRingHom ^ 2))
        exact MvPolynomial.aeval h'
      · intro a ha
        simp only [AlgHom.comp_apply, ← RingHom.mem_ker]
        erw [Ideal.Quotient.mkₐ_ker R₀ (RingHom.ker (Ideal.Quotient.mkₐ (↥R₀) I₀).toRingHom ^ 2)]
        erw [Ideal.Quotient.mkₐ_ker R₀]
        admit
        --refine Submodule.span_induction ha ?_ ?_ ?_ ?_
        --· intro s hs
        --  rw [Ideal.mem_sq (S := S₀) (hsp := rfl)]
        --  admit
        --· simp
        --· intro x y hx hy
        --  simp
        --· intro r x hx
        --  simp
    · admit

section

variable {R : Type*} [CommRing R]-- {A : Type*} [CommRing A] [Algebra R A]

variable {ι : Type*} (I : Ideal (MvPolynomial ι R)) (S : Set (MvPolynomial ι R))

variable (σ : MvPolynomial ι R ⧸ I →ₐ[R] MvPolynomial ι R ⧸ (I ^ 2))

noncomputable def hAux (i : ι) : MvPolynomial ι R :=
  (Quotient.exists_rep (σ (Ideal.Quotient.mk I (MvPolynomial.X i)))).choose

@[simp]
lemma hAux_eq (i : ι) : hAux I σ i = σ (MvPolynomial.X i : MvPolynomial ι R) := by
  simp only [hAux]
  exact Exists.choose_spec (Quotient.exists_rep _)

noncomputable def sOfh : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval (fun j : ι => hAux I σ j)

lemma sigma_eq_mk_sOfh (p : MvPolynomial ι R) : σ p = sOfh I σ p := by
  let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    σ.comp (Ideal.Quotient.mkₐ R I)
  let g : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    (Ideal.Quotient.mkₐ R (I ^ 2)).comp (sOfh I σ)
  suffices h : f = g by
    change f p = g p
    congr
  apply MvPolynomial.algHom_ext
  intro i
  simp [f, g, sOfh]

lemma sOfh_mem_sq (p : MvPolynomial ι R) (hp : p ∈ I) : sOfh I σ p ∈ I ^ 2 := by
  suffices h : Ideal.Quotient.mk I p = 0 by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← sigma_eq_mk_sOfh, h]
    simp
  rwa [Ideal.Quotient.eq_zero_iff_mem]

lemma sOfh_exists_P (p : MvPolynomial ι R) (hp : p ∈ I) (hspan : Ideal.span S = I) :
    ∃ (P : MvPolynomial S (MvPolynomial ι R)),
        MvPolynomial.IsHomogeneous P 2 ∧ MvPolynomial.eval Subtype.val P = sOfh I σ p :=
  (Ideal.mem_sq _ I _ hspan.symm _).mp <| sOfh_mem_sq I σ p hp

variable (R₀ : Subring R) (hcoeffsS : MvPolynomial.Set.coefficients S ⊆ R₀)
  (hcoeffsH : MvPolynomial.Set.coefficients (Set.range <| hAux I σ) ⊆ R₀)

variable (P : S → MvPolynomial S (MvPolynomial ι R))
variable (hPhom : ∀ s : S, MvPolynomial.IsHomogeneous (P s) 2)
variable (hPeval : ∀ s : S, MvPolynomial.eval Subtype.val (P s) = sOfh I σ s)
variable (hcoeffsP : MvPolynomial.Set.coefficients (MvPolynomial.Set.coefficients (Set.range P)) ⊆ R₀)

noncomputable def hAux₀ (i : ι) : MvPolynomial ι R₀ := by
  apply RingOfDefinition.MvPolynomial.choosePreimageOfCoeffs (hAux I σ i)
  apply Set.Subset.trans
  · exact MvPolynomial.Set.coefficients_in (Set.range <| hAux I σ) (hAux I σ i) (Set.mem_range_self i)
  · intro r hr
    refine ⟨⟨r, ?_⟩, rfl⟩
    apply hcoeffsH
    exact hr

variable (I₀ : Ideal (MvPolynomial ι R₀)) (S₀ : Set (MvPolynomial ι R₀))
  (hspan₀ : Ideal.span S₀ = I₀)
  (hpreim₀ : MvPolynomial.map (SubringClass.subtype R₀) ⁻¹' S = S₀)

noncomputable def varTrans : S₀ ≃ S := by
  apply Equiv.ofBijective ?_ ⟨?_, ?_⟩
  · intro ⟨s, hs⟩
    exact ⟨MvPolynomial.map (SubringClass.subtype R₀) s, by rw [← hpreim₀] at hs; exact hs⟩
  · admit
  · admit

#check AlgHom.comp (MvPolynomial.map (MvPolynomial.map (SubringClass.subtype R₀)))
  (MvPolynomial.rename (varTrans S R₀ S₀ hpreim₀))

--lemma comm_diag_varTrans :
--    (MvPolynomial.eval (Subtype.val)).comp
--    ((MvPolynomial.map (SubringClass.subtype R₀)).comp

noncomputable def sOfh₀ : MvPolynomial ι R₀ →ₐ[R₀] MvPolynomial ι R₀ :=
  MvPolynomial.aeval (fun j : ι => hAux₀ I σ R₀ hcoeffsH j)

@[simp]
lemma incl_sOfh₀ (p : MvPolynomial ι R₀) :
    (MvPolynomial.map (SubringClass.subtype R₀)) ((sOfh₀ I σ R₀ hcoeffsH) p)
    = sOfh I σ (MvPolynomial.map (SubringClass.subtype R₀) p) := sorry

variable (hspan : Ideal.span S = I)

lemma exists_PAux₀ (s : MvPolynomial ι R₀) (hs : s ∈ S₀) :
    ∃ (P₀ : MvPolynomial S₀ (MvPolynomial ι R₀)),
      MvPolynomial.IsHomogeneous P₀ 2 ∧
      MvPolynomial.eval Subtype.val P₀ = sOfh₀ I σ R₀ hcoeffsH s := by
  let p : MvPolynomial ι R := MvPolynomial.map (SubringClass.subtype R₀) s
  have hp : p ∈ S := sorry
  let Ps : MvPolynomial S (MvPolynomial ι R) := P ⟨p, hp⟩
  have hPshomog : MvPolynomial.IsHomogeneous Ps 2 := hPhom ⟨p, hp⟩
  have hc : MvPolynomial.coefficients Ps ⊆ Set.range (MvPolynomial.map (SubringClass.subtype R₀)) := sorry
  obtain ⟨P', hP'⟩ := RingOfDefinition.exists_preimage_of_coefficients'
    (MvPolynomial.map (SubringClass.subtype R₀))
    Ps hc
  have hP'homog : MvPolynomial.IsHomogeneous P' 2 := by
    refine MvPolynomial.isHomogeneous_of_map (MvPolynomial.map (SubringClass.subtype R₀)) ?_ P' ?_
    · apply MvPolynomial.map_injective
      exact Subtype.val_injective
    · rw [hP']
      exact hPshomog
  let f : S → S₀ := sorry
  let P₀ : MvPolynomial S₀ (MvPolynomial ι R₀) :=
    MvPolynomial.rename f P'
  have hinj : Function.Injective
      (MvPolynomial.map (SubringClass.subtype R₀) : MvPolynomial ι R₀ →+* MvPolynomial ι R) := by
    apply MvPolynomial.map_injective
    exact Subtype.val_injective
  refine ⟨P₀, ?_, ?_⟩
  · rw [MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff]
    refine MvPolynomial.isHomogeneous_of_map (MvPolynomial.map (SubringClass.subtype R₀)) ?_ P' ?_
    · apply MvPolynomial.map_injective
      exact Subtype.val_injective
    · rw [hP']
      exact hPshomog
    · admit
  · simp [P₀]
    --rw [MvPolynomial.eval_rename]
    apply hinj
    simp
    -- ∀ (s : S), MvPolynomial.eval Subtype.val (P s) = sOfh I σ s

lemma hAux₀_eval (a : MvPolynomial ι R₀) (ha : a ∈ I₀):
    MvPolynomial.aeval (hAux₀ I σ R₀ hcoeffsH) a ∈ I₀ ^ 2 := by
  rw [← hspan₀] at ha
  refine Submodule.span_induction ha ?_ ?_ ?_ ?_
  · intro s hs
    rw [Ideal.mem_sq]
    exact exists_PAux₀ I σ R₀ hcoeffsH S₀ s hs
    exact hspan₀.symm
  · simp
  · intro x y hx hy
    simp only [map_add]
    exact Ideal.add_mem _ hx hy
  · intro a x hx
    simp only [smul_eq_mul, _root_.map_mul]
    apply Ideal.mul_mem_left
    exact hx

end

end Smooth
