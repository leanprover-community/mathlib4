/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.FinitePresentation

/-!

# Descent of finitely presented algebras

If `A` is a finitely presented `R`-algebra, there exists a subring `R₀` of `R` of finite type
over `ℤ` and a finitely presented `R₀`-algebra `A₀` such that `A` is `R`-isomorphic to
`R ⊗[R₀] A₀`.

`R₀` is obtained by choosing a presentation for `A` and adjoining the finitely-many defining
coefficients of `A` to `R`. More generally we show, that `R ⊗[R₀] A₀` is `R`-isomorphic to `A`
whenever `R₀` contains all defining coefficients of `A`.

-/

universe u v w t

variable {R : Type u} [CommRing R]

section SetCoefficients

variable {σ : Type*}

/-- The set of coefficients of a set of multivariate polynomials. -/
def Set.coefficients (s : Set (MvPolynomial σ R)) : Set R :=
  Set.iUnion (ι := s) (fun (p : s) ↦ p.val.coefficients)

/-- The set of coefficients of a finite set of multivariate polynomials is finite. -/
theorem Set.coefficients_finite_of_finite (s : Set (MvPolynomial σ R)) (hf : Set.Finite s) :
    Set.Finite (s.coefficients) :=
  letI : Finite s := hf
  Set.finite_iUnion (fun p ↦ MvPolynomial.coefficients_finite p.val)

theorem Set.coefficients_subset_coefficients (s : Set (MvPolynomial σ R))
    (p : MvPolynomial σ R) (hS : p ∈ s) :
    p.coefficients ⊆ s.coefficients := fun r hr ↦ by
  simp only [Set.coefficients, Set.mem_iUnion]
  exact ⟨⟨p, hS⟩, hr⟩

section Map

variable {S : Type*} [CommRing S] [Algebra R S]
variable {f : R →+* S}

namespace MvPolynomial

/-- If the coefficients of `q : MvPolynomial σ S` are in the range of `f`, then `q` is in the
of `MvPolynomial.map f`. -/
theorem mem_range_of_coefficients (q : MvPolynomial σ S) (hc : q.coefficients ⊆ f.range) :
    q ∈ (MvPolynomial.map f).range := by
  have h (m : σ →₀ ℕ) : ∃ (r : R), f r = q.coeff m ∧ (q.coeff m = 0 → r = 0) := by
    by_cases h : m ∈ q.support
    · obtain ⟨r, hr⟩ := hc (MvPolynomial.coeff_mem_coefficients m h)
      exact ⟨r, by simp_all⟩
    · exact ⟨0, Eq.symm (by simpa using h), by simp⟩
  choose c hfc hcc using h
  let p : (σ →₀ ℕ) →₀ R := Finsupp.ofSupportFinite c <| by
    apply Set.Finite.subset (Finsupp.finite_support q) (fun m minc h ↦ ?_)
    exact minc (hcc m h)
  exact ⟨p, MvPolynomial.ext _ _ fun m ↦ MvPolynomial.coeff_map f p m ▸ hfc m⟩

theorem mem_range_of_coefficients' {R₀ : Subring R} (p : MvPolynomial σ R) (hc : p.coefficients ⊆ R₀) :
    p ∈ (MvPolynomial.map R₀.subtype).range := by
  apply mem_range_of_coefficients
  rw [R₀.range_subtype]
  exact hc

/-- If the coefficients of `q : MvPolynomial σ s` are in the range of `f`, choose a preimage of
`q` under `MvPolynomial.map f` using choice. -/
noncomputable def choosePreimageOfCoeffs (q : MvPolynomial σ S) (hc : q.coefficients ⊆ f.range) :
    MvPolynomial σ R :=
  (q.mem_range_of_coefficients hc).choose

@[simp]
lemma choosePreimageOfCoeffs_map (q : MvPolynomial σ S) (hc : q.coefficients ⊆ f.range) :
    MvPolynomial.map f (q.choosePreimageOfCoeffs hc) = q :=
  (q.mem_range_of_coefficients hc).choose_spec

noncomputable def Set.choosePreimageOfCoeffs (s : Set (MvPolynomial σ S))
    (hc : s.coefficients ⊆ f.range) (p : s) : MvPolynomial σ R :=
  MvPolynomial.choosePreimageOfCoeffs p.val
    ((s.coefficients_subset_coefficients p.val p.property).trans hc)

end MvPolynomial

end Map

end SetCoefficients

open TensorProduct

namespace Algebra

section

variable {S : Type*} [CommRing S] [Algebra R S]
variable {T : Type*} [CommRing T] [Algebra S T]
variable {T' : Type*} [CommRing T'] [Algebra R T']
variable {σ : Type*}
variable {I : Ideal (MvPolynomial σ R)}

variable [Algebra R T] [IsScalarTower R S T]

lemma baseChange_MvPolynomialQuot_ext {f g : S ⊗[R] (MvPolynomial σ R ⧸ I) →ₐ[S] T}
    (h : ∀ (i : σ), f (1 ⊗ₜ (Ideal.Quotient.mk I <| MvPolynomial.X i))
      = g (1 ⊗ₜ (Ideal.Quotient.mk I <| MvPolynomial.X i))) : f = g := by
  apply TensorProduct.ext (by ext)
  apply (AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective R I)).mp
  apply MvPolynomial.algHom_ext
  exact h

end

namespace RingOfDefinition

variable {S : Type v} [CommRing S] [Algebra R S]

section BaseChangeIso

/-!

In this section we construct an algebra isomorphism

`(MvPolynomial σ S ⧸ I) ≃ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ J)`

if the natural map `MvPolynomial σ R → MvPolynomial σ S` satisfies:

- `J` is contained in the preimage of `I`

-/

variable {σ : Type*}
variable (I : Ideal (MvPolynomial σ S)) (J : Ideal (MvPolynomial σ R))
variable (hJ : J ≤ Ideal.comap (MvPolynomial.map <| algebraMap R S) I)

noncomputable def baseChangeHom (hJ : J ≤ Ideal.comap (MvPolynomial.map <| algebraMap R S) I) :
    S ⊗[R] (MvPolynomial σ R ⧸ J) →ₐ[S] MvPolynomial σ S ⧸ I :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (let f : MvPolynomial σ R →ₐ[R] MvPolynomial σ S :=
       MvPolynomial.aeval MvPolynomial.X
     let g : MvPolynomial σ S →ₐ[R] MvPolynomial σ S ⧸ I :=
       Ideal.Quotient.mkₐ R I
     Ideal.Quotient.liftₐ _ (g.comp f) (fun x hx ↦ by
       simp only [AlgHom.comp_apply, ← RingHom.mem_ker]
       convert_to f x ∈ I
       · exact Ideal.Quotient.mkₐ_ker R I
       · exact (hJ hx)))
    (fun _ _ ↦ mul_comm _ _)

@[simp]
lemma baseChangeHom_mk_X (hJ : J ≤ Ideal.comap (MvPolynomial.map <| algebraMap R S) I) (i : σ) :
    (baseChangeHom I J hJ) (1 ⊗ₜ[R] (Ideal.Quotient.mk J) (MvPolynomial.X i))
      = Ideal.Quotient.mk I (MvPolynomial.X i) := by
  simp [baseChangeHom]

variable (T : Set (MvPolynomial σ S)) (hspan : I = Ideal.span T)
  (hcoeffs : T.coefficients ⊆ (algebraMap R S).range)

noncomputable def baseChangeInvAux : MvPolynomial σ S →ₐ[S] S ⊗[R] (MvPolynomial σ R) :=
  MvPolynomial.aeval (S₁ := S ⊗[R] (MvPolynomial σ R)) (fun i ↦ 1 ⊗ₜ MvPolynomial.X i)

@[simp]
lemma baseChangeInvAux_map (p : MvPolynomial σ R) :
    baseChangeInvAux (MvPolynomial.map (algebraMap R S) p) = 1 ⊗ₜ p := by
  simp [baseChangeInvAux]
  rw [MvPolynomial.aeval_map_algebraMap]
  let f : MvPolynomial σ R →ₐ[R] S ⊗[R] MvPolynomial σ R :=
    MvPolynomial.aeval fun i ↦ (1 : S) ⊗ₜ[R] MvPolynomial.X i
  let g : MvPolynomial σ R →ₐ[R] S ⊗[R] MvPolynomial σ R :=
    TensorProduct.includeRight
  change f p = g p
  congr
  simp [f, g]
  apply MvPolynomial.algHom_ext
  intro i
  simp [f, g]

@[simp]
lemma baseChangeInvAux_X (i : σ) :
    baseChangeInvAux (MvPolynomial.X i) = (1 : S) ⊗ₜ (MvPolynomial.X (R := R) i) := by
  simp [baseChangeInvAux]

noncomputable def baseChangeInvQuotAux : MvPolynomial σ S →ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ J) :=
  letI f : S ⊗[R] (MvPolynomial σ R) →ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ J) :=
    Algebra.TensorProduct.map (AlgHom.id S S) (Ideal.Quotient.mkₐ R J)
  AlgHom.comp f baseChangeInvAux

@[simp]
lemma baseChangeInvQuotAux_map (p : MvPolynomial σ R) :
    baseChangeInvQuotAux J (MvPolynomial.map (algebraMap R S) p) = 1 ⊗ₜ (Ideal.Quotient.mk J p) := by
  simp [baseChangeInvQuotAux, AlgHom.coe_comp, Function.comp_apply]

@[simp]
lemma baseChangeInvQuotAux_X (i : σ) :
    (baseChangeInvQuotAux J) (MvPolynomial.X i) = (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk J) (MvPolynomial.X i) := by
  simp [baseChangeInvQuotAux]

variable (hJl : (MvPolynomial.map (algebraMap R S)) ⁻¹' T ⊆ J)

lemma baseChangeInvQuotAux_vanish_of_generator (t : MvPolynomial σ S) (h : t ∈ T) :
    baseChangeInvQuotAux (R := R) J t = 0 := by
  have hc : MvPolynomial.coefficients t ⊆ Set.range (algebraMap R S) :=
    Set.Subset.trans (Set.coefficients_subset_coefficients T t h) hcoeffs
  obtain ⟨p, hp⟩ := MvPolynomial.mem_range_of_coefficients t hc
  rw [← hp, baseChangeInvQuotAux_map]
  have h1 : (Ideal.Quotient.mk J) p = 0 := by
    rw [← RingHom.mem_ker, Ideal.mk_ker]
    apply hJl
    change MvPolynomial.map (algebraMap R S) p ∈ T
    rwa [hp]
  rw [h1, tmul_zero]

noncomputable def baseChangeInv : MvPolynomial σ S ⧸ I →ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ J) := by
  fapply Ideal.Quotient.liftₐ
  · exact baseChangeInvQuotAux J
  · intro x hx
    subst hspan
    refine Submodule.span_induction hx ?_ ?_ ?_ ?_
    · intro x hxinT
      exact baseChangeInvQuotAux_vanish_of_generator J T hcoeffs hJl x hxinT
    · rw [AlgHom.map_zero]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
    · intro r x hx
      change (baseChangeInvQuotAux J) (r * x) = 0
      rw [AlgHom.map_mul, hx, mul_zero]

@[simp]
lemma baseChangeInv_mk_X (i : σ) :
    (baseChangeInv I J hJ T hspan hcoeffs hJl) ((Ideal.Quotient.mk I) (MvPolynomial.X i)) =
      1 ⊗ₜ (Ideal.Quotient.mk J (MvPolynomial.X i)) := by
  simp [baseChangeInv]

instance : IsScalarTower R S (S ⊗[R] (MvPolynomial σ R ⧸ J)) := by
  apply IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := S ⊗[R] (MvPolynomial σ R ⧸ J))
  ext x
  simp

noncomputable def baseChangeIso : (MvPolynomial σ S ⧸ I) ≃ₐ[S] S ⊗[R] (MvPolynomial σ R ⧸ J) :=
  AlgEquiv.ofAlgHom
    (baseChangeInv I J hJ T hspan hcoeffs hJl)
    (baseChangeHom I J hJ)
    (baseChange_MvPolynomialQuot_ext (fun i ↦ by simp))
    ((AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective S I)).mp
        (MvPolynomial.algHom_ext (fun i ↦ by simp)))

end BaseChangeIso

structure Model {σ : Type*} (I : Ideal (MvPolynomial σ R)) where
  s : Set (MvPolynomial σ R)
  hs : Ideal.span s = I
  R₀ : Subring R
  coeffs : s.coefficients ⊆ R₀

namespace Model

variable {σ : Type*} {I : Ideal (MvPolynomial σ R)} (M : Model I)

def mkOfGenerators (s : Set (MvPolynomial σ R)) (hs : Ideal.span s = I) : Model I where
  s := s
  hs := hs
  R₀ := Subalgebra.toSubring <| Algebra.adjoin ℤ s.coefficients
  coeffs := Algebra.subset_adjoin

theorem coefficients_subset (p : MvPolynomial σ R) (hp : p ∈ M.s) :
    p.coefficients ⊆ M.R₀ :=
  Set.Subset.trans (M.s.coefficients_subset_coefficients p hp) M.coeffs

theorem coefficients_subset_range : M.s.coefficients ⊆ (algebraMap M.R₀ R).range :=
  fun x hx ↦ ⟨⟨x, M.coeffs hx⟩, rfl⟩

def definingSet : Set (MvPolynomial σ M.R₀) :=
  (MvPolynomial.map (SubringClass.subtype M.R₀)) ⁻¹' M.s

def definingIdeal : Ideal (MvPolynomial σ M.R₀) :=
  Ideal.span M.definingSet

def model : Type _ :=
  MvPolynomial σ M.R₀ ⧸ Ideal.span M.definingSet

noncomputable instance : CommRing M.model :=
  inferInstanceAs <| CommRing <| MvPolynomial σ M.R₀ ⧸ Ideal.span M.definingSet

noncomputable instance : Algebra M.R₀ M.model :=
  inferInstanceAs <| Algebra M.R₀ <| MvPolynomial σ M.R₀ ⧸ Ideal.span M.definingSet

noncomputable def baseChangeIso : (MvPolynomial σ R ⧸ I) ≃ₐ[R] R ⊗[M.R₀] M.model := by
  refine RingOfDefinition.baseChangeIso I M.definingIdeal ?_ M.s M.hs.symm ?_ ?_
  · simp only [← M.hs]
    apply Ideal.span_preimage_le_comap_span
  · exact M.coefficients_subset_range
  · exact Ideal.subset_span

end Model

theorem exists_finiteType_model_of_finitePresentation [Algebra.FinitePresentation R S] :
    ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
      (_ : S ≃ₐ[R] R ⊗[R₀] S₀), Algebra.FiniteType ℤ R₀ := by
  obtain ⟨n, f, hf, ⟨s, hs⟩⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let M : Model (RingHom.ker f) := Model.mkOfGenerators s hs
  let i : S ≃ₐ[R] (MvPolynomial (Fin n) R ⧸ RingHom.ker f) :=
    (Ideal.quotientKerAlgEquivOfSurjective hf).symm
  refine ⟨M.R₀, M.model, inferInstance, inferInstance, i.trans M.baseChangeIso, ?_⟩
  apply FiniteType.of_adjoin_finite
  apply Set.coefficients_finite_of_finite
  exact Finset.finite_toSet s

theorem exists_noetherian_model_of_finitePresentation [Algebra.FinitePresentation R S] :
    ∃ (R₀ : Subring R) (S₀ : Type u) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
      (_ : S ≃ₐ[R] R ⊗[R₀] S₀), IsNoetherianRing R₀ := by
  obtain ⟨R₀, S₀, i1, i2, f, hf⟩ := exists_finiteType_model_of_finitePresentation (R := R) (S := S)
  exact ⟨R₀, S₀, i1, i2, f, FiniteType.isNoetherianRing ℤ R₀⟩

end RingOfDefinition
