/-
Copyright (c) 2022 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Tower

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

open TensorProduct

namespace Algebra

variable {R : Type u} [CommRing R] {ι : Type v}

def MvPolynomial.coefficients (p : MvPolynomial ι R) : Set R := (p.coeff '' p.support)

lemma MvPolynomial.coefficients_mem {p : MvPolynomial ι R} (m : ι →₀ ℕ) (h : m ∈ MvPolynomial.support p) :
    p.coeff m ∈ MvPolynomial.coefficients p :=
  Set.mem_image_of_mem p.coeff h

def MvPolynomial.Set.coefficients (S : Set (MvPolynomial ι R)) : Set R :=
  Set.iUnion (ι := S) (fun (p : S) ↦ p.val.coeff '' p.val.support)

instance (p : MvPolynomial ι R) : Set.Finite (MvPolynomial.coefficients p) := by
  apply Set.Finite.image
  change Set.Finite (Finsupp.support p)
  rw [← Finsupp.fun_support_eq]
  exact Finsupp.finite_support p

lemma MvPolynomial.Set.coefficients_in (S : Set (MvPolynomial ι R))
    (p : MvPolynomial ι R) (hS : p ∈ S) :
    (MvPolynomial.coefficients p) ⊆ MvPolynomial.Set.coefficients S := by
  intro r hr
  obtain ⟨m, hms, hmeq⟩ := hr
  simp only [MvPolynomial.Set.coefficients, Set.mem_iUnion]
  use ⟨p, hS⟩
  use m

variable {S : Type w} [CommRing S] [Algebra R S]
  {T : Type t} [CommRing T] [Algebra R T]
  {T' : Type t} [CommRing T'] [Algebra R T']

lemma AlgHom.cancel_surjective {f g : T →ₐ[R] S} (p : T' →ₐ[R] T) (hf : Function.Surjective p)
    (heq : f.comp p = g.comp p) : f = g := by
  ext x
  obtain ⟨t', rfl⟩ := hf x
  change (f.comp p) t' = (g.comp p) t'
  rw [heq]

section

variable {S : Type w} [CommRing S] [Algebra R S]

section

variable {T : Type t} [CommRing T] [Algebra S T] {T' : Type v} [CommRing T'] [Algebra R T']
variable (I : Ideal (MvPolynomial ι R))

lemma foo_ext0 (f g : S ⊗[R] T' →ₐ[S] T)
    (h : ∀ (t' : T'), f (1 ⊗ₜ t') = g (1 ⊗ₜ t')) : f = g := by
  ext x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro s p
    convert_to f ((s • 1) ⊗ₜ[R] p) = g ((s • 1) ⊗ₜ[R] p)
    · simp
    · simp
    · simp only [← TensorProduct.smul_tmul', AlgHom.map_smul]
      rw [h]
  · intro x y hx hy
    simp [hx, hy]

variable [Algebra R T] [IsScalarTower R S T]

lemma foo_ext {f g : S ⊗[R] (MvPolynomial ι R ⧸ I) →ₐ[S] T}
    (h : ∀ (i : ι), f (1 ⊗ₜ (Ideal.Quotient.mk I <| MvPolynomial.X i))
      = g (1 ⊗ₜ (Ideal.Quotient.mk I <| MvPolynomial.X i))) : f = g := by
  apply TensorProduct.ext (by ext)
  apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ R I)
  · exact Ideal.Quotient.mkₐ_surjective R I
  · apply MvPolynomial.algHom_ext
    exact h

end

variable (I : Ideal (MvPolynomial ι S))

noncomputable abbrev bar : Ideal (MvPolynomial ι R) := Ideal.comap (MvPolynomial.aeval MvPolynomial.X) I

local notation "I₀" => bar I

noncomputable def foo : S ⊗[R] (MvPolynomial ι R ⧸ I₀) →ₐ[S] MvPolynomial ι S ⧸ I := by
  fapply Algebra.TensorProduct.lift
  · exact Algebra.ofId _ _
  · let f : MvPolynomial ι R →ₐ[R] MvPolynomial ι S :=
      MvPolynomial.aeval MvPolynomial.X
    let g : MvPolynomial ι S →ₐ[R] MvPolynomial ι S ⧸ I :=
      Ideal.Quotient.mkₐ R I
    fapply Ideal.Quotient.liftₐ
    exact g.comp f
    intro x hx
    simp only [AlgHom.comp_apply]
    rw [← RingHom.mem_ker]
    change f x ∈ RingHom.ker (Ideal.Quotient.mkₐ R I)
    erw [Ideal.Quotient.mkₐ_ker R I]
    exact hx
  · intro s p
    apply mul_comm

@[simp]
lemma foo_mk (i : ι) :
    (foo (R := R) I) (1 ⊗ₜ[R] (Ideal.Quotient.mk I₀) (MvPolynomial.X i))
      = Ideal.Quotient.mk I (MvPolynomial.X i) := by
  simp [foo]

lemma fooz_aux2 (t : MvPolynomial ι S)
    (hc : MvPolynomial.coefficients t ⊆ Set.range (algebraMap R S)) :
    ∃ (p : MvPolynomial ι R), MvPolynomial.map (algebraMap R S) p = t := by
  have (m : ι →₀ ℕ) : ∃ (r : R), algebraMap R S r = t.coeff m ∧ (t.coeff m = 0 → r = 0) := by
    by_cases h : m ∈ t.support
    · obtain ⟨r, hr⟩ := hc (MvPolynomial.coefficients_mem m h)
      use r
      simp_all
    · simp at h
      use 0
      simp only [map_zero, implies_true, and_true]
      exact h.symm
  choose c h1 h2 using this
  let p : (ι →₀ ℕ) →₀ R := Finsupp.ofSupportFinite c <| by
    apply Set.Finite.subset
    · exact Finsupp.finite_support t
    · intro m minc h
      exact minc (h2 m h)
  use p
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_map]
  exact h1 m

variable (T : Set (MvPolynomial ι S)) (hgen : I = Ideal.span T)
  (hcoeffs : (MvPolynomial.Set.coefficients T) ⊆ (Set.range <| algebraMap R S))

noncomputable def barz : MvPolynomial ι S →ₐ[S] S ⊗[R] (MvPolynomial ι R) := by
  fapply MvPolynomial.aeval (S₁ := S ⊗[R] (MvPolynomial ι R))
  intro i
  exact 1 ⊗ₜ MvPolynomial.X i

lemma barz_aux (p : MvPolynomial ι R) :
    barz (MvPolynomial.map (algebraMap R S) p) = 1 ⊗ₜ p := by
  simp [barz]
  rw [MvPolynomial.aeval_map_algebraMap]
  let f : MvPolynomial ι R →ₐ[R] S ⊗[R] MvPolynomial ι R :=
    MvPolynomial.aeval fun i ↦ (1 : S) ⊗ₜ[R] MvPolynomial.X i
  let g : MvPolynomial ι R →ₐ[R] S ⊗[R] MvPolynomial ι R :=
    TensorProduct.includeRight
  change f p = g p
  congr
  simp [f, g]
  apply MvPolynomial.algHom_ext
  intro i
  simp [f, g]

noncomputable def barzQuot : MvPolynomial ι S →ₐ[S] S ⊗[R] (MvPolynomial ι R ⧸ I₀) :=
  letI f : S ⊗[R] (MvPolynomial ι R) →ₐ[S] S ⊗[R] (MvPolynomial ι R ⧸ I₀) :=
    Algebra.TensorProduct.map (AlgHom.id S S) (Ideal.Quotient.mkₐ R I₀)
  AlgHom.comp f barz

lemma barzQuot_aux (p : MvPolynomial ι R) :
    barzQuot (R := R) I
      (MvPolynomial.map (algebraMap R S) p) = 1 ⊗ₜ (Ideal.Quotient.mk I₀ p) := by
  simp [barzQuot, AlgHom.coe_comp, Function.comp_apply, barz_aux p]

lemma barzQuot_aux2 (t : MvPolynomial ι S) (h : t ∈ I)
    (hc : MvPolynomial.coefficients t ⊆ Set.range (algebraMap R S)) :
    barzQuot (R := R) I t = 0 := by
  obtain ⟨p, hp⟩ := fooz_aux2 t hc
  rw [← hp, barzQuot_aux]
  have h1 : (Ideal.Quotient.mk I₀) p = 0 := by
    rw [← RingHom.mem_ker, Ideal.mk_ker]
    change MvPolynomial.map (algebraMap R S) p ∈ I
    rwa [hp]
  rw [h1, tmul_zero]

set_option synthInstance.maxHeartbeats 30000

noncomputable def fooz : MvPolynomial ι S ⧸ I →ₐ[S] S ⊗[R] (MvPolynomial ι R ⧸ I₀) := by
  fapply Ideal.Quotient.liftₐ
  · exact barzQuot I
  · intro x hx
    subst hgen
    refine Submodule.span_induction hx ?_ ?_ ?_ ?_
    · intro x hxinT
      apply barzQuot_aux2
      exact Ideal.subset_span hxinT
      exact Set.Subset.trans (MvPolynomial.Set.coefficients_in T x hxinT) hcoeffs
    · rw [AlgHom.map_zero]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
    · intro r x hx
      change (barzQuot (R := R) (Ideal.span T)) (r * x) = 0
      rw [AlgHom.map_mul, hx, mul_zero]

@[simp]
lemma fooz_mk' (i : ι) :
    (fooz I T hgen hcoeffs) ((Ideal.Quotient.mk I) (MvPolynomial.X i)) =
      1 ⊗ₜ (Ideal.Quotient.mk I₀ (MvPolynomial.X i)) := by
  simp [fooz, barzQuot, barz]

instance : IsScalarTower R S (S ⊗[R] (MvPolynomial ι R ⧸ I₀)) := by
  apply IsScalarTower.of_algebraMap_eq' (R := R) (S := S) (A := S ⊗[R] (MvPolynomial ι R ⧸ I₀))
  ext x
  simp

noncomputable def baseChangeIso : (MvPolynomial ι S ⧸ I) ≃ₐ[S] S ⊗[R] (MvPolynomial ι R ⧸ I₀) := by
  fapply AlgEquiv.ofAlgHom
  · exact fooz I T hgen hcoeffs
  · exact foo I
  · apply foo_ext
    intro i
    simp
  · apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ S I)
    exact Ideal.Quotient.mkₐ_surjective S I
    apply MvPolynomial.algHom_ext
    intro i
    simp

end

variable (I : Ideal (MvPolynomial ι R)) (S : Set (MvPolynomial ι R))
  (hgenS : Ideal.span S = I) (hf : Set.Finite S)

def RingOfDefinition : Subring R :=
  Subalgebra.toSubring (Algebra.adjoin ℤ (MvPolynomial.Set.coefficients S))

local notation "R₀" => RingOfDefinition S

local notation "A" => MvPolynomial ι R ⧸ I

def RingOfDefinition.Set : Set (MvPolynomial ι R₀) :=
  MvPolynomial.map (SubringClass.subtype R₀) ⁻¹' S

local notation "S₀" => RingOfDefinition.Set S

local notation "I₀" => Ideal.span S₀

local notation "A₀" => MvPolynomial ι R₀ ⧸ I₀

--noncomputable local instance : Algebra R₀ A₀ := Ideal.Quotient.algebra R₀
noncomputable local instance : Module R₀ A₀ := Algebra.toModule

def baseChange : R ⊗[R₀] A₀ ≃ₐ[R] A := sorry
