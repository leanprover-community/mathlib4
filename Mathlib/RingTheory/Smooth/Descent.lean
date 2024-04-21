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
import Mathlib.RingTheory.RingOfDefinitionIdeal

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

section

variable {σ : Type*}

lemma MvPolynomial.empty_support_iff_degree_zero (m : σ →₀ ℕ) :
    MvPolynomial.degree m = 0 ↔ IsEmpty m.support := by
  simp_all [MvPolynomial.degree]

lemma MvPolynomial.nonempty_support_of_degree (m : σ →₀ ℕ) :
    0 < MvPolynomial.degree m ↔ Nonempty m.support := by
  constructor
  · intro h
    have : MvPolynomial.degree m ≠ 0 := by
      symm
      apply Nat.ne_of_lt
      exact h
    sorry
  · sorry

theorem MvPolynomial.IsHomogeneous.induction_on' {P : MvPolynomial σ R → Prop}
    (p : MvPolynomial σ R) {n : ℕ} (h : MvPolynomial.IsHomogeneous p n)
    (h1 : ∀ (u : σ →₀ ℕ) (hd : MvPolynomial.degree u = n) (a : R), P ((MvPolynomial.monomial u) a))
    (h2 : ∀ (p q : MvPolynomial σ R) (hp : MvPolynomial.IsHomogeneous p n)
      (hq : MvPolynomial.IsHomogeneous q n), P p → P q → P (p + q)) : P p :=
  sorry

#check MvPolynomial.IsHomogeneous.induction_on'

end

variable {S : Type v} [CommRing S] (f : R →+* S)
variable {A : Set R} {B : Set S} (hf : Set.MapsTo f A B)

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
  sorry

end

namespace Smooth

open Pointwise

lemma Ideal.span_pow (S : Set R) (n : ℕ) :
    Ideal.span S ^ n = Ideal.span (S ^ n) := by
  ext x
  constructor
  intro h
  sorry
  sorry
  --rw [Set.mem_pow (s := Ideal.span S) (a := x) (n := n)] at h

lemma Ideal.mem_span_asSum (S : Set R) (x : R) (h : x ∈ Ideal.span S) :
    ∃ (f : S →₀ R), x = Finsupp.sum f (fun s r ↦ r * s) := by
  sorry

lemma Ideal.mem_span_pow (S : Set R) (r : R) (n : ℕ) :
  r ∈ Ideal.span S ^ n ↔
    ∃ (c : Fin n → (S →₀ R)), True := sorry

lemma Ideal.mem_pow (I : Ideal R) (a b : R) {n m : ℕ} (ha : a ∈ I ^ n) (hb : b ∈ I ^ m) :
    a * b ∈ I ^ (n + m) :=
  sorry

lemma Set.mem_pow' (S : Set R) (a b : R) {n m : ℕ} (ha : a ∈ S ^ n) (hb : b ∈ S ^ m) :
    a * b ∈ S ^ (n + m) :=
  sorry

lemma Set.mem_span_monomial {n : ℕ} (S : Set R) :
    ∀ (u : S →₀ ℕ) (_ : MvPolynomial.degree u = n),
    Finsupp.prod u (fun n e ↦ (n : R) ^ e) ∈ S ^ n := by
  apply Nat.caseStrongInductionOn n
  · intro u h
    simp_all [MvPolynomial.degree, Finsupp.prod, h]
  · intro n ih u hdeg
    have : Nonempty u.support := by
      apply (MvPolynomial.nonempty_support_of_degree u).mp
      rw [hdeg]
      omega
    obtain ⟨⟨⟨s, hs⟩, hssup⟩⟩ := this
    rw [← Finsupp.mul_prod_erase (hyf := hssup)]
    let u' : S →₀ ℕ := Finsupp.erase ⟨s, hs⟩ u
    have hdegs : MvPolynomial.degree u = u ⟨s, hs⟩ + MvPolynomial.degree u' := by
      simp only [MvPolynomial.degree, u']
      change Finsupp.sum u (fun _ x ↦ x) = _ + Finsupp.sum _ (fun _ x ↦ x)
      rw [Finsupp.add_sum_erase u ⟨s, hs⟩ (fun _ x ↦ x) hssup]
    have hdeg' : MvPolynomial.degree u' ≤ n := by
      have : u ⟨s, hs⟩ ≠ 0 := by
        simp at hssup
        exact hssup
      omega
    have h1 : s ^ u ⟨s, hs⟩ ∈ S ^ (u ⟨s, hs⟩) := Set.pow_mem_pow hs _
    have h2 : Finsupp.prod u' (fun n e ↦ (n : R) ^ e) ∈ S ^ (MvPolynomial.degree u') := by
      apply ih
      exact hdeg'
      rfl
    simp only [← hdeg, hdegs]
    apply Set.mem_pow'
    exact h1
    exact h2

lemma Set.mem_span_monomial_one (S : Set R)
    (u : S →₀ ℕ) (h : MvPolynomial.degree u = 1) :
    Finsupp.prod u (fun n e ↦ (n : R) ^ e) ∈ S := by
  suffices h' : Finsupp.prod u (fun n e ↦ (n : R) ^ e) ∈ S ^ 1 by simp at h'; exact h'
  apply Set.mem_span_monomial
  exact h

lemma Ideal.mem_span' (S : Set R) (x : R) (hx : x ∈ Ideal.span S) : ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p 1 ∧ MvPolynomial.eval Subtype.val p = x := by
  refine Submodule.span_induction hx ?_ ?_ ?_ ?_
  · intro s hs
    exact ⟨MvPolynomial.X ⟨s, hs⟩, MvPolynomial.isHomogeneous_X _ _, by simp⟩
  · exact ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, by simp⟩
  · rintro x y ⟨px, hpxhom, rfl⟩ ⟨py, hpyhom, rfl⟩
    exact ⟨px + py, MvPolynomial.IsHomogeneous.add hpxhom hpyhom, by simp⟩
  · rintro a x ⟨px, hpxhom, rfl⟩
    exact ⟨MvPolynomial.C a * px, MvPolynomial.IsHomogeneous.C_mul hpxhom a, by simp⟩

lemma Ideal.mem_sq (I : Ideal R) (S : Set R) (hsp : I = Ideal.span S) (x : R) :
  x ∈ I ^ 2 ↔ ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p 2 ∧ MvPolynomial.eval Subtype.val p = x := sorry

lemma Ideal.mem_span_pow' {n : ℕ} (S : Set R) (x : R) :
    x ∈ (Ideal.span S) ^ n ↔ ∃ (p : MvPolynomial S R),
    MvPolynomial.IsHomogeneous p n ∧ MvPolynomial.eval Subtype.val p = x := by
  constructor
  · revert x
    apply Nat.caseStrongInductionOn n
    · intro x _
      exact ⟨MvPolynomial.C x, MvPolynomial.isHomogeneous_C _ _, by simp⟩
    · intro n ih x h
      refine Submodule.smul_induction_on h ?_ ?_
      · intro r hr t ht
        obtain ⟨pr, hprhom, rfl⟩ := ih n (by omega) r hr
        obtain ⟨pt, hpthom, rfl⟩ := Ideal.mem_span' R S t ht
        exact ⟨pr * pt, MvPolynomial.IsHomogeneous.mul hprhom hpthom, by simp⟩
      · rintro x y ⟨px, hpxhom, rfl⟩ ⟨py, hpyhom, rfl⟩
        exact ⟨px + py, MvPolynomial.IsHomogeneous.add hpxhom hpyhom, by simp⟩
  · rintro ⟨p, hp, rfl⟩
    rw [← p.sum_single, map_finsupp_sum, Finsupp.sum]
    apply sum_mem
    rintro c hc
    simp only [MvPolynomial.single_eq_monomial, MvPolynomial.eval_monomial]
    apply Ideal.mul_mem_left
    rw [← @hp c (by simpa using hc), MvPolynomial.weightedDegree_one,
      MvPolynomial.degree, ← Finset.prod_pow_eq_pow_sum, Finsupp.prod]
    apply Ideal.prod_mem_prod
    exact fun x _ ↦ Ideal.pow_mem_pow (Ideal.subset_span x.2) _

section

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

variable {ι : Type*} (f : MvPolynomial ι R →ₐ[R] A) (hfsurj : Function.Surjective f)
variable (S : Set (MvPolynomial ι R))

variable (σ : A →ₐ[R] MvPolynomial ι R ⧸ RingHom.ker f ^ 2)

local notation "I" => RingHom.ker f

noncomputable def hAux (i : ι) : MvPolynomial ι R :=
  (Quotient.exists_rep (σ (f (MvPolynomial.X i)))).choose

@[simp]
lemma hAux_eq (i : ι) : hAux f σ i = σ (f (MvPolynomial.X i : MvPolynomial ι R)) := by
  simp only [hAux]
  exact Exists.choose_spec (Quotient.exists_rep _)

noncomputable def sOfh : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval (fun j : ι => hAux f σ j)

lemma sigma_eq_mk_sOfh (p : MvPolynomial ι R) : σ (f p) = sOfh f σ p := by
  let u : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    σ.comp f
  let v : MvPolynomial ι R →ₐ[R] MvPolynomial ι R ⧸ I ^ 2 :=
    (Ideal.Quotient.mkₐ R (I ^ 2)).comp (sOfh f σ)
  suffices h : u = v by
    change u p = v p
    congr
  apply MvPolynomial.algHom_ext
  intro i
  simp [u, v, sOfh]

lemma sOfh_mem_sq (p : MvPolynomial ι R) (hp : p ∈ I) : sOfh f σ p ∈ I ^ 2 := by
  suffices h : f p = 0 by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← sigma_eq_mk_sOfh, h, map_zero]
  rwa [← RingHom.mem_ker]

lemma sOfh_exists_P (p : MvPolynomial ι R) (hp : p ∈ I) (hspan : Ideal.span S = I) :
    ∃ (P : MvPolynomial S (MvPolynomial ι R)),
        MvPolynomial.IsHomogeneous P 2 ∧ MvPolynomial.eval Subtype.val P = sOfh f σ p :=
  (Ideal.mem_sq _ I _ hspan.symm _).mp <| sOfh_mem_sq f σ p hp

variable (R₀ : Subring R) (hcoeffsS : MvPolynomial.Set.coefficients S ⊆ R₀)
  (hcoeffsH : MvPolynomial.Set.coefficients (Set.range <| hAux f σ) ⊆ R₀)

variable (P : S → MvPolynomial S (MvPolynomial ι R))
variable (hPhom : ∀ s : S, MvPolynomial.IsHomogeneous (P s) 2)
variable (hPeval : ∀ s : S, MvPolynomial.eval Subtype.val (P s) = sOfh f σ s)
variable (hcoeffsP : MvPolynomial.Set.coefficients (MvPolynomial.Set.coefficients (Set.range P)) ⊆ R₀)

noncomputable def hAux₀ (i : ι) : MvPolynomial ι R₀ := by
  apply RingOfDefinition.MvPolynomial.choosePreimageOfCoeffs (hAux f σ i)
  apply Set.Subset.trans
  · exact MvPolynomial.Set.coefficients_in (Set.range <| hAux f σ) (hAux f σ i) (Set.mem_range_self i)
  · intro r hr
    refine ⟨⟨r, ?_⟩, rfl⟩
    apply hcoeffsH
    exact hr

@[simp]
lemma hAux₀_map (i : ι) :
    (MvPolynomial.map (SubringClass.subtype R₀)) (hAux₀ f σ R₀ hcoeffsH i) = hAux f σ i := by
  simp only [hAux₀]
  change (MvPolynomial.map (algebraMap R₀ R)) _ = _
  simp

variable (I₀ : Ideal (MvPolynomial ι R₀)) (S₀ : Set (MvPolynomial ι R₀))
  (hspan₀ : Ideal.span S₀ = I₀)
  (hpreim₀ : MvPolynomial.map (SubringClass.subtype R₀) ⁻¹' S = S₀)

lemma I₀_in_preim_I (hspan : Ideal.span S = I) :
    I₀ ≤ Ideal.comap (MvPolynomial.map (SubringClass.subtype R₀)) (RingHom.ker f) := by
  intro x hx
  subst hspan₀ hpreim₀
  refine Submodule.span_induction hx ?_ ?_ ?_ ?_
  · intro s hs
    rw [← hspan]
    apply Ideal.subset_span
    exact hs
  · simp
  · intro x y hx hy
    exact Ideal.add_mem _ hx hy
  · intro a x hx
    exact Ideal.mul_mem_left _ a hx

lemma hAux_sub_X_in_I (i : ι) (hsig : AlgHom.comp (AlgHom.kerSquareLift f) σ = AlgHom.id R A) :
    hAux f σ i - MvPolynomial.X i ∈ I := by
  change hAux f σ i - MvPolynomial.X i ∈ RingHom.ker f
  rw [RingHom.mem_ker]
  simp
  have : f (MvPolynomial.X i) = AlgHom.id R A (f (MvPolynomial.X i)) := rfl
  rw [this, ← hsig]
  simp
  erw [← hAux_eq]
  erw [Ideal.Quotient.lift_mk]
  simp

lemma hAux_sub_X_ex_rep (hspan : Ideal.span S = I) (i : ι)
    (hsig : AlgHom.comp (AlgHom.kerSquareLift f) σ = AlgHom.id R A) :
    ∃ (p : MvPolynomial S (MvPolynomial ι R)),
    MvPolynomial.IsHomogeneous p 1 ∧
    MvPolynomial.eval Subtype.val p = hAux f σ i - MvPolynomial.X i := by
  rw [← Ideal.mem_span]
  apply hAux_sub_X_in_I
  exact hsig
  exact hspan.symm

noncomputable def hAuxSubXRep (hspan : Ideal.span S = I) (i : ι)
    (hsig : AlgHom.comp (AlgHom.kerSquareLift f) σ = AlgHom.id R A) :
    MvPolynomial S (MvPolynomial ι R) :=
  (hAux_sub_X_ex_rep f S σ hspan i hsig).choose

@[simp]
lemma hAuxSubXRep_eval (hspan : Ideal.span S = I) (i : ι)
    (hsig : AlgHom.comp (AlgHom.kerSquareLift f) σ = AlgHom.id R A) :
    (MvPolynomial.eval Subtype.val) (hAuxSubXRep f S σ hspan i hsig) = hAux f σ i - MvPolynomial.X i :=
  (hAux_sub_X_ex_rep f S σ hspan i hsig).choose_spec.right

lemma hAuxSubXRep_homog (hspan : Ideal.span S = I) (i : ι)
    (hsig : AlgHom.comp (AlgHom.kerSquareLift f) σ = AlgHom.id R A) :
    MvPolynomial.IsHomogeneous (hAuxSubXRep f S σ hspan i hsig) 1 :=
  (hAux_sub_X_ex_rep f S σ hspan i hsig).choose_spec.left

lemma hAux₀_sub_X_in_I (i : ι) (hsig : AlgHom.comp (AlgHom.kerSquareLift f) σ = AlgHom.id R A) :
    MvPolynomial.map (SubringClass.subtype R₀) (hAux₀ f σ R₀ hcoeffsH i - MvPolynomial.X i) ∈ I := by
  simp only [map_sub, hAux₀_map, MvPolynomial.map_X]
  apply hAux_sub_X_in_I
  exact hsig

@[simp]
lemma hAux₀_mod (hspan : Ideal.span S = I)
    (i : ι) (hsig : AlgHom.comp (AlgHom.kerSquareLift f) σ = AlgHom.id R A)
    (hcoeffsQ : MvPolynomial.Set.coefficients (MvPolynomial.coefficients (hAuxSubXRep f S σ hspan i hsig)) ⊆ R₀) :
    Ideal.Quotient.mk I₀ (hAux₀ f σ R₀ hcoeffsH i) = Ideal.Quotient.mk I₀ (MvPolynomial.X i) := by
  rw [Ideal.Quotient.eq]
  let Q : MvPolynomial S (MvPolynomial ι R) := hAuxSubXRep f S σ hspan i hsig
  have hres : Set.MapsTo (MvPolynomial.map (SubringClass.subtype R₀)) S₀ S := by
    subst hpreim₀
    apply Set.mapsTo_preimage
  have hcQ :
      MvPolynomial.Set.coefficients (MvPolynomial.coefficients Q) ⊆ Set.range (SubringClass.subtype R₀) := by
    erw [Subtype.range_val]
    exact hcoeffsQ
  have h2 : MvPolynomial.Set.coefficients S ⊆ Set.range (SubringClass.subtype R₀) := by
    erw [Subtype.range_val]
    exact hcoeffsS
  let Q₀ : MvPolynomial S₀ (MvPolynomial ι R₀) :=
    RingOfDefinition.setMapRepr hres Q hcQ h2 hpreim₀ Subtype.val_injective
  have homog : MvPolynomial.IsHomogeneous Q₀ 1 := by
    apply RingOfDefinition.setMapRepr_homog hres Q hcQ h2 hpreim₀ Subtype.val_injective
    apply hAuxSubXRep_homog f S σ hspan i hsig
  rw [Ideal.mem_span (hsp := hspan₀.symm)]
  refine ⟨Q₀, homog, ?_⟩
  apply MvPolynomial.map_injective (SubringClass.subtype R₀) (Subtype.val_injective)
  simp [Q₀, Q]

noncomputable def sOfh₀ : MvPolynomial ι R₀ →ₐ[R₀] MvPolynomial ι R₀ :=
  MvPolynomial.aeval (fun j : ι => hAux₀ f σ R₀ hcoeffsH j)

@[simp]
lemma incl_sOfh₀ (p : MvPolynomial ι R₀) :
    (MvPolynomial.map (SubringClass.subtype R₀)) ((sOfh₀ f σ R₀ hcoeffsH) p)
    = sOfh f σ (MvPolynomial.map (SubringClass.subtype R₀) p) := by
  change ((MvPolynomial.map (SubringClass.subtype R₀)).comp (sOfh₀ f σ R₀ hcoeffsH)) p
    = ((sOfh f σ).toRingHom.comp (MvPolynomial.map (SubringClass.subtype R₀))) p
  have : (MvPolynomial.map (SubringClass.subtype R₀)).comp (sOfh₀ f σ R₀ hcoeffsH)
    = (sOfh f σ).toRingHom.comp (MvPolynomial.map (SubringClass.subtype R₀)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp [sOfh₀, sOfh]
  rw [this]

variable (hspan : Ideal.span S = I)

lemma exists_PAux₀ (s : MvPolynomial ι R₀) (hs : s ∈ S₀) :
    ∃ (P₀ : MvPolynomial S₀ (MvPolynomial ι R₀)),
      MvPolynomial.IsHomogeneous P₀ 2 ∧
      MvPolynomial.eval Subtype.val P₀ = sOfh₀ f σ R₀ hcoeffsH s := by
  let p : MvPolynomial ι R := MvPolynomial.map (SubringClass.subtype R₀) s
  have hp : p ∈ S := by
    rw [← hpreim₀] at hs
    exact hs
  let Ps : MvPolynomial S (MvPolynomial ι R) := P ⟨p, hp⟩
  have hPshomog : MvPolynomial.IsHomogeneous Ps 2 := hPhom ⟨p, hp⟩
  have hc : MvPolynomial.coefficients Ps ⊆ Set.range (MvPolynomial.map (SubringClass.subtype R₀)) := by
    intro r hr
    have h1 : Ps ∈ Set.range P := Set.mem_range_self _
    have h2 : MvPolynomial.coefficients Ps ⊆ MvPolynomial.Set.coefficients (Set.range P) :=
      MvPolynomial.Set.coefficients_in (Set.range P) Ps h1
    have h3' : MvPolynomial.coefficients r ⊆ R₀ := by
      apply Set.Subset.trans ?_ hcoeffsP
      apply MvPolynomial.Set.coefficients_in
      apply h2
      exact hr
    have h3 : MvPolynomial.coefficients r ⊆ Set.range (SubringClass.subtype R₀) := by
      intro x hx
      use ⟨x, h3' hx⟩
      rfl
    exact RingOfDefinition.exists_preimage_of_coefficients' (SubringClass.subtype R₀) r h3
  obtain ⟨P', hP'⟩ := RingOfDefinition.exists_preimage_of_coefficients'
    (MvPolynomial.map (SubringClass.subtype R₀))
    Ps hc
  --have hP'homog : MvPolynomial.IsHomogeneous P' 2 := by
  --  refine MvPolynomial.isHomogeneous_of_map (MvPolynomial.map (SubringClass.subtype R₀)) ?_ P' ?_
  --  · apply MvPolynomial.map_injective
  --    exact Subtype.val_injective
  --  · rw [hP']
  --    exact hPshomog
  have hinj : Function.Injective
      (MvPolynomial.map (SubringClass.subtype R₀) : MvPolynomial ι R₀ →+* MvPolynomial ι R) := by
    apply MvPolynomial.map_injective
    exact Subtype.val_injective
  have hres : Set.MapsTo (MvPolynomial.map (SubringClass.subtype R₀)) S₀ S := by
    rw [← hpreim₀]
    apply Set.mapsTo_preimage
  have hresinj : Function.Injective hres.restrict := by
    rw [Set.MapsTo.restrict_inj]
    apply Set.injOn_of_injective
    exact hinj
  have hressurj : Function.Surjective hres.restrict := by
    intro ⟨p, hp⟩
    have : MvPolynomial.coefficients p ⊆ Set.range (SubringClass.subtype R₀) := by
      intro r hr
      have h1 := MvPolynomial.Set.coefficients_in S p hp hr
      have h2 := hcoeffsS h1
      use ⟨r, h2⟩
      rfl
    obtain ⟨p', hp'⟩ :=
      RingOfDefinition.exists_preimage_of_coefficients' (SubringClass.subtype R₀)
      p
      this
    have : p' ∈ S₀ := by
      rw [← hpreim₀]
      change (MvPolynomial.map (SubringClass.subtype R₀)) p' ∈ S
      rw [hp']
      exact hp
    use ⟨p', this⟩
    apply Subtype.ext
    simpa
  let g : S₀ ≃ S := Equiv.ofBijective hres.restrict ⟨hresinj, hressurj⟩
  let P₀ : MvPolynomial S₀ (MvPolynomial ι R₀) :=
    MvPolynomial.rename g.symm P'
  have hrenP₀ : (MvPolynomial.rename hres.restrict) P₀ = P' := by
    simp only [MvPolynomial.rename_rename, P₀]
    change MvPolynomial.rename (g ∘ g.symm) P' = P'
    simp
  refine ⟨P₀, ?_, ?_⟩
  · rw [MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff]
    refine MvPolynomial.isHomogeneous_of_map (MvPolynomial.map (SubringClass.subtype R₀)) ?_ P' ?_
    · apply MvPolynomial.map_injective
      exact Subtype.val_injective
    · rw [hP']
      exact hPshomog
    · exact Equiv.injective g.symm
  · apply hinj
    rw [diag_rename_comm_apply _ hres, hrenP₀, hP']
    simp
    exact hPeval ⟨p, hp⟩

lemma hAux₀_eval (a : MvPolynomial ι R₀) (ha : a ∈ I₀):
    MvPolynomial.aeval (hAux₀ f σ R₀ hcoeffsH) a ∈ I₀ ^ 2 := by
  rw [← hspan₀] at ha
  refine Submodule.span_induction ha ?_ ?_ ?_ ?_
  · intro s hs
    rw [Ideal.mem_sq]
    exact exists_PAux₀ f S σ R₀ hcoeffsS hcoeffsH P hPhom hPeval hcoeffsP S₀ hpreim₀ hspan s hs
    exact S₀
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

/-- https://stacks.math.columbia.edu/tag/00TP -/
theorem descent : ∃ (R₀ : Subring R) (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra R₀ A₀)
    (_ : A ≃ₐ[R] R ⊗[R₀] A₀),
    FiniteType ℤ R₀ ∧ FinitePresentation R₀ A₀ ∧ FormallySmooth R₀ A₀ := by
  obtain ⟨ι, hfin, f, hfsurj, S, hS⟩ := FinitePresentation.iff_quotient_mvPolynomial'.mp hfp
  obtain ⟨σ, hsig⟩ := (FormallySmooth.iff_split_surjection f hfsurj).mp inferInstance
  let coeffs_s : Set R := MvPolynomial.Set.coefficients (S : Set (MvPolynomial ι R))
  let coeffs_h : Set R := MvPolynomial.Set.coefficients (Set.range <| hAux f σ)
  have (s : S) : ∃ (p : MvPolynomial S (MvPolynomial ι R)),
      MvPolynomial.IsHomogeneous p 2 ∧ MvPolynomial.eval Subtype.val p = sOfh f σ s := by
    apply sOfh_exists_P f S σ
    · erw [← hS]
      apply Ideal.subset_span
      exact s.property
    · exact hS
  choose p _ _ using this
  let coeffs_p : Set R := MvPolynomial.Set.coefficients <|
    MvPolynomial.Set.coefficients (Set.range p)
  let coeffs_q : Set R := Set.iUnion
    (fun (i : ι) ↦ MvPolynomial.Set.coefficients (MvPolynomial.coefficients (hAuxSubXRep f S σ hS i hsig)))
  let coeffs : Set R := coeffs_s ∪ coeffs_h ∪ coeffs_p ∪ coeffs_q
  let R₀ := (Algebra.adjoin ℤ coeffs).toSubring
  have hcoeffsS : MvPolynomial.Set.coefficients (S : Set (MvPolynomial ι R)) ⊆ R₀ := by
    apply Set.Subset.trans ?_ Algebra.subset_adjoin
    apply Set.Subset.trans ?_ (Set.subset_union_left _ _)
    apply Set.Subset.trans ?_ (Set.subset_union_left _ _)
    apply Set.subset_union_left
  have hcoeffsQ (i : ι) :
      MvPolynomial.Set.coefficients (MvPolynomial.coefficients (hAuxSubXRep f S σ hS i hsig)) ⊆ R₀ := by
    apply Set.Subset.trans ?_ Algebra.subset_adjoin
    apply Set.Subset.trans ?_ (Set.subset_union_right _ coeffs_q)
    apply Set.subset_iUnion _ i
  have hcoeffsH : MvPolynomial.Set.coefficients (Set.range (hAux f σ)) ⊆ R₀ := by
    apply Set.Subset.trans
    exact Set.subset_union_right coeffs_s coeffs_h
    apply Set.Subset.trans
    exact Set.subset_union_left _ coeffs_p
    apply Set.Subset.trans
    exact Set.subset_union_left _ coeffs_q
    exact Algebra.subset_adjoin
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
    · erw [Subtype.range_val]
      exact hcoeffsS
    · intro p hp
      exact Ideal.subset_span hp
  let is : (MvPolynomial ι R ⧸ (RingHom.ker f.toRingHom)) ≃ₐ[R] A :=
    Ideal.quotientKerAlgEquivOfSurjective hfsurj
  let g : A ≃ₐ[R] R ⊗[R₀] A₀ := is.symm.trans f'
  use g
  refine ⟨?_, ?_, ?_⟩
  · apply finiteType_of_adjoin_finite
    apply Set.Finite.union
    apply Set.Finite.union
    apply Set.Finite.union
    · apply MvPolynomial.Set.coefficients_finite_of_finite
      exact Finset.finite_toSet S
    · apply MvPolynomial.Set.coefficients_finite_of_finite
      exact Set.finite_range (hAux f σ)
    · apply MvPolynomial.Set.coefficients_finite_of_finite
      apply MvPolynomial.Set.coefficients_finite_of_finite
      exact Set.finite_range p
    · apply Set.finite_iUnion
      intro i
      apply MvPolynomial.Set.coefficients_finite_of_finite
      apply MvPolynomial.coefficients_finite
  · apply FinitePresentation.quotient
    obtain ⟨S₀', hS₀'⟩ := Set.Finite.exists_finset_coe hS₀fin
    use S₀'
    rw [hS₀']
    --exact FinitePresentation.mvPolynomial R₀ ι
  · fapply FormallySmooth.of_split (Ideal.Quotient.mkₐ R₀ I₀)
    · fapply Ideal.Quotient.liftₐ I₀
      · apply AlgHom.comp (Ideal.Quotient.mkₐ R₀ (RingHom.ker (Ideal.Quotient.mkₐ (↥R₀) I₀).toRingHom ^ 2))
        refine MvPolynomial.aeval (hAux₀ f σ R₀ ?_)
        exact hcoeffsH
      · intro a ha
        simp only [AlgHom.comp_apply, ← RingHom.mem_ker]
        erw [Ideal.Quotient.mkₐ_ker R₀ (RingHom.ker (Ideal.Quotient.mkₐ (↥R₀) I₀).toRingHom ^ 2)]
        erw [Ideal.Quotient.mkₐ_ker R₀]
        fapply hAux₀_eval
        exact S₀
        rfl
        exact ha
    · apply AlgHom.cancel_surjective (Ideal.Quotient.mkₐ R₀ I₀)
      · exact Ideal.Quotient.mkₐ_surjective R₀ I₀
      · apply MvPolynomial.algHom_ext
        intro i
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_comp, Function.comp_apply, AlgHom.id_comp]
        erw [Ideal.Quotient.lift_mk]
        simp
        fapply hAux₀_mod f S σ R₀
        · exact hcoeffsS
        · exact S₀
        · rfl
        · rfl
        · exact hS
        · exact hsig
        · exact hcoeffsQ i

end Smooth
