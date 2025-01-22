import Mathlib

section

variable {ι N : Type*} [Preorder ι] {M : ι → Type*}
  (g : ∀ ⦃i j⦄, i ≤ j → M i → M j) (f : ∀ i, M i → N)

structure IsDirectLimit [DirectedSystem M g] : Prop where
  naturality {i j : ι} (hij : i ≤ j) (x : M i) : f j (g hij x) = f i x
  jointly_surjective (x : N) : ∃ i y, f i y = x
  exists_of_eq {i j : ι} (x : M i) (y : M j) (heq : f i x = f j y) :
    ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), g hik x = g hjk y

namespace IsDirectLimit

variable {f g}
variable [DirectedSystem M g] (h : IsDirectLimit g f)

include h

lemma eq_iff_exists {i j : ι} {x : M i} {y : M j} :
    f i x = f j y ↔ ∃ (k : ι) (hik : i ≤ k) (hjk : j ≤ k), g hik x = g hjk y := by
  refine ⟨fun heq ↦ h.exists_of_eq x y heq, ?_⟩
  rintro ⟨k, hik, hjk, heq⟩
  rw [← h.naturality hik, ← h.naturality hjk, heq]

end IsDirectLimit

end

section

open Algebra MvPolynomial

universe t₁ t₂

variable {R : Type*} [CommRing R]

lemma aeval_mk_X_eq_mk {σ : Type*} (I : Ideal (MvPolynomial σ R)) :
    aeval (fun i ↦ Ideal.Quotient.mk I (X i)) = Ideal.Quotient.mkₐ _ I := by
  rw [aeval_unique (Ideal.Quotient.mkₐ _ I)]
  rfl

noncomputable
def Algebra.Generators.naive {σ : Type t₁} {ι : Type t₂} (v : ι → MvPolynomial σ R) :
    Generators.{t₁} R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) where
  vars := σ
  val i := Ideal.Quotient.mk _ (X i)
  σ' := Quotient.out
  aeval_val_σ' x := by
    rw [aeval_mk_X_eq_mk]
    apply Quotient.out_eq

lemma Generators.naive_val {σ ι : Type*} (v : ι → MvPolynomial σ R) (i : σ) :
    (Generators.naive v).val i = Ideal.Quotient.mk _ (X i) :=
  rfl

noncomputable
def Presentation.naive {σ : Type t₁} {ι : Type t₂} (v : ι → MvPolynomial σ R) :
    Presentation.{t₂, t₁} R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) where
  __ := Generators.naive v
  rels := ι
  relation := v
  span_range_relation_eq_ker := by
    show Ideal.span _ = RingHom.ker (aeval <| fun i ↦ Ideal.Quotient.mk _ (X i)).toRingHom
    simp only [AlgHom.toRingHom_eq_coe, aeval_mk_X_eq_mk, Ideal.Quotient.mkₐ_ker]

end

universe u

variable {ι A₀ : Type*} [Preorder ι] (Aᵢ : ι → Type u) [CommRing A₀]
    [∀ i, CommRing (Aᵢ i)] [∀ i, Algebra A₀ (Aᵢ i)]

open TensorProduct

lemma Ideal.FG.exists_fun {R : Type*} [Semiring R] {I : Ideal R} (hI : I.FG) :
    ∃ (n : ℕ) (f : Fin n → R), I = Ideal.span (Set.range f) := sorry

noncomputable
def Algebra.Presentation.congr {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (PA : Presentation R A) (PB : Presentation R B)
    (e : PA.vars ≃ PB.vars)
    (f : PA.rels ≃ PB.rels) (hef : ∀ r, PB.relation (f r) = (PA.relation r).rename e) :
    A ≃ₐ[R] B := by
  refine ((PA.quotientEquiv.symm.restrictScalars R).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv _ e) ?_)).trans
    (PB.quotientEquiv.restrictScalars R)
  rw [← PB.span_range_relation_eq_ker, ← PA.span_range_relation_eq_ker]
  rw [Ideal.map_span, ← Set.range_comp]
  rw [← Set.image_univ, ← Set.range_eq_univ.mpr f.surjective]
  rw [← Set.range_comp]
  have : PB.relation ∘ ⇑f = (MvPolynomial.renameEquiv R e) ∘ PA.relation := by
    ext : 1
    exact hef _
  rw [this]
  congr

open MvPolynomial

lemma MvPolynomial.mem_range_map_iff {R S σ : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial σ S} {f : R →+* S} :
    p ∈ (MvPolynomial.map f).range ↔ ∀ m, p.coeff m ∈ f.range := by
  refine ⟨?_, ?_⟩
  · rintro ⟨q, rfl⟩ m
    rw [coeff_map]
    simp
  · intro hm
    choose c hc using hm
    rw [← MvPolynomial.support_sum_monomial_coeff p]
    simp_rw [← hc]
    apply sum_mem
    intro m hm
    use monomial m (c m)
    simp

lemma exists_lift_of_isDirected [Nonempty ι] {A : Type*} [CommRing A] [Algebra A₀ A]
      (f : ∀ i, Aᵢ i →ₐ[A₀] A)
      (g : ∀ ⦃i j⦄, i ≤ j → Aᵢ i →ₐ[A₀] Aᵢ j)
      [DirectedSystem Aᵢ (@g · · ·)]
      (hg : IsDirectLimit (@g · · ·) (f ·))
      {I : Type*} (p : MvPolynomial I A) :
      ∃ (k : ι), p ∈ RingHom.range (MvPolynomial.map (f k).toRingHom) := by
  classical
  have : IsDirected ι (· ≤ ·) := by
    constructor
    intro a b
    simpa using hg.exists_of_eq (i := a) (j := b) 0 0 (by simp)
  choose i c hic using hg.jointly_surjective
  obtain ⟨k, hk⟩ := (p.coeffs.image i).exists_le
  use k
  rw [MvPolynomial.mem_range_map_iff]
  intro m
  simp [coeffs] at hk
  have := hk m
  by_cases h : coeff m p = 0
  · use 0
    simp [h]
  · have := hk m h
    use g (hk m h) (c _)
    simp [hg.naturality, hic]

set_option maxHeartbeats 240000
lemma foobar [Nonempty ι] {A : Type*} [CommRing A] [Algebra A₀ A] (f : ∀ i, Aᵢ i →ₐ[A₀] A)
    [∀ i, Algebra (Aᵢ i) A] (hf : ∀ i, algebraMap (Aᵢ i) A = f i)
    (g : ∀ ⦃i j⦄, i ≤ j → Aᵢ i →ₐ[A₀] Aᵢ j)
    [DirectedSystem Aᵢ (@g · · ·)]
    (hg : IsDirectLimit (@g · · ·) (f ·))
    (B : Type*) [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B] :
    ∃ (i : ι) (Bᵢ : Type u) (_ : CommRing Bᵢ) (_ : Algebra (Aᵢ i) Bᵢ)
      (_ : Algebra.FinitePresentation (Aᵢ i) Bᵢ),
      Nonempty (A ⊗[Aᵢ i] Bᵢ ≃ₐ[A] B) := by
  classical
  obtain ⟨I, _, F, hF, hFG⟩ :=
    Algebra.FinitePresentation.iff_quotient_mvPolynomial'.{_, _, 0}.mp
      ‹Algebra.FinitePresentation A B›
  obtain ⟨n, a, ha⟩ := hFG.exists_fun
  have : IsDirected ι (· ≤ ·) := by
    constructor
    intro a b
    simpa using hg.exists_of_eq (i := a) (j := b) 0 0 (by simp)
  choose i c hic using hg.jointly_surjective
  have (p : MvPolynomial I A) : ∃ (k : ι),
      p ∈ RingHom.range (MvPolynomial.map (f k).toRingHom) := by
    obtain ⟨k, hk⟩ := (p.coeffs.image i).exists_le
    use k
    rw [MvPolynomial.mem_range_map_iff]
    intro m
    simp [coeffs] at hk
    have := hk m
    by_cases h : coeff m p = 0
    · use 0
      simp [h]
    · have := hk m h
      use g (hk m h) (c _)
      simp [hg.naturality, hic]
  have : ∃ (k : ι) (a' : Fin n → MvPolynomial I (Aᵢ k)), ∀ l, MvPolynomial.map (f k) (a' l) = a l := by
    choose k p hp using this
    obtain ⟨k', hk'⟩ := (Finset.univ.image (k ∘ a)).exists_le
    use k'
    simp at hk'
    use fun i ↦ MvPolynomial.map (g (hk' i)) (p (a i))
    intro l
    simp [MvPolynomial.map_map]
    convert hp _
    ext
    simp [hg.naturality]
  obtain ⟨k, a', ha'⟩ := this
  let J : Ideal (MvPolynomial I (Aᵢ k)) := Ideal.span (Set.range a')
  let Bᵢ : Type _ := MvPolynomial I (Aᵢ k) ⧸ J
  let P : Algebra.Presentation (Aᵢ k) Bᵢ := Presentation.naive a'
  let Q₁ : Algebra.Presentation A (A ⊗[Aᵢ k] Bᵢ) := P.baseChange A
  let Q₂ : Algebra.Presentation A B := {
    __ := Algebra.Generators.ofSurjective (F ∘ X)
      (by convert hF; apply MvPolynomial.algHom_ext; simp)
    rels := Fin n
    relation := a
    span_range_relation_eq_ker := by
      convert ha.symm
      apply MvPolynomial.ringHom_ext
      · intro x
        simp [-MvPolynomial.algebraMap_apply, ← MvPolynomial.algebraMap_eq]
      · intro i
        simp [-eq_mpr_eq_cast]
        rfl
  }
  refine ⟨k, Bᵢ, inferInstance, inferInstance, ?_, ?_⟩
  · refine Algebra.FinitePresentation.quotient ?_
    use Finset.image a' Finset.univ
    simp [J]
  · refine ⟨Algebra.Presentation.congr Q₁ Q₂ ?_ ?_ ?_⟩
    · exact Equiv.refl _
    · exact Equiv.refl _
    · intro r
      simp [Q₁, Q₂, P, Equiv.coe_refl, Algebra.Presentation.baseChange, Presentation.naive,
        Algebra.Generators.naive, Algebra.Generators.baseChange, Algebra.Generators.ofSurjective,
        hf, ha']
