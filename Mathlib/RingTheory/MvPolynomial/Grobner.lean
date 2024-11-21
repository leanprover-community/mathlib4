/-
Copyright (c) 2024 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Maps

/-!

# Gröbner Bases of ideals in the ring of polynomials over a field

-/
namespace MvPolynomial

variable {σ K α : Type*} [Field K]

structure MonomialOrder (σ α : Type*) [LinearOrder α] [OrderBot α] extends (σ →₀ ℕ) ↪ α,
    OrderHom (σ →₀ ℕ) α  where
  ( le_iff_add_le_add' {m n p} : toFun m ≤ toFun n ↔ toFun (m + p) ≤ toFun (n + p) )
  ( toFun_zero : toFun 0 = ⊥ )

namespace MonomialOrder

variable [LinearOrder α] [OrderBot α] (size : MonomialOrder σ α)

instance : FunLike (MonomialOrder σ α) (σ →₀ ℕ) α where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : EmbeddingLike (MonomialOrder σ α) (σ →₀ ℕ) α where
  injective' f := f.injective

instance : OrderHomClass (MonomialOrder σ α) (σ →₀ ℕ) α where
  map_rel f {_} {_} h := f.monotone' h

theorem wellFounded (size : MonomialOrder σ α) [Finite σ] :
    WellFounded ((· < ·) on size) := by
  have := ((Finsupp.isPWO (Set.univ : Set (σ →₀ ℕ))).image_of_monotone_on (f := size)
    (s := Set.univ) (r' := (· ≤ ·)) (fun _ _ _ _ h => size.monotone' h)).wellFoundedOn
  simpa [and_iff_right_of_imp le_of_lt]

theorem injective : Function.Injective size := size.toEmbedding.injective

@[simp]
theorem add_le_add_right_iff {m n p : σ →₀ ℕ} :
    size (m + p) ≤ size (n + p) ↔ size m ≤ size n :=
  size.le_iff_add_le_add'.symm

@[simp]
theorem add_le_add_left_iff {m n p : σ →₀ ℕ} :
    size (p + m) ≤ size (p + n) ↔ size m ≤ size n := by
  rw [add_comm, add_comm p n, add_le_add_right_iff]

@[simp]
theorem map_zero : size 0 = ⊥ := size.toFun_zero

@[simp]
theorem map_eq_bot_iff {p : σ →₀ ℕ} : size p = ⊥ ↔ p = 0 := by
  rw [← map_zero, size.injective.eq_iff]

noncomputable def leadingMonomial (f : MvPolynomial σ K) : σ →₀ ℕ :=
  (f.support.toList.argmax size).getD 0

protected noncomputable def leadingCoeff (f : MvPolynomial σ K) : K :=
  f.coeff (size.leadingMonomial f)

variable {size}

@[simp]
theorem leadingMonomial_zero : size.leadingMonomial (0 : MvPolynomial σ K) = 0 := by
  simp [leadingMonomial]

@[simp]
theorem leadingCoeff_zero : size.leadingCoeff (0 : MvPolynomial σ K) = 0 := by
  simp [MonomialOrder.leadingCoeff]

theorem leadingMonomial_mem_support {f : MvPolynomial σ K} (hf0 : f ≠ 0) :
    size.leadingMonomial f ∈ f.support := by
  rw [leadingMonomial]
  cases h : f.support.toList.argmax size with
  | none => simp_all
  | some m =>
    classical rw [List.argmax_eq_some_iff] at h
    simp_all

@[simp]
theorem leadingCoeff_eq_zero_iff {p : MvPolynomial σ K} :
    size.leadingCoeff p = 0 ↔ p = 0 := by
  rw [MonomialOrder.leadingCoeff]
  by_cases hp0 : p = 0
  · simp [hp0]
  · simp only [hp0, iff_false]
    exact mem_support_iff.1 (leadingMonomial_mem_support hp0)

theorem le_leadingMonomial_of_mem_support {f : MvPolynomial σ K} {m : σ →₀ ℕ}
    (hm : m ∈ f.support) : size m ≤ size (size.leadingMonomial f) := by
  rw [leadingMonomial]
  cases h : f.support.toList.argmax size with
  | none => simp_all
  | some n =>
    classical rw [List.argmax_eq_some_iff] at h
    simp_all

theorem leadingMonomial_le_iff_forall_le {p : MvPolynomial σ K} {a : α} :
    size (size.leadingMonomial p) ≤ a ↔ ∀ n ∈ p.support, size n ≤ a := by
  refine ⟨?_, ?_⟩
  · intro h q hq
    exact le_trans (le_leadingMonomial_of_mem_support hq) h
  · intro h
    by_cases hp0 : p = 0
    · simp_all only [support_zero, Finset.not_mem_empty, IsEmpty.forall_iff, implies_true,
        leadingMonomial_zero, map_zero, bot_le]
    · exact h _ (leadingMonomial_mem_support hp0)

variable (size)
def monomialIdeal (S : Set (MvPolynomial σ K)) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun p => monomial (leadingMonomial size p) 1) '' (S \ {0}))

variable {size}
theorem mem_monomialIdeal_iff {p : MvPolynomial σ K} {S : Set (MvPolynomial σ K)} :
    p ∈ monomialIdeal size S ↔ ∀ m ∈ p.support, ∃ q ∈ S, q ≠ 0 ∧
      size.leadingMonomial q ≤ m := by
  refine Iff.trans ?_ (Iff.trans (mem_ideal_span_monomial_image (x := p) (s :=
    size.leadingMonomial '' (S \ {0}))) ?_)
  · rw [Set.image_image, monomialIdeal]
  · simp only [Set.exists_mem_image, Set.mem_diff, Set.mem_singleton_iff, and_assoc]

theorem leadingMonomial_add_le {p q : MvPolynomial σ K} :
    size (size.leadingMonomial (p + q)) ≤
      max (size (size.leadingMonomial p)) (size (size.leadingMonomial q)) := by
  rw [leadingMonomial_le_iff_forall_le]
  intro r hr
  classical rcases Finset.mem_union.1 (support_add hr) with hr | hr
  · exact le_sup_of_le_left (le_leadingMonomial_of_mem_support hr)
  · exact le_sup_of_le_right (le_leadingMonomial_of_mem_support hr)

@[simp]
theorem leadingMonomial_neg {p : MvPolynomial σ K} :
    size.leadingMonomial (-p) = size.leadingMonomial p := by
  simp [leadingMonomial]

theorem leadingMonomial_monomial [DecidableEq K] (m : σ →₀ ℕ) (a : K) :
    size.leadingMonomial (monomial m a) = if a = 0 then 0 else m := by
  simp [leadingMonomial, support_monomial]
  split_ifs
  · simp
  · simp

theorem size_leadingMon_sub_lt {p q : MvPolynomial σ K}
    (hp0 : 0 < size.leadingMonomial p)
    (hm : size.leadingMonomial p = size.leadingMonomial q)
    (hc : size.leadingCoeff p = size.leadingCoeff q) :
    size (size.leadingMonomial (p - q)) < size (size.leadingMonomial p) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [sub_eq_add_neg]
    exact le_trans leadingMonomial_add_le (by simp_all)
  · intro h
    have hp0 : p ≠ 0 := by rintro rfl; simp_all
    by_cases hpq : p = q
    · subst q; simp_all [@eq_comm _ ⊥]
    rw [size.injective.eq_iff] at h
    simp only [MonomialOrder.leadingCoeff] at hc
    have hpq : (p - q).coeff (size.leadingMonomial p) = 0 := by
      rw [coeff_sub, hc, hm, sub_self]
    have hp : (p - q).coeff (size.leadingMonomial p) ≠ 0 := by
      rw [← h, ← mem_support_iff]
      exact leadingMonomial_mem_support (by rwa [Ne, sub_eq_zero])
    exact hp hpq

variable (size)

/-- A Groebner set is a Groebner basis for its span. -/
structure IsGroebnerSet (G : Set (MvPolynomial σ K)) : Prop where
  ( monomialIdeal_eq : size.monomialIdeal (Ideal.span G) = size.monomialIdeal G )

variable {size} {G : Set (MvPolynomial σ K)}

def IsReduced (G : Set (MvPolynomial σ K)) (p : MvPolynomial σ K) : Prop :=
  ∀ g ∈ G, ¬ size.leadingMonomial g ≤ size.leadingMonomial p

theorem isGroebnerSet_iff_monomialIdeal_eq :
    IsGroebnerSet size G ↔ size.monomialIdeal (Ideal.span G) = size.monomialIdeal G := by
  refine ⟨fun h => h.monomialIdeal_eq, fun h => ⟨h⟩⟩

theorem isGroebnerSet_iff_leadingMonomial_le :
    IsGroebnerSet size G ↔ ∀ f ∈ Ideal.span G, f ≠ 0 → ∃ g ∈ G, g ≠ 0 ∧
      size.leadingMonomial g ≤ size.leadingMonomial f := by
  simp only [Ideal.ext_iff, isGroebnerSet_iff_monomialIdeal_eq, mem_monomialIdeal_iff]
  refine ⟨?_, ?_⟩
  · intro h f hfI hf0
    classical
    exact (h (monomial (size.leadingMonomial f) 1)).1 (fun m hm => ⟨f, hfI, hf0, (by
      simp only [one_ne_zero, ↓reduceIte, Finset.mem_singleton, support_monomial] at hm
      rw [hm])⟩) (size.leadingMonomial f) (by simp)
  · intro h f
    refine ⟨?_, ?_⟩
    · intro h1 m hmf
      rcases h1 m hmf with ⟨g, hg, hg0, hgm⟩
      rcases h g hg hg0 with ⟨g', hg', hg0', hgg'⟩
      exact ⟨g', hg', hg0', le_trans hgg' hgm⟩
    · intro h1 m hmf
      rcases h1 m hmf with ⟨g, hg, hgm⟩
      exact ⟨g, Ideal.subset_span hg, hgm⟩


theorem isGroebnerSet_iff_isReduced_eq_zero :
    IsGroebnerSet size G ↔ ∀ f ∈ Ideal.span G, size.IsReduced G f → f = 0 := by
  simp only [isGroebnerSet_iff_leadingMonomial_le, IsReduced]
  refine forall_congr' fun f => forall_congr' fun hf => ?_
  by_cases hf0 : f = 0
  · subst hf0
    simp only [leadingMonomial_zero, nonpos_iff_eq_zero, implies_true, iff_true]

  · simp [hf0]

theorem exists_critical_pair_of_mem_of_forall_le {p : MvPolynomial σ K}
    (hG : p ∈ Ideal.span G) (hp : ∀ g ∈ G, ¬ size.leadingMonomial g ≤ size.leadingMonomial p) :
    ∃ g₁ g₂ ∈ G, ¬ IsGroebnerSet _


theorem isGroebnerSet_iff_exists_leadReduction_eq_zero :
    IsGroebnerSet size G ↔
     (∀ p, p ∈ Ideal.span G ↔ ∃ l : LeadReduction size G p, l.result = 0) := by
  rw [isGroebnerSet_iff_leadingMonomial_le]
  refine ⟨?_, ?_⟩
  · intro h p
    refine ⟨?_, ?_⟩
    · intro hp


end MonomialOrder



end MvPolynomial
