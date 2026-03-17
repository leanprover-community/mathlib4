/-
Copyright (c) 2025 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Emilie Uthaiwat, Haoming Ning, Brian Nugent
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!

# Kaplansky criterion for factoriality

We prove Kaplansky criterion for factoriality: an integral domain is a UFD if and only if every
nonzero prime ideal contains a prime element.

We prove a closely related criterion for factoriality: a Noetherian integral domain is a UFD
if and only if every prime ideal of height one is principal.

## Main declarations

`iff_exists_prime_mem_of_isPrime`: an integral domain is a UFD if and only if every nonzero prime
ideal contains a prime element.

`iff_height_one_prime_principal`: a Noetherian integral domain is a UFD if and only if
every prime ideal of height one is principal.

## References

See <https://stacks.math.columbia.edu/tag/0AFT> for reference for `iff_height_one_prime_principal`

-/

variable {R : Type*}

namespace UniqueFactorizationMonoid

open Set Ideal Submonoid

/-- The set of ideals of a semiring `R` that are disjoint from a given subsemigroup `S`. -/
def kaplanskySet [Semiring R] (S : Subsemigroup R) := {I : Ideal R | Disjoint (I : Set R) S}

section semiring

variable [Semiring R] {S : Subsemigroup R} {P : Ideal R}

theorem mem_kaplanskySet_iff : P ∈ kaplanskySet S ↔ (P : Set R) ∩ S = ∅ :=
  disjoint_iff_inter_eq_empty

/-- If `0 ∉ S`, then every chain in `kaplanskySet S` has an upper bound. -/
theorem exists_mem_kaplanskySet_le {C : Set (Ideal R)} (hS : 0 ∉ S) (hC : C ⊆ kaplanskySet S)
      (hC₂ : IsChain (· ≤ ·) C) : ∃ P ∈ kaplanskySet S, ∀ J ∈ C, J ≤ P := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨_, hI⟩
  · exact ⟨⊥, by simpa [mem_kaplanskySet_iff, eq_empty_iff_forall_notMem]⟩
  · refine ⟨sSup C, ?_, fun _ hz ↦ le_sSup hz⟩
    rw [mem_kaplanskySet_iff, eq_empty_iff_forall_notMem]
    intro x hx
    rcases (Submodule.mem_sSup_of_directed ⟨_, hI⟩ hC₂.directedOn).1 hx.1 with ⟨J, hJ₁, hJ₂⟩
    have hx₂ : (J : Set R) ∩ S ≠ ∅ := nonempty_iff_ne_empty.1 ⟨x, hJ₂, hx.2⟩
    exact hx₂ (mem_kaplanskySet_iff.mp (hC hJ₁))

/-- If `0 ∉ S`, then there is a maximal element in `kaplanskySet S`. -/
theorem exists_mem_kaplanskySet_eq_of_le (hS : 0 ∉ S) :
    ∃ P ∈ kaplanskySet S, ∀ I ∈ kaplanskySet S, P ≤ I → I = P := by
  obtain ⟨P, hP⟩ := zorn_le₀ (kaplanskySet S) (fun _ ↦ exists_mem_kaplanskySet_le hS)
  exact ⟨P, hP.1, fun _ hI H ↦ le_antisymm (hP.2 hI H) H⟩

end semiring

section IsDomain

variable [CommSemiring R] [IsDomain R]

theorem span_notMem_kaplanskySet {a : R} (ha : a ≠ 0)
      (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) :
    span {a} ∉ kaplanskySet (closure {r : R | Prime r}).toSubsemigroup := by
  have hzero : 0 ∉ closure {r : R | Prime r} := fun h ↦ by
    rcases exists_multiset_of_mem_closure h with ⟨l, hl, hprod⟩
    exact not_prime_zero (hl 0 (Multiset.prod_eq_zero_iff.1 hprod))
  intro h
  rcases exists_mem_kaplanskySet_eq_of_le hzero with ⟨T, hT, hT₂⟩
  have hT₃ : T ≠ ⊥ := fun h₂ ↦ ha (span_singleton_eq_bot.1 ((h₂ ▸ hT₂) _ h (zero_le _)))
  have Tpri := isPrime_of_maximally_disjoint T _ hT (fun J hJ H ↦ hJ.ne (hT₂ J H hJ.le).symm)
  rcases (H T) hT₃ Tpri with ⟨x, H₃, H₄⟩
  rw [mem_kaplanskySet_iff, eq_empty_iff_forall_notMem] at hT
  exact hT x ⟨H₃, subset_closure H₄⟩

/-- The nontrivial implication of Kaplansky's criterion: an integral domain is a UFD if every
nonzero prime ideal contains a prime element. -/
theorem of_exists_prime_mem_of_isPrime
    (H : ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x) : UniqueFactorizationMonoid R := by
  refine UniqueFactorizationMonoid.of_exists_prime_factors fun a ha ↦ ?_
  have ha₂ := span_notMem_kaplanskySet ha H
  rw [mem_kaplanskySet_iff] at ha₂
  rcases nonempty_iff_ne_empty.2 ha₂ with ⟨x, hx, hx₂⟩
  obtain ⟨b, hb⟩ := mem_span_singleton'.1 hx
  rw [← hb, mul_comm] at hx₂
  have hsubset : closure {r : R | Prime r} ≤ closure {r : R | IsUnit r ∨ Prime r} :=
    closure_mono (by grind)
  have := divisor_closure_eq_closure _ _ (hsubset hx₂)
  clear ha ha₂ hx hb hx₂
  induction this using closure_induction with
  | mem z hz =>
      rcases hz with h | h
      · exact ⟨∅, by simpa using (associated_one_iff_isUnit.2 h).symm⟩
      · exact ⟨{z}, by simpa⟩
  | one => exact ⟨∅, by simp⟩
  | mul z₁ z₂ hz₁ hz₂ h₁ h₂ =>
      obtain ⟨S₁, hS₁pri, hS₁⟩ := h₁
      obtain ⟨S₂, hS₂pri, hS₂⟩ := h₂
      refine ⟨S₁ + S₂, by grind, ?_⟩
      rw [Multiset.prod_add]
      exact hS₁.mul_mul hS₂

/-- Kaplansky's criterion: an integral domain is a UFD if and only if every nonzero prime ideal
contains a prime element. -/
public theorem iff_exists_prime_mem_of_isPrime :
    UniqueFactorizationMonoid R ↔ ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x :=
  ⟨fun _ _ hI hI₂ ↦ hI₂.exists_mem_prime_of_ne_bot hI,
    fun H ↦ of_exists_prime_mem_of_isPrime H⟩

end IsDomain

section CommRing

variable [CommRing R]

/-- Given a prime P of finite height ≥ 1, there exists a prime Q of height one contained in P. -/
lemma exists_height_one_le_of_finite_height
    {P : Ideal R} (h_prime : P.IsPrime) (h_fin : P.FiniteHeight) (hP : P.primeHeight ≥ 1) :
    ∃ Q ≤ P, Q.IsPrime ∧ Q.height = 1 := by
  /- If height P is one, then done -/
  by_cases hP : P.primeHeight = 1
  · rw[← P.height_eq_primeHeight] at hP
    use P
  /- Otherwise, height P > 1 -/
  have hPgt1 : 1 < P.primeHeight := by
    rw[lt_iff_le_and_ne]
    refine ⟨?_, by push_neg at hP; exact hP.symm⟩
    expose_names; exact le_of_eq_of_le rfl hP_1
  /- We obtain an element of height 1 preceeding P in PrimeSpectrum R -/
  obtain ⟨Q, hQ⟩ := (Order.coe_lt_height_iff P.primeHeight_lt_top).mp hPgt1
  use Q.asIdeal
  exact ⟨hQ.1.1, ⟨ Q.2, by rw[Ideal.height_eq_primeHeight]; exact hQ.right ⟩⟩

variable [IsDomain R]

/-- Height of non zero prime ideal in a domain is greater than or equal to one. -/
public lemma height_ge_one_of_prime_ne_bot
    {P : Ideal R} (h_prime : P.IsPrime) (h_ne : P ≠ ⊥) :
    P.height ≥ 1 := by
  /- Suppose P is height 0 -/
  by_contra hC
  push_neg at hC
  rw[ENat.lt_one_iff_eq_zero, P.height_eq_primeHeight] at hC
  /- Order.height is defined for P : PrimeSpectrum R -/
  let Pp : PrimeSpectrum R := ⟨ P, h_prime ⟩
  change Order.height Pp = 0 at hC
  /- Then P is the zero ideal since R is domain -/
  rw[Order.height_eq_zero, isMin_iff_eq_bot] at hC
  have : Pp.asIdeal = ⊥ := by
    rw[hC]
    simp only [PrimeSpectrum.asIdeal_bot]
  exact h_ne this

/- This following lemma is provided kindly by
Bianca Viray, Bryan Boehnke, Grant Yang, George Peykanu, Tianshuo Wang, see
<https://github.com/uw-math-ai/monogenic-extensions/blob/9a46c352a33af11818cc10f474b383f0a2d6dcac/Monogenic/MonogenicOfNonEtale.lean#L93>-/
/-- UFD implies height one prime principal. -/
lemma height_one_prime_principal [UniqueFactorizationMonoid R]
    (q : Ideal R) [hq_prime : q.IsPrime] (hq_height : q.height = 1) :
    ∃ q₀ : R, q = Ideal.span {q₀} := by
  /- Step 1: q ≠ ⊥ because height q = 1 > 0 -/
  have hq_ne_bot : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.height_bot] at hq_height
    exact zero_ne_one hq_height
  /- Step 2: By UFD property, every nonzero prime ideal contains a prime element -/
  obtain ⟨p, hp_mem, hp_prime⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hq_prime hq_ne_bot
  /- Step 3: span {p} is a prime ideal since p is prime -/
  have h_span_prime : (Ideal.span {p}).IsPrime := by
    rw [Ideal.span_singleton_prime hp_prime.ne_zero]
    exact hp_prime
  /- Step 4: span {p} ⊆ q -/
  have h_span_le : Ideal.span {p} ≤ q := (Ideal.span_singleton_le_iff_mem (I := q)).mpr hp_mem
  /- Step 5: span {p} ≠ ⊥ -/
  have h_span_ne_bot : Ideal.span {p} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact hp_prime.ne_zero
  /- Step 6: Since height q = 1, if span {p} < q, then span {p} has height 0
  In a domain, height 0 primes are just ⊥, but span {p} ≠ ⊥, contradiction.
  So span {p} = q. -/
  have h_eq : Ideal.span {p} = q := by
    by_contra h_ne
    have h_lt : Ideal.span {p} < q := lt_of_le_of_ne h_span_le h_ne
    /- height (span {p}) < height q = 1, so height (span {p}) = 0 -/
    haveI : (Ideal.span {p}).IsPrime := h_span_prime
    have hq_ht_ne_top : q.height ≠ ⊤ := by
      rw [hq_height]
      exact ENat.one_ne_top
    haveI : q.FiniteHeight := ⟨Or.inr hq_ht_ne_top⟩
    haveI : (Ideal.span {p}).FiniteHeight := Ideal.finiteHeight_of_le h_span_le hq_prime.ne_top
    have h_ht_lt := Ideal.height_strict_mono_of_is_prime h_lt
    rw [hq_height] at h_ht_lt
    /- height (span {p}) < 1 means height (span {p}) = 0 -/
    have h_ht_zero : (Ideal.span {p}).height = 0 := ENat.lt_one_iff_eq_zero.mp h_ht_lt
    /- span {p} is a minimal prime of R (height 0 prime) -/
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff] at h_ht_zero
    /- In a domain, minimalPrimes of (⊥ : Ideal R) is just {⊥} -/
    have h_span_eq_bot : Ideal.span {p} = ⊥ := by
      have h_mem : Ideal.span {p} ∈ (⊥ : Ideal R).minimalPrimes := h_ht_zero
      /- (⊥ : Ideal R).minimalPrimes = minimalPrimes R by definition -/
      have : (⊥ : Ideal R).minimalPrimes = minimalPrimes R := rfl
      rw [this, IsDomain.minimalPrimes_eq_singleton_bot] at h_mem
      exact Set.mem_singleton_iff.mp h_mem
    exact h_span_ne_bot h_span_eq_bot
  exact ⟨p, h_eq.symm⟩

end CommRing

section IsNoetherianDomain

variable [CommRing R] [IsDomain R] [IsNoetherian R R]

/-- Height one prime is principal implies UFD -/
public theorem of_height_one_prime_principal : (∀ (I : Ideal R), I.IsPrime →
    I.height = 1 → ∃ x : R, I = Ideal.span {x}) → UniqueFactorizationMonoid R := by
  intro h
  rw[iff_exists_prime_mem_of_isPrime]
  intros I hI_ne hI_prime
  /- Since R is a domain, height of I is >= 1 -/
  have hIge1 : I.height ≥ 1 := height_ge_one_of_prime_ne_bot hI_prime hI_ne
  /- There exists a height 1 prime ideal I contained in J -/
  have hJ : ∃ (J : Ideal R), J ≤ I ∧ J.IsPrime ∧ J.height = 1 := by
    apply exists_height_one_le_of_finite_height
    · exact Ideal.finiteHeight_of_isNoetherianRing I
    · rw[I.height_eq_primeHeight] at hIge1
      exact hIge1
  rcases hJ with ⟨J, hJI, hJprime, h_height⟩
  /- By hypothesis J is principal -/
  have hJ_princ := h J hJprime h_height
  obtain ⟨x, hx⟩ := hJ_princ
  /- Since J is height 1, it is not the zero ideal -/
  have hJ_ne: J ≠ ⊥ := by
    intro h_bot
    rw [h_bot, Ideal.height_bot (R := R)] at h_height
    cases h_height
  /- Then x is not zero -/
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    apply hJ_ne
    rw [hx, hx_zero]
    exact Ideal.span_singleton_zero
  /- Then x is prime -/
  have hx_prime : Prime x := by
    rw [hx] at hJprime
    exact (Ideal.span_singleton_prime hx_ne).mp hJprime
  /- Also x is in J -/
  have hxJ : x ∈ J := by
    rw [hx]
    have hx_set : x ∈ ({x} : Set R) := by aesop
    exact Ideal.subset_span hx_set
  /- Then x is in I -/
  exact ⟨x, hJI hxJ, hx_prime⟩

/-- Factoriality criterion: a Noetherian integral domain is a UFD
if and only if every height one prime is principal -/
public theorem iff_height_one_prime_principal :
    UniqueFactorizationMonoid R ↔ (∀ (I : Ideal R), I.IsPrime →
    I.height = 1 → ∃ x : R, I = Ideal.span {x}):=
  ⟨fun _ I _ hI_height => height_one_prime_principal I hI_height,
  of_height_one_prime_principal⟩

end IsNoetherianDomain

end UniqueFactorizationMonoid
