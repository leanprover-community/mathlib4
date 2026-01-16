/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Exact
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!

# Associated primes of a module

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `IsAssociatedPrime`: `IsAssociatedPrime I M` if the prime ideal `I` is the
  radical of the annihilator of some `x : M`.
- `associatedPrimes`: The set of associated primes of a module.

## Main results
- `exists_le_isAssociatedPrime_of_isNoetherianRing`: In a Noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associatedPrimes.eq_singleton_of_isPrimary`: In a Noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## TODO

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

-/

@[expose] public section


variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

open LinearMap Submodule

/-- `IsAssociatedPrime I M` if the prime ideal `I` is the annihilator of some `x : M`. -/
def IsAssociatedPrime : Prop :=
  I.IsPrime ∧ ∃ x, I = ((⊥ : Submodule R M).colon {x}).radical

variable {I J M} in
theorem isAssociatedPrime_iff :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ ∃ x, I = ((⊥ : Submodule R M).colon {x}).radical :=
  .rfl

example (h : I ≤ J) (n : ℕ) : I ^ n ≤ J ^ n := by exact Ideal.pow_right_mono h n

variable {M} in
theorem technical [h : IsNoetherianRing R] (P : Ideal R) (m : M)
    (hP : P ∈ ((⊥ : Submodule R M).colon {m}).minimalPrimes) :
    ∃ m' : M, P = ((⊥ : Submodule R M).colon {m'}) := by
  have hP' := hP.1.1
  by_cases hm : m = 0
  · simp [hm] at hP
    simp [Ideal.minimalPrimes_top] at hP
  classical
  set ann := (⊥ : Submodule R M).colon {m}
  have key : ∃ k > 0, ∃ Q : Ideal R, P ^ k * Q ≤ ann ∧ ¬ Q ≤ P := by
    have h := Ideal.finite_minimalPrimes_of_isNoetherianRing R ann
    have key := Ideal.exists_radical_pow_le_of_fg ann ann.radical.fg_of_isNoetherianRing
    obtain ⟨k, hk⟩ := key
    have hk0 : k ≠ 0 := by
      contrapose! hk
      simpa [hk, ann]
    replace hk0 : 0 < k := pos_of_ne_zero hk0
    rw [← Ideal.sInf_minimalPrimes, ← h.coe_toFinset, ← h.toFinset.inf_id_eq_sInf] at hk
    have tada : {P} ⊆ h.toFinset := by simpa
    rw [← Finset.union_sdiff_of_subset tada, Finset.inf_union, Finset.inf_singleton, id_eq] at hk
    replace hk := (Ideal.pow_right_mono Ideal.mul_le_inf k).trans hk
    rw [mul_pow] at hk
    refine ⟨k, hk0, ((h.toFinset \ {P}).inf id) ^ k, hk, ?_⟩
    rw [Ideal.IsPrime.pow_le_iff hk0.ne', hP'.inf_le']
    push_neg
    intro Q hQ
    simp only [Finset.mem_sdiff, h.mem_toFinset, Finset.mem_singleton] at hQ
    obtain ⟨hQ, hQ'⟩ := hQ
    contrapose! hQ'
    exact le_antisymm hQ' (hP.2 ⟨hQ.1.1, hQ.1.2⟩ hQ')
  obtain ⟨hn0, Q, hQ, hQP⟩ := Nat.find_spec key
  set n := Nat.find key
  let I := P ^ (n - 1) * Q
  have step1 : ∀ y ∈ I, P ≤ (⊥ : Submodule R M).colon {y • m} := by
    intro y hy p hp
    rw [mem_colon_singleton, smul_smul, ← mem_colon_singleton]
    apply hQ
    simpa [I, ← mul_assoc, mul_pow_sub_one hn0.ne'] using mul_mem_mul hp hy
  suffices step2 : ∃ y : I, (⊥ : Submodule R M).colon {y • m} ≤ P by
    obtain ⟨y, hyP⟩ := step2
    exact ⟨y • m, le_antisymm (step1 y y.2) hyP⟩
  by_contra! h'
  simp only [SetLike.not_le_iff_exists] at h'
  choose f g h using h'
  obtain ⟨s, hs⟩ : (⊤ : Submodule R I).FG := Module.Finite.fg_top
  replace hs : Ideal.span (s.image (fun (x : I) ↦ (x : R)) : Set R) = I := by
    apply_fun (map (Submodule.subtype I)) at hs
    simp [← Submodule.span_image] at hs
    simpa
  let z := ∏ i ∈ s, f i
  have hz : z ∉ P := by
    simp only [z, hP'.prod_mem_iff, not_exists, not_and_or]
    exact fun i ↦ Or.inr (h i)
  have hz' : I ≤ ((⊥ : Submodule R M).colon {z • m}) := by
    rw [← hs, Ideal.span_le]
    intro w hw
    simp only [Finset.coe_image, Set.mem_image] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    specialize g i
    obtain ⟨y, hy : z = f i * y⟩ := Finset.dvd_prod_of_mem f hi
    rw [hy, mul_comm, SetLike.mem_coe, mem_colon_singleton, smul_comm,
      ← mem_colon_singleton]
    apply Ideal.mul_mem_left
    exact g
  replace hz' : I * Ideal.span {z} ≤ ann := by
    rw [mul_comm, Ideal.span_singleton_mul_le_iff]
    intro i hi
    specialize hz' hi
    rwa [mem_colon_singleton, smul_smul, mul_comm, ← mem_colon_singleton] at hz'
  have tada : P ^ (n - 1) * (Q * Ideal.span {z}) ≤ ann ∧ ¬ Q * Ideal.span {z} ≤ P := by
    rw [← mul_assoc]
    use hz'
    rw [hP'.mul_le, not_or, Ideal.span_singleton_le_iff_mem]
    exact ⟨hQP, hz⟩
  by_cases tada' : 0 < n - 1
  · have h' := Nat.find_min' key ⟨tada', Q * Ideal.span {z}, tada⟩
    change n ≤ n - 1 at h'
    contrapose! h'
    simpa
  · have : n = 1 := by
      simp only [tsub_pos_iff_lt, not_lt] at tada'
      exact le_antisymm tada' hn0
    simp [I, this] at hz'
    apply tada.2
    exact hz'.trans hP.1.2

  -- there exists p ^ k * q ≤ ann(m) with ¬ q ≤ p
  -- let k be minimal
  -- let I = p ^ (k - 1) * q
  -- any y ∈ I satisfies p ≤ ann(y * m) since z ∈ p implies z * y * m ∈ p ^ k * q * m = 0
  -- we must find element y ∈ I satisfying ann(y * m) ≤ p
  -- suppose not, then every y ∈ I has some z ∉ p with y * z * m = 0
  -- I is finitely generated, take the product of these z's
  -- then z ∉ p and I * z ≤ ann(m)
  -- p ^ (k - 1) * z * q ≤ ann(m) and ¬ z * q ≤ p
  -- contradicts minimality of k, unless k = 1, I = q, z * q ≤ ann(m) ≤ p contradiction

theorem isAssociatedPrime_iff' [h : IsNoetherianRing R] :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ ∃ x, I = (⊥ : Submodule R M).colon {x} := by
  constructor; swap
  · rintro ⟨hx, x, rfl⟩
    exact ⟨hx, x, hx.radical.symm⟩
  · rintro ⟨hx, x, rfl⟩
    refine ⟨hx, technical ((⊥ : Submodule R M).colon {x}).radical x ?_⟩
    rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff]

@[deprecated (since := "2026-01-15")]
alias isAssociatedPrime_iff_exists_injective_linearMap := isAssociatedPrime_iff

variable (R)

/-- The set of associated primes of a module. -/
def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }

variable {I J M R}
variable {M' : Type*} [AddCommGroup M'] [Module R M'] (f : M →ₗ[R] M')

theorem AssociatePrimes.mem_iff : I ∈ associatedPrimes R M ↔ IsAssociatedPrime I M := Iff.rfl

theorem IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime := h.1
theorem IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Function.Injective f) :
    IsAssociatedPrime I M' := by
  obtain ⟨x, rfl⟩ := h.2
  refine ⟨h.1, ⟨f x, ?_⟩⟩
  ext r
  simp_rw [Ideal.mem_radical_iff, mem_colon_singleton, mem_bot, ← map_smul, map_eq_zero_iff f hf]

theorem LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') :
    IsAssociatedPrime I M ↔ IsAssociatedPrime I M' :=
  ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩

theorem not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrime I M := by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  simp [hx, Ideal.radical_eq_top, Subsingleton.elim x 0]

variable (R) in
theorem exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M)
    (hx : x ≠ 0) :
    ∃ P : Ideal R, IsAssociatedPrime P M ∧ ((⊥ : Submodule R M).colon {x}).radical ≤ P := by
  sorry
  -- have : ker (toSpanSingleton R M x) ≠ ⊤ := by
  --   rwa [Ne, Ideal.eq_top_iff_one, mem_ker, toSpanSingleton_apply, one_smul]
  -- obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
  --   set_has_maximal_iff_noetherian.mpr H
  --     { P | ker (toSpanSingleton R M x) ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = ker (toSpanSingleton R M y) }
  --     ⟨_, rfl.le, this, x, rfl⟩
  -- refine ⟨_, ⟨⟨h₁, ?_⟩, y, rfl⟩, l⟩
  -- intro a b hab
  -- rw [or_iff_not_imp_left]
  -- intro ha
  -- rw [mem_ker, toSpanSingleton_apply] at ha hab
  -- have H₁ : ker (toSpanSingleton R M y) ≤ ker (toSpanSingleton R M (a • y)) := by
  --   intro c hc
  --   rw [mem_ker, toSpanSingleton_apply] at hc ⊢
  --   rw [smul_comm, hc, smul_zero]
  -- have H₂ : ker (toSpanSingleton R M (a • y)) ≠ ⊤ := by
  --   rwa [Ne, ker_eq_top, toSpanSingleton_eq_zero_iff]
  -- rwa [H₁.eq_of_not_lt (h₃ _ ⟨l.trans H₁, H₂, _, rfl⟩),
  --   mem_ker, toSpanSingleton_apply, smul_comm, smul_smul]

namespace associatedPrimes

variable {f} {M'' : Type*} [AddCommGroup M''] [Module R M''] {g : M' →ₗ[R] M''}

/-- If `M → M'` is injective, then the set of associated primes of `M` is
contained in that of `M'`. -/
@[stacks 02M3 "first part"]
theorem subset_of_injective (hf : Function.Injective f) :
    associatedPrimes R M ⊆ associatedPrimes R M' := fun _I h => h.map_of_injective f hf

/-- If `0 → M → M' → M''` is an exact sequence, then the set of associated primes of `M'` is
contained in the union of those of `M` and `M''`. -/
@[stacks 02M3 "second part"]
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    associatedPrimes R M' ⊆ associatedPrimes R M ∪ associatedPrimes R M'' := by
  rintro p ⟨_, x, hx⟩
  simp only [Set.mem_union, AssociatePrimes.mem_iff, isAssociatedPrime_iff]
  by_cases! h : ∃ a ∈ p.primeCompl, ∃ y : M, ∃ k, f y = a ^ k • x
  · obtain ⟨a, ha, y, k, hk⟩ := h
    left
    refine ⟨‹_›, y, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
    · rw [hx] at hb
      obtain ⟨n, hb⟩ := hb
      use n
      rw [mem_colon_singleton, mem_bot] at hb ⊢
      apply_fun _ using hf
      rw [map_smul, hk, smul_comm, hb, smul_zero, map_zero]
    · obtain ⟨n, hb⟩ := hb
      rw [mem_colon_singleton, mem_bot] at hb
      apply_fun f at hb
      rw [map_smul, map_zero, hk, ← mul_smul] at hb
      contrapose hb
      have key := p.primeCompl.mul_mem (p.primeCompl.pow_mem hb n) (p.primeCompl.pow_mem ha k)
      contrapose! key
      simp only [hx, Ideal.mem_primeCompl_iff, not_not]
      use 1
      simpa
  · right
    refine ⟨‹_›, g x, le_antisymm (fun b hb ↦ ?_) (fun b hb ↦ ?_)⟩
    · rw [hx] at hb
      refine Ideal.radical_mono (fun y hy ↦ ?_) hb
      rw [mem_colon_singleton, mem_bot] at hy ⊢
      rw [← map_smul, hy, map_zero]
    · obtain ⟨n, hb⟩ := hb
      rw [mem_colon_singleton, mem_bot, ← map_smul, ← mem_ker, hfg.linearMap_ker_eq] at hb
      obtain ⟨y, hy⟩ := hb
      by_contra H
      exact h b H y n hy

variable (R M M') in
/-- The set of associated primes of the product of two modules is equal to
the union of those of the two modules. -/
@[stacks 02M3 "third part"]
theorem prod : associatedPrimes R (M × M') = associatedPrimes R M ∪ associatedPrimes R M' :=
  (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm (Set.union_subset_iff.2
    ⟨subset_of_injective LinearMap.inl_injective, subset_of_injective LinearMap.inr_injective⟩)

end associatedPrimes

theorem LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') :
    associatedPrimes R M = associatedPrimes R M' :=
  le_antisymm (associatedPrimes.subset_of_injective l.injective)
    (associatedPrimes.subset_of_injective l.symm.injective)

theorem associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPrimes R M = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]
  apply not_isAssociatedPrime_of_subsingleton

variable (R M)

theorem associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] :
    (associatedPrimes R M).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩

theorem biUnion_associatedPrimes_eq_zero_divisors [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R M, p = { r : R | ∃ x : M, x ≠ 0 ∧ r • x = 0 } := by
  simp only [AssociatePrimes.mem_iff, isAssociatedPrime_iff']
  refine subset_antisymm (Set.iUnion₂_subset ?_) ?_
  · rintro _ ⟨h, x, ⟨⟩⟩ r h'
    refine ⟨x, ?_, by simpa using h'⟩
    rintro rfl
    rw [colon_singleton_zero] at h
    exact h.1 rfl
  · intro r ⟨x, h, h'⟩
    obtain ⟨P, hP, hx⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x h
    rw [Ideal.IsPrime.radical_le_iff hP.1] at hx
    rw [isAssociatedPrime_iff'] at hP
    refine Set.mem_biUnion hP (hx ?_)
    rwa [mem_colon_singleton]

theorem biUnion_associatedPrimes_eq_compl_nonZeroDivisors [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R R, p = (nonZeroDivisors R : Set R)ᶜ :=
  (biUnion_associatedPrimes_eq_zero_divisors R R).trans <| by
    ext; simp [← nonZeroDivisorsLeft_eq_nonZeroDivisors, and_comm]

variable {R M}

theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator ≤ I := by
  obtain ⟨hI, x, rfl⟩ := h
  intro y hy
  refine Ideal.le_radical ?_
  simp only [mem_annihilator, mem_top, forall_const] at hy
  specialize hy x
  simpa

theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  refine le_antisymm ?_ ?_; swap
  · rw [hJ.radical_le_iff, e]
    intro x hx
    use 1
    simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  rw [e, Ideal.radical_le_radical_iff]
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  intro y hy
  simp only [Ideal.Quotient.mkₐ_eq_mk, mem_colon_singleton, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hy
  have := (hI.mem_or_mem hy).resolve_left
  simp only [Set.top_eq_univ, colon_univ] at this
  apply this
  intro hx
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hx,
    colon_singleton_zero, Ideal.radical_top] at e
  exact hJ.1 e

theorem associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) :
    associatedPrimes R (R ⧸ I) = {I.radical} := by
  ext J
  rw [Set.mem_singleton_iff]
  refine ⟨IsAssociatedPrime.eq_radical hI, ?_⟩
  rintro rfl
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I :) 1, (Ideal.Quotient.mk I :) 0, ?_⟩
    rw [Ne, Ideal.Quotient.eq, sub_zero, ← Ideal.eq_top_iff_one]
    exact hI.1
  obtain ⟨a, ha⟩ := associatedPrimes.nonempty R (R ⧸ I)
  exact ha.eq_radical hI ▸ ha
