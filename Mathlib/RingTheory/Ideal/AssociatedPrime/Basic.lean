/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Exact
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.IsPrimary
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

## Implementation details

The presence of the radical in the definition of `IsAssociatedPrime` is slightly nonstandard but
gives the correct characterization of the prime ideals of any minimal primary decomposition in the
non-Noetherian setting (see Theorem 4.5 in Atiyah-Macdonald). If the ring `R` is assumed to be
Noetherian, then the radical can be dropped from the definition (see `isAssociatedPrime_iff`).

## TODO

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
-/

@[expose] public section

open LinearMap Submodule

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (N : Submodule R M)
  (I : Ideal R) (x : M)

/-- `I : Ideal R` is an associated prime of a submodule `N : Submodule R M` if `I` is prime
and `I = (colon N {x}).radical` for some `x : M`. -/
protected def IsAssociatedPrime : Prop :=
  I.IsPrime ∧ ∃ x, I = (colon N {x}).radical

/-- The set of associated primes of a submodule. -/
protected def associatedPrimes : Set (Ideal R) :=
  { I | N.IsAssociatedPrime I }

variable {N I}

theorem exists_eq_colon_of_mem_minimalPrimes [IsNoetherianRing R]
    (hI : I ∈ (colon N {x}).minimalPrimes) : ∃ x' : M, I = colon N {x'} := by
  by_cases hx : x ∈ N
  · simp [show (colon N {x}) = ⊤ by simpa, Ideal.minimalPrimes_top] at hI
  classical
  set ann := colon N {x}
  -- there exists an integer `n ≠ 0` and an ideal `J` satisfying `I ^ n * J ≤ ann` and `¬ J ≠ I`
  have key : ∃ n ≠ 0, ∃ J : Ideal R, I ^ n * J ≤ ann ∧ ¬ J ≤ I := by
    -- let `n` be large enough so that `ann.radical ^ n ≤ ann` (uses Noetherian)
    obtain ⟨n, hn⟩ := ann.exists_radical_pow_le_of_fg ann.radical.fg_of_isNoetherianRing
    have hn0 : n ≠ 0 := by contrapose! hn; simpa [hn, ann]
    -- then take `J` to be the product of the other minimal primes raised to the `n`th power
    have h := ann.finite_minimalPrimes_of_isNoetherianRing R
    rw [← ann.sInf_minimalPrimes, ← h.coe_toFinset, ← h.toFinset.inf_id_eq_sInf,
      ← Finset.insert_erase (h.mem_toFinset.mpr hI), Finset.inf_insert, id_eq] at hn
    grw [← Ideal.mul_le_inf, mul_pow] at hn
    refine ⟨n, hn0, ((h.toFinset.erase I).inf id) ^ n, hn, ?_⟩
    have (K : Ideal R) (hKI : K ≤ I) (hK : K ∈ ann.minimalPrimes) : K = I :=
      le_antisymm hKI (hI.2 hK.1 hKI)
    simpa [hI.1.1.pow_le_iff hn0, hI.1.1.inf_le', imp_not_comm, not_imp_not]
  obtain ⟨hn0, J, hJ, hJI⟩ := Nat.find_spec key
  -- let `n` be minimal such that there exists an ideal `J` with `I ^ n * J ≤ ann` and `¬ J ≠ I`
  set n := Nat.find key
  -- let `K = I ^ (n - 1) * J`
  let K := I ^ (n - 1) * J
  -- we want `I = colon N {x'}`, and we have `I ≤ colon N {y • x}` for every `y ∈ K` (uses `n ≠ 0`)
  have step1 : ∀ y ∈ K, I ≤ colon N {y • x} := by
    intro y hy p hp
    rw [mem_colon_singleton, smul_smul, ← mem_colon_singleton]
    apply hJ
    simpa [K, ← mul_assoc, mul_pow_sub_one hn0] using mul_mem_mul hp hy
  clear hn0
  -- so it suffices to find a single `y ∈ K` with `colon N {y • x} ≤ I`
  suffices step2 : ∃ y : K, colon N {y • x} ≤ I by
    obtain ⟨y, hyI⟩ := step2
    exact ⟨y • x, le_antisymm (step1 y y.2) hyI⟩
  by_contra! h'
  -- if not, then for every `y ∈ K`, there exists an `f y ∈ colon N {y • x}` with `f y ∉ I`
  simp only [SetLike.not_le_iff_exists] at h'
  choose f g h using h'
  -- let `s` be a finite generating set for `K`
  obtain ⟨s, hs⟩ : (⊤ : Submodule R K).FG := Module.Finite.fg_top
  rw [← (map_injective_of_injective K.subtype_injective).eq_iff,
    map_span, map_subtype_top, ← Finset.coe_image, Ideal.submodule_span_eq] at hs
  -- let `z` be the product of these finitely many `f y`'s
  let z := ∏ y ∈ s, f y
  -- then `z ∉ I`
  have hz : z ∉ I := by
    simp only [z, hI.1.1.prod_mem_iff, not_exists, not_and_or]
    exact fun i ↦ Or.inr (h i)
  -- and `K ≤ colon N {z • x}`
  have hz' : K ≤ colon N {z • x} := by
    rw [← hs, Ideal.span_le, Finset.coe_image, Set.image_subset_iff]
    intro i hi
    obtain ⟨y, hy : z = f i * y⟩ := Finset.dvd_prod_of_mem f hi
    rw [Set.mem_preimage, SetLike.mem_coe, mem_colon_singleton, smul_comm, ← mem_colon_singleton]
    exact hy ▸ Ideal.mul_mem_right y _ (g i)
  -- or equivalently `K * Ideal.span {z} ≤ ann`
  replace hz' : K * Ideal.span {z} ≤ ann := by
    rw [mul_comm, Ideal.span_singleton_mul_le_iff]
    intro i hi
    simpa only [ann, mem_colon_singleton, mul_comm, mul_smul] using hz' hi
  -- but now `K = I ^ (n - 1) * J` contradicts the minimality of `n`
  have hK : I ^ (n - 1) * (J * Ideal.span {z}) ≤ ann ∧ ¬ J * Ideal.span {z} ≤ I := by
    rw [← mul_assoc, hI.1.1.mul_le, not_or, Ideal.span_singleton_le_iff_mem]
    exact ⟨hz', hJI, hz⟩
  by_cases hn' : n - 1 = 0
  · have : n = 1 := by
      grind
    simp [K, this] at hz'
    exact (hK.2 (hz'.trans hI.1.2)).elim
  · have h' : n ≤ n - 1 := Nat.find_min' key ⟨hn', J * Ideal.span {z}, hK⟩
    rw [tsub_le_self.ge_iff_eq, Nat.sub_one_eq_self] at h'
    simp [h'] at hn'

protected theorem isAssociatedPrime_def :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = (colon N {x}).radical :=
  .rfl

protected theorem isAssociatedPrime_iff [h : IsNoetherianRing R] :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = colon N {x} := by
  constructor
  · rintro ⟨hx, x, rfl⟩
    refine ⟨hx, exists_eq_colon_of_mem_minimalPrimes x ?_⟩
    rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff]
  · rintro ⟨hx, x, rfl⟩
    exact ⟨hx, x, hx.radical.symm⟩

protected theorem AssociatePrimes.mem_iff : I ∈ N.associatedPrimes ↔ N.IsAssociatedPrime I :=
  .rfl

end Submodule

section Semiring

variable {R : Type*} [CommSemiring R] (I J : Ideal R) (M : Type*) [AddCommMonoid M] [Module R M]

/-- `IsAssociatedPrime I M` if the prime ideal `I` is the radical of the annihilator
of some `x : M`. -/
def IsAssociatedPrime : Prop :=
  I.IsPrime ∧ ∃ x : M, I = (colon ⊥ {x}).radical

variable (R) in
/-- The set of associated primes of a module. -/
def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }

variable {I J M} {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')

theorem AssociatePrimes.mem_iff : I ∈ associatedPrimes R M ↔ IsAssociatedPrime I M := Iff.rfl

theorem IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime := h.1

theorem isAssociatedPrime_iff [IsNoetherianRing R] :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ ∃ x : M, I = colon ⊥ {x} :=
  (⊥ : Submodule R M).isAssociatedPrime_iff

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
  simp [hx, Subsingleton.elim x 0]

variable (R) in
theorem exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M)
    (hx : x ≠ 0) : ∃ P : Ideal R, IsAssociatedPrime P M ∧ (colon ⊥ {x}).radical ≤ P := by
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | (colon ⊥ {x}).radical ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = (colon ⊥ {y}).radical }
      ⟨_, rfl.le, by simpa, x, rfl⟩
  refine ⟨_, ⟨⟨h₁, ?_⟩, y, rfl⟩, l⟩
  rintro a b ⟨k, hk⟩
  rw [or_iff_not_imp_left]
  intro ha
  simp only [Ideal.mem_radical_iff, mem_colon_singleton, mem_bot] at ha hk
  replace ha := forall_not_of_not_exists ha k
  have H₁ : (colon ⊥ {y} : Ideal R).radical ≤ (colon ⊥ {a ^ k • y}).radical := by
    apply Ideal.radical_mono
    intro c hc
    rw [mem_colon_singleton, mem_bot] at hc ⊢
    rw [smul_comm, hc, smul_zero]
  rw [H₁.eq_of_not_lt (h₃ _ ⟨l.trans H₁, by simpa, _, rfl⟩)]
  use k
  rwa [mem_colon_singleton, smul_smul, ← mul_pow, mul_comm]

namespace associatedPrimes

variable {f} {M'' : Type*} [AddCommMonoid M''] [Module R M''] {g : M' →ₗ[R] M''}

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
  by_cases! h : ∃ a ∈ p.primeCompl, ∃ y : M, ∃ k, f y = a ^ k • x
  · obtain ⟨a, ha, y, k, h⟩ := h
    left
    refine ⟨‹_›, y, le_antisymm (fun b hb ↦ ?_) (fun b ⟨n, hb⟩ ↦ ?_)⟩
    · rw [hx] at hb
      obtain ⟨n, hb⟩ := hb
      use n
      rw [mem_colon_singleton, mem_bot] at hb ⊢
      apply_fun _ using hf
      rw [map_smul, h, smul_comm, hb, smul_zero, map_zero]
    · rw [mem_colon_singleton, mem_bot] at hb
      apply_fun f at hb
      rw [map_smul, map_zero, h, ← mul_smul, ← mem_bot R, ← mem_colon_singleton] at hb
      replace hb := hx.ge (Ideal.le_radical hb)
      contrapose hb
      exact p.primeCompl.mul_mem (p.primeCompl.pow_mem hb n) (p.primeCompl.pow_mem ha k)
  · right
    refine ⟨‹_›, g x, le_antisymm (fun b hb ↦ ?_) (fun b ⟨n, hb⟩ ↦ ?_)⟩
    · rw [hx] at hb
      refine Ideal.radical_mono (fun b hb ↦ ?_) hb
      rw [mem_colon_singleton, mem_bot] at hb ⊢
      rw [← map_smul, hb, map_zero]
    · rw [mem_colon_singleton, mem_bot, ← map_smul, ← LinearMap.mem_ker,
        hfg.linearMap_ker_eq] at hb
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
  simp only [AssociatePrimes.mem_iff, isAssociatedPrime_iff]
  refine subset_antisymm (Set.iUnion₂_subset ?_) ?_
  · rintro _ ⟨h, x, ⟨⟩⟩ r h'
    exact ⟨x, by simpa using h.ne_top, by simpa using h'⟩
  · intro r ⟨x, h, h'⟩
    obtain ⟨P, hP, hx⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x h
    rw [isAssociatedPrime_iff] at hP
    rw [hP.1.radical_le_iff] at hx
    exact Set.mem_biUnion hP (hx (by rwa [mem_colon_singleton]))

theorem biUnion_associatedPrimes_eq_compl_nonZeroDivisors [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R R, p = (nonZeroDivisors R : Set R)ᶜ :=
  (biUnion_associatedPrimes_eq_zero_divisors R R).trans <| by
    ext; simp [← nonZeroDivisorsLeft_eq_nonZeroDivisors, and_comm]

variable {R M}

theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator ≤ I := by
  obtain ⟨hI, x, rfl⟩ := h
  rw [bot_colon']
  exact (annihilator_mono le_top).trans Ideal.le_radical

end Semiring

variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

theorem isAssociatedPrime_iff_exists_injective_linearMap [IsNoetherianRing R] :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ ∃ (f : R ⧸ I →ₗ[R] M), Function.Injective f := by
  rw [isAssociatedPrime_iff, and_congr_right_iff]
  refine fun _ ↦ ⟨fun ⟨x, h⟩ ↦ ?_, fun ⟨f, h⟩ ↦ ⟨(f ∘ₗ mkQ I) 1, ?_⟩⟩
  · replace h : I = ker (toSpanSingleton R M x) := by simp [h, SetLike.ext_iff]
    exact ⟨liftQ _ _ h.le, ker_eq_bot.mp (ker_liftQ_eq_bot' _ _ h)⟩
  · conv_lhs => rw [← I.ker_mkQ, ← ker_comp_of_ker_eq_bot (mkQ I) (ker_eq_bot_of_injective h)]
    simp [SetLike.ext_iff, ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one]

variable {I J M}

theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  have : x ≠ 0 := by
    rintro rfl
    apply hJ.1
    rwa [colon_singleton_zero, Ideal.radical_top] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  have h {y} : y ∈ colon ⊥ {(Ideal.Quotient.mk I) x} ↔ Ideal.Quotient.mk I (y * x) = 0 := by
    rw [mem_colon_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mem_bot]
  simp only [e, Ideal.Quotient.mkₐ_eq_mk, ne_eq, Ideal.Quotient.eq_zero_iff_mem] at this h ⊢
  refine le_antisymm (Ideal.radical_le_radical_iff.mpr fun y hy ↦ ?_)
    (Ideal.radical_mono fun y ↦ h.mpr ∘ I.mul_mem_right x)
  rw [← I.colon_univ, ← Set.top_eq_univ]
  exact (hI.mem_or_mem (h.mp hy)).resolve_left this

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
