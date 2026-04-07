/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.Height.Northcott
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Construction of L-functions

This file constructs L-functions as formal Dirichlet series.

## Main definitions

* `ArithmeticFunction.ofPowerSeries q f`: L-function `f(q⁻ˢ)` obtained from a power series `f(T)`.
* `ArithmeticFunction.eulerProduct f`: the Euler product of a family `f i` of Dirichlet series.

## Implementation notes

We take the following route from polynomials to L-functions:
* Starting from a polynomial in `T`, `PowerSeries.invOfUnit` gives the reciporical power series.
* `ofPowerSeries` gives the local Euler factor as a formal Dirichlet series on powers of `q`.
* `eulerProduct` gives the L-function as the formal product of these local Euler factors.
* `LSeries` gives the L-function as an analytic function on the right half-plane of convergence.

For example, the Riemann zeta function `ζ(s)` corresponds to taking `1 - T` at each prime `p`.

For context, here is a diagram of the possible routes from polynomials to L-functions:

                   T=q⁻ˢ                     s ∈ ℂ
[polynomials in T] ----> [polynomials in q⁻ˢ] ----> [analytic function in s]
          |                           |                           |
          | (reciprocal)              | (reciprocal)              | (reciprocal)
          v         T=q⁻ˢ             V          s ∈ ℂ            V
[power series in T] ----> [power series in q⁻ˢ] ----> [analytic function in s] (the Euler factor)
          |                           |                           |
          | (product)                 | (product)                 | (product)
          v                 T=q⁻ˢ     V               s ∈ ℂ       V
[multivariate power series] ----> [Dirichlet series] ----> [L-function in s] (the Euler product)
-/

@[expose] public section

namespace ArithmeticFunction

@[simp]
theorem algebraMap_map_one {R : Type*} [CommSemiring R] (x : R) :
    algebraMap R (ArithmeticFunction R) x 1 = x := by
  simp [Algebra.algebraMap_eq_smul_one]

end ArithmeticFunction

namespace ArithmeticFunction

open Filter

section PowerSeries

variable {R : Type*} [CommSemiring R]

/-- The arithmetic function corresponding to the Dirichlet series `f(q⁻ˢ)`.
For example, if `f = 1 + X + X² + ...` and `q = p`, then `f(q⁻ˢ) = 1 + p⁻ˢ + p⁻²ˢ + ...`.

If `q ≤ 1` then `k ↦ q ^ k` is not injective, so we use the junk value `f.constantCoeff`. -/
noncomputable def ofPowerSeries (q : ℕ) : PowerSeries R →ₐ[R] ArithmeticFunction R where
  toFun f := if hq : 1 < q then
    ⟨Function.extend (q ^ ·) (f.coeff ·) 0, by simp [Nat.ne_zero_of_lt hq]⟩ else
      algebraMap R (ArithmeticFunction R) f.constantCoeff
  map_zero' := by ext; split_ifs <;> simp [Function.extend]
  map_one' := by
    ext n
    split_ifs with hq
    · by_cases hn : ∃ k, q ^ k = n
      · obtain ⟨a, rfl⟩ := hn
        simp [(Nat.pow_right_injective hq).extend_apply, one_apply, hq.ne']
      · simp [hn, one_apply_ne (fun H ↦ hn ⟨0, H.symm⟩)]
    · simp
  map_add' f g := by
    ext n
    split_ifs with hq
    · by_cases h : ∃ a, q ^ a = n
      · obtain ⟨a, rfl⟩ := h
        simp [(Nat.pow_right_injective hq).extend_apply]
      · simp [h]
    · by_cases hn : n = 1 <;> simp [hn]
  map_mul' f g := by
    ext n
    split_ifs with hq
    · simp_rw [mul_apply, coe_mk]
      by_cases hn : ∃ a, q ^ a = n
      · obtain ⟨k, rfl⟩ := hn
        rw [(Nat.pow_right_injective hq).extend_apply]
        have hs : (Finset.antidiagonal k).map (.prodMap ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩
            ⟨fun k ↦ q ^ k, Nat.pow_right_injective hq⟩) ⊆ (q ^ k).divisorsAntidiagonal := by
          intro k hk
          obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hk
          rw [Finset.mem_antidiagonal] at hi
          simp [Nat.mem_divisorsAntidiagonal, ← hi, pow_add, ne_zero_of_lt hq]
        rw [PowerSeries.coeff_mul k f g, ← Finset.sum_subset hs]
        · simp [(Nat.pow_right_injective hq).extend_apply]
        · intro (a, b) hab h
          by_cases ha : ∃ i, q ^ i = a
          · by_cases hb : ∃ j, q ^ j = b
            · obtain ⟨i, rfl⟩ := ha
              obtain ⟨j, rfl⟩ := hb
              rw [Nat.mem_divisorsAntidiagonal, ← pow_add, Nat.pow_right_inj hq] at hab
              simp_rw [Finset.mem_map, not_exists, not_and, Finset.mem_antidiagonal] at h
              simpa using h (i, j) hab.1
            · rwa [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
          · rwa [Function.extend_apply', Pi.zero_apply, zero_mul]
      · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply, Finset.sum_eq_zero]
        intro (a, b) hk
        obtain ⟨hab, -⟩ := Nat.mem_divisorsAntidiagonal.mp hk
        by_cases ha : ∃ i, q ^ i = a
        · by_cases hb : ∃ j, q ^ j = b
          · obtain ⟨i, rfl⟩ := ha
            obtain ⟨j, rfl⟩ := hb
            rw [← pow_add] at hab
            exact (hn ⟨i + j, hab⟩).elim
          · rwa [mul_comm, Function.extend_apply', Pi.zero_apply, zero_mul]
        · rwa [Function.extend_apply', Pi.zero_apply, zero_mul]
    · simp
  commutes' x := by
    ext n
    split_ifs with hq
    · simp only [Algebra.algebraMap_eq_smul_one, coe_mk]
      by_cases hn : ∃ k, q ^ k = n
      · obtain ⟨k, rfl⟩ := hn
        simp [(Nat.pow_right_injective hq).extend_apply, one_apply, hq.ne']
      · rw [Function.extend_apply' _ _ _ hn, Pi.zero_apply, smul_map, one_apply_ne, smul_zero]
        contrapose! hn
        exact ⟨0, by simp [hn]⟩
    · simp

theorem ofPowerSeries_apply (q : ℕ) (hq : 1 < q) (f : PowerSeries R) (n : ℕ) :
    ofPowerSeries q f n = Function.extend (q ^ ·) (f.coeff ·) 0 n := by
  simp [ofPowerSeries, dif_pos hq]

theorem ofPowerSeries_apply_pow (q : ℕ) (hq : 1 < q) (f : PowerSeries R) (k : ℕ) :
    ofPowerSeries q f (q ^ k) = f.coeff k := by
  rw [ofPowerSeries_apply q hq, (Nat.pow_right_injective hq).extend_apply]

theorem ofPowerSeries_apply_zero (q : ℕ) (f : PowerSeries R) : ofPowerSeries q f 0 = 0 := by
  simp

@[simp]
theorem ofPowerSeries_apply_one (q : ℕ) (f : PowerSeries R) :
    ofPowerSeries q f 1 = f.constantCoeff := by
  by_cases hq : 1 < q
  · rw [← pow_zero q, ofPowerSeries_apply_pow q hq, PowerSeries.coeff_zero_eq_constantCoeff]
  · simp [ofPowerSeries, dif_neg hq]

variable {R : Type*} [CommRing R]

theorem ofPowerSeries_pow (q k : ℕ) (hk : k ≠ 0) (f : PowerSeries R) :
    ofPowerSeries (q ^ k) f = ofPowerSeries q (f.subst (PowerSeries.X ^ k)) := by
  by_cases hq : 1 < q
  · ext n
    by_cases hn : ∃ i, q ^ i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [ofPowerSeries_apply_pow q hq, PowerSeries.coeff_subst_X_pow hk]
      split_ifs with hn
      · obtain ⟨j, rfl⟩ := hn
        rw [pow_mul, ofPowerSeries_apply_pow (q ^ k) (one_lt_pow' hq hk)]
        simp [hk]
      · rw [ofPowerSeries_apply (q ^ k) (one_lt_pow' hq hk), Function.extend_apply', Pi.zero_apply]
        contrapose! hn
        obtain ⟨d, hd⟩ := hn
        rw [← pow_mul, Nat.pow_right_inj hq] at hd
        rw [← hd]
        use d
    · rwa [ofPowerSeries_apply q hq, ofPowerSeries_apply (q ^ k) (one_lt_pow' hq hk),
        Function.extend_apply', Function.extend_apply']
      contrapose! hn
      obtain ⟨i, rfl⟩ := hn
      exact ⟨k * i, pow_mul q k i⟩
  · simp [ofPowerSeries, hq, hk]

theorem isMultiplicative_ofPowerSeries
    (q : ℕ) (hq : IsPrimePow q) (f : PowerSeries R) (hf : f.constantCoeff = 1) :
    IsMultiplicative (ofPowerSeries q f) := by
  have hq' : 1 < q := hq.one_lt
  refine ⟨(ofPowerSeries_apply_one q f).trans hf, ?_⟩
  intro m n hmn
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  rw [← Nat.prime_iff] at hp
  rw [ofPowerSeries_pow p k hk.ne']
  by_cases hm : ∃ i, p ^ i = m
  · obtain ⟨i, rfl⟩ := hm
    by_cases hn : ∃ j, p ^ j = n
    · obtain ⟨j, rfl⟩ := hn
      cases i
      · simp [hk.ne', hf]
      · cases j
        · simp [hk.ne', hf]
        · simp [hp.ne_one] at hmn
    · simp_rw [ofPowerSeries_apply p hp.one_lt]
      rw [Function.extend_apply', Pi.zero_apply,
        Function.extend_apply' _ _ _ hn, Pi.zero_apply, mul_zero]
      · contrapose! hn
        obtain ⟨j, hj⟩ := hn
        obtain ⟨v, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hj.symm)
        exact ⟨v, rfl⟩
  · simp_rw [ofPowerSeries_apply p hp.one_lt]
    rw [Function.extend_apply', Pi.zero_apply, Function.extend_apply' _ _ _ hm,
      Pi.zero_apply, zero_mul]
    contrapose! hm
    obtain ⟨i, hi⟩ := hm
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp ⟨n, hi⟩
    exact ⟨j, rfl⟩

end PowerSeries

section EulerProduct

variable {ι R : Type*} [CommSemiring R]

/-- A private uniform space instance on `ArithmeticFunction R` in order to define `eulerProduct` as
a `tprod`. If `R` is viewed as having the discrete topology, then the resulting topology on
`ArithmeticFunction R` is the topology of pointwise convergence (see `tendsto_iff`).

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance uniformSpace : UniformSpace (ArithmeticFunction R) :=
  letI : UniformSpace R := ⊥
  .comap ((↑) : ArithmeticFunction R → (ℕ → R)) inferInstance

/-- A family `f i : ArithmeticFunction R` tends to `g` if and only if for each `n`, the `n`th
coefficient of `f i` is eventually equal to the `n`th coefficient of `g`. If `R` is viewed as
having the discrete topology, then this is the topology of pointwise convergence.

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
private theorem tendsto_iff
    {f : ι → ArithmeticFunction R} {F : Filter ι} {g : ArithmeticFunction R} :
    Tendsto f F (nhds g) ↔ ∀ n, ∀ᶠ i in F, f i n = g n := by
  let : UniformSpace R := ⊥
  have : Topology.IsInducing ((↑) : ArithmeticFunction R → (ℕ → R)) := ⟨rfl⟩
  simp [this.tendsto_nhds_iff, tendsto_pi_nhds]

/-- The uniform space structure on arithmetic functions is complete.

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance : CompleteSpace (ArithmeticFunction R) := by
  let : UniformSpace R := ⊥
  apply IsUniformInducing.completeSpace ⟨rfl⟩
  apply IsClosed.isComplete
  have : Set.range ((↑) : ArithmeticFunction R → (ℕ → R)) = {f | f 0 = 0} := by
    ext f
    exact ⟨by rintro ⟨f, rfl⟩; simp, fun hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩
  rw [ArithmeticFunction.range_coe]
  apply isClosed_setOf_map_zero

/-- The Euler product of a family of arithmetic functions. Defined as a `tprod`, but see
`tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
noncomputable def eulerProduct (f : ι → ArithmeticFunction R) : ArithmeticFunction R :=
  ∏' i, f i

/-- If arithmetic functions `f i` converges to `1` pointwise, then the partial products
`∏ i ∈ s, f i` converge to `eulerProduct f` pointwise. -/
theorem tendsTo_eulerProduct_of_tendsTo (f : ι → ArithmeticFunction R)
    (hf : ∀ n, ∀ᶠ i in cofinite, f i n = (1 : ArithmeticFunction R) n) :
    ∀ n, ∀ᶠ s in atTop, (∏ i ∈ s, f i) n = eulerProduct f n := by
  let : UniformSpace R := ⊥
  have : IsUniformInducing ((↑) : ArithmeticFunction R → (ℕ → R)) := ⟨rfl⟩
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, ← this.cauchy_map_iff,
    Filter.map_map, cauchy_map_iff', Pi.uniformity, DiscreteUniformity.eq_principal_setRelId,
    tendsto_iInf, tendsto_comap_iff, tendsto_principal, Function.comp_apply, prod_atTop_atTop_eq,
    eventually_atTop_prod_self, SetRel.mem_id]
  intro n
  replace hf : ∀ k ∈ Set.Iic n, ∀ᶠ (x : ι) in cofinite, (f x) k = (1 : ArithmeticFunction R) k :=
    fun k hk ↦ hf k
  rw [← eventually_all_finite (Set.finite_Iic n), eventually_iff_exists_mem] at hf
  obtain ⟨s, hs, hs'⟩ := hf
  let t := (mem_cofinite.mp hs).toFinset
  refine ⟨t, fun u v hu hv ↦ ?_⟩
  rw [← Finset.prod_sdiff hu, ← Finset.prod_sdiff hv]
  replace hu : ∀ i ∈ u \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  replace hv : ∀ i ∈ v \ t, i ∈ s := by
    intro i hi
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.notMem_compl_iff] at hi
    exact hi.2
  suffices ∀ k ≤ n, (∏ x ∈ u \ t, f x) k = (∏ x ∈ v \ t, f x) k by
    rw [mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [this k.1 (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hk))]
  suffices ∀ w, (∀ i ∈ w, i ∈ s) → ∀ k ≤ n, (∏ x ∈ w, f x) k = (1 : ArithmeticFunction R) k by
    intro k hk
    rw [this (u \ t) hu k hk, this (v \ t) hv k hk]
  intro w hw
  induction w using Finset.induction_on
  case empty => simp
  case insert i w hi hw' =>
    intro k hk
    rw [← one_mul (1 : ArithmeticFunction R), Finset.prod_insert hi, mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have h1 := hs' i (hw i (Finset.mem_insert_self i w)) j.1
      ((Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    have h2 := hw' (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) j.2
      ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hj)).trans hk)
    rw [h1, h2]

theorem isMultiplicative_eulerProduct (f : ι → ArithmeticFunction R)
    (hf : ∀ i, IsMultiplicative (f i)) : IsMultiplicative (eulerProduct f) := by
  by_cases hf' : Multipliable f
  · have h (s : Finset ι) : (∏ b ∈ s, f b).IsMultiplicative :=
      isMultiplicative_finsetProd f s fun i a ↦ hf i
    have key := tendsto_iff.mp hf'.hasProd
    refine (forall_and.mp h).imp (fun h ↦ ?_) fun h m n hmn ↦ ?_
    · specialize key 1
      simp_rw [h] at key
      rwa [eventually_const, eq_comm] at key
    · replace h s : (∏ b ∈ s, f b) (m * n) = (∏ b ∈ s, f b) m * (∏ b ∈ s, f b) n := h s hmn
      have h2 := key (m * n)
      simp_rw [h] at h2
      exact eventually_const.mp (EventuallyEq.trans (.symm h2) (.mul (key m) (key n)))
  · rw [eulerProduct, tprod_eq_one_of_not_multipliable hf']
    exact isMultiplicative_one

/-- Given arithmetic functions `f(q⁻ˢ)` with `q → ∞`, the partial products `∏ i ∈ s, f i` converge
to the Euler product pointwise. -/
theorem tendsTo_eulerProduct_ofPowerSeries
    (f : ι → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 1)
    (q : ι → ℕ) [hq : Northcott q] (n : ℕ) :
    ∀ᶠ s in atTop, (∏ i ∈ s, ArithmeticFunction.ofPowerSeries (q i) (f i)) n =
      eulerProduct (fun i ↦ ArithmeticFunction.ofPowerSeries (q i) (f i)) n := by
  apply tendsTo_eulerProduct_of_tendsTo
  refine fun n ↦ (tendsto_atTop.mp ((northcott_iff_tendsto q).mp hq) (n + 1)).mono fun i hi ↦ ?_
  by_cases hn0 : n = 0
  · rw [hn0, map_zero, map_zero]
  · by_cases hn1 : n = 1
    · rw [hn1, ofPowerSeries_apply_one, hf, one_one]
    · have hqi : 1 < q i := by grind
      rw [ofPowerSeries_apply (q i) hqi, Function.extend_apply', Pi.zero_apply, one_apply_ne hn1]
      contrapose! hn1
      obtain ⟨k, rfl⟩ := hn1
      conv_rhs at hi => rw [← pow_one (q i)]
      rw [Nat.add_one_le_iff, Nat.pow_lt_pow_iff_right hqi, Nat.lt_one_iff] at hi
      rw [hi, pow_zero]

end EulerProduct

end ArithmeticFunction

-- TODO: Prove that LSeries converges
