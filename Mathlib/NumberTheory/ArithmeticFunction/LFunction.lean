/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

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

-- PRed
namespace ArithmeticFunction

instance {R : Type*} [Semiring R] : Module R (ArithmeticFunction R) where
  smul x f := ⟨x • f, by simp⟩
  smul_zero x := ext fun n ↦ smul_zero x
  smul_add x f g := ext fun n ↦ smul_add x (f n) (g n)
  zero_smul f := ext fun n ↦ zero_smul R (f n)
  one_smul f := ext fun n ↦ one_smul R (f n)
  add_smul x y f := ext fun n ↦ add_smul x y (f n)
  mul_smul x y f := ext fun n ↦ mul_smul x y (f n)

@[simp]
theorem smul_map {R : Type*} [Semiring R] (x : R) (f : ArithmeticFunction R) (n : ℕ) :
    (x • f) n = x • f n := by
  rfl

instance {R : Type*} [CommSemiring R] : Algebra R (ArithmeticFunction R) :=
  .ofModule (fun x f g ↦ ext fun n ↦ by simp [mul_assoc, Finset.mul_sum])
    fun x f g ↦ ext fun n ↦ by simp [mul_assoc, mul_comm x, Finset.sum_mul]

@[simp]
theorem algebraMap_map_one {R : Type*} [CommSemiring R] (x : R) :
    algebraMap R (ArithmeticFunction R) x 1 = x := by
  simp [Algebra.algebraMap_eq_smul_one]

end ArithmeticFunction

namespace ArithmeticFunction

section PowerSeries

variable {R : Type*} [CommSemiring R]

set_option backward.isDefEq.respectTransparency false in
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

@[simp]
theorem ofPowerSeries_apply_zero (q : ℕ) (f : PowerSeries R) : ofPowerSeries q f 0 = 0 := by
  simp

@[simp]
theorem ofPowerSeries_apply_one (q : ℕ) (f : PowerSeries R) :
    ofPowerSeries q f 1 = f.constantCoeff := by
  by_cases hq : 1 < q
  · rw [ofPowerSeries_apply q hq, ← pow_zero q, (Nat.pow_right_injective hq).extend_apply,
      PowerSeries.coeff_zero_eq_constantCoeff]
  · simp [ofPowerSeries, dif_neg hq]

theorem _root_.PowerSeries.constantCoeff_subst' {R : Type*} [CommRing R] {a : PowerSeries R}
    (ha : PowerSeries.HasSubst a) (f : PowerSeries R) :
    PowerSeries.constantCoeff (PowerSeries.subst a f) =
      finsum (fun d ↦ f.coeff d • (a ^ d).constantCoeff) :=
  PowerSeries.constantCoeff_subst ha f

@[simp]
theorem _root_.PowerSeries.constantCoeff_subst_X_pow
    {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    PowerSeries.constantCoeff (f.subst (PowerSeries.X (R := R) ^ k)) = f.constantCoeff := by
  rw [PowerSeries.constantCoeff_subst' (.X_pow hk), finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hk, hn]

variable {R : Type*} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
theorem ofPowerSeries_pow (q k : ℕ) (hk : k ≠ 0) (f : PowerSeries R) :
    ofPowerSeries (q ^ k) f = ofPowerSeries q (f.subst (PowerSeries.X ^ k)) := by
  by_cases hq : 1 < q
  · ext n
    rw [ofPowerSeries_apply (q ^ k) (one_lt_pow' hq hk), ofPowerSeries_apply q hq]
    by_cases hn : ∃ i, q ^ i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [(Nat.pow_right_injective hq).extend_apply, PowerSeries.coeff_subst' (.X_pow hk)]
      have : ∀ d, ((PowerSeries.X (R := R) ^ k) ^ d) = PowerSeries.X ^ (k * d) := by simp [pow_mul]
      simp_rw [this, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hn : k ∣ i
      · obtain ⟨j, rfl⟩ := hn
        rw [pow_mul, (Nat.pow_right_injective (one_lt_pow' hq hk)).extend_apply,
          finsum_eq_single _ j]
        · simp
        · intro i hi
          simp [hi.symm, hk]
      · rw [Function.extend_apply', Pi.zero_apply, finsum_eq_zero_of_forall_eq_zero]
        · intro d
          apply if_neg
          contrapose! hn
          use d
        · contrapose! hn
          obtain ⟨d, hd⟩ := hn
          rw [← pow_mul, Nat.pow_right_inj hq] at hd
          rw [← hd]
          use d
    · rwa [Function.extend_apply', Function.extend_apply']
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

open Filter

variable {ι R : Type*} [CommSemiring R]

/-- A private uniform space instance on `ArithmeticFunction R` in order to define `eulerProduct` as
a `tprod`. If `R` is viewed as having the discrete topology, then the resulting topology on
`ArithmeticFunction R` is the topology of pointwise convergence (see `tendsto_iff`).

See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
local instance : UniformSpace (ArithmeticFunction R) :=
  .comap ((↑) : ArithmeticFunction R → (ℕ → R)) <| .ofCore <|
    .mk (⨅ s : Finset ℕ, 𝓟 {(f, g) | Set.EqOn f g s})
      (by simp [Set.subset_def, Set.eqOn_refl])
      (tendsto_iInf_iInf fun _ ↦ tendsto_principal_principal.mpr fun _ ↦ Set.EqOn.symm)
      (le_iInf fun s ↦ by
        have key := iInf_le (fun t : Finset ℕ ↦ 𝓟 {(f, g) : (ℕ → R) × (ℕ → R) | Set.EqOn f g t}) s
        exact lift'_le (le_principal_iff.mp key) (by grind [principal_mono, SetRel.comp, Set.EqOn]))

/-- The uniformity on `ArithmeticFunction` required in order to define `eulerProduct` as a `tprod`.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
theorem uniformity_eq : uniformity (ArithmeticFunction R) =
    comap (fun i ↦ (i.1, i.2)) ((⨅ s : Finset ℕ, 𝓟 {((f : ℕ → R), g) | Set.EqOn f g s})) :=
  rfl

/-- The topology on `ArithmeticFunction` is the topology of pointwise convergence.
See `tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
theorem tendsto_iff {f : ι → ArithmeticFunction R} {F : Filter ι} {g : ArithmeticFunction R} :
    Tendsto f F (nhds g) ↔ ∀ n, Filter.Tendsto (fun i ↦ f i n) F (pure (g n)) := by
  simp_rw [nhds_eq_comap_uniformity,
    uniformity_eq, tendsto_comap_iff, tendsto_iInf, tendsto_principal, Function.comp_apply,
    tendsto_pure, Set.EqOn, Finset.mem_coe, Set.mem_setOf_eq, eventually_all_finset, eq_comm]
  exact ⟨fun h n ↦ by simpa using h { n }, fun h s k hk ↦ h k⟩

instance : CompleteSpace (ArithmeticFunction R) where
  complete {f} hf := by
    simp_rw [Cauchy] at hf
    simp_rw [nhds_eq_comap_uniformity]
    simp_rw [uniformity_eq, comap_iInf, comap_principal, le_iInf_iff, le_principal_iff,
      Set.preimage_setOf_eq] at hf ⊢
    obtain ⟨hf0, hf⟩ := hf
    have hf' (i : ℕ) : _ := hf {i}
    simp_rw [Finset.coe_singleton, Set.eqOn_singleton, mem_prod_self_iff] at hf'
    replace hf' : ∀ i, ∃ x : R, {a | x = a i} ∈ f := by
      intro i
      obtain ⟨t, htf, ht⟩ := hf' i
      obtain ⟨g₁, hg₁⟩ := hf0.nonempty_of_mem htf
      use g₁ i
      apply Filter.mem_of_superset htf
      intro g₂ hg₂
      exact @ht (g₁, g₂) ⟨hg₁, hg₂⟩
    choose g hg using hf'
    refine ⟨⟨g, ?_⟩, fun s ↦ ?_⟩
    · specialize hg 0
      contrapose! hg
      simp [hg]
    · simp_rw [coe_mk, Set.EqOn, Finset.mem_coe, Set.setOf_forall, biInter_finset_mem]
      exact fun i hi ↦ hg i

/-- The Euler product of a family of arithmetic functions. Defined as a `tprod`, but see
`tendsTo_eulerProduct_of_tendsTo` for the outward facing `eulerProduct` API. -/
noncomputable def eulerProduct (f : ι → ArithmeticFunction R) : ArithmeticFunction R :=
  ∏' i, f i

/-- If arithmetic functions `f i` converges to `1` pointwise, then the partial products
`∏ i ∈ s, f i` converge to `eulerProduct f` pointwise. -/
theorem tendsTo_eulerProduct_of_tendsTo (f : ι → ArithmeticFunction R)
    (hf : ∀ n, Tendsto (fun i ↦ f i n) cofinite (pure ((1 : ArithmeticFunction R) n))) :
    ∀ n, Tendsto (fun s ↦ (∏ i ∈ s, f i) n) atTop (pure (eulerProduct f n)) := by
  classical
  suffices Multipliable f from tendsto_iff.mp this.hasProd
  simp_rw [multipliable_iff_cauchySeq_finset, CauchySeq, cauchy_map_iff',
    uniformity_eq, tendsto_comap_iff, tendsto_iInf, tendsto_principal, Function.comp_apply,
    Set.EqOn, Finset.mem_coe, Set.mem_setOf_eq, eventually_all_finset]
  intro s n hn
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self]
  replace hf : ∀ k ∈ Set.Iic n, ∀ᶠ (x : ι) in cofinite, (f x) k = (1 : ArithmeticFunction R) k :=
    fun k hk ↦ tendsto_pure.mp (hf k)
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
  have key w (hw : ∀ i ∈ w, i ∈ s) : ∀ k ≤ n, (∏ x ∈ w, f x) k = (1 : ArithmeticFunction R) k := by
    induction w using Finset.induction_on
    case empty => simp
    case insert i w hi hw' =>
      intro k hk
      rw [← one_mul (1 : ArithmeticFunction R)]
      rw [Finset.prod_insert hi, mul_apply, mul_apply]
      apply Finset.sum_congr rfl
      intro j hj
      have h1 := hs' i (hw i (Finset.mem_insert_self i w)) j.1
        ((Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hj)).trans hk)
      have h2 := hw' (fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)) j.2
        ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hj)).trans hk)
      rw [h1, h2]
  intro k hk
  rw [key (u \ t) hu k hk, key (v \ t) hv k hk]

/-- Given arithmetic functions `f(q⁻ˢ)` with `q → ∞`, the partial products `∏ i ∈ s, f i` converge
to the Euler product pointwise. -/
theorem tendsTo_eulerProduct_ofPowerSeries
    (f : ι → PowerSeries R) (hf : ∀ i, (f i).constantCoeff = 1)
    (q : ι → ℕ) [hq : Northcott q] :
    ∀ n, Tendsto (fun s ↦ (∏ i ∈ s, ArithmeticFunction.ofPowerSeries (q i) (f i)) n) atTop
      (pure (eulerProduct (fun i ↦ ArithmeticFunction.ofPowerSeries (q i) (f i)) n)) := by
  apply tendsTo_eulerProduct_of_tendsTo
  intro n
  have key := (northcott_iff_tendsto q).mp hq
  sorry

theorem IsMultiplicative.finsetProd (f : ι → ArithmeticFunction R) (s : Finset ι)
    (hf : ∀ i ∈ s, IsMultiplicative (f i)) : IsMultiplicative (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction
  case empty => simp [isMultiplicative_one] -- make simp
  case insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (s.mem_insert_self a)).mul (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

theorem foo {α β : Type*} {F : Filter α} [F.NeBot] {f : α → β} {b₁ b₂ : β}
    (h₁ : F.Tendsto f (pure b₁)) (h₂ : F.Tendsto f (pure b₂)) : b₁ = b₂ := by
  rw [tendsto_pure, eventually_iff_exists_mem] at h₁ h₂
  obtain ⟨u, huF, hu⟩ := h₁
  obtain ⟨v, hvF, hv⟩ := h₂
  obtain ⟨a, hau, hav⟩ := nonempty_of_mem (inter_mem huF hvF)
  exact (hu a hau).symm.trans (hv a hav)

theorem isMultiplicative_eulerProduct (f : ι → ArithmeticFunction R)
    (hf : ∀ i, IsMultiplicative (f i)) : IsMultiplicative (eulerProduct f) := by
  by_cases hf' : Multipliable f
  · have key (s : Finset ι) : (∏ b ∈ s, f b).IsMultiplicative :=
      .finsetProd f s fun i a ↦ hf i
    simp_rw [IsMultiplicative, forall_and] at key
    obtain ⟨key1, key2⟩ := key
    have key3 : ∀ n, Tendsto (fun s ↦ (∏ b ∈ s, f b) n) atTop (pure (eulerProduct f n)) :=
      tendsto_iff.mp hf'.hasProd
    constructor
    · specialize key3 1
      simp_rw [key1] at key3
      rwa [tendsto_pure, eventually_const, eq_comm] at key3
    · intro m n hmn
      have h1 := (key3 m).prodMk (key3 n)
      have h2 := key3 (m * n)
      rw [prod_pure_pure] at h1
      simp_rw [forall_comm.mp (forall_comm.mp (forall_comm.mp key2 m) n) hmn] at h2
      exact foo h2
        ((tendsto_pure_pure (fun x ↦ x.1 * x.2) (eulerProduct f m, eulerProduct f n)).comp h1)
  · rw [eulerProduct, tprod_eq_one_of_not_multipliable hf']
    exact isMultiplicative_one

end EulerProduct

end ArithmeticFunction

-- TODO: Prove that LSeries converges
