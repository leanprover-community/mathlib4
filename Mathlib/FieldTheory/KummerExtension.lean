/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.FieldTheory.Galois
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Norm
/-!
# Kummer Extensions

## Main result
- `isCyclic_tfae`:
Suppose `L/K` is a finite extension of dimension `n`, and `K` contains all `n`-th roots of unity.
Then `L/K` is cyclic iff
`L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
`L = K[α]` for some `αⁿ ∈ K`.

- `autEquivRootsOfUnity`:
Given an instance `IsSplittingField K L (X ^ n - C a)`
(perhaps via `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`),
then the galois group is isomorphic to `rootsOfUnity n K`, by sending
`σ ↦ σ α / α` for `α ^ n = a`, and the inverse is given by `μ ↦ (α ↦ μ • α)`.

- `autEquivZmod`:
Furthermore, given an explicit choice `ζ` of a primitive `n`-th root of unity, the galois group is
then isomorphic to `Multiplicative (ZMod n)` whose inverse is given by
`i ↦ (α ↦ ζⁱ • α)`.

## Other results
Criteria for `X ^ n - C a` to be irreducible is given:
- `X_pow_sub_C_irreducible_iff_of_prime`:
  For `n = p` a prime, `X ^ n - C a` is irreducible iff `a` is not a `p`-power.
- `X_pow_sub_C_irreducible_iff_of_prime_pow`:
  For `n = p ^ k` an odd prime power, `X ^ n - C a` is irreducible iff `a` is not a `p`-power.
- `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `p`-power for all prime `p ∣ n`.
- `X_pow_sub_C_irreducible_iff_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `d`-power for `d ∣ n` and `d ≠ 1`.

TODO: criteria for even `n`. See [serge_lang_algebra] VI,§9.

-/
universe u

variable {K : Type u} [Field K]

open Polynomial IntermediateField AdjoinRoot

section Splits

lemma root_X_pow_sub_C_pow (n : ℕ) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a := by
  rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]

lemma root_X_pow_sub_C_ne_zero {n : ℕ} (hn : 1 < n) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 :=
  mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (Nat.not_eq_zero_of_lt hn))
    X_ne_zero <| by rwa [natDegree_X_pow_sub_C, natDegree_X]

lemma root_X_pow_sub_C_ne_zero' {n : ℕ} {a : K} (hn : 0 < n) (ha : a ≠ 0) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 := by
  obtain (rfl|hn) := (Nat.succ_le_iff.mpr hn).eq_or_lt
  · rw [← Nat.one_eq_succ_zero, pow_one]
    intro e
    refine mk_ne_zero_of_natDegree_lt (monic_X_sub_C a) (C_ne_zero.mpr ha) (by simp) ?_
    trans AdjoinRoot.mk (X - C a) (X - (X - C a))
    · rw [sub_sub_cancel]
    · rw [map_sub, mk_self, sub_zero, mk_X, e]
  · exact root_X_pow_sub_C_ne_zero hn a

theorem X_pow_sub_C_splits_of_isPrimitiveRoot
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (e : α ^ n = a) :
    (X ^ n - C a).Splits (RingHom.id _) := by
  cases n.eq_zero_or_pos with
  | inl hn =>
    rw [hn, pow_zero, ← C.map_one, ← map_sub]
    exact splits_C _ _
  | inr hn =>
    rw [splits_iff_card_roots, ← nthRoots, hζ.card_nthRoots, natDegree_X_pow_sub_C, if_pos ⟨α, e⟩]

open BigOperators

theorem X_pow_sub_C_eq_prod
    {n : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i in Finset.range n, (X - C (ζ ^ i * α)) := by
  rw [eq_prod_roots_of_monic_of_splits_id (monic_X_pow_sub_C _ (Nat.pos_iff_ne_zero.mp hn))
    (X_pow_sub_C_splits_of_isPrimitiveRoot hζ e), ← nthRoots, hζ.nthRoots_eq e, Multiset.map_map]
  rfl

end Splits

section Irreducible

lemma ne_zero_of_irreducible_X_pow_sub_C {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    n ≠ 0 := by
  rintro rfl
  rw [pow_zero, ← C.map_one, ← map_sub] at H
  exact not_irreducible_C _ H

lemma ne_zero_of_irreducible_X_pow_sub_C' {n : ℕ} (hn : n ≠ 1) {a : K}
    (H : Irreducible (X ^ n - C a)) : a ≠ 0 := by
  rintro rfl
  rw [map_zero, sub_zero] at H
  exact not_irreducible_pow hn H

lemma root_X_pow_sub_C_eq_zero_iff {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a = 0 := by
  have hn := (Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H))
  refine ⟨not_imp_not.mp (root_X_pow_sub_C_ne_zero' hn), ?_⟩
  rintro rfl
  have := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) rfl
  rw [this, pow_one, map_zero, sub_zero, ← mk_X, mk_self]

lemma root_X_pow_sub_C_ne_zero_iff {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 ↔ a ≠ 0 :=
  (root_X_pow_sub_C_eq_zero_iff H).not

theorem pow_ne_of_irreducible_X_pow_sub_C {n : ℕ} {a : K}
    (H : Irreducible (X ^ n - C a)) {m : ℕ} (hm : m ∣ n) (hm' : m ≠ 1) (b : K) : b ^ m ≠ a := by
  have hn : n ≠ 0 := fun e ↦ not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm, pow_mul, map_pow, hq] at H
  have : degree q = 0 := by
    simpa [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C,
      Nat.pos_iff_ne_zero, (mul_ne_zero_iff.mp hn).2] using H.2 _ q rfl
  apply_fun degree at hq
  simp only [this, ← pow_mul, mul_comm k m, degree_X_pow_sub_C, Nat.pos_iff_ne_zero.mpr hn,
    Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2, degree_mul, ← map_pow, add_zero,
    Nat.cast_injective.eq_iff] at hq
  exact hm' ((mul_eq_right₀ (mul_ne_zero_iff.mp hn).2).mp hq)

theorem X_pow_sub_C_irreducible_of_prime {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a) := by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hp.pos, Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor this (X_pow_sub_C_ne_zero hp.pos a)
  -- It suffices to show that `deg g = p`.
  suffices natDegree g = p from (associated_of_dvd_of_natDegree_le hg'
    (X_pow_sub_C_ne_zero hp.pos a) (this.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg
  -- Suppose `deg g ≠ p`.
  by_contra h
  have : Fact (Irreducible g) := ⟨hg⟩
  -- Let `r` be a root of `g`, then `N_K(r) ^ p = N_K(r ^ p) = N_K(a) = a ^ (deg g)`.
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ p = a ^ g.natDegree := by
    have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hg' (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at this
    rw [← map_pow, this, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
      ← finrank_top', ← IntermediateField.adjoin_root_eq_top g,
      IntermediateField.adjoin.finrank,
      AdjoinRoot.minpoly_root hg.ne_zero, natDegree_mul_C]
    · simpa using hg.ne_zero
    · exact AdjoinRoot.isIntegral_root hg.ne_zero
  -- Since `a ^ (deg g)` is a `p`-power, and `p` is coprime to `deg g`, we conclude that `a` is
  -- also a `p`-power, contradicting the hypothesis
  have : p.Coprime (natDegree g) := hp.coprime_iff_not_dvd.mpr (fun e ↦ h (((natDegree_le_of_dvd hg'
    (X_pow_sub_C_ne_zero hp.pos a)).trans_eq natDegree_X_pow_sub_C).antisymm (Nat.le_of_dvd
      (natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg) e)))
  exact ha _ ((pow_mem_range_pow_of_coprime this.symm a).mp ⟨_, key⟩).choose_spec

theorem X_pow_sub_C_irreducible_iff_of_prime {p : ℕ} (hp : p.Prime) {a : K} :
    Irreducible (X ^ p - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · dvd_rfl hp.ne_one), X_pow_sub_C_irreducible_of_prime hp⟩

theorem X_pow_mul_sub_C_irreducible
    {n m : ℕ} {a : K} (hm : Irreducible (X ^ m - C a))
    (hn : ∀ (E : Type u) [Field E] [Algebra K E] (x : E) (hx : minpoly K x = X ^ m - C a),
      Irreducible (X ^ n - C (AdjoinSimple.gen K x))) :
    Irreducible (X ^ (n * m) - C a) := by
  have hm' : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, ← C.map_one, ← map_sub] at hm
    exact not_irreducible_C _ hm
  simpa [pow_mul] using irreducible_comp (monic_X_pow_sub_C a hm') (monic_X_pow n) hm
    (by simpa only [Polynomial.map_pow, map_X] using hn)

-- TODO: generalize to even `n`
theorem X_pow_sub_C_irreducible_of_odd
    {n : ℕ} (hn : Odd n) {a : K} (ha : ∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ n - C a) := by
  induction n using induction_on_primes generalizing K a with
  | h₀ => simp at hn
  | h₁ => simpa using irreducible_X_sub_C a
  | h p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have : IsIntegral K x := not_not.mp fun h ↦ by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos,
        WithBot.nat_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
    apply IH (Nat.odd_mul.mp hn).2
    intros q hq hqn b hb
    apply ha q hq (dvd_mul_of_dvd_right hqn p) (Algebra.norm _ b)
    rw [← map_pow, hb, ← adjoin.powerBasis_gen this,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [minpoly_gen, hx, hp.ne_zero.symm, (Nat.odd_mul.mp hn).1.neg_pow]

theorem X_pow_sub_C_irreducible_iff_forall_prime_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ p : ℕ, p.Prime → p ∣ n → ∀ b : K, b ^ p ≠ a) :=
  ⟨fun e _ hp hpn ↦ pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_odd hn⟩

theorem X_pow_sub_C_irreducible_iff_of_odd {n : ℕ} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (∀ d, d ∣ n → d ≠ 1 → ∀ b : K, b ^ d ≠ a) :=
  ⟨fun e _ ↦ pow_ne_of_irreducible_X_pow_sub_C e,
    fun H ↦ X_pow_sub_C_irreducible_of_odd hn fun p hp hpn ↦ (H p hpn hp.ne_one)⟩

-- TODO: generalize to `p = 2`
theorem X_pow_sub_C_irreducible_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) (n : ℕ) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ (p ^ n) - C a) := by
  apply X_pow_sub_C_irreducible_of_odd (hp.odd_of_ne_two hp').pow
  intros q hq hq'
  simpa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq')] using ha

theorem X_pow_sub_C_irreducible_iff_of_prime_pow
    {p : ℕ} (hp : p.Prime) (hp' : p ≠ 2) {n} (hn : n ≠ 0) {a : K} :
    Irreducible (X ^ p ^ n - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · (dvd_pow dvd_rfl hn) hp.ne_one),
    X_pow_sub_C_irreducible_of_prime_pow hp hp' n⟩

end Irreducible

/-!
### Galois Group of `K[n√a]`
We first develop the theory for a specific `K[n√a] := AdjoinRoot (X ^ n - C a)`.
The main result is the description of the galois group: `autAdjoinRootXPowSubCEquiv`.
-/

variable {n : ℕ} (hζ : (primitiveRoots n K).Nonempty) (hn : 0 < n)
variable (a : K) (H : Irreducible (X ^ n - C a))

set_option quotPrecheck false in
scoped[KummerExtension] notation3 "K[" n "√" a "]" => AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)

attribute [nolint docBlame] KummerExtension.«termK[_√_]»

open scoped KummerExtension

section AdjoinRoot

/-- Also see `Polynomial.separable_X_pow_sub_C_unit` -/
theorem Polynomial.separable_X_pow_sub_C_of_irreducible : (X ^ n - C a).Separable := by
  letI := Fact.mk H
  letI : Algebra K K[n√a] := inferInstance
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  by_cases hn' : n = 1
  · rw [hn', pow_one]; exact separable_X_sub_C
  have ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
  rw [← separable_map (algebraMap K K[n√a]), Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
    algebraMap_eq, X_pow_sub_C_eq_prod (hζ.map_of_injective (algebraMap K _).injective) hn
    (root_X_pow_sub_C_pow n a), separable_prod_X_sub_C_iff']
  exact (hζ.map_of_injective (algebraMap K K[n√a]).injective).injOn_pow_mul
    (root_X_pow_sub_C_ne_zero (lt_of_le_of_ne (show 1 ≤ n from hn) (Ne.symm hn')) _)

/-- The natural embedding of the roots of unity of `K` into `Gal(K[ⁿ√a]/K)`, by sending
`η ↦ (ⁿ√a ↦ η • ⁿ√a)`. Also see `autAdjoinRootXPowSubC` for the `AlgEquiv` version. -/
noncomputable
def autAdjoinRootXPowSubCHom :
    rootsOfUnity ⟨n, hn⟩ K →* (K[n√a] →ₐ[K] K[n√a]) where
  toFun := fun η ↦ liftHom (X ^ n - C a) (((η : Kˣ) : K) • (root _) : K[n√a]) <| by
    have := (mem_rootsOfUnity' _ _).mp η.prop
    dsimp at this
    rw [map_sub, map_pow, aeval_C, aeval_X, Algebra.smul_def, mul_pow, root_X_pow_sub_C_pow,
      AdjoinRoot.algebraMap_eq, ← map_pow, this, map_one, one_mul, sub_self]
  map_one' := algHom_ext <| by simp
  map_mul' := fun ε η ↦ algHom_ext <| by simp [mul_smul, smul_comm ((ε : Kˣ) : K)]

/-- The natural embedding of the roots of unity of `K` into `Gal(K[ⁿ√a]/K)`, by sending
`η ↦ (ⁿ√a ↦ η • ⁿ√a)`. This is an isomorphism when `K` contains a primitive root of unity.
See `autAdjoinRootXPowSubCEquiv`. -/
noncomputable
def autAdjoinRootXPowSubC :
    rootsOfUnity ⟨n, hn⟩ K →* (K[n√a] ≃ₐ[K] K[n√a]) :=
  (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp (autAdjoinRootXPowSubCHom hn a).toHomUnits

lemma autAdjoinRootXPowSubC_root (η) :
    autAdjoinRootXPowSubC hn a η (root _) = ((η : Kˣ) : K) • root _ := by
  dsimp [autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, AlgEquiv.algHomUnitsEquiv]
  apply liftHom_root

variable {a}

/-- The inverse function of `autAdjoinRootXPowSubC` if `K` has all roots of unity.
See `autAdjoinRootXPowSubCEquiv`. -/
noncomputable
def AdjoinRootXPowSubCEquivToRootsOfUnity (σ : K[n√a] ≃ₐ[K] K[n√a]) :
    rootsOfUnity ⟨n, hn⟩ K :=
  letI := Fact.mk H
  letI : IsDomain K[n√a] := inferInstance
  letI := Classical.decEq K
  (rootsOfUnityEquivOfPrimitiveRoots (n := ⟨n, hn⟩) (algebraMap K K[n√a]).injective hζ).symm
    (rootsOfUnity.mkOfPowEq (if a = 0 then 1 else σ (root _) / root _) (by
    -- The if is needed in case `n = 1` and `a = 0` and `K[n√a] = K`.
    split
    · exact one_pow _
    rw [div_pow, ← map_pow]
    simp only [PNat.mk_coe, root_X_pow_sub_C_pow, ← algebraMap_eq, AlgEquiv.commutes]
    rw [div_self]
    rwa [Ne, map_eq_zero_iff _ (algebraMap K _).injective]))

/-- The equivalence between the roots of unity of `K` and `Gal(K[ⁿ√a]/K)`. -/
noncomputable
def autAdjoinRootXPowSubCEquiv :
    rootsOfUnity ⟨n, hn⟩ K ≃* (K[n√a] ≃ₐ[K] K[n√a]) where
  __ := autAdjoinRootXPowSubC hn a
  invFun := AdjoinRootXPowSubCEquivToRootsOfUnity hζ hn H
  left_inv := by
    intro η
    have := Fact.mk H
    have : IsDomain K[n√a] := inferInstance
    letI : Algebra K K[n√a] := inferInstance
    apply (rootsOfUnityEquivOfPrimitiveRoots
      (n := ⟨n, hn⟩) (algebraMap K K[n√a]).injective hζ).injective
    ext
    simp only [algebraMap_eq, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      autAdjoinRootXPowSubC_root, Algebra.smul_def, ne_eq, MulEquiv.apply_symm_apply,
      rootsOfUnity.val_mkOfPowEq_coe, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe,
      AdjoinRootXPowSubCEquivToRootsOfUnity]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      have : (η : Kˣ) = 1 := (pow_one _).symm.trans η.prop
      simp only [PNat.mk_one, this, Units.val_one, map_one]
    · exact mul_div_cancel_right₀ _ (root_X_pow_sub_C_ne_zero' hn h)
  right_inv := by
    intro e
    have := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    apply AlgEquiv.coe_algHom_injective
    apply AdjoinRoot.algHom_ext
    simp only [algebraMap_eq, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, AlgHom.coe_coe,
      autAdjoinRootXPowSubC_root, Algebra.smul_def, PNat.mk_coe,
      AdjoinRootXPowSubCEquivToRootsOfUnity]
    rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply, rootsOfUnity.val_mkOfPowEq_coe]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      rw [(pow_one _).symm.trans (root_X_pow_sub_C_pow 1 a), one_mul,
        ← algebraMap_eq, AlgEquiv.commutes]
    · refine div_mul_cancel₀ _ (root_X_pow_sub_C_ne_zero' hn h)

lemma autAdjoinRootXPowSubCEquiv_root (η) :
    autAdjoinRootXPowSubCEquiv hζ hn H η (root _) = ((η : Kˣ) : K) • root _ :=
  autAdjoinRootXPowSubC_root hn a η

set_option tactic.skipAssignedInstances false in
lemma autAdjoinRootXPowSubCEquiv_symm_smul (σ) :
    ((autAdjoinRootXPowSubCEquiv hζ hn H).symm σ : Kˣ) • (root _ : K[n√a]) = σ (root _) := by
  have := Fact.mk H
  simp only [autAdjoinRootXPowSubCEquiv, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, AdjoinRootXPowSubCEquivToRootsOfUnity,
    algebraMap_eq, Units.smul_def, Algebra.smul_def, rootsOfUnityEquivOfPrimitiveRoots_symm_apply,
    rootsOfUnity.mkOfPowEq, PNat.mk_coe, Units.val_ofPowEqOne, ite_mul, one_mul, ne_eq]
  simp_rw [← root_X_pow_sub_C_eq_zero_iff H]
  split_ifs with h
  · rw [h, mul_zero, map_zero]
  · rw [div_mul_cancel₀ _ h]

end AdjoinRoot

/-! ### Galois Group of `IsSplittingField K L (X ^ n - C a)` -/

section IsSplittingField

variable {a}
variable {L : Type*} [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)]

lemma isSplittingField_AdjoinRoot_X_pow_sub_C :
    haveI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    IsSplittingField K K[n√a] (X ^ n - C a) := by
  have := Fact.mk H
  letI : Algebra K K[n√a] := inferInstance
  constructor
  · rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hζ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective)
      (root_X_pow_sub_C_pow n a)
  · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
    apply Algebra.adjoin_mono
    have := ne_zero_of_irreducible_X_pow_sub_C H
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero
      (Nat.pos_of_ne_zero this) a), aeval_def, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]

variable {α : L} (hα : α ^ n = algebraMap K L a)

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, then a choice of `ⁿ√a` gives an equivalence of
`L` with `K[n√a]`. -/
noncomputable
def adjoinRootXPowSubCEquiv :
    K[n√a] ≃ₐ[K] L :=
  AlgEquiv.ofBijective (AdjoinRoot.liftHom (X ^ n - C a) α (by simp [hα])) <| by
    haveI := Fact.mk H
    letI := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
    refine ⟨(AlgHom.toRingHom _).injective, ?_⟩
    rw [← Algebra.range_top_iff_surjective, ← IsSplittingField.adjoin_rootSet _ (X ^ n - C a),
      eq_comm, adjoin_rootSet_eq_range, IsSplittingField.adjoin_rootSet]
    exact IsSplittingField.splits _ _

lemma adjoinRootXPowSubCEquiv_root :
    adjoinRootXPowSubCEquiv hζ H hα (root _) = α := by
  rw [adjoinRootXPowSubCEquiv, AlgEquiv.coe_ofBijective, liftHom_root]

lemma adjoinRootXPowSubCEquiv_symm_eq_root :
    (adjoinRootXPowSubCEquiv hζ H hα).symm α = root _ := by
  apply (adjoinRootXPowSubCEquiv hζ H hα).injective
  rw [(adjoinRootXPowSubCEquiv hζ H hα).apply_symm_apply, adjoinRootXPowSubCEquiv_root]

lemma Algebra.adjoin_root_eq_top_of_isSplittingField :
    Algebra.adjoin K {α} = ⊤ := by
  apply Subalgebra.map_injective (f := (adjoinRootXPowSubCEquiv hζ H hα).symm)
    (adjoinRootXPowSubCEquiv hζ H hα).symm.injective
  rw [Algebra.map_top, (Algebra.range_top_iff_surjective _).mpr
    (adjoinRootXPowSubCEquiv hζ H hα).symm.surjective, AlgHom.map_adjoin,
    Set.image_singleton, AlgHom.coe_coe, adjoinRootXPowSubCEquiv_symm_eq_root, adjoinRoot_eq_top]

lemma IntermediateField.adjoin_root_eq_top_of_isSplittingField :
    K⟮α⟯ = ⊤ := by
  refine (IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ ?_).symm
  exact (Algebra.adjoin_root_eq_top_of_isSplittingField hζ H hα).symm

variable (a) (L)

/-- An arbitrary choice of `ⁿ√a` in the splitting field of `Xⁿ - a`. -/
noncomputable
abbrev rootOfSplitsXPowSubC : L :=
  (rootOfSplits _ (IsSplittingField.splits L (X ^ n - C a))
      (by simpa [degree_X_pow_sub_C hn] using Nat.pos_iff_ne_zero.mp hn))

lemma rootOfSplitsXPowSubC_pow :
    (rootOfSplitsXPowSubC hn a L) ^ n = algebraMap K L a := by
  have := map_rootOfSplits _ (IsSplittingField.splits L (X ^ n - C a))
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
  exact this _

variable {a}

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, then `Gal(L/K)` is isomorphic to the
roots of unity in `K` if `K` contains all of them.
Note that this does not depend on a choice of `ⁿ√a`. -/
noncomputable
def autEquivRootsOfUnity :
    (L ≃ₐ[K] L) ≃* (rootsOfUnity ⟨n, hn⟩ K) :=
  (AlgEquiv.autCongr (adjoinRootXPowSubCEquiv hζ H (rootOfSplitsXPowSubC_pow hn a L)).symm).trans
    (autAdjoinRootXPowSubCEquiv hζ hn H).symm

lemma autEquivRootsOfUnity_apply_rootOfSplit (σ : L ≃ₐ[K] L) :
    σ (rootOfSplitsXPowSubC hn a L) =
      autEquivRootsOfUnity hζ hn H L σ • (rootOfSplitsXPowSubC hn a L) := by
  obtain ⟨η, rfl⟩ := (autEquivRootsOfUnity hζ hn H L).symm.surjective σ
  rw [MulEquiv.apply_symm_apply, autEquivRootsOfUnity]
  simp only [MulEquiv.symm_trans_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm,
    MulEquiv.symm_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    adjoinRootXPowSubCEquiv_symm_eq_root, autAdjoinRootXPowSubCEquiv_root, AlgEquiv.map_smul,
    adjoinRootXPowSubCEquiv_root]
  rfl

lemma autEquivRootsOfUnity_smul (σ : L ≃ₐ[K] L) :
    autEquivRootsOfUnity hζ hn H L σ • α = σ α := by
  have ⟨ζ, hζ'⟩ := hζ
  rw [mem_primitiveRoots hn] at hζ'
  rw [← mem_nthRoots hn, (hζ'.map_of_injective (algebraMap K L).injective).nthRoots_eq
    (rootOfSplitsXPowSubC_pow hn a L)] at hα
  simp only [Finset.range_val, Multiset.mem_map, Multiset.mem_range] at hα
  obtain ⟨i, _, rfl⟩ := hα
  simp only [map_mul, ← map_pow, ← Algebra.smul_def, AlgEquiv.map_smul,
    autEquivRootsOfUnity_apply_rootOfSplit hζ hn H L]
  exact smul_comm _ _ _

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, and `ζ` is a `n`-th primitive root of unity
in `K`, then `Gal(L/K)` is isomorphic to `ZMod n`. -/
noncomputable
def autEquivZmod {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    (L ≃ₐ[K] L) ≃* Multiplicative (ZMod n) :=
  haveI hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  (autEquivRootsOfUnity ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ hn H L).trans
    ((MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq (k := ⟨n, hn⟩)
      (hζ.isUnit_unit' hn)).symm).trans (AddEquiv.toMultiplicative'
        (hζ.isUnit_unit' hn).zmodEquivZPowers.symm))

lemma autEquivZmod_symm_apply_intCast {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : ℤ) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  rw [← autEquivRootsOfUnity_smul ⟨ζ, (mem_primitiveRoots hn).mpr hζ⟩ hn H L hα]
  simp [MulEquiv.subgroupCongr_symm_apply, Subgroup.smul_def, Units.smul_def, autEquivZmod]

lemma autEquivZmod_symm_apply_natCast {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : ℕ) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  simpa only [Int.cast_ofNat, zpow_natCast] using autEquivZmod_symm_apply_intCast H L hα hζ m

lemma isCyclic_of_isSplittingField_X_pow_sub_C : IsCyclic (L ≃ₐ[K] L) :=
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  isCyclic_of_surjective _
    (autEquivZmod H _ <| (mem_primitiveRoots hn).mp hζ.choose_spec).symm.surjective

lemma isGalois_of_isSplittingField_X_pow_sub_C : IsGalois K L :=
  IsGalois.of_separable_splitting_field (separable_X_pow_sub_C_of_irreducible hζ a H)

lemma finrank_of_isSplittingField_X_pow_sub_C : FiniteDimensional.finrank K L = n := by
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C a)
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ H L
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  have : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C H⟩
  rw [← IsGalois.card_aut_eq_finrank, Fintype.card_congr ((autEquivZmod H L <|
    (mem_primitiveRoots hn).mp hζ.choose_spec).toEquiv.trans Multiplicative.toAdd), ZMod.card]

end IsSplittingField

/-! ### Cyclic extensions of order `n` when `K` has all `n`-th roots of unity. -/

section IsCyclic

variable {L} [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)]
variable (hK : (primitiveRoots (FiniteDimensional.finrank K L) K).Nonempty)

open BigOperators FiniteDimensional
variable (K L)

/-- If `L/K` is a cyclic extension of degree `n`, and `K` contains all `n`-th roots of unity,
then `L = K[α]` for some `α ^ n ∈ K`. -/
lemma exists_root_adjoin_eq_top_of_isCyclic :
    ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤ := by
  -- Let `ζ` be an `n`-th root of unity, and `σ` be a generator of `L ≃ₐ[K] L`.
  have ⟨ζ, hζ⟩ := hK
  rw [mem_primitiveRoots finrank_pos] at hζ
  obtain ⟨σ, hσ⟩ := ‹IsCyclic (L ≃ₐ[K] L)›
  have hσ' := orderOf_eq_card_of_forall_mem_zpowers hσ
  -- Since the minimal polynomial of `σ` over `K` is `Xⁿ - 1`,
  -- `σ` has an eigenvector `v` with eigenvalue `ζ`.
  have : IsRoot (minpoly K σ.toLinearMap) ζ := by
    simpa [minpoly_algEquiv_toLinearMap σ (isOfFinOrder_of_finite σ), hσ',
      sub_eq_zero, IsGalois.card_aut_eq_finrank] using hζ.pow_eq_one
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot this).exists_hasEigenvector
  have hv' := hv.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hv'
  -- We claim that `v` is the desired root.
  refine ⟨v, ?_, ?_⟩
  · -- Since `v ^ n` is fixed by `σ` (`σ (v ^ n) = ζ ^ n • v ^ n = v ^ n`), it is in `K`.
    rw [← IntermediateField.mem_bot,
      ← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨σ', hσ'⟩
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    rw [smul_pow', Submonoid.smul_def, AlgEquiv.smul_def, hv', smul_pow, ← pow_mul,
      mul_comm, pow_mul, hζ.pow_eq_one, one_pow, one_smul]
  · -- Since `σ` does not fix `K⟮α⟯`, `K⟮α⟯` is `L`.
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top, eq_top_iff]
    intros σ' hσ'
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    have := hσ' ⟨v, IntermediateField.mem_adjoin_simple_self K v⟩
    simp only [AlgEquiv.smul_def, hv'] at this
    conv_rhs at this => rw [← one_smul K v]
    obtain ⟨k, rfl⟩ := hζ.dvd_of_pow_eq_one n (smul_left_injective K hv.2 this)
    rw [pow_mul, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one, one_pow]
    exact one_mem _

variable {K L}

lemma irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    Irreducible (X ^ (finrank K L) - C a) := by
  have : X ^ (finrank K L) - C a = minpoly K α := by
    refine minpoly.unique _ _ (monic_X_pow_sub_C _ finrank_pos.ne.symm) ?_ ?_
    · simp only [aeval_def, eval₂_sub, eval₂_X_pow, ha, eval₂_C, sub_self]
    · intros q hq hq'
      refine le_trans ?_ (degree_le_of_dvd (minpoly.dvd _ _ hq') hq.ne_zero)
      rw [degree_X_pow_sub_C finrank_pos,
        degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite K α)),
        ← IntermediateField.adjoin.finrank (IsIntegral.of_finite K α), hα, Nat.cast_le]
      exact (finrank_top K L).ge
  exact this ▸ minpoly.irreducible (IsIntegral.of_finite K α)

lemma isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    IsSplittingField K L (X ^ (finrank K L) - C a) := by
  constructor
  · rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots finrank_pos] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hα,
      IntermediateField.adjoin_simple_toSubalgebra_of_integral (IsIntegral.of_finite K α)]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero finrank_pos a),
      aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C, ha, sub_self]

end IsCyclic

open FiniteDimensional in
/--
Suppose `L/K` is a finite extension of dimension `n`, and `K` contains all `n`-th roots of unity.
Then `L/K` is cyclic iff
`L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
`L = K[α]` for some `αⁿ ∈ K`.
-/
lemma isCyclic_tfae (K L) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : (primitiveRoots (FiniteDimensional.finrank K L) K).Nonempty) :
    List.TFAE [
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L),
      ∃ a : K, Irreducible (X ^ (finrank K L) - C a) ∧
        IsSplittingField K L (X ^ (finrank K L) - C a),
      ∃ (α : L), α ^ (finrank K L) ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤] := by
  tfae_have 1 → 3
  · intro ⟨inst₁, inst₂⟩
    exact exists_root_adjoin_eq_top_of_isCyclic K L hK
  tfae_have 3 → 2
  · intro ⟨α, ⟨a, ha⟩, hα⟩
    exact ⟨a, irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα,
      isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK ha.symm hα⟩
  tfae_have 2 → 1
  · intro ⟨a, H, inst⟩
    exact ⟨isGalois_of_isSplittingField_X_pow_sub_C hK H L,
      isCyclic_of_isSplittingField_X_pow_sub_C hK H L⟩
  tfae_finish
