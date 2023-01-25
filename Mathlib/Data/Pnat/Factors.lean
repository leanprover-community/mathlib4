/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland

! This file was ported from Lean 3 source module data.pnat.factors
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Multiset.Basic
import Mathbin.Data.Pnat.Prime
import Mathbin.Data.Nat.Factors
import Mathbin.Data.Multiset.Sort

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `prime_multiset`: Type of multisets of prime numbers.
* `factor_multiset n`: Multiset of prime factors of `n`.
-/


/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/
def PrimeMultiset :=
  Multiset Nat.Primes deriving Inhabited, CanonicallyOrderedAddMonoid, DistribLattice,
  SemilatticeSup, OrderBot, Sub, OrderedSub
#align prime_multiset PrimeMultiset

namespace PrimeMultiset

-- `@[derive]` doesn't work for `meta` instances
unsafe instance : Repr PrimeMultiset := by delta PrimeMultiset <;> infer_instance

/-- The multiset consisting of a single prime -/
def ofPrime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)
#align prime_multiset.of_prime PrimeMultiset.ofPrime

theorem card_ofPrime (p : Nat.Primes) : Multiset.card (ofPrime p) = 1 :=
  rfl
#align prime_multiset.card_of_prime PrimeMultiset.card_ofPrime

/-- We can forget the primality property and regard a multiset
 of primes as just a multiset of positive integers, or a multiset
 of natural numbers.  In the opposite direction, if we have a
 multiset of positive integers or natural numbers, together with
 a proof that all the elements are prime, then we can regard it
 as a multiset of primes.  The next block of results records
 obvious properties of these coercions.
-/
def toNatMultiset : PrimeMultiset → Multiset ℕ := fun v => v.map fun p => (p : ℕ)
#align prime_multiset.to_nat_multiset PrimeMultiset.toNatMultiset

instance coeNat : Coe PrimeMultiset (Multiset ℕ) :=
  ⟨toNatMultiset⟩
#align prime_multiset.coe_nat PrimeMultiset.coeNat

/-- `prime_multiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `add_monoid_hom`. -/
def coeNatMonoidHom : PrimeMultiset →+ Multiset ℕ :=
  { Multiset.mapAddMonoidHom coe with toFun := coe }
#align prime_multiset.coe_nat_monoid_hom PrimeMultiset.coeNatMonoidHom

@[simp]
theorem coe_coeNatMonoidHom : (coeNatMonoidHom : PrimeMultiset → Multiset ℕ) = coe :=
  rfl
#align prime_multiset.coe_coe_nat_monoid_hom PrimeMultiset.coe_coeNatMonoidHom

theorem coeNat_injective : Function.Injective (coe : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_injective
#align prime_multiset.coe_nat_injective PrimeMultiset.coeNat_injective

theorem coeNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ) = {p} :=
  rfl
#align prime_multiset.coe_nat_of_prime PrimeMultiset.coeNat_ofPrime

theorem coeNat_prime (v : PrimeMultiset) (p : ℕ) (h : p ∈ (v : Multiset ℕ)) : p.Prime :=
  by
  rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
  exact h_eq ▸ hp'
#align prime_multiset.coe_nat_prime PrimeMultiset.coeNat_prime

/-- Converts a `prime_multiset` to a `multiset ℕ+`. -/
def toPnatMultiset : PrimeMultiset → Multiset ℕ+ := fun v => v.map fun p => (p : ℕ+)
#align prime_multiset.to_pnat_multiset PrimeMultiset.toPnatMultiset

instance coePnat : Coe PrimeMultiset (Multiset ℕ+) :=
  ⟨toPnatMultiset⟩
#align prime_multiset.coe_pnat PrimeMultiset.coePnat

/-- `coe_pnat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `add_monoid_hom`. -/
def coePnatMonoidHom : PrimeMultiset →+ Multiset ℕ+ :=
  { Multiset.mapAddMonoidHom coe with toFun := coe }
#align prime_multiset.coe_pnat_monoid_hom PrimeMultiset.coePnatMonoidHom

@[simp]
theorem coe_coePnatMonoidHom : (coePnatMonoidHom : PrimeMultiset → Multiset ℕ+) = coe :=
  rfl
#align prime_multiset.coe_coe_pnat_monoid_hom PrimeMultiset.coe_coePnatMonoidHom

theorem coePnat_injective : Function.Injective (coe : PrimeMultiset → Multiset ℕ+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_injective
#align prime_multiset.coe_pnat_injective PrimeMultiset.coePnat_injective

theorem coePnat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ+) = {(p : ℕ+)} :=
  rfl
#align prime_multiset.coe_pnat_of_prime PrimeMultiset.coePnat_ofPrime

theorem coePnat_prime (v : PrimeMultiset) (p : ℕ+) (h : p ∈ (v : Multiset ℕ+)) : p.Prime :=
  by
  rcases multiset.mem_map.mp h with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
  exact h_eq ▸ hp'
#align prime_multiset.coe_pnat_prime PrimeMultiset.coePnat_prime

instance coeMultisetPnatNat : Coe (Multiset ℕ+) (Multiset ℕ) :=
  ⟨fun v => v.map fun n => (n : ℕ)⟩
#align prime_multiset.coe_multiset_pnat_nat PrimeMultiset.coeMultisetPnatNat

theorem coePnat_nat (v : PrimeMultiset) : ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ) :=
  by
  change (v.map (coe : Nat.Primes → ℕ+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  congr
#align prime_multiset.coe_pnat_nat PrimeMultiset.coePnat_nat

/-- The product of a `prime_multiset`, as a `ℕ+`. -/
def prod (v : PrimeMultiset) : ℕ+ :=
  (v : Multiset PNat).Prod
#align prime_multiset.prod PrimeMultiset.prod

theorem coe_prod (v : PrimeMultiset) : (v.Prod : ℕ) = (v : Multiset ℕ).Prod :=
  by
  let h : (v.prod : ℕ) = ((v.map coe).map coe).Prod :=
    pnat.coe_monoid_hom.map_multiset_prod v.to_pnat_multiset
  rw [Multiset.map_map] at h
  have : (coe : ℕ+ → ℕ) ∘ (coe : Nat.Primes → ℕ+) = coe := funext fun p => rfl
  rw [this] at h; exact h
#align prime_multiset.coe_prod PrimeMultiset.coe_prod

theorem prod_ofPrime (p : Nat.Primes) : (ofPrime p).Prod = (p : ℕ+) :=
  Multiset.prod_singleton _
#align prime_multiset.prod_of_prime PrimeMultiset.prod_ofPrime

/-- If a `multiset ℕ` consists only of primes, it can be recast as a `prime_multiset`. -/
def ofNatMultiset (v : Multiset ℕ) (h : ∀ p : ℕ, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h
#align prime_multiset.of_nat_multiset PrimeMultiset.ofNatMultiset

theorem to_ofNatMultiset (v : Multiset ℕ) (h) : (ofNatMultiset v h : Multiset ℕ) = v :=
  by
  unfold_coes
  dsimp [of_nat_multiset, to_nat_multiset]
  have : (fun (p : ℕ) (h : p.Prime) => ((⟨p, h⟩ : Nat.Primes) : ℕ)) = fun p h => id p :=
    by
    funext p h
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]
#align prime_multiset.to_of_nat_multiset PrimeMultiset.to_ofNatMultiset

theorem prod_ofNatMultiset (v : Multiset ℕ) (h) : ((ofNatMultiset v h).Prod : ℕ) = (v.Prod : ℕ) :=
  by rw [coe_prod, to_of_nat_multiset]
#align prime_multiset.prod_of_nat_multiset PrimeMultiset.prod_ofNatMultiset

/-- If a `multiset ℕ+` consists only of primes, it can be recast as a `prime_multiset`. -/
def ofPnatMultiset (v : Multiset ℕ+) (h : ∀ p : ℕ+, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : ℕ), hp⟩) v h
#align prime_multiset.of_pnat_multiset PrimeMultiset.ofPnatMultiset

theorem to_ofPnatMultiset (v : Multiset ℕ+) (h) : (ofPnatMultiset v h : Multiset ℕ+) = v :=
  by
  unfold_coes; dsimp [of_pnat_multiset, to_pnat_multiset]
  have : (fun (p : ℕ+) (h : p.Prime) => (coe : Nat.Primes → ℕ+) ⟨p, h⟩) = fun p h => id p :=
    by
    funext p h
    apply Subtype.eq
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]
#align prime_multiset.to_of_pnat_multiset PrimeMultiset.to_ofPnatMultiset

theorem prod_ofPnatMultiset (v : Multiset ℕ+) (h) : ((ofPnatMultiset v h).Prod : ℕ+) = v.Prod :=
  by
  dsimp [Prod]
  rw [to_of_pnat_multiset]
#align prime_multiset.prod_of_pnat_multiset PrimeMultiset.prod_ofPnatMultiset

/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
def ofNatList (l : List ℕ) (h : ∀ p : ℕ, p ∈ l → p.Prime) : PrimeMultiset :=
  ofNatMultiset (l : Multiset ℕ) h
#align prime_multiset.of_nat_list PrimeMultiset.ofNatList

theorem prod_ofNatList (l : List ℕ) (h) : ((ofNatList l h).Prod : ℕ) = l.Prod :=
  by
  have := prod_of_nat_multiset (l : Multiset ℕ) h
  rw [Multiset.coe_prod] at this
  exact this
#align prime_multiset.prod_of_nat_list PrimeMultiset.prod_ofNatList

/-- If a `list ℕ+` consists only of primes, it can be recast as a `prime_multiset` with
the coercion from lists to multisets. -/
def ofPnatList (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.Prime) : PrimeMultiset :=
  ofPnatMultiset (l : Multiset ℕ+) h
#align prime_multiset.of_pnat_list PrimeMultiset.ofPnatList

theorem prod_ofPnatList (l : List ℕ+) (h) : (ofPnatList l h).Prod = l.Prod :=
  by
  have := prod_of_pnat_multiset (l : Multiset ℕ+) h
  rw [Multiset.coe_prod] at this
  exact this
#align prime_multiset.prod_of_pnat_list PrimeMultiset.prod_ofPnatList

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
theorem prod_zero : (0 : PrimeMultiset).Prod = 1 :=
  by
  dsimp [Prod]
  exact Multiset.prod_zero
#align prime_multiset.prod_zero PrimeMultiset.prod_zero

theorem prod_add (u v : PrimeMultiset) : (u + v).Prod = u.Prod * v.Prod :=
  by
  change (coe_pnat_monoid_hom (u + v)).Prod = _
  rw [coe_pnat_monoid_hom.map_add]
  exact Multiset.prod_add _ _
#align prime_multiset.prod_add PrimeMultiset.prod_add

theorem prod_smul (d : ℕ) (u : PrimeMultiset) : (d • u).Prod = u.Prod ^ d :=
  by
  induction' d with d ih
  rfl
  rw [succ_nsmul, prod_add, ih, Nat.succ_eq_add_one, pow_succ, mul_comm]
#align prime_multiset.prod_smul PrimeMultiset.prod_smul

end PrimeMultiset

namespace PNat

/-- The prime factors of n, regarded as a multiset -/
def factorMultiset (n : ℕ+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.factors n) (@Nat.prime_of_mem_factors n)
#align pnat.factor_multiset PNat.factorMultiset

/-- The product of the factors is the original number -/
theorem prod_factorMultiset (n : ℕ+) : (factorMultiset n).Prod = n :=
  Eq <| by
    dsimp [factor_multiset]
    rw [PrimeMultiset.prod_ofNatList]
    exact Nat.prod_factors n.ne_zero
#align pnat.prod_factor_multiset PNat.prod_factorMultiset

theorem coeNat_factorMultiset (n : ℕ+) :
    (factorMultiset n : Multiset ℕ) = (Nat.factors n : Multiset ℕ) :=
  PrimeMultiset.to_ofNatMultiset (Nat.factors n) (@Nat.prime_of_mem_factors n)
#align pnat.coe_nat_factor_multiset PNat.coeNat_factorMultiset

end PNat

namespace PrimeMultiset

/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factorMultiset_prod (v : PrimeMultiset) : v.Prod.factorMultiset = v :=
  by
  apply PrimeMultiset.coeNat_injective
  rw [v.prod.coe_nat_factor_multiset, PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  unfold_coes
  dsimp [PrimeMultiset.toNatMultiset]
  rw [Multiset.coe_prod]
  let l' := l.map (coe : Nat.Primes → ℕ)
  have : ∀ p : ℕ, p ∈ l' → p.Prime := fun p hp =>
    by
    rcases list.mem_map.mp hp with ⟨⟨p', hp'⟩, ⟨h_mem, h_eq⟩⟩
    exact h_eq ▸ hp'
  exact multiset.coe_eq_coe.mpr (@Nat.factors_unique _ l' rfl this).symm
#align prime_multiset.factor_multiset_prod PrimeMultiset.factorMultiset_prod

end PrimeMultiset

namespace PNat

/-- Positive integers biject with multisets of primes. -/
def factorMultisetEquiv : ℕ+ ≃ PrimeMultiset
    where
  toFun := factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factorMultiset
  right_inv := PrimeMultiset.factorMultiset_prod
#align pnat.factor_multiset_equiv PNat.factorMultisetEquiv

/-- Factoring gives a homomorphism from the multiplicative
 monoid ℕ+ to the additive monoid of multisets. -/
theorem factorMultiset_one : factorMultiset 1 = 0 := by
  simp [factor_multiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]
#align pnat.factor_multiset_one PNat.factorMultiset_one

theorem factorMultiset_mul (n m : ℕ+) :
    factorMultiset (n * m) = factorMultiset n + factorMultiset m :=
  by
  let u := factor_multiset n
  let v := factor_multiset m
  have : n = u.prod := (prod_factor_multiset n).symm; rw [this]
  have : m = v.prod := (prod_factor_multiset m).symm; rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat' rw [PrimeMultiset.factorMultiset_prod]
#align pnat.factor_multiset_mul PNat.factorMultiset_mul

theorem factorMultiset_pow (n : ℕ+) (m : ℕ) : factorMultiset (n ^ m) = m • factorMultiset n :=
  by
  let u := factor_multiset n
  have : n = u.prod := (prod_factor_multiset n).symm
  rw [this, ← PrimeMultiset.prod_smul]
  repeat' rw [PrimeMultiset.factorMultiset_prod]
#align pnat.factor_multiset_pow PNat.factorMultiset_pow

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factorMultiset_ofPrime (p : Nat.Primes) :
    (p : ℕ+).factorMultiset = PrimeMultiset.ofPrime p :=
  by
  apply factor_multiset_equiv.symm.injective
  change (p : ℕ+).factorMultiset.Prod = (PrimeMultiset.ofPrime p).Prod
  rw [(p : ℕ+).prod_factor_multiset, PrimeMultiset.prod_ofPrime]
#align pnat.factor_multiset_of_prime PNat.factorMultiset_ofPrime

/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factorMultiset_le_iff {m n : ℕ+} : factorMultiset m ≤ factorMultiset n ↔ m ∣ n :=
  by
  constructor
  · intro h
    rw [← prod_factor_multiset m, ← prod_factor_multiset m]
    apply Dvd.intro (n.factor_multiset - m.factor_multiset).Prod
    rw [← PrimeMultiset.prod_add, PrimeMultiset.factorMultiset_prod, add_tsub_cancel_of_le h,
      prod_factor_multiset]
  · intro h
    rw [← mul_div_exact h, factor_multiset_mul]
    exact le_self_add
#align pnat.factor_multiset_le_iff PNat.factorMultiset_le_iff

theorem factorMultiset_le_iff' {m : ℕ+} {v : PrimeMultiset} : factorMultiset m ≤ v ↔ m ∣ v.Prod :=
  by
  let h := @factor_multiset_le_iff m v.prod
  rw [v.factor_multiset_prod] at h
  exact h
#align pnat.factor_multiset_le_iff' PNat.factorMultiset_le_iff'

end PNat

namespace PrimeMultiset

theorem prod_dvd_iff {u v : PrimeMultiset} : u.Prod ∣ v.Prod ↔ u ≤ v :=
  by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  rw [u.factor_multiset_prod] at h
  exact h.symm
#align prime_multiset.prod_dvd_iff PrimeMultiset.prod_dvd_iff

theorem prod_dvd_iff' {u : PrimeMultiset} {n : ℕ+} : u.Prod ∣ n ↔ u ≤ n.factorMultiset :=
  by
  let h := @prod_dvd_iff u n.factor_multiset
  rw [n.prod_factor_multiset] at h
  exact h
#align prime_multiset.prod_dvd_iff' PrimeMultiset.prod_dvd_iff'

end PrimeMultiset

namespace PNat

/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets. -/
theorem factorMultiset_gcd (m n : ℕ+) :
    factorMultiset (gcd m n) = factorMultiset m ⊓ factorMultiset n :=
  by
  apply le_antisymm
  · apply le_inf_iff.mpr <;> constructor <;> apply factor_multiset_le_iff.mpr
    exact gcd_dvd_left m n
    exact gcd_dvd_right m n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    exact inf_le_left
    exact inf_le_right
#align pnat.factor_multiset_gcd PNat.factorMultiset_gcd

theorem factorMultiset_lcm (m n : ℕ+) :
    factorMultiset (lcm m n) = factorMultiset m ⊔ factorMultiset n :=
  by
  apply le_antisymm
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factor_multiset]
    apply lcm_dvd <;> rw [← factor_multiset_le_iff']
    exact le_sup_left
    exact le_sup_right
  · apply sup_le_iff.mpr <;> constructor <;> apply factor_multiset_le_iff.mpr
    exact dvd_lcm_left m n
    exact dvd_lcm_right m n
#align pnat.factor_multiset_lcm PNat.factorMultiset_lcm

/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factorMultiset (m : ℕ+) (p : Nat.Primes) (k : ℕ) :
    (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factorMultiset.count p :=
  by
  intros
  rw [Multiset.le_count_iff_replicate_le]
  rw [← factor_multiset_le_iff, factor_multiset_pow, factor_multiset_of_prime]
  congr 2
  apply multiset.eq_replicate.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
  · intro q h
    rw [PrimeMultiset.ofPrime, Multiset.nsmul_singleton _ k] at h
    exact Multiset.eq_of_mem_replicate h
#align pnat.count_factor_multiset PNat.count_factorMultiset

end PNat

namespace PrimeMultiset

theorem prod_inf (u v : PrimeMultiset) : (u ⊓ v).Prod = PNat.gcd u.Prod v.Prod :=
  by
  let n := u.prod
  let m := v.prod
  change (u ⊓ v).Prod = PNat.gcd n m
  have : u = n.factor_multiset := u.factor_multiset_prod.symm; rw [this]
  have : v = m.factor_multiset := v.factor_multiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_gcd n m, PNat.prod_factorMultiset]
#align prime_multiset.prod_inf PrimeMultiset.prod_inf

theorem prod_sup (u v : PrimeMultiset) : (u ⊔ v).Prod = PNat.lcm u.Prod v.Prod :=
  by
  let n := u.prod
  let m := v.prod
  change (u ⊔ v).Prod = PNat.lcm n m
  have : u = n.factor_multiset := u.factor_multiset_prod.symm; rw [this]
  have : v = m.factor_multiset := v.factor_multiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_lcm n m, PNat.prod_factorMultiset]
#align prime_multiset.prod_sup PrimeMultiset.prod_sup

end PrimeMultiset

