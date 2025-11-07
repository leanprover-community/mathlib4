/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Multiset.OrderedMonoid
import Mathlib.Data.Multiset.Sort

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `PrimeMultiset`: Type of multisets of prime numbers.
* `FactorMultiset n`: Multiset of prime factors of `n`.
-/

/-- The type of multisets of prime numbers.  Unique factorization
gives an equivalence between this set and ℕ+, as we will formalize
below. -/
def PrimeMultiset :=
  Multiset Nat.Primes
deriving Inhabited, AddCommMonoid, DistribLattice,
  SemilatticeSup, Sub,
  IsOrderedCancelAddMonoid, CanonicallyOrderedAdd, OrderBot, OrderedSub

namespace PrimeMultiset

-- `@[derive]` doesn't work for `meta` instances
unsafe instance : Repr PrimeMultiset := by delta PrimeMultiset; infer_instance

/-- The multiset consisting of a single prime -/
def ofPrime (p : Nat.Primes) : PrimeMultiset :=
  ({p} : Multiset Nat.Primes)

@[simp]
theorem card_ofPrime (p : Nat.Primes) : Multiset.card (ofPrime p) = 1 :=
  rfl

/-- We can forget the primality property and regard a multiset
of primes as just a multiset of positive integers, or a multiset
of natural numbers.  In the opposite direction, if we have a
multiset of positive integers or natural numbers, together with
a proof that all the elements are prime, then we can regard it
as a multiset of primes.  The next block of results records
obvious properties of these coercions.
-/
def toNatMultiset : PrimeMultiset → Multiset ℕ := fun v => v.map (↑)

instance coeNat : Coe PrimeMultiset (Multiset ℕ) :=
  ⟨toNatMultiset⟩

/-- `PrimeMultiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `AddMonoidHom`. -/
def coeNatMonoidHom : PrimeMultiset →+ Multiset ℕ :=
  Multiset.mapAddMonoidHom (↑)

@[simp]
theorem coe_coeNatMonoidHom : (coeNatMonoidHom : PrimeMultiset → Multiset ℕ) = (↑) :=
  rfl

theorem coeNat_injective : Function.Injective ((↑) : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_injective

theorem coeNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ) = {(p : ℕ)} :=
  rfl

theorem coeNat_prime (v : PrimeMultiset) (p : ℕ) (h : p ∈ (v : Multiset ℕ)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

/-- Converts a `PrimeMultiset` to a `Multiset ℕ+`. -/
def toPNatMultiset : PrimeMultiset → Multiset ℕ+ := fun v => v.map (↑)

instance coePNat : Coe PrimeMultiset (Multiset ℕ+) :=
  ⟨toPNatMultiset⟩

/-- `coePNat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `AddMonoidHom`. -/
def coePNatMonoidHom : PrimeMultiset →+ Multiset ℕ+ :=
  Multiset.mapAddMonoidHom (↑)

@[simp]
theorem coe_coePNatMonoidHom : (coePNatMonoidHom : PrimeMultiset → Multiset ℕ+) = (↑) :=
  rfl

theorem coePNat_injective : Function.Injective ((↑) : PrimeMultiset → Multiset ℕ+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_injective

theorem coePNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ+) = {(p : ℕ+)} :=
  rfl

theorem coePNat_prime (v : PrimeMultiset) (p : ℕ+) (h : p ∈ (v : Multiset ℕ+)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  exact h_eq ▸ hp'

instance coeMultisetPNatNat : Coe (Multiset ℕ+) (Multiset ℕ) :=
  ⟨fun v => v.map (↑)⟩

theorem coePNat_nat (v : PrimeMultiset) : ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ) := by
  change (v.map ((↑) : Nat.Primes → ℕ+)).map Subtype.val = v.map Subtype.val
  rw [Multiset.map_map]
  rfl

/-- The product of a `PrimeMultiset`, as a `ℕ+`. -/
def prod (v : PrimeMultiset) : ℕ+ :=
  (v : Multiset PNat).prod

theorem coe_prod (v : PrimeMultiset) : (v.prod : ℕ) = (v : Multiset ℕ).prod := by
  have h : (v.prod : ℕ) = ((v.map (↑) : Multiset ℕ+).map (↑)).prod :=
    PNat.coeMonoidHom.map_multiset_prod v.toPNatMultiset
  simpa [Multiset.map_map] using h

theorem prod_ofPrime (p : Nat.Primes) : (ofPrime p).prod = (p : ℕ+) :=
  Multiset.prod_singleton _

/-- If a `Multiset ℕ` consists only of primes, it can be recast as a `PrimeMultiset`. -/
def ofNatMultiset (v : Multiset ℕ) (h : ∀ p : ℕ, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h

@[simp]
theorem mem_ofNatMultiset {p : ℕ+} {s : Multiset ℕ} (hs) :
    p ∈ (ofNatMultiset s hs : Multiset ℕ+) ↔ (p : ℕ) ∈ s := by
  simp only [ofNatMultiset, toPNatMultiset, Multiset.map_pmap, Multiset.mem_pmap, Nat.Primes.toPNat,
    ← PNat.coe_inj]
  simp

@[simp]
theorem to_ofNatMultiset (v : Multiset ℕ) (h) : (ofNatMultiset v h : Multiset ℕ) = v := by
  dsimp [ofNatMultiset, toNatMultiset]
  rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']

@[simp]
theorem prod_ofNatMultiset (v : Multiset ℕ) (h) :
    ((ofNatMultiset v h).prod : ℕ) = (v.prod : ℕ) := by rw [coe_prod, to_ofNatMultiset]

/-- If a `Multiset ℕ+` consists only of primes, it can be recast as a `PrimeMultiset`. -/
def ofPNatMultiset (v : Multiset ℕ+) (h : ∀ p : ℕ+, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : ℕ), hp⟩) v h

@[simp]
theorem to_ofPNatMultiset (v : Multiset ℕ+) (h) : (ofPNatMultiset v h : Multiset ℕ+) = v := by
  dsimp [ofPNatMultiset, toPNatMultiset]
  have : (fun (p : ℕ+) (h : p.Prime) => ((↑) : Nat.Primes → ℕ+) ⟨p, h⟩) = fun p _ => id p := by
    funext p h
    apply Subtype.eq
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]

@[simp]
theorem prod_ofPNatMultiset (v : Multiset ℕ+) (h) : ((ofPNatMultiset v h).prod : ℕ+) = v.prod := by
  dsimp [prod]
  rw [to_ofPNatMultiset]

/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
def ofNatList (l : List ℕ) (h : ∀ p : ℕ, p ∈ l → p.Prime) : PrimeMultiset :=
  ofNatMultiset (l : Multiset ℕ) h

@[simp]
theorem mem_ofNatList {p : ℕ+} {l : List ℕ} (hl) :
    p ∈ (ofNatList l hl : Multiset ℕ+) ↔ (p : ℕ) ∈ l := by
  simp [ofNatList]

@[simp]
theorem prod_ofNatList (l : List ℕ) (h) : ((ofNatList l h).prod : ℕ) = l.prod := by
  have := prod_ofNatMultiset (l : Multiset ℕ) h
  rw [Multiset.prod_coe] at this
  exact this

/-- If a `List ℕ+` consists only of primes, it can be recast as a `PrimeMultiset` with
the coercion from lists to multisets. -/
def ofPNatList (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.Prime) : PrimeMultiset :=
  ofPNatMultiset (l : Multiset ℕ+) h

@[simp]
theorem toPNatMultiset_ofPNatList {l : List ℕ+} (hl) : (ofPNatList l hl : Multiset ℕ+) = l := by
  simp [ofPNatList]

@[simp]
theorem prod_ofPNatList (l : List ℕ+) (h) : (ofPNatList l h).prod = l.prod := by
  have := prod_ofPNatMultiset (l : Multiset ℕ+) h
  rw [Multiset.prod_coe] at this
  exact this

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
@[simp]
theorem prod_zero : (0 : PrimeMultiset).prod = 1 := by
  exact Multiset.prod_zero

@[simp]
theorem prod_add (u v : PrimeMultiset) : (u + v).prod = u.prod * v.prod := by
  change (coePNatMonoidHom (u + v)).prod = _
  rw [coePNatMonoidHom.map_add]
  exact Multiset.prod_add _ _

@[simp]
theorem prod_smul (d : ℕ) (u : PrimeMultiset) : (d • u).prod = u.prod ^ d := by
  induction d with
  | zero => simp only [zero_nsmul, pow_zero, prod_zero]
  | succ n ih => rw [succ_nsmul, prod_add, ih, pow_succ]

end PrimeMultiset

namespace PNat

/-- The prime factors of n, regarded as a multiset -/
def factorMultiset (n : ℕ+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

/-- The product of the factors is the original number -/
@[simp]
theorem prod_factorMultiset (n : ℕ+) : (factorMultiset n).prod = n :=
  eq <| by
    dsimp [factorMultiset]
    rw [PrimeMultiset.prod_ofNatList]
    exact Nat.prod_primeFactorsList n.ne_zero

theorem coeNat_factorMultiset (n : ℕ+) :
    (factorMultiset n : Multiset ℕ) = (Nat.primeFactorsList n : Multiset ℕ) :=
  PrimeMultiset.to_ofNatMultiset (Nat.primeFactorsList n) (@Nat.prime_of_mem_primeFactorsList n)

@[simp]
theorem mem_factorMultiset {p n : ℕ+} : p ∈ (n.factorMultiset : Multiset ℕ+) ↔ p.Prime ∧ p ∣ n := by
  simp [factorMultiset, dvd_iff, PNat.Prime]

end PNat

namespace PrimeMultiset

/-- If we start with a multiset of primes, take the product and
then factor it, we get back the original multiset. -/
@[simp]
theorem factorMultiset_prod (v : PrimeMultiset) : v.prod.factorMultiset = v := by
  apply PrimeMultiset.coeNat_injective
  rw [v.prod.coeNat_factorMultiset, PrimeMultiset.coe_prod]
  rcases v with ⟨l⟩
  dsimp [PrimeMultiset.toNatMultiset]
  let l' := l.map ((↑) : Nat.Primes → ℕ)
  have (p : ℕ) (hp : p ∈ l') : p.Prime := by
    simp only [List.map_subtype, List.map_id_fun', id_eq, List.mem_unattach, l'] at hp
    obtain ⟨hp', -⟩ := hp
    exact hp'
  exact Multiset.coe_eq_coe.mpr (@Nat.primeFactorsList_unique _ l' rfl this).symm

end PrimeMultiset

namespace PNat

/-- Positive integers biject with multisets of primes. -/
def factorMultisetEquiv : ℕ+ ≃ PrimeMultiset where
  toFun := factorMultiset
  invFun := PrimeMultiset.prod
  left_inv := prod_factorMultiset
  right_inv := PrimeMultiset.factorMultiset_prod

/-- Factoring gives a homomorphism from the multiplicative
monoid ℕ+ to the additive monoid of multisets. -/
@[simp]
theorem factorMultiset_one : factorMultiset 1 = 0 := by
  simp [factorMultiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]

@[simp]
theorem factorMultiset_mul (n m : ℕ+) :
    factorMultiset (n * m) = factorMultiset n + factorMultiset m := by
  let u := factorMultiset n
  let v := factorMultiset m
  have : n = u.prod := (prod_factorMultiset n).symm; rw [this]
  have : m = v.prod := (prod_factorMultiset m).symm; rw [this]
  rw [← PrimeMultiset.prod_add]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

@[simp]
theorem factorMultiset_pow (n : ℕ+) (m : ℕ) :
    factorMultiset (n ^ m) = m • factorMultiset n := by
  let u := factorMultiset n
  have : n = u.prod := (prod_factorMultiset n).symm
  rw [this, ← PrimeMultiset.prod_smul]
  repeat' rw [PrimeMultiset.factorMultiset_prod]

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factorMultiset_ofPrime (p : Nat.Primes) :
    (p : ℕ+).factorMultiset = PrimeMultiset.ofPrime p := by
  apply factorMultisetEquiv.symm.injective
  change (p : ℕ+).factorMultiset.prod = (PrimeMultiset.ofPrime p).prod
  rw [(p : ℕ+).prod_factorMultiset, PrimeMultiset.prod_ofPrime]

/-- We now have four different results that all encode the
idea that inequality of multisets corresponds to divisibility
of positive integers. -/
@[simp]
theorem factorMultiset_le_iff {m n : ℕ+} : factorMultiset m ≤ factorMultiset n ↔ m ∣ n := by
  constructor
  · intro h
    rw [← prod_factorMultiset m, ← prod_factorMultiset m]
    apply Dvd.intro (n.factorMultiset - m.factorMultiset).prod
    rw [← PrimeMultiset.prod_add, PrimeMultiset.factorMultiset_prod, add_tsub_cancel_of_le h,
      prod_factorMultiset]
  · intro h
    rw [← mul_div_exact h, factorMultiset_mul]
    exact le_self_add

@[gcongr]
alias ⟨_, factorMultiset_mono⟩ := factorMultiset_le_iff

theorem factorMultiset_le_iff' {m : ℕ+} {v : PrimeMultiset} :
    factorMultiset m ≤ v ↔ m ∣ v.prod := by
  let h := @factorMultiset_le_iff m v.prod
  rw [v.factorMultiset_prod] at h
  exact h

end PNat

namespace PrimeMultiset

@[simp]
theorem prod_dvd_iff {u v : PrimeMultiset} : u.prod ∣ v.prod ↔ u ≤ v := by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  rw [u.factorMultiset_prod] at h
  exact h.symm

@[gcongr] alias ⟨_, prod_dvd_prod⟩ := prod_dvd_iff

theorem prod_dvd_iff' {u : PrimeMultiset} {n : ℕ+} : u.prod ∣ n ↔ u ≤ n.factorMultiset := by
  let h := @prod_dvd_iff u n.factorMultiset
  rw [n.prod_factorMultiset] at h
  exact h

end PrimeMultiset

namespace PNat

/-- The gcd and lcm operations on positive integers correspond
to the inf and sup operations on multisets. -/
theorem factorMultiset_gcd (m n : ℕ+) :
    factorMultiset (gcd m n) = factorMultiset m ⊓ factorMultiset n := by
  apply le_antisymm
  · apply le_inf_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact gcd_dvd_left m n
    · exact gcd_dvd_right m n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    · exact inf_le_left
    · exact inf_le_right

theorem factorMultiset_lcm (m n : ℕ+) :
    factorMultiset (lcm m n) = factorMultiset m ⊔ factorMultiset n := by
  apply le_antisymm
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    apply lcm_dvd <;> rw [← factorMultiset_le_iff']
    · exact le_sup_left
    · exact le_sup_right
  · apply sup_le_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    · exact dvd_lcm_left m n
    · exact dvd_lcm_right m n

/-- The number of occurrences of p in the factor multiset of m
is the same as the p-adic valuation of m. -/
theorem count_factorMultiset (m : ℕ+) (p : Nat.Primes) (k : ℕ) :
    (p : ℕ+) ^ k ∣ m ↔ k ≤ m.factorMultiset.count p := by
  rw [Multiset.le_count_iff_replicate_le, ← factorMultiset_le_iff, factorMultiset_pow,
    factorMultiset_ofPrime]
  congr! 2
  apply Multiset.eq_replicate.mpr
  constructor
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
  · intro q h
    rw [PrimeMultiset.ofPrime, Multiset.nsmul_singleton _ k] at h
    exact Multiset.eq_of_mem_replicate h

end PNat

namespace PrimeMultiset

theorem prod_inf (u v : PrimeMultiset) : (u ⊓ v).prod = PNat.gcd u.prod v.prod := by
  let n := u.prod
  let m := v.prod
  change (u ⊓ v).prod = PNat.gcd n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_gcd n m, PNat.prod_factorMultiset]

theorem prod_sup (u v : PrimeMultiset) : (u ⊔ v).prod = PNat.lcm u.prod v.prod := by
  let n := u.prod
  let m := v.prod
  change (u ⊔ v).prod = PNat.lcm n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  rw [← PNat.factorMultiset_lcm n m, PNat.prod_factorMultiset]

end PrimeMultiset
