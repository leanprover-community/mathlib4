/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
import Mathlib.Algebra.BigOperators.Multiset.Basic
import Mathlib.Data.PNat.Prime
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Multiset.Sort

#align_import data.pnat.factors from "leanprover-community/mathlib"@"e3d9ab8faa9dea8f78155c6c27d62a621f4c152d"

/-!
# Prime factors of nonzero naturals

This file defines the factorization of a nonzero natural number `n` as a multiset of primes,
the multiplicity of `p` in this factors multiset being the p-adic valuation of `n`.

## Main declarations

* `PrimeMultiset`: Type of multisets of prime numbers.
* `FactorMultiset n`: Multiset of prime factors of `n`.
-/

-- Porting note: `deriving` contained
-- Inhabited, CanonicallyOrderedAddMonoid, DistribLattice, SemilatticeSup, OrderBot, Sub, OrderedSub
/-- The type of multisets of prime numbers.  Unique factorization
 gives an equivalence between this set and ℕ+, as we will formalize
 below. -/
def PrimeMultiset :=
  Multiset Nat.Primes deriving Inhabited, CanonicallyOrderedAddMonoid, DistribLattice,
  SemilatticeSup, Sub
#align prime_multiset PrimeMultiset

instance : OrderBot PrimeMultiset where
  bot_le := by simp only [bot_le, forall_const]
               -- 🎉 no goals

instance : OrderedSub PrimeMultiset where
  tsub_le_iff_right _ _ _ := Multiset.sub_le_iff_le_add

namespace PrimeMultiset

-- `@[derive]` doesn't work for `meta` instances
unsafe instance : Repr PrimeMultiset := by delta PrimeMultiset; infer_instance
                                           -- ⊢ Repr (Multiset Nat.Primes)
                                                                -- 🎉 no goals

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
def toNatMultiset : PrimeMultiset → Multiset ℕ := fun v => v.map Coe.coe
#align prime_multiset.to_nat_multiset PrimeMultiset.toNatMultiset

instance coeNat : Coe PrimeMultiset (Multiset ℕ) :=
  ⟨toNatMultiset⟩
#align prime_multiset.coe_nat PrimeMultiset.coeNat

/-- `PrimeMultiset.coe`, the coercion from a multiset of primes to a multiset of
naturals, promoted to an `AddMonoidHom`. -/
def coeNatMonoidHom : PrimeMultiset →+ Multiset ℕ :=
  { Multiset.mapAddMonoidHom Coe.coe with toFun := Coe.coe }
#align prime_multiset.coe_nat_monoid_hom PrimeMultiset.coeNatMonoidHom

@[simp]
theorem coe_coeNatMonoidHom : (coeNatMonoidHom : PrimeMultiset → Multiset ℕ) = Coe.coe :=
  rfl
#align prime_multiset.coe_coe_nat_monoid_hom PrimeMultiset.coe_coeNatMonoidHom

theorem coeNat_injective : Function.Injective (Coe.coe : PrimeMultiset → Multiset ℕ) :=
  Multiset.map_injective Nat.Primes.coe_nat_injective
#align prime_multiset.coe_nat_injective PrimeMultiset.coeNat_injective

theorem coeNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ) = {(p : ℕ)} :=
  rfl
#align prime_multiset.coe_nat_of_prime PrimeMultiset.coeNat_ofPrime

theorem coeNat_prime (v : PrimeMultiset) (p : ℕ) (h : p ∈ (v : Multiset ℕ)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  -- ⊢ Nat.Prime p
  exact h_eq ▸ hp'
  -- 🎉 no goals
#align prime_multiset.coe_nat_prime PrimeMultiset.coeNat_prime

/-- Converts a `PrimeMultiset` to a `Multiset ℕ+`. -/
def toPNatMultiset : PrimeMultiset → Multiset ℕ+ := fun v => v.map Coe.coe
#align prime_multiset.to_pnat_multiset PrimeMultiset.toPNatMultiset

instance coePNat : Coe PrimeMultiset (Multiset ℕ+) :=
  ⟨toPNatMultiset⟩
#align prime_multiset.coe_pnat PrimeMultiset.coePNat

/-- `coePNat`, the coercion from a multiset of primes to a multiset of positive
naturals, regarded as an `AddMonoidHom`. -/
def coePNatMonoidHom : PrimeMultiset →+ Multiset ℕ+ :=
  { Multiset.mapAddMonoidHom Coe.coe with toFun := Coe.coe }
#align prime_multiset.coe_pnat_monoid_hom PrimeMultiset.coePNatMonoidHom

@[simp]
theorem coe_coePNatMonoidHom : (coePNatMonoidHom : PrimeMultiset → Multiset ℕ+) = Coe.coe :=
  rfl
#align prime_multiset.coe_coe_pnat_monoid_hom PrimeMultiset.coe_coePNatMonoidHom

theorem coePNat_injective : Function.Injective (Coe.coe : PrimeMultiset → Multiset ℕ+) :=
  Multiset.map_injective Nat.Primes.coe_pnat_injective
#align prime_multiset.coe_pnat_injective PrimeMultiset.coePNat_injective

theorem coePNat_ofPrime (p : Nat.Primes) : (ofPrime p : Multiset ℕ+) = {(p : ℕ+)} :=
  rfl
#align prime_multiset.coe_pnat_of_prime PrimeMultiset.coePNat_ofPrime

theorem coePNat_prime (v : PrimeMultiset) (p : ℕ+) (h : p ∈ (v : Multiset ℕ+)) : p.Prime := by
  rcases Multiset.mem_map.mp h with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
  -- ⊢ PNat.Prime p
  exact h_eq ▸ hp'
  -- 🎉 no goals
#align prime_multiset.coe_pnat_prime PrimeMultiset.coePNat_prime

instance coeMultisetPNatNat : Coe (Multiset ℕ+) (Multiset ℕ) :=
  ⟨fun v => v.map Coe.coe⟩
#align prime_multiset.coe_multiset_pnat_nat PrimeMultiset.coeMultisetPNatNat

theorem coePNat_nat (v : PrimeMultiset) : ((v : Multiset ℕ+) : Multiset ℕ) = (v : Multiset ℕ) := by
  change (v.map (Coe.coe : Nat.Primes → ℕ+)).map Subtype.val = v.map Subtype.val
  -- ⊢ Multiset.map Subtype.val (Multiset.map Coe.coe v) = Multiset.map Subtype.val v
  rw [Multiset.map_map]
  -- ⊢ Multiset.map (Subtype.val ∘ Coe.coe) v = Multiset.map Subtype.val v
  congr
  -- 🎉 no goals
#align prime_multiset.coe_pnat_nat PrimeMultiset.coePNat_nat

/-- The product of a `PrimeMultiset`, as a `ℕ+`. -/
def prod (v : PrimeMultiset) : ℕ+ :=
  (v : Multiset PNat).prod
#align prime_multiset.prod PrimeMultiset.prod

theorem coe_prod (v : PrimeMultiset) : (v.prod : ℕ) = (v : Multiset ℕ).prod := by
  let h : (v.prod : ℕ) = ((v.map Coe.coe).map Coe.coe).prod :=
    PNat.coeMonoidHom.map_multiset_prod v.toPNatMultiset
  rw [Multiset.map_map] at h
  -- ⊢ ↑(prod v) = Multiset.prod (toNatMultiset v)
  have : (Coe.coe : ℕ+ → ℕ) ∘ (Coe.coe : Nat.Primes → ℕ+) = Coe.coe := funext fun p => rfl
  -- ⊢ ↑(prod v) = Multiset.prod (toNatMultiset v)
  rw [this] at h; exact h
  -- ⊢ ↑(prod v) = Multiset.prod (toNatMultiset v)
                  -- 🎉 no goals
#align prime_multiset.coe_prod PrimeMultiset.coe_prod

theorem prod_ofPrime (p : Nat.Primes) : (ofPrime p).prod = (p : ℕ+) :=
  Multiset.prod_singleton _
#align prime_multiset.prod_of_prime PrimeMultiset.prod_ofPrime

/-- If a `Multiset ℕ` consists only of primes, it can be recast as a `PrimeMultiset`. -/
def ofNatMultiset (v : Multiset ℕ) (h : ∀ p : ℕ, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ Nat.Primes Nat.Prime (fun p hp => ⟨p, hp⟩) v h
#align prime_multiset.of_nat_multiset PrimeMultiset.ofNatMultiset

theorem to_ofNatMultiset (v : Multiset ℕ) (h) : (ofNatMultiset v h : Multiset ℕ) = v := by
  dsimp [ofNatMultiset, toNatMultiset]
  -- ⊢ Multiset.map Coe.coe (Multiset.pmap (fun p hp => { val := p, property := hp  …
  have : (fun p h => (Coe.coe : Nat.Primes → ℕ) ⟨p, h⟩) = fun p _ => id p := by
    funext p h
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]
  -- 🎉 no goals
#align prime_multiset.to_of_nat_multiset PrimeMultiset.to_ofNatMultiset

theorem prod_ofNatMultiset (v : Multiset ℕ) (h) : ((ofNatMultiset v h).prod : ℕ) = (v.prod : ℕ) :=
  by rw [coe_prod, to_ofNatMultiset]
     -- 🎉 no goals
#align prime_multiset.prod_of_nat_multiset PrimeMultiset.prod_ofNatMultiset

/-- If a `Multiset ℕ+` consists only of primes, it can be recast as a `PrimeMultiset`. -/
def ofPNatMultiset (v : Multiset ℕ+) (h : ∀ p : ℕ+, p ∈ v → p.Prime) : PrimeMultiset :=
  @Multiset.pmap ℕ+ Nat.Primes PNat.Prime (fun p hp => ⟨(p : ℕ), hp⟩) v h
#align prime_multiset.of_pnat_multiset PrimeMultiset.ofPNatMultiset

theorem to_ofPNatMultiset (v : Multiset ℕ+) (h) : (ofPNatMultiset v h : Multiset ℕ+) = v := by
  dsimp [ofPNatMultiset, toPNatMultiset]
  -- ⊢ Multiset.map Coe.coe (Multiset.pmap (fun p hp => { val := ↑p, property := hp …
  have : (fun (p : ℕ+) (h : p.Prime) => (Coe.coe : Nat.Primes → ℕ+) ⟨p, h⟩) = fun p _ => id p := by
    funext p h
    apply Subtype.eq
    rfl
  rw [Multiset.map_pmap, this, Multiset.pmap_eq_map, Multiset.map_id]
  -- 🎉 no goals
#align prime_multiset.to_of_pnat_multiset PrimeMultiset.to_ofPNatMultiset

theorem prod_ofPNatMultiset (v : Multiset ℕ+) (h) : ((ofPNatMultiset v h).prod : ℕ+) = v.prod := by
  dsimp [prod]
  -- ⊢ Multiset.prod (toPNatMultiset (ofPNatMultiset v h)) = Multiset.prod v
  rw [to_ofPNatMultiset]
  -- 🎉 no goals
#align prime_multiset.prod_of_pnat_multiset PrimeMultiset.prod_ofPNatMultiset

/-- Lists can be coerced to multisets; here we have some results
about how this interacts with our constructions on multisets. -/
def ofNatList (l : List ℕ) (h : ∀ p : ℕ, p ∈ l → p.Prime) : PrimeMultiset :=
  ofNatMultiset (l : Multiset ℕ) h
#align prime_multiset.of_nat_list PrimeMultiset.ofNatList

theorem prod_ofNatList (l : List ℕ) (h) : ((ofNatList l h).prod : ℕ) = l.prod := by
  have := prod_ofNatMultiset (l : Multiset ℕ) h
  -- ⊢ ↑(prod (ofNatList l h)) = List.prod l
  rw [Multiset.coe_prod] at this
  -- ⊢ ↑(prod (ofNatList l h)) = List.prod l
  exact this
  -- 🎉 no goals
#align prime_multiset.prod_of_nat_list PrimeMultiset.prod_ofNatList

/-- If a `List ℕ+` consists only of primes, it can be recast as a `PrimeMultiset` with
the coercion from lists to multisets. -/
def ofPNatList (l : List ℕ+) (h : ∀ p : ℕ+, p ∈ l → p.Prime) : PrimeMultiset :=
  ofPNatMultiset (l : Multiset ℕ+) h
#align prime_multiset.of_pnat_list PrimeMultiset.ofPNatList

theorem prod_ofPNatList (l : List ℕ+) (h) : (ofPNatList l h).prod = l.prod := by
  have := prod_ofPNatMultiset (l : Multiset ℕ+) h
  -- ⊢ prod (ofPNatList l h) = List.prod l
  rw [Multiset.coe_prod] at this
  -- ⊢ prod (ofPNatList l h) = List.prod l
  exact this
  -- 🎉 no goals
#align prime_multiset.prod_of_pnat_list PrimeMultiset.prod_ofPNatList

/-- The product map gives a homomorphism from the additive monoid
of multisets to the multiplicative monoid ℕ+. -/
theorem prod_zero : (0 : PrimeMultiset).prod = 1 := by
  exact Multiset.prod_zero
  -- 🎉 no goals
#align prime_multiset.prod_zero PrimeMultiset.prod_zero

theorem prod_add (u v : PrimeMultiset) : (u + v).prod = u.prod * v.prod := by
  change (coePNatMonoidHom (u + v)).prod = _
  -- ⊢ Multiset.prod (↑coePNatMonoidHom (u + v)) = prod u * prod v
  rw [coePNatMonoidHom.map_add]
  -- ⊢ Multiset.prod (↑coePNatMonoidHom u + ↑coePNatMonoidHom v) = prod u * prod v
  exact Multiset.prod_add _ _
  -- 🎉 no goals
#align prime_multiset.prod_add PrimeMultiset.prod_add

-- Porting note: Need to replace ^ with Pow.pow to get the original mathlib statement
theorem prod_smul (d : ℕ) (u : PrimeMultiset) : (d • u).prod = Pow.pow u.prod d := by
  induction' d with n ih
  -- ⊢ prod (Nat.zero • u) = Pow.pow (prod u) Nat.zero
  · rfl
    -- 🎉 no goals
  · have : ∀ n' : ℕ, Pow.pow (prod u) n' = Monoid.npow n' (prod u) := fun _ ↦ rfl
    -- ⊢ prod (Nat.succ n • u) = Pow.pow (prod u) (Nat.succ n)
    rw [succ_nsmul, prod_add, ih, this, this, Monoid.npow_succ, mul_comm]
    -- 🎉 no goals
#align prime_multiset.prod_smul PrimeMultiset.prod_smul

end PrimeMultiset

namespace PNat

/-- The prime factors of n, regarded as a multiset -/
def factorMultiset (n : ℕ+) : PrimeMultiset :=
  PrimeMultiset.ofNatList (Nat.factors n) (@Nat.prime_of_mem_factors n)
#align pnat.factor_multiset PNat.factorMultiset

/-- The product of the factors is the original number -/
theorem prod_factorMultiset (n : ℕ+) : (factorMultiset n).prod = n :=
  eq <| by
    dsimp [factorMultiset]
    -- ⊢ ↑(PrimeMultiset.prod (PrimeMultiset.ofNatList (Nat.factors ↑n) (_ : ∀ {p : ℕ …
    rw [PrimeMultiset.prod_ofNatList]
    -- ⊢ List.prod (Nat.factors ↑n) = ↑n
    exact Nat.prod_factors n.ne_zero
    -- 🎉 no goals
#align pnat.prod_factor_multiset PNat.prod_factorMultiset

theorem coeNat_factorMultiset (n : ℕ+) :
    (factorMultiset n : Multiset ℕ) = (Nat.factors n : Multiset ℕ) :=
  PrimeMultiset.to_ofNatMultiset (Nat.factors n) (@Nat.prime_of_mem_factors n)
#align pnat.coe_nat_factor_multiset PNat.coeNat_factorMultiset

end PNat

namespace PrimeMultiset

/-- If we start with a multiset of primes, take the product and
 then factor it, we get back the original multiset. -/
theorem factorMultiset_prod (v : PrimeMultiset) : v.prod.factorMultiset = v := by
  apply PrimeMultiset.coeNat_injective
  -- ⊢ Coe.coe (PNat.factorMultiset (prod v)) = Coe.coe v
  suffices toNatMultiset (PNat.factorMultiset (prod v)) = toNatMultiset v by exact this
  -- ⊢ toNatMultiset (PNat.factorMultiset (prod v)) = toNatMultiset v
  rw [v.prod.coeNat_factorMultiset, PrimeMultiset.coe_prod]
  -- ⊢ ↑(Nat.factors (Multiset.prod (toNatMultiset v))) = toNatMultiset v
  rcases v with ⟨l⟩
  -- ⊢ ↑(Nat.factors (Multiset.prod (toNatMultiset (Quot.mk Setoid.r l)))) = toNatM …
  --unfold_coes
  dsimp [PrimeMultiset.toNatMultiset]
  -- ⊢ ↑(Nat.factors (Multiset.prod ↑(List.map Coe.coe l))) = ↑(List.map Coe.coe l)
  rw [Multiset.coe_prod]
  -- ⊢ ↑(Nat.factors (List.prod (List.map Coe.coe l))) = ↑(List.map Coe.coe l)
  let l' := l.map (Coe.coe : Nat.Primes → ℕ)
  -- ⊢ ↑(Nat.factors (List.prod (List.map Coe.coe l))) = ↑(List.map Coe.coe l)
  have : ∀ p : ℕ, p ∈ l' → p.Prime := fun p hp => by
    rcases List.mem_map.mp hp with ⟨⟨_, hp'⟩, ⟨_, h_eq⟩⟩
    exact h_eq ▸ hp'
  exact Multiset.coe_eq_coe.mpr (@Nat.factors_unique _ l' rfl this).symm
  -- 🎉 no goals
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
  simp [factorMultiset, PrimeMultiset.ofNatList, PrimeMultiset.ofNatMultiset]
  -- 🎉 no goals
#align pnat.factor_multiset_one PNat.factorMultiset_one

theorem factorMultiset_mul (n m : ℕ+) :
    factorMultiset (n * m) = factorMultiset n + factorMultiset m := by
  let u := factorMultiset n
  -- ⊢ factorMultiset (n * m) = factorMultiset n + factorMultiset m
  let v := factorMultiset m
  -- ⊢ factorMultiset (n * m) = factorMultiset n + factorMultiset m
  have : n = u.prod := (prod_factorMultiset n).symm; rw [this]
  -- ⊢ factorMultiset (n * m) = factorMultiset n + factorMultiset m
                                                     -- ⊢ factorMultiset (PrimeMultiset.prod u * m) = factorMultiset (PrimeMultiset.pr …
  have : m = v.prod := (prod_factorMultiset m).symm; rw [this]
  -- ⊢ factorMultiset (PrimeMultiset.prod u * m) = factorMultiset (PrimeMultiset.pr …
                                                     -- ⊢ factorMultiset (PrimeMultiset.prod u * PrimeMultiset.prod v) = factorMultise …
  rw [← PrimeMultiset.prod_add]
  -- ⊢ factorMultiset (PrimeMultiset.prod (u + v)) = factorMultiset (PrimeMultiset. …
  repeat' rw [PrimeMultiset.factorMultiset_prod]
  -- 🎉 no goals
#align pnat.factor_multiset_mul PNat.factorMultiset_mul

theorem factorMultiset_pow (n : ℕ+) (m : ℕ) :
    factorMultiset (Pow.pow n m ) = m • factorMultiset n := by
  let u := factorMultiset n
  -- ⊢ factorMultiset (Pow.pow n m) = m • factorMultiset n
  have : n = u.prod := (prod_factorMultiset n).symm
  -- ⊢ factorMultiset (Pow.pow n m) = m • factorMultiset n
  rw [this, ← PrimeMultiset.prod_smul]
  -- ⊢ factorMultiset (PrimeMultiset.prod (m • u)) = m • factorMultiset (PrimeMulti …
  repeat' rw [PrimeMultiset.factorMultiset_prod]
  -- 🎉 no goals
#align pnat.factor_multiset_pow PNat.factorMultiset_pow

/-- Factoring a prime gives the corresponding one-element multiset. -/
theorem factorMultiset_ofPrime (p : Nat.Primes) :
    (p : ℕ+).factorMultiset = PrimeMultiset.ofPrime p := by
  apply factorMultisetEquiv.symm.injective
  -- ⊢ ↑factorMultisetEquiv.symm (factorMultiset ↑p) = ↑factorMultisetEquiv.symm (P …
  change (p : ℕ+).factorMultiset.prod = (PrimeMultiset.ofPrime p).prod
  -- ⊢ PrimeMultiset.prod (factorMultiset ↑p) = PrimeMultiset.prod (PrimeMultiset.o …
  rw [(p : ℕ+).prod_factorMultiset, PrimeMultiset.prod_ofPrime]
  -- 🎉 no goals
#align pnat.factor_multiset_of_prime PNat.factorMultiset_ofPrime

/-- We now have four different results that all encode the
 idea that inequality of multisets corresponds to divisibility
 of positive integers. -/
theorem factorMultiset_le_iff {m n : ℕ+} : factorMultiset m ≤ factorMultiset n ↔ m ∣ n := by
  constructor
  -- ⊢ factorMultiset m ≤ factorMultiset n → m ∣ n
  · intro h
    -- ⊢ m ∣ n
    rw [← prod_factorMultiset m, ← prod_factorMultiset m]
    -- ⊢ PrimeMultiset.prod (factorMultiset (PrimeMultiset.prod (factorMultiset m)))  …
    apply Dvd.intro (n.factorMultiset - m.factorMultiset).prod
    -- ⊢ PrimeMultiset.prod (factorMultiset (PrimeMultiset.prod (factorMultiset m)))  …
    rw [← PrimeMultiset.prod_add, PrimeMultiset.factorMultiset_prod, add_tsub_cancel_of_le h,
      prod_factorMultiset]
  · intro h
    -- ⊢ factorMultiset m ≤ factorMultiset n
    rw [← mul_div_exact h, factorMultiset_mul]
    -- ⊢ factorMultiset m ≤ factorMultiset m + factorMultiset (divExact n m)
    exact le_self_add
    -- 🎉 no goals
#align pnat.factor_multiset_le_iff PNat.factorMultiset_le_iff

theorem factorMultiset_le_iff' {m : ℕ+} {v : PrimeMultiset} :
    factorMultiset m ≤ v ↔ m ∣ v.prod := by
  let h := @factorMultiset_le_iff m v.prod
  -- ⊢ factorMultiset m ≤ v ↔ m ∣ PrimeMultiset.prod v
  rw [v.factorMultiset_prod] at h
  -- ⊢ factorMultiset m ≤ v ↔ m ∣ PrimeMultiset.prod v
  exact h
  -- 🎉 no goals
#align pnat.factor_multiset_le_iff' PNat.factorMultiset_le_iff'

end PNat

namespace PrimeMultiset

theorem prod_dvd_iff {u v : PrimeMultiset} : u.prod ∣ v.prod ↔ u ≤ v := by
  let h := @PNat.factorMultiset_le_iff' u.prod v
  -- ⊢ prod u ∣ prod v ↔ u ≤ v
  rw [u.factorMultiset_prod] at h
  -- ⊢ prod u ∣ prod v ↔ u ≤ v
  exact h.symm
  -- 🎉 no goals
#align prime_multiset.prod_dvd_iff PrimeMultiset.prod_dvd_iff

theorem prod_dvd_iff' {u : PrimeMultiset} {n : ℕ+} : u.prod ∣ n ↔ u ≤ n.factorMultiset := by
  let h := @prod_dvd_iff u n.factorMultiset
  -- ⊢ prod u ∣ n ↔ u ≤ PNat.factorMultiset n
  rw [n.prod_factorMultiset] at h
  -- ⊢ prod u ∣ n ↔ u ≤ PNat.factorMultiset n
  exact h
  -- 🎉 no goals
#align prime_multiset.prod_dvd_iff' PrimeMultiset.prod_dvd_iff'

end PrimeMultiset

namespace PNat

/-- The gcd and lcm operations on positive integers correspond
 to the inf and sup operations on multisets. -/
theorem factorMultiset_gcd (m n : ℕ+) :
    factorMultiset (gcd m n) = factorMultiset m ⊓ factorMultiset n := by
  apply le_antisymm
  -- ⊢ factorMultiset (gcd m n) ≤ factorMultiset m ⊓ factorMultiset n
  · apply le_inf_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    -- ⊢ factorMultiset (gcd m n) ≤ factorMultiset m ∧ factorMultiset (gcd m n) ≤ fac …
                          -- ⊢ factorMultiset (gcd m n) ≤ factorMultiset m
                                          -- ⊢ gcd m n ∣ m
                                          -- ⊢ gcd m n ∣ n
    exact gcd_dvd_left m n
    -- ⊢ gcd m n ∣ n
    exact gcd_dvd_right m n
    -- 🎉 no goals
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    -- ⊢ PrimeMultiset.prod (factorMultiset m ⊓ factorMultiset n) ∣ gcd m n
    apply dvd_gcd <;> rw [PrimeMultiset.prod_dvd_iff']
    -- ⊢ PrimeMultiset.prod (factorMultiset m ⊓ factorMultiset n) ∣ m
                      -- ⊢ factorMultiset m ⊓ factorMultiset n ≤ factorMultiset m
                      -- ⊢ factorMultiset m ⊓ factorMultiset n ≤ factorMultiset n
    exact inf_le_left
    -- ⊢ factorMultiset m ⊓ factorMultiset n ≤ factorMultiset n
    exact inf_le_right
    -- 🎉 no goals
#align pnat.factor_multiset_gcd PNat.factorMultiset_gcd

theorem factorMultiset_lcm (m n : ℕ+) :
    factorMultiset (lcm m n) = factorMultiset m ⊔ factorMultiset n := by
  apply le_antisymm
  -- ⊢ factorMultiset (lcm m n) ≤ factorMultiset m ⊔ factorMultiset n
  · rw [← PrimeMultiset.prod_dvd_iff, prod_factorMultiset]
    -- ⊢ lcm m n ∣ PrimeMultiset.prod (factorMultiset m ⊔ factorMultiset n)
    apply lcm_dvd <;> rw [← factorMultiset_le_iff']
    -- ⊢ m ∣ PrimeMultiset.prod (factorMultiset m ⊔ factorMultiset n)
                      -- ⊢ factorMultiset m ≤ factorMultiset m ⊔ factorMultiset n
                      -- ⊢ factorMultiset n ≤ factorMultiset m ⊔ factorMultiset n
    exact le_sup_left
    -- ⊢ factorMultiset n ≤ factorMultiset m ⊔ factorMultiset n
    exact le_sup_right
    -- 🎉 no goals
  · apply sup_le_iff.mpr; constructor <;> apply factorMultiset_le_iff.mpr
    -- ⊢ factorMultiset m ≤ factorMultiset (lcm m n) ∧ factorMultiset n ≤ factorMulti …
                          -- ⊢ factorMultiset m ≤ factorMultiset (lcm m n)
                                          -- ⊢ m ∣ lcm m n
                                          -- ⊢ n ∣ lcm m n
    exact dvd_lcm_left m n
    -- ⊢ n ∣ lcm m n
    exact dvd_lcm_right m n
    -- 🎉 no goals
#align pnat.factor_multiset_lcm PNat.factorMultiset_lcm

/-- The number of occurrences of p in the factor multiset of m
 is the same as the p-adic valuation of m. -/
theorem count_factorMultiset (m : ℕ+) (p : Nat.Primes) (k : ℕ) :
    Pow.pow (p : ℕ+) k ∣ m ↔ k ≤ m.factorMultiset.count p := by
  intros
  -- ⊢ Pow.pow (↑p) k ∣ m ↔ k ≤ Multiset.count p (factorMultiset m)
  rw [Multiset.le_count_iff_replicate_le, ← factorMultiset_le_iff, factorMultiset_pow,
    factorMultiset_ofPrime]
  congr! 2
  -- ⊢ k • PrimeMultiset.ofPrime p = Multiset.replicate k p
  apply Multiset.eq_replicate.mpr
  -- ⊢ ↑Multiset.card (k • PrimeMultiset.ofPrime p) = k ∧ ∀ (b : Nat.Primes), b ∈ k …
  constructor
  -- ⊢ ↑Multiset.card (k • PrimeMultiset.ofPrime p) = k
  · rw [Multiset.card_nsmul, PrimeMultiset.card_ofPrime, mul_one]
    -- 🎉 no goals
  · intro q h
    -- ⊢ q = p
    rw [PrimeMultiset.ofPrime, Multiset.nsmul_singleton _ k] at h
    -- ⊢ q = p
    exact Multiset.eq_of_mem_replicate h
    -- 🎉 no goals
#align pnat.count_factor_multiset PNat.count_factorMultiset

end PNat

namespace PrimeMultiset

theorem prod_inf (u v : PrimeMultiset) : (u ⊓ v).prod = PNat.gcd u.prod v.prod := by
  let n := u.prod
  -- ⊢ prod (u ⊓ v) = PNat.gcd (prod u) (prod v)
  let m := v.prod
  -- ⊢ prod (u ⊓ v) = PNat.gcd (prod u) (prod v)
  change (u ⊓ v).prod = PNat.gcd n m
  -- ⊢ prod (u ⊓ v) = PNat.gcd n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  -- ⊢ prod (u ⊓ v) = PNat.gcd n m
                                                             -- ⊢ prod (PNat.factorMultiset n ⊓ v) = PNat.gcd n m
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  -- ⊢ prod (PNat.factorMultiset n ⊓ v) = PNat.gcd n m
                                                             -- ⊢ prod (PNat.factorMultiset n ⊓ PNat.factorMultiset m) = PNat.gcd n m
  rw [← PNat.factorMultiset_gcd n m, PNat.prod_factorMultiset]
  -- 🎉 no goals
#align prime_multiset.prod_inf PrimeMultiset.prod_inf

theorem prod_sup (u v : PrimeMultiset) : (u ⊔ v).prod = PNat.lcm u.prod v.prod := by
  let n := u.prod
  -- ⊢ prod (u ⊔ v) = PNat.lcm (prod u) (prod v)
  let m := v.prod
  -- ⊢ prod (u ⊔ v) = PNat.lcm (prod u) (prod v)
  change (u ⊔ v).prod = PNat.lcm n m
  -- ⊢ prod (u ⊔ v) = PNat.lcm n m
  have : u = n.factorMultiset := u.factorMultiset_prod.symm; rw [this]
  -- ⊢ prod (u ⊔ v) = PNat.lcm n m
                                                             -- ⊢ prod (PNat.factorMultiset n ⊔ v) = PNat.lcm n m
  have : v = m.factorMultiset := v.factorMultiset_prod.symm; rw [this]
  -- ⊢ prod (PNat.factorMultiset n ⊔ v) = PNat.lcm n m
                                                             -- ⊢ prod (PNat.factorMultiset n ⊔ PNat.factorMultiset m) = PNat.lcm n m
  rw [← PNat.factorMultiset_lcm n m, PNat.prod_factorMultiset]
  -- 🎉 no goals
#align prime_multiset.prod_sup PrimeMultiset.prod_sup

end PrimeMultiset
