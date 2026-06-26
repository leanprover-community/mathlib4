/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs

/-! # Antidiagonal with values in general types

We define a type class `Finset.HasAntidiagonal A` which contains a function
`antidiagonal : A → Finset (A × A)` such that `antidiagonal n`
is the finset of all pairs adding to `n`, as witnessed by `mem_antidiagonal`.

Analogously, the type class `Finset.HasMulAntidiagonal A` contains a function
`mulAntidiagonal : A → Finset (A × A)` such that `mulAntidiagonal n`
is the finset of all pairs multiplying to `n`, as witnessed by `mem_mulAntidiagonal`.

When `A` is a canonically ordered additive monoid with locally finite order
this typeclass can be instantiated with `Finset.antidiagonalOfLocallyFinite`.
This applies in particular when `A` is `ℕ`, more generally or `σ →₀ ℕ`,
or even `ι →₀ A`  under the additional assumption `OrderedSub A`
that make it a canonically ordered additive monoid.
(In fact, we would just need an `AddMonoid` with a compatible order,
finite `Iic`, such that if `a + b = n`, then `a, b ≤ n`,
and any finiteness condition would be OK.)

For computational reasons it is better to manually provide instances for `ℕ`
and `σ →₀ ℕ`, to avoid quadratic runtime performance.
These instances are provided as `Finset.Nat.instHasAntidiagonal` and
`Finsupp.instHasAntidiagonal`.
This is why `Finset.mulAntidiagonalOfLocallyFinite` is an `abbrev` and not an `instance`.

This definition does not exactly match with that of `Multiset.antidiagonal`
defined in `Mathlib/Data/Multiset/Antidiagonal.lean`, because of the multiplicities.
Indeed, by counting multiplicities, `Multiset α` is equivalent to `α →₀ ℕ`,
but `Finset.antidiagonal` and `Multiset.antidiagonal` will return different objects.
For example, for `s : Multiset ℕ := {0,0,0}`, `Multiset.antidiagonal s` has 8 elements
but `Finset.antidiagonal s` has only 4.

```lean
def s : Multiset ℕ := {0, 0, 0}
#eval (Finset.antidiagonal s).card -- 4
#eval Multiset.card (Multiset.antidiagonal s) -- 8
```

## TODO

* For `PNat`, `HasMulAntidiagonal` will recover the set of divisors of a strictly positive integer.
-/

@[expose] public section

open Function

namespace Finset

/-- The class of additive monoids with an antidiagonal. -/
class HasAntidiagonal (A : Type*) [AddMonoid A] where
  /-- The antidiagonal of an element `n` is the finset of pairs `(i, j)` such that
  `i + j = n`. -/
  antidiagonal : A → Finset (A × A)
  /-- A pair belongs to `antidiagonal n` iff the sum of its components is equal to `n`. -/
  mem_antidiagonal {n} {a} : a ∈ antidiagonal n ↔ a.fst + a.snd = n

export HasAntidiagonal (antidiagonal mem_antidiagonal)

attribute [simp] mem_antidiagonal

/-- The class of (multiplicative) monoids with a mulAntidiagonal. -/
class HasMulAntidiagonal (A : Type*) [Monoid A] where
  /-- The mulAntidiagonal of an element `n` is the finset of pairs `(i, j)` such that
  `i * j = n`. -/
  mulAntidiagonal : A → Finset (A × A)
  /-- A pair belongs to `mulAntidiagonal n` iff the product of its components is equal to `n`. -/
  mem_mulAntidiagonal {n} {a} : a ∈ mulAntidiagonal n ↔ a.fst * a.snd = n

attribute [to_additive] HasMulAntidiagonal

export HasMulAntidiagonal (mulAntidiagonal mem_mulAntidiagonal)

attribute [simp] HasMulAntidiagonal.mem_mulAntidiagonal

variable {A : Type*}

namespace HasMulAntidiagonal

/-- All `HasMulAntidiagonal` instances are equal -/
@[to_additive /-- All `HasAntidiagonal` instances are equal -/]
instance [Monoid A] : Subsingleton (HasMulAntidiagonal A) where
  allEq := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    congr with n xy
    rw [ha, hb]

-- The goal of this lemma is to allow to rewrite mulAntidiagonal/antidiagonal
-- when the decidability instances obfuscate Lean
set_option linter.overlappingInstances false in
@[to_additive]
lemma congr (A : Type*) [Monoid A]
    [H1 : HasMulAntidiagonal A] [H2 : HasMulAntidiagonal A] :
    H1.mulAntidiagonal = H2.mulAntidiagonal := by congr!; subsingleton

@[to_additive]
theorem swap_mem_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} {xy : A × A} :
    xy.swap ∈ mulAntidiagonal n ↔ xy ∈ mulAntidiagonal n := by
  simp [mul_comm]

@[to_additive (attr := simp) map_prodComm_antidiagonal]
theorem map_prodComm_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} :
    (mulAntidiagonal n).map (Equiv.prodComm A A) = mulAntidiagonal n :=
  Finset.ext fun ⟨a, b⟩ => by simp [mul_comm]

/-- See also `Finset.map_prodComm_mulAntidiagonal`. -/
@[to_additive (attr := simp)]
theorem map_swap_mulAntidiagonal [CommMonoid A] [HasMulAntidiagonal A] {n : A} :
    (mulAntidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = mulAntidiagonal n :=
  map_prodComm_mulAntidiagonal

section CancelMonoid

variable [CancelMonoid A] [HasMulAntidiagonal A] {p q : A × A} {n : A}

/-- A point in the mulAntidiagonal is determined by its first coordinate.

See also `Finset.mulAntidiagonal_congr'`. -/
@[to_additive
/-- A point in the antidiagonal is determined by its first coordinate.

See also `Finset.antidiagonal_congr'`. -/]
theorem mulAntidiagonal_congr (hp : p ∈ mulAntidiagonal n) (hq : q ∈ mulAntidiagonal n) :
    p = q ↔ p.1 = q.1 := by
  refine ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((mul_right_inj q.fst).mp ?_)⟩
  rw [mem_mulAntidiagonal] at hp hq
  rw [hq, ← h, hp]

/-- A point in the mulAntidiagonal is determined by its first co-ordinate (subtype version of
`Finset.mulAntidiagonal_congr`). This lemma is used by the `ext` tactic. -/
@[to_additive (attr := ext)
/-- A point in the antidiagonal is determined by its first co-ordinate (subtype version of
`Finset.antidiagonal_congr`). This lemma is used by the `ext` tactic. -/]
theorem mulAntidiagonal_subtype_ext {p q : mulAntidiagonal n} (h : p.val.1 = q.val.1) : p = q :=
  Subtype.ext ((mulAntidiagonal_congr p.prop q.prop).mpr h)

end CancelMonoid

section CancelCommMonoid
variable [CancelCommMonoid A] [HasMulAntidiagonal A] {p q : A × A} {n : A}

/-- A point in the mulAntidiagonal is determined by its second coordinate.

See also `Finset.mulAntidiagonal_congr`. -/
@[to_additive /-- A point in the antidiagonal is determined by its second coordinate.

See also `Finset.antidiagonal_congr`. -/]
lemma mulAntidiagonal_congr' (hp : p ∈ mulAntidiagonal n) (hq : q ∈ mulAntidiagonal n) :
    p = q ↔ p.2 = q.2 := by
  rw [← Prod.swap_inj]
  exact mulAntidiagonal_congr (swap_mem_mulAntidiagonal.2 hp) (swap_mem_mulAntidiagonal.2 hq)

end CancelCommMonoid

section CanonicallyOrderedMul

variable [CommMonoid A] [PartialOrder A] [CanonicallyOrderedMul A] [HasMulAntidiagonal A]

@[to_additive (attr := simp)]
theorem mulAntidiagonal_one : mulAntidiagonal (1 : A) = {(1, 1)} := by
  ext ⟨x, y⟩
  simp

@[to_additive]
theorem mulAntidiagonal.fst_le {n : A} {kl : A × A} (hlk : kl ∈ mulAntidiagonal n) : kl.1 ≤ n := by
  rw [le_iff_exists_mul]
  use kl.2
  rwa [mem_mulAntidiagonal, eq_comm] at hlk

@[to_additive]
theorem mulAntidiagonal.snd_le {n : A} {kl : A × A} (hlk : kl ∈ mulAntidiagonal n) : kl.2 ≤ n := by
  rw [le_iff_exists_mul]
  use kl.1
  rwa [mem_mulAntidiagonal, eq_comm, mul_comm] at hlk

end CanonicallyOrderedMul

end HasMulAntidiagonal

namespace HasAntidiagonal
section OrderedSub

variable [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A] [Sub A] [OrderedSub A]
variable [AddLeftReflectLE A]
variable [HasAntidiagonal A]

theorem filter_fst_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m ≤ n)] :
    {x ∈ antidiagonal n | x.fst = m} = if m ≤ n then {(m, n - m)} else ∅ := by
  ext ⟨a, b⟩
  suffices a = m → (a + b = n ↔ m ≤ n ∧ b = n - m) by
    rw [mem_filter, mem_antidiagonal, apply_ite (fun n ↦ (a, b) ∈ n), mem_singleton,
      Prod.mk_inj, ite_prop_iff_or]
    simpa [← and_assoc, @and_right_comm _ (a = _), and_congr_left_iff]
  rintro rfl
  constructor
  · rintro rfl
    exact ⟨le_add_right le_rfl, (add_tsub_cancel_left _ _).symm⟩
  · rintro ⟨h, rfl⟩
    exact add_tsub_cancel_of_le h

theorem filter_snd_eq_antidiagonal (n m : A) [DecidablePred (· = m)] [Decidable (m ≤ n)] :
    {x ∈ antidiagonal n | x.snd = m} = if m ≤ n then {(n - m, m)} else ∅ := by
  rw [← map_swap_antidiagonal, filter_map]
  simp [filter_fst_eq_antidiagonal, apply_ite (Finset.map _)]

end OrderedSub

end HasAntidiagonal

namespace HasMulAntidiagonal

/-- The disjoint union of mulAntidiagonals `Σ (n : A), mulAntidiagonal n` is equivalent to the
  product `A × A`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/
@[to_additive (attr := simps) sigmaAntidiagonalEquivProd
/-- The disjoint union of antidiagonals `Σ (n : A), antidiagonal n` is equivalent to the
  product `A × A`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/]
def sigmaMulAntidiagonalEquivProd [Monoid A] [HasMulAntidiagonal A] :
    (Σ n : A, mulAntidiagonal n) ≃ A × A where
  toFun x := x.2
  invFun x := ⟨x.1 * x.2, x, mem_mulAntidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [mem_mulAntidiagonal] at h
    exact Sigma.subtype_ext h rfl

section

variable {A : Type*}
  [CommMonoid A] [PartialOrder A] [CanonicallyOrderedMul A]
  [LocallyFiniteOrderBot A] [DecidableEq A]

/-- In a canonically ordered multiplicative monoid, the mulAntidiagonal can be constructed by
filtering.

Note that this is not an instance, as for sometimes a more efficient algorithm is available. -/
@[to_additive
/-- In a canonically ordered additive monoid, the antidiagonal can be construct by filtering.

Note that this is not an instance, as for some times a more efficient algorithm is available. -/]
abbrev mulAntidiagonalOfLocallyFinite : HasMulAntidiagonal A where
  mulAntidiagonal n := {uv ∈ Iic n ×ˢ Iic n | uv.fst * uv.snd = n}
  mem_mulAntidiagonal {n} {a} := by
    simp only [mem_filter, and_iff_right_iff_imp]
    intro h
    simp [← h]

end

section Multiplicative

open Multiplicative

variable {A : Type*} [AddMonoid A] [HasAntidiagonal A]

instance : HasMulAntidiagonal (Multiplicative A) where
  mulAntidiagonal a :=
    (antidiagonal (toAdd a)).map ⟨fun p ↦ (ofAdd p.1 , ofAdd p.2), fun _ _ h ↦ by aesop⟩
  mem_mulAntidiagonal {a p} := by aesop

lemma mem_mulAntidiagonal_ofAdd_iff_toAdd_mem_antidiagonal {a : A}
    {p : Multiplicative A × Multiplicative A} :
    p ∈ mulAntidiagonal (ofAdd a) ↔ (toAdd p.1, toAdd p.2) ∈ antidiagonal a := by
  simp only [mem_mulAntidiagonal, mem_antidiagonal]
  rw [Multiplicative.ext_iff, toAdd_mul, toAdd_ofAdd]

end Multiplicative

end HasMulAntidiagonal

end Finset
