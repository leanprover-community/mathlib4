/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Bhavik Mehta, Eric Wieser,
  Fengyang Wang
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Interval.Finset.Defs

/-! # Antidiagonal with values in general types

We define type classes for finite antidiagonals:
* `Finset.HasAntidiagonal A`: additive version with `antidiagonal : A → Finset (A × A)`
  where `antidiagonal n` is the finset of all pairs adding to `n`.
* `Finset.HasMulAntidiagonal M`: multiplicative version with `mulAntidiagonal : M → Finset (M × M)`
  where `mulAntidiagonal n` is the finset of all pairs multiplying to `n`.

The multiplicative version is linked to the additive version via `@[to_additive]`.

## Additive Antidiagonal

When `A` is a canonically ordered additive monoid with locally finite order,
`HasAntidiagonal` can be instantiated with `Finset.antidiagonalOfLocallyFinite`.
This applies in particular when `A` is `ℕ`, more generally `σ →₀ ℕ`,
or even `ι →₀ A` under the additional assumption `OrderedSub A`
that makes it a canonically ordered additive monoid.
(In fact, we would just need an `AddMonoid` with a compatible order,
finite `Iic`, such that if `a + b = n`, then `a, b ≤ n`,
and any finiteness condition would be OK.)

For computational reasons it is better to manually provide instances for `ℕ`
and `σ →₀ ℕ`, to avoid quadratic runtime performance.
These instances are provided as `Finset.Nat.instHasAntidiagonal` and `Finsupp.instHasAntidiagonal`.
This is why `Finset.antidiagonalOfLocallyFinite` is an `abbrev` and not an `instance`.

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

* Define a `HasMulAntidiagonal` instance for `PNat` using `Nat.divisorsAntidiagonal`.
  This will recover the set of divisor pairs of a strictly positive integer.
-/

@[expose] public section

open Function

namespace Finset

/-- The class of additive monoids with an antidiagonal -/
class HasAntidiagonal (A : Type*) [AddMonoid A] where
  /-- The antidiagonal of an element `n` is the finset of pairs `(i, j)` such that `i + j = n`. -/
  antidiagonal : A → Finset (A × A)
  /-- A pair belongs to `antidiagonal n` iff the sum of its components is equal to `n`. -/
  mem_antidiagonal {n} {a} : a ∈ antidiagonal n ↔ a.fst + a.snd = n

export HasAntidiagonal (antidiagonal mem_antidiagonal)

attribute [simp] mem_antidiagonal

variable {A : Type*}

/-- All `HasAntidiagonal` instances are equal -/
instance [AddMonoid A] : Subsingleton (HasAntidiagonal A) where
  allEq := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    congr with n xy
    rw [ha, hb]

-- The goal of this lemma is to allow to rewrite antidiagonal
-- when the decidability instances obsucate Lean
lemma hasAntidiagonal_congr (A : Type*) [AddMonoid A]
    [H1 : HasAntidiagonal A] [H2 : HasAntidiagonal A] :
    H1.antidiagonal = H2.antidiagonal := by congr!; subsingleton

theorem swap_mem_antidiagonal [AddCommMonoid A] [HasAntidiagonal A] {n : A} {xy : A × A} :
    xy.swap ∈ antidiagonal n ↔ xy ∈ antidiagonal n := by
  simp [add_comm]

@[simp] theorem map_prodComm_antidiagonal [AddCommMonoid A] [HasAntidiagonal A] {n : A} :
    (antidiagonal n).map (Equiv.prodComm A A) = antidiagonal n :=
  Finset.ext fun ⟨a, b⟩ => by simp [add_comm]

/-- See also `Finset.map_prodComm_antidiagonal`. -/
@[simp] theorem map_swap_antidiagonal [AddCommMonoid A] [HasAntidiagonal A] {n : A} :
    (antidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = antidiagonal n :=
  map_prodComm_antidiagonal

/-! ### Namespaced versions for use with `@[to_additive]` -/

namespace Antidiag

theorem swap_mem [AddCommMonoid A] [HasAntidiagonal A]
    {n : A} {xy : A × A} : xy.swap ∈ antidiagonal n ↔ xy ∈ antidiagonal n :=
  swap_mem_antidiagonal

theorem map_prodComm [AddCommMonoid A] [HasAntidiagonal A] {n : A} :
    (antidiagonal n).map (Equiv.prodComm A A) = antidiagonal n :=
  map_prodComm_antidiagonal

@[simp]
theorem map_swap [AddCommMonoid A] [HasAntidiagonal A] {n : A} :
    (antidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = antidiagonal n :=
  map_swap_antidiagonal

end Antidiag

section AddCancelMonoid
variable [AddCancelMonoid A] [HasAntidiagonal A] {p q : A × A} {n : A}

/-- A point in the antidiagonal is determined by its first coordinate.

See also `Finset.antidiagonal_congr'`. -/
theorem antidiagonal_congr (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
    p = q ↔ p.1 = q.1 := by
  refine ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((add_right_inj q.fst).mp ?_)⟩
  rw [mem_antidiagonal] at hp hq
  rw [hq, ← h, hp]

/-- A point in the antidiagonal is determined by its first co-ordinate (subtype version of
`Finset.antidiagonal_congr`). This lemma is used by the `ext` tactic. -/
@[ext] theorem antidiagonal_subtype_ext {p q : antidiagonal n} (h : p.val.1 = q.val.1) : p = q :=
  Subtype.ext ((antidiagonal_congr p.prop q.prop).mpr h)

end AddCancelMonoid

section AddCancelCommMonoid
variable [AddCancelCommMonoid A] [HasAntidiagonal A] {p q : A × A} {n : A}

/-- A point in the antidiagonal is determined by its second coordinate.

See also `Finset.antidiagonal_congr`. -/
lemma antidiagonal_congr' (hp : p ∈ antidiagonal n) (hq : q ∈ antidiagonal n) :
    p = q ↔ p.2 = q.2 := by
  rw [← Prod.swap_inj]
  exact antidiagonal_congr (swap_mem_antidiagonal.2 hp) (swap_mem_antidiagonal.2 hq)

end AddCancelCommMonoid

section CanonicallyOrderedAdd
variable [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A] [HasAntidiagonal A]

@[simp]
theorem antidiagonal_zero : antidiagonal (0 : A) = {(0, 0)} := by
  ext ⟨x, y⟩
  simp

theorem antidiagonal.fst_le {n : A} {kl : A × A} (hlk : kl ∈ antidiagonal n) : kl.1 ≤ n := by
  rw [le_iff_exists_add]
  use kl.2
  rwa [mem_antidiagonal, eq_comm] at hlk

theorem antidiagonal.snd_le {n : A} {kl : A × A} (hlk : kl ∈ antidiagonal n) : kl.2 ≤ n := by
  rw [le_iff_exists_add]
  use kl.1
  rwa [mem_antidiagonal, eq_comm, add_comm] at hlk

end CanonicallyOrderedAdd

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
  have : (fun x : A × A ↦ (x.snd = m)) ∘ Prod.swap = fun x : A × A ↦ x.fst = m := by
    ext; simp
  rw [← map_swap_antidiagonal, filter_map]
  simp [this, filter_fst_eq_antidiagonal, apply_ite (Finset.map _)]

end OrderedSub

/-- The disjoint union of antidiagonals `Σ (n : A), antidiagonal n` is equivalent to the product
    `A × A`. This is such an equivalence, obtained by mapping `(n, (k, l))` to `(k, l)`. -/
@[simps]
def sigmaAntidiagonalEquivProd [AddMonoid A] [HasAntidiagonal A] :
    (Σ n : A, antidiagonal n) ≃ A × A where
  toFun x := x.2
  invFun x := ⟨x.1 + x.2, x, mem_antidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [mem_antidiagonal] at h
    exact Sigma.subtype_ext h rfl

variable {A : Type*}
  [AddCommMonoid A] [PartialOrder A] [CanonicallyOrderedAdd A]
  [LocallyFiniteOrderBot A] [DecidableEq A]

/-- In a canonically ordered additive monoid, the antidiagonal can be construct by filtering.

Note that this is not an instance, as for some times a more efficient algorithm is available. -/
abbrev antidiagonalOfLocallyFinite : HasAntidiagonal A where
  antidiagonal n := {uv ∈ Iic n ×ˢ Iic n | uv.fst + uv.snd = n}
  mem_antidiagonal {n} {a} := by
    simp only [mem_filter, and_iff_right_iff_imp]
    intro h
    simp [← h]

/-! ## Multiplicative Antidiagonal -/

/-- The class of multiplicative monoids with a multiplicative antidiagonal -/
@[to_additive existing HasAntidiagonal]
class HasMulAntidiagonal (M : Type*) [Monoid M] where
  /-- The multiplicative antidiagonal of `n` is the finset of pairs `(i, j)` such that
  `i * j = n`. -/
  mulAntidiagonal : M → Finset (M × M)
  /-- A pair belongs to `mulAntidiagonal n` iff the product of its components equals `n`. -/
  mem_mulAntidiagonal {n} {a} : a ∈ mulAntidiagonal n ↔ a.fst * a.snd = n

export HasMulAntidiagonal (mulAntidiagonal mem_mulAntidiagonal)

attribute [simp] mem_mulAntidiagonal

variable {M : Type*}

/-- All `HasMulAntidiagonal` instances are equal -/
instance [Monoid M] : Subsingleton (HasMulAntidiagonal M) where
  allEq := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    congr with n xy
    rw [ha, hb]

@[to_additive existing hasAntidiagonal_congr]
lemma hasMulAntidiagonal_congr (M : Type*) [Monoid M]
    [H1 : HasMulAntidiagonal M] [H2 : HasMulAntidiagonal M] :
    H1.mulAntidiagonal = H2.mulAntidiagonal := by congr!; subsingleton

namespace MulAntidiag

@[to_additive existing Antidiag.swap_mem]
theorem swap_mem [CommMonoid M] [HasMulAntidiagonal M]
    {n : M} {xy : M × M} : xy.swap ∈ mulAntidiagonal n ↔ xy ∈ mulAntidiagonal n := by
  simp [mul_comm]

@[to_additive existing Antidiag.map_prodComm]
theorem map_prodComm [CommMonoid M] [HasMulAntidiagonal M] {n : M} :
    (mulAntidiagonal n).map (Equiv.prodComm M M) = mulAntidiagonal n :=
  Finset.ext fun ⟨a, b⟩ => by simp [mul_comm]

/-- See also `Finset.MulAntidiag.map_prodComm`. -/
@[to_additive existing Antidiag.map_swap]
theorem map_swap [CommMonoid M] [HasMulAntidiagonal M] {n : M} :
    (mulAntidiagonal n).map ⟨Prod.swap, Prod.swap_injective⟩ = mulAntidiagonal n :=
  map_prodComm

end MulAntidiag

section CancelMonoid
variable [CancelMonoid M] [HasMulAntidiagonal M] {p q : M × M} {n : M}

/-- A point in the multiplicative antidiagonal is determined by its first coordinate. -/
@[to_additive existing antidiagonal_congr]
theorem mulAntidiagonal_congr (hp : p ∈ mulAntidiagonal n) (hq : q ∈ mulAntidiagonal n) :
    p = q ↔ p.1 = q.1 := by
  refine ⟨congr_arg Prod.fst, fun h ↦ Prod.ext h ((mul_right_inj q.fst).mp ?_)⟩
  rw [mem_mulAntidiagonal] at hp hq
  rw [hq, ← h, hp]

/-- A point in the multiplicative antidiagonal is determined by its first coordinate
(subtype version). -/
@[to_additive existing antidiagonal_subtype_ext]
theorem mulAntidiagonal_subtype_ext {p q : mulAntidiagonal n} (h : p.val.1 = q.val.1) : p = q :=
  Subtype.ext ((mulAntidiagonal_congr p.prop q.prop).mpr h)

end CancelMonoid

section CancelCommMonoid
variable [CancelCommMonoid M] [HasMulAntidiagonal M] {p q : M × M} {n : M}

/-- A point in the multiplicative antidiagonal is determined by its second coordinate. -/
@[to_additive existing antidiagonal_congr']
lemma mulAntidiagonal_congr' (hp : p ∈ mulAntidiagonal n) (hq : q ∈ mulAntidiagonal n) :
    p = q ↔ p.2 = q.2 := by
  rw [← Prod.swap_inj]
  exact mulAntidiagonal_congr (MulAntidiag.swap_mem.2 hp) (MulAntidiag.swap_mem.2 hq)

end CancelCommMonoid

/-- The disjoint union of multiplicative antidiagonals `Σ (n : M), mulAntidiagonal n` is equivalent
to the product `M × M`. -/
@[to_additive existing sigmaAntidiagonalEquivProd]
def sigmaMulAntidiagonalEquivProd [Monoid M] [HasMulAntidiagonal M] :
    (Σ n : M, mulAntidiagonal n) ≃ M × M where
  toFun x := x.2
  invFun x := ⟨x.1 * x.2, x, mem_mulAntidiagonal.mpr rfl⟩
  left_inv := by
    rintro ⟨n, ⟨k, l⟩, h⟩
    rw [mem_mulAntidiagonal] at h
    exact Sigma.subtype_ext h rfl

end Finset
