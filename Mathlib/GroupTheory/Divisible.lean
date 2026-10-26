/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.GroupTheory.QuotientGroup.Defs

import Mathlib.Data.Rat.Cast.CharZero

/-!
# Divisible and rootable groups

In this file, we define a divisible additive monoid and a rootable monoid with some basic
properties.

## Main definition

* `IsDivisibleBy A α`: An additive monoid `A` is said to be divisible by `α` iff for all `n ≠ 0 ∈ α`
  and `y ∈ A`, there is an `x ∈ A` such that `n • x = y`.
* `IsRootableBy A α`: A monoid `A` is said to be rootable by `α` iff for all `n ≠ 0 ∈ α` and
  `y ∈ A`, there is an `x ∈ A` such that `x^n = y`.

## Main results

For additive monoids and groups:

* `AddGroup.isDivisibleBy_int_iff_isDivisibleBy_nat`: for additive groups, `ℤ`-divisibility is
  equivalent to `ℕ`-divisibility.
* `QuotientAddGroup.isDivisibleBy`: quotient group of divisible group is divisible.

and their multiplicative counterparts:

* `Group.isRootableBy_int_iff_isRootableBy_nat`: for additive groups, `ℤ`-rootability is equivalent
  to `ℕ`-rootability.
* `QuotientGroup.isRootableBy`: quotient group of rootable group is rootable.

TODO: Show that divisibility implies injectivity in the category of `AddCommGroup`.

## Implementation notes

We previously employed a constructive approach, where we required an explicit divisor or root for
any given element. However, in many circumstances (most notably quotient groups, e.g. ℝ ⧸ ℚ),
there's no clear canonical candidate. As such, `IsDivisibleBy` and `IsRootableBy` are now
`Prop`-valued typeclasses.
-/

@[expose] public section

open scoped Pointwise

section AddMonoid

variable (A α : Type*) [AddMonoid A] [SMul α A] [Zero α]

/--
An `AddMonoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
class IsDivisibleBy [AddMonoid A] : Prop where
  exists_div : ∀ a : A, ∀ {n : α}, n ≠ 0 → ∃ m : A, n • m = a

/--
An `AddMonoid A` is `α`-divisible iff `n • x = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `div : A → α → A` function such that
* `div a 0 = 0` for all `a ∈ A`
* `n • div a n = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[deprecated IsDivisibleBy +typeChanged (since := "2026-10-26")]
class DivisibleBy where
  /-- The division function -/
  div : A → α → A
  div_zero : ∀ a, div a 0 = 0
  div_cancel : ∀ {n : α} (a : A), n ≠ 0 → n • div a n = a

attribute [deprecated IsDivisibleBy +typeChanged (since := "2026-10-26")]
  DivisibleBy.div DivisibleBy.div_zero DivisibleBy.div_cancel

end AddMonoid

section Monoid

variable (A α : Type*) [Monoid A] [Pow A α] [Zero α]

/--
A `Monoid A` is `α`-rootable iff `x ^ n = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive existing]
class IsRootableBy [Monoid A] : Prop where
  exists_root : ∀ a : A, ∀ {n : α}, n ≠ 0 → ∃ m : A, m ^ n = a

/-- A `Monoid A` is `α`-rootable iff `xⁿ = a` has a solution for all `n ≠ 0 ∈ α` and `a ∈ A`.
Here we adopt a constructive approach where we ask an explicit `root : A → α → A` function such that
* `root a 0 = 1` for all `a ∈ A`
* `(root a n)ⁿ = a` for all `n ≠ 0 ∈ α` and `a ∈ A`.
-/
@[to_additive existing, deprecated IsRootableBy +typeChanged (since := "2026-10-26")]
class RootableBy where
  /-- The root function -/
  root : A → α → A
  root_zero : ∀ a, root a 0 = 1
  root_cancel : ∀ {n : α} (a : A), n ≠ 0 → root a n ^ n = a

attribute [deprecated IsRootableBy +typeChanged (since := "2026-10-26")]
  RootableBy.root RootableBy.root_zero RootableBy.root_cancel

@[to_additive IsDivisibleBy.surjective_smul]
theorem IsRootableBy.surjective_pow [IsRootableBy A α] {n : α} (hn : n ≠ 0) :
    Function.Surjective fun a : A => a ^ n := fun x =>
  IsRootableBy.exists_root x hn

set_option linter.deprecated false in
@[to_additive (attr := deprecated IsRootableBy.surjective_pow +typeChanged (since := "2026-10-26"))
DivisibleBy.surjective_smul]
theorem RootableBy.surjective_pow [RootableBy A α] {n : α} (hn : n ≠ 0) :
    Function.Surjective fun a : A => a ^ n := fun x =>
  ⟨RootableBy.root x n, RootableBy.root_cancel _ hn⟩

@[to_additive isDivisibleBy_iff_smul_surjective]
theorem isRootableBy_iff_pow_surjective :
    IsRootableBy A α ↔ ∀ {n : α}, n ≠ 0 → Function.Surjective (fun a => a ^ n : A → A) :=
  ⟨fun h _ hn a ↦ h.exists_root a hn, fun H ↦ ⟨fun a _ hn ↦ H hn a⟩⟩

set_option linter.deprecated false in
/--
A `Monoid A` is `α`-rootable iff the `pow _ n` function is surjective, i.e. the constructive version
implies the textbook approach.
-/
@[to_additive (attr := instance_reducible,
deprecated isRootableBy_iff_pow_surjective +typeChanged (since := "2026-10-26"))
divisibleByOfSMulRightSurj
  /-- An `AddMonoid A` is `α`-divisible iff `n • _` is a surjective function, i.e. the
  constructive version implies the textbook approach. -/]
noncomputable def rootableByOfPowLeftSurj
    (H : ∀ {n : α}, n ≠ 0 → Function.Surjective (fun a => a ^ n : A → A)) : RootableBy A α where
  root a n := @dite _ (n = 0) (Classical.dec _) (fun _ => (1 : A)) fun hn => (H hn a).choose
  root_zero _ := by exact dite_eq_left rfl
  root_cancel a hn := by
    dsimp only
    rw [dite_eq_right hn]
    exact (H hn a).choose_spec

section Pi

variable {ι β : Type*} (B : ι → Type*) [∀ i : ι, Pow (B i) β]
variable [Zero β] [∀ i : ι, Monoid (B i)] [∀ i, IsRootableBy (B i) β]

@[to_additive]
instance Pi.isRootableBy : IsRootableBy (∀ i, B i) β where
  exists_root a n hn := by
    choose r hr using fun i ↦ IsRootableBy.exists_root (a i) hn
    exact ⟨r, funext hr⟩

end Pi

section Pi

variable {ι β : Type*} (B : ι → Type*) [∀ i : ι, Pow (B i) β]
variable [Zero β] [∀ i : ι, Monoid (B i)]

set_option linter.deprecated false in
@[to_additive (attr := deprecated Pi.isRootableBy +typeChanged (since := "2026-10-26"))]
instance Pi.rootableBy [∀ i, RootableBy (B i) β] : RootableBy (∀ i, B i) β where
  root x n i := RootableBy.root (x i) n
  root_zero _x := funext fun _i => RootableBy.root_zero _
  root_cancel _x hn := funext fun _i => RootableBy.root_cancel _ hn

end Pi

section Prod

variable {β B B' : Type*} [Pow B β] [Pow B' β]
variable [Zero β] [Monoid B] [Monoid B'] [IsRootableBy B β] [IsRootableBy B' β]

@[to_additive]
instance Prod.isRootableBy : IsRootableBy (B × B') β where
  exists_root x n hn := by
    obtain ⟨a, ha⟩ := IsRootableBy.exists_root x.1 hn
    obtain ⟨b, hb⟩ := IsRootableBy.exists_root x.2 hn
    exact ⟨⟨a, b⟩, Prod.ext ha hb⟩

end Prod

section Prod

variable {β B B' : Type*} [Pow B β] [Pow B' β]
variable [Zero β] [Monoid B] [Monoid B']

set_option linter.deprecated false in
@[to_additive (attr := deprecated Prod.isRootableBy +typeChanged (since := "2026-10-26"))]
instance Prod.rootableBy [RootableBy B β] [RootableBy B' β] : RootableBy (B × B') β where
  root p n := (RootableBy.root p.1 n, RootableBy.root p.2 n)
  root_zero _p := Prod.ext (RootableBy.root_zero _) (RootableBy.root_zero _)
  root_cancel _p hn := Prod.ext (RootableBy.root_cancel _ hn) (RootableBy.root_cancel _ hn)

end Prod

section ULift

@[to_additive]
instance ULift.isRootableBy [IsRootableBy A α] : IsRootableBy (ULift A) α where
  exists_root x n hn := by
    obtain ⟨r, hr⟩ := IsRootableBy.exists_root x.down hn
    exact ⟨ULift.up r, ULift.ext hr⟩

end ULift

section ULift

set_option linter.deprecated false in
@[to_additive]
instance ULift.instRootableBy [RootableBy A α] : RootableBy (ULift A) α where
  root x a := ULift.up <| RootableBy.root x.down a
  root_zero x := ULift.ext <| RootableBy.root_zero x.down
  root_cancel _ h := ULift.ext <| RootableBy.root_cancel _ h

end ULift

end Monoid

namespace Group

variable {A : Type*} [Group A]

/-- A group is `ℤ`-rootable iff it is `ℕ`-rootable. -/
@[to_additive
/-- A group is `ℤ`-divisible iff it is `ℕ`-divisible. -/]
theorem isRootableBy_int_iff_isRootableBy_nat : IsRootableBy A ℤ ↔ IsRootableBy A ℕ := by
  constructor <;> refine fun h ↦ ⟨fun a n hn ↦ ?_⟩
  · simpa using h.exists_root a (n := n) (mod_cast hn)
  · obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
    · simpa using h.exists_root a (mod_cast hn)
    · simpa [inv_eq_iff_eq_inv] using h.exists_root a⁻¹ (by simpa using hn)

@[to_additive]
instance [IsRootableBy A ℕ] : IsRootableBy A ℤ := isRootableBy_int_iff_isRootableBy_nat.2 ‹_›

set_option linter.deprecated false in
open Int in
/-- A group is `ℤ`-rootable if it is `ℕ`-rootable.
-/
@[to_additive (attr := instance_reducible,
deprecated isRootableBy_int_iff_isRootableBy_nat +typeChanged (since := "2026-10-26"))
  /-- An additive group is `ℤ`-divisible if it is `ℕ`-divisible. -/]
def rootableByIntOfRootableByNat [RootableBy A ℕ] : RootableBy A ℤ where
  root a z :=
    match z with
    | (n : ℕ) => RootableBy.root a n
    | -[n+1] => (RootableBy.root a (n + 1))⁻¹
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    cases n
    · rw [Int.ofNat_eq_natCast, Nat.cast_ne_zero] at hn
      simp [RootableBy.root_cancel _ hn]
    · simp [RootableBy.root_cancel _ (Nat.add_one_ne_zero _)]

set_option linter.deprecated false in
/-- A group is `ℕ`-rootable if it is `ℤ`-rootable
-/
@[to_additive (attr := instance_reducible,
deprecated isRootableBy_int_iff_isRootableBy_nat +typeChanged (since := "2026-10-26"))
  /-- An additive group is `ℕ`-divisible if it `ℤ`-divisible. -/]
def rootableByNatOfRootableByInt [RootableBy A ℤ] : RootableBy A ℕ where
  root a n := RootableBy.root a (n : ℤ)
  root_zero a := RootableBy.root_zero a
  root_cancel {n} a hn := by
    have := RootableBy.root_cancel a (show (n : ℤ) ≠ 0 from mod_cast hn)
    simpa

end Group

namespace AddCommGroup

variable (A : Type*) [AddCommGroup A]

theorem nsmul_top_eq_top_of_isDivisibleBy [IsDivisibleBy A ℕ] {n : ℕ} (hn : n ≠ 0) :
    n • (⊤ : AddSubgroup A) = ⊤ :=
  AddSubgroup.map_top_of_surjective _ (IsDivisibleBy.exists_div · hn)

theorem smul_top_eq_top_of_isDivisibleBy [IsDivisibleBy A ℕ] {n : ℤ} (hn : n ≠ 0) :
    n • (⊤ : AddSubgroup A) = ⊤ :=
  AddSubgroup.map_top_of_surjective _ (IsDivisibleBy.exists_div · hn)

@[deprecated smul_top_eq_top_of_isDivisibleBy +typeChanged (since := "2026-10-26")]
theorem smul_top_eq_top_of_divisibleBy_int [DivisibleBy A ℤ] {n : ℤ} (hn : n ≠ 0) :
    n • (⊤ : AddSubgroup A) = ⊤ :=
  AddSubgroup.map_top_of_surjective _ fun a => ⟨DivisibleBy.div a n, DivisibleBy.div_cancel _ hn⟩

/-- If for all `n ≠ 0 ∈ ℤ`, `n • A = A`, then `A` is divisible.
-/
@[instance_reducible,
deprecated smul_top_eq_top_of_isDivisibleBy +typeChanged (since := "2026-10-26")]
noncomputable def divisibleByIntOfSMulTopEqTop
    (H : ∀ {n : ℤ} (_hn : n ≠ 0), n • (⊤ : AddSubgroup A) = ⊤) : DivisibleBy A ℤ where
  div a n :=
    if hn : n = 0 then 0 else (show a ∈ n • (⊤ : AddSubgroup A) by rw [H hn]; trivial).choose
  div_zero _ := dite_eq_left rfl
  div_cancel a hn := by
    simp_rw [dite_eq_right hn]
    generalize_proofs h1
    exact h1.choose_spec.2

end AddCommGroup

instance (priority := 100) isDivisibleBy_nat_of_charZero {𝕜} [DivisionRing 𝕜] [CharZero 𝕜] :
    IsDivisibleBy 𝕜 ℕ where
  exists_div a n hn := by
    use a / n
    rw [nsmul_eq_mul', div_mul_cancel₀ _ (mod_cast hn)]

instance (priority := 100) isDivisibleBy_int_of_charZero {𝕜} [DivisionRing 𝕜] [CharZero 𝕜] :
    IsDivisibleBy 𝕜 ℤ where
  exists_div a n hn := by
    use a / n
    rw [zsmul_eq_mul', div_mul_cancel₀ _ (mod_cast hn)]

instance (priority := 100) isDivisibleBy_rat_of_charZero {𝕜} [DivisionRing 𝕜] [CharZero 𝕜] :
    IsDivisibleBy 𝕜 ℚ where
  exists_div a n hn := by
    use a / n
    change DivisionRing.qsmul .. = _
    rw [DivisionRing.qsmul_def, (Rat.cast_commute _ _).eq, div_mul_cancel₀ _ (mod_cast hn)]

section Hom

variable {A B α : Type*}
variable [Zero α] [Monoid A] [Monoid B] [Pow A α] [Pow B α]
variable (f : A → B)

/--
If `f : A → B` is a surjective homomorphism and `A` is `α`-rootable, then `B` is also `α`-rootable.
-/
@[to_additive
/-- If `f : A → B` is a surjective homomorphism and `A` is `α`-divisible, then `B` is also
`α`-divisible. -/]
theorem Function.Surjective.isRootableBy [IsRootableBy A α] (hf : Function.Surjective f)
    (hpow : ∀ (a : A) (n : α), f (a ^ n) = f a ^ n) : IsRootableBy B α where
  exists_root b n hn := by
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨r, hr⟩ := IsRootableBy.exists_root a hn
    use f r
    rw [← hpow, hr]

set_option linter.deprecated false in
/--
If `f : A → B` is a surjective homomorphism and `A` is `α`-rootable, then `B` is also `α`-rootable.
-/
@[to_additive (attr := instance_reducible,
deprecated Function.Surjective.isRootableBy +typeChanged (since := "2026-10-26"))
      /-- If `f : A → B` is a surjective homomorphism and `A` is `α`-divisible, then `B` is also
      `α`-divisible. -/]
noncomputable def Function.Surjective.rootableBy [RootableBy A α] (hf : Function.Surjective f)
    (hpow : ∀ (a : A) (n : α), f (a ^ n) = f a ^ n) : RootableBy B α :=
  rootableByOfPowLeftSurj _ _ fun {n} hn x =>
    let ⟨y, hy⟩ := hf x
    ⟨f <| RootableBy.root y n,
      (by rw [← hpow (RootableBy.root y n) n, RootableBy.root_cancel _ hn, hy] : _ ^ n = x)⟩

end Hom

section Quotient

variable {A : Type*} [CommGroup A] (B : Subgroup A)

/-- Any quotient group of a rootable group is rootable. -/
@[to_additive /-- Any quotient group of a divisible group is divisible -/]
noncomputable instance QuotientGroup.isRootableBy [IsRootableBy A ℕ] : IsRootableBy (A ⧸ B) ℕ :=
  QuotientGroup.mk_surjective.isRootableBy _ fun _ _ => rfl

set_option linter.deprecated false in
/-- Any quotient group of a rootable group is rootable. -/
@[to_additive (attr := deprecated QuotientGroup.isRootableBy +typeChanged (since := "2026-10-26"))
/-- Any quotient group of a divisible group is divisible -/]
noncomputable instance QuotientGroup.rootableBy [RootableBy A ℕ] : RootableBy (A ⧸ B) ℕ :=
  QuotientGroup.mk_surjective.rootableBy _ fun _ _ => rfl

end Quotient
