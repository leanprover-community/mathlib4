/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.TypeTags

/-!
# Pretransitive group actions

This file defines a typeclass for pretransitive group actions.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

public section

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M G α β : Type*}

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `MonoidAction.IsPretransitive` and
`AddMonoidAction.IsPretransitive` and provide `MonoidAction.exists_smul_eq`/`AddMonoidAction.exists_vadd_eq`,
`MonoidAction.surjective_smul`/`AddMonoidAction.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*Action.IsTransitive`; users should assume
`[MonoidAction.IsPretransitive M α] [Nonempty α]` instead.
-/

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g +ᵥ x = y`.
  A transitive action should furthermore have `α` nonempty. -/
class AddMonoidAction.IsPretransitive (M α : Type*) [VAdd M α] : Prop where
  /-- There is `g` such that `g +ᵥ x = y`. -/
  exists_vadd_eq : ∀ x y : α, ∃ g : M, g +ᵥ x = y

/-- Deprecated alias for `AddMonoidAction.IsPretransitive`. -/
@[deprecated AddMonoidAction.IsPretransitive (since := "2026-09-02")]
abbrev AddAction.IsPretransitive := @AddMonoidAction.IsPretransitive
@[deprecated (since := "2026-09-02")]
alias AddAction.IsPretransitive.exists_vadd_eq := AddMonoidAction.IsPretransitive.exists_vadd_eq

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive (attr := mk_iff)]
class MonoidAction.IsPretransitive (M α : Type*) [SMul M α] : Prop where
  /-- There is `g` such that `g • x = y`. -/
  exists_smul_eq : ∀ x y : α, ∃ g : M, g • x = y

/-- Deprecated alias for `MonoidAction.IsPretransitive`. -/
@[deprecated MonoidAction.IsPretransitive (since := "2026-09-02")]
abbrev MulAction.IsPretransitive := @MonoidAction.IsPretransitive
@[deprecated (since := "2026-09-02")]
alias MulAction.IsPretransitive.exists_smul_eq := MonoidAction.IsPretransitive.exists_smul_eq
@[deprecated (since := "2026-09-02")]
alias MulAction.isPretransitive_iff := MonoidAction.isPretransitive_iff
@[deprecated (since := "2026-09-02")]
alias AddAction.isPretransitive_iff := AddMonoidAction.isPretransitive_iff

@[to_additive]
instance MonoidAction.instIsPretransitiveOfSubsingleton
    {M α : Type*} [Monoid M] [MonoidAction M α] [Subsingleton α] :
    MonoidAction.IsPretransitive M α where
  exists_smul_eq x y := ⟨1, by
    simp only [one_smul, Subsingleton.elim x y] ⟩

namespace MonoidAction
variable (M) [SMul M α] [IsPretransitive M α]

@[to_additive]
lemma exists_smul_eq (x y : α) : ∃ m : M, m • x = y := IsPretransitive.exists_smul_eq x y

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.exists_smul_eq := exists_smul_eq
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.exists_vadd_eq := _root_.AddMonoidAction.exists_vadd_eq

@[to_additive]
lemma surjective_smul (x : α) : Surjective fun c : M ↦ c • x := exists_smul_eq M x

@[deprecated (since := "2026-09-02")] alias _root_.MulAction.surjective_smul := surjective_smul
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.surjective_vadd := _root_.AddMonoidAction.surjective_vadd

/-- The left regular action of a group on itself is transitive. -/
@[to_additive /-- The regular action of a group on itself is transitive. -/]
instance Regular.isPretransitive [Group G] : IsPretransitive G G :=
  ⟨fun x y ↦ ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.Regular.isPretransitive := Regular.isPretransitive
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.Regular.isPretransitive := _root_.AddMonoidAction.Regular.isPretransitive

/-- The right regular action of a group on itself is transitive. -/
@[to_additive /-- The right regular action of an additive group on itself is transitive. -/]
instance Regular.isPretransitive_mulOpposite [Group G] : IsPretransitive Gᵐᵒᵖ G :=
  ⟨fun x y ↦ ⟨.op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.Regular.isPretransitive_mulOpposite := Regular.isPretransitive_mulOpposite
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.Regular.isPretransitive_addOpposite :=
  _root_.AddMonoidAction.Regular.isPretransitive_addOpposite

/-- If `G` is a group acting multiplicatively on a set, then the action is transitive if there is
a single element whose orbit is everything. -/
@[to_additive /-- If `G` is a group acting additively on a set, then the action is transitive if
there is a single element whose orbit is everything. -/]
lemma IsPretransitive.of_orbit {X : Type*} [Group G] [MonoidAction G X] {x₀ : X}
    (ha : ∀ x, ∃ g : G, g • x₀ = x) :
    IsPretransitive G X := by
  constructor
  intro x y
  rcases ha x with ⟨g, rfl⟩
  rcases ha y with ⟨h, rfl⟩
  exact ⟨h * g⁻¹, by simp [mul_smul]⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsPretransitive.of_orbit := IsPretransitive.of_orbit
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsPretransitive.of_orbit := _root_.AddMonoidAction.IsPretransitive.of_orbit

end MonoidAction

namespace MonoidAction

@[to_additive]
lemma IsPretransitive.of_smul_eq {M N α : Type*} [SMul M α] [SMul N α] [IsPretransitive M α]
    (f : M → N) (hf : ∀ {c : M} {x : α}, f c • x = c • x) : IsPretransitive N α where
  exists_smul_eq x y := (exists_smul_eq x y).elim fun m h ↦ ⟨f m, hf.trans h⟩

@[deprecated (since := "2026-09-02")]
alias _root_.MulAction.IsPretransitive.of_smul_eq := IsPretransitive.of_smul_eq
@[deprecated (since := "2026-09-02")]
alias _root_.AddAction.IsPretransitive.of_vadd_eq :=
  _root_.AddMonoidAction.IsPretransitive.of_vadd_eq

end MonoidAction

section CompatibleScalar

@[to_additive]
lemma MonoidAction.IsPretransitive.of_isScalarTower (M : Type*) {N α : Type*} [Monoid N] [SMul M N]
    [MonoidAction N α] [SMul M α] [IsScalarTower M N α] [IsPretransitive M α] : IsPretransitive N α :=
  of_smul_eq (fun x : M ↦ x • 1) (smul_one_smul N _ _)

@[deprecated (since := "2026-09-02")]
alias MulAction.IsPretransitive.of_isScalarTower := MonoidAction.IsPretransitive.of_isScalarTower
@[deprecated (since := "2026-09-02")]
alias AddAction.IsPretransitive.of_vaddAssocClass :=
  AddMonoidAction.IsPretransitive.of_vaddAssocClass

end CompatibleScalar

/-! ### `Additive`, `Multiplicative` -/

section

open Additive Multiplicative

instance Additive.addMonoidAction_isPretransitive [Monoid α] [MonoidAction α β]
    [MonoidAction.IsPretransitive α β] : AddMonoidAction.IsPretransitive (Additive α) β :=
  ⟨@MonoidAction.exists_smul_eq α _ _ _⟩

@[deprecated (since := "2026-09-02")]
alias Additive.addAction_isPretransitive := Additive.addMonoidAction_isPretransitive

instance Multiplicative.monoidAction_isPretransitive [AddMonoid α] [AddMonoidAction α β]
    [AddMonoidAction.IsPretransitive α β] : MonoidAction.IsPretransitive (Multiplicative α) β :=
  ⟨@AddMonoidAction.exists_vadd_eq α _ _ _⟩

@[deprecated (since := "2026-09-02")]
alias Multiplicative.mulAction_isPretransitive := Multiplicative.monoidAction_isPretransitive

end
