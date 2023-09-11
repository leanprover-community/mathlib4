/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic

#align_import algebra.covariant_and_contravariant from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-!

# Covariants and contravariants

This file contains general lemmas and instances to work with the interactions between a relation and
an action on a Type.

The intended application is the splitting of the ordering from the algebraic assumptions on the
operations in the `Ordered[...]` hierarchy.

The strategy is to introduce two more flexible typeclasses, `CovariantClass` and
`ContravariantClass`:

* `CovariantClass` models the implication `a ≤ b → c * a ≤ c * b` (multiplication is monotone),
* `ContravariantClass` models the implication `a * b < a * c → b < c`.

Since `Co(ntra)variantClass` takes as input the operation (typically `(+)` or `(*)`) and the order
relation (typically `(≤)` or `(<)`), these are the only two typeclasses that I have used.

The general approach is to formulate the lemma that you are interested in and prove it, with the
`Ordered[...]` typeclass of your liking.  After that, you convert the single typeclass,
say `[OrderedCancelMonoid M]`, into three typeclasses, e.g.
`[LeftCancelSemigroup M] [PartialOrder M] [CovariantClass M M (Function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several `Co(ntra)variantClass` assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[CovariantClass M M (*) (≤)] [ContravariantClass M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `CovariantClass` uses the `(≤)`-relation, while
`ContravariantClass` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[Semigroup α] [PartialOrder α] [ContravariantClass α α (*) (≤)] => LeftCancelSemigroup α
```
holds -- note the `Co*ntra*` assumption on the `(≤)`-relation.

# Formalization notes

We stick to the convention of using `Function.swap (*)` (or `Function.swap (+)`), for the
typeclass assumptions, since `Function.swap` is slightly better behaved than `flip`.
However, sometimes as a **non-typeclass** assumption, we prefer `flip (*)` (or `flip (+)`),
as it is easier to use.

-/


-- TODO: convert `ExistsMulOfLE`, `ExistsAddOfLE`?
-- TODO: relationship with `Con/AddCon`
-- TODO: include equivalence of `LeftCancelSemigroup` with
-- `Semigroup PartialOrder ContravariantClass α α (*) (≤)`?
-- TODO : use ⇒, as per Eric's suggestion?  See
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/ordered.20stuff/near/236148738
-- for a discussion.
open Function

section Variants

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (M N)

/-- `Covariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `CovariantClass` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)
#align covariant Covariant

/-- `Contravariant` is useful to formulate succintly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `ContravariantClass` doc-string for its meaning. -/
def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂
#align contravariant Contravariant

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`CovariantClass` says that "the action `μ` preserves the relation `r`."

More precisely, the `CovariantClass` is a class taking two Types `M N`, together with an "action"
`μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the assertion that
for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
`(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)`,
obtained from `(n₁, n₂)` by acting upon it by `m`.

If `m : M` and `h : r n₁ n₂`, then `CovariantClass.elim m h : r (μ m n₁) (μ m n₂)`.
-/
class CovariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the pair
  `(n₁, n₂)`, then, the relation `r` also holds for the pair `(μ m n₁, μ m n₂)` -/
  protected elim : Covariant M N μ r
#align covariant_class CovariantClass

/-- Given an action `μ` of a Type `M` on a Type `N` and a relation `r` on `N`, informally, the
`ContravariantClass` says that "if the result of the action `μ` on a pair satisfies the
relation `r`, then the initial pair satisfied the relation `r`."

More precisely, the `ContravariantClass` is a class taking two Types `M N`, together with an
"action" `μ : M → N → N` and a relation `r : N → N → Prop`.  Its unique field `elim` is the
assertion that for all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
`r` also holds for the pair `(n₁, n₂)`.

If `m : M` and `h : r (μ m n₁) (μ m n₂)`, then `ContravariantClass.elim m h : r n₁ n₂`.
-/
class ContravariantClass : Prop where
  /-- For all `m ∈ M` and all elements `n₁, n₂ ∈ N`, if the relation `r` holds for the
  pair `(μ m n₁, μ m n₂)` obtained from `(n₁, n₂)` by acting upon it by `m`, then, the relation
  `r` also holds for the pair `(n₁, n₂)`. -/
  protected elim : Contravariant M N μ r
#align contravariant_class ContravariantClass

theorem rel_iff_cov [CovariantClass M N μ r] [ContravariantClass M N μ r] (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩
#align rel_iff_cov rel_iff_cov

section flip

variable {M N μ r}

theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) :=
  fun a _ _ hbc ↦ h a hbc
#align covariant.flip Covariant.flip

theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) :=
  fun a _ _ hbc ↦ h a hbc
#align contravariant.flip Contravariant.flip

end flip

section Covariant

variable {M N μ r} [CovariantClass M N μ r]

theorem act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  CovariantClass.elim _ ab
#align act_rel_act_of_rel act_rel_act_of_rel

@[to_additive]
theorem Group.covariant_iff_contravariant [Group N] :
    Covariant N N (· * ·) r ↔ Contravariant N N (· * ·) r := by
  refine ⟨fun h a b c bc ↦ ?_, fun h a b c bc ↦ ?_⟩
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c]
    exact h a⁻¹ bc
  · rw [← inv_mul_cancel_left a b, ← inv_mul_cancel_left a c] at bc
    exact h a⁻¹ bc
#align group.covariant_iff_contravariant Group.covariant_iff_contravariant
#align add_group.covariant_iff_contravariant AddGroup.covariant_iff_contravariant

@[to_additive]
instance (priority := 100) Group.covconv [Group N] [CovariantClass N N (· * ·) r] :
    ContravariantClass N N (· * ·) r :=
  ⟨Group.covariant_iff_contravariant.mp CovariantClass.elim⟩

@[to_additive]
theorem Group.covariant_swap_iff_contravariant_swap [Group N] :
    Covariant N N (swap (· * ·)) r ↔ Contravariant N N (swap (· * ·)) r := by
  refine ⟨fun h a b c bc ↦ ?_, fun h a b c bc ↦ ?_⟩
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a]
    exact h a⁻¹ bc
  · rw [← mul_inv_cancel_right b a, ← mul_inv_cancel_right c a] at bc
    exact h a⁻¹ bc
#align group.covariant_swap_iff_contravariant_swap Group.covariant_swap_iff_contravariant_swap
#align add_group.covariant_swap_iff_contravariant_swap AddGroup.covariant_swap_iff_contravariant_swap


@[to_additive]
instance (priority := 100) Group.covconv_swap [Group N] [CovariantClass N N (swap (· * ·)) r] :
    ContravariantClass N N (swap (· * ·)) r :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp CovariantClass.elim⟩


section Trans

variable [IsTrans N r] (m n : M) {a b c d : N}

--  Lemmas with 3 elements.
theorem act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  _root_.trans (act_rel_act_of_rel m ab) rl
#align act_rel_of_rel_of_act_rel act_rel_of_rel_of_act_rel

theorem rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  _root_.trans rr (act_rel_act_of_rel _ ab)
#align rel_act_of_rel_of_rel_act rel_act_of_rel_of_rel_act

end Trans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {M N μ r} {mu : N → N → N} [IsTrans N r] [i : CovariantClass N N mu r]
  [i' : CovariantClass N N (swap mu) r] {a b c d : N}

theorem act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r _ c _ _ ab) (act_rel_act_of_rel b cd)
#align act_rel_act_of_rel_of_rel act_rel_act_of_rel_of_rel

end MEqN

section Contravariant

variable {M N μ r} [ContravariantClass M N μ r]

theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  ContravariantClass.elim _ ab
#align rel_of_act_rel_act rel_of_act_rel_act

section Trans

variable [IsTrans N r] (m n : M) {a b c d : N}

--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
    r (μ m a) c :=
  _root_.trans ab (rel_of_act_rel_act m rl)
#align act_rel_of_act_rel_of_rel_act_rel act_rel_of_act_rel_of_rel_act_rel

theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
    r a (μ m c) :=
  _root_.trans (rel_of_act_rel_act m ab) rr
#align rel_act_of_act_rel_act_of_rel_act rel_act_of_act_rel_act_of_rel_act

end Trans

end Contravariant

section Monotone

variable {α : Type*} {M N μ} [Preorder α] [Preorder N]

variable {f : N → α}

/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const [CovariantClass M N μ (· ≤ ·)] (m : M) : Monotone (μ m) :=
  fun _ _ ha ↦ CovariantClass.elim m ha
#align covariant.monotone_of_const Covariant.monotone_of_const

/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (m + n))`. -/
theorem Monotone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Monotone f) (m : M) :
    Monotone fun n ↦ f (μ m n) :=
  fun _ _ x ↦ hf (Covariant.monotone_of_const m x)
#align monotone.covariant_of_const Monotone.covariant_of_const

/-- Same as `Monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (n + m))`. -/
theorem Monotone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Monotone f) (m : N) : Monotone fun n ↦ f (μ n m) :=
  fun _ _ x ↦ hf (@Covariant.monotone_of_const _ _ (swap μ) _ _ m _ _ x)
#align monotone.covariant_of_const' Monotone.covariant_of_const'

/-- Dual of `Monotone.covariant_of_const` -/
theorem Antitone.covariant_of_const [CovariantClass M N μ (· ≤ ·)] (hf : Antitone f) (m : M) :
    Antitone fun n ↦ f (μ m n) :=
  hf.comp_monotone <| Covariant.monotone_of_const m
#align antitone.covariant_of_const Antitone.covariant_of_const

/-- Dual of `Monotone.covariant_of_const'` -/
theorem Antitone.covariant_of_const' {μ : N → N → N} [CovariantClass N N (swap μ) (· ≤ ·)]
    (hf : Antitone f) (m : N) : Antitone fun n ↦ f (μ n m) :=
  hf.comp_monotone <| @Covariant.monotone_of_const _ _ (swap μ) _ _ m
#align antitone.covariant_of_const' Antitone.covariant_of_const'

end Monotone

theorem covariant_le_of_covariant_lt [PartialOrder N] :
    Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  intro h a b c bc
  rcases le_iff_eq_or_lt.mp bc with (rfl | bc)
  · exact rfl.le
  · exact (h _ bc).le
#align covariant_le_of_covariant_lt covariant_le_of_covariant_lt

theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) := by
  refine fun h a b c bc ↦ lt_iff_le_and_ne.mpr ⟨h a bc.le, ?_⟩
  rintro rfl; exact lt_irrefl _ bc
#align contravariant_lt_of_contravariant_le contravariant_lt_of_contravariant_le

theorem covariant_le_iff_contravariant_lt [LinearOrder N] :
    Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h _ _ _ bc ↦ not_le.mp fun k ↦ not_le.mpr bc (h _ k),
   fun h _ _ _ bc ↦ not_lt.mp fun k ↦ not_lt.mpr bc (h _ k)⟩
#align covariant_le_iff_contravariant_lt covariant_le_iff_contravariant_lt

theorem covariant_lt_iff_contravariant_le [LinearOrder N] :
    Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h _ _ _ bc ↦ not_lt.mp fun k ↦ not_lt.mpr bc (h _ k),
   fun h _ _ _ bc ↦ not_le.mp fun k ↦ not_le.mpr bc (h _ k)⟩
#align covariant_lt_iff_contravariant_le covariant_lt_iff_contravariant_le

-- Porting note: `covariant_flip_mul_iff` used to use the `IsSymmOp` typeclass from Lean 3 core.
-- To avoid it, we prove the relevant lemma here.
@[to_additive]
lemma flip_mul [CommSemigroup N] : (flip (· * ·) : N → N → N) = (· * ·) :=
  funext fun a ↦ funext fun b ↦ mul_comm b a

@[to_additive]
theorem covariant_flip_mul_iff [CommSemigroup N] :
    Covariant N N (flip (· * ·)) r ↔ Covariant N N (· * ·) r := by rw [flip_mul]
#align covariant_flip_mul_iff covariant_flip_mul_iff
#align covariant_flip_add_iff covariant_flip_add_iff

@[to_additive]
theorem contravariant_flip_mul_iff [CommSemigroup N] :
    Contravariant N N (flip (· * ·)) r ↔ Contravariant N N (· * ·) r := by rw [flip_mul]
#align contravariant_flip_mul_iff contravariant_flip_mul_iff
#align contravariant_flip_add_iff contravariant_flip_add_iff

@[to_additive]
instance contravariant_mul_lt_of_covariant_mul_le [Mul N] [LinearOrder N]
    [CovariantClass N N (· * ·) (· ≤ ·)] : ContravariantClass N N (· * ·) (· < ·) where
  elim := (covariant_le_iff_contravariant_lt N N (· * ·)).mp CovariantClass.elim

@[to_additive]
instance covariant_mul_lt_of_contravariant_mul_le [Mul N] [LinearOrder N]
    [ContravariantClass N N (· * ·) (· ≤ ·)] : CovariantClass N N (· * ·) (· < ·) where
  elim := (covariant_lt_iff_contravariant_le N N (· * ·)).mpr ContravariantClass.elim

@[to_additive]
instance covariant_swap_mul_le_of_covariant_mul_le [CommSemigroup N] [LE N]
    [CovariantClass N N (· * ·) (· ≤ ·)] : CovariantClass N N (swap (· * ·)) (· ≤ ·) where
  elim := (covariant_flip_mul_iff N (· ≤ ·)).mpr CovariantClass.elim

@[to_additive]
instance contravariant_swap_mul_le_of_contravariant_mul_le [CommSemigroup N] [LE N]
    [ContravariantClass N N (· * ·) (· ≤ ·)] : ContravariantClass N N (swap (· * ·)) (· ≤ ·) where
  elim := (contravariant_flip_mul_iff N (· ≤ ·)).mpr ContravariantClass.elim

@[to_additive]
instance contravariant_swap_mul_lt_of_contravariant_mul_lt [CommSemigroup N] [LT N]
    [ContravariantClass N N (· * ·) (· < ·)] : ContravariantClass N N (swap (· * ·)) (· < ·) where
  elim := (contravariant_flip_mul_iff N (· < ·)).mpr ContravariantClass.elim

@[to_additive]
instance covariant_swap_mul_lt_of_covariant_mul_lt [CommSemigroup N] [LT N]
    [CovariantClass N N (· * ·) (· < ·)] : CovariantClass N N (swap (· * ·)) (· < ·) where
  elim := (covariant_flip_mul_iff N (· < ·)).mpr CovariantClass.elim

@[to_additive]
instance LeftCancelSemigroup.covariant_mul_lt_of_covariant_mul_le [LeftCancelSemigroup N]
    [PartialOrder N] [CovariantClass N N (· * ·) (· ≤ ·)] :
    CovariantClass N N (· * ·) (· < ·) where
  elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_right a).mpr cb⟩

@[to_additive]
instance RightCancelSemigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le
    [RightCancelSemigroup N] [PartialOrder N] [CovariantClass N N (swap (· * ·)) (· ≤ ·)] :
    CovariantClass N N (swap (· * ·)) (· < ·) where
  elim a b c bc := by
    cases' lt_iff_le_and_ne.mp bc with bc cb
    exact lt_iff_le_and_ne.mpr ⟨CovariantClass.elim a bc, (mul_ne_mul_left a).mpr cb⟩

@[to_additive]
instance LeftCancelSemigroup.contravariant_mul_le_of_contravariant_mul_lt [LeftCancelSemigroup N]
    [PartialOrder N] [ContravariantClass N N (· * ·) (· < ·)] :
    ContravariantClass N N (· * ·) (· ≤ ·) where
  elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_right_inj a).mp h).le
    · exact (ContravariantClass.elim _ h).le

@[to_additive]
instance RightCancelSemigroup.contravariant_swap_mul_le_of_contravariant_swap_mul_lt
    [RightCancelSemigroup N] [PartialOrder N] [ContravariantClass N N (swap (· * ·)) (· < ·)] :
    ContravariantClass N N (swap (· * ·)) (· ≤ ·) where
  elim a b c bc := by
    cases' le_iff_eq_or_lt.mp bc with h h
    · exact ((mul_left_inj a).mp h).le
    · exact (ContravariantClass.elim _ h).le

end Variants
