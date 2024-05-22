/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Group.Basic
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
`[CancelMonoid M] [PartialOrder M] [CovariantClass M M (Function.swap (*)) (≤)]`
and have a go at seeing if the proof still works!

Note that it is possible to combine several `Co(ntra)variantClass` assumptions together.
Indeed, the usual ordered typeclasses arise from assuming the pair
`[CovariantClass M M (*) (≤)] [ContravariantClass M M (*) (<)]`
on top of order/algebraic assumptions.

A formal remark is that normally `CovariantClass` uses the `(≤)`-relation, while
`ContravariantClass` uses the `(<)`-relation. This need not be the case in general, but seems to be
the most common usage. In the opposite direction, the implication
```lean
[Semigroup α] [PartialOrder α] [ContravariantClass α α (*) (≤)] → LeftCancelSemigroup α
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

/-- `Covariant` is useful to formulate succinctly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `CovariantClass` doc-string for its meaning. -/
def Covariant : Prop :=
  ∀ (m) {n₁ n₂}, r n₁ n₂ → r (μ m n₁) (μ m n₂)
#align covariant Covariant

/-- `Contravariant` is useful to formulate succinctly statements about the interactions between an
action of a Type on another one and a relation on the acted-upon Type.

See the `ContravariantClass` doc-string for its meaning. -/
def Contravariant : Prop :=
  ∀ (m) {n₁ n₂}, r (μ m n₁) (μ m n₂) → r n₁ n₂
#align contravariant Contravariant

/-- TODO -/
class MulLeftMono [Mul M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (· * ·) (· ≤ ·)

/-- TODO -/
class MulRightMono [Mul M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (swap (· * ·)) (· ≤ ·)

/-- TODO -/
class AddLeftMono [Add M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (· + ·) (· ≤ ·)

/-- TODO -/
class AddRightMono [Add M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (swap (· + ·)) (· ≤ ·)

attribute [to_additive] MulLeftMono MulRightMono

/-- TODO -/
class MulLeftStrictMono [Mul M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (· * ·) (· < ·)

/-- TODO -/
class MulRightStrictMono [Mul M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (swap (· * ·)) (· < ·)

/-- TODO -/
class AddLeftStrictMono [Add M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (· + ·) (· < ·)

/-- TODO -/
class AddRightStrictMono [Add M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Covariant M M (swap (· + ·)) (· < ·)

attribute [to_additive] MulLeftStrictMono MulRightStrictMono

/-- TODO -/
class MulLeftReflectLE [Mul M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (· * ·) (· ≤ ·)

/-- TODO -/
class MulRightReflectLE [Mul M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (swap (· * ·)) (· ≤ ·)

/-- TODO -/
class AddLeftReflectLE [Add M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (· + ·) (· ≤ ·)

/-- TODO -/
class AddRightReflectLE [Add M] [LE M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (swap (· + ·)) (· ≤ ·)

attribute [to_additive] MulLeftReflectLE MulRightReflectLE

/-- TODO -/
class MulLeftReflectLT [Mul M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (· * ·) (· < ·)

/-- TODO -/
class MulRightReflectLT [Mul M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (swap (· * ·)) (· < ·)

/-- TODO -/
class AddLeftReflectLT [Add M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (· + ·) (· < ·)

/-- TODO -/
class AddRightReflectLT [Add M] [LT M] : Prop where
  /-- TODO -/
  protected elim : Contravariant M M (swap (· + ·)) (· < ·)

attribute [to_additive] MulLeftReflectLT MulRightReflectLT

variable {M N μ r}

theorem rel_iff_cov (co : Covariant M N μ r) (contra : Contravariant M N μ r)
    (m : M) {a b : N} :
    r (μ m a) (μ m b) ↔ r a b :=
  ⟨contra _, co _⟩
#align rel_iff_cov rel_iff_cov

section flip

theorem Covariant.flip (h : Covariant M N μ r) : Covariant M N μ (flip r) :=
  fun a _ _ ↦ h a
#align covariant.flip Covariant.flip

theorem Contravariant.flip (h : Contravariant M N μ r) : Contravariant M N μ (flip r) :=
  fun a _ _ ↦ h a
#align contravariant.flip Contravariant.flip

end flip

section Covariant

variable (co : Covariant M N μ r)

theorem Covariant.act_rel_act_of_rel (m : M) {a b : N} (ab : r a b) : r (μ m a) (μ m b) :=
  co _ ab
#align act_rel_act_of_rel Covariant.act_rel_act_of_rel

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
instance (priority := 100) Group.mulLeftReflectLE_of_mulLeftMono [Group N] [LE N]
    [MulLeftMono N] : MulLeftReflectLE N :=
  ⟨Group.covariant_iff_contravariant.mp MulLeftMono.elim⟩

@[to_additive]
instance (priority := 100) Group.mulLeftReflectLT_of_mulLeftStrictMono [Group N] [LT N]
    [MulLeftStrictMono N] : MulLeftReflectLT N :=
  ⟨Group.covariant_iff_contravariant.mp MulLeftStrictMono.elim⟩

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
instance (priority := 100) Group.mulRightReflectLE_of_mulRightMono [Group N] [LE N]
    [MulRightMono N] : MulRightReflectLE N :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp MulRightMono.elim⟩

@[to_additive]
instance (priority := 100) Group.mulRightReflectLT_of_mulRightStrictMono [Group N] [LT N]
    [MulRightStrictMono N] : MulRightReflectLT N :=
  ⟨Group.covariant_swap_iff_contravariant_swap.mp MulRightStrictMono.elim⟩


section Trans

variable [IsTrans N r] (m n : M) {a b c d : N}

--  Lemmas with 3 elements.
theorem Covariant.act_rel_of_rel_of_act_rel (ab : r a b) (rl : r (μ m b) c) : r (μ m a) c :=
  _root_.trans (co.act_rel_act_of_rel m ab) rl
#align act_rel_of_rel_of_act_rel Covariant.act_rel_of_rel_of_act_rel

theorem Covariant.rel_act_of_rel_of_rel_act (ab : r a b) (rr : r c (μ m a)) : r c (μ m b) :=
  _root_.trans rr (co.act_rel_act_of_rel _ ab)
#align rel_act_of_rel_of_rel_act Covariant.rel_act_of_rel_of_rel_act

end Trans

end Covariant

--  Lemma with 4 elements.
section MEqN

variable {mu : N → N → N} [IsTrans N r] (co : Covariant N N mu r)
  (co' : Covariant N N (swap mu) r) {a b c d : N}

theorem Covariant.act_rel_act_of_rel_of_rel (ab : r a b) (cd : r c d) : r (mu a c) (mu b d) :=
  _root_.trans (@act_rel_act_of_rel _ _ (swap mu) r co' c _ _ ab) (act_rel_act_of_rel co b cd)
#align act_rel_act_of_rel_of_rel Covariant.act_rel_act_of_rel_of_rel

end MEqN

namespace Contravariant

variable (contra : Contravariant M N μ r)

theorem rel_of_act_rel_act (m : M) {a b : N} (ab : r (μ m a) (μ m b)) : r a b :=
  contra _ ab
#align rel_of_act_rel_act Contravariant.rel_of_act_rel_act

section Trans

variable [IsTrans N r] (m n : M) {a b c d : N}

--  Lemmas with 3 elements.
theorem act_rel_of_act_rel_of_rel_act_rel (ab : r (μ m a) b) (rl : r (μ m b) (μ m c)) :
    r (μ m a) c :=
  _root_.trans ab (contra.rel_of_act_rel_act m rl)
#align act_rel_of_act_rel_of_rel_act_rel Contravariant.act_rel_of_act_rel_of_rel_act_rel

theorem rel_act_of_act_rel_act_of_rel_act (ab : r (μ m a) (μ m b)) (rr : r b (μ m c)) :
    r a (μ m c) :=
  _root_.trans (contra.rel_of_act_rel_act m ab) rr
#align rel_act_of_act_rel_act_of_rel_act Contravariant.rel_act_of_act_rel_act_of_rel_act

end Trans

end Contravariant

section Monotone

variable {α : Type*} [Preorder α] [Preorder N]
variable {f : N → α}

/-- The partial application of a constant to a covariant operator is monotone. -/
theorem Covariant.monotone_of_const (co : Covariant M N μ (· ≤ ·)) (m : M) : Monotone (μ m) :=
  fun _ _ ↦ co m
#align covariant.monotone_of_const Covariant.monotone_of_const

/-- A monotone function remains monotone when composed with the partial application
of a covariant operator. E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (m + n))`. -/
theorem Monotone.covariant_of_const (co : Covariant M N μ (· ≤ ·)) (hf : Monotone f) (m : M) :
    Monotone (f <| μ m ·) :=
  hf.comp (co.monotone_of_const m)
#align monotone.covariant_of_const Monotone.covariant_of_const

/-- Same as `Monotone.covariant_of_const`, but with the constant on the other side of
the operator.  E.g., `∀ (m : ℕ), Monotone f → Monotone (fun n ↦ f (n + m))`. -/
theorem Monotone.covariant_of_const' {μ : N → N → N} (co : Covariant N N (swap μ) (· ≤ ·))
    (hf : Monotone f) (m : N) : Monotone (f <| μ · m) :=
  Monotone.covariant_of_const co hf m
#align monotone.covariant_of_const' Monotone.covariant_of_const'

/-- Dual of `Monotone.covariant_of_const` -/
theorem Antitone.covariant_of_const (co : Covariant M N μ (· ≤ ·)) (hf : Antitone f) (m : M) :
    Antitone (f <| μ m ·) :=
  hf.comp_monotone <| co.monotone_of_const m
#align antitone.covariant_of_const Antitone.covariant_of_const

/-- Dual of `Monotone.covariant_of_const'` -/
theorem Antitone.covariant_of_const' {μ : N → N → N} (co : Covariant N N (swap μ) (· ≤ ·))
    (hf : Antitone f) (m : N) : Antitone (f <| μ · m) :=
  Antitone.covariant_of_const co hf m
#align antitone.covariant_of_const' Antitone.covariant_of_const'

end Monotone

theorem covariant_le_of_covariant_lt [PartialOrder N] :
    Covariant M N μ (· < ·) → Covariant M N μ (· ≤ ·) := by
  intro h a b c bc
  rcases bc.eq_or_lt with (rfl | bc)
  · exact le_rfl
  · exact (h _ bc).le
#align covariant_le_of_covariant_lt covariant_le_of_covariant_lt

@[to_additive]
theorem mulLeftMono_of_mulLeftStrictMono (M) [Mul M] [PartialOrder M] [MulLeftStrictMono M] :
    MulLeftMono M := ⟨covariant_le_of_covariant_lt MulLeftStrictMono.elim⟩

@[to_additive]
theorem mulRightMono_of_mulRightStrictMono (M) [Mul M] [PartialOrder M] [MulRightStrictMono M] :
    MulRightMono M := ⟨covariant_le_of_covariant_lt MulRightStrictMono.elim⟩

theorem contravariant_le_iff_contravariant_lt_and_eq [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) ∧ Contravariant M N μ (· = ·) := by
  refine ⟨fun h ↦ ⟨fun a b c bc ↦ ?_, fun a b c bc ↦ ?_⟩, fun h ↦ fun a b c bc ↦ ?_⟩
  · exact (h a bc.le).lt_of_ne (by rintro rfl; exact lt_irrefl _ bc)
  · exact (h a bc.le).antisymm (h a bc.ge)
  · exact bc.lt_or_eq.elim (fun bc ↦ (h.1 a bc).le) (fun bc ↦ (h.2 a bc).le)

theorem contravariant_lt_of_contravariant_le [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) → Contravariant M N μ (· < ·) :=
  And.left ∘ contravariant_le_iff_contravariant_lt_and_eq.mp
#align contravariant_lt_of_contravariant_le contravariant_lt_of_contravariant_le

theorem covariant_le_iff_contravariant_lt [LinearOrder N] :
    Covariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) :=
  ⟨fun h _ _ _ bc ↦ not_le.mp fun k ↦ bc.not_le (h _ k),
   fun h _ _ _ bc ↦ not_lt.mp fun k ↦ bc.not_lt (h _ k)⟩
#align covariant_le_iff_contravariant_lt covariant_le_iff_contravariant_lt

theorem covariant_lt_iff_contravariant_le [LinearOrder N] :
    Covariant M N μ (· < ·) ↔ Contravariant M N μ (· ≤ ·) :=
  ⟨fun h _ _ _ bc ↦ not_lt.mp fun k ↦ bc.not_lt (h _ k),
   fun h _ _ _ bc ↦ not_le.mp fun k ↦ bc.not_le (h _ k)⟩
#align covariant_lt_iff_contravariant_le covariant_lt_iff_contravariant_le

variable {mu : N → N → N}

theorem covariant_flip_iff [IsSymmOp N N mu] :
    Covariant N N (flip mu) r ↔ Covariant N N mu r := by rw [IsSymmOp.flip_eq]
#noalign covariant_flip_mul_iff
#noalign covariant_flip_add_iff

theorem contravariant_flip_iff [IsSymmOp N N mu] :
    Contravariant N N (flip mu) r ↔ Contravariant N N mu r := by rw [IsSymmOp.flip_eq]
#noalign contravariant_flip_mul_iff
#noalign contravariant_flip_add_iff

@[to_additive]
instance mulLeftReflectLT_of_mulLeftMono [Mul N] [LinearOrder N] [MulLeftMono N] :
    MulLeftReflectLT N where
  elim := covariant_le_iff_contravariant_lt.mp MulLeftMono.elim

@[to_additive]
instance mulRightReflectLT_of_mulRightMono [Mul N] [LinearOrder N] [MulRightMono N] :
    MulRightReflectLT N where
  elim := covariant_le_iff_contravariant_lt.mp MulRightMono.elim

@[to_additive]
instance mulLeftMono_of_mulLeftReflectLT [Mul N] [LinearOrder N] [MulLeftReflectLT N] :
    MulLeftMono N where
  elim := covariant_le_iff_contravariant_lt.mpr MulLeftReflectLT.elim

@[to_additive]
instance mulRightMono_of_mulRightReflectLT [Mul N] [LinearOrder N] [MulRightReflectLT N] :
    MulRightMono N where
  elim := covariant_le_iff_contravariant_lt.mpr MulRightReflectLT.elim

@[to_additive]
instance mulRightMono_of_mulLeftMono [CommSemigroup N] [LE N] [MulLeftMono N] :
    MulRightMono N where
  elim := covariant_flip_iff.mpr MulLeftMono.elim

@[to_additive]
instance mulRightStrictMono_of_mulLeftStrictMono [CommSemigroup N] [LT N] [MulLeftStrictMono N] :
    MulRightStrictMono N where
  elim := covariant_flip_iff.mpr MulLeftStrictMono.elim

@[to_additive]
instance mulRightReflectLE_of_mulLeftReflectLE [CommSemigroup N] [LE N] [MulLeftReflectLE N] :
    MulRightReflectLE N where
  elim := contravariant_flip_iff.mpr MulLeftReflectLE.elim

@[to_additive]
instance mulRightReflectLT_of_mulLeftReflectLT [CommSemigroup N] [LT N] [MulLeftReflectLT N] :
    MulRightReflectLT N where
  elim := contravariant_flip_iff.mpr MulLeftReflectLT.elim

theorem covariant_lt_of_covariant_le_of_contravariant_eq (contra : Contravariant M N μ (· = ·))
    [PartialOrder N] (co : Covariant M N μ (· ≤ ·)) : Covariant M N μ (· < ·) :=
  fun a _ _ bc ↦ (co a bc.le).lt_of_ne (bc.ne ∘ contra _)

theorem contravariant_le_of_contravariant_eq_and_lt [PartialOrder N]
    (contra_eq : Contravariant M N μ (· = ·)) (contra_lt : Contravariant M N μ (· < ·)) :
    Contravariant M N μ (· ≤ ·) :=
  contravariant_le_iff_contravariant_lt_and_eq.mpr ⟨contra_lt, contra_eq⟩

/- TODO:
  redefine `IsLeftCancel N mu` as abbrev of `ContravariantClass N N mu (· = ·)`,
  redefine `IsRightCancel N mu` as abbrev of `ContravariantClass N N (flip mu) (· = ·)`,
  redefine `IsLeftCancelMul` as abbrev of `IsLeftCancel`,
  then the following four instances (actually eight) can be removed in favor of the above two. -/

@[to_additive]
instance IsLeftCancelMul.mulLeftStrictMono_of_mulLeftMono [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftMono N] :
    MulLeftStrictMono N where
  elim a _ _ bc := (MulLeftMono.elim a bc.le).lt_of_ne ((mul_ne_mul_right a).mpr bc.ne)

@[to_additive]
instance IsRightCancelMul.mulRightStrictMono_of_mulRightMono
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightMono N] :
    MulRightStrictMono N where
  elim a _ _ bc := (MulRightMono.elim a bc.le).lt_of_ne ((mul_ne_mul_left a).mpr bc.ne)

@[to_additive]
instance IsLeftCancelMul.mulLeftReflectLE_of_mulLeftReflectLT [Mul N] [IsLeftCancelMul N]
    [PartialOrder N] [MulLeftReflectLT N] :
    MulLeftReflectLE N where
  elim := contravariant_le_iff_contravariant_lt_and_eq.mpr
    ⟨MulLeftReflectLT.elim, fun _ ↦ mul_left_cancel⟩

@[to_additive]
instance IsRightCancelMul.mulRightReflectLE_of_mulRightReflectLT
    [Mul N] [IsRightCancelMul N] [PartialOrder N] [MulRightReflectLT N] :
    MulRightReflectLE N where
  elim := contravariant_le_iff_contravariant_lt_and_eq.mpr
    ⟨MulRightReflectLT.elim, fun _ ↦ mul_right_cancel⟩

end Variants
