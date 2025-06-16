/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.GroupWithZero.ProdHom
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Monoid.Lex
import Mathlib.Data.Prod.Lex

/-!
# Order homomorphisms for products of linearly ordered groups with zero

This file defines order homomorphisms for products of linearly ordered groups with zero,
which is identified with the `WithZero` of the lexicographic product of the units of the groups.

The product of linearly ordered groups with zero `WithZero (αˣ ×ₗ βˣ)` is a
linearly ordered group with zero itself with natural inclusions but only one projection.
One has to work with the lexicographic product of the units `αˣ ×ₗ βˣ` since otherwise,
the plain product `αˣ × βˣ` would not be linearly ordered.

## TODO

Create the "LinOrdCommGrpWithZero" category.

-/

-- TODO: find a better place
/-- `toLex` as a monoid isomorphism. -/
def toLexMulEquiv (G H : Type*) [MulOneClass G] [MulOneClass H] : G × H ≃* G ×ₗ H where
  toFun := toLex
  invFun := ofLex
  left_inv := ofLex_toLex
  right_inv := toLex_ofLex
  map_mul' := toLex_mul

@[simp]
lemma coe_toLexMulEquiv (G H : Type*) [MulOneClass G] [MulOneClass H] :
    ⇑(toLexMulEquiv G H) = toLex :=
  rfl

@[simp]
lemma coe_symm_toLexMulEquiv (G H : Type*) [MulOneClass G] [MulOneClass H] :
    ⇑(toLexMulEquiv G H).symm = ofLex :=
  rfl

@[simp]
lemma toEquiv_toLexMulEquiv (G H : Type*) [MulOneClass G] [MulOneClass H] :
    ⇑(toLexMulEquiv G H : G × H ≃ G ×ₗ H) = toLex :=
  rfl

@[simp]
lemma toEquiv_symm_toLexMulEquiv (G H : Type*) [MulOneClass G] [MulOneClass H] :
    ⇑((toLexMulEquiv G H).symm : G ×ₗ H ≃ G × H) = ofLex :=
  rfl

namespace MonoidWithZeroHom

variable {M₀ N₀ : Type*}

lemma inl_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : Monotone (inl M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inl_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.zero_le, WithZero.withZeroUnitsEquiv]

lemma inl_strictMono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [PartialOrder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : StrictMono (inl M₀ N₀) :=
  inl_mono.strictMono_of_injective inl_injective

lemma inr_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : Monotone (inr M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inr_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.zero_le, WithZero.withZeroUnitsEquiv]

lemma inr_strictMono [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : StrictMono (inr M₀ N₀) :=
  inr_mono.strictMono_of_injective inr_injective

lemma fst_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀] :
    Monotone (fst M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp +contextual [WithZero.forall, Prod.le_def]


lemma snd_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀] :
    Monotone (snd M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp [WithZero.forall, Prod.le_def]

end MonoidWithZeroHom

namespace LinearOrderedCommGroupWithZero

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

open MonoidWithZeroHom

/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
M to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inl : α →*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inl α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inl_mono

/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
N to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inr : β →*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inr α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inr_mono

/-- Given linearly ordered groups with zero M, N, the natural projection ordered homomorphism from
`WithZero (Mˣ ×ₗ Nˣ)` to M, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def fst : WithZero (αˣ ×ₗ βˣ) →*₀o α where
  __ := (fst α β).comp (WithZero.map' (toLexMulEquiv ..).symm.toMonoidHom)
  monotone' := by
    -- this can't rely on `Monotone.comp` since `ofLex` is not monotone
    intro x y
    cases x <;>
    cases y
    · simp
    · simp
    · simp [WithZero.zero_lt_coe]
    · simpa using Prod.Lex.monotone_fst _ _

@[simp]
theorem fst_comp_inl : (fst _ _).comp (inl α β) = .id α := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp

variable {α β}

lemma inl_eq_coe_inlₗ {m : α} (hm : m ≠ 0) :
    inl α β m = OrderMonoidHom.inlₗ αˣ βˣ (Units.mk0 _ hm) := by
  lift m to αˣ using isUnit_iff_ne_zero.mpr hm
  simp

lemma inr_eq_coe_inrₗ {n : β} (hn : n ≠ 0) :
    inr α β n = OrderMonoidHom.inrₗ αˣ βˣ (Units.mk0 _ hn) := by
  lift n to βˣ using isUnit_iff_ne_zero.mpr hn
  simp

theorem inl_mul_inr_eq_coe_toLex {m : α} {n : β} (hm : m ≠ 0) (hn : n ≠ 0) :
    inl α β m * inr α β n = toLex (Units.mk0 _ hm, Units.mk0 _ hn) := by
  rw [inl_eq_coe_inlₗ hm, inr_eq_coe_inrₗ hn,
      ← WithZero.coe_mul, OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex]

end LinearOrderedCommGroupWithZero
