/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Prod
import Mathlib.Algebra.Order.Pi
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.Tactic.GCongr.Core
import Mathlib.Tactic.Positivity

#align_import algebra.order.smul from "leanprover-community/mathlib"@"3ba15165bd6927679be7c22d6091a87337e3cd0c"

/-!
# Ordered scalar product

In this file we define

* `OrderedSMul R M` : an ordered additive commutative monoid `M` is an `OrderedSMul`
  over an `OrderedSemiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `Analysis/Convex/Cone.lean`.

## Implementation notes
* We choose to define `OrderedSMul` as a `Prop`-valued mixin, so that it can be
  used for actions, modules, and algebras
  (the axioms for an "ordered algebra" are exactly that the algebra is ordered as a module).
* To get ordered modules and ordered vector spaces, it suffices to replace the
  `OrderedAddCommMonoid` and the `OrderedSemiring` as desired.

## TODO

Delete the lemmas that have been generalised by `PosSMulMono` and friends.

## References

* https://en.wikipedia.org/wiki/Ordered_vector_space

## Tags

ordered module, ordered scalar, ordered smul, ordered action, ordered vector space
-/


open Pointwise

/-- The ordered scalar product property is when an ordered additive commutative monoid
with a partial order has a scalar multiplication which is compatible with the order.
-/
class OrderedSMul (R M : Type*) [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulWithZero R M] :
  Prop where
  /-- Scalar multiplication by positive elements preserves the order. -/
  protected smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b
  /-- If `c • a < c • b` for some positive `c`, then `a < b`. -/
  protected lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b
#align ordered_smul OrderedSMul

variable {ι α β γ 𝕜 R M N : Type*}

instance OrderDual.instOrderedSMul [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulWithZero R M]
    [OrderedSMul R M] : OrderedSMul R Mᵒᵈ where
  smul_lt_smul_of_pos := OrderedSMul.smul_lt_smul_of_pos (M := M)
  lt_of_smul_lt_smul_of_pos := OrderedSMul.lt_of_smul_lt_smul_of_pos (M := M)

section OrderedSMul

variable [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulWithZero R M] [OrderedSMul R M]
  {s : Set M} {a b : M} {c : R}

instance OrderedSMul.toPosSMulStrictMono : PosSMulStrictMono R M where
  elim _a ha _b₁ _b₂ hb := OrderedSMul.smul_lt_smul_of_pos hb ha

instance OrderedSMul.toPosSMulReflectLT : PosSMulReflectLT R M :=
  PosSMulReflectLT.of_pos $ fun _a ha _b₁ _b₂ h ↦ OrderedSMul.lt_of_smul_lt_smul_of_pos h ha

@[gcongr] theorem smul_lt_smul_of_pos : a < b → 0 < c → c • a < c • b := smul_lt_smul_of_pos_left
#align smul_lt_smul_of_pos smul_lt_smul_of_pos

-- TODO: Remove `smul_le_smul_of_nonneg` completely
@[gcongr] theorem smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b :=
  smul_le_smul_of_nonneg_left h₁ h₂
#align smul_le_smul_of_nonneg smul_le_smul_of_nonneg

#align smul_nonneg smul_nonneg
#align smul_nonpos_of_nonneg_of_nonpos smul_nonpos_of_nonneg_of_nonpos

theorem eq_of_smul_eq_smul_of_pos_of_le (h₁ : c • a = c • b) (hc : 0 < c) (hle : a ≤ b) : a = b :=
  hle.lt_or_eq.resolve_left fun hlt => (smul_lt_smul_of_pos hlt hc).ne h₁
#align eq_of_smul_eq_smul_of_pos_of_le eq_of_smul_eq_smul_of_pos_of_le

theorem lt_of_smul_lt_smul_of_nonneg (h : c • a < c • b) (hc : 0 ≤ c) : a < b :=
  lt_of_smul_lt_smul_of_nonneg_left h hc
#align lt_of_smul_lt_smul_of_nonneg lt_of_smul_lt_smul_of_nonneg

theorem smul_lt_smul_iff_of_pos (hc : 0 < c) : c • a < c • b ↔ a < b :=
  smul_lt_smul_iff_of_pos_left hc
#align smul_lt_smul_iff_of_pos smul_lt_smul_iff_of_pos

theorem smul_pos_iff_of_pos (hc : 0 < c) : 0 < c • a ↔ 0 < a := smul_pos_iff_of_pos_left hc
#align smul_pos_iff_of_pos smul_pos_iff_of_pos

#align smul_pos smul_pos

theorem monotone_smul_left (hc : 0 ≤ c) : Monotone (SMul.smul c : M → M) :=
  monotone_smul_left_of_nonneg hc
#align monotone_smul_left monotone_smul_left

theorem strictMono_smul_left (hc : 0 < c) : StrictMono (SMul.smul c : M → M) :=
  strictMono_smul_left_of_pos hc
#align strict_mono_smul_left strictMono_smul_left

theorem smul_lowerBounds_subset_lowerBounds_smul (hc : 0 ≤ c) :
    c • lowerBounds s ⊆ lowerBounds (c • s) :=
  (monotone_smul_left hc).image_lowerBounds_subset_lowerBounds_image
#align smul_lower_bounds_subset_lower_bounds_smul smul_lowerBounds_subset_lowerBounds_smul

theorem smul_upperBounds_subset_upperBounds_smul (hc : 0 ≤ c) :
    c • upperBounds s ⊆ upperBounds (c • s) :=
  (monotone_smul_left hc).image_upperBounds_subset_upperBounds_image
#align smul_upper_bounds_subset_upper_bounds_smul smul_upperBounds_subset_upperBounds_smul

theorem BddBelow.smul_of_nonneg (hs : BddBelow s) (hc : 0 ≤ c) : BddBelow (c • s) :=
  (monotone_smul_left hc).map_bddBelow hs
#align bdd_below.smul_of_nonneg BddBelow.smul_of_nonneg

theorem BddAbove.smul_of_nonneg (hs : BddAbove s) (hc : 0 ≤ c) : BddAbove (c • s) :=
  (monotone_smul_left hc).map_bddAbove hs
#align bdd_above.smul_of_nonneg BddAbove.smul_of_nonneg

end OrderedSMul

/-- To prove that a linear ordered monoid is an ordered module, it suffices to verify only the first
axiom of `OrderedSMul`. -/
theorem OrderedSMul.mk'' [OrderedSemiring 𝕜] [LinearOrderedAddCommMonoid M] [SMulWithZero 𝕜 M]
    (h : ∀ ⦃c : 𝕜⦄, 0 < c → StrictMono fun a : M => c • a) : OrderedSMul 𝕜 M :=
  { smul_lt_smul_of_pos := fun hab hc => h hc hab
    lt_of_smul_lt_smul_of_pos := fun hab hc => (h hc).lt_iff_lt.1 hab }
#align ordered_smul.mk'' OrderedSMul.mk''

instance Nat.orderedSMul [LinearOrderedCancelAddCommMonoid M] : OrderedSMul ℕ M :=
  OrderedSMul.mk'' fun n hn a b hab => by
    cases n with
    | zero => cases hn
    | succ n =>
      induction n with
      | zero => dsimp; rwa [one_nsmul, one_nsmul]
      | succ n ih => simp only [succ_nsmul _ n.succ, _root_.add_lt_add hab (ih n.succ_pos)]
#align nat.ordered_smul Nat.orderedSMul

instance Int.orderedSMul [LinearOrderedAddCommGroup M] : OrderedSMul ℤ M :=
  OrderedSMul.mk'' fun n hn => by
    cases n
    · simp only [Int.ofNat_eq_coe, Int.coe_nat_pos, coe_nat_zsmul] at hn ⊢
      exact strictMono_smul_left hn
    · cases (Int.negSucc_not_pos _).1 hn
#align int.ordered_smul Int.orderedSMul

section LinearOrderedSemiring
variable [LinearOrderedSemiring R] [LinearOrderedAddCommMonoid M] [SMulWithZero R M]
  [OrderedSMul R M] {a : R}

-- TODO: `LinearOrderedField M → OrderedSMul ℚ M`
instance LinearOrderedSemiring.toOrderedSMul : OrderedSMul R R :=
  OrderedSMul.mk'' fun _ => strictMono_mul_left_of_pos
#align linear_ordered_semiring.to_ordered_smul LinearOrderedSemiring.toOrderedSMul

theorem smul_max (ha : 0 ≤ a) (b₁ b₂ : M) : a • max b₁ b₂ = max (a • b₁) (a • b₂) :=
  smul_max_of_nonneg ha _ _
#align smul_max smul_max

theorem smul_min (ha : 0 ≤ a) (b₁ b₂ : M) : a • min b₁ b₂ = min (a • b₁) (a • b₂) :=
  smul_min_of_nonneg ha _ _
#align smul_min smul_min

end LinearOrderedSemiring

section LinearOrderedSemifield

variable [LinearOrderedSemifield 𝕜] [OrderedAddCommMonoid M] [OrderedAddCommMonoid N]
  [MulActionWithZero 𝕜 M] [MulActionWithZero 𝕜 N]

/-- To prove that a vector space over a linear ordered field is ordered, it suffices to verify only
the first axiom of `OrderedSMul`. -/
theorem OrderedSMul.mk' (h : ∀ ⦃a b : M⦄ ⦃c : 𝕜⦄, a < b → 0 < c → c • a ≤ c • b) :
    OrderedSMul 𝕜 M := by
  have hlt' : ∀ (a b : M) (c : 𝕜), a < b → 0 < c → c • a < c • b := by
    refine' fun a b c hab hc => (h hab hc).lt_of_ne _
    rw [Ne.def, hc.ne'.isUnit.smul_left_cancel]
    exact hab.ne
  refine' { smul_lt_smul_of_pos := fun {a b c} => hlt' a b c..}
  intro a b c hab hc
  obtain ⟨c, rfl⟩ := hc.ne'.isUnit
  rw [← inv_smul_smul c a, ← inv_smul_smul c b]
  refine' hlt' _ _ _ hab (pos_of_mul_pos_right _ hc.le)
  simp only [c.mul_inv, zero_lt_one]
#align ordered_smul.mk' OrderedSMul.mk'

instance [OrderedSMul 𝕜 M] [OrderedSMul 𝕜 N] : OrderedSMul 𝕜 (M × N) :=
  OrderedSMul.mk' fun _ _ _ h hc =>
    ⟨smul_le_smul_of_nonneg h.1.1 hc.le, smul_le_smul_of_nonneg h.1.2 hc.le⟩

instance Pi.orderedSMul {M : ι → Type*} [∀ i, OrderedAddCommMonoid (M i)]
    [∀ i, MulActionWithZero 𝕜 (M i)] [∀ i, OrderedSMul 𝕜 (M i)] : OrderedSMul 𝕜 (∀ i, M i) :=
  OrderedSMul.mk' fun _ _ _ h hc i => smul_le_smul_of_nonneg (h.le i) hc.le
#align pi.ordered_smul Pi.orderedSMul

/- Sometimes Lean fails to apply the dependent version to non-dependent functions, so we define
another instance. -/
instance Pi.orderedSMul' [OrderedSMul 𝕜 M] : OrderedSMul 𝕜 (ι → M) :=
  Pi.orderedSMul
#align pi.ordered_smul' Pi.orderedSMul'

-- Sometimes Lean fails to unify the module with the scalars, so we define another instance.
instance Pi.orderedSMul'' : OrderedSMul 𝕜 (ι → 𝕜) :=
  @Pi.orderedSMul' ι 𝕜 𝕜 _ _ _ _
#align pi.ordered_smul'' Pi.orderedSMul''

variable [OrderedSMul 𝕜 M] {s : Set M} {a b : M} {c : 𝕜}

theorem smul_le_smul_iff_of_pos (hc : 0 < c) : c • a ≤ c • b ↔ a ≤ b :=
  smul_le_smul_iff_of_pos_left hc
#align smul_le_smul_iff_of_pos smul_le_smul_iff_of_pos

theorem inv_smul_le_iff (h : 0 < c) : c⁻¹ • a ≤ b ↔ a ≤ c • b := inv_smul_le_iff_of_pos h
#align inv_smul_le_iff inv_smul_le_iff

theorem inv_smul_lt_iff (h : 0 < c) : c⁻¹ • a < b ↔ a < c • b := inv_smul_lt_iff_of_pos h
#align inv_smul_lt_iff inv_smul_lt_iff

theorem le_inv_smul_iff (h : 0 < c) : a ≤ c⁻¹ • b ↔ c • a ≤ b := le_inv_smul_iff_of_pos h
#align le_inv_smul_iff le_inv_smul_iff

theorem lt_inv_smul_iff (h : 0 < c) : a < c⁻¹ • b ↔ c • a < b := lt_inv_smul_iff_of_pos h
#align lt_inv_smul_iff lt_inv_smul_iff

variable (M)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps]
def OrderIso.smulLeft (hc : 0 < c) : M ≃o M where
  toFun b := c • b
  invFun b := c⁻¹ • b
  left_inv := inv_smul_smul₀ hc.ne'
  right_inv := smul_inv_smul₀ hc.ne'
  map_rel_iff' := smul_le_smul_iff_of_pos hc
#align order_iso.smul_left OrderIso.smulLeft
#align order_iso.smul_left_symm_apply OrderIso.smulLeft_symm_apply
#align order_iso.smul_left_apply OrderIso.smulLeft_apply

variable {M}

@[simp]
theorem lowerBounds_smul_of_pos (hc : 0 < c) : lowerBounds (c • s) = c • lowerBounds s :=
  (OrderIso.smulLeft _ hc).lowerBounds_image
#align lower_bounds_smul_of_pos lowerBounds_smul_of_pos

@[simp]
theorem upperBounds_smul_of_pos (hc : 0 < c) : upperBounds (c • s) = c • upperBounds s :=
  (OrderIso.smulLeft _ hc).upperBounds_image
#align upper_bounds_smul_of_pos upperBounds_smul_of_pos

@[simp]
theorem bddBelow_smul_iff_of_pos (hc : 0 < c) : BddBelow (c • s) ↔ BddBelow s :=
  (OrderIso.smulLeft _ hc).bddBelow_image
#align bdd_below_smul_iff_of_pos bddBelow_smul_iff_of_pos

@[simp]
theorem bddAbove_smul_iff_of_pos (hc : 0 < c) : BddAbove (c • s) ↔ BddAbove s :=
  (OrderIso.smulLeft _ hc).bddAbove_image
#align bdd_above_smul_iff_of_pos bddAbove_smul_iff_of_pos

end LinearOrderedSemifield

namespace Mathlib.Meta.Positivity

section OrderedSMul

variable [OrderedSemiring R] [OrderedAddCommMonoid M] [SMulWithZero R M] [OrderedSMul R M] {a : R}
  {b : M}

private theorem smul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b :=
  smul_nonneg ha.le hb

private theorem smul_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b :=
  smul_nonneg ha hb.le

end OrderedSMul

section NoZeroSMulDivisors

variable [Zero R] [Zero M] [SMul R M] [NoZeroSMulDivisors R M] {a : R} {b : M}

private theorem smul_ne_zero_of_pos_of_ne_zero [Preorder R] (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 :=
  smul_ne_zero ha.ne' hb

private theorem smul_ne_zero_of_ne_zero_of_pos [Preorder M] (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 :=
  smul_ne_zero ha hb.ne'

end NoZeroSMulDivisors

open Lean.Meta Qq

/-- Positivity extension for HSMul, i.e. (_ • _).  -/
@[positivity HSMul.hSMul _ _]
def evalHSMul : PositivityExt where eval {_u α} zα pα (e : Q($α)) := do
  let .app (.app (.app (.app (.app (.app
        (.const ``HSMul.hSMul [u1, _, _]) (M : Q(Type u1))) _) _) _)
          (a : Q($M))) (b : Q($α)) ← whnfR e | throwError "failed to match hSMul"
  let zM : Q(Zero $M) ← synthInstanceQ (q(Zero $M))
  let pM : Q(PartialOrder $M) ← synthInstanceQ (q(PartialOrder $M))
  -- Using `q()` here would be impractical, as we would have to manually `synthInstanceQ` all the
  -- required typeclasses. Ideally we could tell `q()` to do this automatically.
  match ← core zM pM a, ← core zα pα b with
  | .positive pa, .positive pb =>
      pure (.positive (← mkAppM ``smul_pos #[pa, pb]))
  | .positive pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_pos_of_nonneg #[pa, pb]))
  | .nonnegative pa, .positive pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_nonneg_of_pos #[pa, pb]))
  | .nonnegative pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg #[pa, pb]))
  | .positive pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_pos_of_ne_zero #[pa, pb]))
  | .nonzero pa, .positive pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_ne_zero_of_pos #[pa, pb]))
  | .nonzero pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero #[pa, pb]))
  | _, _ => pure .none
