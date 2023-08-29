/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import Mathlib.Algebra.Group.Semiconj
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Hom.Aut
import Mathlib.Algebra.Hom.Group

#align_import algebra.group.conj from "leanprover-community/mathlib"@"0743cc5d9d86bcd1bba10f480e948a257d65056f"

/-!
# Conjugacy of group elements

See also `MulAut.conj` and `Quandle.conj`.
-/

universe u v

variable {α : Type u} {β : Type v}

section Monoid

variable [Monoid α] [Monoid β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
def IsConj (a b : α) :=
  ∃ c : αˣ, SemiconjBy (↑c) a b
#align is_conj IsConj

@[refl]
theorem IsConj.refl (a : α) : IsConj a a :=
  ⟨1, SemiconjBy.one_left a⟩
#align is_conj.refl IsConj.refl

@[symm]
theorem IsConj.symm {a b : α} : IsConj a b → IsConj b a
  | ⟨c, hc⟩ => ⟨c⁻¹, hc.units_inv_symm_left⟩
#align is_conj.symm IsConj.symm

theorem isConj_comm {g h : α} : IsConj g h ↔ IsConj h g :=
  ⟨IsConj.symm, IsConj.symm⟩
#align is_conj_comm isConj_comm

@[trans]
theorem IsConj.trans {a b c : α} : IsConj a b → IsConj b c → IsConj a c
  | ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩ => ⟨c₂ * c₁, hc₂.mul_left hc₁⟩
#align is_conj.trans IsConj.trans

@[simp]
theorem isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b :=
  ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy, mul_comm, ← Units.mul_inv_eq_iff_eq_mul, mul_assoc, c.mul_inv, mul_one] at hc
    -- ⊢ a = b
    exact hc, fun h => by rw [h]⟩
    -- 🎉 no goals
                          -- 🎉 no goals
#align is_conj_iff_eq isConj_iff_eq

protected theorem MonoidHom.map_isConj (f : α →* β) {a b : α} : IsConj a b → IsConj (f a) (f b)
  | ⟨c, hc⟩ => ⟨Units.map f c, by rw [Units.coe_map, SemiconjBy, ← f.map_mul, hc.eq, f.map_mul]⟩
                                  -- 🎉 no goals
#align monoid_hom.map_is_conj MonoidHom.map_isConj

end Monoid

section CancelMonoid

variable [CancelMonoid α]

-- These lemmas hold for `RightCancelMonoid` with the current proofs, but for the sake of
-- not duplicating code (these lemmas also hold for `LeftCancelMonoids`) we leave these
-- not generalised.
@[simp]
theorem isConj_one_right {a : α} : IsConj 1 a ↔ a = 1 :=
  ⟨fun ⟨c, hc⟩ => mul_right_cancel (hc.symm.trans ((mul_one _).trans (one_mul _).symm)), fun h => by
    rw [h]⟩
    -- 🎉 no goals
#align is_conj_one_right isConj_one_right

@[simp]
theorem isConj_one_left {a : α} : IsConj a 1 ↔ a = 1 :=
  calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right
#align is_conj_one_left isConj_one_left

end CancelMonoid

section Group

variable [Group α]

@[simp]
theorem isConj_iff {a b : α} : IsConj a b ↔ ∃ c : α, c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_self c, inv_mul_self c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩
#align is_conj_iff isConj_iff

-- Porting note: not in simp NF.
-- @[simp]
theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
  ((MulAut.conj b).map_inv a).symm
#align conj_inv conj_inv

@[simp]
theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
  ((MulAut.conj b).map_mul a c).symm
#align conj_mul conj_mul

@[simp]
theorem conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction' i with i hi
  -- ⊢ (a * b * a⁻¹) ^ Nat.zero = a * b ^ Nat.zero * a⁻¹
  · simp
    -- 🎉 no goals
  · simp [pow_succ, hi]
    -- 🎉 no goals
#align conj_pow conj_pow

@[simp]
theorem conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction' i
  -- ⊢ (a * b * a⁻¹) ^ Int.ofNat a✝ = a * b ^ Int.ofNat a✝ * a⁻¹
  · change (a * b * a⁻¹) ^ (_ : ℤ) = a * b ^ (_ : ℤ) * a⁻¹
    -- ⊢ (a * b * a⁻¹) ^ Int.ofNat a✝ = a * b ^ Int.ofNat a✝ * a⁻¹
    simp [zpow_ofNat]
    -- 🎉 no goals
  · simp [zpow_negSucc, conj_pow]
    -- ⊢ a * ((b ^ (a✝ + 1))⁻¹ * a⁻¹) = a * (b ^ (a✝ + 1))⁻¹ * a⁻¹
    rw [mul_assoc]
    -- 🎉 no goals
-- Porting note: Added `change`, `zpow_ofNat`, and `rw`.
#align conj_zpow conj_zpow

theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ :=
  (MulAut.conj x).injective
#align conj_injective conj_injective

end Group

@[simp]
theorem isConj_iff₀ [GroupWithZero α] {a b : α} : IsConj a b ↔ ∃ c : α, c ≠ 0 ∧ c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ =>
    ⟨c, by
      rw [← Units.val_inv_eq_inv_val, Units.mul_inv_eq_iff_eq_mul]
      -- ⊢ ↑c ≠ 0 ∧ ↑c * a = b * ↑c
      exact ⟨c.ne_zero, hc⟩⟩,
      -- 🎉 no goals
    fun ⟨c, c0, hc⟩ =>
    ⟨Units.mk0 c c0, by
      rw [SemiconjBy, ← Units.mul_inv_eq_iff_eq_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
      -- ⊢ c * a * c⁻¹ = b
      exact hc⟩⟩
      -- 🎉 no goals
#align is_conj_iff₀ isConj_iff₀

namespace IsConj

/- This small quotient API is largely copied from the API of `Associates`;
where possible, try to keep them in sync -/
/-- The setoid of the relation `IsConj` iff there is a unit `u` such that `u * x = y * u` -/
protected def setoid (α : Type*) [Monoid α] : Setoid α where
  r := IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩
#align is_conj.setoid IsConj.setoid

end IsConj

attribute [local instance] IsConj.setoid

/-- The quotient type of conjugacy classes of a group. -/
def ConjClasses (α : Type*) [Monoid α] : Type _ :=
  Quotient (IsConj.setoid α)
#align conj_classes ConjClasses

namespace ConjClasses

section Monoid

variable [Monoid α] [Monoid β]

/-- The canonical quotient map from a monoid `α` into the `ConjClasses` of `α` -/
protected def mk {α : Type*} [Monoid α] (a : α) : ConjClasses α := ⟦a⟧
#align conj_classes.mk ConjClasses.mk

instance : Inhabited (ConjClasses α) := ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b :=
  Iff.intro Quotient.exact Quot.sound
#align conj_classes.mk_eq_mk_iff_is_conj ConjClasses.mk_eq_mk_iff_isConj

theorem quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a :=
  rfl
#align conj_classes.quotient_mk_eq_mk ConjClasses.quotient_mk_eq_mk

theorem quot_mk_eq_mk (a : α) : Quot.mk Setoid.r a = ConjClasses.mk a :=
  rfl
#align conj_classes.quot_mk_eq_mk ConjClasses.quot_mk_eq_mk

theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) :=
  Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h
#align conj_classes.forall_is_conj ConjClasses.forall_isConj

theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) :=
  forall_isConj.2 fun a => ⟨a, rfl⟩
#align conj_classes.mk_surjective ConjClasses.mk_surjective

instance : One (ConjClasses α) :=
  ⟨⟦1⟧⟩

theorem one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1 :=
  rfl
#align conj_classes.one_eq_mk_one ConjClasses.one_eq_mk_one

theorem exists_rep (a : ConjClasses α) : ∃ a0 : α, ConjClasses.mk a0 = a :=
  Quot.exists_rep a
#align conj_classes.exists_rep ConjClasses.exists_rep

/-- A `MonoidHom` maps conjugacy classes of one group to conjugacy classes of another. -/
def map (f : α →* β) : ConjClasses α → ConjClasses β :=
  Quotient.lift (ConjClasses.mk ∘ f) fun _ _ ab => mk_eq_mk_iff_isConj.2 (f.map_isConj ab)
#align conj_classes.map ConjClasses.map

theorem map_surjective {f : α →* β} (hf : Function.Surjective f) :
    Function.Surjective (ConjClasses.map f) := by
  intro b
  -- ⊢ ∃ a, map f a = b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  -- ⊢ ∃ a, map f a = ConjClasses.mk b
  obtain ⟨a, rfl⟩ := hf b
  -- ⊢ ∃ a_1, map f a_1 = ConjClasses.mk (↑f a)
  exact ⟨ConjClasses.mk a, rfl⟩
  -- 🎉 no goals
#align conj_classes.map_surjective ConjClasses.map_surjective

-- Porting note: This has not been adapted to mathlib4, is it still accurate?
library_note "slow-failing instance priority"/--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
 * a class `C` has instances `instT : C T` and `instT' : C T'`
 * types `T` and `T'` are both specializations of another type `S`
 * the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
   instead they have to be found by instance search
If those conditions hold, the instance `instT` should be assigned lower priority.

For example, suppose the search for an instance of `DecidableEq (Multiset α)` tries the
candidate instance `Con.quotient.decidableEq (c : Con M) : decidableEq c.quotient`.
Since `Multiset` and `Con.quotient` are both quotient types, unification will check
that the relations `List.perm` and `c.toSetoid.r` unify. However, `c.toSetoid` depends on
a `Mul M` instance, so this unification triggers a search for `Mul (List α)`;
this will traverse all subclasses of `Mul` before failing.
On the other hand, the search for an instance of `DecidableEq (Con.quotient c)` for `c : Con M`
can quickly reject the candidate instance `Multiset.decidableEq` because the type of
`List.perm : List ?m_1 → List ?m_1 → Prop` does not unify with `M → M → Prop`.
Therefore, we should assign `Con.quotient.decidableEq` a lower priority because it fails slowly.
(In terms of the rules above, `C := DecidableEq`, `T := Con.quotient`,
`instT := Con.quotient.decidableEq`, `T' := Multiset`, `instT' := Multiset.decidableEq`,
and `S := Quot`.)

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/

-- see Note [slow-failing instance priority]
instance (priority := 900) [DecidableRel (IsConj : α → α → Prop)] : DecidableEq (ConjClasses α) :=
  instDecidableEqQuotient

end Monoid

section CommMonoid

variable [CommMonoid α]

theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (mk_eq_mk_iff_isConj.trans isConj_iff_eq).1
#align conj_classes.mk_injective ConjClasses.mk_injective

theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) :=
  ⟨mk_injective, mk_surjective⟩
#align conj_classes.mk_bijective ConjClasses.mk_bijective

/-- The bijection between a `CommGroup` and its `ConjClasses`. -/
def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotient.lift id fun (a : α) b => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    rw [Function.RightInverse, Function.LeftInverse, forall_isConj]
    -- ⊢ ∀ (a : α), ConjClasses.mk (Quotient.lift id (_ : ∀ (a b : α), IsConj a b → a …
    intro x
    -- ⊢ ConjClasses.mk (Quotient.lift id (_ : ∀ (a b : α), IsConj a b → a = b) (Conj …
    rw [← quotient_mk_eq_mk, ← quotient_mk_eq_mk, Quotient.lift_mk, id.def]⟩
    -- 🎉 no goals
#align conj_classes.mk_equiv ConjClasses.mkEquiv

end CommMonoid

end ConjClasses

section Monoid

variable [Monoid α]

/-- Given an element `a`, `conjugatesOf a` is the set of conjugates. -/
def conjugatesOf (a : α) : Set α :=
  { b | IsConj a b }
#align conjugates_of conjugatesOf

theorem mem_conjugatesOf_self {a : α} : a ∈ conjugatesOf a :=
  IsConj.refl _
#align mem_conjugates_of_self mem_conjugatesOf_self

theorem IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b :=
  Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩
#align is_conj.conjugates_of_eq IsConj.conjugatesOf_eq

theorem isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conjugatesOf b :=
  ⟨IsConj.conjugatesOf_eq, fun h => by
    have ha := @mem_conjugatesOf_self _ _ b -- Porting note: added `@`.
    -- ⊢ IsConj a b
    rwa [← h] at ha⟩
    -- 🎉 no goals
#align is_conj_iff_conjugates_of_eq isConj_iff_conjugatesOf_eq

end Monoid

namespace ConjClasses

variable [Monoid α]

attribute [local instance] IsConj.setoid

/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
def carrier : ConjClasses α → Set α :=
  Quotient.lift conjugatesOf fun (_ : α) _ ab => IsConj.conjugatesOf_eq ab
#align conj_classes.carrier ConjClasses.carrier

theorem mem_carrier_mk {a : α} : a ∈ carrier (ConjClasses.mk a) :=
  IsConj.refl _
#align conj_classes.mem_carrier_mk ConjClasses.mem_carrier_mk

theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a ∈ carrier b ↔ ConjClasses.mk a = b := by
  revert b
  -- ⊢ ∀ {b : ConjClasses α}, a ∈ carrier b ↔ ConjClasses.mk a = b
  rw [forall_isConj]
  -- ⊢ ∀ (a_1 : α), a ∈ carrier (ConjClasses.mk a_1) ↔ ConjClasses.mk a = ConjClass …
  intro b
  -- ⊢ a ∈ carrier (ConjClasses.mk b) ↔ ConjClasses.mk a = ConjClasses.mk b
  rw [carrier, eq_comm, mk_eq_mk_iff_isConj, ← quotient_mk_eq_mk, Quotient.lift_mk]
  -- ⊢ a ∈ conjugatesOf b ↔ IsConj b a
  rfl
  -- 🎉 no goals
#align conj_classes.mem_carrier_iff_mk_eq ConjClasses.mem_carrier_iff_mk_eq

theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} :=
  Set.ext fun _ => mem_carrier_iff_mk_eq
#align conj_classes.carrier_eq_preimage_mk ConjClasses.carrier_eq_preimage_mk

end ConjClasses

assert_not_exists Multiset
