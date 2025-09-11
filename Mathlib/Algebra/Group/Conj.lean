/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Conjugacy of group elements

See also `MulAut.conj` and `Quandle.conj`.
-/

assert_not_exists MonoidWithZero Multiset MulAction

universe u v

variable {α : Type u} {β : Type v}

section Monoid

variable [Monoid α] [Monoid β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
def IsConj (a b : α) :=
  ∃ c : αˣ, SemiconjBy (↑c) a b

@[refl]
theorem IsConj.refl (a : α) : IsConj a a :=
  ⟨1, SemiconjBy.one_left a⟩

@[symm]
theorem IsConj.symm {a b : α} : IsConj a b → IsConj b a
  | ⟨c, hc⟩ => ⟨c⁻¹, hc.units_inv_symm_left⟩

theorem isConj_comm {g h : α} : IsConj g h ↔ IsConj h g :=
  ⟨IsConj.symm, IsConj.symm⟩

@[trans]
theorem IsConj.trans {a b c : α} : IsConj a b → IsConj b c → IsConj a c
  | ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩ => ⟨c₂ * c₁, hc₂.mul_left hc₁⟩

theorem IsConj.pow {a b : α} (n : ℕ) : IsConj a b → IsConj (a ^ n) (b ^ n)
  | ⟨c, hc⟩ => ⟨c, hc.pow_right n⟩

@[simp]
theorem isConj_iff_eq {α : Type*} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b :=
  ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy, mul_comm, ← Units.mul_inv_eq_iff_eq_mul, mul_assoc, c.mul_inv, mul_one] at hc
    exact hc, fun h => by rw [h]⟩

protected theorem MonoidHom.map_isConj (f : α →* β) {a b : α} : IsConj a b → IsConj (f a) (f b)
  | ⟨c, hc⟩ => ⟨Units.map f c, by rw [Units.coe_map, SemiconjBy, ← f.map_mul, hc.eq, f.map_mul]⟩

@[simp]
theorem isConj_one_right {a : α} : IsConj 1 a ↔ a = 1 := by
  refine ⟨fun ⟨c, h⟩ => ?_, fun h => by rw [h]⟩
  rw [SemiconjBy, mul_one] at h
  exact c.isUnit.mul_eq_right.mp h.symm

@[simp]
theorem isConj_one_left {a : α} : IsConj a 1 ↔ a = 1 :=
  calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := isConj_one_right

end Monoid

section Group

variable [Group α]

@[simp]
theorem isConj_iff {a b : α} : IsConj a b ↔ ∃ c : α, c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_cancel c, inv_mul_cancel c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
  (map_inv (MulAut.conj b) a).symm

@[simp]
theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
  (map_mul (MulAut.conj b) a c).symm

@[simp]
theorem conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction i with
  | zero => simp
  | succ i hi => simp [pow_succ, hi]

@[simp]
theorem conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  cases i
  · simp
  · simp only [zpow_negSucc, conj_pow, mul_inv_rev, inv_inv]
    rw [mul_assoc]

theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ :=
  (MulAut.conj x).injective

end Group

namespace IsConj

/- This small quotient API is largely copied from the API of `Associates`;
where possible, try to keep them in sync -/
/-- The setoid of the relation `IsConj` iff there is a unit `u` such that `u * x = y * u` -/
protected def setoid (α : Type*) [Monoid α] : Setoid α where
  r := IsConj
  iseqv := ⟨IsConj.refl, IsConj.symm, IsConj.trans⟩

end IsConj

attribute [local instance] IsConj.setoid

/-- The quotient type of conjugacy classes of a group. -/
def ConjClasses (α : Type*) [Monoid α] : Type _ :=
  Quotient (IsConj.setoid α)

namespace ConjClasses

section Monoid

variable [Monoid α] [Monoid β]

/-- The canonical quotient map from a monoid `α` into the `ConjClasses` of `α` -/
protected def mk {α : Type*} [Monoid α] (a : α) : ConjClasses α := ⟦a⟧

instance : Inhabited (ConjClasses α) := ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b :=
  Iff.intro Quotient.exact Quot.sound

theorem quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a :=
  rfl

theorem quot_mk_eq_mk (a : α) : Quot.mk Setoid.r a = ConjClasses.mk a :=
  rfl

theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) :=
  Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) :=
  forall_isConj.2 fun a => ⟨a, rfl⟩

instance : One (ConjClasses α) :=
  ⟨⟦1⟧⟩

theorem one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1 :=
  rfl

theorem exists_rep (a : ConjClasses α) : ∃ a0 : α, ConjClasses.mk a0 = a :=
  Quot.exists_rep a

/-- A `MonoidHom` maps conjugacy classes of one group to conjugacy classes of another. -/
def map (f : α →* β) : ConjClasses α → ConjClasses β :=
  Quotient.lift (ConjClasses.mk ∘ f) fun _ _ ab => mk_eq_mk_iff_isConj.2 (f.map_isConj ab)

theorem map_surjective {f : α →* β} (hf : Function.Surjective f) :
    Function.Surjective (ConjClasses.map f) := by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩

library_note "slow-failing instance priority"/--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
* a class `C` has instances `instT : C T` and `instT' : C T'`
* types `T` and `T'` are both reducible specializations of another type `S`
* the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
  instead they have to be found by instance search
If those conditions hold, the instance `instT` should be assigned lower priority.

Note that there is no issue unless `T` and `T'` are reducibly equal to `S`, Otherwise the instance
discrimination tree can distinguish them, and the note does not apply.

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/

instance [DecidableRel (IsConj : α → α → Prop)] : DecidableEq (ConjClasses α) :=
  inferInstanceAs <| DecidableEq <| Quotient (IsConj.setoid α)

end Monoid

section CommMonoid

variable [CommMonoid α]

theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (mk_eq_mk_iff_isConj.trans isConj_iff_eq).1

theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) :=
  ⟨mk_injective, mk_surjective⟩

/-- The bijection between a `CommGroup` and its `ConjClasses`. -/
def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotient.lift id fun (_ : α) _ => isConj_iff_eq.1, Quotient.lift_mk _ _, by
    rw [Function.RightInverse, Function.LeftInverse, forall_isConj]
    solve_by_elim⟩

end CommMonoid

end ConjClasses

section Monoid

variable [Monoid α]

/-- Given an element `a`, `conjugatesOf a` is the set of conjugates. -/
def conjugatesOf (a : α) : Set α :=
  { b | IsConj a b }

theorem mem_conjugatesOf_self {a : α} : a ∈ conjugatesOf a :=
  IsConj.refl _

theorem IsConj.conjugatesOf_eq {a b : α} (ab : IsConj a b) : conjugatesOf a = conjugatesOf b :=
  Set.ext fun _ => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

theorem isConj_iff_conjugatesOf_eq {a b : α} : IsConj a b ↔ conjugatesOf a = conjugatesOf b :=
  ⟨IsConj.conjugatesOf_eq, fun h => by
    have ha := mem_conjugatesOf_self (a := b)
    rwa [← h] at ha⟩

end Monoid

namespace ConjClasses

variable [Monoid α]

attribute [local instance] IsConj.setoid

/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
def carrier : ConjClasses α → Set α :=
  Quotient.lift conjugatesOf fun (_ : α) _ ab => IsConj.conjugatesOf_eq ab

theorem mem_carrier_mk {a : α} : a ∈ carrier (ConjClasses.mk a) :=
  IsConj.refl _

theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} :
    a ∈ carrier b ↔ ConjClasses.mk a = b := by
  revert b
  rw [forall_isConj]
  intro b
  rw [carrier, eq_comm, mk_eq_mk_iff_isConj, ← quotient_mk_eq_mk, Quotient.lift_mk]
  rfl

theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.carrier = ConjClasses.mk ⁻¹' {a} :=
  Set.ext fun _ => mem_carrier_iff_mk_eq

end ConjClasses
