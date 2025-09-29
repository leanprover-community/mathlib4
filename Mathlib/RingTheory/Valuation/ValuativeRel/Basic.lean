/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Adam Topaz
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.Defs.Filter

/-!

# Valuative Relations

In this file we introduce a class called `ValuativeRel R` for a ring `R`.
This bundles a relation `rel : R → R → Prop` on `R` which mimics a
preorder on `R` arising from a valuation.
We introduce the notation `x ≤ᵥ y` for this relation.

Recall that the equivalence class of a valuation is *completely* characterized by
such a preorder. Thus, we can think of `ValuativeRel R` as a way of
saying that `R` is endowed with an equivalence class of valuations.

## Main Definitions

- `ValuativeRel R` endows a commutative ring `R` with a relation arising from a valuation.
  This is equivalent to fixing an equivalence class of valuations on `R`.
  Use the notation `x ≤ᵥ y` for this relation.
- `ValuativeRel.valuation R` is the "canonical" valuation associated to `ValuativeRel R`,
  taking values in `ValuativeRel.ValueGroupWithZero R`.
- Given a valuation `v` on `R` and an instance `[ValuativeRel R]`, writing `[v.Compatible]`
  ensures that the relation `x ≤ᵥ y` is equivalent to `v x ≤ v y`. Note that
  it is possible to have `[v.Compatible]` and `[w.Compatible]` for two different valuations on `R`.
- If we have both `[ValuativeRel R]` and `[TopologicalSpace R]`, then writing
  `[IsValuativeTopology R]` ensures that the topology on `R` agrees with the one induced by the
  valuation.
- Given `[ValuativeRel A]`, `[ValuativeRel B]` and `[Algebra A B]`, the class
  `[ValuativeExtension A B]` ensures that the algebra map `A → B` is compatible with the valuations
  on `A` and `B`. For example, this can be used to talk about extensions of valued fields.


## Remark

The last two axioms in `ValuativeRel`, namely `rel_mul_cancel` and `not_rel_one_zero`, are
used to ensure that we have a well-behaved valuation taking values in a *value group* (with zero).
In principle, it should be possible to drop these two axioms and obtain a value monoid,
however, such a value monoid would not necessarily embed into an ordered abelian group with zero.
Similarly, without these axioms, the support of the valuation need not be a prime ideal.
We have thus opted to include these two axioms and obtain a `ValueGroupWithZero` associated to
a `ValuativeRel` in order to best align with the literature about valuations on commutative rings.

Future work could refactor `ValuativeRel` by dropping the `rel_mul_cancel` and `not_rel_one_zero`
axioms, opting to make these mixins instead.

## Projects

The `ValuativeRel` class should eventually replace the existing `Valued` typeclass.
Once such a refactor happens, `ValuativeRel` could be renamed to `Valued`.

-/

noncomputable section

/-- The class `[ValuativeRel R]` class introduces an operator `x ≤ᵥ y : Prop` for `x y : R`
which is the natural relation arising from (the equivalence class of) a valuation on `R`.
More precisely, if v is a valuation on R then the associated relation is `x ≤ᵥ y ↔ v x ≤ v y`.
Use this class to talk about the case where `R` is equipped with an equivalence class
of valuations. -/
@[ext]
class ValuativeRel (R : Type*) [CommRing R] where
  /-- The relation operator arising from `ValuativeRel`. -/
  rel : R → R → Prop
  rel_total (x y) : rel x y ∨ rel y x
  rel_trans {z y x} : rel x y → rel y z → rel x z
  rel_add {x y z} : rel x z → rel y z → rel (x + y) z
  rel_mul_right {x y} (z) : rel x y → rel (x * z) (y * z)
  rel_mul_cancel {x y z} : ¬ rel z 0 → rel (x * z) (y * z) → rel x y
  not_rel_one_zero : ¬ rel 1 0

@[inherit_doc] infix:50 " ≤ᵥ " => ValuativeRel.rel

macro_rules | `($a ≤ᵥ $b) => `(binrel% ValuativeRel.rel $a $b)

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ≤ᵥ y`
is equivalent to `v x ≤ x y`. -/
class Compatible [ValuativeRel R] where
  rel_iff_le (x y : R) : x ≤ᵥ y ↔ v x ≤ v y

end Valuation

/-- A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation. -/
class ValuativePreorder (R : Type*) [CommRing R] [ValuativeRel R] [Preorder R] where
  rel_iff_le (x y : R) : x ≤ᵥ y ↔ x ≤ y

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

@[simp]
lemma rel_refl (x : R) : x ≤ᵥ x := by
  cases rel_total x x <;> assumption

lemma rel_rfl {x : R} : x ≤ᵥ x :=
  rel_refl x

protected alias rel.refl := rel_refl

protected alias rel.rfl := rel_rfl

@[simp]
theorem zero_rel (x : R) : 0 ≤ᵥ x := by
  simpa using rel_mul_right x ((rel_total 0 1).resolve_right not_rel_one_zero)

lemma rel_mul_left {x y : R} (z) : x ≤ᵥ y → (z * x) ≤ᵥ (z * y) := by
  rw [mul_comm z x, mul_comm z y]
  apply rel_mul_right

instance : Trans (rel (R := R)) (rel (R := R)) (rel (R := R)) where
  trans h1 h2 := rel_trans h1 h2

protected alias rel.trans := rel_trans

lemma rel_trans' {x y z : R} (h1 : y ≤ᵥ z) (h2 : x ≤ᵥ y) : x ≤ᵥ z :=
  h2.trans h1

protected alias rel.trans' := rel_trans'

lemma rel_mul {x x' y y' : R} (h1 : x ≤ᵥ y) (h2 : x' ≤ᵥ y') : (x * x') ≤ᵥ y * y' := by
  calc x * x' ≤ᵥ x * y' := rel_mul_left _ h2
    _ ≤ᵥ y * y' := rel_mul_right _ h1

theorem rel_add_cases (x y : R) : x + y ≤ᵥ x ∨ x + y ≤ᵥ y :=
  (rel_total y x).imp (fun h => rel_add .rfl h) (fun h => rel_add h .rfl)

variable (R) in
/-- The submonoid of elements `x : R` whose valuation is positive. -/
def posSubmonoid : Submonoid R where
  carrier := { x | ¬ x ≤ᵥ 0}
  mul_mem' {x y} hx hy := by
    dsimp only [Set.mem_setOf_eq] at hx hy ⊢
    contrapose! hy
    rw [show (0 : R) = x * 0 by simp, mul_comm x y, mul_comm x 0] at hy
    exact rel_mul_cancel hx hy
  one_mem' := not_rel_one_zero

@[simp]
lemma posSubmonoid_def (x : R) : x ∈ posSubmonoid R ↔ ¬ x ≤ᵥ 0 := Iff.refl _

@[simp]
lemma right_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    x * u ≤ᵥ y * u ↔ x ≤ᵥ y := ⟨rel_mul_cancel u.prop, rel_mul_right _⟩

@[simp]
lemma left_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    u * x ≤ᵥ u * y ↔ x ≤ᵥ y := by
  simp only [← right_cancel_posSubmonoid x y u, mul_comm]

@[simp]
lemma val_posSubmonoid_ne_zero (x : posSubmonoid R) :
    (x : R) ≠ 0 := by
  have := x.prop
  rw [posSubmonoid_def] at this
  contrapose! this
  simp [this]

variable (R) in
/-- The setoid used to construct `ValueGroupWithZero R`. -/
def valueSetoid : Setoid (R × posSubmonoid R) where
  r := fun (x, s) (y, t) => x * t ≤ᵥ y * s ∧ y * s ≤ᵥ x * t
  iseqv := {
    refl ru := ⟨rel_refl _, rel_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := rel_mul h1 (rel_refl ↑w)
        rw [mul_right_comm s] at this
        have := rel_trans this (rel_mul h3 (rel_refl _))
        rw [mul_right_comm r, mul_right_comm t] at this
        simpa using this
      · have := rel_mul h4 (rel_refl ↑u)
        rw [mul_right_comm s] at this
        have := rel_trans this (rel_mul h2 (rel_refl _))
        rw [mul_right_comm t, mul_right_comm r] at this
        simpa using this
  }

variable (R) in
/-- The "canonical" value group-with-zero of a ring with a valuative relation. -/
def ValueGroupWithZero := Quotient (valueSetoid R)

/-- Construct an element of the value group-with-zero from an element `r : R` and
  `y : posSubmonoid R`. This should be thought of as `v r / v y`. -/
protected
def ValueGroupWithZero.mk (x : R) (y : posSubmonoid R) : ValueGroupWithZero R :=
  Quotient.mk _ (x, y)

protected
theorem ValueGroupWithZero.sound {x y : R} {t s : posSubmonoid R}
    (h₁ : x * s ≤ᵥ y * t) (h₂ : y * t ≤ᵥ x * s) :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s :=
  Quotient.sound ⟨h₁, h₂⟩

protected
theorem ValueGroupWithZero.exact {x y : R} {t s : posSubmonoid R}
    (h : ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s) :
    x * s ≤ᵥ y * t ∧ y * t ≤ᵥ x * s :=
  Quotient.exact h

protected
theorem ValueGroupWithZero.ind {motive : ValueGroupWithZero R → Prop} (mk : ∀ x y, motive (.mk x y))
    (t : ValueGroupWithZero R) : motive t :=
  Quotient.ind (fun (x, y) => mk x y) t

/-- Lifts a function `R → posSubmonoid R → α` to the value group-with-zero of `R`. -/
protected
def ValueGroupWithZero.lift {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (t : ValueGroupWithZero R) : α :=
  Quotient.lift (fun (x, y) => f x y) (fun (x, t) (y, s) ⟨h₁, h₂⟩ => hf x y s t h₁ h₂) t

@[simp] protected
theorem ValueGroupWithZero.lift_mk {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (x : R) (y : posSubmonoid R) : ValueGroupWithZero.lift f hf (.mk x y) = f x y := rfl

/-- Lifts a function `R → posSubmonoid R → R → posSubmonoid R → α` to
  the value group-with-zero of `R`. -/
protected
def ValueGroupWithZero.lift₂ {α : Sort*} (f : R → posSubmonoid R → R → posSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : posSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (t₁ : ValueGroupWithZero R) (t₂ : ValueGroupWithZero R) : α :=
  Quotient.lift₂ (fun (x, t) (y, s) => f x t y s)
    (fun (x, t) (z, v) (y, s) (w, u) ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => hf x y z w s t u v h₁ h₂ h₃ h₄) t₁ t₂

@[simp] protected
lemma ValueGroupWithZero.lift₂_mk {α : Sort*} (f : R → posSubmonoid R → R → posSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : posSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (x y : R) (z w : posSubmonoid R) :
    ValueGroupWithZero.lift₂ f hf (.mk x z) (.mk y w) = f x z y w := rfl

theorem ValueGroupWithZero.mk_eq_mk {x y : R} {t s : posSubmonoid R} :
    ValueGroupWithZero.mk x t = ValueGroupWithZero.mk y s ↔ x * s ≤ᵥ y * t ∧ y * t ≤ᵥ x * s :=
  Quotient.eq

instance : Zero (ValueGroupWithZero R) where
  zero := .mk 0 1

@[simp]
theorem ValueGroupWithZero.mk_eq_zero (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 0 ↔ x ≤ᵥ 0 :=
  ⟨fun h => by simpa using ValueGroupWithZero.mk_eq_mk.mp h,
    fun h => ValueGroupWithZero.sound (by simpa using h) (by simp)⟩

@[simp]
theorem ValueGroupWithZero.mk_zero (x : posSubmonoid R) : ValueGroupWithZero.mk 0 x = 0 :=
  (ValueGroupWithZero.mk_eq_zero 0 x).mpr .rfl

instance : One (ValueGroupWithZero R) where
  one := .mk 1 1

@[simp]
theorem ValueGroupWithZero.mk_self (x : posSubmonoid R) : ValueGroupWithZero.mk (x : R) x = 1 :=
  ValueGroupWithZero.sound (by simp) (by simp)

@[simp]
theorem ValueGroupWithZero.mk_one_one : ValueGroupWithZero.mk (1 : R) 1 = 1 :=
  ValueGroupWithZero.sound (by simp) (by simp)

@[simp]
theorem ValueGroupWithZero.mk_eq_one (x : R) (y : posSubmonoid R) :
    ValueGroupWithZero.mk x y = 1 ↔ x ≤ᵥ y ∧ y ≤ᵥ x := by
  simp [← mk_one_one, mk_eq_mk]

theorem ValueGroupWithZero.lift_zero {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t) :
    ValueGroupWithZero.lift f hf 0 = f 0 1 :=
  rfl

@[simp]
theorem ValueGroupWithZero.lift_one {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t) :
    ValueGroupWithZero.lift f hf 1 = f 1 1 :=
  rfl

instance : Mul (ValueGroupWithZero R) where
  mul := ValueGroupWithZero.lift₂ (fun a b c d => .mk (a * c) (b * d)) <| by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    apply ValueGroupWithZero.sound
    · rw [Submonoid.coe_mul, Submonoid.coe_mul,
        mul_mul_mul_comm x, mul_mul_mul_comm y]
      exact rel_mul h₁ h₃
    · rw [Submonoid.coe_mul, Submonoid.coe_mul,
        mul_mul_mul_comm x, mul_mul_mul_comm y]
      exact rel_mul h₂ h₄

@[simp]
theorem ValueGroupWithZero.mk_mul_mk (a b : R) (c d : posSubmonoid R) :
    ValueGroupWithZero.mk a c * ValueGroupWithZero.mk b d = ValueGroupWithZero.mk (a * b) (c * d) :=
  rfl

theorem ValueGroupWithZero.lift_mul {α : Type*} [Mul α] (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (hdist : ∀ (a b r s), f (a * b) (r * s) = f a r * f b s)
    (a b : ValueGroupWithZero R) :
    ValueGroupWithZero.lift f hf (a * b) =
      ValueGroupWithZero.lift f hf a * ValueGroupWithZero.lift f hf b := by
  induction a using ValueGroupWithZero.ind
  induction b using ValueGroupWithZero.ind
  simpa using hdist _ _ _ _

instance : CommMonoidWithZero (ValueGroupWithZero R) where
  mul_assoc a b c := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp [mul_assoc]
  one_mul := ValueGroupWithZero.ind <| by simp [← ValueGroupWithZero.mk_one_one]
  mul_one := ValueGroupWithZero.ind <| by simp [← ValueGroupWithZero.mk_one_one]
  zero_mul := ValueGroupWithZero.ind <| fun _ _ => by
    rw [← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_mul_mk]
    simp
  mul_zero := ValueGroupWithZero.ind <| fun _ _ => by
    rw [← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_mul_mk]
    simp
  mul_comm a b := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    simp [mul_comm]
  npow n := ValueGroupWithZero.lift (fun a b => ValueGroupWithZero.mk (a ^ n) (b ^ n)) <| by
    intro x y t s h₁ h₂
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ, ← ValueGroupWithZero.mk_mul_mk, ih]
      apply congrArg (_ * ·)
      exact ValueGroupWithZero.sound h₁ h₂
  npow_zero := ValueGroupWithZero.ind (by simp)
  npow_succ n := ValueGroupWithZero.ind (by simp [pow_succ])

instance : LE (ValueGroupWithZero R) where
  le := ValueGroupWithZero.lift₂ (fun a s b t => a * t ≤ᵥ b * s) <| by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    by_cases hw : w ≤ᵥ 0 <;> by_cases hz : z ≤ᵥ 0
    · refine propext ⟨fun h => rel_trans ?_ (zero_rel _), fun h => rel_trans ?_ (zero_rel _)⟩
      · apply rel_mul_cancel (s * v).prop
        rw [mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply rel_trans (rel_mul_right (u : R) (rel_mul_right (v : R) h₂))
        rw [mul_right_comm x]
        apply rel_trans (rel_mul_right (u : R) (rel_mul_right (t : R) h))
        apply rel_trans (rel_mul_right (u : R) (rel_mul_right (t : R) (rel_mul_right (s : R) hz)))
        simp
      · apply rel_mul_cancel (t * u).prop
        rw [mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply rel_trans (rel_mul_right (v : R) (rel_mul_right (u : R) h₁))
        rw [mul_right_comm y]
        apply rel_trans (rel_mul_right (v : R) (rel_mul_right (s : R) h))
        apply rel_trans (rel_mul_right (v : R) (rel_mul_right (s : R) (rel_mul_right (t : R) hw)))
        simp
    · absurd hz
      apply rel_mul_cancel u.prop
      simpa using rel_trans h₃ (rel_mul_right (v : R) hw)
    · absurd hw
      apply rel_mul_cancel v.prop
      simpa using rel_trans h₄ (rel_mul_right (u : R) hz)
    · refine propext ⟨fun h => ?_, fun h => ?_⟩
      · apply rel_mul_cancel s.prop
        apply rel_mul_cancel hz
        calc y * u * s * z
          _ = y * s * (z * u) := by ring
          _ ≤ᵥ x * t * (w * v) := rel_mul h₂ h₃
          _ = x * v * (t * w) := by ring
          _ ≤ᵥ z * s * (t * w) := rel_mul_right (t * w) h
          _ = w * t * s * z := by ring
      · apply rel_mul_cancel t.prop
        apply rel_mul_cancel hw
        calc x * v * t * w
          _ = x * t * (w * v) := by ring
          _ ≤ᵥ y * s * (z * u) := rel_mul h₁ h₄
          _ = y * u * (s * z) := by ring
          _ ≤ᵥ w * t * (s * z) := rel_mul_right (s * z) h
          _ = z * s * t * w := by ring

@[simp]
theorem ValueGroupWithZero.mk_le_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t ≤ ValueGroupWithZero.mk y s ↔ x * s ≤ᵥ y * t := Iff.rfl

instance : LinearOrder (ValueGroupWithZero R) where
  le_refl := ValueGroupWithZero.ind fun _ _ => .rfl
  le_trans a b c hab hbc := by
    induction a using ValueGroupWithZero.ind with | mk a₁ a₂
    induction b using ValueGroupWithZero.ind with | mk b₁ b₂
    induction c using ValueGroupWithZero.ind with | mk c₁ c₂
    rw [ValueGroupWithZero.mk_le_mk] at hab hbc ⊢
    apply rel_mul_cancel b₂.prop
    calc a₁ * c₂ * b₂
      _ = a₁ * b₂ * c₂ := by rw [mul_right_comm]
      _ ≤ᵥ b₁ * a₂ * c₂ := rel_mul_right (c₂ : R) hab
      _ = b₁ * c₂ * a₂ := by rw [mul_right_comm]
      _ ≤ᵥ c₁ * b₂ * a₂ := rel_mul_right (a₂ : R) hbc
      _ = c₁ * a₂ * b₂ := by rw [mul_right_comm]
  le_antisymm a b hab hba := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    exact ValueGroupWithZero.sound hab hba
  le_total a b := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    rw [ValueGroupWithZero.mk_le_mk, ValueGroupWithZero.mk_le_mk]
    apply rel_total
  toDecidableLE := Classical.decRel LE.le

@[simp]
theorem ValueGroupWithZero.mk_lt_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t < ValueGroupWithZero.mk y s ↔
      x * s ≤ᵥ y * t ∧ ¬ y * t ≤ᵥ x * s :=
  Iff.rfl

instance : Bot (ValueGroupWithZero R) where
  bot := 0

theorem ValueGroupWithZero.bot_eq_zero : (⊥ : ValueGroupWithZero R) = 0 := rfl

instance : OrderBot (ValueGroupWithZero R) where
  bot_le := ValueGroupWithZero.ind fun x y => by
    rw [ValueGroupWithZero.bot_eq_zero, ← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_le_mk]
    simp

instance : IsOrderedMonoid (ValueGroupWithZero R) where
  mul_le_mul_left a b hab c := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    induction c using ValueGroupWithZero.ind
    simp only [ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_le_mk, Submonoid.coe_mul]
    conv_lhs => apply mul_mul_mul_comm
    conv_rhs => apply mul_mul_mul_comm
    apply rel_mul_left
    exact hab

instance : Inv (ValueGroupWithZero R) where
  inv := ValueGroupWithZero.lift (fun x s => by
    classical exact if h : x ≤ᵥ 0 then 0 else .mk s ⟨x, h⟩) <| by
    intro x y t s h₁ h₂
    by_cases hx : x ≤ᵥ 0 <;> by_cases hy : y ≤ᵥ 0
    · simp [hx, hy]
    · absurd hy
      apply rel_mul_cancel s.prop
      simpa using rel_trans h₂ (rel_mul_right (t : R) hx)
    · absurd hx
      apply rel_mul_cancel t.prop
      simpa using rel_trans h₁ (rel_mul_right (s : R) hy)
    · simp only [dif_neg hx, dif_neg hy]
      apply ValueGroupWithZero.sound
      · simpa [mul_comm] using h₂
      · simpa [mul_comm] using h₁

@[simp]
theorem ValueGroupWithZero.inv_mk (x : R) (y : posSubmonoid R) (hx : ¬x ≤ᵥ 0) :
    (ValueGroupWithZero.mk x y)⁻¹ = ValueGroupWithZero.mk (y : R) ⟨x, hx⟩ := dif_neg hx

/-- The value group-with-zero is a linearly ordered commutative group with zero. -/
instance : LinearOrderedCommGroupWithZero (ValueGroupWithZero R) where
  zero_le_one := bot_le
  exists_pair_ne := by
    refine ⟨0, 1, fun h => ?_⟩
    apply ge_of_eq at h
    rw [← ValueGroupWithZero.mk_zero 1, ← ValueGroupWithZero.mk_one_one,
      ValueGroupWithZero.mk_le_mk] at h
    simp [not_rel_one_zero] at h
  inv_zero := dif_pos .rfl
  mul_inv_cancel := ValueGroupWithZero.ind fun x y h => by
    rw [ne_eq, ← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_eq_mk] at h
    simp only [Submonoid.coe_one, mul_one, zero_mul, zero_rel, and_true] at h
    rw [ValueGroupWithZero.inv_mk x y h, ← ValueGroupWithZero.mk_one_one,
      ValueGroupWithZero.mk_mul_mk, ValueGroupWithZero.mk_eq_mk]
    simp [mul_comm]

variable (R) in
/-- The "canonical" valuation associated to a valuative relation. -/
def valuation : Valuation R (ValueGroupWithZero R) where
  toFun r := ValueGroupWithZero.mk r 1
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := by simp
  map_add_le_max' := by simp [rel_add_cases]

instance : (valuation R).Compatible where
  rel_iff_le _ _ := by simp [valuation]

@[simp]
lemma ValueGroupWithZero.lift_valuation {α : Sort*} (f : R → posSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : posSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (x : R) :
    ValueGroupWithZero.lift f hf (valuation R x) = f x 1 :=
  rfl

lemma valuation_eq_zero_iff {x : R} :
    valuation R x = 0 ↔ x ≤ᵥ 0 :=
  ValueGroupWithZero.mk_eq_zero _ _

lemma valuation_posSubmonoid_ne_zero (x : posSubmonoid R) :
    valuation R (x : R) ≠ 0 := by
  rw [ne_eq, valuation_eq_zero_iff]
  exact x.prop

lemma ValueGroupWithZero.mk_eq_div (r : R) (s : posSubmonoid R) :
    ValueGroupWithZero.mk r s = valuation R r / valuation R (s : R) := by
  rw [eq_div_iff (valuation_posSubmonoid_ne_zero _)]
  simp [valuation, mk_eq_mk]

/-- Construct a valuative relation on a ring using a valuation. -/
def ofValuation
    {S Γ : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) : ValuativeRel S where
  rel x y := v x ≤ v y
  rel_total x y := le_total (v x) (v y)
  rel_trans := le_trans
  rel_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  rel_mul_right _ h := by simp only [map_mul, mul_le_mul_right' h]
  rel_mul_cancel h0 h := by
    rw [map_zero, le_zero_iff] at h0
    simp only [map_mul] at h
    exact le_of_mul_le_mul_right h (lt_of_le_of_ne' zero_le' h0)
  not_rel_one_zero := by simp

lemma _root_.Valuation.Compatible.ofValuation
    {S Γ : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) :
    letI := ValuativeRel.ofValuation v  -- letI so that instance is inlined directly in declaration
    Valuation.Compatible v :=
  letI := ValuativeRel.ofValuation v
  ⟨fun _ _ ↦ Iff.rfl⟩

lemma isEquiv {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₁]
    [LinearOrderedCommMonoidWithZero Γ₂]
    (v₁ : Valuation R Γ₁)
    (v₂ : Valuation R Γ₂)
    [v₁.Compatible] [v₂.Compatible] :
    v₁.IsEquiv v₂ := by
  intro x y
  simp_rw [← Valuation.Compatible.rel_iff_le]

@[simp]
lemma _root_.Valuation.apply_posSubmonoid_ne_zero {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation R Γ) [v.Compatible] (x : posSubmonoid R) :
    v (x : R) ≠ 0 := by
  simp [(isEquiv v (valuation R)).ne_zero, valuation_posSubmonoid_ne_zero]

@[deprecated (since := "2025-08-06")]
alias valuation_posSubmonoid_ne_zero_of_compatible := _root_.Valuation.apply_posSubmonoid_ne_zero

@[simp]
lemma _root_.Valuation.apply_posSubmonoid_pos {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ]
    (v : Valuation R Γ) [v.Compatible] (x : posSubmonoid R) :
    0 < v x :=
  zero_lt_iff.mpr <| v.apply_posSubmonoid_ne_zero x

variable (R) in
/-- An alias for endowing a ring with a preorder defined as the valuative relation. -/
def WithPreorder := R

/-- The ring instance on `WithPreorder R` arising from the ring structure on `R`. -/
instance : CommRing (WithPreorder R) := inferInstanceAs (CommRing R)

/-- The preorder on `WithPreorder R` arising from the valuative relation on `R`. -/
instance : Preorder (WithPreorder R) where
  le (x y : R) := x ≤ᵥ y
  le_refl _ := rel_refl _
  le_trans _ _ _ := rel_trans

/-- The valuative relation on `WithPreorder R` arising from the valuative relation on `R`.
This is defined as the preorder itself. -/
instance : ValuativeRel (WithPreorder R) where
  rel := (· ≤ ·)
  rel_total := rel_total (R := R)
  rel_trans := rel_trans (R := R)
  rel_add := rel_add (R := R)
  rel_mul_right := rel_mul_right (R := R)
  rel_mul_cancel := rel_mul_cancel (R := R)
  not_rel_one_zero := not_rel_one_zero (R := R)

instance : ValuativePreorder (WithPreorder R) where
  rel_iff_le _ _ := Iff.rfl

variable (R) in
/-- The support of the valuation on `R`. -/
def supp : Ideal R where
  carrier := { x | x ≤ᵥ 0 }
  add_mem' ha hb := rel_add ha hb
  zero_mem' := rel_refl _
  smul_mem' x _ h := by simpa using rel_mul_left _ h

@[simp]
lemma supp_def (x : R) : x ∈ supp R ↔ x ≤ᵥ 0 := Iff.refl _

lemma supp_eq_valuation_supp : supp R = (valuation R).supp := by
  ext x
  constructor
  · intro h
    simp only [supp_def, Valuation.mem_supp_iff] at h ⊢
    apply ValueGroupWithZero.sound
    · simpa
    · simp
  · intro h
    have := ValueGroupWithZero.exact h
    simpa using this.left

instance : (supp R).IsPrime := by
  rw [supp_eq_valuation_supp]
  infer_instance

open NNReal in variable (R) in
/-- An auxiliary structure used to define `IsRankLeOne`. -/
structure RankLeOneStruct where
  /-- The embedding of the value group-with-zero into the nonnegative reals. -/
  emb : ValueGroupWithZero R →*₀ ℝ≥0
  strictMono : StrictMono emb

variable (R) in
/-- We say that a ring with a valuative relation is of rank one if
there exists a strictly monotone embedding of the "canonical" value group-with-zero into
the nonnegative reals, and the image of this embedding contains some element different
from `0` and `1`. -/
class IsRankLeOne where
  nonempty : Nonempty (RankLeOneStruct R)

variable (R) in
/-- We say that a valuative relation on a ring is *nontrivial* if the
  value group-with-zero is nontrivial, meaning that it has an element
  which is different from 0 and 1. -/
class IsNontrivial where
  condition : ∃ γ : ValueGroupWithZero R, γ ≠ 0 ∧ γ ≠ 1

lemma isNontrivial_iff_nontrivial_units :
    IsNontrivial R ↔ Nontrivial (ValueGroupWithZero R)ˣ := by
  constructor
  · rintro ⟨γ, hγ, hγ'⟩
    refine ⟨Units.mk0 _ hγ, 1, ?_⟩
    simp [← Units.val_eq_one, hγ']
  · rintro ⟨r, s, h⟩
    rcases eq_or_ne r 1 with rfl | hr
    · exact ⟨s.val, by simp, by simpa using h.symm⟩
    · exact ⟨r.val, by simp, by simpa using hr⟩

lemma isNontrivial_iff_isNontrivial :
    IsNontrivial R ↔ (valuation R).IsNontrivial := by
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    by_cases hs : valuation R s = 1
    · refine ⟨r, ?_, ?_⟩
      · simpa [valuation] using hr
      · simp only [ne_eq, ValueGroupWithZero.mk_eq_one, not_and, valuation, Valuation.coe_mk,
          MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, OneMemClass.coe_one] at hr' hs ⊢
        contrapose! hr'
        exact hr'.imp hs.right.trans' hs.left.trans
    · refine ⟨s, ?_, hs⟩
      simp [valuation, ← posSubmonoid_def]
  · rintro ⟨r, hr, hr'⟩
    exact ⟨valuation R r, hr, hr'⟩

variable (R) in
/-- A ring with a valuative relation is discrete if its value group-with-zero
has a maximal element `< 1`. -/
class IsDiscrete where
  has_maximal_element :
    ∃ γ : ValueGroupWithZero R, γ < 1 ∧ (∀ δ : ValueGroupWithZero R, δ < 1 → δ ≤ γ)

lemma valuation_surjective (γ : ValueGroupWithZero R) :
    ∃ (a : R) (b : posSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  induction γ using ValueGroupWithZero.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroupWithZero.inv_mk (b : R) 1 b.prop]

lemma exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq (γ : (ValueGroupWithZero R)ˣ) :
    ∃ (a b : posSubmonoid R), valuation R a / valuation _ (b : R) = γ := by
  obtain ⟨a, b, hab⟩ := valuation_surjective γ.val
  lift a to posSubmonoid R using by
    rw [posSubmonoid_def, ← valuation_eq_zero_iff]
    intro H
    simp [H, eq_comm] at hab
  use a, b

end ValuativeRel

open Topology ValuativeRel in
/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the relation `· ≤ᵥ ·`. -/
class IsValuativeTopology (R : Type*) [CommRing R] [ValuativeRel R] [TopologicalSpace R] where
  mem_nhds_iff {s : Set R} {x : R} : s ∈ 𝓝 (x : R) ↔
    ∃ γ : (ValueGroupWithZero R)ˣ, (x + ·) '' { z | valuation _ z < γ } ⊆ s

@[deprecated (since := "2025-08-01")] alias ValuativeTopology := IsValuativeTopology

namespace ValuativeRel

variable {R Γ : Type*} [CommRing R] [ValuativeRel R] [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ)

/-- Any valuation compatible with the valuative relation can be factored through
the value group. -/
noncomputable
def ValueGroupWithZero.embed [h : v.Compatible] : ValueGroupWithZero R →*₀ Γ where
  toFun := ValuativeRel.ValueGroupWithZero.lift (fun r s ↦ v r / v (s : R)) <| by
    intro x y r s
    simp only [h.rel_iff_le, map_mul, ← and_imp, ← le_antisymm_iff]
    rw [div_eq_div_iff] <;> simp
  map_zero' := by simp [ValueGroupWithZero.lift_zero]
  map_one' := by simp
  map_mul' _ _ := by
    apply ValuativeRel.ValueGroupWithZero.lift_mul
    simp [field]

@[simp]
lemma ValueGroupWithZero.embed_mk [v.Compatible] (x : R) (s : posSubmonoid R) :
    embed v (.mk x s) = v x / v (s : R) :=
  rfl

@[simp]
lemma ValueGroupWithZero.embed_valuation (γ : ValueGroupWithZero R) :
    embed (valuation R) γ = γ := by
  induction γ using ValueGroupWithZero.ind
  simp [embed_mk, ← mk_eq_div]

lemma ValueGroupWithZero.embed_strictMono [v.Compatible] : StrictMono (embed v) := by
  intro a b h
  obtain ⟨a, r, rfl⟩ := valuation_surjective a
  obtain ⟨b, s, rfl⟩ := valuation_surjective b
  simp only [map_div₀]
  rw [div_lt_div_iff₀] at h ⊢
  any_goals simp [zero_lt_iff]
  rw [← map_mul, ← map_mul, (isEquiv (valuation R) v).lt_iff_lt] at h
  simpa [embed] using h

/-- For any `x ∈ posSubmonoid R`, the trivial valuation `1 : Valuation R Γ` sends `x` to `1`.
In fact, this is true for any `x ≠ 0`. This lemma is a special case useful for shorthand of
`x ∈ posSubmonoid R → x ≠ 0`. -/
lemma one_apply_posSubmonoid [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R ↦ x = 0]
    (x : posSubmonoid R) : (1 : Valuation R Γ) x = 1 :=
  Valuation.one_apply_of_ne_zero (by simp)

end ValuativeRel

/-- If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`. -/
class ValuativeExtension
    (A B : Type*)
    [CommRing A] [CommRing B]
    [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] where
  rel_iff_rel (a b : A) : algebraMap A B a ≤ᵥ algebraMap A B b ↔ a ≤ᵥ b

namespace ValuativeExtension

open ValuativeRel

variable {A B : Type*} [CommRing A] [CommRing B]
  [ValuativeRel A] [ValuativeRel B] [Algebra A B]
  [ValuativeExtension A B]

variable (A B) in
/-- The morphism of `posSubmonoid`s associated to an algebra map.
  This is used in constructing `ValuativeExtension.mapValueGroupWithZero`. -/
@[simps]
def mapPosSubmonoid : posSubmonoid A →* posSubmonoid B where
  toFun := fun ⟨a,ha⟩ => ⟨algebraMap _ _ a,
    by simpa only [posSubmonoid_def, ← (algebraMap A B).map_zero, rel_iff_rel] using ha⟩
  map_one' := by simp
  map_mul' := by simp

variable (A) in
instance compatible_comap {Γ : Type*}
    [LinearOrderedCommMonoidWithZero Γ] (w : Valuation B Γ) [w.Compatible] :
    (w.comap (algebraMap A B)).Compatible := by
  constructor
  simp [← rel_iff_rel (A := A) (B := B), Valuation.Compatible.rel_iff_le (v := w)]

variable (A B) in
/-- The map on value groups-with-zero associated to the structure morphism of an algebra. -/
def mapValueGroupWithZero : ValueGroupWithZero A →*₀ ValueGroupWithZero B :=
  have := compatible_comap A (valuation B)
  ValueGroupWithZero.embed ((valuation B).comap (algebraMap A B))

@[simp]
lemma mapValueGroupWithZero_mk (r : A) (s : posSubmonoid A) :
    mapValueGroupWithZero A B (.mk r s) = .mk (algebraMap A B r) (mapPosSubmonoid A B s) := by
  simp [mapValueGroupWithZero, ValueGroupWithZero.mk_eq_div (R := B)]

@[simp]
lemma mapValueGroupWithZero_valuation (a : A) :
    mapValueGroupWithZero A B (valuation _ a) = valuation _ (algebraMap _ _ a) := by
  simp [valuation]

end ValuativeExtension

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

/-- Any rank-at-most-one valuation has a mul-archimedean value group.
The converse (for any compatible valuation) is `ValuativeRel.isRankLeOne_iff_mulArchimedean`
which is in a later file since it requires a larger theory of reals. -/
instance [IsRankLeOne R] : MulArchimedean (ValueGroupWithZero R) := by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := R)
  exact .comap f.toMonoidHom hf

end ValuativeRel
