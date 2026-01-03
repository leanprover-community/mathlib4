/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu, Adam Topaz
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Topology.Defs.Filter

/-!

# Valuative Relations

In this file we introduce a class called `ValuativeRel R` for a ring `R`.
This bundles a relation `vle : R → R → Prop` on `R` which mimics a
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

The last two axioms in `ValuativeRel`, namely `vle_mul_cancel` and `not_vle_one_zero`, are
used to ensure that we have a well-behaved valuation taking values in a *value group* (with zero).
In principle, it should be possible to drop these two axioms and obtain a value monoid,
however, such a value monoid would not necessarily embed into an ordered abelian group with zero.
Similarly, without these axioms, the support of the valuation need not be a prime ideal.
We have thus opted to include these two axioms and obtain a `ValueGroupWithZero` associated to
a `ValuativeRel` in order to best align with the literature about valuations on commutative rings.

Future work could refactor `ValuativeRel` by dropping the `vle_mul_cancel` and `not_vle_one_zero`
axioms, opting to make these mixins instead.

## Projects

The `ValuativeRel` class should eventually replace the existing `Valued` typeclass.
Once such a refactor happens, `ValuativeRel` could be renamed to `Valued`.

-/

@[expose] public section

noncomputable section

/-- The class `[ValuativeRel R]` class introduces an operator `x ≤ᵥ y : Prop` for `x y : R`
which is the natural relation arising from (the equivalence class of) a valuation on `R`.
More precisely, if v is a valuation on R then the associated relation is `x ≤ᵥ y ↔ v x ≤ v y`.
Use this class to talk about the case where `R` is equipped with an equivalence class
of valuations. -/
@[ext]
class ValuativeRel (R : Type*) [CommRing R] where
  /-- The valuation less-equal operator arising from `ValuativeRel`. -/
  vle : R → R → Prop
  vle_total (x y) : vle x y ∨ vle y x
  vle_trans {z y x} : vle x y → vle y z → vle x z
  vle_add {x y z} : vle x z → vle y z → vle (x + y) z
  vle_mul_right {x y} (z) : vle x y → vle (x * z) (y * z)
  vle_mul_cancel {x y z} : ¬ vle z 0 → vle (x * z) (y * z) → vle x y
  not_vle_one_zero : ¬ vle 1 0

@[inherit_doc] infix:50 " ≤ᵥ " => ValuativeRel.vle

macro_rules | `($a ≤ᵥ $b) => `(binrel% ValuativeRel.vle $a $b)

attribute [gcongr] ValuativeRel.vle_mul_right

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ≤ᵥ y`
is equivalent to `v x ≤ v y`. -/
class Compatible [ValuativeRel R] where
  vle_iff_le (x y : R) : x ≤ᵥ y ↔ v x ≤ v y

end Valuation

/-- A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation. -/
class ValuativePreorder (R : Type*) [CommRing R] [ValuativeRel R] [Preorder R] where
  vle_iff_le (x y : R) : x ≤ᵥ y ↔ x ≤ y

namespace ValuativeRel

@[deprecated (since := "2025-12-20")] alias Rel := vle
@[deprecated (since := "2025-12-20")] alias rel_total := vle_total
@[deprecated (since := "2025-12-20")] alias rel_trans := vle_trans
@[deprecated (since := "2025-12-20")] alias rel_add := vle_add
@[deprecated (since := "2025-12-20")] alias rel_mul_right := vle_mul_right
@[deprecated (since := "2025-12-20")] alias rel_mul_cancel := vle_mul_cancel
@[deprecated (since := "2025-12-20")] alias not_rel_one_zero := not_vle_one_zero

variable {R : Type*} [CommRing R] [ValuativeRel R] {x y z : R}

/-- The valuation less-than relation, defined as `x < y ↔ ¬ y ≤ᵥ x`. -/
def vlt (x y : R) : Prop := ¬ y ≤ᵥ x

@[deprecated (since := "2025-12-20")] alias SRel := vlt

@[inherit_doc] infix:50 " <ᵥ " => ValuativeRel.vlt

macro_rules | `($a <ᵥ $b) => `(binrel% ValuativeRel.vlt $a $b)

@[simp, grind =] lemma not_vle {x y : R} : ¬ x ≤ᵥ y ↔ y <ᵥ x := .rfl
@[simp, grind =] lemma not_vlt {x y : R} : ¬ x <ᵥ y ↔ y ≤ᵥ x := not_vle.not_left

@[deprecated not_vle (since := "2025-12-20")]
lemma srel_iff {x y : R} : x <ᵥ y ↔ ¬ y ≤ᵥ x := Iff.rfl

@[deprecated (since := "2025-12-20")] alias not_srel_iff := not_vlt

@[simp]
lemma vle_refl (x : R) : x ≤ᵥ x := by
  cases vle_total x x <;> assumption

@[deprecated (since := "2025-12-20")] alias rel_refl := vle_refl

lemma vle_rfl {x : R} : x ≤ᵥ x :=
  vle_refl x

@[deprecated (since := "2025-12-20")] alias rel_rfl := vle_rfl

protected alias vle.refl := vle_refl

@[deprecated (since := "2025-12-20")] protected alias Rel.refl := vle.refl

protected alias vle.rfl := vle_rfl

@[deprecated (since := "2025-12-20")] protected alias Rel.rfl := vle.rfl

@[simp]
theorem zero_vle (x : R) : 0 ≤ᵥ x := by
  simpa using vle_mul_right x ((vle_total 0 1).resolve_right not_vle_one_zero)

@[deprecated (since := "2025-12-20")] alias zero_rel := zero_vle

@[simp]
lemma zero_vlt_one : (0 : R) <ᵥ 1 :=
  not_vle_one_zero

@[deprecated (since := "2025-12-20")] alias zero_srel_one := zero_vlt_one

@[gcongr]
lemma vle_mul_left {x y : R} (z) : x ≤ᵥ y → z * x ≤ᵥ z * y := by
  rw [mul_comm z x, mul_comm z y]
  apply vle_mul_right

@[deprecated (since := "2025-12-20")] alias rel_mul_left := vle_mul_left

instance : Trans (vle (R := R)) (vle (R := R)) (vle (R := R)) where
  trans h1 h2 := vle_trans h1 h2

protected alias vle.trans := vle_trans

@[deprecated (since := "2025-12-20")] protected alias Rel.trans := vle.trans

lemma vle_trans' {x y z : R} (h1 : y ≤ᵥ z) (h2 : x ≤ᵥ y) : x ≤ᵥ z :=
  h2.trans h1

@[deprecated (since := "2025-12-20")] alias rel_trans' := vle_trans'

protected alias vle.trans' := vle_trans'

@[deprecated (since := "2025-12-20")] protected alias Rel.trans' := vle.trans'

@[gcongr]
lemma mul_vle_mul {x x' y y' : R} (h1 : x ≤ᵥ y) (h2 : x' ≤ᵥ y') : x * x' ≤ᵥ y * y' := by
  calc x * x' ≤ᵥ x * y' := vle_mul_left _ h2
    _ ≤ᵥ y * y' := vle_mul_right _ h1

@[deprecated (since := "2025-12-20")] alias mul_rel_mul := mul_vle_mul

@[simp] lemma mul_vle_mul_iff_left (hz : 0 <ᵥ z) : x * z ≤ᵥ y * z ↔ x ≤ᵥ y :=
  ⟨vle_mul_cancel hz, vle_mul_right _⟩

@[deprecated (since := "2025-12-20")] alias mul_rel_mul_iff_left := mul_vle_mul_iff_left

@[simp] lemma mul_vle_mul_iff_right (hx : 0 <ᵥ x) : x * y ≤ᵥ x * z ↔ y ≤ᵥ z := by
  simp [mul_comm x, hx]

@[deprecated (since := "2025-12-20")] alias mul_rel_mul_iff_right := mul_vle_mul_iff_right

@[simp] lemma mul_vlt_mul_iff_left (hz : 0 <ᵥ z) : x * z <ᵥ y * z ↔ x <ᵥ y :=
  (mul_vle_mul_iff_left hz).not

@[deprecated (since := "2025-12-20")] alias mul_srel_mul_iff_left := mul_vlt_mul_iff_left

@[simp] lemma mul_vlt_mul_iff_right (hx : 0 <ᵥ x) : x * y <ᵥ x * z ↔ y <ᵥ z :=
  (mul_vle_mul_iff_right hx).not

@[deprecated (since := "2025-12-20")] alias mul_srel_mul_iff_right := mul_vlt_mul_iff_right

@[deprecated (since := "2025-11-04")] alias rel_mul := mul_vle_mul

theorem vle_add_cases (x y : R) : x + y ≤ᵥ x ∨ x + y ≤ᵥ y :=
  (vle_total y x).imp (fun h => vle_add .rfl h) (fun h => vle_add h .rfl)

@[deprecated (since := "2025-12-20")] alias rel_add_cases := vle_add_cases

@[simp] lemma zero_vlt_mul (hx : 0 <ᵥ x) (hy : 0 <ᵥ y) : 0 <ᵥ x * y := by
  contrapose hy
  rw [not_vlt] at hy ⊢
  rw [show (0 : R) = x * 0 by simp, mul_comm x y, mul_comm x 0] at hy
  exact vle_mul_cancel hx hy

@[deprecated (since := "2025-12-20")] alias zero_srel_mul := zero_vlt_mul

variable (R) in
/-- The submonoid of elements `x : R` whose valuation is positive. -/
def posSubmonoid : Submonoid R where
  carrier := { x | 0 <ᵥ x }
  mul_mem' := zero_vlt_mul
  one_mem' := zero_vlt_one

@[simp] lemma zero_vlt_coe_posSubmonoid (x : posSubmonoid R) : 0 <ᵥ x.val := x.prop

@[deprecated (since := "2025-12-20")] alias zero_srel_coe_posSubmonoid := zero_vlt_coe_posSubmonoid

@[simp]
lemma posSubmonoid_def (x : R) : x ∈ posSubmonoid R ↔ 0 <ᵥ x := Iff.rfl

lemma right_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    x * u ≤ᵥ y * u ↔ x ≤ᵥ y := by simp

lemma left_cancel_posSubmonoid (x y : R) (u : posSubmonoid R) :
    u * x ≤ᵥ u * y ↔ x ≤ᵥ y := by simp

@[simp]
lemma val_posSubmonoid_ne_zero (x : posSubmonoid R) : (x : R) ≠ 0 := by
  have := x.prop
  rw [posSubmonoid_def] at this
  contrapose! this
  simp [this]

variable (R) in
/-- The setoid used to construct `ValueGroupWithZero R`. -/
def valueSetoid : Setoid (R × posSubmonoid R) where
  r := fun (x, s) (y, t) => x * t ≤ᵥ y * s ∧ y * s ≤ᵥ x * t
  iseqv := {
    refl ru := ⟨vle_refl _, vle_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := mul_vle_mul h1 (vle_refl ↑w)
        rw [mul_right_comm s] at this
        have := vle_trans this (mul_vle_mul h3 (vle_refl _))
        rw [mul_right_comm r, mul_right_comm t] at this
        simpa using this
      · have := mul_vle_mul h4 (vle_refl ↑u)
        rw [mul_right_comm s] at this
        have := vle_trans this (mul_vle_mul h2 (vle_refl _))
        rw [mul_right_comm t, mul_right_comm r] at this
        simpa using this
  }

/-- Pull a `ValuativeRel` instace along a ring homomorphism. -/
@[simps -isSimp]
protected abbrev comap {S : Type*} [CommRing S] (f : S →+* R) : ValuativeRel S where
  rel r s := f r ≤ᵥ f s
  rel_total _ _ := rel_total _ _
  rel_trans := rel_trans
  rel_add {_ _ _} := by simpa using rel_add (R := R)
  rel_mul_right _ := by simpa using rel_mul_right _
  rel_mul_cancel {_ _ _} := by simpa using rel_mul_cancel (R := R)
  not_rel_one_zero := by simpa using not_rel_one_zero

instance (S : Subring R) : ValuativeRel S := .comap S.subtype

lemma coe_rel_coe (S : Subring R) {x y : S} : (x : R) ≤ᵥ y ↔ x ≤ᵥ y := .rfl

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
      exact mul_vle_mul h₁ h₃
    · rw [Submonoid.coe_mul, Submonoid.coe_mul,
        mul_mul_mul_comm x, mul_mul_mul_comm y]
      exact mul_vle_mul h₂ h₄

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
    · refine propext ⟨fun h => vle_trans ?_ (zero_vle _), fun h => vle_trans ?_ (zero_vle _)⟩
      · apply vle_mul_cancel (s * v).prop
        rw [mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply vle_trans (vle_mul_right (u : R) (vle_mul_right (v : R) h₂))
        rw [mul_right_comm x]
        apply vle_trans (vle_mul_right (u : R) (vle_mul_right (t : R) h))
        apply vle_trans (vle_mul_right (u : R) (vle_mul_right (t : R) (vle_mul_right (s : R) hz)))
        simp
      · apply vle_mul_cancel (t * u).prop
        rw [mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply vle_trans (vle_mul_right (v : R) (vle_mul_right (u : R) h₁))
        rw [mul_right_comm y]
        apply vle_trans (vle_mul_right (v : R) (vle_mul_right (s : R) h))
        apply vle_trans (vle_mul_right (v : R) (vle_mul_right (s : R) (vle_mul_right (t : R) hw)))
        simp
    · absurd hz
      apply vle_mul_cancel u.prop
      simpa using vle_trans h₃ (vle_mul_right (v : R) hw)
    · absurd hw
      apply vle_mul_cancel v.prop
      simpa using vle_trans h₄ (vle_mul_right (u : R) hz)
    · refine propext ⟨fun h => ?_, fun h => ?_⟩
      · apply vle_mul_cancel s.prop
        apply vle_mul_cancel hz
        calc y * u * s * z
          _ = y * s * (z * u) := by ring
          _ ≤ᵥ x * t * (w * v) := by gcongr
          _ = x * v * (t * w) := by ring
          _ ≤ᵥ z * s * (t * w) := by gcongr
          _ = w * t * s * z := by ring
      · apply vle_mul_cancel t.prop
        apply vle_mul_cancel hw
        calc x * v * t * w
          _ = x * t * (w * v) := by ring
          _ ≤ᵥ y * s * (z * u) := by gcongr
          _ = y * u * (s * z) := by ring
          _ ≤ᵥ w * t * (s * z) := by gcongr
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
    apply vle_mul_cancel b₂.prop
    calc a₁ * c₂ * b₂
      _ = a₁ * b₂ * c₂ := by rw [mul_right_comm]
      _ ≤ᵥ b₁ * a₂ * c₂ := vle_mul_right (c₂ : R) hab
      _ = b₁ * c₂ * a₂ := by rw [mul_right_comm]
      _ ≤ᵥ c₁ * b₂ * a₂ := vle_mul_right (a₂ : R) hbc
      _ = c₁ * a₂ * b₂ := by rw [mul_right_comm]
  le_antisymm a b hab hba := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    exact ValueGroupWithZero.sound hab hba
  le_total a b := by
    induction a using ValueGroupWithZero.ind
    induction b using ValueGroupWithZero.ind
    rw [ValueGroupWithZero.mk_le_mk, ValueGroupWithZero.mk_le_mk]
    apply vle_total
  toDecidableLE := Classical.decRel LE.le

@[simp]
theorem ValueGroupWithZero.mk_lt_mk (x y : R) (t s : posSubmonoid R) :
    ValueGroupWithZero.mk x t < ValueGroupWithZero.mk y s ↔ x * s <ᵥ y * t := by
  rw [lt_iff_not_ge, ← not_vle, mk_le_mk]

@[simp]
lemma ValueGroupWithZero.mk_pos {x : R} {s : posSubmonoid R} :
    0 < ValueGroupWithZero.mk x s ↔ 0 <ᵥ x := by rw [← mk_zero 1]; simp [-mk_zero]

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
    exact vle_mul_right _ hab

instance : Inv (ValueGroupWithZero R) where
  inv := ValueGroupWithZero.lift (fun x s => by
    classical exact if h : x ≤ᵥ 0 then 0 else .mk s ⟨x, h⟩) <| by
    intro x y t s h₁ h₂
    by_cases hx : x ≤ᵥ 0 <;> by_cases hy : y ≤ᵥ 0
    · simp [hx, hy]
    · absurd hy
      apply vle_mul_cancel s.prop
      simpa using vle_trans h₂ (vle_mul_right (t : R) hx)
    · absurd hx
      apply vle_mul_cancel t.prop
      simpa using vle_trans h₁ (vle_mul_right (s : R) hy)
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
    simp [not_vle_one_zero] at h
  inv_zero := dif_pos .rfl
  mul_inv_cancel := ValueGroupWithZero.ind fun x y h => by
    rw [ne_eq, ← ValueGroupWithZero.mk_zero 1, ValueGroupWithZero.mk_eq_mk] at h
    simp only [Submonoid.coe_one, mul_one, zero_mul, zero_vle, and_true] at h
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
  map_add_le_max' := by simp [vle_add_cases]

instance : (valuation R).Compatible where
  vle_iff_le _ _ := by simp [valuation]

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

set_option linter.flexible false in -- simp followed by gcongr
/-- Construct a valuative relation on a ring using a valuation. -/
def ofValuation
    {S Γ : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) : ValuativeRel S where
  vle x y := v x ≤ v y
  vle_total x y := le_total (v x) (v y)
  vle_trans := le_trans
  vle_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  vle_mul_right _ h := by simp [map_mul]; gcongr
  vle_mul_cancel h0 h := by
    rw [map_zero, le_zero_iff] at h0
    simp only [map_mul] at h
    exact le_of_mul_le_mul_right h (lt_of_le_of_ne' zero_le' h0)
  not_vle_one_zero := by simp

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
  simp_rw [← Valuation.Compatible.vle_iff_le]

end ValuativeRel

namespace Valuation

open ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Compatible]
variable {x y : R}

lemma vle_iff_le : x ≤ᵥ y ↔ v x ≤ v y :=
  Compatible.vle_iff_le _ _

@[deprecated (since := "2025-12-20")] alias rel_iff_le := vle_iff_le

lemma vlt_iff_lt : x <ᵥ y ↔ v x < v y := by
  simp [lt_iff_not_ge, ← Compatible.vle_iff_le]

@[deprecated (since := "2025-12-20")] alias srel_iff_lt := vlt_iff_lt

@[deprecated (since := "2025-10-09")]
alias Compatible.srel_iff_lt := vlt_iff_lt

lemma vle_one_iff : x ≤ᵥ 1 ↔ v x ≤ 1 := by simp [v.vle_iff_le]
lemma vlt_one_iff : x <ᵥ 1 ↔ v x < 1 := by simp [v.vlt_iff_lt]
lemma one_vle_iff : 1 ≤ᵥ x ↔ 1 ≤ v x := by simp [v.vle_iff_le]
lemma one_vlt_iff : 1 <ᵥ x ↔ 1 < v x := by simp [v.vlt_iff_lt]

@[deprecated (since := "2025-12-20")] alias rel_one_iff := vle_one_iff
@[deprecated (since := "2025-12-20")] alias srel_one_iff := vlt_one_iff
@[deprecated (since := "2025-12-20")] alias one_rel_iff := one_vle_iff
@[deprecated (since := "2025-12-20")] alias one_srel_iff := one_vlt_iff

@[simp]
lemma apply_posSubmonoid_ne_zero (x : posSubmonoid R) : v (x : R) ≠ 0 := by
  simp [(isEquiv v (valuation R)).ne_zero, valuation_posSubmonoid_ne_zero]

@[deprecated (since := "2025-08-06")]
alias _root_.ValuativeRel.valuation_posSubmonoid_ne_zero_of_compatible := apply_posSubmonoid_ne_zero

@[simp]
lemma apply_posSubmonoid_pos (x : posSubmonoid R) : 0 < v x :=
  zero_lt_iff.mpr <| v.apply_posSubmonoid_ne_zero x

end Valuation

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

variable (R) in
/-- An alias for endowing a ring with a preorder defined as the valuative relation. -/
def WithPreorder := R

/-- The ring instance on `WithPreorder R` arising from the ring structure on `R`. -/
instance : CommRing (WithPreorder R) := inferInstanceAs (CommRing R)

/-- The preorder on `WithPreorder R` arising from the valuative relation on `R`. -/
instance : Preorder (WithPreorder R) where
  le (x y : R) := x ≤ᵥ y
  le_refl _ := vle_refl _
  le_trans _ _ _ := vle_trans
  lt (x y : R) := x <ᵥ y
  lt_iff_le_not_ge (x y : R) := by have := vle_total x y; grind

/-- The valuative relation on `WithPreorder R` arising from the valuative relation on `R`.
This is defined as the preorder itself. -/
instance : ValuativeRel (WithPreorder R) where
  vle := (· ≤ ·)
  vle_total := vle_total (R := R)
  vle_trans := vle_trans (R := R)
  vle_add := vle_add (R := R)
  vle_mul_right := vle_mul_right (R := R)
  vle_mul_cancel := vle_mul_cancel (R := R)
  not_vle_one_zero := not_vle_one_zero (R := R)

instance : ValuativePreorder (WithPreorder R) where
  vle_iff_le _ _ := Iff.rfl

variable (R) in
/-- The support of the valuation on `R`. -/
def supp : Ideal R where
  carrier := { x | x ≤ᵥ 0 }
  add_mem' ha hb := vle_add ha hb
  zero_mem' := vle_refl _
  smul_mem' x _ h := by simpa using vle_mul_left _ h

@[simp]
lemma supp_def (x : R) : x ∈ supp R ↔ x ≤ᵥ 0 := Iff.refl _

lemma supp_eq_valuation_supp : supp R = (valuation R).supp := by
  ext
  simpa using valuation_eq_zero_iff.symm

instance : (supp R).IsPrime := by
  rw [supp_eq_valuation_supp]
  infer_instance

section CommRing

variable {R : Type*} [CommRing R] [ValuativeRel R] {a b c d : R}

lemma vlt_of_vlt_of_vle (hab : a <ᵥ b) (hbc : b ≤ᵥ c) : a <ᵥ c :=
  lt_of_lt_of_le (α := WithPreorder R) hab hbc

@[deprecated (since := "2025-12-20")] alias srel_of_srel_of_rel := vlt_of_vlt_of_vle

alias vlt.trans_vle := vlt_of_vlt_of_vle

@[deprecated (since := "2025-12-20")] alias SRel.trans_rel := vlt.trans_vle

lemma vlt_of_vle_of_vlt (hab : a ≤ᵥ b) (hbc : b <ᵥ c) : a <ᵥ c :=
  lt_of_le_of_lt (α := WithPreorder R) hab hbc

@[deprecated (since := "2025-12-20")] alias srel_of_rel_of_srel := mul_vlt_mul_iff_left

alias vle.trans_vlt := vlt_of_vle_of_vlt

@[deprecated (since := "2025-12-20")] alias Rel.trans_srel := srel_of_rel_of_srel

lemma vlt.vle (hab : a <ᵥ b) : a ≤ᵥ b :=
  le_of_lt (α := WithPreorder R) hab

@[deprecated (since := "2025-12-20")] alias SRel.rel := vlt.vle

lemma vlt.trans (hab : a <ᵥ b) (hbc : b <ᵥ c) : a <ᵥ c :=
  hab.trans_vle hbc.vle

@[deprecated (since := "2025-12-20")] alias SRel.trans := vlt.trans

lemma vle_mul_right_iff (hc : 0 <ᵥ c) : a * c ≤ᵥ b * c ↔ a ≤ᵥ b :=
  ⟨vle_mul_cancel hc, vle_mul_right _⟩

@[deprecated (since := "2025-12-20")] alias rel_mul_right_iff := vle_mul_right_iff

lemma vle_mul_left_iff (hc : 0 <ᵥ c) : c * a ≤ᵥ c * b ↔ a ≤ᵥ b := by
  simp [mul_comm c, vle_mul_right_iff hc]

@[deprecated (since := "2025-12-20")] alias rel_mul_left_iff := vle_mul_left_iff

lemma vlt_mul_right_iff (hc : 0 <ᵥ c) : a * c <ᵥ b * c ↔ a <ᵥ b :=
  (vle_mul_right_iff hc).not

@[deprecated (since := "2025-12-20")] alias srel_mul_right_iff := vlt_mul_right_iff

@[gcongr] alias ⟨_, vlt_mul_right⟩ := vlt_mul_right_iff

@[deprecated (since := "2025-12-20")] alias srel_mul_right := vlt_mul_right

lemma vlt_mul_left_iff (hc : 0 <ᵥ c) : c * a <ᵥ c * b ↔ a <ᵥ b :=
  (vle_mul_left_iff hc).not

@[deprecated (since := "2025-12-20")] alias srel_mul_left_iff := vlt_mul_left_iff

@[gcongr] alias ⟨_, vlt_mul_left⟩ := vlt_mul_left_iff

@[deprecated (since := "2025-12-20")] alias srel_mul_left := vlt_mul_left

lemma mul_vlt_mul_of_vlt_of_vle (hab : a <ᵥ b) (hcd : c ≤ᵥ d) (hd : 0 <ᵥ d) :
    a * c <ᵥ b * d :=
  (vle_mul_left _ hcd).trans_vlt (vlt_mul_right hd hab)

@[deprecated (since := "2025-12-20")] alias mul_srel_mul_of_srel_of_rel := mul_vlt_mul_of_vlt_of_vle

lemma mul_vlt_mul_of_vle_of_vlt (hab : a ≤ᵥ b) (hcd : c <ᵥ d) (ha : 0 <ᵥ a) :
    a * c <ᵥ b * d :=
  (vlt_mul_left ha hcd).trans_vle (vle_mul_right _ hab)

@[deprecated (since := "2025-12-20")] alias mul_srel_mul_of_rel_of_srel := mul_vlt_mul_of_vle_of_vlt

lemma mul_vlt_mul (hab : a <ᵥ b) (hcd : c <ᵥ d) : a * c <ᵥ b * d :=
  (vle_mul_left _ hcd.vle).trans_vlt (vlt_mul_right ((zero_vle c).trans_vlt hcd) hab)

@[deprecated (since := "2025-12-20")] alias mul_srel_mul := mul_vlt_mul

lemma pow_vle_pow (hab : a ≤ᵥ b) (n : ℕ) : a ^ n ≤ᵥ b ^ n := by
  induction n with
  | zero => simp
  | succ _ hn => simp [pow_succ, mul_vle_mul hn hab]

@[deprecated (since := "2025-12-20")] alias pow_rel_pow := pow_vle_pow

lemma pow_vlt_pow (hab : a <ᵥ b) {n : ℕ} (hn : n ≠ 0) : a ^ n <ᵥ b ^ n := by
  obtain (rfl | n) := n
  · aesop
  clear hn
  induction n with
  | zero => aesop
  | succ _ _ => simp_all [pow_succ, mul_vlt_mul]

@[deprecated (since := "2025-12-20")] alias pow_srel_pow := pow_vlt_pow

lemma pow_vle_pow_of_vle_one (ha : a ≤ᵥ 1) {n m : ℕ} (hnm : n ≤ m) : a ^ m ≤ᵥ a ^ n := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using vle_mul_left (a ^ n) (pow_vle_pow ha m)

@[deprecated (since := "2025-12-20")] alias pow_rel_pow_of_rel_one := pow_vle_pow_of_vle_one

lemma pow_vle_pow_of_one_vle (ha : 1 ≤ᵥ a) {n m : ℕ} (hnm : n ≤ m) : a ^ n ≤ᵥ a ^ m := by
  obtain ⟨m, rfl⟩ := exists_add_of_le hnm
  simpa [pow_add] using vle_mul_left (a ^ n) (pow_vle_pow ha m)

@[deprecated (since := "2025-12-20")] alias pow_rel_pow_of_one_rel := pow_vle_pow_of_one_vle

end CommRing

section Field

variable {K : Type*} [Field K] [ValuativeRel K] {a b c x : K}

@[simp]
lemma vle_zero_iff : a ≤ᵥ 0 ↔ a = 0 := by
  rw [← supp_def, Ideal.eq_bot_of_prime (supp K), Ideal.mem_bot]

@[deprecated (since := "2025-12-20")] alias rel_zero_iff := vle_zero_iff

@[simp]
lemma zero_vlt_iff : 0 <ᵥ a ↔ a ≠ 0 := by
  simp [vlt]

@[deprecated (since := "2025-12-20")] alias zero_srel_iff := zero_vlt_iff

lemma vle_div_iff (hc : c ≠ 0) : a ≤ᵥ b / c ↔ a * c ≤ᵥ b := by
  rw [← vle_mul_right_iff (c := c) (by simpa), div_mul_cancel₀ _ (by aesop)]

@[deprecated (since := "2025-12-20")] alias rel_div_iff := vle_div_iff

lemma div_vle_iff (hc : c ≠ 0) : a / c ≤ᵥ b ↔ a ≤ᵥ b * c := by
  rw [← vle_mul_right_iff (c := c) (by simpa), div_mul_cancel₀ _ (by aesop)]

@[deprecated (since := "2025-12-20")] alias div_rel_iff := div_vle_iff

lemma one_vle_div_iff (hb : b ≠ 0) : 1 ≤ᵥ a / b ↔ b ≤ᵥ a := by
  simp [vle_div_iff hb]

@[deprecated (since := "2025-12-20")] alias one_rel_div_iff := one_vle_div_iff

lemma div_vle_one_iff (hb : b ≠ 0) : a / b ≤ᵥ 1 ↔ a ≤ᵥ b := by
  simp [div_vle_iff hb]

@[deprecated (since := "2025-12-20")] alias div_rel_one_iff := div_vle_one_iff

lemma one_vle_inv (hx : x ≠ 0) : 1 ≤ᵥ x⁻¹ ↔ x ≤ᵥ 1 := by
  simpa using one_vle_div_iff (a := 1) hx

@[deprecated (since := "2025-12-20")] alias one_rel_inv := one_vle_inv

lemma inv_vle_one (hx : x ≠ 0) : x⁻¹ ≤ᵥ 1 ↔ 1 ≤ᵥ x := by
  simpa using div_vle_one_iff (a := 1) hx

@[deprecated (since := "2025-12-20")] alias inv_rel_one := inv_vle_one

lemma inv_vlt_one (hx : x ≠ 0) : x⁻¹ <ᵥ 1 ↔ 1 <ᵥ x :=
  (one_vle_inv hx).not

@[deprecated (since := "2025-12-20")] alias inv_srel_one := inv_vlt_one

lemma one_vlt_inv (hx : x ≠ 0) : x⁻¹ <ᵥ 1 ↔ 1 <ᵥ x :=
  (one_vle_inv hx).not

@[deprecated (since := "2025-12-20")] alias one_srel_inv := one_vlt_inv

end Field

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

lemma IsNontrivial.exists_lt_one [IsNontrivial R] :
    ∃ γ : ValueGroupWithZero R, 0 < γ ∧ γ < 1 := by
  obtain ⟨γ, h0, h1⟩ := IsNontrivial.condition (R := R)
  obtain h1 | h1 := lt_or_lt_iff_ne.mpr h1
  · exact ⟨γ, zero_lt_iff.mpr h0, h1⟩
  · exact ⟨γ⁻¹, by simpa [zero_lt_iff], by simp [inv_lt_one_iff₀, h0, h1]⟩

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

lemma isNontrivial_iff_isNontrivial
    {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) [v.Compatible] :
    IsNontrivial R ↔ v.IsNontrivial := by
  constructor
  · rintro ⟨r, hr, hr'⟩
    induction r using ValueGroupWithZero.ind with | mk r s
    have hγ : v r ≠ 0 := by simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr
    have hγ' : v r ≤ v s → v r < v s := by
      simpa [Valuation.Compatible.vle_iff_le (v := v)] using hr'
    by_cases hr : v r = 1
    · exact ⟨s, by simp, fun h ↦ by simp [h, hr] at hγ'⟩
    · exact ⟨r, by simpa using hγ, hr⟩
  · rintro ⟨r, hr, hr'⟩
    exact ⟨valuation R r, (isEquiv v (valuation R)).ne_zero.mp hr,
      by simpa [(isEquiv v (valuation R)).eq_one_iff_eq_one] using hr'⟩

instance {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    [IsNontrivial R] (v : Valuation R Γ₀) [v.Compatible] :
    v.IsNontrivial := by rwa [← isNontrivial_iff_isNontrivial]

lemma ValueGroupWithZero.mk_eq_valuation {K : Type*} [Field K] [ValuativeRel K]
    (x : K) (y : posSubmonoid K) :
    ValueGroupWithZero.mk x y = valuation K (x / y) := by
  rw [Valuation.map_div, ValueGroupWithZero.mk_eq_div]

lemma exists_valuation_div_valuation_eq (γ : ValueGroupWithZero R) :
    ∃ (a : R) (b : posSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  induction γ using ValueGroupWithZero.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroupWithZero.inv_mk (b : R) 1 b.prop]

lemma exists_valuation_posSubmonoid_div_valuation_posSubmonoid_eq (γ : (ValueGroupWithZero R)ˣ) :
    ∃ (a b : posSubmonoid R), valuation R a / valuation _ (b : R) = γ := by
  obtain ⟨a, b, hab⟩ := exists_valuation_div_valuation_eq γ.val
  lift a to posSubmonoid R using by
    contrapose! hab
    rw [posSubmonoid_def, not_vlt, ← valuation_eq_zero_iff] at hab
    simp [hab, eq_comm]
  use a, b

-- See `exists_valuation_div_valuation_eq` for the version that works for all rings.
theorem valuation_surjective {K : Type*} [Field K] [ValuativeRel K] :
    Function.Surjective (valuation K) :=
  ValueGroupWithZero.ind (ValueGroupWithZero.mk_eq_valuation · · ▸ ⟨_, rfl⟩)

variable (R) in
/-- A ring with a valuative relation is discrete if its value group-with-zero
has a maximal element `< 1`. -/
class IsDiscrete where
  has_maximal_element :
    ∃ γ : ValueGroupWithZero R, γ < 1 ∧ (∀ δ : ValueGroupWithZero R, δ < 1 → δ ≤ γ)

variable (R) in
/-- The maximal element that is `< 1` in the value group of a discrete valuation. -/
-- TODO: Link to `Valuation.IsUniformizer` once we connect `Valuation.IsRankOneDiscrete` with
-- `ValuativeRel`.
noncomputable
def uniformizer [IsDiscrete R] : ValueGroupWithZero R :=
  IsDiscrete.has_maximal_element.choose

lemma uniformizer_lt_one [IsDiscrete R] :
    uniformizer R < 1 := IsDiscrete.has_maximal_element.choose_spec.1

lemma le_uniformizer_iff [IsDiscrete R] {a : ValueGroupWithZero R} :
    a ≤ uniformizer R ↔ a < 1 :=
  ⟨fun h ↦ h.trans_lt uniformizer_lt_one,
    IsDiscrete.has_maximal_element.choose_spec.2 a⟩

lemma uniformizer_pos [IsDiscrete R] [IsNontrivial R] :
    0 < uniformizer R := by
  obtain ⟨γ, hγ, hγ'⟩ := IsNontrivial.exists_lt_one (R := R)
  exact hγ.trans_le (le_uniformizer_iff.mpr hγ')

@[simp]
lemma uniformizer_ne_zero [IsDiscrete R] [IsNontrivial R] :
    uniformizer R ≠ 0 :=
  uniformizer_pos.ne'

lemma uniformizer_inv_le_iff [IsDiscrete R] [IsNontrivial R] {a : ValueGroupWithZero R} :
    (uniformizer R)⁻¹ ≤ a ↔ 1 < a := by
  by_cases ha : a = 0
  · simp [ha]
  replace ha : 0 < a := bot_lt_iff_ne_bot.mpr ha
  rw [inv_le_comm₀ uniformizer_pos ha, le_uniformizer_iff, inv_lt_one₀ ha]

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
    simp only [h.vle_iff_le, map_mul, ← and_imp, ← le_antisymm_iff]
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
  obtain ⟨a, r, rfl⟩ := exists_valuation_div_valuation_eq a
  obtain ⟨b, s, rfl⟩ := exists_valuation_div_valuation_eq b
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
  vle_iff_vle (a b : A) : algebraMap A B a ≤ᵥ algebraMap A B b ↔ a ≤ᵥ b

namespace ValuativeExtension

open ValuativeRel

variable {A B : Type*} [CommRing A] [CommRing B]
  [ValuativeRel A] [ValuativeRel B] [Algebra A B]
  [ValuativeExtension A B]

lemma vlt_iff_vlt {a b : A} : algebraMap A B a <ᵥ algebraMap A B b ↔ a <ᵥ b := by
  rw [← not_vle, vle_iff_vle, not_vle]

@[deprecated (since := "2025-12-20")] alias srel_iff_srel := vlt_iff_vlt

variable (A B) in
/-- The morphism of `posSubmonoid`s associated to an algebra map.
  This is used in constructing `ValuativeExtension.mapValueGroupWithZero`. -/
@[simps]
def mapPosSubmonoid : posSubmonoid A →* posSubmonoid B where
  toFun := fun ⟨a,ha⟩ => ⟨algebraMap _ _ a,
    by simpa only [posSubmonoid_def, ← (algebraMap A B).map_zero, vlt_iff_vlt] using ha⟩
  map_one' := by simp
  map_mul' := by simp

variable (A) in
instance compatible_comap {Γ : Type*}
    [LinearOrderedCommMonoidWithZero Γ] (w : Valuation B Γ) [w.Compatible] :
    (w.comap (algebraMap A B)).Compatible := by
  constructor
  simp [← vle_iff_vle (A := A) (B := B), Valuation.Compatible.vle_iff_le (v := w)]

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

lemma mapValueGroupWithZero_strictMono : StrictMono (mapValueGroupWithZero A B) :=
  ValueGroupWithZero.embed_strictMono _

variable (B) in
lemma _root_.ValuativeRel.IsRankLeOne.of_valuativeExtension [IsRankLeOne B] : IsRankLeOne A := by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := B)
  exact ⟨⟨f.comp (mapValueGroupWithZero _ _), hf.comp mapValueGroupWithZero_strictMono⟩⟩

end ValuativeExtension

instance {R : Type*} [CommRing R] [ValuativeRel R] (S : Subring R) :
    ValuativeExtension S R where
  rel_iff_rel _ _ := .rfl

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

/-- Any rank-at-most-one valuation has a mul-archimedean value group.
The converse (for any compatible valuation) is `ValuativeRel.isRankLeOne_iff_mulArchimedean`
which is in a later file since it requires a larger theory of reals. -/
instance [IsRankLeOne R] : MulArchimedean (ValueGroupWithZero R) := by
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := R)
  exact .comap f.toMonoidHom hf

end ValuativeRel
