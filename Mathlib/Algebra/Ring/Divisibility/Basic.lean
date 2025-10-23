/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about divisibility in rings

Note that this file is imported by basic tactics like `linarith` and so must have only minimal
imports. Further results about divisibility in rings may be found in
`Mathlib/Algebra/Ring/Divisibility/Lemmas.lean` which is not subject to this import constraint.
-/


variable {α β : Type*}

section Semigroup

variable [Semigroup α] [Semigroup β] {F : Type*} [EquivLike F α β] [MulEquivClass F α β]

theorem map_dvd_iff (f : F) {a b} : f a ∣ f b ↔ a ∣ b :=
  let f := MulEquivClass.toMulEquiv f
  ⟨fun h ↦ by rw [← f.left_inv a, ← f.left_inv b]; exact map_dvd f.symm h, map_dvd f⟩

theorem map_dvd_iff_dvd_symm (f : F) {a : α} {b : β} :
    f a ∣ b ↔ a ∣ (MulEquivClass.toMulEquiv f).symm b := by
  obtain ⟨c, rfl⟩ : ∃ c, f c = b := EquivLike.surjective f b
  simp [map_dvd_iff]

theorem MulEquiv.decompositionMonoid (f : F) [DecompositionMonoid β] : DecompositionMonoid α where
  primal a b c h := by
    rw [← map_dvd_iff f, map_mul] at h
    obtain ⟨a₁, a₂, h⟩ := DecompositionMonoid.primal _ h
    refine ⟨symm f a₁, symm f a₂, ?_⟩
    simp_rw [← map_dvd_iff f, ← map_mul, eq_symm_apply]
    iterate 2 erw [(f : α ≃* β).apply_symm_apply]
    exact h

/--
If `G` is a `LeftCancelSemiGroup`, left multiplication by `g` yields an equivalence between `G`
and the set of elements of `G` divisible by `g`.
-/
protected noncomputable def Equiv.dvd {G : Type*} [LeftCancelSemigroup G] (g : G) :
    G ≃ {a : G // g ∣ a} where
  toFun := fun a ↦ ⟨g * a, ⟨a, rfl⟩⟩
  invFun := fun ⟨_, h⟩ ↦ h.choose
  left_inv := fun _ ↦ by simp
  right_inv := by
    rintro ⟨_, ⟨_, rfl⟩⟩
    simp

@[simp]
theorem Equiv.dvd_apply {G : Type*} [LeftCancelSemigroup G] (g a : G) :
    Equiv.dvd g a = g * a := rfl

end Semigroup

section DistribSemigroup

variable [Add α] [Semigroup α]

theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])

alias Dvd.dvd.add := dvd_add

end DistribSemigroup

section Semiring
variable [Semiring α] {a b c : α} {m n : ℕ}

lemma min_pow_dvd_add (ha : c ^ m ∣ a) (hb : c ^ n ∣ b) : c ^ min m n ∣ a + b :=
  ((pow_dvd_pow c (m.min_le_left n)).trans ha).add ((pow_dvd_pow c (m.min_le_right n)).trans hb)

end Semiring

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α]

theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)

end NonUnitalCommSemiring

section Semigroup

variable [Semigroup α] [HasDistribNeg α] {a b : α}

/-- An element `a` of a semigroup with a distributive negation divides the negation of an element
`b` iff `a` divides `b`. -/
@[simp]
theorem dvd_neg : a ∣ -b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_inj, Dvd.dvd]

/-- The negation of an element `a` of a semigroup with a distributive negation divides another
element `b` iff `a` divides `b`. -/
@[simp]
theorem neg_dvd : -a ∣ b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by
    simp only [Equiv.neg_symm, Equiv.neg_apply, mul_neg, neg_mul, neg_neg, Dvd.dvd]

alias ⟨Dvd.dvd.of_neg_left, Dvd.dvd.neg_left⟩ := neg_dvd

alias ⟨Dvd.dvd.of_neg_right, Dvd.dvd.neg_right⟩ := dvd_neg

end Semigroup

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right

alias Dvd.dvd.sub := dvd_sub

/-- If an element `a` divides another element `c` in a ring, `a` divides the sum of another element
`b` with `c` iff `a` divides `b`. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun H => by simpa only [add_sub_cancel_right] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩

/-- If an element `a` divides another element `b` in a ring, `a` divides the sum of `b` and another
element `c` iff `a` divides `c`. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw [add_comm]; exact dvd_add_left h

/-- If an element `a` divides another element `c` in a ring, `a` divides the difference of another
element `b` with `c` iff `a` divides `b`. -/
theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b := by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)

/-- If an element `a` divides another element `b` in a ring, `a` divides the difference of `b` and
another element `c` iff `a` divides `c`. -/
theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c := by
  rw [sub_eq_add_neg, dvd_add_right h, dvd_neg]

theorem dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  rw [← sub_add_cancel b c, dvd_add_right h]

theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [← dvd_neg, neg_sub]

end NonUnitalRing

section Ring

variable [Ring α] {a b : α}

/-- An element a divides the sum a + b if and only if a divides b. -/
@[simp]
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b. -/
@[simp]
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)

/-- An element `a` divides the difference `a - b` if and only if `a` divides `b`. -/
@[simp]
theorem dvd_sub_self_left : a ∣ a - b ↔ a ∣ b :=
  dvd_sub_right dvd_rfl

/-- An element `a` divides the difference `b - a` if and only if `a` divides `b`. -/
@[simp]
theorem dvd_sub_self_right : a ∣ b - a ↔ a ∣ b :=
  dvd_sub_left dvd_rfl

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing α]

theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) :
    k ∣ a * x - b * y := by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y) using 1
  rw [mul_sub_left_distrib, mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]

end NonUnitalCommRing
