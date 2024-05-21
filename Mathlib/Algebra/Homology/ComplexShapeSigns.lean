/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ComplexShape
import Mathlib.Algebra.Ring.NegOnePow

/-! Signs in constructions on homological complexes

In this file, we shall introduce various typeclasses which will allow
the construction of the total complex of a bicomplex and of the
the monoidal category structure on categories of homological complexes (TODO).

The most important definition is that of `TotalComplexShape c₁ c₂ c₁₂` given
three complex shapes `c₁`, `c₂`, `c₁₂`: it allows the definition of a total
complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂` (at least
when suitable coproducts exist).

In particular, we construct an instance of `TotalComplexShape c c c` when `c : ComplexShape I`
and `I` is an additive monoid equipped with a group homomorphism `ε' : Multiplicative I → ℤˣ`
satisfying certain properties (see `ComplexShape.TensorSigns`).

TODO @joelriou: add more classes for the associativity of the total complex, etc.

-/

variable {I₁ I₂ I₁₂ : Type*}
  (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c₁₂ : ComplexShape I₁₂)

/-- A total complex shape for three complexes shapes `c₁`, `c₂`, `c₁₂` on three types
`I₁`, `I₂` and `I₁₂` consists of the data and properties that will allow the construction
of a total complex functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂` which
sends `K` to a complex which in degree `i₁₂ : I₁₂` consists of the coproduct
of the `(K.X i₁).X i₂` such that `π ⟨i₁, i₂⟩ = i₁₂`. -/
class TotalComplexShape  where
  /-- a map on indices -/
  π : I₁ × I₂ → I₁₂
  /-- the sign of the horizontal differential in the total complex -/
  ε₁ : I₁ × I₂ → ℤˣ
  /-- the sign of the vertical differential in the total complex -/
  ε₂ : I₁ × I₂ → ℤˣ
  rel₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁', i₂⟩)
  rel₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') : c₁₂.Rel (π ⟨i₁, i₂⟩) (π ⟨i₁, i₂'⟩)
  ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ ⟨i₁, i₂⟩ * ε₁ ⟨i₁, i₂'⟩ = - ε₁ ⟨i₁, i₂⟩ * ε₂ ⟨i₁', i₂⟩

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂]

/-- The map `I₁ × I₂ → I₁₂` on indices given by `TotalComplexShape c₁ c₂ c₁₂`. -/
abbrev π (i : I₁ × I₂) : I₁₂ := TotalComplexShape.π c₁ c₂ c₁₂ i

/-- The sign of the horizontal differential in the total complex. -/
abbrev ε₁ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₁ c₁ c₂ c₁₂ i

/-- The sign of the vertical differential in the total complex. -/
abbrev ε₂ (i : I₁ × I₂) : ℤˣ := TotalComplexShape.ε₂ c₁ c₂ c₁₂ i

variable {c₁}

lemma rel_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) :=
  TotalComplexShape.rel₁ h i₂

lemma next_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  c₁₂.next_eq' (rel_π₁ c₂ c₁₂ h i₂)

lemma prev_π₁ {i₁ i₁' : I₁} (h : c₁.Rel i₁ i₁') (i₂ : I₂) :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁', i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₁ c₂ c₁₂ h i₂)

variable (c₁) {c₂}

lemma rel_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.Rel (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) :=
  TotalComplexShape.rel₂ i₁ h

lemma next_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.next (π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  c₁₂.next_eq' (rel_π₂ c₁ c₁₂ i₁ h)

lemma prev_π₂ (i₁ : I₁) {i₂ i₂' : I₂} (h : c₂.Rel i₂ i₂') :
    c₁₂.prev (π c₁ c₂ c₁₂ ⟨i₁, i₂'⟩) = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ :=
  c₁₂.prev_eq' (rel_π₂ c₁ c₁₂ i₁ h)

variable {c₁}

lemma ε₂_ε₁ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ =
      - ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ :=
  TotalComplexShape.ε₂_ε₁ h₁ h₂

lemma ε₁_ε₂ {i₁ i₁' : I₁} {i₂ i₂' : I₂} (h₁ : c₁.Rel i₁ i₁') (h₂ : c₂.Rel i₂ i₂') :
    ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ =
      - ε₂ c₁ c₂ c₁₂ ⟨i₁', i₂⟩ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂'⟩ :=
  Eq.trans (mul_one _).symm (by
    rw [← Int.units_mul_self (ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂')), mul_assoc]
    conv_lhs =>
      arg 2
      rw [← mul_assoc, ε₂_ε₁ c₁₂ h₁ h₂]
    rw [neg_mul, neg_mul, neg_mul, mul_neg, neg_inj, ← mul_assoc, ← mul_assoc,
      Int.units_mul_self, one_mul])

section

variable {I : Type*} [AddMonoid I] (c : ComplexShape I)

/-- If `I` is an additive monoid and `c : ComplexShape I`, `c.TensorSigns` contains the data of
map `ε : I → ℤˣ` and properties which allows the construction of a `TotalComplexShape c c c`. -/
class TensorSigns where
  /-- the signs which appear in the vertical differential of the total complex -/
  ε' : Multiplicative I →* ℤˣ
  rel_add (p q r : I) (hpq : c.Rel p q) : c.Rel (p + r) (q + r)
  add_rel (p q r : I) (hpq : c.Rel p q) : c.Rel (r + p) (r + q)
  ε'_succ (p q : I) (hpq : c.Rel p q) : ε' q = - ε' p

variable [TensorSigns c]

/-- The signs which appear in the vertical differential of the total complex. -/
abbrev ε (i : I) : ℤˣ := TensorSigns.ε' c i

lemma rel_add {p q : I} (hpq : c.Rel p q) (r : I) : c.Rel (p + r) (q + r) :=
  TensorSigns.rel_add _ _ _ hpq

lemma add_rel (r : I) {p q : I} (hpq : c.Rel p q) : c.Rel (r + p) (r + q) :=
  TensorSigns.add_rel _ _ _ hpq

@[simp]
lemma ε_zero : c.ε 0 = 1 := by
  apply MonoidHom.map_one

lemma ε_succ {p q : I} (hpq : c.Rel p q) : c.ε q = - c.ε p :=
  TensorSigns.ε'_succ p q hpq

lemma ε_add (p q : I) : c.ε (p + q) = c.ε p * c.ε q := by
  apply MonoidHom.map_mul

lemma next_add (p q : I) (hp : c.Rel p (c.next p)) :
    c.next (p + q) = c.next p + q :=
  c.next_eq' (c.rel_add hp q)

lemma next_add' (p q : I) (hq : c.Rel q (c.next q)) :
    c.next (p + q) = p + c.next q :=
  c.next_eq' (c.add_rel p hq)

@[simps]
instance : TotalComplexShape c c c where
  π := fun ⟨p, q⟩ => p + q
  ε₁ := fun _ => 1
  ε₂ := fun ⟨p, _⟩ => c.ε p
  rel₁ h q := c.rel_add h q
  rel₂ p _ _ h := c.add_rel p h
  ε₂_ε₁ h _ := by
    dsimp
    rw [neg_mul, one_mul, mul_one, c.ε_succ h, neg_neg]

instance : TensorSigns (ComplexShape.down ℕ) where
  ε' := MonoidHom.mk' (fun (i : ℕ) => (-1 : ℤˣ) ^ i) (pow_add (-1 : ℤˣ))
  rel_add p q r (hpq : q + 1 = p) := by dsimp; omega
  add_rel p q r (hpq : q + 1 = p) := by dsimp; omega
  ε'_succ := by
    rintro _ q rfl
    dsimp
    rw [pow_add, pow_one, mul_neg, mul_one, neg_neg]

@[simp]
lemma ε_down_ℕ (n : ℕ) : (ComplexShape.down ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

instance : TensorSigns (ComplexShape.up ℤ) where
  ε' := MonoidHom.mk' Int.negOnePow Int.negOnePow_add
  rel_add p q r (hpq : p + 1 = q) := by dsimp; omega
  add_rel p q r (hpq : p + 1 = q) := by dsimp; omega
  ε'_succ := by
    rintro p _ rfl
    dsimp
    rw [Int.negOnePow_succ]

@[simp]
lemma ε_up_ℤ (n : ℤ) : (ComplexShape.up ℤ).ε n = n.negOnePow := rfl

end

end ComplexShape

/-- A total complex shape symmetry contains the data and properties which allow the
identification of the two total complex functors
`HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex C c₁₂`
and `HomologicalComplex₂ C c₂ c₁ ⥤ HomologicalComplex C c₁₂` via the flip. -/
class TotalComplexShapeSymmetry [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂] where
  symm (i₁ : I₁) (i₂ : I₂) : ComplexShape.π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩
  /-- the signs involved in the symmetry isomorphism of the total complex -/
  σ (i₁ : I₁) (i₂ : I₂) : ℤˣ
  σ_ε₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ i₁ i₂ * ComplexShape.ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁' i₂
  σ_ε₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ i₁ i₂ * ComplexShape.ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ComplexShape.ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ i₁ i₂'

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetry c₁ c₂ c₁₂]

/-- The signs involved in the symmetry isomorphism of the total complex. -/
abbrev σ (i₁ : I₁) (i₂ : I₂) : ℤˣ := TotalComplexShapeSymmetry.σ c₁ c₂ c₁₂ i₁ i₂

lemma π_symm (i₁ : I₁) (i₂ : I₂) :
    π c₂ c₁ c₁₂ ⟨i₂, i₁⟩ = π c₁ c₂ c₁₂ ⟨i₁, i₂⟩ := by
  apply TotalComplexShapeSymmetry.symm

variable {c₁}

lemma σ_ε₁ {i₁ i₁' : I₁} (h₁ : c₁.Rel i₁ i₁') (i₂ : I₂) :
    σ c₁ c₂ c₁₂ i₁ i₂ * ε₁ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ε₂ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ c₁ c₂ c₁₂ i₁' i₂ :=
  TotalComplexShapeSymmetry.σ_ε₁ h₁ i₂

variable (c₁) {c₂}

lemma σ_ε₂ (i₁ : I₁) {i₂ i₂' : I₂} (h₂ : c₂.Rel i₂ i₂') :
    σ c₁ c₂ c₁₂ i₁ i₂ * ε₂ c₁ c₂ c₁₂ ⟨i₁, i₂⟩ = ε₁ c₂ c₁ c₁₂ ⟨i₂, i₁⟩ * σ c₁ c₂ c₁₂ i₁ i₂' :=
  TotalComplexShapeSymmetry.σ_ε₂ i₁ h₂

@[simps]
instance : TotalComplexShapeSymmetry (up ℤ) (up ℤ) (up ℤ) where
  symm p q := add_comm q p
  σ p q := (p * q).negOnePow
  σ_ε₁ := by
    rintro p _ rfl q
    dsimp
    rw [mul_one, ← Int.negOnePow_add, add_comm q, add_mul, one_mul, Int.negOnePow_add,
      Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
  σ_ε₂ := by
    rintro p q _ rfl
    dsimp
    rw [one_mul, ← Int.negOnePow_add, mul_add, mul_one]

end ComplexShape

/-- This typeclass expresses that the signs given by `[TotalComplexShapeSymmetry c₁ c₂ c₁₂]`
and by `[TotalComplexShapeSymmetry c₂ c₁ c₁₂]` are compatible. -/
class TotalComplexShapeSymmetrySymmetry [TotalComplexShape c₁ c₂ c₁₂]
    [TotalComplexShape c₂ c₁ c₁₂] [TotalComplexShapeSymmetry c₁ c₂ c₁₂]
    [TotalComplexShapeSymmetry c₂ c₁ c₁₂] : Prop where
  σ_symm i₁ i₂ : ComplexShape.σ c₂ c₁ c₁₂ i₂ i₁ = ComplexShape.σ c₁ c₂ c₁₂ i₁ i₂

namespace ComplexShape

variable [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetry c₁ c₂ c₁₂] [TotalComplexShapeSymmetry c₂ c₁ c₁₂]
  [TotalComplexShapeSymmetrySymmetry c₁ c₂ c₁₂]

lemma σ_symm (i₁ : I₁) (i₂ : I₂) :
    σ c₂ c₁ c₁₂ i₂ i₁ = σ c₁ c₂ c₁₂ i₁ i₂ := by
  apply TotalComplexShapeSymmetrySymmetry.σ_symm

end ComplexShape
