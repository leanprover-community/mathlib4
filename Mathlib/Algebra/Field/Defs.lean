/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Rat.Init
import Mathbin.Algebra.Ring.Defs

/-!
# Division (semi)rings and (semi)fields

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `field_theory` folder.

## Main definitions

* `division_semiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `division_ring`: : Nontrivial ring with multiplicative inverses for nonzero elements.
* `semifield`: Commutative division semiring.
* `field`: Commutative division ring.
* `is_field`: Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
  commutative, that it has more than one element and that all non-zero elements have a
  multiplicative inverse. In contrast to `field`, which contains the data of a function associating
  to an element of the field its multiplicative inverse, this predicate only assumes the existence
  and can therefore more easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `group_with_zero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `group_with_zero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/


open Function Set

universe u

variable {α β K : Type _}

/-- The default definition of the coercion `(↑(a : ℚ) : K)` for a division ring `K`
is defined as `(a / b : K) = (a : K) * (b : K)⁻¹`.
Use `coe` instead of `rat.cast_rec` for better definitional behaviour.
-/
def Rat.castRec [HasLiftT ℕ K] [HasLiftT ℤ K] [Mul K] [Inv K] : ℚ → K
  | ⟨a, b, _, _⟩ => ↑a * (↑b)⁻¹
#align rat.cast_rec Rat.castRec

/-- Type class for the canonical homomorphism `ℚ → K`.
-/
@[protect_proj]
class HasRatCast (K : Type u) where
  ratCast : ℚ → K
#align has_rat_cast HasRatCast

/-- The default definition of the scalar multiplication `(a : ℚ) • (x : K)` for a division ring `K`
is given by `a • x = (↑ a) * x`.
Use `(a : ℚ) • (x : K)` instead of `qsmul_rec` for better definitional behaviour.
-/
def qsmulRec (coe : ℚ → K) [Mul K] (a : ℚ) (x : K) : K :=
  coe a * x
#align qsmul_rec qsmulRec

/-- A `division_semiring` is a `semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj]
class DivisionSemiring (α : Type _) extends Semiring α, GroupWithZero α
#align division_semiring DivisionSemiring

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements.

An instance of `division_ring K` includes maps `rat_cast : ℚ → K` and `qsmul : ℚ → K → K`.
If the division ring has positive characteristic p, we define `rat_cast (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `rat_cast` and `qsmul` are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj]
class DivisionRing (K : Type u) extends Ring K, DivInvMonoid K, Nontrivial K, HasRatCast K where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : K)⁻¹ = 0
  ratCast := Rat.castRec
  rat_cast_mk : ∀ (a : ℤ) (b : ℕ) (h1 h2), rat_cast ⟨a, b, h1, h2⟩ = a * b⁻¹ := by
    intros
    rfl
  qsmul : ℚ → K → K := qsmulRec rat_cast
  qsmul_eq_mul' : ∀ (a : ℚ) (x : K), qsmul a x = rat_cast a * x := by
    intros
    rfl
#align division_ring DivisionRing

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing α] : DivisionSemiring α :=
  { ‹DivisionRing α›, (inferInstance : Semiring α) with }
#align division_ring.to_division_semiring DivisionRing.toDivisionSemiring

/-- A `semifield` is a `comm_semiring` with multiplicative inverses for nonzero elements. -/
@[protect_proj]
class Semifield (α : Type _) extends CommSemiring α, DivisionSemiring α, CommGroupWithZero α
#align semifield Semifield

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements.

An instance of `field K` includes maps `of_rat : ℚ → K` and `qsmul : ℚ → K → K`.
If the field has positive characteristic p, we define `of_rat (1 / p) = 1 / 0 = 0`
for consistency with our division by zero convention.
The fields `of_rat` and `qsmul are needed to implement the
`algebra_rat [division_ring K] : algebra ℚ K` instance, since we need to control the specific
definitions for some special cases of `K` (in particular `K = ℚ` itself).
See also Note [forgetful inheritance].
-/
@[protect_proj]
class Field (K : Type u) extends CommRing K, DivisionRing K
#align field Field

section DivisionRing

variable [DivisionRing K] {a b : K}

namespace Rat

-- see Note [coercion into rings]
/-- Construct the canonical injection from `ℚ` into an arbitrary
  division ring. If the field has positive characteristic `p`,
  we define `1 / p = 1 / 0 = 0` for consistency with our
  division by zero convention. -/
instance (priority := 900) castCoe {K : Type _} [HasRatCast K] : CoeTC ℚ K :=
  ⟨HasRatCast.ratCast⟩
#align rat.cast_coe Rat.castCoe

theorem cast_mk' (a b h1 h2) : ((⟨a, b, h1, h2⟩ : ℚ) : K) = a * b⁻¹ :=
  DivisionRing.rat_cast_mk _ _ _ _
#align rat.cast_mk' Rat.cast_mk'

theorem cast_def : ∀ r : ℚ, (r : K) = r.num / r.denom
  | ⟨a, b, h1, h2⟩ => (cast_mk' _ _ _ _).trans (div_eq_mul_inv _ _).symm
#align rat.cast_def Rat.cast_def

instance (priority := 100) smulDivisionRing : HasSmul ℚ K :=
  ⟨DivisionRing.qsmul⟩
#align rat.smul_division_ring Rat.smulDivisionRing

theorem smul_def (a : ℚ) (x : K) : a • x = ↑a * x :=
  DivisionRing.qsmul_eq_mul' a x
#align rat.smul_def Rat.smul_def

end Rat

end DivisionRing

section Field

variable [Field K]

-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield : Semifield K :=
  { ‹Field K›, (inferInstance : Semiring K) with }
#align field.to_semifield Field.toSemifield

end Field

section IsField

/-- A predicate to express that a (semi)ring is a (semi)field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a (semi)field. -/
structure IsField (R : Type u) [Semiring R] : Prop where
  exists_pair_ne : ∃ x y : R, x ≠ y
  mul_comm : ∀ x y : R, x * y = y * x
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
#align is_field IsField

/-- Transferring from `semifield` to `is_field`. -/
theorem Semifield.toIsField (R : Type u) [Semifield R] : IsField R :=
  { ‹Semifield R› with mul_inv_cancel := fun a ha => ⟨a⁻¹, mul_inv_cancel ha⟩ }
#align semifield.to_is_field Semifield.toIsField

/-- Transferring from `field` to `is_field`. -/
theorem Field.toIsField (R : Type u) [Field R] : IsField R :=
  Semifield.toIsField _
#align field.to_is_field Field.toIsField

@[simp]
theorem IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩
#align is_field.nontrivial IsField.nontrivial

@[simp]
theorem not_is_field_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬IsField R := fun h =>
  let ⟨x, y, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)
#align not_is_field_of_subsingleton not_is_field_of_subsingleton

open Classical

/-- Transferring from `is_field` to `semifield`. -/
noncomputable def IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield R :=
  { ‹Semiring R›, h with inv := fun a => if ha : a = 0 then 0 else Classical.choose (IsField.mul_inv_cancel h ha),
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a ha => by
      convert Classical.choose_spec (IsField.mul_inv_cancel h ha)
      exact dif_neg ha }
#align is_field.to_semifield IsField.toSemifield

/-- Transferring from `is_field` to `field`. -/
noncomputable def IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R :=
  { ‹Ring R›, IsField.toSemifield h with }
#align is_field.to_field IsField.toField

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_is_field (R : Type u) [Ring R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by
  intro x hx
  apply exists_unique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
    
  · intro y z hxy hxz
    calc
      y = y * (x * z) := by rw [hxz, mul_one]
      _ = x * y * z := by rw [← mul_assoc, hf.mul_comm y x]
      _ = z := by rw [hxy, one_mul]
      
    
#align uniq_inv_of_is_field uniq_inv_of_is_field

end IsField

