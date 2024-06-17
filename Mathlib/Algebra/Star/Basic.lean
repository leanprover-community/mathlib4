/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Opposite

#align_import algebra.star.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# Star monoids, rings, and modules

We introduce the basic algebraic notions of star monoids, star rings, and star modules.
A star algebra is simply a star ring that is also a star module.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type*) [Ring R] [StarRing R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star non-unital, non-associative, semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/

assert_not_exists Finset
assert_not_exists Subgroup

universe u v w

open MulOpposite
open scoped NNRat

/-- Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class Star (R : Type u) where
  star : R → R
#align has_star Star

-- https://github.com/leanprover/lean4/issues/2096
compile_def% Star.star

variable {R : Type u}

export Star (star)

/-- A star operation (e.g. complex conjugate).
-/
add_decl_doc star

/-- `StarMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under star. -/
class StarMemClass (S R : Type*) [Star R] [SetLike S R] : Prop where
  /-- Closure under star. -/
  star_mem : ∀ {s : S} {r : R}, r ∈ s → star r ∈ s
#align star_mem_class StarMemClass

export StarMemClass (star_mem)

attribute [aesop safe apply (rule_sets := [SetLike])] star_mem

namespace StarMemClass

variable {S : Type w} [Star R] [SetLike S R] [hS : StarMemClass S R] (s : S)

instance instStar : Star s where
  star r := ⟨star (r : R), star_mem r.prop⟩

@[simp] lemma coe_star (x : s) : star x = star (x : R) := rfl

end StarMemClass

/-- Typeclass for a star operation with is involutive.
-/
class InvolutiveStar (R : Type u) extends Star R where
  /-- Involutive condition. -/
  star_involutive : Function.Involutive star
#align has_involutive_star InvolutiveStar

export InvolutiveStar (star_involutive)

@[simp]
theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r :=
  star_involutive _
#align star_star star_star

theorem star_injective [InvolutiveStar R] : Function.Injective (star : R → R) :=
  Function.Involutive.injective star_involutive
#align star_injective star_injective

@[simp]
theorem star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y :=
  star_injective.eq_iff
#align star_inj star_inj

/-- `star` as an equivalence when it is involutive. -/
protected def Equiv.star [InvolutiveStar R] : Equiv.Perm R :=
  star_involutive.toPerm _
#align equiv.star Equiv.star

theorem eq_star_of_eq_star [InvolutiveStar R] {r s : R} (h : r = star s) : s = star r := by
  simp [h]
#align eq_star_of_eq_star eq_star_of_eq_star

theorem eq_star_iff_eq_star [InvolutiveStar R] {r s : R} : r = star s ↔ s = star r :=
  ⟨eq_star_of_eq_star, eq_star_of_eq_star⟩
#align eq_star_iff_eq_star eq_star_iff_eq_star

theorem star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : star r = s ↔ star s = r :=
  eq_comm.trans <| eq_star_iff_eq_star.trans eq_comm
#align star_eq_iff_star_eq star_eq_iff_star_eq

/-- Typeclass for a trivial star operation. This is mostly meant for `ℝ`.
-/
class TrivialStar (R : Type u) [Star R] : Prop where
  /-- Condition that star is trivial-/
  star_trivial : ∀ r : R, star r = r
#align has_trivial_star TrivialStar

export TrivialStar (star_trivial)

attribute [simp] star_trivial

/-- A `*`-magma is a magma `R` with an involutive operation `star`
such that `star (r * s) = star s * star r`.
-/
class StarMul (R : Type u) [Mul R] extends InvolutiveStar R where
  /-- `star` skew-distributes over multiplication. -/
  star_mul : ∀ r s : R, star (r * s) = star s * star r
#align star_semigroup StarMul

export StarMul (star_mul)

attribute [simp 900] star_mul

section StarMul

variable [Mul R] [StarMul R]

theorem star_star_mul (x y : R) : star (star x * y) = star y * x := by rw [star_mul, star_star]
#align star_star_mul star_star_mul

theorem star_mul_star (x y : R) : star (x * star y) = y * star x := by rw [star_mul, star_star]
#align star_mul_star star_mul_star

@[simp]
theorem semiconjBy_star_star_star {x y z : R} :
    SemiconjBy (star x) (star z) (star y) ↔ SemiconjBy x y z := by
  simp_rw [SemiconjBy, ← star_mul, star_inj, eq_comm]
#align semiconj_by_star_star_star semiconjBy_star_star_star

alias ⟨_, SemiconjBy.star_star_star⟩ := semiconjBy_star_star_star
#align semiconj_by.star_star_star SemiconjBy.star_star_star

@[simp]
theorem commute_star_star {x y : R} : Commute (star x) (star y) ↔ Commute x y :=
  semiconjBy_star_star_star
#align commute_star_star commute_star_star

alias ⟨_, Commute.star_star⟩ := commute_star_star
#align commute.star_star Commute.star_star

theorem commute_star_comm {x y : R} : Commute (star x) y ↔ Commute x (star y) := by
  rw [← commute_star_star, star_star]
#align commute_star_comm commute_star_comm

end StarMul

/-- In a commutative ring, make `simp` prefer leaving the order unchanged. -/
@[simp]
theorem star_mul' [CommSemigroup R] [StarMul R] (x y : R) : star (x * y) = star x * star y :=
  (star_mul x y).trans (mul_comm _ _)
#align star_mul' star_mul'

/-- `star` as a `MulEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starMulEquiv [Mul R] [StarMul R] : R ≃* Rᵐᵒᵖ :=
  { (InvolutiveStar.star_involutive.toPerm star).trans opEquiv with
    toFun := fun x => MulOpposite.op (star x)
    map_mul' := fun x y => by simp only [star_mul, op_mul] }
#align star_mul_equiv starMulEquiv
#align star_mul_equiv_apply starMulEquiv_apply

/-- `star` as a `MulAut` for commutative `R`. -/
@[simps apply]
def starMulAut [CommSemigroup R] [StarMul R] : MulAut R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_mul' := star_mul' }
#align star_mul_aut starMulAut
#align star_mul_aut_apply starMulAut_apply

variable (R)

@[simp]
theorem star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1 :=
  op_injective <| (starMulEquiv : R ≃* Rᵐᵒᵖ).map_one.trans op_one.symm
#align star_one star_one

variable {R}

@[simp]
theorem star_pow [Monoid R] [StarMul R] (x : R) (n : ℕ) : star (x ^ n) = star x ^ n :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_pow x n).trans (op_pow (star x) n).symm
#align star_pow star_pow

@[simp]
theorem star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_inv x).trans (op_inv (star x)).symm
#align star_inv star_inv

@[simp]
theorem star_zpow [Group R] [StarMul R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <|
    ((starMulEquiv : R ≃* Rᵐᵒᵖ).toMonoidHom.map_zpow x z).trans (op_zpow (star x) z).symm
#align star_zpow star_zpow

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div [CommGroup R] [StarMul R] (x y : R) : star (x / y) = star x / star y :=
  map_div (starMulAut : R ≃* R) _ _
#align star_div star_div

/-- Any commutative monoid admits the trivial `*`-structure.

See note [reducible non-instances].
-/
abbrev starMulOfComm {R : Type*} [CommMonoid R] : StarMul R where
  star := id
  star_involutive _ := rfl
  star_mul := mul_comm
#align star_semigroup_of_comm starMulOfComm

section

attribute [local instance] starMulOfComm

/-- Note that since `starMulOfComm` is reducible, `simp` can already prove this. -/
theorem star_id_of_comm {R : Type*} [CommSemiring R] {x : R} : star x = x :=
  rfl
#align star_id_of_comm star_id_of_comm

end

/-- A `*`-additive monoid `R` is an additive monoid with an involutive `star` operation which
preserves addition.  -/
class StarAddMonoid (R : Type u) [AddMonoid R] extends InvolutiveStar R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_add_monoid StarAddMonoid

export StarAddMonoid (star_add)

attribute [simp] star_add

/-- `star` as an `AddEquiv` -/
@[simps apply]
def starAddEquiv [AddMonoid R] [StarAddMonoid R] : R ≃+ R :=
  { InvolutiveStar.star_involutive.toPerm star with
    toFun := star
    map_add' := star_add }
#align star_add_equiv starAddEquiv
#align star_add_equiv_apply starAddEquiv_apply

variable (R)

@[simp]
theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 :=
  (starAddEquiv : R ≃+ R).map_zero
#align star_zero star_zero

variable {R}

@[simp]
theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 :=
  starAddEquiv.map_eq_zero_iff (M := R)
#align star_eq_zero star_eq_zero

theorem star_ne_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x ≠ 0 ↔ x ≠ 0 := by
  simp only [ne_eq, star_eq_zero]
#align star_ne_zero star_ne_zero

@[simp]
theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r :=
  (starAddEquiv : R ≃+ R).map_neg _
#align star_neg star_neg

@[simp]
theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s :=
  (starAddEquiv : R ≃+ R).map_sub _ _
#align star_sub star_sub

@[simp]
theorem star_nsmul [AddMonoid R] [StarAddMonoid R] (x : R) (n : ℕ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_nsmul _ _
#align star_nsmul star_nsmul

@[simp]
theorem star_zsmul [AddGroup R] [StarAddMonoid R] (x : R) (n : ℤ) : star (n • x) = n • star x :=
  (starAddEquiv : R ≃+ R).toAddMonoidHom.map_zsmul _ _
#align star_zsmul star_zsmul

/-- A `*`-ring `R` is a non-unital, non-associative (semi)ring with an involutive `star` operation
which is additive which makes `R` with its multiplicative structure into a `*`-multiplication
(i.e. `star (r * s) = star s * star r`).  -/
class StarRing (R : Type u) [NonUnitalNonAssocSemiring R] extends StarMul R where
  /-- `star` commutes with addition -/
  star_add : ∀ r s : R, star (r + s) = star r + star s
#align star_ring StarRing

instance (priority := 100) StarRing.toStarAddMonoid [NonUnitalNonAssocSemiring R] [StarRing R] :
    StarAddMonoid R where
  star_add := StarRing.star_add
#align star_ring.to_star_add_monoid StarRing.toStarAddMonoid

/-- `star` as a `RingEquiv` from `R` to `Rᵐᵒᵖ` -/
@[simps apply]
def starRingEquiv [NonUnitalNonAssocSemiring R] [StarRing R] : R ≃+* Rᵐᵒᵖ :=
  { starAddEquiv.trans (MulOpposite.opAddEquiv : R ≃+ Rᵐᵒᵖ), starMulEquiv with
    toFun := fun x => MulOpposite.op (star x) }
#align star_ring_equiv starRingEquiv
#align star_ring_equiv_apply starRingEquiv_apply

@[simp, norm_cast]
theorem star_natCast [NonAssocSemiring R] [StarRing R] (n : ℕ) : star (n : R) = n :=
  (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)
#align star_nat_cast star_natCast

-- Porting note (#10756): new theorem
@[simp]
theorem star_ofNat [NonAssocSemiring R] [StarRing R] (n : ℕ) [n.AtLeastTwo] :
    star (no_index (OfNat.ofNat n) : R) = OfNat.ofNat n :=
  star_natCast _

section

@[simp, norm_cast]
theorem star_intCast [Ring R] [StarRing R] (z : ℤ) : star (z : R) = z :=
  (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)
#align star_int_cast star_intCast

@[simp, norm_cast]
lemma star_nnratCast [DivisionSemiring R] [StarRing R] (q : ℚ≥0) : star (q : R) = q :=
  (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

@[simp, norm_cast]
theorem star_ratCast [DivisionRing R] [StarRing R] (r : ℚ) : star (r : R) = r :=
  (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)
#align star_rat_cast star_ratCast

end

section CommSemiring
variable [CommSemiring R] [StarRing R]

/-- `star` as a ring automorphism, for commutative `R`. -/
@[simps apply]
def starRingAut : RingAut R := { starAddEquiv, starMulAut (R := R) with toFun := star }
#align star_ring_aut starRingAut
#align star_ring_aut_apply starRingAut_apply

variable (R)

/-- `star` as a ring endomorphism, for commutative `R`. This is used to denote complex
conjugation, and is available under the notation `conj` in the locale `ComplexConjugate`.

Note that this is the preferred form (over `starRingAut`, available under the same hypotheses)
because the notation `E →ₗ⋆[R] F` for an `R`-conjugate-linear map (short for
`E →ₛₗ[starRingEnd R] F`) does not pretty-print if there is a coercion involved, as would be the
case for `(↑starRingAut : R →* R)`. -/
def starRingEnd : R →+* R := @starRingAut R _ _
#align star_ring_end starRingEnd

variable {R}

@[inherit_doc]
scoped[ComplexConjugate] notation "conj" => starRingEnd _

/-- This is not a simp lemma, since we usually want simp to keep `starRingEnd` bundled.
 For example, for complex conjugation, we don't want simp to turn `conj x`
 into the bare function `star x` automatically since most lemmas are about `conj x`. -/
theorem starRingEnd_apply (x : R) : starRingEnd R x = star x := rfl
#align star_ring_end_apply starRingEnd_apply

/- Porting note (#11119): removed `simp` attribute due to report by linter:

simp can prove this:
  by simp only [RingHomCompTriple.comp_apply, RingHom.id_apply]
One of the lemmas above could be a duplicate.
If that's not the case try reordering lemmas or adding @[priority].
 -/
-- @[simp]
theorem starRingEnd_self_apply (x : R) : starRingEnd R (starRingEnd R x) = x := star_star x
#align star_ring_end_self_apply starRingEnd_self_apply

instance RingHom.involutiveStar {S : Type*} [NonAssocSemiring S] : InvolutiveStar (S →+* R) where
  toStar := { star := fun f => RingHom.comp (starRingEnd R) f }
  star_involutive := by
    intro
    ext
    simp only [RingHom.coe_comp, Function.comp_apply, starRingEnd_self_apply]
#align ring_hom.has_involutive_star RingHom.involutiveStar

theorem RingHom.star_def {S : Type*} [NonAssocSemiring S] (f : S →+* R) :
    Star.star f = RingHom.comp (starRingEnd R) f := rfl
#align ring_hom.star_def RingHom.star_def

theorem RingHom.star_apply {S : Type*} [NonAssocSemiring S] (f : S →+* R) (s : S) :
    star f s = star (f s) := rfl
#align ring_hom.star_apply RingHom.star_apply

-- A more convenient name for complex conjugation
alias Complex.conj_conj := starRingEnd_self_apply
#align complex.conj_conj Complex.conj_conj

alias RCLike.conj_conj := starRingEnd_self_apply
set_option linter.uppercaseLean3 false in
#align is_R_or_C.conj_conj RCLike.conj_conj

open scoped ComplexConjugate

@[simp] lemma conj_trivial [TrivialStar R] (a : R) : conj a = a := star_trivial _

end CommSemiring

@[simp]
theorem star_inv' [DivisionSemiring R] [StarRing R] (x : R) : star x⁻¹ = (star x)⁻¹ :=
  op_injective <| (map_inv₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x).trans (op_inv (star x)).symm
#align star_inv' star_inv'

@[simp]
theorem star_zpow₀ [DivisionSemiring R] [StarRing R] (x : R) (z : ℤ) : star (x ^ z) = star x ^ z :=
  op_injective <| (map_zpow₀ (starRingEquiv : R ≃+* Rᵐᵒᵖ) x z).trans (op_zpow (star x) z).symm
#align star_zpow₀ star_zpow₀

/-- When multiplication is commutative, `star` preserves division. -/
@[simp]
theorem star_div' [Semifield R] [StarRing R] (x y : R) : star (x / y) = star x / star y := by
  apply op_injective
  rw [division_def, op_div, mul_comm, star_mul, star_inv', op_mul, op_inv]
#align star_div' star_div'

#noalign star_bit0
#noalign star_bit1

/-- Any commutative semiring admits the trivial `*`-structure.

See note [reducible non-instances].
-/
abbrev starRingOfComm {R : Type*} [CommSemiring R] : StarRing R :=
  { starMulOfComm with
    star_add := fun _ _ => rfl }
#align star_ring_of_comm starRingOfComm

instance Nat.instStarRing : StarRing ℕ := starRingOfComm
instance Int.instStarRing : StarRing ℤ := starRingOfComm
instance Rat.instStarRing : StarRing ℚ := starRingOfComm
instance NNRat.instStarRing : StarRing ℚ≥0 := starRingOfComm
instance Nat.instTrivialStar : TrivialStar ℕ := ⟨fun _ ↦ rfl⟩
instance Int.instTrivialStar : TrivialStar ℤ := ⟨fun _ ↦ rfl⟩
instance Rat.instTrivialStar : TrivialStar ℚ := ⟨fun _ ↦ rfl⟩
instance NNRat.instTrivialStar : TrivialStar ℚ≥0 := ⟨fun _ ↦ rfl⟩

/-- A star module `A` over a star ring `R` is a module which is a star add monoid,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.

Note that it is up to the user of this typeclass to enforce
`[Semiring R] [StarRing R] [AddCommMonoid A] [StarAddMonoid A] [Module R A]`, and that
the statement only requires `[Star R] [Star A] [SMul R A]`.

If used as `[CommRing R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]`, this represents a
star algebra.
-/

class StarModule (R : Type u) (A : Type v) [Star R] [Star A] [SMul R A] : Prop where
  /-- `star` commutes with scalar multiplication -/
  star_smul : ∀ (r : R) (a : A), star (r • a) = star r • star a
#align star_module StarModule

export StarModule (star_smul)

attribute [simp] star_smul

/-- A commutative star monoid is a star module over itself via `Monoid.toMulAction`. -/
instance StarMul.toStarModule [CommMonoid R] [StarMul R] : StarModule R R :=
  ⟨star_mul'⟩
#align star_semigroup.to_star_module StarMul.toStarModule

instance StarAddMonoid.toStarModuleNat {α} [AddCommMonoid α] [StarAddMonoid α] : StarModule ℕ α :=
  ⟨fun n a ↦ by rw [star_nsmul, star_trivial n]⟩

namespace RingHomInvPair

/-- Instance needed to define star-linear maps over a commutative star ring
(ex: conjugate-linear maps when R = ℂ).  -/
instance [CommSemiring R] [StarRing R] : RingHomInvPair (starRingEnd R) (starRingEnd R) :=
  ⟨RingHom.ext star_star, RingHom.ext star_star⟩

end RingHomInvPair

section

/-- `StarHomClass F R S` states that `F` is a type of `star`-preserving maps from `R` to `S`. -/
class StarHomClass (F : Type*) (R S : outParam Type*) [Star R] [Star S] [FunLike F R S] : Prop where
  /-- the maps preserve star -/
  map_star : ∀ (f : F) (r : R), f (star r) = star (f r)
#align star_hom_class StarHomClass

export StarHomClass (map_star)

end

/-! ### Instances -/


namespace Units

variable [Monoid R] [StarMul R]

instance : StarMul Rˣ where
  star u :=
    { val := star u
      inv := star ↑u⁻¹
      val_inv := (star_mul _ _).symm.trans <| (congr_arg star u.inv_val).trans <| star_one _
      inv_val := (star_mul _ _).symm.trans <| (congr_arg star u.val_inv).trans <| star_one _ }
  star_involutive _ := Units.ext (star_involutive _)
  star_mul _ _ := Units.ext (star_mul _ _)

@[simp]
theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) :=
  rfl
#align units.coe_star Units.coe_star

@[simp]
theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) :=
  rfl
#align units.coe_star_inv Units.coe_star_inv

instance {A : Type*} [Star A] [SMul R A] [StarModule R A] : StarModule Rˣ A :=
  ⟨fun u a => star_smul (u : R) a⟩

end Units

protected theorem IsUnit.star [Monoid R] [StarMul R] {a : R} : IsUnit a → IsUnit (star a)
  | ⟨u, hu⟩ => ⟨Star.star u, hu ▸ rfl⟩
#align is_unit.star IsUnit.star

@[simp]
theorem isUnit_star [Monoid R] [StarMul R] {a : R} : IsUnit (star a) ↔ IsUnit a :=
  ⟨fun h => star_star a ▸ h.star, IsUnit.star⟩
#align is_unit_star isUnit_star

theorem Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
    Ring.inverse (star a) = star (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [Ring.inverse_unit, ← Units.coe_star, Ring.inverse_unit, ← Units.coe_star_inv]
  rw [Ring.inverse_non_unit _ ha, Ring.inverse_non_unit _ (mt isUnit_star.mp ha), star_zero]
#align ring.inverse_star Ring.inverse_star

protected instance Invertible.star {R : Type*} [MulOneClass R] [StarMul R] (r : R) [Invertible r] :
    Invertible (star r) where
  invOf := Star.star (⅟ r)
  invOf_mul_self := by rw [← star_mul, mul_invOf_self, star_one]
  mul_invOf_self := by rw [← star_mul, invOf_mul_self, star_one]
#align invertible.star Invertible.star

theorem star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Invertible r]
    [Invertible (star r)] : star (⅟ r) = ⅟ (star r) := by
  have : star (⅟ r) = star (⅟ r) * ((star r) * ⅟ (star r)) := by
    simp only [mul_invOf_self, mul_one]
  rw [this, ← mul_assoc]
  have : (star (⅟ r)) * (star r) = star 1 := by rw [← star_mul, mul_invOf_self]
  rw [this, star_one, one_mul]
#align star_inv_of star_invOf


section Regular

protected theorem IsLeftRegular.star [Mul R] [StarMul R] {x : R} (hx : IsLeftRegular x) :
    IsRightRegular (star x) :=
  fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h

protected theorem IsRightRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRightRegular x) :
    IsLeftRegular (star x) :=
  fun a b h => star_injective <| hx <| by simpa using congr_arg Star.star h

protected theorem IsRegular.star [Mul R] [StarMul R] {x : R} (hx : IsRegular x) :
    IsRegular (star x) :=
  ⟨hx.right.star, hx.left.star⟩

@[simp]
theorem isRightRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRightRegular (star x) ↔ IsLeftRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
theorem isLeftRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsLeftRegular (star x) ↔ IsRightRegular x :=
  ⟨fun h => star_star x ▸ h.star, (·.star)⟩

@[simp]
theorem isRegular_star_iff [Mul R] [StarMul R] {x : R} :
    IsRegular (star x) ↔ IsRegular x := by
  rw [isRegular_iff, isRegular_iff, isRightRegular_star_iff, isLeftRegular_star_iff, and_comm]

end Regular


namespace MulOpposite

/-- The opposite type carries the same star operation. -/
instance [Star R] : Star Rᵐᵒᵖ where star r := op (star r.unop)

@[simp]
theorem unop_star [Star R] (r : Rᵐᵒᵖ) : unop (star r) = star (unop r) :=
  rfl
#align mul_opposite.unop_star MulOpposite.unop_star

@[simp]
theorem op_star [Star R] (r : R) : op (star r) = star (op r) :=
  rfl
#align mul_opposite.op_star MulOpposite.op_star

instance [InvolutiveStar R] : InvolutiveStar Rᵐᵒᵖ where
  star_involutive r := unop_injective (star_star r.unop)

instance [Mul R] [StarMul R] : StarMul Rᵐᵒᵖ where
  star_mul x y := unop_injective (star_mul y.unop x.unop)

instance [AddMonoid R] [StarAddMonoid R] : StarAddMonoid Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

instance [Semiring R] [StarRing R] : StarRing Rᵐᵒᵖ where
  star_add x y := unop_injective (star_add x.unop y.unop)

end MulOpposite

/-- A commutative star monoid is a star module over its opposite via
`Monoid.toOppositeMulAction`. -/
instance StarSemigroup.toOpposite_starModule [CommMonoid R] [StarMul R] :
    StarModule Rᵐᵒᵖ R :=
  ⟨fun r s => star_mul' s r.unop⟩
#align star_semigroup.to_opposite_star_module StarSemigroup.toOpposite_starModule
