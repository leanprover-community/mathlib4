/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module data.real.basic
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Bounds
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Algebra.Star.Basic
import Mathbin.Data.Real.CauSeqCompletion

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.
-/


assert_not_exists finset

assert_not_exists Module

assert_not_exists Submonoid

open Pointwise

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where of_cauchy ::
  cauchy : CauSeq.Completion.CauchyCat (abs : ℚ → ℚ)
#align real Real

-- mathport name: exprℝ
notation "ℝ" => Real

attribute [pp_using_anonymous_constructor] Real

namespace CauSeq.Completion

-- this can't go in `data.real.cau_seq_completion` as the structure on `rat` isn't available
@[simp]
theorem of_rat_rat {abv : ℚ → ℚ} [IsAbsoluteValue abv] (q : ℚ) :
    ofRat (q : ℚ) = (q : @CauchyCat _ _ _ _ abv _) :=
  rfl
#align cau_seq.completion.of_rat_rat CauSeq.Completion.of_rat_rat

end CauSeq.Completion

namespace Real

open CauSeq CauSeq.Completion

variable {x y : ℝ}

theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by constructor <;> cc
#align real.ext_cauchy_iff Real.ext_cauchy_iff

theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2
#align real.ext_cauchy Real.ext_cauchy

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equivCauchy : ℝ ≃ CauSeq.Completion.CauchyCat abs :=
  ⟨Real.cauchy, Real.of_cauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩
#align real.equiv_Cauchy Real.equivCauchy

-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
private irreducible_def zero : ℝ :=
  ⟨0⟩
#align real.zero real.zero

private irreducible_def one : ℝ :=
  ⟨1⟩
#align real.one real.one

private irreducible_def add : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩
#align real.add real.add

private irreducible_def neg : ℝ → ℝ
  | ⟨a⟩ => ⟨-a⟩
#align real.neg real.neg

private irreducible_def mul : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩
#align real.mul real.mul

private noncomputable irreducible_def inv' : ℝ → ℝ
  | ⟨a⟩ => ⟨a⁻¹⟩
#align real.inv' real.inv'

instance : Zero ℝ :=
  ⟨zero⟩

instance : One ℝ :=
  ⟨one⟩

instance : Add ℝ :=
  ⟨add⟩

instance : Neg ℝ :=
  ⟨neg⟩

instance : Mul ℝ :=
  ⟨mul⟩

instance : Sub ℝ :=
  ⟨fun a b => a + -b⟩

noncomputable instance : Inv ℝ :=
  ⟨inv'⟩

theorem of_cauchy_zero : (⟨0⟩ : ℝ) = 0 :=
  show _ = zero by rw [zero]
#align real.of_cauchy_zero Real.of_cauchy_zero

theorem of_cauchy_one : (⟨1⟩ : ℝ) = 1 :=
  show _ = one by rw [one]
#align real.of_cauchy_one Real.of_cauchy_one

theorem of_cauchy_add (a b) : (⟨a + b⟩ : ℝ) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add]
#align real.of_cauchy_add Real.of_cauchy_add

theorem of_cauchy_neg (a) : (⟨-a⟩ : ℝ) = -⟨a⟩ :=
  show _ = neg _ by rw [neg]
#align real.of_cauchy_neg Real.of_cauchy_neg

theorem of_cauchy_sub (a b) : (⟨a - b⟩ : ℝ) = ⟨a⟩ - ⟨b⟩ :=
  by
  rw [sub_eq_add_neg, of_cauchy_add, of_cauchy_neg]
  rfl
#align real.of_cauchy_sub Real.of_cauchy_sub

theorem of_cauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ :=
  show _ = mul _ _ by rw [mul]
#align real.of_cauchy_mul Real.of_cauchy_mul

theorem of_cauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by rw [inv']
#align real.of_cauchy_inv Real.of_cauchy_inv

theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  show zero.cauchy = 0 by rw [zero]
#align real.cauchy_zero Real.cauchy_zero

theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  show one.cauchy = 1 by rw [one]
#align real.cauchy_one Real.cauchy_one

theorem cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (add _ _).cauchy = _ by rw [add]
#align real.cauchy_add Real.cauchy_add

theorem cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
  | ⟨a⟩ => show (neg _).cauchy = _ by rw [neg]
#align real.cauchy_neg Real.cauchy_neg

theorem cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (mul _ _).cauchy = _ by rw [mul]
#align real.cauchy_mul Real.cauchy_mul

theorem cauchy_sub : ∀ a b, (a - b : ℝ).cauchy = a.cauchy - b.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    rw [sub_eq_add_neg, ← cauchy_neg, ← cauchy_add]
    rfl
#align real.cauchy_sub Real.cauchy_sub

theorem cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
  | ⟨f⟩ => show (inv' _).cauchy = _ by rw [inv']
#align real.cauchy_inv Real.cauchy_inv

instance : NatCast ℝ where natCast n := ⟨n⟩

instance : IntCast ℝ where intCast z := ⟨z⟩

instance : RatCast ℝ where ratCast q := ⟨q⟩

theorem of_cauchy_nat_cast (n : ℕ) : (⟨n⟩ : ℝ) = n :=
  rfl
#align real.of_cauchy_nat_cast Real.of_cauchy_nat_cast

theorem of_cauchy_int_cast (z : ℤ) : (⟨z⟩ : ℝ) = z :=
  rfl
#align real.of_cauchy_int_cast Real.of_cauchy_int_cast

theorem of_cauchy_rat_cast (q : ℚ) : (⟨q⟩ : ℝ) = q :=
  rfl
#align real.of_cauchy_rat_cast Real.of_cauchy_rat_cast

theorem cauchy_nat_cast (n : ℕ) : (n : ℝ).cauchy = n :=
  rfl
#align real.cauchy_nat_cast Real.cauchy_nat_cast

theorem cauchy_int_cast (z : ℤ) : (z : ℝ).cauchy = z :=
  rfl
#align real.cauchy_int_cast Real.cauchy_int_cast

theorem cauchy_rat_cast (q : ℚ) : (q : ℝ).cauchy = q :=
  rfl
#align real.cauchy_rat_cast Real.cauchy_rat_cast

instance : CommRing ℝ := by
  refine_struct
            { Real.hasNatCast,
              Real.hasIntCast with
              zero := (0 : ℝ)
              one := (1 : ℝ)
              mul := (· * ·)
              add := (· + ·)
              neg := @Neg.neg ℝ _
              sub := @Sub.sub ℝ _
              npow := @npowRec ℝ ⟨1⟩ ⟨(· * ·)⟩
              nsmul := @nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩
              zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩ } <;>
          repeat' rintro ⟨_⟩ <;>
        try rfl <;>
      simp [← of_cauchy_zero, ← of_cauchy_one, ← of_cauchy_add, ← of_cauchy_neg, ← of_cauchy_mul,
        fun n => show @coe ℕ ℝ ⟨_⟩ n = ⟨n⟩ from rfl, NatCast.natCast, IntCast.intCast] <;>
    first
      |apply
        add_assoc|apply
        add_comm|apply
        mul_assoc|apply mul_comm|apply left_distrib|apply right_distrib|apply sub_eq_add_neg|skip

/-- `real.equiv_Cauchy` as a ring equivalence. -/
@[simps]
def ringEquivCauchy : ℝ ≃+* CauSeq.Completion.CauchyCat abs :=
  { equivCauchy with
    toFun := cauchy
    invFun := of_cauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }
#align real.ring_equiv_Cauchy Real.ringEquivCauchy

/-! Extra instances to short-circuit type class resolution.

 These short-circuits have an additional property of ensuring that a computable path is found; if
 `field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
 version of them. -/


instance : Ring ℝ := by infer_instance

instance : CommSemiring ℝ := by infer_instance

instance : Semiring ℝ := by infer_instance

instance : CommMonoidWithZero ℝ := by infer_instance

instance : MonoidWithZero ℝ := by infer_instance

instance : AddCommGroup ℝ := by infer_instance

instance : AddGroup ℝ := by infer_instance

instance : AddCommMonoid ℝ := by infer_instance

instance : AddMonoid ℝ := by infer_instance

instance : AddLeftCancelSemigroup ℝ := by infer_instance

instance : AddRightCancelSemigroup ℝ := by infer_instance

instance : AddCommSemigroup ℝ := by infer_instance

instance : AddSemigroup ℝ := by infer_instance

instance : CommMonoid ℝ := by infer_instance

instance : Monoid ℝ := by infer_instance

instance : CommSemigroup ℝ := by infer_instance

instance : Semigroup ℝ := by infer_instance

instance : Inhabited ℝ :=
  ⟨0⟩

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance : StarRing ℝ :=
  starRingOfComm

instance : TrivialStar ℝ :=
  ⟨fun _ => rfl⟩

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : CauSeq ℚ abs) : ℝ :=
  ⟨CauSeq.Completion.mk x⟩
#align real.mk Real.mk

theorem mk_eq {f g : CauSeq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans mk_eq
#align real.mk_eq Real.mk_eq

private irreducible_def lt : ℝ → ℝ → Prop
  | ⟨x⟩, ⟨y⟩ =>
    (Quotient.liftOn₂ x y (· < ·)) fun f₁ g₁ f₂ g₂ hf hg =>
      propext <|
        ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩
#align real.lt real.lt

instance : LT ℝ :=
  ⟨Lt⟩

theorem lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g :=
  show Lt _ _ ↔ _ by rw [lt] <;> rfl
#align real.lt_cauchy Real.lt_cauchy

@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy
#align real.mk_lt Real.mk_lt

theorem mk_zero : mk 0 = 0 := by rw [← of_cauchy_zero] <;> rfl
#align real.mk_zero Real.mk_zero

theorem mk_one : mk 1 = 1 := by rw [← of_cauchy_one] <;> rfl
#align real.mk_one Real.mk_one

theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, ← of_cauchy_add]
#align real.mk_add Real.mk_add

theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, ← of_cauchy_mul]
#align real.mk_mul Real.mk_mul

theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by simp [mk, ← of_cauchy_neg]
#align real.mk_neg Real.mk_neg

@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt] <;> exact iff_of_eq (congr_arg Pos (sub_zero f))
#align real.mk_pos Real.mk_pos

private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y
#align real.le real.le

instance : LE ℝ :=
  ⟨Le⟩

private theorem le_def {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  show Le _ _ ↔ _ by rw [le]
#align real.le_def real.le_def

@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by simp [le_def, mk_eq] <;> rfl
#align real.mk_le Real.mk_le

@[elab_as_elim]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x :=
  by
  cases' x with x
  induction' x using Quot.induction_on with x
  exact h x
#align real.ind_mk Real.ind_mk

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b :=
  by
  induction a using Real.ind_mk
  induction b using Real.ind_mk
  induction c using Real.ind_mk
  simp only [mk_lt, ← mk_add]
  show Pos _ ↔ Pos _; rw [add_sub_add_left_eq_sub]
#align real.add_lt_add_iff_left Real.add_lt_add_iff_left

instance : PartialOrder ℝ where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b :=
    (Real.ind_mk a) fun a => (Real.ind_mk b) fun b => by simpa using lt_iff_le_not_le
  le_refl a := a.ind_mk (by intro a <;> rw [mk_le])
  le_trans a b c :=
    (Real.ind_mk a) fun a =>
      (Real.ind_mk b) fun b => (Real.ind_mk c) fun c => by simpa using le_trans
  lt_iff_le_not_le a b :=
    (Real.ind_mk a) fun a => (Real.ind_mk b) fun b => by simpa using lt_iff_le_not_le
  le_antisymm a b :=
    (Real.ind_mk a) fun a =>
      (Real.ind_mk b) fun b => by simpa [mk_eq] using @CauSeq.le_antisymm _ _ a b

instance : Preorder ℝ := by infer_instance

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { md := tactic.transparency.semireducible[tactic.transparency.semireducible] } -/
theorem rat_cast_lt {x y : ℚ} : (x : ℝ) < (y : ℝ) ↔ x < y :=
  by
  rw [mk_lt]
  exact const_lt
#align real.rat_cast_lt Real.rat_cast_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 := by
  convert rat_cast_lt.2 zero_lt_one <;> simp [← of_cauchy_rat_cast, of_cauchy_one, of_cauchy_zero]
#align real.zero_lt_one Real.zero_lt_one

protected theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨Real.zero_lt_one⟩
#align real.fact_zero_lt_one Real.fact_zero_lt_one

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
  by
  induction' a using Real.ind_mk with a
  induction' b using Real.ind_mk with b
  simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos
#align real.mul_pos Real.mul_pos

instance : StrictOrderedCommRing ℝ :=
  { Real.commRing, Real.partialOrder,
    Real.semiring with
    exists_pair_ne := ⟨0, 1, Real.zero_lt_one.Ne⟩
    add_le_add_left := by
      simp only [le_iff_eq_or_lt]
      rintro a b ⟨rfl, h⟩
      · simp
      · exact fun c => Or.inr ((add_lt_add_iff_left c).2 ‹_›)
    zero_le_one := le_of_lt Real.zero_lt_one
    mul_pos := @Real.mul_pos }

instance : StrictOrderedRing ℝ :=
  inferInstance

instance : StrictOrderedCommSemiring ℝ :=
  inferInstance

instance : StrictOrderedSemiring ℝ :=
  inferInstance

instance : OrderedRing ℝ :=
  inferInstance

instance : OrderedSemiring ℝ :=
  inferInstance

instance : OrderedAddCommGroup ℝ :=
  inferInstance

instance : OrderedCancelAddCommMonoid ℝ :=
  inferInstance

instance : OrderedAddCommMonoid ℝ :=
  inferInstance

instance : Nontrivial ℝ :=
  inferInstance

private irreducible_def sup : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊔ ·) (fun x₁ x₂ hx y₁ y₂ hy => sup_equiv_sup hx hy) x y⟩
#align real.sup real.sup

instance : HasSup ℝ :=
  ⟨sup⟩

theorem of_cauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩ :=
  show _ = sup _ _ by
    rw [sup]
    rfl
#align real.of_cauchy_sup Real.of_cauchy_sup

@[simp]
theorem mk_sup (a b) : (mk (a ⊔ b) : ℝ) = mk a ⊔ mk b :=
  of_cauchy_sup _ _
#align real.mk_sup Real.mk_sup

private irreducible_def inf : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊓ ·) (fun x₁ x₂ hx y₁ y₂ hy => inf_equiv_inf hx hy) x y⟩
#align real.inf real.inf

instance : HasInf ℝ :=
  ⟨inf⟩

theorem of_cauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩ :=
  show _ = inf _ _ by
    rw [inf]
    rfl
#align real.of_cauchy_inf Real.of_cauchy_inf

@[simp]
theorem mk_inf (a b) : (mk (a ⊓ b) : ℝ) = mk a ⊓ mk b :=
  of_cauchy_inf _ _
#align real.mk_inf Real.mk_inf

instance : DistribLattice ℝ :=
  { Real.partialOrder with
    sup := (· ⊔ ·)
    le := (· ≤ ·)
    le_sup_left := fun a =>
      (Real.ind_mk a) fun a b =>
        (Real.ind_mk b) fun b => by
          rw [← mk_sup, mk_le]
          exact CauSeq.le_sup_left
    le_sup_right := fun a =>
      (Real.ind_mk a) fun a b =>
        (Real.ind_mk b) fun b => by
          rw [← mk_sup, mk_le]
          exact CauSeq.le_sup_right
    sup_le := fun a =>
      (Real.ind_mk a) fun a b =>
        (Real.ind_mk b) fun b c =>
          (Real.ind_mk c) fun c => by
            simp_rw [← mk_sup, mk_le]
            exact CauSeq.sup_le
    inf := (· ⊓ ·)
    inf_le_left := fun a =>
      (Real.ind_mk a) fun a b =>
        (Real.ind_mk b) fun b => by
          rw [← mk_inf, mk_le]
          exact CauSeq.inf_le_left
    inf_le_right := fun a =>
      (Real.ind_mk a) fun a b =>
        (Real.ind_mk b) fun b => by
          rw [← mk_inf, mk_le]
          exact CauSeq.inf_le_right
    le_inf := fun a =>
      (Real.ind_mk a) fun a b =>
        (Real.ind_mk b) fun b c =>
          (Real.ind_mk c) fun c => by
            simp_rw [← mk_inf, mk_le]
            exact CauSeq.le_inf
    le_sup_inf := fun a =>
      (Real.ind_mk a) fun a b =>
        (Real.ind_mk b) fun b c =>
          (Real.ind_mk c) fun c =>
            Eq.le
              (by
                simp only [← mk_sup, ← mk_inf]
                exact congr_arg mk (CauSeq.sup_inf_distrib_left _ _ _).symm) }

-- Extra instances to short-circuit type class resolution
instance : Lattice ℝ :=
  inferInstance

instance : SemilatticeInf ℝ :=
  inferInstance

instance : SemilatticeSup ℝ :=
  inferInstance

open Classical

instance : IsTotal ℝ (· ≤ ·) :=
  ⟨fun a => (Real.ind_mk a) fun a b => (Real.ind_mk b) fun b => by simpa using le_total a b⟩

noncomputable instance : LinearOrder ℝ :=
  Lattice.toLinearOrder _

noncomputable instance : LinearOrderedCommRing ℝ :=
  { Real.nontrivial, Real.strictOrderedRing, Real.commRing, Real.linearOrder with }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedRing ℝ := by infer_instance

noncomputable instance : LinearOrderedSemiring ℝ := by infer_instance

instance : IsDomain ℝ :=
  { Real.nontrivial, Real.commRing, LinearOrderedRing.isDomain with }

noncomputable instance : LinearOrderedField ℝ :=
  { Real.linearOrderedCommRing with
    inv := Inv.inv
    mul_inv_cancel := by
      rintro ⟨a⟩ h
      rw [mul_comm]
      simp only [← of_cauchy_inv, ← of_cauchy_mul, ← of_cauchy_one, ← of_cauchy_zero, Ne.def] at *
      exact CauSeq.Completion.inv_mul_cancel h
    inv_zero := by simp [← of_cauchy_zero, ← of_cauchy_inv]
    ratCast := coe
    rat_cast_mk := fun n d hd h2 => by
      rw [← of_cauchy_rat_cast, Rat.cast_mk', of_cauchy_mul, of_cauchy_inv, of_cauchy_nat_cast,
        of_cauchy_int_cast] }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedAddCommGroup ℝ := by infer_instance

noncomputable instance field : Field ℝ := by infer_instance
#align real.field Real.field

noncomputable instance : DivisionRing ℝ := by infer_instance

noncomputable instance decidableLt (a b : ℝ) : Decidable (a < b) := by infer_instance
#align real.decidable_lt Real.decidableLt

noncomputable instance decidableLe (a b : ℝ) : Decidable (a ≤ b) := by infer_instance
#align real.decidable_le Real.decidableLe

noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by infer_instance
#align real.decidable_eq Real.decidableEq

/-- Show an underlying cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `quot.mk`, so two cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr ℝ where repr r := "real.of_cauchy " ++ repr r.cauchy

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { md := tactic.transparency.semireducible[tactic.transparency.semireducible] } -/
theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f :=
  by
  intro h
  induction' x using Real.ind_mk with x
  apply le_of_not_lt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_le (H _ le_rfl).1
  rw [mk_lt]
  refine' ⟨_, half_pos K0, i, fun j ij => _⟩
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
#align real.le_mk_of_forall_le Real.le_mk_of_forall_le

theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) :
    mk f ≤ x := by
  cases' h with i H
  rw [← neg_le_neg_iff, ← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩
#align real.mk_le_of_forall_le Real.mk_le_of_forall_le

theorem mk_near_of_forall_near {f : CauSeq ℚ abs} {x : ℝ} {ε : ℝ}
    (H : ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| ≤ ε) : |mk f - x| ≤ ε :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add'.2 <|
        mk_le_of_forall_le <|
          H.imp fun i h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
      sub_le_comm.1 <|
        le_mk_of_forall_le <| H.imp fun i h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩
#align real.mk_near_of_forall_near Real.mk_near_of_forall_near

instance : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    (Real.ind_mk x) fun f =>
      let ⟨M, M0, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

theorem is_cau_seq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) :=
  ⟨fun H ε ε0 =>
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => lt_trans (by simpa using (@Rat.cast_lt ℝ _ _ _).2 (hi _ ij)) δε,
    fun H ε ε0 =>
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij =>
      (@Rat.cast_lt ℝ _ _ _).1 <| by simpa using hi _ ij⟩
#align real.is_cau_seq_iff_lift Real.is_cau_seq_iff_lift

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨is_cau_seq_iff_lift.2 (of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_le_of_dense (abs_nonneg _)) fun ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun i h j ij => le_of_lt (h j ij)⟩
#align real.of_near Real.of_near

theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  Int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x
    ⟨n, fun z h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x
    ⟨n, le_of_lt hn⟩)
#align real.exists_floor Real.exists_floor

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j k «expr ≥ » «expr⌈ ⌉₊»(«expr ⁻¹»(ε))) -/
theorem exists_is_lub (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x, IsLUB S x :=
  by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ S, (m : ℝ) ≤ y * d } :=
    by
    cases' exists_int_gt U with k hk
    refine' fun d => ⟨k * d, fun z h => _⟩
    rcases h with ⟨y, yS, hy⟩
    refine' Int.cast_le.1 (hy.trans _)
    push_cast
    exact mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg
  choose f hf using fun d : ℕ =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : ∀ n > 0, ∃ y ∈ S, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  have hf₂ : ∀ n > 0, ∀ y ∈ S, (y - (n : ℕ)⁻¹ : ℝ) < (f n / n : ℚ) :=
    by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp [-sub_eq_add_neg]
    rwa [lt_div_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, _root_.inv_mul_cancel]
    exact ne_of_gt (Nat.cast_pos.2 n0)
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) :=
    by
    intro ε ε0
    suffices ∀ (j) (_ : j ≥ ⌈ε⁻¹⌉₊) (k) (_ : k ≥ ⌈ε⁻¹⌉₊), (f j / j - f k / k : ℚ) < ε
      by
      refine' ⟨_, fun j ij => abs_lt.2 ⟨_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt, neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine' lt_of_lt_of_le ((@Rat.cast_lt ℝ _ _ _).1 _) ((inv_le ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩
  refine' ⟨mk g, ⟨fun x xS => _, fun y h => _⟩⟩
  · refine' le_of_forall_ge_of_dense fun z xz => _
    cases' exists_nat_gt (x - z)⁻¹ with K hK
    refine' le_mk_of_forall_le ⟨K, fun n nK => _⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine' le_trans _ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
  ·
    exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩
#align real.exists_is_lub Real.exists_is_lub

noncomputable instance : SupSet ℝ :=
  ⟨fun S => if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_is_lub S h.1 h.2) else 0⟩

theorem Sup_def (S : Set ℝ) :
    supₛ S =
      if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_is_lub S h.1 h.2) else 0 :=
  rfl
#align real.Sup_def Real.Sup_def

protected theorem is_lub_Sup (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddAbove S) : IsLUB S (supₛ S) :=
  by
  simp only [Sup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec
#align real.is_lub_Sup Real.is_lub_Sup

noncomputable instance : InfSet ℝ :=
  ⟨fun S => -supₛ (-S)⟩

theorem Inf_def (S : Set ℝ) : infₛ S = -supₛ (-S) :=
  rfl
#align real.Inf_def Real.Inf_def

protected theorem is_glb_Inf (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddBelow S) : IsGLB S (infₛ S) :=
  by
  rw [Inf_def, ← is_lub_neg', neg_neg]
  exact Real.is_lub_Sup _ h₁.neg h₂.neg
#align real.is_glb_Inf Real.is_glb_Inf

noncomputable instance : ConditionallyCompleteLinearOrder ℝ :=
  { Real.linearOrder, Real.lattice with
    sup := SupSet.supₛ
    inf := InfSet.infₛ
    le_cSup := fun s a hs ha => (Real.is_lub_Sup s ⟨a, ha⟩ hs).1 ha
    cSup_le := fun s a hs ha => (Real.is_lub_Sup s hs ⟨a, ha⟩).2 ha
    cInf_le := fun s a hs ha => (Real.is_glb_Inf s ⟨a, ha⟩ hs).1 ha
    le_cInf := fun s a hs ha => (Real.is_glb_Inf s hs ⟨a, ha⟩).2 ha }

theorem lt_Inf_add_pos {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ s, a < infₛ s + ε :=
  exists_lt_of_cinfₛ_lt h <| lt_add_of_pos_right _ hε
#align real.lt_Inf_add_pos Real.lt_Inf_add_pos

theorem add_neg_lt_Sup {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : ε < 0) :
    ∃ a ∈ s, supₛ s + ε < a :=
  exists_lt_of_lt_csupₛ h <| add_lt_iff_neg_left.2 hε
#align real.add_neg_lt_Sup Real.add_neg_lt_Sup

theorem Inf_le_iff {s : Set ℝ} (h : BddBelow s) (h' : s.Nonempty) {a : ℝ} :
    infₛ s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε :=
  by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_cinfₛ_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact cinfₛ_lt_of_lt h x_in hx
#align real.Inf_le_iff Real.Inf_le_iff

theorem le_Sup_iff {s : Set ℝ} (h : BddAbove s) (h' : s.Nonempty) {a : ℝ} :
    a ≤ supₛ s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x :=
  by
  rw [le_iff_forall_pos_lt_add]
  refine' ⟨fun H ε ε_neg => _, fun H ε ε_pos => _⟩
  · exact exists_lt_of_lt_csupₛ h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csupₛ_of_lt h x_in hx)
#align real.le_Sup_iff Real.le_Sup_iff

@[simp]
theorem Sup_empty : supₛ (∅ : Set ℝ) = 0 :=
  dif_neg <| by simp
#align real.Sup_empty Real.Sup_empty

theorem csupr_empty {α : Sort _} [IsEmpty α] (f : α → ℝ) : (⨆ i, f i) = 0 :=
  by
  dsimp [supᵢ]
  convert Real.Sup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance
#align real.csupr_empty Real.csupr_empty

@[simp]
theorem csupr_const_zero {α : Sort _} : (⨆ i : α, (0 : ℝ)) = 0 :=
  by
  cases isEmpty_or_nonempty α
  · exact Real.csupr_empty _
  · exact csupᵢ_const
#align real.csupr_const_zero Real.csupr_const_zero

theorem Sup_of_not_bdd_above {s : Set ℝ} (hs : ¬BddAbove s) : supₛ s = 0 :=
  dif_neg fun h => hs h.2
#align real.Sup_of_not_bdd_above Real.Sup_of_not_bdd_above

theorem supr_of_not_bdd_above {α : Sort _} {f : α → ℝ} (hf : ¬BddAbove (Set.range f)) :
    (⨆ i, f i) = 0 :=
  Sup_of_not_bdd_above hf
#align real.supr_of_not_bdd_above Real.supr_of_not_bdd_above

theorem Sup_univ : supₛ (@Set.univ ℝ) = 0 :=
  Real.Sup_of_not_bdd_above fun ⟨x, h⟩ => not_le_of_lt (lt_add_one _) <| h (Set.mem_univ _)
#align real.Sup_univ Real.Sup_univ

@[simp]
theorem Inf_empty : infₛ (∅ : Set ℝ) = 0 := by simp [Inf_def, supₛ_empty]
#align real.Inf_empty Real.Inf_empty

theorem cinfi_empty {α : Sort _} [IsEmpty α] (f : α → ℝ) : (⨅ i, f i) = 0 := by
  rw [infᵢ_of_empty', infₛ_empty]
#align real.cinfi_empty Real.cinfi_empty

@[simp]
theorem cinfi_const_zero {α : Sort _} : (⨅ i : α, (0 : ℝ)) = 0 :=
  by
  cases isEmpty_or_nonempty α
  · exact Real.cinfi_empty _
  · exact cinfᵢ_const
#align real.cinfi_const_zero Real.cinfi_const_zero

theorem Inf_of_not_bdd_below {s : Set ℝ} (hs : ¬BddBelow s) : infₛ s = 0 :=
  neg_eq_zero.2 <| Sup_of_not_bdd_above <| mt bdd_above_neg.1 hs
#align real.Inf_of_not_bdd_below Real.Inf_of_not_bdd_below

theorem infi_of_not_bdd_below {α : Sort _} {f : α → ℝ} (hf : ¬BddBelow (Set.range f)) :
    (⨅ i, f i) = 0 :=
  Inf_of_not_bdd_below hf
#align real.infi_of_not_bdd_below Real.infi_of_not_bdd_below

/--
As `0` is the default value for `real.Sup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem Sup_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ supₛ S :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact Sup_empty.ge
  · apply dite _ (fun h => le_csupₛ_of_le h hy <| hS y hy) fun h => (Sup_of_not_bdd_above h).ge
#align real.Sup_nonneg Real.Sup_nonneg

/-- As `0` is the default value for `real.Sup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `Sup S ≤ 0`.
-/
theorem Sup_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : supₛ S ≤ 0 :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts[Sup_empty.le, csupₛ_le hS₂ hS]
#align real.Sup_nonpos Real.Sup_nonpos

/-- As `0` is the default value for `real.Inf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem Inf_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ infₛ S :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts[Inf_empty.ge, le_cinfₛ hS₂ hS]
#align real.Inf_nonneg Real.Inf_nonneg

/--
As `0` is the default value for `real.Inf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `Inf S ≤ 0`.
-/
theorem Inf_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : infₛ S ≤ 0 :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact Inf_empty.le
  · apply dite _ (fun h => cinfₛ_le_of_le h hy <| hS y hy) fun h => (Inf_of_not_bdd_below h).le
#align real.Inf_nonpos Real.Inf_nonpos

theorem Inf_le_Sup (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : infₛ s ≤ supₛ s :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [infₛ_empty, supₛ_empty]
  · exact cinfₛ_le_csupₛ h₁ h₂ hne
#align real.Inf_le_Sup Real.Inf_le_Sup

theorem cau_seq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x :=
  by
  let S := { x : ℝ | const abs x < f }
  have lb : ∃ x, x ∈ S := exists_lt f
  have ub' : ∀ x, f < const abs x → ∀ y ∈ S, y ≤ x := fun x h y yS =>
    le_of_lt <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀ y ∈ S, y ≤ x := (exists_gt f).imp ub'
  refine' ⟨Sup S, ((lt_total _ _).resolve_left fun h => _).resolve_right fun h => _⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine' (csupₛ_le lb (ub' _ _)).not_lt (sub_lt_self _ (half_pos ε0))
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    exact ih _ ij
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine' (le_csupₛ ub _).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
    exact ih _ ij
#align real.cau_seq_converges Real.cau_seq_converges

instance : CauSeq.IsComplete ℝ abs :=
  ⟨cau_seq_converges⟩

end Real

