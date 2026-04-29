/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

import Mathlib.Algebra.Order.CauSeq.Completion
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.

The facts that the real numbers are an Archimedean floor ring,
and a conditionally complete linear order,
have been deferred to the file `Mathlib/Data/Real/Archimedean.lean`,
in order to keep the imports here simple.

The fact that the real numbers are a (trivial) \*-ring has similarly been deferred to
`Mathlib/Data/Real/Star.lean`.
-/

public section


assert_not_exists Finset Module Submonoid FloorRing

/-- The type `ℝ` of real numbers.
It is constructed as equivalence classes of Cauchy sequences of rational numbers. -/
def Real := CauSeq.Completion.Cauchy (abs : ℚ → ℚ)

@[inherit_doc]
notation "ℝ" => Real

namespace Real

open CauSeq CauSeq.Completion

variable {x : ℝ}

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
private def equivCauchy : ℝ ≃ CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  Equiv.refl _

private def ofCauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ) → ℝ :=
  equivCauchy.symm

private def cauchy : ℝ → CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  equivCauchy

private theorem ext_cauchy_iff {x y : Real} : x = y ↔ x.cauchy = y.cauchy := by
  rw [cauchy, equivCauchy.injective.eq_iff]

private theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2

protected def zero : ℝ := equivCauchy.symm 0
protected def one : ℝ := equivCauchy.symm 1
protected def add (a b : ℝ) : ℝ := equivCauchy.symm (equivCauchy a + equivCauchy b)
protected def neg (a : ℝ) : ℝ := equivCauchy.symm (-equivCauchy a)
protected def mul (a b : ℝ) : ℝ := equivCauchy.symm (equivCauchy a * equivCauchy b)
protected noncomputable def inv (a : ℝ) : ℝ := equivCauchy.symm (equivCauchy a)⁻¹

instance : Zero ℝ := ⟨Real.zero⟩
instance : One ℝ := ⟨Real.one⟩
instance : Add ℝ := ⟨Real.add⟩
instance : Neg ℝ := ⟨Real.neg⟩
instance : Mul ℝ := ⟨Real.mul⟩
instance : Sub ℝ := ⟨fun a b ↦ a + (-b)⟩
noncomputable instance : Inv ℝ := ⟨Real.inv⟩

private theorem sub_def (a b : ℝ) : a - b = a + (-b) := rfl

private theorem ofCauchy_zero : (.ofCauchy 0 : ℝ) = 0 :=
  equivCauchy.injective rfl

private theorem ofCauchy_one : (.ofCauchy 1 : ℝ) = 1 :=
  equivCauchy.injective rfl

private theorem ofCauchy_add (a b : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)) :
    (.ofCauchy (a + b) : ℝ) = .ofCauchy a + .ofCauchy b :=
  equivCauchy.injective rfl

private theorem ofCauchy_neg (a : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)) :
    (.ofCauchy (-a) : ℝ) = -(.ofCauchy a) :=
  equivCauchy.injective rfl

private theorem ofCauchy_sub (a b : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)) :
    (.ofCauchy (a - b) : ℝ) = .ofCauchy a - .ofCauchy b := by
  simp only [sub_eq_add_neg, ofCauchy_add, ofCauchy_neg, sub_def]

private theorem ofCauchy_mul (a b : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)) :
    (.ofCauchy (a * b) : ℝ) = .ofCauchy a * .ofCauchy b :=
  equivCauchy.injective rfl

private theorem ofCauchy_inv (a : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)) :
    (.ofCauchy (a⁻¹) : ℝ) = (.ofCauchy a)⁻¹ :=
  equivCauchy.injective rfl

private theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  equivCauchy.apply_symm_apply _

private theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  equivCauchy.apply_symm_apply _

private theorem cauchy_add (a b : ℝ) : (a + b).cauchy = a.cauchy + b.cauchy :=
  equivCauchy.apply_symm_apply _

private theorem cauchy_neg (a : ℝ) : (-a).cauchy = -a.cauchy :=
  equivCauchy.apply_symm_apply _

private theorem cauchy_mul (a b : ℝ) : (a * b).cauchy = a.cauchy * b.cauchy :=
  equivCauchy.apply_symm_apply _

private theorem cauchy_sub (a b : ℝ) : (a - b).cauchy = a.cauchy - b.cauchy := by
  simp only [sub_eq_add_neg, cauchy_add, cauchy_neg, sub_def]

private theorem cauchy_inv (a : ℝ) : (a⁻¹).cauchy = a.cauchy⁻¹ :=
  equivCauchy.apply_symm_apply _

protected def ratCast (q : ℚ) : ℝ := equivCauchy.symm q

instance instRatCast : RatCast ℝ := ⟨Real.ratCast⟩
instance instNatCast : NatCast ℝ := ⟨fun n ↦ (n : ℚ)⟩
instance instIntCast : IntCast ℝ := ⟨fun n ↦ (n : ℚ)⟩
instance instNNRatCast : NNRatCast ℝ := ⟨fun q ↦ (q : ℚ)⟩

private lemma ofCauchy_natCast (n : ℕ) : (ofCauchy n : ℝ) = n := equivCauchy.injective rfl
private lemma ofCauchy_intCast (z : ℤ) : (ofCauchy z : ℝ) = z := equivCauchy.injective rfl
private lemma ofCauchy_nnratCast (q : ℚ≥0) : (ofCauchy q : ℝ) = q := equivCauchy.injective rfl
private lemma ofCauchy_ratCast (q : ℚ) : (ofCauchy q : ℝ) = q := equivCauchy.injective rfl

private lemma cauchy_natCast (n : ℕ) : (n : ℝ).cauchy = n := equivCauchy.apply_symm_apply _
private lemma cauchy_intCast (z : ℤ) : (z : ℝ).cauchy = z := equivCauchy.apply_symm_apply _
private lemma cauchy_nnratCast (q : ℚ≥0) : (q : ℝ).cauchy = q := equivCauchy.apply_symm_apply _
private lemma cauchy_ratCast (q : ℚ) : (q : ℝ).cauchy = q := equivCauchy.apply_symm_apply _

instance commRing : CommRing ℝ where
  npow := @npowRec ℝ ⟨1⟩ ⟨(· * ·)⟩
  nsmul := @nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩ (@nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩)
  add_zero a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  zero_add a := by apply ext_cauchy; simp [cauchy_add, cauchy_zero]
  add_comm a b := by apply ext_cauchy; simp only [cauchy_add, add_comm]
  add_assoc a b c := by apply ext_cauchy; simp only [cauchy_add, add_assoc]
  mul_zero a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  zero_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_zero]
  mul_one a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  one_mul a := by apply ext_cauchy; simp [cauchy_mul, cauchy_one]
  mul_comm a b := by apply ext_cauchy; simp only [cauchy_mul, mul_comm]
  mul_assoc a b c := by apply ext_cauchy; simp only [cauchy_mul, mul_assoc]
  left_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, mul_add]
  right_distrib a b c := by apply ext_cauchy; simp only [cauchy_add, cauchy_mul, add_mul]
  neg_add_cancel a := by apply ext_cauchy; simp [cauchy_add, cauchy_neg, cauchy_zero]
  natCast_zero := by apply ext_cauchy; simp [cauchy_natCast, cauchy_zero]
  natCast_succ n := by apply ext_cauchy; simp [cauchy_natCast, cauchy_one, cauchy_add]
  intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast, cauchy_intCast]

/-! Extra instances to short-circuit type class resolution.

These short-circuits have an additional property of ensuring that a computable path is found; if
`Field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
version of them. -/

instance instRing : Ring ℝ := by infer_instance

instance : CommSemiring ℝ := by infer_instance

instance semiring : Semiring ℝ := by infer_instance

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

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
private def mk (x : CauSeq ℚ abs) : ℝ :=
  CauSeq.Completion.mk x

private theorem mk_eq {f g : CauSeq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans CauSeq.Completion.mk_eq

protected def lt (x y : ℝ) : Prop :=
  (Quotient.liftOn₂ x y (· < ·)) fun _ _ _ _ hf hg ↦
    propext <|
      ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
        lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩

instance : LT ℝ := ⟨Real.lt⟩

@[simp]
private theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  show Real.lt _ _ ↔ _ by rw [Real.lt]; rfl

private theorem mk_zero : mk 0 = 0 := by rw [← ofCauchy_zero]; rfl

private theorem mk_one : mk 1 = 1 := by rw [← ofCauchy_one]; rfl

private theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by
  simp [mk, ← CauSeq.Completion.mk_add]; rfl

private theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by
  simp [mk, ← CauSeq.Completion.mk_mul]; rfl

private theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by
  simp [mk, ← CauSeq.Completion.mk_neg]; rfl

@[simp]
private theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))

private lemma mk_const {x : ℚ} : mk (const abs x) = x := rfl

protected def le (x y : ℝ) : Prop :=
  x < y ∨ x = y

instance : LE ℝ := ⟨Real.le⟩

private theorem le_def' {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  Iff.rfl

@[simp]
private theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by
  simp only [le_def', mk_lt, mk_eq]; rfl

@[elab_as_elim]
private theorem ind_mk {C : ℝ → Prop} (x : ℝ) (h : ∀ y, C (mk y)) : C x := by
  induction x using Quot.induction_on
  exact h _

instance partialOrder : PartialOrder ℝ where
  lt_iff_le_not_ge a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using lt_iff_le_not_ge
  le_refl a := by
    induction a using Real.ind_mk
    rw [mk_le]
  le_trans a b c := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simpa using le_trans
  le_antisymm a b := by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa [mk_eq] using CauSeq.le_antisymm

instance : Preorder ℝ := by infer_instance

theorem ratCast_lt {x y : ℚ} : (x : ℝ) < (y : ℝ) ↔ x < y := by
  rw [← mk_const, ← mk_const, mk_lt]
  exact const_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 :=
  ratCast_lt.2 zero_lt_one

instance instNontrivial : Nontrivial ℝ where
  exists_pair_ne := ⟨0, 1, Real.zero_lt_one.ne⟩

instance instZeroLEOneClass : ZeroLEOneClass ℝ where
  zero_le_one := le_of_lt Real.zero_lt_one

instance instIsOrderedAddMonoid : IsOrderedAddMonoid ℝ where
  add_le_add_left := by
    simp only [le_iff_eq_or_lt]
    rintro a b ⟨rfl, h⟩
    · simp only [lt_self_iff_false, or_false, forall_const]
    · refine fun c => Or.inr ?_
      induction a using Real.ind_mk with | _ a =>
      induction b using Real.ind_mk with | _ b =>
      induction c using Real.ind_mk with | _ c =>
      simp only [mk_lt] at *
      change Pos _ at *
      rwa [add_sub_add_right_eq_sub]

instance instIsStrictOrderedRing : IsStrictOrderedRing ℝ :=
  .of_mul_pos fun a b ↦ by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos

instance instIsOrderedRing : IsOrderedRing ℝ :=
  inferInstance

instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid ℝ :=
  inferInstance

protected def sup (x y : ℝ) : ℝ :=
  Quotient.map₂ (· ⊔ ·) (fun _ _ hx _ _ hy ↦ sup_equiv_sup hx hy) x y

instance : Max ℝ := ⟨Real.sup⟩

@[simp]
private theorem mk_sup (a b) : (mk (a ⊔ b) : ℝ) = mk a ⊔ mk b :=
  rfl

protected def inf (x y : ℝ) : ℝ :=
  Quotient.map₂ (· ⊓ ·) (fun _ _ hx _ _ hy ↦ inf_equiv_inf hx hy) x y

instance : Min ℝ := ⟨Real.inf⟩

@[simp]
private theorem mk_inf (a b) : (mk (a ⊓ b) : ℝ) = mk a ⊓ mk b :=
  rfl

instance : DistribLattice ℝ where
  sup := (· ⊔ ·)
  le_sup_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_sup, mk_le]
    exact CauSeq.le_sup_left
  le_sup_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_sup, mk_le]
    exact CauSeq.le_sup_right
  sup_le := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_sup, mk_le]
    exact CauSeq.sup_le
  inf := (· ⊓ ·)
  inf_le_left := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_inf, mk_le]
    exact CauSeq.inf_le_left
  inf_le_right := by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    dsimp only; rw [← mk_inf, mk_le]
    exact CauSeq.inf_le_right
  le_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    simp_rw [← mk_inf, mk_le]
    exact CauSeq.le_inf
  le_sup_inf := by
    intro a b c
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    induction c using Real.ind_mk
    apply Eq.le
    simp only [← mk_sup, ← mk_inf]
    exact congr_arg mk (CauSeq.sup_inf_distrib_left ..).symm

-- Extra instances to short-circuit type class resolution
instance lattice : Lattice ℝ :=
  inferInstance

instance : SemilatticeInf ℝ :=
  inferInstance

instance : SemilatticeSup ℝ :=
  inferInstance

instance leTotal_R : @Std.Total ℝ (· ≤ ·) :=
  ⟨by
    intro a b
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa using CauSeq.le_total ..⟩

open scoped Classical in
noncomputable instance linearOrder : LinearOrder ℝ :=
  Lattice.toLinearOrder ℝ

instance : IsDomain ℝ := IsStrictOrderedRing.isDomain

noncomputable instance instDivInvMonoid : DivInvMonoid ℝ where

private lemma ofCauchy_div (f g) : (.ofCauchy (f / g) : ℝ) = (.ofCauchy f) / (.ofCauchy g) := by
  simp_rw [div_eq_mul_inv, ofCauchy_mul, ofCauchy_inv]

noncomputable instance instField : Field ℝ where
  mul_inv_cancel a h := by
    simp only [ne_eq, ext_cauchy_iff, cauchy_zero, cauchy_mul, cauchy_inv, cauchy_one] at h ⊢
    exact CauSeq.Completion.mul_inv_cancel h
  inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← ofCauchy_nnratCast, NNRat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_natCast]
  ratCast_def q := by
    rw [← ofCauchy_ratCast, Rat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_intCast]

-- Extra instances to short-circuit type class resolution
noncomputable instance : DivisionRing ℝ := by infer_instance

noncomputable instance decidableLT (a b : ℝ) : Decidable (a < b) := by infer_instance

noncomputable instance decidableLE (a b : ℝ) : Decidable (a ≤ b) := by infer_instance

noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by infer_instance

private theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f := by
  intro h
  induction x using Real.ind_mk
  apply le_of_not_gt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_ge (H _ le_rfl).1
  rw [← mk_const, mk_lt]
  refine ⟨_, half_pos K0, i, fun j ij => ?_⟩
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this

private theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) :
    mk f ≤ x := by
  obtain ⟨i, H⟩ := h
  rw [← neg_le_neg_iff, ← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩

private theorem mk_near_of_forall_near {f : CauSeq ℚ abs} {x : ℝ} {ε : ℝ}
    (H : ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| ≤ ε) : |mk f - x| ≤ ε :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add'.2 <|
        mk_le_of_forall_le <|
          H.imp fun _ h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
      sub_le_comm.1 <|
        le_mk_of_forall_le <| H.imp fun _ h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩

lemma mul_add_one_le_add_one_pow {a : ℝ} (ha : 0 ≤ a) (b : ℕ) : a * b + 1 ≤ (a + 1) ^ b := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  clear ha
  induction b generalizing a with
  | zero => simp
  | succ b hb =>
    calc
      a * ↑(b + 1) + 1 = (0 + 1) ^ b * a + (a * b + 1) := by
        simp [mul_add, add_assoc, add_left_comm]
      _ ≤ (a + 1) ^ b * a + (a + 1) ^ b := by
        gcongr
        · norm_num
        · exact hb ha'
      _ = (a + 1) ^ (b + 1) := by simp [pow_succ, mul_add]

end Real

/-- A function `f : R → ℝ` is power-multiplicative if for all `r ∈ R` and all positive `n ∈ ℕ`,
`f (r ^ n) = (f r) ^ n`. -/
@[expose] def IsPowMul {R : Type*} [Pow R ℕ] (f : R → ℝ) : Prop :=
  ∀ (a : R) {n : ℕ}, 1 ≤ n → f (a ^ n) = f a ^ n

lemma IsPowMul.map_one_le_one {R : Type*} [Monoid R] {f : R → ℝ} (hf : IsPowMul f) :
    f 1 ≤ 1 := by
  have hf1 : (f 1) ^ 2 = f 1 := by conv_rhs => rw [← one_pow 2, hf _ one_le_two]
  rcases eq_zero_or_one_of_sq_eq_self hf1 with h | h <;> rw [h]
  exact zero_le_one

/-- A ring homomorphism `f : α →+* β` is bounded with respect to the functions `nα : α → ℝ` and
  `nβ : β → ℝ` if there exists a positive constant `C` such that for all `x` in `α`,
  `nβ (f x) ≤ C * nα x`. -/
@[expose] def RingHom.IsBoundedWrt {α : Type*} [Ring α] {β : Type*} [Ring β]
    (nα : α → ℝ) (nβ : β → ℝ) (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, nβ (f x) ≤ C * nα x
