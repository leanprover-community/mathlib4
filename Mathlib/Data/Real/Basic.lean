/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Order.CauSeq.Completion

#align_import data.real.basic from "leanprover-community/mathlib"@"cb42593171ba005beaaf4549fcfe0dece9ada4c9"

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.

The facts that the real numbers are an Archimedean floor ring,
and a conditionally complete linear order,
have been deferred to the file `Mathlib/Data/Real/Archimedean.lean`,
in order to keep the imports here simple.
-/


assert_not_exists Finset
assert_not_exists Module
assert_not_exists Submonoid
assert_not_exists FloorRing

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where ofCauchy ::
  /-- The underlying Cauchy completion -/
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)
#align real Real

@[inherit_doc]
notation "ℝ" => Real

-- Porting note: unknown attribute
-- attribute [pp_using_anonymous_constructor] Real

namespace CauSeq.Completion

-- this can't go in `Data.Real.CauSeqCompletion` as the structure on `ℚ` isn't available
@[simp]
theorem ofRat_rat {abv : ℚ → ℚ} [IsAbsoluteValue abv] (q : ℚ) :
    ofRat (q : ℚ) = (q : Cauchy abv) :=
  rfl
#align cau_seq.completion.of_rat_rat CauSeq.Completion.ofRat_rat

end CauSeq.Completion

namespace Real

open CauSeq CauSeq.Completion

variable {x y : ℝ}

theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by rw [ofCauchy.injEq]
#align real.ext_cauchy_iff Real.ext_cauchy_iff

theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2
#align real.ext_cauchy Real.ext_cauchy

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equivCauchy : ℝ ≃ CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  ⟨Real.cauchy, Real.ofCauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩
set_option linter.uppercaseLean3 false in
#align real.equiv_Cauchy Real.equivCauchy

-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
private irreducible_def zero : ℝ :=
  ⟨0⟩

private irreducible_def one : ℝ :=
  ⟨1⟩

private irreducible_def add : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg : ℝ → ℝ
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

private noncomputable irreducible_def inv' : ℝ → ℝ
  | ⟨a⟩ => ⟨a⁻¹⟩

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

theorem ofCauchy_zero : (⟨0⟩ : ℝ) = 0 :=
  zero_def.symm
#align real.of_cauchy_zero Real.ofCauchy_zero

theorem ofCauchy_one : (⟨1⟩ : ℝ) = 1 :=
  one_def.symm
#align real.of_cauchy_one Real.ofCauchy_one

theorem ofCauchy_add (a b) : (⟨a + b⟩ : ℝ) = ⟨a⟩ + ⟨b⟩ :=
  (add_def _ _).symm
#align real.of_cauchy_add Real.ofCauchy_add

theorem ofCauchy_neg (a) : (⟨-a⟩ : ℝ) = -⟨a⟩ :=
  (neg_def _).symm
#align real.of_cauchy_neg Real.ofCauchy_neg

theorem ofCauchy_sub (a b) : (⟨a - b⟩ : ℝ) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg, ofCauchy_add, ofCauchy_neg]
  rfl
#align real.of_cauchy_sub Real.ofCauchy_sub

theorem ofCauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ :=
  (mul_def _ _).symm
#align real.of_cauchy_mul Real.ofCauchy_mul

theorem ofCauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by rw [inv']
#align real.of_cauchy_inv Real.ofCauchy_inv

theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  show zero.cauchy = 0 by rw [zero_def]
#align real.cauchy_zero Real.cauchy_zero

theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  show one.cauchy = 1 by rw [one_def]
#align real.cauchy_one Real.cauchy_one

theorem cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (add _ _).cauchy = _ by rw [add_def]
#align real.cauchy_add Real.cauchy_add

theorem cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
  | ⟨a⟩ => show (neg _).cauchy = _ by rw [neg_def]
#align real.cauchy_neg Real.cauchy_neg

theorem cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (mul _ _).cauchy = _ by rw [mul_def]
#align real.cauchy_mul Real.cauchy_mul

theorem cauchy_sub : ∀ a b, (a - b : ℝ).cauchy = a.cauchy - b.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    rw [sub_eq_add_neg, ← cauchy_neg, ← cauchy_add]
    rfl
#align real.cauchy_sub Real.cauchy_sub

theorem cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
  | ⟨f⟩ => show (inv' _).cauchy = _ by rw [inv']
#align real.cauchy_inv Real.cauchy_inv

instance instNatCast : NatCast ℝ where natCast n := ⟨n⟩
instance instIntCast : IntCast ℝ where intCast z := ⟨z⟩
instance instNNRatCast : NNRatCast ℝ where nnratCast q := ⟨q⟩
instance instRatCast : RatCast ℝ where ratCast q := ⟨q⟩

lemma ofCauchy_natCast (n : ℕ) : (⟨n⟩ : ℝ) = n := rfl
lemma ofCauchy_intCast (z : ℤ) : (⟨z⟩ : ℝ) = z := rfl
lemma ofCauchy_nnratCast (q : ℚ≥0) : (⟨q⟩ : ℝ) = q := rfl
lemma ofCauchy_ratCast (q : ℚ) : (⟨q⟩ : ℝ) = q := rfl
#align real.of_cauchy_nat_cast Real.ofCauchy_natCast
#align real.of_cauchy_int_cast Real.ofCauchy_intCast
#align real.of_cauchy_rat_cast Real.ofCauchy_ratCast

lemma cauchy_natCast (n : ℕ) : (n : ℝ).cauchy = n := rfl
lemma cauchy_intCast (z : ℤ) : (z : ℝ).cauchy = z := rfl
lemma cauchy_nnratCast (q : ℚ≥0) : (q : ℝ).cauchy = q := rfl
lemma cauchy_ratCast (q : ℚ) : (q : ℝ).cauchy = q := rfl
#align real.cauchy_nat_cast Real.cauchy_natCast
#align real.cauchy_int_cast Real.cauchy_intCast
#align real.cauchy_rat_cast Real.cauchy_ratCast

instance commRing : CommRing ℝ := by
  refine' { natCast := fun n => ⟨n⟩
            intCast := fun z => ⟨z⟩
            zero := (0 : ℝ)
            one := (1 : ℝ)
            mul := (· * ·)
            add := (· + ·)
            neg := @Neg.neg ℝ _
            sub := @Sub.sub ℝ _
            npow := @npowRec ℝ ⟨1⟩ ⟨(· * ·)⟩
            nsmul := @nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩
            zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩ (@nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩),
            .. }
  all_goals
    intros
    first
    | rfl
    | apply ext_cauchy
      simp [cauchy_add, cauchy_zero, cauchy_one, cauchy_neg, cauchy_mul,
        cauchy_natCast, cauchy_intCast]
      first
        | done
        | apply add_assoc
        | apply add_comm
        | apply left_distrib
        | apply right_distrib
        | apply mul_assoc
        | apply mul_comm

/-- `Real.equivCauchy` as a ring equivalence. -/
@[simps]
def ringEquivCauchy : ℝ ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  { equivCauchy with
    toFun := cauchy
    invFun := ofCauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }
set_option linter.uppercaseLean3 false in
#align real.ring_equiv_Cauchy Real.ringEquivCauchy
set_option linter.uppercaseLean3 false in
#align real.ring_equiv_Cauchy_apply Real.ringEquivCauchy_apply
set_option linter.uppercaseLean3 false in
#align real.ring_equiv_Cauchy_symm_apply_cauchy Real.ringEquivCauchy_symm_apply_cauchy

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
  ext_cauchy_iff.trans CauSeq.Completion.mk_eq
#align real.mk_eq Real.mk_eq

private irreducible_def lt : ℝ → ℝ → Prop
  | ⟨x⟩, ⟨y⟩ =>
    (Quotient.liftOn₂ x y (· < ·)) fun _ _ _ _ hf hg =>
      propext <|
        ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩

instance : LT ℝ :=
  ⟨lt⟩

theorem lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g :=
  show lt _ _ ↔ _ by rw [lt_def]; rfl
#align real.lt_cauchy Real.lt_cauchy

@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy
#align real.mk_lt Real.mk_lt

theorem mk_zero : mk 0 = 0 := by rw [← ofCauchy_zero]; rfl
#align real.mk_zero Real.mk_zero

theorem mk_one : mk 1 = 1 := by rw [← ofCauchy_one]; rfl
#align real.mk_one Real.mk_one

theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, ← ofCauchy_add]
#align real.mk_add Real.mk_add

theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, ← ofCauchy_mul]
#align real.mk_mul Real.mk_mul

theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by simp [mk, ← ofCauchy_neg]
#align real.mk_neg Real.mk_neg

@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))
#align real.mk_pos Real.mk_pos

private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y

instance : LE ℝ :=
  ⟨le⟩

private theorem le_def' {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  show le _ _ ↔ _ by rw [le_def]

@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by
  simp only [le_def', mk_lt, mk_eq]; rfl
#align real.mk_le Real.mk_le

@[elab_as_elim]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x := by
  cases' x with x
  induction' x using Quot.induction_on with x
  exact h x
#align real.ind_mk Real.ind_mk

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b := by
  induction a using Real.ind_mk
  induction b using Real.ind_mk
  induction c using Real.ind_mk
  simp only [mk_lt, ← mk_add]
  show Pos _ ↔ Pos _; rw [add_sub_add_left_eq_sub]
#align real.add_lt_add_iff_left Real.add_lt_add_iff_left

instance partialOrder : PartialOrder ℝ where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b := by
    induction' a using Real.ind_mk with a
    induction' b using Real.ind_mk with b
    simpa using lt_iff_le_not_le
  le_refl a := by
    induction' a using Real.ind_mk with a
    rw [mk_le]
  le_trans a b c := by
    induction' a using Real.ind_mk with a
    induction' b using Real.ind_mk with b
    induction' c using Real.ind_mk with c
    simpa using le_trans
  le_antisymm a b := by
    induction' a using Real.ind_mk with a
    induction' b using Real.ind_mk with b
    simpa [mk_eq] using @CauSeq.le_antisymm _ _ a b

instance : Preorder ℝ := by infer_instance

theorem ratCast_lt {x y : ℚ} : (x : ℝ) < (y : ℝ) ↔ x < y := by
  erw [mk_lt]
  exact const_lt
#align real.rat_cast_lt Real.ratCast_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 := by
  convert ratCast_lt.2 zero_lt_one <;> simp [← ofCauchy_ratCast, ofCauchy_one, ofCauchy_zero]
#align real.zero_lt_one Real.zero_lt_one

protected theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨Real.zero_lt_one⟩
#align real.fact_zero_lt_one Real.fact_zero_lt_one

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b := by
  induction' a using Real.ind_mk with a
  induction' b using Real.ind_mk with b
  simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos
#align real.mul_pos Real.mul_pos

instance : StrictOrderedCommRing ℝ :=
  { Real.commRing, Real.partialOrder,
    Real.semiring with
    exists_pair_ne := ⟨0, 1, Real.zero_lt_one.ne⟩
    add_le_add_left := by
      simp only [le_iff_eq_or_lt]
      rintro a b ⟨rfl, h⟩
      · simp only [lt_self_iff_false, or_false, forall_const]
      · exact fun c => Or.inr ((add_lt_add_iff_left c).2 ‹_›)
    zero_le_one := le_of_lt Real.zero_lt_one
    mul_pos := @Real.mul_pos }

instance strictOrderedRing : StrictOrderedRing ℝ :=
  inferInstance

instance strictOrderedCommSemiring : StrictOrderedCommSemiring ℝ :=
  inferInstance

instance strictOrderedSemiring : StrictOrderedSemiring ℝ :=
  inferInstance

instance orderedRing : OrderedRing ℝ :=
  inferInstance

instance orderedSemiring : OrderedSemiring ℝ :=
  inferInstance

instance orderedAddCommGroup : OrderedAddCommGroup ℝ :=
  inferInstance

instance orderedCancelAddCommMonoid : OrderedCancelAddCommMonoid ℝ :=
  inferInstance

instance orderedAddCommMonoid : OrderedAddCommMonoid ℝ :=
  inferInstance

instance nontrivial : Nontrivial ℝ :=
  inferInstance

private irreducible_def sup : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊔ ·) (fun _ _ hx _ _ hy => sup_equiv_sup hx hy) x y⟩

instance : Sup ℝ :=
  ⟨sup⟩

theorem ofCauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩ :=
  show _ = sup _ _ by
    rw [sup_def]
    rfl
#align real.of_cauchy_sup Real.ofCauchy_sup

@[simp]
theorem mk_sup (a b) : (mk (a ⊔ b) : ℝ) = mk a ⊔ mk b :=
  ofCauchy_sup _ _
#align real.mk_sup Real.mk_sup

private irreducible_def inf : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊓ ·) (fun _ _ hx _ _ hy => inf_equiv_inf hx hy) x y⟩

instance : Inf ℝ :=
  ⟨inf⟩

theorem ofCauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩ :=
  show _ = inf _ _ by
    rw [inf_def]
    rfl
#align real.of_cauchy_inf Real.ofCauchy_inf

@[simp]
theorem mk_inf (a b) : (mk (a ⊓ b) : ℝ) = mk a ⊓ mk b :=
  ofCauchy_inf _ _
#align real.mk_inf Real.mk_inf

instance : DistribLattice ℝ :=
  { Real.partialOrder with
    sup := (· ⊔ ·)
    le := (· ≤ ·)
    le_sup_left := by
      intros a b
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      rw [← mk_sup, mk_le]
      exact CauSeq.le_sup_left
    le_sup_right := by
      intros a b
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      rw [← mk_sup, mk_le]
      exact CauSeq.le_sup_right
    sup_le := by
      intros a b c
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      induction' c using Real.ind_mk with c
      simp_rw [← mk_sup, mk_le]
      exact CauSeq.sup_le
    inf := (· ⊓ ·)
    inf_le_left := by
      intros a b
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      rw [← mk_inf, mk_le]
      exact CauSeq.inf_le_left
    inf_le_right := by
      intros a b
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      rw [← mk_inf, mk_le]
      exact CauSeq.inf_le_right
    le_inf := by
      intros a b c
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      induction' c using Real.ind_mk with c
      simp_rw [← mk_inf, mk_le]
      exact CauSeq.le_inf
    le_sup_inf := by
      intros a b c
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      induction' c using Real.ind_mk with c
      apply Eq.le
      simp only [← mk_sup, ← mk_inf]
      exact congr_arg mk (CauSeq.sup_inf_distrib_left _ _ _).symm }

-- Extra instances to short-circuit type class resolution
instance lattice : Lattice ℝ :=
  inferInstance

instance : SemilatticeInf ℝ :=
  inferInstance

instance : SemilatticeSup ℝ :=
  inferInstance

open scoped Classical

instance : IsTotal ℝ (· ≤ ·) :=
  ⟨by
    intros a b
    induction' a using Real.ind_mk with a
    induction' b using Real.ind_mk with b
    simpa using le_total a b⟩

noncomputable instance linearOrder : LinearOrder ℝ :=
  Lattice.toLinearOrder _

noncomputable instance linearOrderedCommRing : LinearOrderedCommRing ℝ :=
  { Real.nontrivial, Real.strictOrderedRing, Real.commRing, Real.linearOrder with }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedRing ℝ := by infer_instance

noncomputable instance : LinearOrderedSemiring ℝ := by infer_instance

instance : IsDomain ℝ :=
  { Real.nontrivial, Real.commRing, LinearOrderedRing.isDomain with }

noncomputable instance instDivInvMonoid : DivInvMonoid ℝ where

lemma ofCauchy_div (f g) : (⟨f / g⟩ : ℝ) = (⟨f⟩ : ℝ) / (⟨g⟩ : ℝ) := by
  simp_rw [div_eq_mul_inv, ofCauchy_mul, ofCauchy_inv]

noncomputable instance instLinearOrderedField : LinearOrderedField ℝ where
  toLinearOrderedCommRing := linearOrderedCommRing
  mul_inv_cancel := by
    rintro ⟨a⟩ h
    rw [mul_comm]
    simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
      Ne, ofCauchy.injEq] at *
    exact CauSeq.Completion.inv_mul_cancel h
  inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
  nnqsmul := _
  qsmul := _
  nnratCast_def q := by
    rw [← ofCauchy_nnratCast, NNRat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_natCast]
  ratCast_def q := by
    rw [← ofCauchy_ratCast, Rat.cast_def, ofCauchy_div, ofCauchy_natCast, ofCauchy_intCast]

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedAddCommGroup ℝ := by infer_instance

noncomputable instance field : Field ℝ := by infer_instance
#align real.field Real.field

noncomputable instance : DivisionRing ℝ := by infer_instance

noncomputable instance decidableLT (a b : ℝ) : Decidable (a < b) := by infer_instance
#align real.decidable_lt Real.decidableLT

noncomputable instance decidableLE (a b : ℝ) : Decidable (a ≤ b) := by infer_instance
#align real.decidable_le Real.decidableLE

noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by infer_instance
#align real.decidable_eq Real.decidableEq

/-- Show an underlying cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `Quot.mk`, so two cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr ℝ where reprPrec r _ := "Real.ofCauchy " ++ repr r.cauchy

theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f := by
  intro h
  induction' x using Real.ind_mk with x
  apply le_of_not_lt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_le (H _ le_rfl).1
  erw [mk_lt]
  refine ⟨_, half_pos K0, i, fun j ij => ?_⟩
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
          H.imp fun _ h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
      sub_le_comm.1 <|
        le_mk_of_forall_le <| H.imp fun _ h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩
#align real.mk_near_of_forall_near Real.mk_near_of_forall_near

end Real

/-- A function `f : R → ℝ≥0` is nonarchimedean if it satisfies the strong triangle inequality
  `f (r + s) ≤ max (f r) (f s)` for all `r s : R`. -/
def IsNonarchimedean {A : Type _} [Add A] (f : A → ℝ) : Prop :=
  ∀ r s, f (r + s) ≤ max (f r) (f s)
