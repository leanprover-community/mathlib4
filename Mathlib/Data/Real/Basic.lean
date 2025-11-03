/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.CauSeq.Completion
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Cast.Defs

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.

The facts that the real numbers are an Archimedean floor ring,
and a conditionally complete linear order,
have been deferred to the file `Mathlib/Data/Real/Archimedean.lean`,
in order to keep the imports here simple.

The fact that the real numbers are a (trivial) *-ring has similarly been deferred to
`Mathlib/Data/Real/Star.lean`.
-/


assert_not_exists Finset Module Submonoid FloorRing

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where ofCauchy ::
  /-- The underlying Cauchy completion -/
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)

@[inherit_doc]
notation "ℝ" => Real

namespace CauSeq.Completion

-- this can't go in `Data.Real.CauSeqCompletion` as the structure on `ℚ` isn't available
@[simp]
theorem ofRat_rat {abv : ℚ → ℚ} [IsAbsoluteValue abv] (q : ℚ) :
    ofRat (q : ℚ) = (q : Cauchy abv) :=
  rfl

end CauSeq.Completion

namespace Real

open CauSeq CauSeq.Completion

variable {x : ℝ}

theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by rw [ofCauchy.injEq]

theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equivCauchy : ℝ ≃ CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  ⟨Real.cauchy, Real.ofCauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩

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

theorem ofCauchy_one : (⟨1⟩ : ℝ) = 1 :=
  one_def.symm

theorem ofCauchy_add (a b) : (⟨a + b⟩ : ℝ) = ⟨a⟩ + ⟨b⟩ :=
  (add_def _ _).symm

theorem ofCauchy_neg (a) : (⟨-a⟩ : ℝ) = -⟨a⟩ :=
  (neg_def _).symm

theorem ofCauchy_sub (a b) : (⟨a - b⟩ : ℝ) = ⟨a⟩ - ⟨b⟩ := by
  rw [sub_eq_add_neg, ofCauchy_add, ofCauchy_neg]
  rfl

theorem ofCauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ :=
  (mul_def _ _).symm

theorem ofCauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by rw [inv']

theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  show zero.cauchy = 0 by rw [zero_def]

theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  show one.cauchy = 1 by rw [one_def]

theorem cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (add _ _).cauchy = _ by rw [add_def]

theorem cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
  | ⟨a⟩ => show (neg _).cauchy = _ by rw [neg_def]

theorem cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (mul _ _).cauchy = _ by rw [mul_def]

theorem cauchy_sub : ∀ a b, (a - b : ℝ).cauchy = a.cauchy - b.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    rw [sub_eq_add_neg, ← cauchy_neg, ← cauchy_add]
    rfl

theorem cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
  | ⟨f⟩ => show (inv' _).cauchy = _ by rw [inv']

instance instNatCast : NatCast ℝ where natCast n := ⟨n⟩
instance instIntCast : IntCast ℝ where intCast z := ⟨z⟩
instance instNNRatCast : NNRatCast ℝ where nnratCast q := ⟨q⟩
instance instRatCast : RatCast ℝ where ratCast q := ⟨q⟩

lemma ofCauchy_natCast (n : ℕ) : (⟨n⟩ : ℝ) = n := rfl
lemma ofCauchy_intCast (z : ℤ) : (⟨z⟩ : ℝ) = z := rfl
lemma ofCauchy_nnratCast (q : ℚ≥0) : (⟨q⟩ : ℝ) = q := rfl
lemma ofCauchy_ratCast (q : ℚ) : (⟨q⟩ : ℝ) = q := rfl

lemma cauchy_natCast (n : ℕ) : (n : ℝ).cauchy = n := rfl
lemma cauchy_intCast (z : ℤ) : (z : ℝ).cauchy = z := rfl
lemma cauchy_nnratCast (q : ℚ≥0) : (q : ℝ).cauchy = q := rfl
lemma cauchy_ratCast (q : ℚ) : (q : ℝ).cauchy = q := rfl

instance commRing : CommRing ℝ where
  natCast n := ⟨n⟩
  intCast z := ⟨z⟩
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
  natCast_zero := by apply ext_cauchy; simp [cauchy_zero]
  natCast_succ n := by apply ext_cauchy; simp [cauchy_one, cauchy_add]
  intCast_negSucc z := by apply ext_cauchy; simp [cauchy_neg, cauchy_natCast]

/-- `Real.equivCauchy` as a ring equivalence. -/
@[simps]
def ringEquivCauchy : ℝ ≃+* CauSeq.Completion.Cauchy (abs : ℚ → ℚ) :=
  { equivCauchy with
    toFun := cauchy
    invFun := ofCauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }

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
def mk (x : CauSeq ℚ abs) : ℝ :=
  ⟨CauSeq.Completion.mk x⟩

theorem mk_eq {f g : CauSeq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans CauSeq.Completion.mk_eq

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

@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy

theorem mk_zero : mk 0 = 0 := by rw [← ofCauchy_zero]; rfl

theorem mk_one : mk 1 = 1 := by rw [← ofCauchy_one]; rfl

theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, ← ofCauchy_add]

theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, ← ofCauchy_mul]

theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by simp [mk, ← ofCauchy_neg]

@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt]
  exact iff_of_eq (congr_arg Pos (sub_zero f))

lemma mk_const {x : ℚ} : mk (const abs x) = x := rfl

private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y

instance : LE ℝ :=
  ⟨le⟩

private theorem le_def' {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  iff_of_eq <| le_def _ _

@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by
  simp only [le_def', mk_lt, mk_eq]; rfl

@[elab_as_elim]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x := by
  obtain ⟨x⟩ := x
  induction x using Quot.induction_on
  exact h _

instance partialOrder : PartialOrder ℝ where
  le := (· ≤ ·)
  lt := (· < ·)
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

protected theorem zero_lt_one : (0 : ℝ) < 1 := by
  convert ratCast_lt.2 zero_lt_one <;> simp [← ofCauchy_ratCast, ofCauchy_one, ofCauchy_zero]

@[deprecated ZeroLEOneClass.factZeroLtOne (since := "2025-05-12")]
protected theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨Real.zero_lt_one⟩

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
      simp only [mk_lt, ← mk_add] at *
      change Pos _ at *
      rwa [add_sub_add_left_eq_sub]

@[deprecated (since := "2025-09-15")]
protected alias add_lt_add_iff_left := _root_.add_lt_add_iff_left

instance instIsStrictOrderedRing : IsStrictOrderedRing ℝ :=
  .of_mul_pos fun a b ↦ by
    induction a using Real.ind_mk
    induction b using Real.ind_mk
    simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos

instance instIsOrderedRing : IsOrderedRing ℝ :=
  inferInstance

instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid ℝ :=
  inferInstance

private irreducible_def sup : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊔ ·) (fun _ _ hx _ _ hy => sup_equiv_sup hx hy) x y⟩

instance : Max ℝ :=
  ⟨sup⟩

theorem ofCauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩ :=
  show _ = sup _ _ by
    rw [sup_def]
    rfl

@[simp]
theorem mk_sup (a b) : (mk (a ⊔ b) : ℝ) = mk a ⊔ mk b :=
  ofCauchy_sup _ _

private irreducible_def inf : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊓ ·) (fun _ _ hx _ _ hy => inf_equiv_inf hx hy) x y⟩

instance : Min ℝ :=
  ⟨inf⟩

theorem ofCauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩ :=
  show _ = inf _ _ by
    rw [inf_def]
    rfl

@[simp]
theorem mk_inf (a b) : (mk (a ⊓ b) : ℝ) = mk a ⊓ mk b :=
  ofCauchy_inf _ _

instance : DistribLattice ℝ :=
  { Real.partialOrder with
    sup := (· ⊔ ·)
    le := (· ≤ ·)
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
      exact congr_arg mk (CauSeq.sup_inf_distrib_left ..).symm }

-- Extra instances to short-circuit type class resolution
instance lattice : Lattice ℝ :=
  inferInstance

instance : SemilatticeInf ℝ :=
  inferInstance

instance : SemilatticeSup ℝ :=
  inferInstance

instance leTotal_R : IsTotal ℝ (· ≤ ·) :=
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

lemma ofCauchy_div (f g) : (⟨f / g⟩ : ℝ) = (⟨f⟩ : ℝ) / (⟨g⟩ : ℝ) := by
  simp_rw [div_eq_mul_inv, ofCauchy_mul, ofCauchy_inv]

noncomputable instance instField : Field ℝ where
  mul_inv_cancel := by
    rintro ⟨a⟩ h
    rw [mul_comm]
    simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
      Ne, ofCauchy.injEq] at *
    exact CauSeq.Completion.inv_mul_cancel h
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

/-- Show an underlying Cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr ℝ where
  reprPrec r p := Repr.addAppParen ("Real.ofCauchy " ++ repr r.cauchy) p

theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f := by
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

theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) :
    mk f ≤ x := by
  obtain ⟨i, H⟩ := h
  rw [← neg_le_neg_iff, ← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩

theorem mk_near_of_forall_near {f : CauSeq ℚ abs} {x : ℝ} {ε : ℝ}
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
def IsPowMul {R : Type*} [Pow R ℕ] (f : R → ℝ) :=
  ∀ (a : R) {n : ℕ}, 1 ≤ n → f (a ^ n) = f a ^ n

lemma IsPowMul.map_one_le_one {R : Type*} [Monoid R] {f : R → ℝ} (hf : IsPowMul f) :
    f 1 ≤ 1 := by
  have hf1 : (f 1)^2 = f 1 := by conv_rhs => rw [← one_pow 2, hf _ one_le_two]
  rcases eq_zero_or_one_of_sq_eq_self hf1 with h | h <;> rw [h]
  exact zero_le_one

/-- A ring homomorphism `f : α →+* β` is bounded with respect to the functions `nα : α → ℝ` and
  `nβ : β → ℝ` if there exists a positive constant `C` such that for all `x` in `α`,
  `nβ (f x) ≤ C * nα x`. -/
def RingHom.IsBoundedWrt {α : Type*} [Ring α] {β : Type*} [Ring β] (nα : α → ℝ) (nβ : β → ℝ)
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, nβ (f x) ≤ C * nα x
