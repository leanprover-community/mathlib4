/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Bounds
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.CauSeqCompletion

#align_import data.real.basic from "leanprover-community/mathlib"@"cb42593171ba005beaaf4549fcfe0dece9ada4c9"

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.
-/


assert_not_exists Finset
assert_not_exists Module
assert_not_exists Submonoid

open Pointwise

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
                   -- 🎉 no goals
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
  -- ⊢ { cauchy := a } + -{ cauchy := b } = { cauchy := a } - { cauchy := b }
  rfl
  -- 🎉 no goals
#align real.of_cauchy_sub Real.ofCauchy_sub

theorem ofCauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ :=
  (mul_def _ _).symm
#align real.of_cauchy_mul Real.ofCauchy_mul

theorem ofCauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by rw [inv']
                     -- 🎉 no goals
#align real.of_cauchy_inv Real.ofCauchy_inv

theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  show zero.cauchy = 0 by rw [zero_def]
                          -- 🎉 no goals
#align real.cauchy_zero Real.cauchy_zero

theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  show one.cauchy = 1 by rw [one_def]
                         -- 🎉 no goals
#align real.cauchy_one Real.cauchy_one

theorem cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (add _ _).cauchy = _ by rw [add_def]
                                             -- 🎉 no goals
#align real.cauchy_add Real.cauchy_add

theorem cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
  | ⟨a⟩ => show (neg _).cauchy = _ by rw [neg_def]
                                      -- 🎉 no goals
#align real.cauchy_neg Real.cauchy_neg

theorem cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (mul _ _).cauchy = _ by rw [mul_def]
                                             -- 🎉 no goals
#align real.cauchy_mul Real.cauchy_mul

theorem cauchy_sub : ∀ a b, (a - b : ℝ).cauchy = a.cauchy - b.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    rw [sub_eq_add_neg, ← cauchy_neg, ← cauchy_add]
    -- ⊢ ({ cauchy := a } - { cauchy := b }).cauchy = ({ cauchy := a } + -{ cauchy := …
    rfl
    -- 🎉 no goals
#align real.cauchy_sub Real.cauchy_sub

theorem cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
  | ⟨f⟩ => show (inv' _).cauchy = _ by rw [inv']
                                       -- 🎉 no goals
#align real.cauchy_inv Real.cauchy_inv

instance natCast : NatCast ℝ where natCast n := ⟨n⟩

instance intCast : IntCast ℝ where intCast z := ⟨z⟩

instance ratCast : RatCast ℝ where ratCast q := ⟨q⟩

theorem ofCauchy_natCast (n : ℕ) : (⟨n⟩ : ℝ) = n :=
  rfl
#align real.of_cauchy_nat_cast Real.ofCauchy_natCast

theorem ofCauchy_intCast (z : ℤ) : (⟨z⟩ : ℝ) = z :=
  rfl
#align real.of_cauchy_int_cast Real.ofCauchy_intCast

theorem ofCauchy_ratCast (q : ℚ) : (⟨q⟩ : ℝ) = q :=
  rfl
#align real.of_cauchy_rat_cast Real.ofCauchy_ratCast

theorem cauchy_natCast (n : ℕ) : (n : ℝ).cauchy = n :=
  rfl
#align real.cauchy_nat_cast Real.cauchy_natCast

theorem cauchy_intCast (z : ℤ) : (z : ℝ).cauchy = z :=
  rfl
#align real.cauchy_int_cast Real.cauchy_intCast

theorem cauchy_ratCast (q : ℚ) : (q : ℝ).cauchy = q :=
  rfl
#align real.cauchy_rat_cast Real.cauchy_ratCast

-- TODO: variables `x y` should be not included in this definition;
-- not sure how to exclude them
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
            zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩,
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

instance : Ring ℝ := by infer_instance
                        -- 🎉 no goals

instance : CommSemiring ℝ := by infer_instance
                                -- 🎉 no goals

instance semiring : Semiring ℝ := by infer_instance
                                     -- 🎉 no goals

instance : CommMonoidWithZero ℝ := by infer_instance
                                      -- 🎉 no goals

instance : MonoidWithZero ℝ := by infer_instance
                                  -- 🎉 no goals

instance : AddCommGroup ℝ := by infer_instance
                                -- 🎉 no goals

instance : AddGroup ℝ := by infer_instance
                            -- 🎉 no goals

instance : AddCommMonoid ℝ := by infer_instance
                                 -- 🎉 no goals

instance : AddMonoid ℝ := by infer_instance
                             -- 🎉 no goals

instance : AddLeftCancelSemigroup ℝ := by infer_instance
                                          -- 🎉 no goals

instance : AddRightCancelSemigroup ℝ := by infer_instance
                                           -- 🎉 no goals

instance : AddCommSemigroup ℝ := by infer_instance
                                    -- 🎉 no goals

instance : AddSemigroup ℝ := by infer_instance
                                -- 🎉 no goals

instance : CommMonoid ℝ := by infer_instance
                              -- 🎉 no goals

instance : Monoid ℝ := by infer_instance
                          -- 🎉 no goals

instance : CommSemigroup ℝ := by infer_instance
                                 -- 🎉 no goals

instance : Semigroup ℝ := by infer_instance
                             -- 🎉 no goals

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
                     -- ⊢ (match { cauchy := Quotient.mk equiv f }, { cauchy := Quotient.mk equiv g }  …
                                  -- 🎉 no goals
#align real.lt_cauchy Real.lt_cauchy

@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy
#align real.mk_lt Real.mk_lt

theorem mk_zero : mk 0 = 0 := by rw [← ofCauchy_zero]; rfl
                                 -- ⊢ mk 0 = { cauchy := 0 }
                                                       -- 🎉 no goals
#align real.mk_zero Real.mk_zero

theorem mk_one : mk 1 = 1 := by rw [← ofCauchy_one]; rfl
                                -- ⊢ mk 1 = { cauchy := 1 }
                                                     -- 🎉 no goals
#align real.mk_one Real.mk_one

theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, ← ofCauchy_add]
                                                                     -- 🎉 no goals
#align real.mk_add Real.mk_add

theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, ← ofCauchy_mul]
                                                                     -- 🎉 no goals
#align real.mk_mul Real.mk_mul

theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by simp [mk, ← ofCauchy_neg]
                                                          -- 🎉 no goals
#align real.mk_neg Real.mk_neg

@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt]
  -- ⊢ 0 < f ↔ Pos f
  exact iff_of_eq (congr_arg Pos (sub_zero f))
  -- 🎉 no goals
#align real.mk_pos Real.mk_pos

private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y

instance : LE ℝ :=
  ⟨le⟩

private theorem le_def' {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  show le _ _ ↔ _ by rw [le_def]
                     -- 🎉 no goals

@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by simp [le_def', mk_eq]; rfl
                                                               -- ⊢ f < g ∨ f ≈ g ↔ f ≤ g
                                                                                      -- 🎉 no goals
#align real.mk_le Real.mk_le

@[elab_as_elim]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x := by
  cases' x with x
  -- ⊢ C { cauchy := x }
  induction' x using Quot.induction_on with x
  -- ⊢ C { cauchy := Quot.mk Setoid.r x }
  exact h x
  -- 🎉 no goals
#align real.ind_mk Real.ind_mk

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b := by
  induction a using Real.ind_mk
  -- ⊢ c + mk y✝ < c + b ↔ mk y✝ < b
  induction b using Real.ind_mk
  -- ⊢ c + mk y✝¹ < c + mk y✝ ↔ mk y✝¹ < mk y✝
  induction c using Real.ind_mk
  -- ⊢ mk y✝ + mk y✝² < mk y✝ + mk y✝¹ ↔ mk y✝² < mk y✝¹
  simp only [mk_lt, ← mk_add]
  -- ⊢ y✝ + y✝² < y✝ + y✝¹ ↔ y✝² < y✝¹
  show Pos _ ↔ Pos _; rw [add_sub_add_left_eq_sub]
  -- ⊢ Pos (y✝ + y✝¹ - (y✝ + y✝²)) ↔ Pos (y✝¹ - y✝²)
                      -- 🎉 no goals
#align real.add_lt_add_iff_left Real.add_lt_add_iff_left

instance partialOrder : PartialOrder ℝ where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b := by
    induction' a using Real.ind_mk with a
    -- ⊢ mk a < b ↔ mk a ≤ b ∧ ¬b ≤ mk a
    induction' b using Real.ind_mk with b
    -- ⊢ mk a < mk b ↔ mk a ≤ mk b ∧ ¬mk b ≤ mk a
    simpa using lt_iff_le_not_le
    -- ⊢ mk a ≤ mk a
    -- 🎉 no goals
    -- 🎉 no goals
  le_refl a := by
    induction' a using Real.ind_mk with a
    -- ⊢ mk a ≤ b → b ≤ c → mk a ≤ c
    rw [mk_le]
    -- ⊢ mk a ≤ mk b → mk b ≤ c → mk a ≤ c
  le_trans a b c := by
    -- ⊢ mk a ≤ mk b → mk b ≤ mk c → mk a ≤ mk c
    induction' a using Real.ind_mk with a
    -- 🎉 no goals
    induction' b using Real.ind_mk with b
    induction' c using Real.ind_mk with c
    simpa using le_trans
  le_antisymm a b := by
    induction' a using Real.ind_mk with a
    -- ⊢ mk a ≤ b → b ≤ mk a → mk a = b
    induction' b using Real.ind_mk with b
    -- ⊢ mk a ≤ mk b → mk b ≤ mk a → mk a = mk b
    simpa [mk_eq] using @CauSeq.le_antisymm _ _ a b
    -- 🎉 no goals

instance : Preorder ℝ := by infer_instance
                            -- 🎉 no goals

theorem ratCast_lt {x y : ℚ} : (x : ℝ) < (y : ℝ) ↔ x < y := by
  erw [mk_lt]
  -- ⊢ const abs ↑x < const abs ↑y ↔ x < y
  exact const_lt
  -- 🎉 no goals
#align real.rat_cast_lt Real.ratCast_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 := by
  convert ratCast_lt.2 zero_lt_one <;> simp [← ofCauchy_ratCast, ofCauchy_one, ofCauchy_zero]
  -- ⊢ 0 = ↑0
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align real.zero_lt_one Real.zero_lt_one

protected theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨Real.zero_lt_one⟩
#align real.fact_zero_lt_one Real.fact_zero_lt_one

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b := by
  induction' a using Real.ind_mk with a
  -- ⊢ 0 < mk a → 0 < b → 0 < mk a * b
  induction' b using Real.ind_mk with b
  -- ⊢ 0 < mk a → 0 < mk b → 0 < mk a * mk b
  simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos
  -- 🎉 no goals
#align real.mul_pos Real.mul_pos

instance : StrictOrderedCommRing ℝ :=
  { Real.commRing, Real.partialOrder,
    Real.semiring with
    exists_pair_ne := ⟨0, 1, Real.zero_lt_one.ne⟩
    add_le_add_left := by
      simp only [le_iff_eq_or_lt]
      -- ⊢ ∀ (a b : ℝ), a = b ∨ a < b → ∀ (c : ℝ), c + a = c + b ∨ c + a < c + b
      rintro a b ⟨rfl, h⟩
      -- ⊢ ∀ (c : ℝ), c + a = c + a ∨ c + a < c + a
      · simp only [lt_self_iff_false, or_false, forall_const]
        -- 🎉 no goals
      · exact fun c => Or.inr ((add_lt_add_iff_left c).2 ‹_›)
        -- 🎉 no goals
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
    -- ⊢ { cauchy := Quotient.mk equiv (a ⊔ b) } =
    rfl
    -- 🎉 no goals
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
    -- ⊢ { cauchy := Quotient.mk equiv (a ⊓ b) } =
    rfl
    -- 🎉 no goals
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
      -- ⊢ a ≤ a ⊔ b
      induction' a using Real.ind_mk with a
      -- ⊢ mk a ≤ mk a ⊔ b
      induction' b using Real.ind_mk with b
      -- ⊢ mk a ≤ mk a ⊔ mk b
      rw [← mk_sup, mk_le]
      -- ⊢ a ≤ a ⊔ b
      exact CauSeq.le_sup_left
      -- 🎉 no goals
    le_sup_right := by
      intros a b
      -- ⊢ b ≤ a ⊔ b
      induction' a using Real.ind_mk with a
      -- ⊢ b ≤ mk a ⊔ b
      induction' b using Real.ind_mk with b
      -- ⊢ mk b ≤ mk a ⊔ mk b
      rw [← mk_sup, mk_le]
      -- ⊢ b ≤ a ⊔ b
      exact CauSeq.le_sup_right
      -- 🎉 no goals
    sup_le := by
      intros a b c
      -- ⊢ a ≤ c → b ≤ c → a ⊔ b ≤ c
      induction' a using Real.ind_mk with a
      -- ⊢ mk a ≤ c → b ≤ c → mk a ⊔ b ≤ c
      induction' b using Real.ind_mk with b
      -- ⊢ mk a ≤ c → mk b ≤ c → mk a ⊔ mk b ≤ c
      induction' c using Real.ind_mk with c
      -- ⊢ mk a ≤ mk c → mk b ≤ mk c → mk a ⊔ mk b ≤ mk c
      simp_rw [← mk_sup, mk_le]
      -- ⊢ a ≤ c → b ≤ c → a ⊔ b ≤ c
      exact CauSeq.sup_le
      -- 🎉 no goals
    inf := (· ⊓ ·)
    inf_le_left := by
      intros a b
      -- ⊢ a ⊓ b ≤ a
      induction' a using Real.ind_mk with a
      -- ⊢ mk a ⊓ b ≤ mk a
      induction' b using Real.ind_mk with b
      -- ⊢ mk a ⊓ mk b ≤ mk a
      rw [← mk_inf, mk_le]
      -- ⊢ a ⊓ b ≤ a
      exact CauSeq.inf_le_left
      -- 🎉 no goals
    inf_le_right := by
      intros a b
      -- ⊢ a ⊓ b ≤ b
      induction' a using Real.ind_mk with a
      -- ⊢ mk a ⊓ b ≤ b
      induction' b using Real.ind_mk with b
      -- ⊢ mk a ⊓ mk b ≤ mk b
      rw [← mk_inf, mk_le]
      -- ⊢ a ⊓ b ≤ b
      exact CauSeq.inf_le_right
      -- 🎉 no goals
    le_inf := by
      intros a b c
      -- ⊢ a ≤ b → a ≤ c → a ≤ b ⊓ c
      induction' a using Real.ind_mk with a
      -- ⊢ mk a ≤ b → mk a ≤ c → mk a ≤ b ⊓ c
      induction' b using Real.ind_mk with b
      -- ⊢ mk a ≤ mk b → mk a ≤ c → mk a ≤ mk b ⊓ c
      induction' c using Real.ind_mk with c
      -- ⊢ mk a ≤ mk b → mk a ≤ mk c → mk a ≤ mk b ⊓ mk c
      simp_rw [← mk_inf, mk_le]
      -- ⊢ a ≤ b → a ≤ c → a ≤ b ⊓ c
      exact CauSeq.le_inf
      -- 🎉 no goals
    le_sup_inf := by
      intros a b c
      -- ⊢ (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ b ⊓ c
      induction' a using Real.ind_mk with a
      -- ⊢ (mk a ⊔ b) ⊓ (mk a ⊔ c) ≤ mk a ⊔ b ⊓ c
      induction' b using Real.ind_mk with b
      -- ⊢ (mk a ⊔ mk b) ⊓ (mk a ⊔ c) ≤ mk a ⊔ mk b ⊓ c
      induction' c using Real.ind_mk with c
      -- ⊢ (mk a ⊔ mk b) ⊓ (mk a ⊔ mk c) ≤ mk a ⊔ mk b ⊓ mk c
      apply Eq.le
      -- ⊢ (mk a ⊔ mk b) ⊓ (mk a ⊔ mk c) = mk a ⊔ mk b ⊓ mk c
      simp only [← mk_sup, ← mk_inf]
      -- ⊢ mk ((a ⊔ b) ⊓ (a ⊔ c)) = mk (a ⊔ b ⊓ c)
      exact congr_arg mk (CauSeq.sup_inf_distrib_left _ _ _).symm }
      -- 🎉 no goals

-- Extra instances to short-circuit type class resolution
instance lattice : Lattice ℝ :=
  inferInstance

instance : SemilatticeInf ℝ :=
  inferInstance

instance : SemilatticeSup ℝ :=
  inferInstance

open Classical

instance : IsTotal ℝ (· ≤ ·) :=
  ⟨by
    intros a b
    -- ⊢ a ≤ b ∨ b ≤ a
    induction' a using Real.ind_mk with a
    -- ⊢ mk a ≤ b ∨ b ≤ mk a
    induction' b using Real.ind_mk with b
    -- ⊢ mk a ≤ mk b ∨ mk b ≤ mk a
    simpa using le_total a b⟩
    -- 🎉 no goals

noncomputable instance linearOrder : LinearOrder ℝ :=
  Lattice.toLinearOrder _

noncomputable instance linearOrderedCommRing : LinearOrderedCommRing ℝ :=
  { Real.nontrivial, Real.strictOrderedRing, Real.commRing, Real.linearOrder with }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedRing ℝ := by infer_instance
                                                   -- 🎉 no goals

noncomputable instance : LinearOrderedSemiring ℝ := by infer_instance
                                                       -- 🎉 no goals

instance : IsDomain ℝ :=
  { Real.nontrivial, Real.commRing, LinearOrderedRing.isDomain with }

noncomputable instance : LinearOrderedField ℝ :=
  { Real.linearOrderedCommRing with
    inv := Inv.inv
    mul_inv_cancel := by
      rintro ⟨a⟩ h
      -- ⊢ { cauchy := a } * { cauchy := a }⁻¹ = 1
      rw [mul_comm]
      -- ⊢ { cauchy := a }⁻¹ * { cauchy := a } = 1
      simp only [← ofCauchy_inv, ← ofCauchy_mul, ← ofCauchy_one, ← ofCauchy_zero,
        Ne.def, ofCauchy.injEq] at *
      exact CauSeq.Completion.inv_mul_cancel h
      -- 🎉 no goals
    inv_zero := by simp [← ofCauchy_zero, ← ofCauchy_inv]
                   -- 🎉 no goals
    ratCast := (↑)
    ratCast_mk := fun n d hd h2 => by
      rw [← ofCauchy_ratCast, Rat.cast_mk', ofCauchy_mul, ofCauchy_inv, ofCauchy_natCast,
        ofCauchy_intCast] }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedAddCommGroup ℝ := by infer_instance
                                                           -- 🎉 no goals

noncomputable instance field : Field ℝ := by infer_instance
                                             -- 🎉 no goals
#align real.field Real.field

noncomputable instance : DivisionRing ℝ := by infer_instance
                                              -- 🎉 no goals

noncomputable instance decidableLT (a b : ℝ) : Decidable (a < b) := by infer_instance
                                                                       -- 🎉 no goals
#align real.decidable_lt Real.decidableLT

noncomputable instance decidableLE (a b : ℝ) : Decidable (a ≤ b) := by infer_instance
                                                                       -- 🎉 no goals
#align real.decidable_le Real.decidableLE

noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by infer_instance
                                                                       -- 🎉 no goals
#align real.decidable_eq Real.decidableEq

/-- Show an underlying cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `Quot.mk`, so two cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr ℝ where reprPrec r _ := "Real.ofCauchy " ++ repr r.cauchy

theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f := by
  intro h
  -- ⊢ x ≤ mk f
  induction' x using Real.ind_mk with x
  -- ⊢ mk x ≤ mk f
  apply le_of_not_lt
  -- ⊢ ¬mk f < mk x
  rw [mk_lt]
  -- ⊢ ¬f < x
  rintro ⟨K, K0, hK⟩
  -- ⊢ False
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  -- ⊢ False
  apply not_lt_of_le (H _ le_rfl).1
  -- ⊢ ↑(↑f i) < mk x
  erw [mk_lt]
  -- ⊢ const abs ↑(↑f i) < x
  refine' ⟨_, half_pos K0, i, fun j ij => _⟩
  -- ⊢ K / 2 ≤ ↑(x - const abs ↑(↑f i)) j
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  -- ⊢ K / 2 ≤ ↑(x - const abs ↑(↑f i)) j
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
  -- 🎉 no goals
#align real.le_mk_of_forall_le Real.le_mk_of_forall_le

theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) :
    mk f ≤ x := by
  cases' h with i H
  -- ⊢ mk f ≤ x
  rw [← neg_le_neg_iff, ← mk_neg]
  -- ⊢ -x ≤ mk (-f)
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩
  -- 🎉 no goals
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

instance instArchimedean : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩
#align real.archimedean Real.instArchimedean

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

theorem isCauSeq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) :=
  ⟨fun H ε ε0 =>
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => lt_trans (by simpa using (@Rat.cast_lt ℝ _ _ _).2 (hi _ ij)) δε,
                                               -- 🎉 no goals
    fun H ε ε0 =>
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij =>
      (@Rat.cast_lt ℝ _ _ _).1 <| by simpa using hi _ ij⟩
                                     -- 🎉 no goals
#align real.is_cau_seq_iff_lift Real.isCauSeq_iff_lift

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩
#align real.of_near Real.of_near

theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  Int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x
    ⟨n, fun _ h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x
    ⟨n, le_of_lt hn⟩)
#align real.exists_floor Real.exists_floor

theorem exists_isLUB (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x, IsLUB S x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  -- ⊢ ∃ x, IsLUB S x
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ S, (m : ℝ) ≤ y * d } := by
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
  have hf₂ : ∀ n > 0, ∀ y ∈ S, (y - ((n : ℕ) : ℝ)⁻¹) < (f n / n : ℚ) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [Rat.cast_div, Rat.cast_coe_int, Rat.cast_coe_nat, gt_iff_lt]
    rwa [lt_div_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, _root_.inv_mul_cancel]
    exact ne_of_gt (Nat.cast_pos.2 n0)
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) := by
    intro ε ε0
    suffices ∀ j ≥ ⌈ε⁻¹⌉₊, ∀ k ≥ ⌈ε⁻¹⌉₊, (f j / j - f k / k : ℚ) < ε by
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
  -- ⊢ ∃ x, IsLUB S x
  refine' ⟨mk g, ⟨fun x xS => _, fun y h => _⟩⟩
  -- ⊢ x ≤ mk g
  · refine' le_of_forall_ge_of_dense fun z xz => _
    -- ⊢ z ≤ mk g
    cases' exists_nat_gt (x - z)⁻¹ with K hK
    -- ⊢ z ≤ mk g
    refine' le_mk_of_forall_le ⟨K, fun n nK => _⟩
    -- ⊢ z ≤ ↑(↑g n)
    replace xz := sub_pos.2 xz
    -- ⊢ z ≤ ↑(↑g n)
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    -- ⊢ z ≤ ↑(↑g n)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    -- ⊢ z ≤ ↑(↑g n)
    refine' le_trans _ (hf₂ _ n0 _ xS).le
    -- ⊢ z ≤ x - (↑n)⁻¹
    rwa [le_sub_comm, inv_le (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
    -- 🎉 no goals
  · exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩
#align real.exists_is_lub Real.exists_isLUB

noncomputable instance : SupSet ℝ :=
  ⟨fun S => if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB S h.1 h.2) else 0⟩

theorem sSup_def (S : Set ℝ) :
    sSup S = if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB S h.1 h.2) else 0 :=
  rfl
#align real.Sup_def Real.sSup_def

protected theorem isLUB_sSup (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddAbove S) :
    IsLUB S (sSup S) := by
  simp only [sSup_def, dif_pos (And.intro h₁ h₂)]
  -- ⊢ IsLUB S (choose (_ : ∃ x, IsLUB S x))
  apply Classical.choose_spec
  -- 🎉 no goals
#align real.is_lub_Sup Real.isLUB_sSup

noncomputable instance : InfSet ℝ :=
  ⟨fun S => -sSup (-S)⟩

theorem sInf_def (S : Set ℝ) : sInf S = -sSup (-S) :=
  rfl
#align real.Inf_def Real.sInf_def

protected theorem is_glb_sInf (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddBelow S) :
    IsGLB S (sInf S) := by
  rw [sInf_def, ← isLUB_neg', neg_neg]
  -- ⊢ IsLUB (-S) (sSup (-S))
  exact Real.isLUB_sSup _ h₁.neg h₂.neg
  -- 🎉 no goals
#align real.is_glb_Inf Real.is_glb_sInf

noncomputable instance : ConditionallyCompleteLinearOrder ℝ :=
  { Real.linearOrder, Real.lattice with
    sSup := SupSet.sSup
    sInf := InfSet.sInf
    le_csSup := fun s a hs ha => (Real.isLUB_sSup s ⟨a, ha⟩ hs).1 ha
    csSup_le := fun s a hs ha => (Real.isLUB_sSup s hs ⟨a, ha⟩).2 ha
    csInf_le := fun s a hs ha => (Real.is_glb_sInf s ⟨a, ha⟩ hs).1 ha
    le_csInf := fun s a hs ha => (Real.is_glb_sInf s hs ⟨a, ha⟩).2 ha
    csSup_of_not_bddAbove := fun s hs ↦ by simp [hs, sSup_def]
                                           -- 🎉 no goals
    csInf_of_not_bddBelow := fun s hs ↦ by simp [hs, sInf_def, sSup_def] }
                                           -- 🎉 no goals

theorem lt_sInf_add_pos {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ s, a < sInf s + ε :=
  exists_lt_of_csInf_lt h <| lt_add_of_pos_right _ hε
#align real.lt_Inf_add_pos Real.lt_sInf_add_pos

theorem add_neg_lt_sSup {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : ε < 0) :
    ∃ a ∈ s, sSup s + ε < a :=
  exists_lt_of_lt_csSup h <| add_lt_iff_neg_left.2 hε
#align real.add_neg_lt_Sup Real.add_neg_lt_sSup

theorem sInf_le_iff {s : Set ℝ} (h : BddBelow s) (h' : s.Nonempty) {a : ℝ} :
    sInf s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε := by
  rw [le_iff_forall_pos_lt_add]
  -- ⊢ (∀ (ε : ℝ), 0 < ε → sInf s < a + ε) ↔ ∀ (ε : ℝ), 0 < ε → ∃ x, x ∈ s ∧ x < a  …
  constructor <;> intro H ε ε_pos
  -- ⊢ (∀ (ε : ℝ), 0 < ε → sInf s < a + ε) → ∀ (ε : ℝ), 0 < ε → ∃ x, x ∈ s ∧ x < a  …
                  -- ⊢ ∃ x, x ∈ s ∧ x < a + ε
                  -- ⊢ sInf s < a + ε
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
    -- 🎉 no goals
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    -- ⊢ sInf s < a + ε
    exact csInf_lt_of_lt h x_in hx
    -- 🎉 no goals
#align real.Inf_le_iff Real.sInf_le_iff

theorem le_sSup_iff {s : Set ℝ} (h : BddAbove s) (h' : s.Nonempty) {a : ℝ} :
    a ≤ sSup s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x := by
  rw [le_iff_forall_pos_lt_add]
  -- ⊢ (∀ (ε : ℝ), 0 < ε → a < sSup s + ε) ↔ ∀ (ε : ℝ), ε < 0 → ∃ x, x ∈ s ∧ a + ε  …
  refine' ⟨fun H ε ε_neg => _, fun H ε ε_pos => _⟩
  -- ⊢ ∃ x, x ∈ s ∧ a + ε < x
  · exact exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
    -- 🎉 no goals
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    -- ⊢ a < sSup s + ε
    exact sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in hx)
    -- 🎉 no goals
#align real.le_Sup_iff Real.le_sSup_iff

@[simp]
theorem sSup_empty : sSup (∅ : Set ℝ) = 0 :=
  dif_neg <| by simp
                -- 🎉 no goals
#align real.Sup_empty Real.sSup_empty

theorem ciSup_empty {α : Sort*} [IsEmpty α] (f : α → ℝ) : ⨆ i, f i = 0 := by
  dsimp [iSup]
  -- ⊢ sSup (Set.range fun i => f i) = 0
  convert Real.sSup_empty
  -- ⊢ (Set.range fun i => f i) = ∅
  rw [Set.range_eq_empty_iff]
  -- ⊢ IsEmpty α
  infer_instance
  -- 🎉 no goals
#align real.csupr_empty Real.ciSup_empty

@[simp]
theorem ciSup_const_zero {α : Sort*} : ⨆ _ : α, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty α
  -- ⊢ ⨆ (x : α), 0 = 0
  · exact Real.ciSup_empty _
    -- 🎉 no goals
  · exact ciSup_const
    -- 🎉 no goals
#align real.csupr_const_zero Real.ciSup_const_zero

theorem sSup_of_not_bddAbove {s : Set ℝ} (hs : ¬BddAbove s) : sSup s = 0 :=
  dif_neg fun h => hs h.2
#align real.Sup_of_not_bdd_above Real.sSup_of_not_bddAbove

theorem iSup_of_not_bddAbove {α : Sort*} {f : α → ℝ} (hf : ¬BddAbove (Set.range f)) :
    ⨆ i, f i = 0 :=
  sSup_of_not_bddAbove hf
#align real.supr_of_not_bdd_above Real.iSup_of_not_bddAbove

theorem sSup_univ : sSup (@Set.univ ℝ) = 0 :=
  Real.sSup_of_not_bddAbove fun ⟨_, h⟩ => not_le_of_lt (lt_add_one _) <| h (Set.mem_univ _)
#align real.Sup_univ Real.sSup_univ

@[simp]
theorem sInf_empty : sInf (∅ : Set ℝ) = 0 := by simp [sInf_def, sSup_empty]
                                                -- 🎉 no goals
#align real.Inf_empty Real.sInf_empty

theorem ciInf_empty {α : Sort*} [IsEmpty α] (f : α → ℝ) : ⨅ i, f i = 0 := by
  rw [iInf_of_empty', sInf_empty]
  -- 🎉 no goals
#align real.cinfi_empty Real.ciInf_empty

@[simp]
theorem ciInf_const_zero {α : Sort*} : ⨅ _ : α, (0 : ℝ) = 0 := by
  cases isEmpty_or_nonempty α
  -- ⊢ ⨅ (x : α), 0 = 0
  · exact Real.ciInf_empty _
    -- 🎉 no goals
  · exact ciInf_const
    -- 🎉 no goals
#align real.cinfi_const_zero Real.ciInf_const_zero

theorem sInf_of_not_bddBelow {s : Set ℝ} (hs : ¬BddBelow s) : sInf s = 0 :=
  neg_eq_zero.2 <| sSup_of_not_bddAbove <| mt bddAbove_neg.1 hs
#align real.Inf_of_not_bdd_below Real.sInf_of_not_bddBelow

theorem iInf_of_not_bddBelow {α : Sort*} {f : α → ℝ} (hf : ¬BddBelow (Set.range f)) :
    ⨅ i, f i = 0 :=
  sInf_of_not_bddBelow hf
#align real.infi_of_not_bdd_below Real.iInf_of_not_bddBelow

/--
As `0` is the default value for `Real.sSup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ sSup S`.
-/
theorem sSup_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ sSup S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  -- ⊢ 0 ≤ sSup ∅
  · exact sSup_empty.ge
    -- 🎉 no goals
  · apply dite _ (fun h => le_csSup_of_le h hy <| hS y hy) fun h => (sSup_of_not_bddAbove h).ge
    -- 🎉 no goals
#align real.Sup_nonneg Real.sSup_nonneg

/--
As `0` is the default value for `Real.sSup` of the empty set or sets which are not bounded above, it
suffices to show that `f i` is nonnegative to show that `0 ≤ ⨆ i, f i`.
-/
protected theorem iSup_nonneg {ι : Sort*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ ⨆ i, f i :=
  sSup_nonneg _ <| Set.forall_range_iff.2 hf
#align real.supr_nonneg Real.iSup_nonneg

/--
As `0` is the default value for `Real.sSup` of the empty set or sets which are not bounded above, it
suffices to show that all elements of `S` are bounded by a nonnegative number to show that `sSup S`
is bounded by this number.
-/
protected theorem sSup_le {S : Set ℝ} {a : ℝ} (hS : ∀ x ∈ S, x ≤ a) (ha : 0 ≤ a) : sSup S ≤ a := by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  -- ⊢ sSup ∅ ≤ a
  exacts [sSup_empty.trans_le ha, csSup_le hS₂ hS]
  -- 🎉 no goals
#align real.Sup_le Real.sSup_le

protected theorem iSup_le {ι : Sort*} {f : ι → ℝ} {a : ℝ} (hS : ∀ i, f i ≤ a) (ha : 0 ≤ a) :
    ⨆ i, f i ≤ a :=
  Real.sSup_le (Set.forall_range_iff.2 hS) ha
#align real.supr_le Real.iSup_le

/-- As `0` is the default value for `Real.sSup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `sSup S ≤ 0`.
-/
theorem sSup_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : sSup S ≤ 0 :=
  Real.sSup_le hS le_rfl
#align real.Sup_nonpos Real.sSup_nonpos

/-- As `0` is the default value for `Real.sInf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ sInf S`.
-/
theorem sInf_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ sInf S := by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  -- ⊢ 0 ≤ sInf ∅
  exacts [sInf_empty.ge, le_csInf hS₂ hS]
  -- 🎉 no goals
#align real.Inf_nonneg Real.sInf_nonneg

/-- As `0` is the default value for `Real.sInf` of the empty set, it suffices to show that `f i` is
bounded below by `0` to show that `0 ≤ iInf f`.
-/
theorem iInf_nonneg {ι} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) : 0 ≤ iInf f :=
  sInf_nonneg _ <| Set.forall_range_iff.2 hf

/--
As `0` is the default value for `Real.sInf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `sInf S ≤ 0`.
-/
theorem sInf_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : sInf S ≤ 0 := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  -- ⊢ sInf ∅ ≤ 0
  · exact sInf_empty.le
    -- 🎉 no goals
  · apply dite _ (fun h => csInf_le_of_le h hy <| hS y hy) fun h => (sInf_of_not_bddBelow h).le
    -- 🎉 no goals
#align real.Inf_nonpos Real.sInf_nonpos

theorem sInf_le_sSup (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : sInf s ≤ sSup s := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  -- ⊢ sInf ∅ ≤ sSup ∅
  · rw [sInf_empty, sSup_empty]
    -- 🎉 no goals
  · exact csInf_le_csSup h₁ h₂ hne
    -- 🎉 no goals
#align real.Inf_le_Sup Real.sInf_le_sSup

theorem cauSeq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x := by
  let S := { x : ℝ | const abs x < f }
  -- ⊢ ∃ x, f ≈ const abs x
  have lb : ∃ x, x ∈ S := exists_lt f
  -- ⊢ ∃ x, f ≈ const abs x
  have ub' : ∀ x, f < const abs x → ∀ y ∈ S, y ≤ x := fun x h y yS =>
    le_of_lt <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀ y ∈ S, y ≤ x := (exists_gt f).imp ub'
  -- ⊢ ∃ x, f ≈ const abs x
  refine' ⟨sSup S, ((lt_total _ _).resolve_left fun h => _).resolve_right fun h => _⟩
  -- ⊢ False
  · rcases h with ⟨ε, ε0, i, ih⟩
    -- ⊢ False
    refine' (csSup_le lb (ub' _ _)).not_lt (sub_lt_self _ (half_pos ε0))
    -- ⊢ f < const abs (sSup S - ε / 2)
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    -- ⊢ ε / 2 ≤ ↑(const abs (sSup S - ε / 2) - f) j
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    -- ⊢ ε ≤ sSup S - ↑f j
    exact ih _ ij
    -- 🎉 no goals
  · rcases h with ⟨ε, ε0, i, ih⟩
    -- ⊢ False
    refine' (le_csSup ub _).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    -- ⊢ ε / 2 + sSup S ∈ S
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    -- ⊢ ε / 2 ≤ ↑(f - const abs (ε / 2 + sSup S)) j
    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
    -- ⊢ ε ≤ ↑f j - sSup S
    exact ih _ ij
    -- 🎉 no goals
#align real.cau_seq_converges Real.cauSeq_converges

instance : CauSeq.IsComplete ℝ abs :=
  ⟨cauSeq_converges⟩

open Set

theorem iInf_Ioi_eq_iInf_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : BddBelow (f '' Ioi x))
    (hf_mono : Monotone f) : ⨅ r : Ioi x, f r = ⨅ q : { q' : ℚ // x < q' }, f q := by
  refine' le_antisymm _ _
  -- ⊢ ⨅ (r : ↑(Ioi x)), f ↑r ≤ ⨅ (q : { q' // x < ↑q' }), f ↑↑q
  · have : Nonempty { r' : ℚ // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine' le_ciInf fun r => _
    -- ⊢ ⨅ (r : ↑(Ioi x)), f ↑r ≤ f ↑↑r
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    -- ⊢ ⨅ (r : ↑(Ioi x)), f ↑r ≤ f ↑↑r
    refine' ciInf_set_le hf (hxy.trans _)
    -- ⊢ ↑y < ↑↑r
    exact_mod_cast hyr
    -- 🎉 no goals
  · refine' le_ciInf fun q => _
    -- ⊢ ⨅ (q : { q' // x < ↑q' }), f ↑↑q ≤ f ↑q
    have hq := q.prop
    -- ⊢ ⨅ (q : { q' // x < ↑q' }), f ↑↑q ≤ f ↑q
    rw [mem_Ioi] at hq
    -- ⊢ ⨅ (q : { q' // x < ↑q' }), f ↑↑q ≤ f ↑q
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq
    -- ⊢ ⨅ (q : { q' // x < ↑q' }), f ↑↑q ≤ f ↑q
    refine' (ciInf_le _ _).trans _
    · refine' ⟨hf.some, fun z => _⟩
      -- ⊢ (z ∈ range fun q => f ↑↑q) → Set.Nonempty.some hf ≤ z
      rintro ⟨u, rfl⟩
      -- ⊢ Set.Nonempty.some hf ≤ (fun q => f ↑↑q) u
      suffices hfu : f u ∈ f '' Ioi x
      -- ⊢ Set.Nonempty.some hf ≤ (fun q => f ↑↑q) u
      exact hf.choose_spec hfu
      -- ⊢ f ↑↑u ∈ f '' Ioi x
      exact ⟨u, u.prop, rfl⟩
      -- 🎉 no goals
    · exact ⟨y, hxy⟩
      -- 🎉 no goals
    · refine' hf_mono (le_trans _ hyq.le)
      -- ⊢ ↑↑{ val := y, property := hxy } ≤ ↑y
      norm_cast
      -- 🎉 no goals
#align infi_Ioi_eq_infi_rat_gt Real.iInf_Ioi_eq_iInf_rat_gt

end Real
