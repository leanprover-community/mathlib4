/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis
-/
import Mathlib.Algebra.Order.CauSeq.Basic

#align_import data.real.cau_seq_completion from "leanprover-community/mathlib"@"cf4c49c445991489058260d75dae0ff2b1abca28"

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a ring
with absolute value.
-/


namespace CauSeq.Completion

open CauSeq

section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

-- TODO: rename this to `CauSeq.Completion` instead of `CauSeq.Completion.Cauchy`.
/-- The Cauchy completion of a ring with absolute value. -/
def Cauchy :=
  @Quotient (CauSeq _ abv) CauSeq.equiv
set_option linter.uppercaseLean3 false in
#align cau_seq.completion.Cauchy CauSeq.Completion.Cauchy

variable {abv}

/-- The map from Cauchy sequences into the Cauchy completion. -/
def mk : CauSeq _ abv → Cauchy abv :=
  Quotient.mk''
#align cau_seq.completion.mk CauSeq.Completion.mk

@[simp]
theorem mk_eq_mk (f : CauSeq _ abv) : @Eq (Cauchy abv) ⟦f⟧ (mk f) :=
  rfl
#align cau_seq.completion.mk_eq_mk CauSeq.Completion.mk_eq_mk

theorem mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ f ≈ g :=
  Quotient.eq
#align cau_seq.completion.mk_eq CauSeq.Completion.mk_eq

/-- The map from the original ring into the Cauchy completion. -/
def ofRat (x : β) : Cauchy abv :=
  mk (const abv x)
#align cau_seq.completion.of_rat CauSeq.Completion.ofRat

instance : Zero (Cauchy abv) :=
  ⟨ofRat 0⟩

instance : One (Cauchy abv) :=
  ⟨ofRat 1⟩

instance : Inhabited (Cauchy abv) :=
  ⟨0⟩

theorem ofRat_zero : (ofRat 0 : Cauchy abv) = 0 :=
  rfl
#align cau_seq.completion.of_rat_zero CauSeq.Completion.ofRat_zero

theorem ofRat_one : (ofRat 1 : Cauchy abv) = 1 :=
  rfl
#align cau_seq.completion.of_rat_one CauSeq.Completion.ofRat_one

@[simp]
theorem mk_eq_zero {f : CauSeq _ abv} : mk f = 0 ↔ LimZero f := by
  have : mk f = 0 ↔ LimZero (f - 0) := Quotient.eq
  rwa [sub_zero] at this
#align cau_seq.completion.mk_eq_zero CauSeq.Completion.mk_eq_zero

instance : Add (Cauchy abv) :=
  ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

@[simp]
theorem mk_add (f g : CauSeq β abv) : mk f + mk g = mk (f + g) :=
  rfl
#align cau_seq.completion.mk_add CauSeq.Completion.mk_add

instance : Neg (Cauchy abv) :=
  ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩

@[simp]
theorem mk_neg (f : CauSeq β abv) : -mk f = mk (-f) :=
  rfl
#align cau_seq.completion.mk_neg CauSeq.Completion.mk_neg

instance : Mul (Cauchy abv) :=
  ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

@[simp]
theorem mk_mul (f g : CauSeq β abv) : mk f * mk g = mk (f * g) :=
  rfl
#align cau_seq.completion.mk_mul CauSeq.Completion.mk_mul

instance : Sub (Cauchy abv) :=
  ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩

@[simp]
theorem mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g) :=
  rfl
#align cau_seq.completion.mk_sub CauSeq.Completion.mk_sub

instance {γ : Type*} [SMul γ β] [IsScalarTower γ β β] : SMul γ (Cauchy abv) :=
  ⟨fun c => (Quotient.map (c • ·)) fun _ _ hf => smul_equiv_smul _ hf⟩

@[simp]
theorem mk_smul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv) :
    c • mk f = mk (c • f) :=
  rfl
#align cau_seq.completion.mk_smul CauSeq.Completion.mk_smul

instance : Pow (Cauchy abv) ℕ :=
  ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩

@[simp]
theorem mk_pow (n : ℕ) (f : CauSeq β abv) : mk f ^ n = mk (f ^ n) :=
  rfl
#align cau_seq.completion.mk_pow CauSeq.Completion.mk_pow

instance : NatCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

instance : IntCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

@[simp]
theorem ofRat_natCast (n : ℕ) : (ofRat n : Cauchy abv) = n :=
  rfl
#align cau_seq.completion.of_rat_nat_cast CauSeq.Completion.ofRat_natCast

@[simp]
theorem ofRat_intCast (z : ℤ) : (ofRat z : Cauchy abv) = z :=
  rfl
#align cau_seq.completion.of_rat_int_cast CauSeq.Completion.ofRat_intCast

theorem ofRat_add (x y : β) :
    ofRat (x + y) = (ofRat x + ofRat y : Cauchy abv) :=
  congr_arg mk (const_add _ _)
#align cau_seq.completion.of_rat_add CauSeq.Completion.ofRat_add

theorem ofRat_neg (x : β) : ofRat (-x) = (-ofRat x : Cauchy abv) :=
  congr_arg mk (const_neg _)
#align cau_seq.completion.of_rat_neg CauSeq.Completion.ofRat_neg

theorem ofRat_mul (x y : β) :
    ofRat (x * y) = (ofRat x * ofRat y : Cauchy abv) :=
  congr_arg mk (const_mul _ _)
#align cau_seq.completion.of_rat_mul CauSeq.Completion.ofRat_mul

private theorem zero_def : 0 = @mk _ _ _ _ abv _ 0 :=
  rfl

private theorem one_def : 1 = @mk _ _ _ _ abv _ 1 :=
  rfl

instance Cauchy.ring : Ring (Cauchy abv) :=
  Function.Surjective.ring mk (surjective_quotient_mk' _) zero_def.symm one_def.symm
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

/-- `CauSeq.Completion.ofRat` as a `RingHom` -/
@[simps]
def ofRatRingHom : β →+* (Cauchy abv) where
  toFun := ofRat
  map_zero' := ofRat_zero
  map_one' := ofRat_one
  map_add' := ofRat_add
  map_mul' := ofRat_mul
#align cau_seq.completion.of_rat_ring_hom CauSeq.Completion.ofRatRingHom
#align cau_seq.completion.of_rat_ring_hom_apply CauSeq.Completion.ofRatRingHom_apply

theorem ofRat_sub (x y : β) : ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv) :=
  congr_arg mk (const_sub _ _)
#align cau_seq.completion.of_rat_sub CauSeq.Completion.ofRat_sub

end

section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [CommRing β] {abv : β → α} [IsAbsoluteValue abv]

instance Cauchy.commRing : CommRing (Cauchy abv) :=
  Function.Surjective.commRing mk (surjective_quotient_mk' _) zero_def.symm one_def.symm
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

end

open scoped Classical

section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

instance instNNRatCast : NNRatCast (Cauchy abv) where nnratCast q := ofRat q
instance instRatCast : RatCast (Cauchy abv) where ratCast q := ofRat q

@[simp, norm_cast] lemma ofRat_nnratCast (q : ℚ≥0) : ofRat (q : β) = (q : Cauchy abv) := rfl
@[simp, norm_cast] lemma ofRat_ratCast (q : ℚ) : ofRat (q : β) = (q : Cauchy abv) := rfl
#align cau_seq.completion.of_rat_rat_cast CauSeq.Completion.ofRat_ratCast

noncomputable instance : Inv (Cauchy abv) :=
  ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg => by
      have := limZero_congr fg
      by_cases hf : LimZero f
      · simp [hf, this.1 hf, Setoid.refl]
      · have hg := mt this.2 hf
        simp only [hf, dite_false, hg]
        have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf)
        have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg)
        have Ig' : mk g * mk (inv g hg) = 1 := mk_eq.2 (mul_inv_cancel hg)
        rw [mk_eq.2 fg, ← Ig] at If
        rw [← mul_one (mk (inv f hf)), ← Ig', ← mul_assoc, If, mul_assoc, Ig', mul_one]⟩

-- porting note (#10618): simp can prove this
-- @[simp]
theorem inv_zero : (0 : (Cauchy abv))⁻¹ = 0 :=
  congr_arg mk <| by rw [dif_pos] <;> [rfl; exact zero_limZero]
#align cau_seq.completion.inv_zero CauSeq.Completion.inv_zero

@[simp]
theorem inv_mk {f} (hf) : (@mk α _ β _ abv _ f)⁻¹ = mk (inv f hf) :=
  congr_arg mk <| by rw [dif_neg]
#align cau_seq.completion.inv_mk CauSeq.Completion.inv_mk

theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 := fun h =>
  have : LimZero (1 - 0 : CauSeq _ abv) := Setoid.symm h
  have : LimZero 1 := by simpa
  by apply one_ne_zero <| const_limZero.1 this
#align cau_seq.completion.cau_seq_zero_ne_one CauSeq.Completion.cau_seq_zero_ne_one

theorem zero_ne_one : (0 : (Cauchy abv)) ≠ 1 := fun h => cau_seq_zero_ne_one <| mk_eq.1 h
#align cau_seq.completion.zero_ne_one CauSeq.Completion.zero_ne_one

protected theorem inv_mul_cancel {x : (Cauchy abv)} : x ≠ 0 → x⁻¹ * x = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.inv_mul_cancel hf)
#align cau_seq.completion.inv_mul_cancel CauSeq.Completion.inv_mul_cancel

protected theorem mul_inv_cancel {x : (Cauchy abv)} : x ≠ 0 → x * x⁻¹ = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)
#align cau_seq.completion.mul_inv_cancel CauSeq.Completion.mul_inv_cancel

theorem ofRat_inv (x : β) : ofRat x⁻¹ = ((ofRat x)⁻¹ : (Cauchy abv)) :=
  congr_arg mk <| by split_ifs with h <;>
    [simp only [const_limZero.1 h, GroupWithZero.inv_zero, const_zero]; rfl]
#align cau_seq.completion.of_rat_inv CauSeq.Completion.ofRat_inv

noncomputable instance instDivInvMonoid : DivInvMonoid (Cauchy abv) where

lemma ofRat_div (x y : β) : ofRat (x / y) = (ofRat x / ofRat y : Cauchy abv) := by
  simp only [div_eq_mul_inv, ofRat_inv, ofRat_mul]
#align cau_seq.completion.of_rat_div CauSeq.Completion.ofRat_div

/-- The Cauchy completion forms a division ring. -/
noncomputable instance Cauchy.divisionRing : DivisionRing (Cauchy abv) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  inv_zero := inv_zero
  mul_inv_cancel x := CauSeq.Completion.mul_inv_cancel
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by simp_rw [← ofRat_nnratCast, NNRat.cast_def, ofRat_div, ofRat_natCast]
  ratCast_def q := by rw [← ofRat_ratCast, Rat.cast_def, ofRat_div, ofRat_natCast, ofRat_intCast]
  nnqsmul_def q x := Quotient.inductionOn x fun f ↦ congr_arg mk <| ext fun i ↦ NNRat.smul_def _ _
  qsmul_def q x := Quotient.inductionOn x fun f ↦ congr_arg mk <| ext fun i ↦ Rat.smul_def _ _

/-- Show the first 10 items of a representative of this equivalence class of cauchy sequences.

The representative chosen is the one passed in the VM to `Quot.mk`, so two cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance [Repr β] : Repr (Cauchy abv) where
  reprPrec r _ :=
    let N := 10
    let seq := r.unquot
    "(sorry /- " ++ Std.Format.joinSep ((List.range N).map <| repr ∘ seq) ", " ++ ", ... -/)"

end

section

variable {α : Type*} [LinearOrderedField α]
variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv]

/-- The Cauchy completion forms a field. -/
noncomputable instance Cauchy.field : Field (Cauchy abv) :=
  { Cauchy.divisionRing, Cauchy.commRing with }

end

end CauSeq.Completion

variable {α : Type*} [LinearOrderedField α]

namespace CauSeq

section

variable (β : Type*) [Ring β] (abv : β → α) [IsAbsoluteValue abv]

/-- A class stating that a ring with an absolute value is complete, i.e. every Cauchy
sequence has a limit. -/
class IsComplete : Prop where
  /-- Every Cauchy sequence has a limit. -/
  isComplete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b
#align cau_seq.is_complete CauSeq.IsComplete
#align cau_seq.is_complete.is_complete CauSeq.IsComplete.isComplete

end

section

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]
variable [IsComplete β abv]

theorem complete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b :=
  IsComplete.isComplete
#align cau_seq.complete CauSeq.complete

/-- The limit of a Cauchy sequence in a complete ring. Chosen non-computably. -/
noncomputable def lim (s : CauSeq β abv) : β :=
  Classical.choose (complete s)
#align cau_seq.lim CauSeq.lim

theorem equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s) :=
  Classical.choose_spec (complete s)
#align cau_seq.equiv_lim CauSeq.equiv_lim

theorem eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f) : x = lim f :=
  const_equiv.mp <| Setoid.trans h <| equiv_lim f
#align cau_seq.eq_lim_of_const_equiv CauSeq.eq_lim_of_const_equiv

theorem lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x) : lim f = x :=
  (eq_lim_of_const_equiv <| Setoid.symm h).symm
#align cau_seq.lim_eq_of_equiv_const CauSeq.lim_eq_of_equiv_const

theorem lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : lim f = lim g :=
  lim_eq_of_equiv_const <| Setoid.trans h <| equiv_lim g
#align cau_seq.lim_eq_lim_of_equiv CauSeq.lim_eq_lim_of_equiv

@[simp]
theorem lim_const (x : β) : lim (const abv x) = x :=
  lim_eq_of_equiv_const <| Setoid.refl _
#align cau_seq.lim_const CauSeq.lim_const

theorem lim_add (f g : CauSeq β abv) : lim f + lim g = lim (f + g) :=
  eq_lim_of_const_equiv <|
    show LimZero (const abv (lim f + lim g) - (f + g)) by
      rw [const_add, add_sub_add_comm]
      exact add_limZero (Setoid.symm (equiv_lim f)) (Setoid.symm (equiv_lim g))
#align cau_seq.lim_add CauSeq.lim_add

theorem lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = lim (f * g) :=
  eq_lim_of_const_equiv <|
    show LimZero (const abv (lim f * lim g) - f * g) by
      have h :
        const abv (lim f * lim g) - f * g =
          (const abv (lim f) - f) * g + const abv (lim f) * (const abv (lim g) - g) := by
              apply Subtype.ext
              rw [coe_add]
              simp [sub_mul, mul_sub]
      rw [h]
      exact
        add_limZero (mul_limZero_left _ (Setoid.symm (equiv_lim _)))
          (mul_limZero_right _ (Setoid.symm (equiv_lim _)))
#align cau_seq.lim_mul_lim CauSeq.lim_mul_lim

theorem lim_mul (f : CauSeq β abv) (x : β) : lim f * x = lim (f * const abv x) := by
  rw [← lim_mul_lim, lim_const]
#align cau_seq.lim_mul CauSeq.lim_mul

theorem lim_neg (f : CauSeq β abv) : lim (-f) = -lim f :=
  lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-lim f)) by
      rw [const_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
      exact Setoid.symm (equiv_lim f))
#align cau_seq.lim_neg CauSeq.lim_neg

theorem lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔ LimZero f :=
  ⟨fun h => by
    have hf := equiv_lim f
    rw [h] at hf
    exact (limZero_congr hf).mpr (const_limZero.mpr rfl),
   fun h => by
    have h₁ : f = f - const abv 0 := ext fun n => by simp [sub_apply, const_apply]
    rw [h₁] at h
    exact lim_eq_of_equiv_const h⟩
#align cau_seq.lim_eq_zero_iff CauSeq.lim_eq_zero_iff

end

section

variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv] [IsComplete β abv]

theorem lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) : lim (inv f hf) = (lim f)⁻¹ :=
  have hl : lim f ≠ 0 := by rwa [← lim_eq_zero_iff] at hf
  lim_eq_of_equiv_const <|
    show LimZero (inv f hf - const abv (lim f)⁻¹) from
      have h₁ : ∀ (g f : CauSeq β abv) (hf : ¬LimZero f), LimZero (g - f * inv f hf * g) :=
        fun g f hf => by
          have h₂ : g - f * inv f hf * g = 1 * g - f * inv f hf * g := by rw [one_mul g]
          have h₃ : f * inv f hf * g = (f * inv f hf) * g := by simp [mul_assoc]
          have h₄ : g - f * inv f hf * g = (1 - f * inv f hf) * g := by rw [h₂, h₃, ← sub_mul]
          have h₅ : g - f * inv f hf * g = g * (1 - f * inv f hf) := by rw [h₄, mul_comm]
          have h₆ : g - f * inv f hf * g = g * (1 - inv f hf * f) := by rw [h₅, mul_comm f]
          rw [h₆]; exact mul_limZero_right _ (Setoid.symm (CauSeq.inv_mul_cancel _))
      have h₂ :
        LimZero
          (inv f hf - const abv (lim f)⁻¹ -
            (const abv (lim f) - f) * (inv f hf * const abv (lim f)⁻¹)) := by
              rw [sub_mul, ← sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add]
              show LimZero
                (inv f hf - const abv (lim f) * (inv f hf * const abv (lim f)⁻¹) -
                  (const abv (lim f)⁻¹ - f * (inv f hf * const abv (lim f)⁻¹)))
              exact sub_limZero
                (by rw [← mul_assoc, mul_right_comm, const_inv hl]; exact h₁ _ _ _)
                (by rw [← mul_assoc]; exact h₁ _ _ _)
      (limZero_congr h₂).mpr <| mul_limZero_left _ (Setoid.symm (equiv_lim f))
#align cau_seq.lim_inv CauSeq.lim_inv

end

section

variable [IsComplete α abs]

theorem lim_le {f : CauSeq α abs} {x : α} (h : f ≤ CauSeq.const abs x) : lim f ≤ x :=
  CauSeq.const_le.1 <| CauSeq.le_of_eq_of_le (Setoid.symm (equiv_lim f)) h
#align cau_seq.lim_le CauSeq.lim_le

theorem le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x ≤ f) : x ≤ lim f :=
  CauSeq.const_le.1 <| CauSeq.le_of_le_of_eq h (equiv_lim f)
#align cau_seq.le_lim CauSeq.le_lim

theorem lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < lim f :=
  CauSeq.const_lt.1 <| CauSeq.lt_of_lt_of_eq h (equiv_lim f)
#align cau_seq.lt_lim CauSeq.lt_lim

theorem lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : lim f < x :=
  CauSeq.const_lt.1 <| CauSeq.lt_of_eq_of_lt (Setoid.symm (equiv_lim f)) h
#align cau_seq.lim_lt CauSeq.lim_lt

end

end CauSeq
