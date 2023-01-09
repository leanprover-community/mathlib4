/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis

! This file was ported from Lean 3 source module data.real.cau_seq_completion
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.CauSeq

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a ring
with absolute value.
-/


namespace CauSeq.Completion

open CauSeq

section

parameter {α : Type _}[LinearOrderedField α]

parameter {β : Type _}[Ring β]{abv : β → α}[IsAbsoluteValue abv]

/-- The Cauchy completion of a ring with absolute value. -/
def CauchyCat :=
  @Quotient (CauSeq _ abv) CauSeq.equiv
#align cau_seq.completion.Cauchy CauSeq.Completion.CauchyCat

/-- The map from Cauchy sequences into the Cauchy completion. -/
def mk : CauSeq _ abv → Cauchy :=
  Quotient.mk''
#align cau_seq.completion.mk CauSeq.Completion.mk

@[simp]
theorem mk_eq_mk (f) : @Eq Cauchy ⟦f⟧ (mk f) :=
  rfl
#align cau_seq.completion.mk_eq_mk CauSeq.Completion.mk_eq_mk

theorem mk_eq {f g} : mk f = mk g ↔ f ≈ g :=
  Quotient.eq
#align cau_seq.completion.mk_eq CauSeq.Completion.mk_eq

/-- The map from the original ring into the Cauchy completion. -/
def ofRat (x : β) : Cauchy :=
  mk (const abv x)
#align cau_seq.completion.of_rat CauSeq.Completion.ofRat

instance : Zero Cauchy :=
  ⟨of_rat 0⟩

instance : One Cauchy :=
  ⟨of_rat 1⟩

instance : Inhabited Cauchy :=
  ⟨0⟩

theorem of_rat_zero : of_rat 0 = 0 :=
  rfl
#align cau_seq.completion.of_rat_zero CauSeq.Completion.of_rat_zero

theorem of_rat_one : of_rat 1 = 1 :=
  rfl
#align cau_seq.completion.of_rat_one CauSeq.Completion.of_rat_one

@[simp]
theorem mk_eq_zero {f} : mk f = 0 ↔ LimZero f := by
  have : mk f = 0 ↔ lim_zero (f - 0) := Quotient.eq <;> rwa [sub_zero] at this
#align cau_seq.completion.mk_eq_zero CauSeq.Completion.mk_eq_zero

instance : Add Cauchy :=
  ⟨(Quotient.map₂ (· + ·)) fun f₁ g₁ hf f₂ g₂ hg => add_equiv_add hf hg⟩

@[simp]
theorem mk_add (f g : CauSeq β abv) : mk f + mk g = mk (f + g) :=
  rfl
#align cau_seq.completion.mk_add CauSeq.Completion.mk_add

instance : Neg Cauchy :=
  ⟨(Quotient.map Neg.neg) fun f₁ f₂ hf => neg_equiv_neg hf⟩

@[simp]
theorem mk_neg (f : CauSeq β abv) : -mk f = mk (-f) :=
  rfl
#align cau_seq.completion.mk_neg CauSeq.Completion.mk_neg

instance : Mul Cauchy :=
  ⟨(Quotient.map₂ (· * ·)) fun f₁ g₁ hf f₂ g₂ hg => mul_equiv_mul hf hg⟩

@[simp]
theorem mk_mul (f g : CauSeq β abv) : mk f * mk g = mk (f * g) :=
  rfl
#align cau_seq.completion.mk_mul CauSeq.Completion.mk_mul

instance : Sub Cauchy :=
  ⟨(Quotient.map₂ Sub.sub) fun f₁ g₁ hf f₂ g₂ hg => sub_equiv_sub hf hg⟩

@[simp]
theorem mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g) :=
  rfl
#align cau_seq.completion.mk_sub CauSeq.Completion.mk_sub

instance {γ : Type _} [HasSmul γ β] [IsScalarTower γ β β] : HasSmul γ Cauchy :=
  ⟨fun c => (Quotient.map ((· • ·) c)) fun f₁ g₁ hf => smul_equiv_smul _ hf⟩

@[simp]
theorem mk_smul {γ : Type _} [HasSmul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv) :
    c • mk f = mk (c • f) :=
  rfl
#align cau_seq.completion.mk_smul CauSeq.Completion.mk_smul

instance : Pow Cauchy ℕ :=
  ⟨fun x n => Quotient.map (· ^ n) (fun f₁ g₁ hf => pow_equiv_pow hf _) x⟩

@[simp]
theorem mk_pow (n : ℕ) (f : CauSeq β abv) : mk f ^ n = mk (f ^ n) :=
  rfl
#align cau_seq.completion.mk_pow CauSeq.Completion.mk_pow

instance : NatCast Cauchy :=
  ⟨fun n => mk n⟩

instance : IntCast Cauchy :=
  ⟨fun n => mk n⟩

@[simp]
theorem of_rat_nat_cast (n : ℕ) : of_rat n = n :=
  rfl
#align cau_seq.completion.of_rat_nat_cast CauSeq.Completion.of_rat_nat_cast

@[simp]
theorem of_rat_int_cast (z : ℤ) : of_rat z = z :=
  rfl
#align cau_seq.completion.of_rat_int_cast CauSeq.Completion.of_rat_int_cast

theorem of_rat_add (x y : β) : of_rat (x + y) = of_rat x + of_rat y :=
  congr_arg mk (const_add _ _)
#align cau_seq.completion.of_rat_add CauSeq.Completion.of_rat_add

theorem of_rat_neg (x : β) : of_rat (-x) = -of_rat x :=
  congr_arg mk (const_neg _)
#align cau_seq.completion.of_rat_neg CauSeq.Completion.of_rat_neg

theorem of_rat_mul (x y : β) : of_rat (x * y) = of_rat x * of_rat y :=
  congr_arg mk (const_mul _ _)
#align cau_seq.completion.of_rat_mul CauSeq.Completion.of_rat_mul

private theorem zero_def : 0 = mk 0 :=
  rfl
#align cau_seq.completion.zero_def cau_seq.completion.zero_def

private theorem one_def : 1 = mk 1 :=
  rfl
#align cau_seq.completion.one_def cau_seq.completion.one_def

instance : Ring Cauchy :=
  Function.Surjective.ring mk (surjective_quotient_mk _) zero_def.symm one_def.symm
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

/-- `cau_seq.completion.of_rat` as a `ring_hom`  -/
@[simps]
def ofRatRingHom : β →+* Cauchy where
  toFun := of_rat
  map_zero' := of_rat_zero
  map_one' := of_rat_one
  map_add' := of_rat_add
  map_mul' := of_rat_mul
#align cau_seq.completion.of_rat_ring_hom CauSeq.Completion.ofRatRingHom

theorem of_rat_sub (x y : β) : of_rat (x - y) = of_rat x - of_rat y :=
  congr_arg mk (const_sub _ _)
#align cau_seq.completion.of_rat_sub CauSeq.Completion.of_rat_sub

end

section

parameter {α : Type _}[LinearOrderedField α]

parameter {β : Type _}[CommRing β]{abv : β → α}[IsAbsoluteValue abv]

-- mathport name: exprCauchy
local notation "Cauchy" => @CauchyCat _ _ _ _ abv _

instance : CommRing Cauchy :=
  Function.Surjective.commRing mk (surjective_quotient_mk _) zero_def.symm one_def.symm
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

end

open Classical

section

parameter {α : Type _}[LinearOrderedField α]

parameter {β : Type _}[DivisionRing β]{abv : β → α}[IsAbsoluteValue abv]

-- mathport name: exprCauchy
local notation "Cauchy" => @CauchyCat _ _ _ _ abv _

instance : RatCast Cauchy :=
  ⟨fun q => ofRat q⟩

@[simp]
theorem of_rat_rat_cast (q : ℚ) : ofRat (↑q : β) = (q : Cauchy) :=
  rfl
#align cau_seq.completion.of_rat_rat_cast CauSeq.Completion.of_rat_rat_cast

noncomputable instance : Inv Cauchy :=
  ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg =>
      by
      have := lim_zero_congr fg
      by_cases hf : lim_zero f
      · simp [hf, this.1 hf, Setoid.refl]
      · have hg := mt this.2 hf
        simp [hf, hg]
        have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf)
        have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg)
        have Ig' : mk g * mk (inv g hg) = 1 := mk_eq.2 (mul_inv_cancel hg)
        rw [mk_eq.2 fg, ← Ig] at If
        rw [← mul_one (mk (inv f hf)), ← Ig', ← mul_assoc, If, mul_assoc, Ig', mul_one]⟩

@[simp]
theorem inv_zero : (0 : Cauchy)⁻¹ = 0 :=
  congr_arg mk <| by rw [dif_pos] <;> [rfl, exact zero_lim_zero]
#align cau_seq.completion.inv_zero CauSeq.Completion.inv_zero

@[simp]
theorem inv_mk {f} (hf) : (@mk α _ β _ abv _ f)⁻¹ = mk (inv f hf) :=
  congr_arg mk <| by rw [dif_neg]
#align cau_seq.completion.inv_mk CauSeq.Completion.inv_mk

theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 := fun h =>
  have : LimZero (1 - 0) := Setoid.symm h
  have : LimZero 1 := by simpa
  one_ne_zero <| const_lim_zero.1 this
#align cau_seq.completion.cau_seq_zero_ne_one CauSeq.Completion.cau_seq_zero_ne_one

theorem zero_ne_one : (0 : Cauchy) ≠ 1 := fun h => cau_seq_zero_ne_one <| mk_eq.1 h
#align cau_seq.completion.zero_ne_one CauSeq.Completion.zero_ne_one

protected theorem inv_mul_cancel {x : Cauchy} : x ≠ 0 → x⁻¹ * x = 1 :=
  (Quotient.induction_on x) fun f hf => by
    simp at hf; simp [hf]
    exact Quotient.sound (CauSeq.inv_mul_cancel hf)
#align cau_seq.completion.inv_mul_cancel CauSeq.Completion.inv_mul_cancel

protected theorem mul_inv_cancel {x : Cauchy} : x ≠ 0 → x * x⁻¹ = 1 :=
  (Quotient.induction_on x) fun f hf => by
    simp at hf; simp [hf]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)
#align cau_seq.completion.mul_inv_cancel CauSeq.Completion.mul_inv_cancel

theorem of_rat_inv (x : β) : ofRat x⁻¹ = ((ofRat x)⁻¹ : Cauchy) :=
  congr_arg mk <| by split_ifs with h <;> [simp [const_lim_zero.1 h], rfl]
#align cau_seq.completion.of_rat_inv CauSeq.Completion.of_rat_inv

/-- The Cauchy completion forms a division ring. -/
noncomputable instance : DivisionRing Cauchy :=
  { CauchyCat.ring with
    inv := Inv.inv
    mul_inv_cancel := fun x => CauSeq.Completion.mul_inv_cancel
    exists_pair_ne := ⟨0, 1, zero_ne_one⟩
    inv_zero
    ratCast := fun q => ofRat q
    rat_cast_mk := fun n d hd hnd => by
      rw [Rat.cast_mk', of_rat_mul, of_rat_int_cast, of_rat_inv, of_rat_nat_cast] }

theorem of_rat_div (x y : β) : ofRat (x / y) = (ofRat x / ofRat y : Cauchy) := by
  simp only [div_eq_mul_inv, of_rat_inv, of_rat_mul]
#align cau_seq.completion.of_rat_div CauSeq.Completion.of_rat_div

/-- Show the first 10 items of a representative of this equivalence class of cauchy sequences.

The representative chosen is the one passed in the VM to `quot.mk`, so two cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance [Repr β] : Repr Cauchy
    where repr r :=
    let N := 10
    let seq := r.unquot
    "(sorry /- " ++ (", ".intercalate <| (List.range N).map <| repr ∘ seq) ++ ", ... -/)"

end

section

parameter {α : Type _}[LinearOrderedField α]

parameter {β : Type _}[Field β]{abv : β → α}[IsAbsoluteValue abv]

-- mathport name: exprCauchy
local notation "Cauchy" => @CauchyCat _ _ _ _ abv _

/-- The Cauchy completion forms a field. -/
noncomputable instance : Field Cauchy :=
  { CauchyCat.divisionRing, CauchyCat.commRing with }

end

end CauSeq.Completion

variable {α : Type _} [LinearOrderedField α]

namespace CauSeq

section

variable (β : Type _) [Ring β] (abv : β → α) [IsAbsoluteValue abv]

/-- A class stating that a ring with an absolute value is complete, i.e. every Cauchy
sequence has a limit. -/
class IsComplete : Prop where
  IsComplete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b
#align cau_seq.is_complete CauSeq.IsComplete

end

section

variable {β : Type _} [Ring β] {abv : β → α} [IsAbsoluteValue abv]

variable [IsComplete β abv]

theorem complete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b :=
  is_complete.is_complete
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
      rw [const_add, add_sub_add_comm] <;>
        exact add_lim_zero (Setoid.symm (equiv_lim f)) (Setoid.symm (equiv_lim g))
#align cau_seq.lim_add CauSeq.lim_add

theorem lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = lim (f * g) :=
  eq_lim_of_const_equiv <|
    show LimZero (const abv (lim f * lim g) - f * g)
      by
      have h :
        const abv (lim f * lim g) - f * g =
          (const abv (lim f) - f) * g + const abv (lim f) * (const abv (lim g) - g) :=
        by simp [const_mul (lim f), mul_add, add_mul, sub_eq_add_neg, add_comm, add_left_comm]
      rw [h] <;>
        exact
          add_lim_zero (mul_lim_zero_left _ (Setoid.symm (equiv_lim _)))
            (mul_lim_zero_right _ (Setoid.symm (equiv_lim _)))
#align cau_seq.lim_mul_lim CauSeq.lim_mul_lim

theorem lim_mul (f : CauSeq β abv) (x : β) : lim f * x = lim (f * const abv x) := by
  rw [← lim_mul_lim, lim_const]
#align cau_seq.lim_mul CauSeq.lim_mul

theorem lim_neg (f : CauSeq β abv) : lim (-f) = -lim f :=
  lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-lim f)) by
      rw [const_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg] <;>
        exact Setoid.symm (equiv_lim f))
#align cau_seq.lim_neg CauSeq.lim_neg

theorem lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔ LimZero f :=
  ⟨fun h => by
    have hf := equiv_lim f <;> rw [h] at hf <;>
      exact (lim_zero_congr hf).mpr (const_lim_zero.mpr rfl),
    fun h =>
    by
    have h₁ : f = f - const abv 0 := ext fun n => by simp [sub_apply, const_apply]
    rw [h₁] at h <;> exact lim_eq_of_equiv_const h⟩
#align cau_seq.lim_eq_zero_iff CauSeq.lim_eq_zero_iff

end

section

variable {β : Type _} [Field β] {abv : β → α} [IsAbsoluteValue abv] [IsComplete β abv]

theorem lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) : lim (inv f hf) = (lim f)⁻¹ :=
  have hl : lim f ≠ 0 := by rwa [← lim_eq_zero_iff] at hf
  lim_eq_of_equiv_const <|
    show LimZero (inv f hf - const abv (lim f)⁻¹) from
      have h₁ : ∀ (g f : CauSeq β abv) (hf : ¬LimZero f), LimZero (g - f * inv f hf * g) :=
        fun g f hf => by
        rw [← one_mul g, ← mul_assoc, ← sub_mul, mul_one, mul_comm, mul_comm f] <;>
          exact mul_lim_zero_right _ (Setoid.symm (CauSeq.inv_mul_cancel _))
      have h₂ :
        LimZero
          (inv f hf - const abv (lim f)⁻¹ -
            (const abv (lim f) - f) * (inv f hf * const abv (lim f)⁻¹)) :=
        by
        rw [sub_mul, ← sub_add, sub_sub, sub_add_eq_sub_sub, sub_right_comm, sub_add] <;>
          exact
            show
              lim_zero
                (inv f hf - const abv (lim f) * (inv f hf * const abv (lim f)⁻¹) -
                  (const abv (lim f)⁻¹ - f * (inv f hf * const abv (lim f)⁻¹)))
              from
              sub_lim_zero (by rw [← mul_assoc, mul_right_comm, const_inv hl] <;> exact h₁ _ _ _)
                (by rw [← mul_assoc] <;> exact h₁ _ _ _)
      (lim_zero_congr h₂).mpr <| mul_lim_zero_left _ (Setoid.symm (equiv_lim f))
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

