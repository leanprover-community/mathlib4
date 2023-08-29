/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Data.Real.Sqrt

#align_import data.complex.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. The result that the complex numbers are algebraically closed, see
`FieldTheory.AlgebraicClosure`.
-/


open BigOperators

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
structure Complex : Type where
  re : ℝ
  im : ℝ
#align complex Complex


notation "ℂ" => Complex

namespace Complex

open ComplexConjugate

noncomputable instance : DecidableEq ℂ :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps apply]
def equivRealProd : ℂ ≃ ℝ × ℝ where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align complex.equiv_real_prod Complex.equivRealProd

@[simp]
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl
#align complex.eta Complex.eta

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl
#align complex.ext Complex.ext

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  ⟨fun H => by simp [H], fun h => ext h.1 h.2⟩
               -- 🎉 no goals
#align complex.ext_iff Complex.ext_iff

theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩
#align complex.re_surjective Complex.re_surjective

theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩
#align complex.im_surjective Complex.im_surjective

@[simp]
theorem range_re : range re = univ :=
  re_surjective.range_eq
#align complex.range_re Complex.range_re

@[simp]
theorem range_im : range im = univ :=
  im_surjective.range_eq
#align complex.range_im Complex.range_im

-- Porting note: refactored instance to allow `norm_cast` to work
/-- The natural inclusion of the real numbers into the complex numbers.
The name `Complex.ofReal` is reserved for the bundled homomorphism. -/
@[coe]
def ofReal' (r : ℝ) : ℂ :=
  ⟨r, 0⟩
instance : Coe ℝ ℂ :=
  ⟨ofReal'⟩

@[simp, norm_cast]
theorem ofReal_re (r : ℝ) : Complex.re (r : ℂ) = r :=
  rfl
#align complex.of_real_re Complex.ofReal_re

@[simp, norm_cast]
theorem ofReal_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl
#align complex.of_real_im Complex.ofReal_im

theorem ofReal_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ :=
  rfl
#align complex.of_real_def Complex.ofReal_def

@[simp, norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩
                   -- 🎉 no goals
#align complex.of_real_inj Complex.ofReal_inj

-- Porting note: made coercion explicit
theorem ofReal_injective : Function.Injective ((↑) : ℝ → ℂ) := fun _ _ => congrArg re
#align complex.of_real_injective Complex.ofReal_injective

-- Porting note: made coercion explicit
instance canLift : CanLift ℂ ℝ (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩
#align complex.can_lift Complex.canLift

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def Set.reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t
#align set.re_prod_im Complex.Set.reProdIm

infixl:72 " ×ℂ " => Set.reProdIm

theorem mem_reProdIm {z : ℂ} {s t : Set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t :=
  Iff.rfl
#align complex.mem_re_prod_im Complex.mem_reProdIm

instance : Zero ℂ :=
  ⟨(0 : ℝ)⟩

instance : Inhabited ℂ :=
  ⟨0⟩

@[simp]
theorem zero_re : (0 : ℂ).re = 0 :=
  rfl
#align complex.zero_re Complex.zero_re

@[simp]
theorem zero_im : (0 : ℂ).im = 0 :=
  rfl
#align complex.zero_im Complex.zero_im

@[simp, norm_cast]
theorem ofReal_zero : ((0 : ℝ) : ℂ) = 0 :=
  rfl
#align complex.of_real_zero Complex.ofReal_zero

@[simp]
theorem ofReal_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
  ofReal_inj
#align complex.of_real_eq_zero Complex.ofReal_eq_zero

theorem ofReal_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
  not_congr ofReal_eq_zero
#align complex.of_real_ne_zero Complex.ofReal_ne_zero

instance : One ℂ :=
  ⟨(1 : ℝ)⟩

@[simp]
theorem one_re : (1 : ℂ).re = 1 :=
  rfl
#align complex.one_re Complex.one_re

@[simp]
theorem one_im : (1 : ℂ).im = 0 :=
  rfl
#align complex.one_im Complex.one_im

@[simp, norm_cast]
theorem ofReal_one : ((1 : ℝ) : ℂ) = 1 :=
  rfl
#align complex.of_real_one Complex.ofReal_one

@[simp]
theorem ofReal_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 :=
  ofReal_inj
#align complex.of_real_eq_one Complex.ofReal_eq_one

theorem ofReal_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 :=
  not_congr ofReal_eq_one
#align complex.of_real_ne_one Complex.ofReal_ne_one

instance : Add ℂ :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re :=
  rfl
#align complex.add_re Complex.add_re

@[simp]
theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im :=
  rfl
#align complex.add_im Complex.add_im

section
set_option linter.deprecated false
@[simp]
theorem bit0_re (z : ℂ) : (bit0 z).re = bit0 z.re :=
  rfl
#align complex.bit0_re Complex.bit0_re

@[simp]
theorem bit1_re (z : ℂ) : (bit1 z).re = bit1 z.re :=
  rfl
#align complex.bit1_re Complex.bit1_re

@[simp]
theorem bit0_im (z : ℂ) : (bit0 z).im = bit0 z.im :=
  Eq.refl _
#align complex.bit0_im Complex.bit0_im

@[simp]
theorem bit1_im (z : ℂ) : (bit1 z).im = bit0 z.im :=
  add_zero _
#align complex.bit1_im Complex.bit1_im

@[simp, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  ext_iff.2 <| by simp [ofReal']
                  -- 🎉 no goals
#align complex.of_real_add Complex.ofReal_add

@[simp, norm_cast]
theorem ofReal_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 (r : ℂ)  :=
  ext_iff.2 <| by simp [bit0]
                  -- 🎉 no goals
#align complex.of_real_bit0 Complex.ofReal_bit0

@[simp, norm_cast]
theorem ofReal_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 (r : ℂ) :=
  ext_iff.2 <| by simp [bit1]
                  -- 🎉 no goals
#align complex.of_real_bit1 Complex.ofReal_bit1

end

instance : Neg ℂ :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
theorem neg_re (z : ℂ) : (-z).re = -z.re :=
  rfl
#align complex.neg_re Complex.neg_re

@[simp]
theorem neg_im (z : ℂ) : (-z).im = -z.im :=
  rfl
#align complex.neg_im Complex.neg_im

@[simp, norm_cast]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
  ext_iff.2 <| by simp [ofReal']
                  -- 🎉 no goals
#align complex.of_real_neg Complex.ofReal_neg

instance : Sub ℂ :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

instance : Mul ℂ :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp]
theorem mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  rfl
#align complex.mul_re Complex.mul_re

@[simp]
theorem mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl
#align complex.mul_im Complex.mul_im

@[simp, norm_cast]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  ext_iff.2 <| by simp [ofReal']
                  -- 🎉 no goals
#align complex.of_real_mul Complex.ofReal_mul

theorem ofReal_mul_re (r : ℝ) (z : ℂ) : (↑r * z).re = r * z.re := by simp [ofReal']
                                                                     -- 🎉 no goals
#align complex.of_real_mul_re Complex.ofReal_mul_re

theorem ofReal_mul_im (r : ℝ) (z : ℂ) : (↑r * z).im = r * z.im := by simp [ofReal']
                                                                     -- 🎉 no goals
#align complex.of_real_mul_im Complex.ofReal_mul_im

theorem ofReal_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (ofReal_mul_re _ _) (ofReal_mul_im _ _)
#align complex.of_real_mul' Complex.ofReal_mul'

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
def I : ℂ :=
  ⟨0, 1⟩
set_option linter.uppercaseLean3 false in
#align complex.I Complex.I

@[simp]
theorem I_re : I.re = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align complex.I_re Complex.I_re

@[simp]
theorem I_im : I.im = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align complex.I_im Complex.I_im

@[simp]
theorem I_mul_I : I * I = -1 :=
  ext_iff.2 <| by simp
                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_mul_I Complex.I_mul_I

theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  ext_iff.2 <| by simp
                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_mul Complex.I_mul

theorem I_ne_zero : (I : ℂ) ≠ 0 :=
  mt (congr_arg im) zero_ne_one.symm
set_option linter.uppercaseLean3 false in
#align complex.I_ne_zero Complex.I_ne_zero

theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  ext_iff.2 <| by simp [ofReal']
                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.mk_eq_add_mul_I Complex.mk_eq_add_mul_I

@[simp]
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  ext_iff.2 <| by simp [ofReal']
                  -- 🎉 no goals
#align complex.re_add_im Complex.re_add_im

theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp
                                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.mul_I_re Complex.mul_I_re

theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by simp
                                                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.mul_I_im Complex.mul_I_im

theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp
                                                    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_mul_re Complex.I_mul_re

theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by simp
                                                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_mul_im Complex.I_mul_im

@[simp]
theorem equivRealProd_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal']
  -- ⊢ (↑equivRealProd.symm p).re = (↑p.fst + ↑p.snd * I).re
          -- 🎉 no goals
          -- 🎉 no goals
#align complex.equiv_real_prod_symm_apply Complex.equivRealProd_symm_apply

/-! ### Commutative ring instance and lemmas -/


/- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `Data.Complex.Module`. -/
instance : Nontrivial ℂ :=
  pullback_nonzero re rfl rfl

-- porting note: moved from `Module/Data/Complex/Basic.lean`
section SMul

variable {R : Type*} [SMul R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`RestrictScalars.module ℝ ℂ ℂ = Complex.module` definitionally. -/
instance instSMulRealComplex : SMul R ℂ where
  smul r x := ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(· • ·), SMul.smul]
                                                              -- 🎉 no goals
#align complex.smul_re Complex.smul_re

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(· • ·), SMul.smul]
                                                              -- 🎉 no goals
#align complex.smul_im Complex.smul_im

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl
#align complex.real_smul Complex.real_smul

end SMul

-- Porting note: proof needed modifications and rewritten fields
instance addCommGroup : AddCommGroup ℂ :=
  { zero := (0 : ℂ)
    add := (· + ·)
    neg := Neg.neg
    sub := Sub.sub
    nsmul := fun n z => n • z
    zsmul := fun n z => n • z
    zsmul_zero' := by intros; ext <;> simp [smul_re, smul_im]
                      -- ⊢ (fun n z => n • z) 0 a✝ = 0
                     -- ⊢ (fun n z => n • z) 0 x✝ = 0
                             -- ⊢ ((fun n z => n • z) 0 x✝).re = 0.re
                                     -- 🎉 no goals
                                     -- 🎉 no goals
                              -- ⊢ ((fun n z => n • z) 0 a✝).re = 0.re
                                      -- 🎉 no goals
      -- ⊢ (fun n z => n • z) (n✝ + 1) x✝ = x✝ + (fun n z => n • z) n✝ x✝
              -- ⊢ ((fun n z => n • z) (n✝ + 1) x✝).re = (x✝ + (fun n z => n • z) n✝ x✝).re
                                      -- 🎉 no goals
                    -- ⊢ a✝ + b✝ + c✝ = a✝ + (b✝ + c✝)
                            -- ⊢ (a✝ + b✝ + c✝).re = (a✝ + (b✝ + c✝)).re
                                    -- 🎉 no goals
                                    -- 🎉 no goals
    nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
                   -- ⊢ 0 + a✝ = a✝
                           -- ⊢ (0 + a✝).re = a✝.re
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    nsmul_succ := by
                   -- ⊢ a✝ + 0 = a✝
                           -- ⊢ (a✝ + 0).re = a✝.re
                                   -- 🎉 no goals
                                   -- 🎉 no goals
      intros; ext <;> simp [AddMonoid.nsmul_succ, add_mul, add_comm,
        smul_re, smul_im]
    zsmul_succ' := by
      intros; ext <;> simp [SubNegMonoid.zsmul_succ', add_mul, add_comm,
      -- ⊢ (fun n z => n • z) (Int.ofNat (Nat.succ n✝)) a✝ = a✝ + (fun n z => n • z) (I …
              -- ⊢ ((fun n z => n • z) (Int.ofNat (Nat.succ n✝)) a✝).re = (a✝ + (fun n z => n • …
        smul_re, smul_im]
    zsmul_neg' := by
      intros; ext <;> simp [zsmul_neg', add_mul, smul_re, smul_im]
      -- ⊢ (fun n z => n • z) (Int.negSucc n✝) a✝ = -(fun n z => n • z) (↑(Nat.succ n✝) …
              -- ⊢ ((fun n z => n • z) (Int.negSucc n✝) a✝).re = (-(fun n z => n • z) (↑(Nat.su …
                      -- 🎉 no goals
                      -- 🎉 no goals
    add_assoc := by intros; ext <;> simp [add_assoc]
    zero_add := by intros; ext <;> simp
    add_zero := by intros; ext <;> simp
    add_comm := by intros; ext <;> simp [add_comm]
                   -- ⊢ a✝ + b✝ = b✝ + a✝
                       -- ⊢ -a✝ + a✝ = 0
                               -- ⊢ (-a✝ + a✝).re = 0.re
                                       -- 🎉 no goals
                                       -- 🎉 no goals
                           -- ⊢ (a✝ + b✝).re = (b✝ + a✝).re
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    add_left_neg := by intros; ext <;> simp }


instance Complex.addGroupWithOne : AddGroupWithOne ℂ :=
  { Complex.addCommGroup with
    natCast := fun n => ⟨n, 0⟩
    natCast_zero := by
      ext <;> simp [Nat.cast, AddMonoidWithOne.natCast_zero]
      -- ⊢ (NatCast.natCast 0).re = 0.re
              -- 🎉 no goals
              -- 🎉 no goals
    natCast_succ := fun _ => by ext <;> simp [Nat.cast, AddMonoidWithOne.natCast_succ]
                                -- ⊢ (NatCast.natCast (x✝ + 1)).re = (NatCast.natCast x✝ + 1).re
                                        -- 🎉 no goals
                                        -- 🎉 no goals
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun _ => by ext <;> rfl
                                 -- ⊢ (IntCast.intCast ↑x✝).re = (↑x✝).re
                                         -- 🎉 no goals
                                         -- 🎉 no goals
    intCast_negSucc := fun n => by
      ext
      -- ⊢ (IntCast.intCast (Int.negSucc n)).re = (-↑(n + 1)).re
      · simp [AddGroupWithOne.intCast_negSucc]
        -- ⊢ -1 + -↑n = -(↑(n + 1)).re
        show -(1: ℝ) + (-n) = -(↑(n + 1))
        -- ⊢ -1 + -↑n = -↑(n + 1)
        simp [Nat.cast_add, add_comm]
        -- 🎉 no goals
      · simp [AddGroupWithOne.intCast_negSucc]
        -- ⊢ (↑(n + 1)).im = 0
        show im ⟨n, 0⟩ = 0
        -- ⊢ { re := ↑n, im := 0 }.im = 0
        rfl
        -- 🎉 no goals
    one := 1 }

-- Porting note: proof needed modifications and rewritten fields
instance commRing : CommRing ℂ :=
  { Complex.addGroupWithOne with
    zero := (0 : ℂ)
    add := (· + ·)
    one := 1
    mul := (· * ·)
    npow := @npowRec _ ⟨(1 : ℂ)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp [add_comm]
                   -- ⊢ a✝ + b✝ = b✝ + a✝
                           -- ⊢ (a✝ + b✝).re = (b✝ + a✝).re
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    left_distrib := by
      intros; ext <;> simp [mul_re, mul_im] <;> ring
      -- ⊢ a✝ * (b✝ + c✝) = a✝ * b✝ + a✝ * c✝
              -- ⊢ (a✝ * (b✝ + c✝)).re = (a✝ * b✝ + a✝ * c✝).re
                      -- ⊢ a✝.re * (b✝.re + c✝.re) - a✝.im * (b✝.im + c✝.im) = a✝.re * b✝.re - a✝.im *  …
                      -- ⊢ a✝.re * (b✝.im + c✝.im) + a✝.im * (b✝.re + c✝.re) = a✝.re * b✝.im + a✝.im *  …
                                                -- 🎉 no goals
                                                -- 🎉 no goals
    right_distrib := by
      intros; ext <;> simp [mul_re, mul_im] <;> ring
      -- ⊢ (a✝ + b✝) * c✝ = a✝ * c✝ + b✝ * c✝
              -- ⊢ ((a✝ + b✝) * c✝).re = (a✝ * c✝ + b✝ * c✝).re
                      -- ⊢ (a✝.re + b✝.re) * c✝.re - (a✝.im + b✝.im) * c✝.im = a✝.re * c✝.re - a✝.im *  …
                      -- ⊢ (a✝.re + b✝.re) * c✝.im + (a✝.im + b✝.im) * c✝.re = a✝.re * c✝.im + a✝.im *  …
                                                -- 🎉 no goals
                                                -- 🎉 no goals
    zero_mul := by intros; ext <;> simp [zero_mul]
                   -- ⊢ 0 * a✝ = 0
                           -- ⊢ (0 * a✝).re = 0.re
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    mul_zero := by intros; ext <;> simp [mul_zero]
                   -- ⊢ a✝ * 0 = 0
                           -- ⊢ (a✝ * 0).re = 0.re
                                   -- 🎉 no goals
                                   -- 🎉 no goals
    mul_assoc := by intros; ext <;> simp [mul_assoc] <;> ring
                    -- ⊢ a✝ * b✝ * c✝ = a✝ * (b✝ * c✝)
                            -- ⊢ (a✝ * b✝ * c✝).re = (a✝ * (b✝ * c✝)).re
                                    -- ⊢ (a✝.re * b✝.re - a✝.im * b✝.im) * c✝.re - (a✝.re * b✝.im + a✝.im * b✝.re) *  …
                                    -- ⊢ (a✝.re * b✝.re - a✝.im * b✝.im) * c✝.im + (a✝.re * b✝.im + a✝.im * b✝.re) *  …
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
    one_mul := by intros; ext <;> simp [one_mul]
                  -- ⊢ 1 * a✝ = a✝
                          -- ⊢ (1 * a✝).re = a✝.re
                                  -- 🎉 no goals
                                  -- 🎉 no goals
    mul_one := by intros; ext <;> simp [mul_one]
                  -- ⊢ a✝ * 1 = a✝
                          -- ⊢ (a✝ * 1).re = a✝.re
                                  -- 🎉 no goals
                                  -- 🎉 no goals
    mul_comm := by intros; ext <;> simp [mul_comm]; ring }
                   -- ⊢ a✝ * b✝ = b✝ * a✝
                           -- ⊢ (a✝ * b✝).re = (b✝ * a✝).re
                                   -- 🎉 no goals
                                   -- ⊢ a✝.re * b✝.im + b✝.re * a✝.im = b✝.re * a✝.im + a✝.re * b✝.im
                                                    -- 🎉 no goals

/-- This shortcut instance ensures we do not find `Ring` via the noncomputable `Complex.field`
instance. -/
instance : Ring ℂ := by infer_instance
                        -- 🎉 no goals

/-- This shortcut instance ensures we do not find `CommSemiring` via the noncomputable
`Complex.field` instance. -/
instance : CommSemiring ℂ :=
  inferInstance

-- porting note: added due to changes in typeclass search order
/-- This shortcut instance ensures we do not find `Semiring` via the noncomputable
`Complex.field` instance. -/
instance : Semiring ℂ :=
  inferInstance

/-- The "real part" map, considered as an additive group homomorphism. -/
def reAddGroupHom : ℂ →+ ℝ where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re
#align complex.re_add_group_hom Complex.reAddGroupHom

@[simp]
theorem coe_reAddGroupHom : (reAddGroupHom : ℂ → ℝ) = re :=
  rfl
#align complex.coe_re_add_group_hom Complex.coe_reAddGroupHom

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
def imAddGroupHom : ℂ →+ ℝ where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im
#align complex.im_add_group_hom Complex.imAddGroupHom

@[simp]
theorem coe_imAddGroupHom : (imAddGroupHom : ℂ → ℝ) = im :=
  rfl
#align complex.coe_im_add_group_hom Complex.coe_imAddGroupHom

section
set_option linter.deprecated false
@[simp]
theorem I_pow_bit0 (n : ℕ) : I ^ bit0 n = (-1) ^ n := by rw [pow_bit0', Complex.I_mul_I]
                                                         -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_pow_bit0 Complex.I_pow_bit0

@[simp]
theorem I_pow_bit1 (n : ℕ) : I ^ bit1 n = (-1) ^ n * I := by rw [pow_bit1', Complex.I_mul_I]
                                                             -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_pow_bit1 Complex.I_pow_bit1

--Porting note: new theorem
@[simp, norm_cast]
theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℝ) : ℂ) = OfNat.ofNat n :=
  rfl

@[simp]
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℂ).re = OfNat.ofNat n :=
  rfl

@[simp]
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℂ).im = 0 :=
  rfl

end
/-! ### Complex conjugation -/


/-- This defines the complex conjugate as the `star` operation of the `StarRing ℂ`. It
is recommended to use the ring endomorphism version `starRingEnd`, available under the
notation `conj` in the locale `ComplexConjugate`. -/
instance : StarRing ℂ where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
                          -- 🎉 no goals
  star_mul a b := by ext <;> simp [add_comm] <;> ring
                     -- ⊢ (star (a * b)).re = (star b * star a).re
                             -- ⊢ a.re * b.re - a.im * b.im = b.re * a.re - b.im * a.im
                             -- ⊢ -(a.re * b.im) + -(a.im * b.re) = -(b.re * a.im) + -(b.im * a.re)
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals
  star_add a b := by ext <;> simp [add_comm]
                     -- ⊢ (star (a + b)).re = (star a + star b).re
                             -- 🎉 no goals
                             -- 🎉 no goals

@[simp]
theorem conj_re (z : ℂ) : (conj z).re = z.re :=
  rfl
#align complex.conj_re Complex.conj_re

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl
#align complex.conj_im Complex.conj_im

theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  ext_iff.2 <| by simp [star]
                  -- 🎉 no goals
#align complex.conj_of_real Complex.conj_ofReal

@[simp]
theorem conj_I : conj I = -I :=
  ext_iff.2 <| by simp
                  -- 🎉 no goals
  set_option linter.uppercaseLean3 false in
#align complex.conj_I Complex.conj_I


section
set_option linter.deprecated false
theorem conj_bit0 (z : ℂ) : conj (bit0 z) = bit0 (conj z) :=
  ext_iff.2 <| by simp [bit0]
                  -- 🎉 no goals
#align complex.conj_bit0 Complex.conj_bit0

theorem conj_bit1 (z : ℂ) : conj (bit1 z) = bit1 (conj z) :=
  ext_iff.2 <| by simp [bit0]
                  -- 🎉 no goals
#align complex.conj_bit1 Complex.conj_bit1
end
-- @[simp]
/- Porting note: `simp` attribute removed as the result could be proved
by `simp only [@map_neg, Complex.conj_i, @neg_neg]`
-/
theorem conj_neg_I : conj (-I) = I :=
  ext_iff.2 <| by simp
                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.conj_neg_I Complex.conj_neg_I

theorem conj_eq_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩
    -- 🎉 no goals
#align complex.conj_eq_iff_real Complex.conj_eq_iff_real

theorem conj_eq_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal'], fun h => ⟨_, h.symm⟩⟩
                             -- ⊢ ↑(↑r).re = ↑r
                                              -- 🎉 no goals
#align complex.conj_eq_iff_re Complex.conj_eq_iff_re

theorem conj_eq_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩
#align complex.conj_eq_iff_im Complex.conj_eq_iff_im

-- `simpNF` complains about this being provable by `IsROrC.star_def` even
-- though it's not imported by this file.
-- Porting note: linter `simpNF` not found
@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl
#align complex.star_def Complex.star_def

/-! ### Norm squared -/


/-- The norm squared function. -/
-- Porting note: `@[pp_nodot]` not found
-- @[pp_nodot]
def normSq : ℂ →*₀ ℝ where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by simp
                  -- 🎉 no goals
  map_one' := by simp
                 -- 🎉 no goals
  map_mul' z w := by
    dsimp
    -- ⊢ (z.re * w.re - z.im * w.im) * (z.re * w.re - z.im * w.im) + (z.re * w.im + z …
    ring
    -- 🎉 no goals
#align complex.norm_sq Complex.normSq

theorem normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl
#align complex.norm_sq_apply Complex.normSq_apply

@[simp]
theorem normSq_ofReal (r : ℝ) : normSq r = r * r := by
  simp [normSq, ofReal']
  -- 🎉 no goals
#align complex.norm_sq_of_real Complex.normSq_ofReal

@[simp]
theorem normSq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl
#align complex.norm_sq_mk Complex.normSq_mk

theorem normSq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.norm_sq_add_mul_I Complex.normSq_add_mul_I

theorem normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal']
  -- ⊢ (↑(↑normSq z)).re = (↑(starRingEnd ℂ) z * z).re
          -- 🎉 no goals
          -- 🎉 no goals
#align complex.norm_sq_eq_conj_mul_self Complex.normSq_eq_conj_mul_self

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_zero]` -/
theorem normSq_zero : normSq 0 = 0 :=
  normSq.map_zero
#align complex.norm_sq_zero Complex.normSq_zero

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_one]` -/
theorem normSq_one : normSq 1 = 1 :=
  normSq.map_one
#align complex.norm_sq_one Complex.normSq_one

@[simp]
theorem normSq_I : normSq I = 1 := by simp [normSq]
                                      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.norm_sq_I Complex.normSq_I

theorem normSq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
#align complex.norm_sq_nonneg Complex.normSq_nonneg

@[simp]
theorem range_normSq : range normSq = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨Real.sqrt x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩
                     -- 🎉 no goals
#align complex.range_norm_sq Complex.range_normSq

theorem normSq_eq_zero {z : ℂ} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩
#align complex.norm_sq_eq_zero Complex.normSq_eq_zero

@[simp]
theorem normSq_pos {z : ℂ} : 0 < normSq z ↔ z ≠ 0 :=
  (normSq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans normSq_eq_zero)
#align complex.norm_sq_pos Complex.normSq_pos

@[simp]
theorem normSq_neg (z : ℂ) : normSq (-z) = normSq z := by simp [normSq]
                                                          -- 🎉 no goals
#align complex.norm_sq_neg Complex.normSq_neg

@[simp]
theorem normSq_conj (z : ℂ) : normSq (conj z) = normSq z := by simp [normSq]
                                                               -- 🎉 no goals
#align complex.norm_sq_conj Complex.normSq_conj

theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w
#align complex.norm_sq_mul Complex.normSq_mul

theorem normSq_add (z w : ℂ) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  dsimp [normSq]; ring
  -- ⊢ (z.re + w.re) * (z.re + w.re) + (z.im + w.im) * (z.im + w.im) = z.re * z.re  …
                  -- 🎉 no goals
#align complex.norm_sq_add Complex.normSq_add

theorem re_sq_le_normSq (z : ℂ) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)
#align complex.re_sq_le_norm_sq Complex.re_sq_le_normSq

theorem im_sq_le_normSq (z : ℂ) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)
#align complex.im_sq_le_norm_sq Complex.im_sq_le_normSq

theorem mul_conj (z : ℂ) : z * conj z = normSq z :=
  ext_iff.2 <| by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal']
                  -- 🎉 no goals
#align complex.mul_conj Complex.mul_conj

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  ext_iff.2 <| by simp [two_mul, ofReal']
                  -- 🎉 no goals
#align complex.add_conj Complex.add_conj

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
def ofReal : ℝ →+* ℂ where
  toFun x := (x : ℂ)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add
#align complex.of_real Complex.ofReal

@[simp]
theorem ofReal_eq_coe (r : ℝ) : ofReal r = r :=
  rfl
#align complex.of_real_eq_coe Complex.ofReal_eq_coe

@[simp]
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]
                                -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_sq Complex.I_sq

@[simp]
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl
#align complex.sub_re Complex.sub_re

@[simp]
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl
#align complex.sub_im Complex.sub_im

@[simp, norm_cast]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  ext_iff.2 <| by simp [ofReal']
                  -- 🎉 no goals
#align complex.of_real_sub Complex.ofReal_sub

@[simp, norm_cast]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]
  -- ⊢ ↑(r ^ Nat.zero) = ↑r ^ Nat.zero
                  -- 🎉 no goals
                  -- 🎉 no goals
#align complex.of_real_pow Complex.ofReal_pow

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  ext_iff.2 <| by simp [two_mul, sub_eq_add_neg, ofReal']
                  -- 🎉 no goals
#align complex.sub_conj Complex.sub_conj

theorem normSq_sub (z w : ℂ) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg, normSq_add]
  -- ⊢ ↑normSq z + ↑normSq (-w) + 2 * (z * ↑(starRingEnd ℂ) (-w)).re = ↑normSq z +  …
  simp only [RingHom.map_neg, mul_neg, neg_re, normSq_neg]
  -- ⊢ ↑normSq z + ↑normSq w + -(2 * (z * ↑(starRingEnd ℂ) w).re) = ↑normSq z + ↑no …
  ring
  -- 🎉 no goals
#align complex.norm_sq_sub Complex.normSq_sub

/-! ### Inversion -/


noncomputable instance : Inv ℂ :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  rfl
#align complex.inv_def Complex.inv_def

@[simp]
theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal']
                                                        -- 🎉 no goals
#align complex.inv_re Complex.inv_re

@[simp]
theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal']
                                                         -- 🎉 no goals
#align complex.inv_im Complex.inv_im

@[simp, norm_cast]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ :=
  ext_iff.2 <| by simp [ofReal']
                  -- 🎉 no goals
#align complex.of_real_inv Complex.ofReal_inv

protected theorem inv_zero : (0⁻¹ : ℂ) = 0 := by
  rw [← ofReal_zero, ← ofReal_inv, inv_zero]
  -- 🎉 no goals
#align complex.inv_zero Complex.inv_zero

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← ofReal_mul, mul_inv_cancel (mt normSq_eq_zero.1 h),
    ofReal_one]
#align complex.mul_inv_cancel Complex.mul_inv_cancel

noncomputable instance : RatCast ℂ where
  ratCast := Rat.castRec

/-! ### Cast lemmas -/

@[simp, norm_cast]
theorem ofReal_nat_cast (n : ℕ) : ((n : ℝ) : ℂ) = n :=
  map_natCast ofReal n
#align complex.of_real_nat_cast Complex.ofReal_nat_cast

@[simp, norm_cast]
theorem nat_cast_re (n : ℕ) : (n : ℂ).re = n := by rw [← ofReal_nat_cast, ofReal_re]
                                                   -- 🎉 no goals
#align complex.nat_cast_re Complex.nat_cast_re

@[simp, norm_cast]
theorem nat_cast_im (n : ℕ) : (n : ℂ).im = 0 := by rw [← ofReal_nat_cast, ofReal_im]
                                                   -- 🎉 no goals
#align complex.nat_cast_im Complex.nat_cast_im

@[simp, norm_cast]
theorem ofReal_int_cast (n : ℤ) : ((n : ℝ) : ℂ) = n :=
  map_intCast ofReal n
#align complex.of_real_int_cast Complex.ofReal_int_cast

@[simp, norm_cast]
theorem int_cast_re (n : ℤ) : (n : ℂ).re = n := by rw [← ofReal_int_cast, ofReal_re]
                                                   -- 🎉 no goals
#align complex.int_cast_re Complex.int_cast_re

@[simp, norm_cast]
theorem int_cast_im (n : ℤ) : (n : ℂ).im = 0 := by rw [← ofReal_int_cast, ofReal_im]
                                                   -- 🎉 no goals
#align complex.int_cast_im Complex.int_cast_im

@[simp, norm_cast]
theorem rat_cast_im (q : ℚ) : (q : ℂ).im = 0 := by
  show (Rat.castRec q : ℂ).im = 0
  -- ⊢ (Rat.castRec q).im = 0
  cases q
  -- ⊢ (Rat.castRec (Rat.mk' num✝ den✝)).im = 0
  simp [Rat.castRec]
  -- 🎉 no goals
#align complex.rat_cast_im Complex.rat_cast_im

@[simp, norm_cast]
theorem rat_cast_re (q : ℚ) : (q : ℂ).re = (q : ℝ) := by
  show (Rat.castRec q : ℂ).re = _
  -- ⊢ (Rat.castRec q).re = ↑q
  cases q
  -- ⊢ (Rat.castRec (Rat.mk' num✝ den✝)).re = ↑(Rat.mk' num✝ den✝)
  simp [Rat.castRec, normSq, Rat.mk_eq_divInt, Rat.mkRat_eq_div, div_eq_mul_inv, *]
  -- 🎉 no goals
#align complex.rat_cast_re Complex.rat_cast_re

/-! ### Field instance and lemmas -/

noncomputable instance instField : Field ℂ :=
{ qsmul := fun n z => n • z
  qsmul_eq_mul' := fun n z => ext_iff.2 <| by simp [Rat.smul_def, smul_re, smul_im]
                                              -- 🎉 no goals
  inv := Inv.inv
  mul_inv_cancel := @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero }
#align complex.field Complex.instField

section
set_option linter.deprecated false
@[simp]
theorem I_zpow_bit0 (n : ℤ) : I ^ bit0 n = (-1) ^ n := by rw [zpow_bit0', I_mul_I]
                                                          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_zpow_bit0 Complex.I_zpow_bit0

@[simp]
theorem I_zpow_bit1 (n : ℤ) : I ^ bit1 n = (-1) ^ n * I := by rw [zpow_bit1', I_mul_I]
                                                              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.I_zpow_bit1 Complex.I_zpow_bit1

end

theorem div_re (z w : ℂ) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]
  -- 🎉 no goals
#align complex.div_re Complex.div_re

theorem div_im (z w : ℂ) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]
  -- 🎉 no goals
#align complex.div_im Complex.div_im

theorem conj_inv (x : ℂ) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _
#align complex.conj_inv Complex.conj_inv

@[simp, norm_cast]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s :=
  map_div₀ ofReal r s
#align complex.of_real_div Complex.ofReal_div

@[simp, norm_cast]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
  map_zpow₀ ofReal r n
#align complex.of_real_zpow Complex.ofReal_zpow

@[simp]
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  (div_eq_iff_mul_eq I_ne_zero).2 <| by simp [mul_assoc]
                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.div_I Complex.div_I

@[simp]
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div, div_I, one_mul]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.inv_I Complex.inv_I

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_inv₀]` -/
theorem normSq_inv (z : ℂ) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z
#align complex.norm_sq_inv Complex.normSq_inv

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_div₀]` -/
theorem normSq_div (z w : ℂ) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w
#align complex.norm_sq_div Complex.normSq_div

@[simp, norm_cast]
theorem ofReal_rat_cast (n : ℚ) : ((n : ℝ) : ℂ) = (n : ℂ) :=
  map_ratCast ofReal n
#align complex.of_real_rat_cast Complex.ofReal_rat_cast


/-! ### Characteristic zero -/


instance charZero : CharZero ℂ :=
  charZero_of_inj_zero fun n h => by
    rwa [← ofReal_nat_cast, ofReal_eq_zero, Nat.cast_eq_zero] at h
    -- 🎉 no goals
#align complex.char_zero_complex Complex.charZero

-- Test if the `ℚ` smul instance is correct.
example : (Complex.instSMulRealComplex : SMul ℚ ℂ) = (Algebra.toSMul : SMul ℚ ℂ) := rfl

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  have : (↑(↑2 : ℝ) : ℂ) = (2 : ℂ) := by rfl
  -- ⊢ ↑z.re = (z + ↑(starRingEnd ℂ) z) / 2
  simp only [add_conj, ofReal_mul, ofReal_one, ofReal_bit0, this,
    mul_div_cancel_left (z.re : ℂ) two_ne_zero]
#align complex.re_eq_add_conj Complex.re_eq_add_conj

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  have : (↑2 : ℝ ) * I = 2 * I := by rfl
  -- ⊢ ↑z.im = (z - ↑(starRingEnd ℂ) z) / (2 * I)
  simp only [sub_conj, ofReal_mul, ofReal_one, ofReal_bit0, mul_right_comm, this,
    mul_div_cancel_left _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I ≠ 0)]
#align complex.im_eq_sub_conj Complex.im_eq_sub_conj

/-! ### Absolute value -/


namespace AbsTheory

-- We develop enough theory to bundle `abs` into an `AbsoluteValue` before making things public;
-- this is so there's not two versions of it hanging around.
local notation "abs" z => Real.sqrt (normSq z)

private theorem mul_self_abs (z : ℂ) : ((abs z) * abs z) = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

private theorem abs_nonneg' (z : ℂ) : 0 ≤ abs z :=
  Real.sqrt_nonneg _

theorem abs_conj (z : ℂ) : (abs conj z) = abs z := by simp
                                                      -- 🎉 no goals
#align complex.abs_theory.abs_conj Complex.AbsTheory.abs_conj

private theorem abs_re_le_abs (z : ℂ) : |z.re| ≤ abs z := by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (abs_nonneg' _), abs_mul_abs_self, mul_self_abs]
  -- ⊢ z.re * z.re ≤ ↑normSq z
  apply re_sq_le_normSq
  -- 🎉 no goals

private theorem re_le_abs (z : ℂ) : z.re ≤ abs z :=
  (abs_le.1 (abs_re_le_abs _)).2

private theorem abs_mul (z w : ℂ) : (abs z * w) = (abs z) * abs w := by
  rw [normSq_mul, Real.sqrt_mul (normSq_nonneg _)]
  -- 🎉 no goals

private theorem abs_add (z w : ℂ) : (abs z + w) ≤ (abs z) + abs w :=
  (mul_self_le_mul_self_iff (abs_nonneg' (z + w))
      (add_nonneg (abs_nonneg' z) (abs_nonneg' w))).2 <| by
    rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs, add_right_comm, normSq_add,
      add_le_add_iff_left, mul_assoc, mul_le_mul_left (zero_lt_two' ℝ), ←
      Real.sqrt_mul <| normSq_nonneg z, ← normSq_conj w, ← map_mul]
    exact re_le_abs (z * conj w)
    -- 🎉 no goals

/-- The complex absolute value function, defined as the square root of the norm squared. -/
noncomputable def _root_.Complex.abs : AbsoluteValue ℂ ℝ where
  toFun x := abs x
  map_mul' := abs_mul
  nonneg' := abs_nonneg'
  eq_zero' _ := (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero
  add_le' := abs_add
#align complex.abs Complex.abs

end AbsTheory

theorem abs_def : (Complex.abs : ℂ → ℝ) = fun z => (normSq z).sqrt :=
  rfl
#align complex.abs_def Complex.abs_def

theorem abs_apply {z : ℂ} : Complex.abs z = (normSq z).sqrt :=
  rfl
#align complex.abs_apply Complex.abs_apply

@[simp, norm_cast]
theorem abs_ofReal (r : ℝ) : Complex.abs r = |r| := by
  simp [Complex.abs, normSq_ofReal, Real.sqrt_mul_self_eq_abs]
  -- 🎉 no goals
#align complex.abs_of_real Complex.abs_ofReal

nonrec theorem abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : Complex.abs r = r :=
  (Complex.abs_ofReal _).trans (abs_of_nonneg h)
#align complex.abs_of_nonneg Complex.abs_of_nonneg

theorem abs_of_nat (n : ℕ) : Complex.abs n = n :=
  calc
    Complex.abs n = Complex.abs (n : ℝ) := by rw [ofReal_nat_cast]
                                              -- 🎉 no goals
    _ = _ := Complex.abs_of_nonneg (Nat.cast_nonneg n)
#align complex.abs_of_nat Complex.abs_of_nat

theorem mul_self_abs (z : ℂ) : Complex.abs z * Complex.abs z = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)
#align complex.mul_self_abs Complex.mul_self_abs

theorem sq_abs (z : ℂ) : Complex.abs z ^ 2 = normSq z :=
  Real.sq_sqrt (normSq_nonneg _)
#align complex.sq_abs Complex.sq_abs

@[simp]
theorem sq_abs_sub_sq_re (z : ℂ) : Complex.abs z ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  rw [sq_abs, normSq_apply, ← sq, ← sq, add_sub_cancel']
  -- 🎉 no goals
#align complex.sq_abs_sub_sq_re Complex.sq_abs_sub_sq_re

@[simp]
theorem sq_abs_sub_sq_im (z : ℂ) : Complex.abs z ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_abs_sub_sq_re, sub_sub_cancel]
  -- 🎉 no goals
#align complex.sq_abs_sub_sq_im Complex.sq_abs_sub_sq_im

@[simp]
theorem abs_I : Complex.abs I = 1 := by simp [Complex.abs]
                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align complex.abs_I Complex.abs_I

@[simp]
theorem abs_two : Complex.abs 2 = 2 :=
  calc
    Complex.abs 2 = Complex.abs (2 : ℝ) := by rfl
                                              -- 🎉 no goals
    _ = (2 : ℝ) := Complex.abs_of_nonneg (by norm_num)
                                             -- 🎉 no goals
#align complex.abs_two Complex.abs_two

@[simp]
theorem range_abs : range Complex.abs = Ici 0 :=
  Subset.antisymm
    (by simp only [range_subset_iff, Ici, mem_setOf_eq, map_nonneg, forall_const])
        -- 🎉 no goals
    (fun x hx => ⟨x, Complex.abs_of_nonneg hx⟩)
#align complex.range_abs Complex.range_abs

@[simp]
theorem abs_conj (z : ℂ) : Complex.abs (conj z) = Complex.abs z :=
  AbsTheory.abs_conj z
#align complex.abs_conj Complex.abs_conj

@[simp]
theorem abs_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.abs (s.prod f) = s.prod fun I => Complex.abs (f I) :=
  map_prod Complex.abs _ _
#align complex.abs_prod Complex.abs_prod

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_pow]` -/
theorem abs_pow (z : ℂ) (n : ℕ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  map_pow Complex.abs z n
#align complex.abs_pow Complex.abs_pow

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_zpow₀]` -/
theorem abs_zpow (z : ℂ) (n : ℤ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  map_zpow₀ Complex.abs z n
#align complex.abs_zpow Complex.abs_zpow

theorem abs_re_le_abs (z : ℂ) : |z.re| ≤ Complex.abs z :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq]
    -- ⊢ z.re ^ 2 ≤ z.re ^ 2 + z.im * z.im
    exact le_add_of_nonneg_right (mul_self_nonneg _)
    -- 🎉 no goals
#align complex.abs_re_le_abs Complex.abs_re_le_abs

theorem abs_im_le_abs (z : ℂ) : |z.im| ≤ Complex.abs z :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq, ← sq]
    -- ⊢ z.im ^ 2 ≤ z.re ^ 2 + z.im ^ 2
    exact le_add_of_nonneg_left (sq_nonneg _)
    -- 🎉 no goals
#align complex.abs_im_le_abs Complex.abs_im_le_abs

theorem re_le_abs (z : ℂ) : z.re ≤ Complex.abs z :=
  (abs_le.1 (abs_re_le_abs _)).2
#align complex.re_le_abs Complex.re_le_abs

theorem im_le_abs (z : ℂ) : z.im ≤ Complex.abs z :=
  (abs_le.1 (abs_im_le_abs _)).2
#align complex.im_le_abs Complex.im_le_abs

@[simp]
theorem abs_re_lt_abs {z : ℂ} : |z.re| < Complex.abs z ↔ z.im ≠ 0 := by
  rw [Complex.abs, AbsoluteValue.coe_mk, MulHom.coe_mk, Real.lt_sqrt (abs_nonneg _), normSq_apply,
    _root_.sq_abs, ← sq, lt_add_iff_pos_right, mul_self_pos]
#align complex.abs_re_lt_abs Complex.abs_re_lt_abs

@[simp]
theorem abs_im_lt_abs {z : ℂ} : |z.im| < Complex.abs z ↔ z.re ≠ 0 := by
  simpa using @abs_re_lt_abs (z * I)
  -- 🎉 no goals
#align complex.abs_im_lt_abs Complex.abs_im_lt_abs

@[simp]
theorem abs_abs (z : ℂ) : |Complex.abs z| = Complex.abs z :=
  _root_.abs_of_nonneg (AbsoluteValue.nonneg _ z)
#align complex.abs_abs Complex.abs_abs

-- Porting note: probably should be golfed
theorem abs_le_abs_re_add_abs_im (z : ℂ) : Complex.abs z ≤ |z.re| + |z.im| := by
  simpa [re_add_im] using Complex.abs.add_le z.re (z.im * I)
  -- 🎉 no goals
#align complex.abs_le_abs_re_add_abs_im Complex.abs_le_abs_re_add_abs_im

-- Porting note: added so `two_pos` in the next proof works
-- TODO: move somewhere else
instance : NeZero (1 : ℝ) :=
 ⟨by apply one_ne_zero⟩
     -- 🎉 no goals

theorem abs_le_sqrt_two_mul_max (z : ℂ) : Complex.abs z ≤ Real.sqrt 2 * max |z.re| |z.im| := by
  cases' z with x y
  -- ⊢ ↑abs { re := x, im := y } ≤ Real.sqrt 2 * max |{ re := x, im := y }.re| |{ r …
  simp only [abs_apply, normSq_mk, ← sq]
  -- ⊢ Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt 2 * max |x| |y|
  by_cases hle : |x| ≤ |y|
  -- ⊢ Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt 2 * max |x| |y|
  · calc
      Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt (y ^ 2 + y ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle) _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_right hle, ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]
  · have hle' := le_of_not_le hle
    -- ⊢ Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt 2 * max |x| |y|
    rw [add_comm]
    -- ⊢ Real.sqrt (y ^ 2 + x ^ 2) ≤ Real.sqrt 2 * max |x| |y|
    calc
      Real.sqrt (y ^ 2 + x ^ 2) ≤ Real.sqrt (x ^ 2 + x ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle') _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_left hle', ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]
#align complex.abs_le_sqrt_two_mul_max Complex.abs_le_sqrt_two_mul_max

theorem abs_re_div_abs_le_one (z : ℂ) : |z.re / Complex.abs z| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
                        -- 🎉 no goals
  else by simp_rw [_root_.abs_div, abs_abs,
    div_le_iff (AbsoluteValue.pos Complex.abs hz), one_mul, abs_re_le_abs]
#align complex.abs_re_div_abs_le_one Complex.abs_re_div_abs_le_one

theorem abs_im_div_abs_le_one (z : ℂ) : |z.im / Complex.abs z| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
                        -- 🎉 no goals
  else by simp_rw [_root_.abs_div, abs_abs,
    div_le_iff (AbsoluteValue.pos Complex.abs hz), one_mul, abs_im_le_abs]
#align complex.abs_im_div_abs_le_one Complex.abs_im_div_abs_le_one

-- Porting note: removed `norm_cast` attribute because the RHS can't start with `↑`
@[simp]
theorem abs_cast_nat (n : ℕ) : Complex.abs (n : ℂ) = n := by
  rw [← ofReal_nat_cast, abs_of_nonneg (Nat.cast_nonneg n)]
  -- 🎉 no goals
#align complex.abs_cast_nat Complex.abs_cast_nat

@[simp, norm_cast]
theorem int_cast_abs (n : ℤ) : |↑n| = Complex.abs n := by
  rw [← ofReal_int_cast, abs_ofReal]
  -- 🎉 no goals
#align complex.int_cast_abs Complex.int_cast_abs

theorem normSq_eq_abs (x : ℂ) : normSq x = (Complex.abs x) ^ 2 := by
  simp [abs, sq, abs_def, Real.mul_self_sqrt (normSq_nonneg _)]
  -- 🎉 no goals
#align complex.norm_sq_eq_abs Complex.normSq_eq_abs

/-! ### Cauchy sequences -/

local notation "abs'" => Abs.abs

theorem isCauSeq_re (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).re := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_re_le_abs (f j - f i)) (H _ ij)
                       -- 🎉 no goals
#align complex.is_cau_seq_re Complex.isCauSeq_re

theorem isCauSeq_im (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).im := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_im_le_abs (f j - f i)) (H _ ij)
                       -- 🎉 no goals
#align complex.is_cau_seq_im Complex.isCauSeq_im

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_re f⟩
#align complex.cau_seq_re Complex.cauSeqRe

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_im f⟩
#align complex.cau_seq_im Complex.cauSeqIm

theorem isCauSeq_abs {f : ℕ → ℂ} (hf : IsCauSeq Complex.abs f) :
  IsCauSeq abs' (Complex.abs ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt
    (Complex.abs.abs_abv_sub_le_abv_sub _ _) (hi j hj)⟩
#align complex.is_cau_seq_abs Complex.isCauSeq_abs

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def limAux (f : CauSeq ℂ Complex.abs) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩
#align complex.lim_aux Complex.limAux

theorem equiv_limAux (f : CauSeq ℂ Complex.abs) :
  f ≈ CauSeq.const Complex.abs (limAux f) := fun ε ε0 =>
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun i H j ij => by
    cases' H _ ij with H₁ H₂
    -- ⊢ ↑abs (↑(f - CauSeq.const (↑abs) (limAux f)) j) < ε
    apply lt_of_le_of_lt (abs_le_abs_re_add_abs_im _)
    -- ⊢ abs' (↑(f - CauSeq.const (↑abs) (limAux f)) j).re + abs' (↑(f - CauSeq.const …
    dsimp [limAux] at *
    -- ⊢ abs' ((↑f j).re - CauSeq.lim (cauSeqRe f)) + abs' ((↑f j).im - CauSeq.lim (c …
    have := add_lt_add H₁ H₂
    -- ⊢ abs' ((↑f j).re - CauSeq.lim (cauSeqRe f)) + abs' ((↑f j).im - CauSeq.lim (c …
    rwa [add_halves] at this
    -- 🎉 no goals
#align complex.equiv_lim_aux Complex.equiv_limAux

instance instIsComplete : CauSeq.IsComplete ℂ Complex.abs :=
  ⟨fun f => ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq

theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ Complex.abs) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I :=
  lim_eq_of_equiv_const <|
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const Complex.abs (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ =>
          Complex.ext (by simp [limAux, cauSeqRe, ofReal']) (by simp [limAux, cauSeqIm, ofReal'])
                          -- 🎉 no goals
                                                                -- 🎉 no goals
#align complex.lim_eq_lim_im_add_lim_re Complex.lim_eq_lim_im_add_lim_re

theorem lim_re (f : CauSeq ℂ Complex.abs) : lim (cauSeqRe f) = (lim f).re := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal']
  -- ⊢ CauSeq.lim (cauSeqRe f) = (↑(CauSeq.lim (cauSeqRe f)) + ↑(CauSeq.lim (cauSeq …
                                 -- 🎉 no goals
#align complex.lim_re Complex.lim_re

theorem lim_im (f : CauSeq ℂ Complex.abs) : lim (cauSeqIm f) = (lim f).im := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal']
  -- ⊢ CauSeq.lim (cauSeqIm f) = (↑(CauSeq.lim (cauSeqRe f)) + ↑(CauSeq.lim (cauSeq …
                                 -- 🎉 no goals
#align complex.lim_im Complex.lim_im

theorem isCauSeq_conj (f : CauSeq ℂ Complex.abs) :
  IsCauSeq Complex.abs fun n => conj (f n) := fun ε ε0 =>
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    rw [← RingHom.map_sub, abs_conj]; exact hi j hj⟩
    -- ⊢ ↑abs (↑f j - ↑f i) < ε
                                      -- 🎉 no goals
#align complex.is_cau_seq_conj Complex.isCauSeq_conj

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cauSeqConj (f : CauSeq ℂ Complex.abs) : CauSeq ℂ Complex.abs :=
  ⟨_, isCauSeq_conj f⟩
#align complex.cau_seq_conj Complex.cauSeqConj

theorem lim_conj (f : CauSeq ℂ Complex.abs) : lim (cauSeqConj f) = conj (lim f) :=
  Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
                  -- 🎉 no goals
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)
        -- ⊢ CauSeq.lim { val := fun n => -(↑f n).im, property := (_ : (fun f => IsCauSeq …
                                                                        -- 🎉 no goals
#align complex.lim_conj Complex.lim_conj

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqAbs (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_abs f.2⟩
#align complex.cau_seq_abs Complex.cauSeqAbs

theorem lim_abs (f : CauSeq ℂ Complex.abs) : lim (cauSeqAbs f) = Complex.abs (lim f) :=
  lim_eq_of_equiv_const fun ε ε0 =>
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (Complex.abs.abs_abv_sub_le_abv_sub _ _) (hi j hj)⟩
#align complex.lim_abs Complex.lim_abs

variable {α : Type*} (s : Finset α)

@[simp, norm_cast]
theorem ofReal_prod (f : α → ℝ) : ((∏ i in s, f i : ℝ) : ℂ) = ∏ i in s, (f i : ℂ) :=
  map_prod ofReal _ _
#align complex.of_real_prod Complex.ofReal_prod

@[simp, norm_cast]
theorem ofReal_sum (f : α → ℝ) : ((∑ i in s, f i : ℝ) : ℂ) = ∑ i in s, (f i : ℂ) :=
  map_sum ofReal _ _
#align complex.of_real_sum Complex.ofReal_sum

@[simp]
theorem re_sum (f : α → ℂ) : (∑ i in s, f i).re = ∑ i in s, (f i).re :=
  reAddGroupHom.map_sum f s
#align complex.re_sum Complex.re_sum

@[simp]
theorem im_sum (f : α → ℂ) : (∑ i in s, f i).im = ∑ i in s, (f i).im :=
  imAddGroupHom.map_sum f s
#align complex.im_sum Complex.im_sum

end Complex
