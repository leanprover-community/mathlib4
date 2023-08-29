/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic

#align_import number_theory.padics.padic_integers from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `ZMod p` is established in another file.

## Important definitions

* `PadicInt` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/


open Padic Metric LocalRing

noncomputable section

open Classical

/-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. -/
def PadicInt (p : ℕ) [Fact p.Prime] :=
  { x : ℚ_[p] // ‖x‖ ≤ 1 }
#align padic_int PadicInt

/-- The ring of `p`-adic integers. -/
notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt

/-! ### Ring structure and coercion to `ℚ_[p]` -/


variable {p : ℕ} [Fact p.Prime]

instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩

theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext
#align padic_int.ext PadicInt.ext

variable (p)

/-- The `p`-adic integers as a subring of `ℚ_[p]`. -/
def subring : Subring ℚ_[p] where
  carrier := { x : ℚ_[p] | ‖x‖ ≤ 1 }
  zero_mem' := by norm_num
                  -- 🎉 no goals
                 -- 🎉 no goals
  one_mem' := by norm_num
  add_mem' hx hy := (padicNormE.nonarchimedean _ _).trans <| max_le_iff.2 ⟨hx, hy⟩
  mul_mem' hx hy := (padicNormE.mul _ _).trans_le <| mul_le_one hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx
#align padic_int.subring PadicInt.subring

@[simp]
theorem mem_subring_iff {x : ℚ_[p]} : x ∈ subring p ↔ ‖x‖ ≤ 1 := Iff.rfl
#align padic_int.mem_subring_iff PadicInt.mem_subring_iff

variable {p}

/-- Addition on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Add ℤ_[p] := (by infer_instance : Add (subring p))
                            -- 🎉 no goals

/-- Multiplication on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Mul ℤ_[p] := (by infer_instance : Mul (subring p))
                            -- 🎉 no goals

/-- Negation on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Neg ℤ_[p] := (by infer_instance : Neg (subring p))
                            -- 🎉 no goals

/-- Subtraction on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Sub ℤ_[p] := (by infer_instance : Sub (subring p))
                            -- 🎉 no goals

/-- Zero on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : Zero ℤ_[p] := (by infer_instance : Zero (subring p))
                             -- 🎉 no goals

instance : Inhabited ℤ_[p] := ⟨0⟩

/-- One on `ℤ_[p]` is inherited from `ℚ_[p]`. -/
instance : One ℤ_[p] := ⟨⟨1, by norm_num⟩⟩
                                -- 🎉 no goals

@[simp]
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl
#align padic_int.mk_zero PadicInt.mk_zero

@[simp, norm_cast]
theorem coe_add (z1 z2 : ℤ_[p]) : ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2 := rfl
#align padic_int.coe_add PadicInt.coe_add

@[simp, norm_cast]
theorem coe_mul (z1 z2 : ℤ_[p]) : ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2 := rfl
#align padic_int.coe_mul PadicInt.coe_mul

@[simp, norm_cast]
theorem coe_neg (z1 : ℤ_[p]) : ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1 := rfl
#align padic_int.coe_neg PadicInt.coe_neg

@[simp, norm_cast]
theorem coe_sub (z1 z2 : ℤ_[p]) : ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2 := rfl
#align padic_int.coe_sub PadicInt.coe_sub

@[simp, norm_cast]
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl
#align padic_int.coe_one PadicInt.coe_one

@[simp, norm_cast]
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl
#align padic_int.coe_zero PadicInt.coe_zero

theorem coe_eq_zero (z : ℤ_[p]) : (z : ℚ_[p]) = 0 ↔ z = 0 := by rw [← coe_zero, Subtype.coe_inj]
                                                                -- 🎉 no goals
#align padic_int.coe_eq_zero PadicInt.coe_eq_zero

theorem coe_ne_zero (z : ℤ_[p]) : (z : ℚ_[p]) ≠ 0 ↔ z ≠ 0 := z.coe_eq_zero.not
#align padic_int.coe_ne_zero PadicInt.coe_ne_zero

instance : AddCommGroup ℤ_[p] := (by infer_instance : AddCommGroup (subring p))
                                     -- 🎉 no goals

instance instCommRing : CommRing ℤ_[p] := (by infer_instance : CommRing (subring p))
                                              -- 🎉 no goals

@[simp, norm_cast]
theorem coe_nat_cast (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n := rfl
#align padic_int.coe_nat_cast PadicInt.coe_nat_cast

@[simp, norm_cast]
theorem coe_int_cast (z : ℤ) : ((z : ℤ_[p]) : ℚ_[p]) = z := rfl
#align padic_int.coe_int_cast PadicInt.coe_int_cast

/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
def Coe.ringHom : ℤ_[p] →+* ℚ_[p] := (subring p).subtype
#align padic_int.coe.ring_hom PadicInt.Coe.ringHom

@[simp, norm_cast]
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x ^ n) : ℚ_[p]) = (↑x : ℚ_[p]) ^ n := rfl
#align padic_int.coe_pow PadicInt.coe_pow

-- @[simp] -- Porting note: not in simpNF
theorem mk_coe (k : ℤ_[p]) : (⟨k, k.2⟩ : ℤ_[p]) = k := Subtype.coe_eta _ _
#align padic_int.mk_coe PadicInt.mk_coe

/-- The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic integer.
Otherwise, the inverse is defined to be `0`. -/
def inv : ℤ_[p] → ℤ_[p]
  | ⟨k, _⟩ => if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0
                                           -- 🎉 no goals
#align padic_int.inv PadicInt.inv

instance : CharZero ℤ_[p] where
  cast_injective m n h := Nat.cast_injective (by rw [Subtype.ext_iff] at h; norm_cast at h)
                                                 -- ⊢ ↑m = ↑n
                                                                            -- 🎉 no goals

@[norm_cast] -- @[simp] -- Porting note: not in simpNF
theorem coe_int_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 := by
  suffices (z1 : ℚ_[p]) = z2 ↔ z1 = z2 from Iff.trans (by norm_cast) this
  -- ⊢ ↑z1 = ↑z2 ↔ z1 = z2
  norm_cast
  -- 🎉 no goals
#align padic_int.coe_int_eq PadicInt.coe_int_eq

/-- A sequence of integers that is Cauchy with respect to the `p`-adic norm converges to a `p`-adic
integer. -/
def ofIntSeq (seq : ℕ → ℤ) (h : IsCauSeq (padicNorm p) fun n => seq n) : ℤ_[p] :=
  ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) ≤ (1 : ℝ) by
      rw [PadicSeq.norm]
      -- ⊢ ↑(if hf : { val := fun n => ↑(seq n), property := h } ≈ 0 then 0 else padicN …
      split_ifs with hne <;> norm_cast
      -- ⊢ ↑0 ≤ 1
                             -- 🎉 no goals
                             -- ⊢ padicNorm p (↑{ val := fun n => ↑(seq n), property := h } (PadicSeq.stationa …
      apply padicNorm.of_int⟩
      -- 🎉 no goals
#align padic_int.of_int_seq PadicInt.ofIntSeq

end PadicInt

namespace PadicInt

/-! ### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/


variable (p : ℕ) [Fact p.Prime]

instance : MetricSpace ℤ_[p] := Subtype.metricSpace

instance completeSpace : CompleteSpace ℤ_[p] :=
  have : IsClosed { x : ℚ_[p] | ‖x‖ ≤ 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe
#align padic_int.complete_space PadicInt.completeSpace

instance : Norm ℤ_[p] := ⟨fun z => ‖(z : ℚ_[p])‖⟩

variable {p}

theorem norm_def {z : ℤ_[p]} : ‖z‖ = ‖(z : ℚ_[p])‖ := rfl
#align padic_int.norm_def PadicInt.norm_def

variable (p)

instance : NormedCommRing ℤ_[p] :=
  { PadicInt.instCommRing with
    dist_eq := fun ⟨_, _⟩ ⟨_, _⟩ => rfl
    norm_mul := by simp [norm_def]
                   -- 🎉 no goals
    norm := norm }

instance : NormOneClass ℤ_[p] :=
  ⟨norm_def.trans norm_one⟩

instance isAbsoluteValue : IsAbsoluteValue fun z : ℤ_[p] => ‖z‖ where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := by simp [norm_eq_zero]
                     -- 🎉 no goals
  abv_add' := fun ⟨_, _⟩ ⟨_, _⟩ => norm_add_le _ _
  abv_mul' _ _ := by simp only [norm_def, padicNormE.mul, PadicInt.coe_mul]
                     -- 🎉 no goals
#align padic_int.is_absolute_value PadicInt.isAbsoluteValue

variable {p}

instance : IsDomain ℤ_[p] := Function.Injective.isDomain (subring p).subtype Subtype.coe_injective

end PadicInt

namespace PadicInt

/-! ### Norm -/


variable {p : ℕ} [Fact p.Prime]

theorem norm_le_one (z : ℤ_[p]) : ‖z‖ ≤ 1 := z.2
#align padic_int.norm_le_one PadicInt.norm_le_one

@[simp]
theorem norm_mul (z1 z2 : ℤ_[p]) : ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp [norm_def]
                                                                 -- 🎉 no goals
#align padic_int.norm_mul PadicInt.norm_mul

@[simp]
theorem norm_pow (z : ℤ_[p]) : ∀ n : ℕ, ‖z ^ n‖ = ‖z‖ ^ n
  | 0 => by simp
            -- 🎉 no goals
  | k + 1 => by
    rw [pow_succ, pow_succ, norm_mul]
    -- ⊢ ‖z‖ * ‖z ^ k‖ = ‖z‖ * ‖z‖ ^ k
    congr
    -- ⊢ ‖z ^ k‖ = ‖z‖ ^ k
    apply norm_pow
    -- 🎉 no goals
#align padic_int.norm_pow PadicInt.norm_pow

theorem nonarchimedean (q r : ℤ_[p]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := padicNormE.nonarchimedean _ _
#align padic_int.nonarchimedean PadicInt.nonarchimedean

theorem norm_add_eq_max_of_ne {q r : ℤ_[p]} : ‖q‖ ≠ ‖r‖ → ‖q + r‖ = max ‖q‖ ‖r‖ :=
  padicNormE.add_eq_max_of_ne
#align padic_int.norm_add_eq_max_of_ne PadicInt.norm_add_eq_max_of_ne

theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_right) h
                     -- ⊢ max ‖z1‖ ‖z2‖ ≥ ‖z2‖
                                                     -- 🎉 no goals
#align padic_int.norm_eq_of_norm_add_lt_right PadicInt.norm_eq_of_norm_add_lt_right

theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_left) h
                     -- ⊢ max ‖z1‖ ‖z2‖ ≥ ‖z1‖
                                                     -- 🎉 no goals
#align padic_int.norm_eq_of_norm_add_lt_left PadicInt.norm_eq_of_norm_add_lt_left

@[simp]
theorem padic_norm_e_of_padicInt (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ = ‖z‖ := by simp [norm_def]
                                                                         -- 🎉 no goals
#align padic_int.padic_norm_e_of_padic_int PadicInt.padic_norm_e_of_padicInt

theorem norm_int_cast_eq_padic_norm (z : ℤ) : ‖(z : ℤ_[p])‖ = ‖(z : ℚ_[p])‖ := by simp [norm_def]
                                                                                  -- 🎉 no goals
#align padic_int.norm_int_cast_eq_padic_norm PadicInt.norm_int_cast_eq_padic_norm

@[simp]
theorem norm_eq_padic_norm {q : ℚ_[p]} (hq : ‖q‖ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ‖q‖ := rfl
#align padic_int.norm_eq_padic_norm PadicInt.norm_eq_padic_norm

@[simp]
theorem norm_p : ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹ := padicNormE.norm_p
#align padic_int.norm_p PadicInt.norm_p

-- @[simp] -- Porting note: not in simpNF
theorem norm_p_pow (n : ℕ) : ‖(p : ℤ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ) := padicNormE.norm_p_pow n
#align padic_int.norm_p_pow PadicInt.norm_p_pow

private def cauSeq_to_rat_cauSeq (f : CauSeq ℤ_[p] norm) : CauSeq ℚ_[p] fun a => ‖a‖ :=
  ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩
                                -- 🎉 no goals

variable (p)

instance complete : CauSeq.IsComplete ℤ_[p] norm :=
  ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeq_to_rat_cauSeq f)‖ ≤ 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using CauSeq.equiv_lim (cauSeq_to_rat_cauSeq f) ε⟩⟩
      -- 🎉 no goals
#align padic_int.complete PadicInt.complete

end PadicInt

namespace PadicInt

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℝ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  -- ⊢ ∃ k, ↑p ^ (-↑k) < ε
  use k
  -- ⊢ ↑p ^ (-↑k) < ε
  rw [← inv_lt_inv hε (_root_.zpow_pos_of_pos _ _)]
  -- ⊢ ε⁻¹ < (↑p ^ (-↑k))⁻¹
  · rw [zpow_neg, inv_inv, zpow_ofNat]
    -- ⊢ ε⁻¹ < ↑p ^ k
    apply lt_of_lt_of_le hk
    -- ⊢ ↑k ≤ ↑p ^ k
    norm_cast
    -- ⊢ k ≤ p ^ k
    apply le_of_lt
    -- ⊢ k < p ^ k
    convert Nat.lt_pow_self _ _ using 1
    -- ⊢ 1 < p
    exact hp.1.one_lt
    -- 🎉 no goals
  · exact_mod_cast hp.1.pos
    -- 🎉 no goals
#align padic_int.exists_pow_neg_lt PadicInt.exists_pow_neg_lt

theorem exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℚ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (by exact_mod_cast hε)
  -- ⊢ ∃ k, ↑p ^ (-↑k) < ε
  use k
  -- ⊢ ↑p ^ (-↑k) < ε
  rw [show (p : ℝ) = (p : ℚ) by simp] at hk
  -- ⊢ ↑p ^ (-↑k) < ε
  exact_mod_cast hk
  -- 🎉 no goals
#align padic_int.exists_pow_neg_lt_rat PadicInt.exists_pow_neg_lt_rat

variable {p}

theorem norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_int_cast_eq_padic_norm]
                                         -- 🎉 no goals
  padicNormE.norm_int_lt_one_iff_dvd k
#align padic_int.norm_int_lt_one_iff_dvd PadicInt.norm_int_lt_one_iff_dvd

theorem norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} :
    ‖(k : ℤ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ ↑(p ^ n) ∣ k by simpa [norm_int_cast_eq_padic_norm]
                                                                -- 🎉 no goals
  padicNormE.norm_int_le_pow_iff_dvd _ _
#align padic_int.norm_int_le_pow_iff_dvd PadicInt.norm_int_le_pow_iff_dvd

/-! ### Valuation on `ℤ_[p]` -/


/-- `PadicInt.valuation` lifts the `p`-adic valuation on `ℚ` to `ℤ_[p]`.  -/
def valuation (x : ℤ_[p]) :=
  Padic.valuation (x : ℚ_[p])
#align padic_int.valuation PadicInt.valuation

theorem norm_eq_pow_val {x : ℤ_[p]} (hx : x ≠ 0) : ‖x‖ = (p : ℝ) ^ (-x.valuation) := by
  refine @Padic.norm_eq_pow_val p hp x ?_
  -- ⊢ ↑x ≠ 0
  contrapose! hx
  -- ⊢ x = 0
  exact Subtype.val_injective hx
  -- 🎉 no goals
#align padic_int.norm_eq_pow_val PadicInt.norm_eq_pow_val

@[simp]
theorem valuation_zero : valuation (0 : ℤ_[p]) = 0 := Padic.valuation_zero
#align padic_int.valuation_zero PadicInt.valuation_zero

@[simp]
theorem valuation_one : valuation (1 : ℤ_[p]) = 0 := Padic.valuation_one
#align padic_int.valuation_one PadicInt.valuation_one

@[simp]
theorem valuation_p : valuation (p : ℤ_[p]) = 1 := by simp [valuation]
                                                      -- 🎉 no goals
#align padic_int.valuation_p PadicInt.valuation_p

theorem valuation_nonneg (x : ℤ_[p]) : 0 ≤ x.valuation := by
  by_cases hx : x = 0
  -- ⊢ 0 ≤ valuation x
  · simp [hx]
    -- 🎉 no goals
  have h : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt
  -- ⊢ 0 ≤ valuation x
  rw [← neg_nonpos, ← (zpow_strictMono h).le_iff_le]
  -- ⊢ (fun x x_1 => x ^ x_1) (↑p) (-valuation x) ≤ (fun x x_1 => x ^ x_1) (↑p) 0
  show (p : ℝ) ^ (-valuation x) ≤ (p : ℝ) ^ (0 : ℤ)
  -- ⊢ ↑p ^ (-valuation x) ≤ ↑p ^ 0
  rw [← norm_eq_pow_val hx]
  -- ⊢ ‖x‖ ≤ ↑p ^ 0
  simpa using x.property
  -- 🎉 no goals
#align padic_int.valuation_nonneg PadicInt.valuation_nonneg

@[simp]
theorem valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) :
    ((p : ℤ_[p]) ^ n * c).valuation = n + c.valuation := by
  have : ‖(p : ℤ_[p]) ^ n * c‖ = ‖(p : ℤ_[p]) ^ n‖ * ‖c‖ := norm_mul _ _
  -- ⊢ valuation (↑p ^ n * c) = ↑n + valuation c
  have aux : (p : ℤ_[p]) ^ n * c ≠ 0 := by
    contrapose! hc
    rw [mul_eq_zero] at hc
    cases' hc with hc hc
    · refine (hp.1.ne_zero ?_).elim
      exact_mod_cast pow_eq_zero hc
    · exact hc
  rwa [norm_eq_pow_val aux, norm_p_pow, norm_eq_pow_val hc, ← zpow_add₀, ← neg_add,
    zpow_inj, neg_inj] at this
  · exact_mod_cast hp.1.pos
    -- 🎉 no goals
  · exact_mod_cast hp.1.ne_one
    -- 🎉 no goals
  · exact_mod_cast hp.1.ne_zero
    -- 🎉 no goals
#align padic_int.valuation_p_pow_mul PadicInt.valuation_p_pow_mul

section Units

/-! ### Units of `ℤ_[p]` -/

-- Porting note: `reducible` cannot be local and making it global breaks a lot of things
-- attribute [local reducible] PadicInt

theorem mul_inv : ∀ {z : ℤ_[p]}, ‖z‖ = 1 → z * z.inv = 1
  | ⟨k, _⟩, h => by
    have hk : k ≠ 0 := fun h' => zero_ne_one' ℚ_[p] (by simp [h'] at h)
    -- ⊢ { val := k, property := property✝ } * inv { val := k, property := property✝  …
    unfold PadicInt.inv
    -- ⊢ ({ val := k, property := property✝ } *
    rw [norm_eq_padic_norm] at h
    -- ⊢ ({ val := k, property := property✝ } *
    dsimp only
    -- ⊢ ({ val := k, property := property✝ } * if h : ‖k‖ = 1 then { val := k⁻¹, pro …
    rw [dif_pos h]
    -- ⊢ { val := k, property := property✝ } * { val := k⁻¹, property := (_ : ‖k⁻¹‖ ≤ …
    apply Subtype.ext_iff_val.2
    -- ⊢ ↑({ val := k, property := property✝ } * { val := k⁻¹, property := (_ : ‖k⁻¹‖ …
    simp [mul_inv_cancel hk]
    -- 🎉 no goals
#align padic_int.mul_inv PadicInt.mul_inv

theorem inv_mul {z : ℤ_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1 := by rw [mul_comm, mul_inv hz]
                                                                 -- 🎉 no goals
#align padic_int.inv_mul PadicInt.inv_mul

theorem isUnit_iff {z : ℤ_[p]} : IsUnit z ↔ ‖z‖ = 1 :=
  ⟨fun h => by
    rcases isUnit_iff_dvd_one.1 h with ⟨w, eq⟩
    -- ⊢ ‖z‖ = 1
    refine' le_antisymm (norm_le_one _) _
    -- ⊢ 1 ≤ ‖z‖
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    -- ⊢ 1 ≤ ‖z‖
    rwa [mul_one, ← norm_mul, ← eq, norm_one] at this, fun h =>
    -- 🎉 no goals
    ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩
#align padic_int.is_unit_iff PadicInt.isUnit_iff

theorem norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1) : ‖z1 + z2‖ < 1 :=
  lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)
#align padic_int.norm_lt_one_add PadicInt.norm_lt_one_add

theorem norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ‖z2‖ < 1) : ‖z1 * z2‖ < 1 :=
  calc
    ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp
                                  -- 🎉 no goals
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2

#align padic_int.norm_lt_one_mul PadicInt.norm_lt_one_mul

-- @[simp] -- Porting note: not in simpNF
theorem mem_nonunits {z : ℤ_[p]} : z ∈ nonunits ℤ_[p] ↔ ‖z‖ < 1 := by
  rw [lt_iff_le_and_ne]; simp [norm_le_one z, nonunits, isUnit_iff]
  -- ⊢ z ∈ nonunits ℤ_[p] ↔ ‖z‖ ≤ 1 ∧ ‖z‖ ≠ 1
                         -- 🎉 no goals
#align padic_int.mem_nonunits PadicInt.mem_nonunits

/-- A `p`-adic number `u` with `‖u‖ = 1` is a unit of `ℤ_[p]`. -/
def mkUnits {u : ℚ_[p]} (h : ‖u‖ = 1) : ℤ_[p]ˣ :=
  let z : ℤ_[p] := ⟨u, le_of_eq h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩
#align padic_int.mk_units PadicInt.mkUnits

@[simp]
theorem mkUnits_eq {u : ℚ_[p]} (h : ‖u‖ = 1) : ((mkUnits h : ℤ_[p]) : ℚ_[p]) = u := rfl
#align padic_int.mk_units_eq PadicInt.mkUnits_eq

@[simp]
theorem norm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖ = 1 := isUnit_iff.mp <| by simp
                                                                           -- 🎉 no goals
#align padic_int.norm_units PadicInt.norm_units

/-- `unitCoeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unitCoeff_spec`. -/
def unitCoeff {x : ℤ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ :=
  let u : ℚ_[p] := x * (p : ℚ_[p]) ^ (-x.valuation)
  have hu : ‖u‖ = 1 := by
    simp [hx, Nat.zpow_ne_zero_of_pos (by exact_mod_cast hp.1.pos) x.valuation, norm_eq_pow_val,
      zpow_neg, inv_mul_cancel]
  mkUnits hu
#align padic_int.unit_coeff PadicInt.unitCoeff

@[simp]
theorem unitCoeff_coe {x : ℤ_[p]} (hx : x ≠ 0) :
    (unitCoeff hx : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-x.valuation) := rfl
#align padic_int.unit_coeff_coe PadicInt.unitCoeff_coe

theorem unitCoeff_spec {x : ℤ_[p]} (hx : x ≠ 0) :
    x = (unitCoeff hx : ℤ_[p]) * (p : ℤ_[p]) ^ Int.natAbs (valuation x) := by
  apply Subtype.coe_injective
  -- ⊢ (fun a => ↑a) x = (fun a => ↑a) (↑(unitCoeff hx) * ↑p ^ Int.natAbs (valuatio …
  push_cast
  -- ⊢ ↑x = ↑↑(unitCoeff hx) * ↑p ^ Int.natAbs (valuation x)
  have repr : (x : ℚ_[p]) = unitCoeff hx * (p : ℚ_[p]) ^ x.valuation := by
    rw [unitCoeff_coe, mul_assoc, ← zpow_add₀]
    · simp
    · exact_mod_cast hp.1.ne_zero
  convert repr using 2
  -- ⊢ ↑p ^ Int.natAbs (valuation x) = ↑p ^ valuation x
  rw [← zpow_ofNat, Int.natAbs_of_nonneg (valuation_nonneg x)]
  -- 🎉 no goals
#align padic_int.unit_coeff_spec PadicInt.unitCoeff_spec

end Units

section NormLeIff

/-! ### Various characterizations of open unit balls -/


theorem norm_le_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ ↑n ≤ x.valuation := by
  rw [norm_eq_pow_val hx]
  -- ⊢ ↑p ^ (-valuation x) ≤ ↑p ^ (-↑n) ↔ ↑n ≤ valuation x
  lift x.valuation to ℕ using x.valuation_nonneg with k
  -- ⊢ ↑p ^ (-↑k) ≤ ↑p ^ (-↑n) ↔ ↑n ≤ ↑k
  simp only [Int.ofNat_le, zpow_neg, zpow_ofNat]
  -- ⊢ (↑p ^ k)⁻¹ ≤ (↑p ^ n)⁻¹ ↔ n ≤ k
  have aux : ∀ m : ℕ, 0 < (p : ℝ) ^ m := by
    intro m
    refine pow_pos ?_ m
    exact_mod_cast hp.1.pos
  rw [inv_le_inv (aux _) (aux _)]
  -- ⊢ ↑p ^ n ≤ ↑p ^ k ↔ n ≤ k
  have : p ^ n ≤ p ^ k ↔ n ≤ k := (pow_strictMono_right hp.1.one_lt).le_iff_le
  -- ⊢ ↑p ^ n ≤ ↑p ^ k ↔ n ≤ k
  rw [← this]
  -- ⊢ ↑p ^ n ≤ ↑p ^ k ↔ p ^ n ≤ p ^ k
  norm_cast
  -- 🎉 no goals
#align padic_int.norm_le_pow_iff_le_valuation PadicInt.norm_le_pow_iff_le_valuation

theorem mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) ↔ ↑n ≤ x.valuation := by
  rw [Ideal.mem_span_singleton]
  -- ⊢ ↑p ^ n ∣ x ↔ ↑n ≤ valuation x
  constructor
  -- ⊢ ↑p ^ n ∣ x → ↑n ≤ valuation x
  · rintro ⟨c, rfl⟩
    -- ⊢ ↑n ≤ valuation (↑p ^ n * c)
    suffices c ≠ 0 by
      rw [valuation_p_pow_mul _ _ this, le_add_iff_nonneg_right]
      apply valuation_nonneg
    contrapose! hx
    -- ⊢ ↑p ^ n * c = 0
    rw [hx, mul_zero]
    -- 🎉 no goals
  · nth_rewrite 2 [unitCoeff_spec hx]
    -- ⊢ ↑n ≤ valuation x → ↑p ^ n ∣ ↑(unitCoeff hx) * ↑p ^ Int.natAbs (valuation x)
    lift x.valuation to ℕ using x.valuation_nonneg with k
    -- ⊢ ↑n ≤ ↑k → ↑p ^ n ∣ ↑(unitCoeff hx) * ↑p ^ Int.natAbs ↑k
    simp only [Int.natAbs_ofNat, Units.isUnit, IsUnit.dvd_mul_left, Int.ofNat_le]
    -- ⊢ n ≤ k → ↑p ^ n ∣ ↑p ^ k
    intro H
    -- ⊢ ↑p ^ n ∣ ↑p ^ k
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le H
    -- ⊢ ↑p ^ n ∣ ↑p ^ (n + k)
    simp only [pow_add, dvd_mul_right]
    -- 🎉 no goals
#align padic_int.mem_span_pow_iff_le_valuation PadicInt.mem_span_pow_iff_le_valuation

theorem norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
  by_cases hx : x = 0
  -- ⊢ ‖x‖ ≤ ↑p ^ (-↑n) ↔ x ∈ Ideal.span {↑p ^ n}
  · subst hx
    -- ⊢ ‖0‖ ≤ ↑p ^ (-↑n) ↔ 0 ∈ Ideal.span {↑p ^ n}
    simp only [norm_zero, zpow_neg, zpow_ofNat, inv_nonneg, iff_true_iff, Submodule.zero_mem]
    -- ⊢ 0 ≤ ↑p ^ n
    exact_mod_cast Nat.zero_le _
    -- 🎉 no goals
  rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx]
  -- 🎉 no goals
#align padic_int.norm_le_pow_iff_mem_span_pow PadicInt.norm_le_pow_iff_mem_span_pow

theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) :
    ‖x‖ ≤ (p : ℝ) ^ n ↔ ‖x‖ < (p : ℝ) ^ (n + 1) := by
  rw [norm_def]; exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _
  -- ⊢ ‖↑x‖ ≤ ↑p ^ n ↔ ‖↑x‖ < ↑p ^ (n + 1)
                 -- 🎉 no goals
#align padic_int.norm_le_pow_iff_norm_lt_pow_add_one PadicInt.norm_le_pow_iff_norm_lt_pow_add_one

theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) :
    ‖x‖ < (p : ℝ) ^ n ↔ ‖x‖ ≤ (p : ℝ) ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]
  -- 🎉 no goals
#align padic_int.norm_lt_pow_iff_norm_le_pow_sub_one PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one

theorem norm_lt_one_iff_dvd (x : ℤ_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x := by
  have := norm_le_pow_iff_mem_span_pow x 1
  -- ⊢ ‖x‖ < 1 ↔ ↑p ∣ x
  rw [Ideal.mem_span_singleton, pow_one] at this
  -- ⊢ ‖x‖ < 1 ↔ ↑p ∣ x
  rw [← this, norm_le_pow_iff_norm_lt_pow_add_one]
  -- ⊢ ‖x‖ < 1 ↔ ‖x‖ < ↑p ^ (-↑1 + 1)
  simp only [zpow_zero, Int.ofNat_zero, Int.ofNat_succ, add_left_neg, zero_add]
  -- 🎉 no goals
#align padic_int.norm_lt_one_iff_dvd PadicInt.norm_lt_one_iff_dvd

@[simp]
theorem pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p : ℤ_[p]) ^ n ∣ a ↔ (p ^ n : ℤ) ∣ a := by
  rw [← Nat.cast_pow, ← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton, Nat.cast_pow]
#align padic_int.pow_p_dvd_int_iff PadicInt.pow_p_dvd_int_iff

end NormLeIff

section Dvr

/-! ### Discrete valuation ring -/


instance : LocalRing ℤ_[p] :=
  LocalRing.of_nonunits_add <| by simp only [mem_nonunits]; exact fun x y => norm_lt_one_add
                                  -- ⊢ ∀ (a b : ℤ_[p]), ‖a‖ < 1 → ‖b‖ < 1 → ‖a + b‖ < 1
                                                            -- 🎉 no goals

theorem p_nonnunit : (p : ℤ_[p]) ∈ nonunits ℤ_[p] := by
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one <| by exact_mod_cast hp.1.one_lt
  -- ⊢ ↑p ∈ nonunits ℤ_[p]
  rwa [← norm_p, ← mem_nonunits] at this
  -- 🎉 no goals
#align padic_int.p_nonnunit PadicInt.p_nonnunit

theorem maximalIdeal_eq_span_p : maximalIdeal ℤ_[p] = Ideal.span {(p : ℤ_[p])} := by
  apply le_antisymm
  -- ⊢ maximalIdeal ℤ_[p] ≤ Ideal.span {↑p}
  · intro x hx
    -- ⊢ x ∈ Ideal.span {↑p}
    simp only [LocalRing.mem_maximalIdeal, mem_nonunits] at hx
    -- ⊢ x ∈ Ideal.span {↑p}
    rwa [Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
    -- 🎉 no goals
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    -- ⊢ ↑p ∈ ↑(maximalIdeal ℤ_[p])
    exact p_nonnunit
    -- 🎉 no goals
#align padic_int.maximal_ideal_eq_span_p PadicInt.maximalIdeal_eq_span_p

theorem prime_p : Prime (p : ℤ_[p]) := by
  rw [← Ideal.span_singleton_prime, ← maximalIdeal_eq_span_p]
  -- ⊢ Ideal.IsPrime (maximalIdeal ℤ_[p])
  · infer_instance
    -- 🎉 no goals
  · exact_mod_cast hp.1.ne_zero
    -- 🎉 no goals
#align padic_int.prime_p PadicInt.prime_p

theorem irreducible_p : Irreducible (p : ℤ_[p]) := Prime.irreducible prime_p
#align padic_int.irreducible_p PadicInt.irreducible_p

instance : DiscreteValuationRing ℤ_[p] :=
  DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_p, fun {x hx} =>
      ⟨x.valuation.natAbs, unitCoeff hx, by rw [mul_comm, ← unitCoeff_spec hx]⟩⟩
                                            -- 🎉 no goals

theorem ideal_eq_span_pow_p {s : Ideal ℤ_[p]} (hs : s ≠ ⊥) :
    ∃ n : ℕ, s = Ideal.span {(p : ℤ_[p]) ^ n} :=
  DiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p
#align padic_int.ideal_eq_span_pow_p PadicInt.ideal_eq_span_pow_p

open CauSeq

instance : IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] where
  prec' x hx := by
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢
    let x' : CauSeq ℤ_[p] norm := ⟨x, ?_⟩; swap
    -- ⊢ ∃ L, ∀ (n : ℕ), ‖x n - L‖ ≤ ↑p ^ (-↑n)
                                           -- ⊢ IsCauSeq norm x
    · intro ε hε
      -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → ‖x j - x i‖ < ε
      obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      -- ⊢ ∃ i, ∀ (j : ℕ), j ≥ i → ‖x j - x i‖ < ε
      refine ⟨m, fun n hn => lt_of_le_of_lt ?_ hm⟩
      -- ⊢ ‖x n - x m‖ ≤ ↑p ^ (-↑m)
      rw [← neg_sub, norm_neg]
      -- ⊢ ‖x m - x n‖ ≤ ↑p ^ (-↑m)
      exact hx hn
      -- 🎉 no goals
    · refine ⟨x'.lim, fun n => ?_⟩
      -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
      have : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := by
        apply zpow_pos_of_pos
        exact_mod_cast hp.1.pos
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
      by_cases hin : i ≤ n
      -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
      · exact (hi i le_rfl n hin).le
        -- 🎉 no goals
      · push_neg at hin
        -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
        specialize hi i le_rfl i le_rfl
        -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
        specialize hx hin.le
        -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
        have := nonarchimedean (x n - x i : ℤ_[p]) (x i - x'.lim)
        -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
        rw [sub_add_sub_cancel] at this
        -- ⊢ ‖x n - CauSeq.lim x'‖ ≤ ↑p ^ (-↑n)
        refine' this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)
        -- 🎉 no goals

end Dvr

section FractionRing

instance algebra : Algebra ℤ_[p] ℚ_[p] :=
  Algebra.ofSubring (subring p)
#align padic_int.algebra PadicInt.algebra

@[simp]
theorem algebraMap_apply (x : ℤ_[p]) : algebraMap ℤ_[p] ℚ_[p] x = x :=
  rfl
#align padic_int.algebra_map_apply PadicInt.algebraMap_apply

instance isFractionRing : IsFractionRing ℤ_[p] ℚ_[p] where
  map_units' := fun ⟨x, hx⟩ => by
    rwa [algebraMap_apply, isUnit_iff_ne_zero, PadicInt.coe_ne_zero, ←
      mem_nonZeroDivisors_iff_ne_zero]
  surj' x := by
    by_cases hx : ‖x‖ ≤ 1
    -- ⊢ ∃ x_1, x * ↑(algebraMap ℤ_[p] ℚ_[p]) ↑x_1.snd = ↑(algebraMap ℤ_[p] ℚ_[p]) x_ …
    · use (⟨x, hx⟩, 1)
      -- ⊢ x * ↑(algebraMap ℤ_[p] ℚ_[p]) ↑({ val := x, property := hx }, 1).snd = ↑(alg …
      rw [Submonoid.coe_one, map_one, mul_one, PadicInt.algebraMap_apply, Subtype.coe_mk]
      -- 🎉 no goals
    · set n := Int.toNat (-x.valuation) with hn
      -- ⊢ ∃ x_1, x * ↑(algebraMap ℤ_[p] ℚ_[p]) ↑x_1.snd = ↑(algebraMap ℤ_[p] ℚ_[p]) x_ …
      have hn_coe : (n : ℤ) = -x.valuation := by
        rw [hn, Int.toNat_of_nonneg]
        rw [Right.nonneg_neg_iff]
        rw [Padic.norm_le_one_iff_val_nonneg, not_le] at hx
        exact hx.le
      set a := x * (p : ℚ_[p]) ^ n with ha
      -- ⊢ ∃ x_1, x * ↑(algebraMap ℤ_[p] ℚ_[p]) ↑x_1.snd = ↑(algebraMap ℤ_[p] ℚ_[p]) x_ …
      have ha_norm : ‖a‖ = 1 := by
        have hx : x ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hx
          exact hx zero_le_one
        rw [ha, padicNormE.mul, padicNormE.norm_p_pow, Padic.norm_eq_pow_val hx, ← zpow_add',
          hn_coe, neg_neg, add_left_neg, zpow_zero]
        exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne p))
      use
        (⟨a, le_of_eq ha_norm⟩,
          ⟨(p ^ n : ℤ_[p]), mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne _)⟩)
      simp only [map_pow, map_natCast, algebraMap_apply, PadicInt.coe_pow, PadicInt.coe_nat_cast,
        Subtype.coe_mk, Nat.cast_pow]
  eq_iff_exists' := by
    simp_rw [algebraMap_apply, Subtype.coe_inj]
    -- ⊢ ∀ {x y : ℤ_[p]}, x = y ↔ ∃ c, ↑c * x = ↑c * y
    refine ⟨fun h => ⟨1, by rw [h]⟩, ?_⟩
    -- ⊢ (∃ c, ↑c * x✝ = ↑c * y✝) → x✝ = y✝
    rintro ⟨⟨c, hc⟩, h⟩
    -- ⊢ x✝ = y✝
    exact (mul_eq_mul_left_iff.mp h).resolve_right (mem_nonZeroDivisors_iff_ne_zero.mp hc)
    -- 🎉 no goals
#align padic_int.is_fraction_ring PadicInt.isFractionRing

end FractionRing

end PadicInt
