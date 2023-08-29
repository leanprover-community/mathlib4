/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Ideal.LocalRing
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Bezout
import Mathlib.Tactic.FieldSimp

#align_import ring_theory.valuation.valuation_ring from "leanprover-community/mathlib"@"c163ec99dfc664628ca15d215fce0a5b9c265b68"

/-!
# Valuation Rings

A valuation ring is a domain such that for every pair of elements `a b`, either `a` divides
`b` or vice-versa.

Any valuation ring induces a natural valuation on its fraction field, as we show in this file.
Namely, given the following instances:
`[CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]`,
there is a natural valuation `Valuation A K` on `K` with values in `value_group A K` where
the image of `A` under `algebraMap A K` agrees with `(Valuation A K).integer`.

We also provide the equivalence of the following notions for a domain `R` in `ValuationRing.tFAE`.
1. `R` is a valuation ring.
2. For each `x : FractionRing K`, either `x` or `x⁻¹` is in `R`.
3. "divides" is a total relation on the elements of `R`.
4. "contains" is a total relation on the ideals of `R`.
5. `R` is a local bezout domain.

-/


universe u v w

/-- An integral domain is called a `ValuationRing` provided that for any pair
of elements `a b : A`, either `a` divides `b` or vice versa. -/
class ValuationRing (A : Type u) [CommRing A] [IsDomain A] : Prop where
  cond' : ∀ a b : A, ∃ c : A, a * c = b ∨ b * c = a
#align valuation_ring ValuationRing

-- Porting note: this lemma is needed since infer kinds are unsupported in Lean 4
lemma ValuationRing.cond {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A] (a b : A) :
  ∃ c : A, a * c = b ∨ b * c = a := @ValuationRing.cond' A _ _ _ _ _

namespace ValuationRing

section

variable (A : Type u) [CommRing A]

variable (K : Type v) [Field K] [Algebra A K]

/-- The value group of the valuation ring `A`. Note: this is actually a group with zero. -/
def ValueGroup : Type v := Quotient (MulAction.orbitRel Aˣ K)
#align valuation_ring.value_group ValuationRing.ValueGroup

instance : Inhabited (ValueGroup A K) := ⟨Quotient.mk'' 0⟩

instance : LE (ValueGroup A K) :=
  LE.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => ∃ c : A, c • b = a)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩; ext
        -- ⊢ (fun a b => ∃ c, c • b = a) ((fun m => m • a) c) ((fun m => m • b) d) = (fun …
                                          -- ⊢ (fun a b => ∃ c, c • b = a) ((fun m => m • a) c) ((fun m => m • b) d) ↔ (fun …
        constructor
        -- ⊢ (fun a b => ∃ c, c • b = a) ((fun m => m • a) c) ((fun m => m • b) d) → (fun …
        · rintro ⟨e, he⟩; use (c⁻¹ : Aˣ) * e * d
          -- ⊢ ∃ c, c • b = a
                          -- ⊢ (↑c⁻¹ * e * ↑d) • b = a
          apply_fun fun t => c⁻¹ • t at he
          -- ⊢ (↑c⁻¹ * e * ↑d) • b = a
          simpa [mul_smul] using he
          -- 🎉 no goals
        · rintro ⟨e, he⟩; dsimp
          -- ⊢ ∃ c_1, c_1 • (fun m => m • b) d = (fun m => m • a) c
                          -- ⊢ ∃ c_1, c_1 • d • b = c • a
          use (d⁻¹ : Aˣ) * c * e
          -- ⊢ (↑d⁻¹ * ↑c * e) • d • b = c • a
          erw [← he, ← mul_smul, ← mul_smul]
          -- ⊢ (↑d⁻¹ * ↑c * e * ↑d) • b = (↑c * e) • b
          congr 1
          -- ⊢ ↑d⁻¹ * ↑c * e * ↑d = ↑c * e
          rw [mul_comm]
          -- ⊢ ↑d * (↑d⁻¹ * ↑c * e) = ↑c * e
          simp only [← mul_assoc, ← Units.val_mul, mul_inv_self, one_mul])
          -- 🎉 no goals

instance : Zero (ValueGroup A K) := ⟨Quotient.mk'' 0⟩

instance : One (ValueGroup A K) := ⟨Quotient.mk'' 1⟩

instance : Mul (ValueGroup A K) :=
  Mul.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => Quotient.mk'' <| a * b)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        -- ⊢ (fun a b => Quotient.mk'' (a * b)) ((fun m => m • a) c) ((fun m => m • b) d) …
        apply Quotient.sound'
        -- ⊢ Setoid.r ((fun m => m • a) c * (fun m => m • b) d) (a * b)
        dsimp
        -- ⊢ Setoid.r (c • a * d • b) (a * b)
        use c * d
        -- ⊢ (fun m => m • (a * b)) (c * d) = c • a * d • b
        simp only [mul_smul, Algebra.smul_def, Units.smul_def, RingHom.map_mul, Units.val_mul]
        -- ⊢ ↑(algebraMap A K) ↑c * (↑(algebraMap A K) ↑d * (a * b)) = ↑(algebraMap A K)  …
        ring)
        -- 🎉 no goals

instance : Inv (ValueGroup A K) :=
  Inv.mk fun x =>
    Quotient.liftOn' x (fun a => Quotient.mk'' a⁻¹)
      (by
        rintro _ a ⟨b, rfl⟩
        -- ⊢ (fun a => Quotient.mk'' a⁻¹) ((fun m => m • a) b) = (fun a => Quotient.mk''  …
        apply Quotient.sound'
        -- ⊢ Setoid.r ((fun m => m • a) b)⁻¹ a⁻¹
        use b⁻¹
        -- ⊢ (fun m => m • a⁻¹) b⁻¹ = ((fun m => m • a) b)⁻¹
        dsimp
        -- ⊢ b⁻¹ • a⁻¹ = (b • a)⁻¹
        rw [Units.smul_def, Units.smul_def, Algebra.smul_def, Algebra.smul_def, mul_inv,
          map_units_inv])

variable [IsDomain A] [ValuationRing A] [IsFractionRing A K]

protected theorem le_total (a b : ValueGroup A K) : a ≤ b ∨ b ≤ a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  -- ⊢ Quot.mk Setoid.r a ≤ b ∨ b ≤ Quot.mk Setoid.r a
                     -- ⊢ Quot.mk Setoid.r a ≤ Quot.mk Setoid.r b ∨ Quot.mk Setoid.r b ≤ Quot.mk Setoi …
  obtain ⟨xa, ya, hya, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective a
  -- ⊢ Quot.mk Setoid.r (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) ≤ Quot.mk Set …
  obtain ⟨xb, yb, hyb, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective b
  -- ⊢ Quot.mk Setoid.r (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) ≤ Quot.mk Set …
  have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
  -- ⊢ Quot.mk Setoid.r (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) ≤ Quot.mk Set …
  have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
  -- ⊢ Quot.mk Setoid.r (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) ≤ Quot.mk Set …
  obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
  -- ⊢ Quot.mk Setoid.r (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) ≤ Quot.mk Set …
  · right
    -- ⊢ Quot.mk Setoid.r (↑(algebraMap A K) xb / ↑(algebraMap A K) yb) ≤ Quot.mk Set …
    use c
    -- ⊢ c • (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) = ↑(algebraMap A K) xb / ↑ …
    rw [Algebra.smul_def]
    -- ⊢ ↑(algebraMap A K) c * (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) = ↑(alge …
    field_simp
    -- ⊢ ↑(algebraMap A K) c * ↑(algebraMap A K) xa * ↑(algebraMap A K) yb = ↑(algebr …
    simp only [← RingHom.map_mul, ← h]; congr 1; ring
    -- ⊢ ↑(algebraMap A K) (c * xa * yb) = ↑(algebraMap A K) (xa * yb * c)
                                        -- ⊢ c * xa * yb = xa * yb * c
                                                 -- 🎉 no goals
  · left
    -- ⊢ Quot.mk Setoid.r (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) ≤ Quot.mk Set …
    use c
    -- ⊢ c • (↑(algebraMap A K) xb / ↑(algebraMap A K) yb) = ↑(algebraMap A K) xa / ↑ …
    rw [Algebra.smul_def]
    -- ⊢ ↑(algebraMap A K) c * (↑(algebraMap A K) xb / ↑(algebraMap A K) yb) = ↑(alge …
    field_simp
    -- ⊢ ↑(algebraMap A K) c * ↑(algebraMap A K) xb * ↑(algebraMap A K) ya = ↑(algebr …
    simp only [← RingHom.map_mul, ← h]; congr 1; ring
    -- ⊢ ↑(algebraMap A K) (c * xb * ya) = ↑(algebraMap A K) (xb * ya * c)
                                        -- ⊢ c * xb * ya = xb * ya * c
                                                 -- 🎉 no goals
#align valuation_ring.le_total ValuationRing.le_total

-- Porting note: it is much faster to split the instance `LinearOrderedCommGroupWithZero`
-- into two parts
noncomputable instance : LinearOrder (ValueGroup A K) where
  le_refl := by rintro ⟨⟩; use 1; rw [one_smul]
                -- ⊢ Quot.mk Setoid.r a✝ ≤ Quot.mk Setoid.r a✝
                           -- ⊢ 1 • a✝ = a✝
                                  -- 🎉 no goals
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e, rfl⟩ ⟨f, rfl⟩; use e * f; rw [mul_smul]
                 -- ⊢ Quot.mk Setoid.r (e • f • c) ≤ Quot.mk Setoid.r c
                                                       -- ⊢ (e * f) • c = e • f • c
                                                                  -- 🎉 no goals
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ ⟨e, rfl⟩ ⟨f, hf⟩
    -- ⊢ Quot.mk Setoid.r (e • b) = Quot.mk Setoid.r b
    by_cases hb : b = 0; · simp [hb]
    -- ⊢ Quot.mk Setoid.r (e • b) = Quot.mk Setoid.r b
                           -- 🎉 no goals
    have : IsUnit e := by
      apply isUnit_of_dvd_one
      use f
      rw [mul_comm]
      rw [← mul_smul, Algebra.smul_def] at hf
      nth_rw 2 [← one_mul b] at hf
      rw [← (algebraMap A K).map_one] at hf
      exact IsFractionRing.injective _ _ (mul_right_cancel₀ hb hf).symm
    apply Quotient.sound'
    -- ⊢ Setoid.r (e • b) b
    exact ⟨this.unit, rfl⟩
    -- 🎉 no goals
  le_total := ValuationRing.le_total _ _
  decidableLE := by classical infer_instance
                    -- 🎉 no goals

noncomputable instance linearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero (ValueGroup A K) where
  mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; apply Quotient.sound'; rw [mul_assoc]; apply Setoid.refl'
                  -- ⊢ Quot.mk Setoid.r a * Quot.mk Setoid.r b * Quot.mk Setoid.r c = Quot.mk Setoi …
                                      -- ⊢ Setoid.r (a * b * c) (a * (b * c))
                                                             -- ⊢ Setoid.r (a * (b * c)) (a * (b * c))
                                                                             -- 🎉 no goals
  one_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [one_mul]; apply Setoid.refl'
                -- ⊢ 1 * Quot.mk Setoid.r a = Quot.mk Setoid.r a
                            -- ⊢ Setoid.r (1 * a) a
                                                   -- ⊢ Setoid.r a a
                                                                 -- 🎉 no goals
  mul_one := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_one]; apply Setoid.refl'
                -- ⊢ Quot.mk Setoid.r a * 1 = Quot.mk Setoid.r a
                            -- ⊢ Setoid.r (a * 1) a
                                                   -- ⊢ Setoid.r a a
                                                                 -- 🎉 no goals
  mul_comm := by rintro ⟨a⟩ ⟨b⟩; apply Quotient.sound'; rw [mul_comm]; apply Setoid.refl'
                 -- ⊢ Quot.mk Setoid.r a * Quot.mk Setoid.r b = Quot.mk Setoid.r b * Quot.mk Setoi …
                                 -- ⊢ Setoid.r (a * b) (b * a)
                                                        -- ⊢ Setoid.r (b * a) (b * a)
                                                                       -- 🎉 no goals
  mul_le_mul_left := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c, rfl⟩ ⟨d⟩
    -- ⊢ Quot.mk Setoid.r d * Quot.mk Setoid.r (c • b) ≤ Quot.mk Setoid.r d * Quot.mk …
    use c; simp only [Algebra.smul_def]; ring
    -- ⊢ c • (d * b) = d * c • b
           -- ⊢ ↑(algebraMap A K) c * (d * b) = d * (↑(algebraMap A K) c * b)
                                         -- 🎉 no goals
  zero_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [zero_mul]; apply Setoid.refl'
                 -- ⊢ 0 * Quot.mk Setoid.r a = 0
                             -- ⊢ Setoid.r (0 * a) 0
                                                    -- ⊢ Setoid.r 0 0
                                                                   -- 🎉 no goals
  mul_zero := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_zero]; apply Setoid.refl'
                 -- ⊢ Quot.mk Setoid.r a * 0 = 0
                             -- ⊢ Setoid.r (a * 0) 0
                                                    -- ⊢ Setoid.r 0 0
                                                                   -- 🎉 no goals
  zero_le_one := ⟨0, by rw [zero_smul]⟩
                        -- 🎉 no goals
  exists_pair_ne := by
    use 0, 1
    -- ⊢ 0 ≠ 1
    intro c; obtain ⟨d, hd⟩ := Quotient.exact' c
    -- ⊢ False
             -- ⊢ False
    apply_fun fun t => d⁻¹ • t at hd
    -- ⊢ False
    simp only [inv_smul_smul, smul_zero, one_ne_zero] at hd
    -- 🎉 no goals
  inv_zero := by apply Quotient.sound'; rw [inv_zero]; apply Setoid.refl'
                 -- ⊢ Setoid.r 0⁻¹ 0
                                        -- ⊢ Setoid.r 0 0
                                                       -- 🎉 no goals
  mul_inv_cancel := by
    rintro ⟨a⟩ ha
    -- ⊢ Quot.mk Setoid.r a * (Quot.mk Setoid.r a)⁻¹ = 1
    apply Quotient.sound'
    -- ⊢ Setoid.r (a * a⁻¹) 1
    use 1
    -- ⊢ (fun m => m • 1) 1 = a * a⁻¹
    simp only [one_smul, ne_eq]
    -- ⊢ 1 = a * a⁻¹
    apply (mul_inv_cancel _).symm
    -- ⊢ a ≠ 0
    contrapose ha
    -- ⊢ ¬Quot.mk Setoid.r a ≠ 0
    simp only [Classical.not_not] at ha ⊢
    -- ⊢ Quot.mk Setoid.r a = 0
    rw [ha]
    -- ⊢ Quot.mk Setoid.r 0 = 0
    rfl
    -- 🎉 no goals

/-- Any valuation ring induces a valuation on its fraction field. -/
def valuation : Valuation K (ValueGroup A K) where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := Quotient.mk'', map_zero' := (_ : Q …
    obtain ⟨xa, ya, hya, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective a
    -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := Quotient.mk'', map_zero' := (_ : Q …
    obtain ⟨xb, yb, hyb, rfl⟩ : ∃ a b : A, _ := IsFractionRing.div_surjective b
    -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := Quotient.mk'', map_zero' := (_ : Q …
    have : (algebraMap A K) ya ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := Quotient.mk'', map_zero' := (_ : Q …
    have : (algebraMap A K) yb ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
    -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := Quotient.mk'', map_zero' := (_ : Q …
    obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
    -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := Quotient.mk'', map_zero' := (_ : Q …
    dsimp
    -- ⊢ Quotient.mk'' (↑(algebraMap A K) xa / ↑(algebraMap A K) ya + ↑(algebraMap A  …
    · apply le_trans _ (le_max_left _ _)
      -- ⊢ Quotient.mk'' (↑(algebraMap A K) xa / ↑(algebraMap A K) ya + ↑(algebraMap A  …
      use c + 1
      -- ⊢ (c + 1) • (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) = ↑(algebraMap A K)  …
      rw [Algebra.smul_def]
      -- ⊢ ↑(algebraMap A K) (c + 1) * (↑(algebraMap A K) xa / ↑(algebraMap A K) ya) =  …
      field_simp
      -- ⊢ (↑(algebraMap A K) c + 1) * ↑(algebraMap A K) xa * (↑(algebraMap A K) ya * ↑ …
      simp only [← RingHom.map_mul, ← RingHom.map_add, ← (algebraMap A K).map_one, ← h]
      -- ⊢ ↑(algebraMap A K) ((c + 1) * xa * (ya * yb)) = ↑(algebraMap A K) ((xa * yb + …
      congr 1; ring
      -- ⊢ (c + 1) * xa * (ya * yb) = (xa * yb + xa * yb * c) * ya
               -- 🎉 no goals
    · apply le_trans _ (le_max_right _ _)
      -- ⊢ ZeroHom.toFun (↑{ toZeroHom := { toFun := Quotient.mk'', map_zero' := (_ : Q …
      use c + 1
      -- ⊢ (c + 1) • (↑(algebraMap A K) xb / ↑(algebraMap A K) yb) = ↑(algebraMap A K)  …
      rw [Algebra.smul_def]
      -- ⊢ ↑(algebraMap A K) (c + 1) * (↑(algebraMap A K) xb / ↑(algebraMap A K) yb) =  …
      field_simp
      -- ⊢ (↑(algebraMap A K) c + 1) * ↑(algebraMap A K) xb * (↑(algebraMap A K) ya * ↑ …
      simp only [← RingHom.map_mul, ← RingHom.map_add, ← (algebraMap A K).map_one, ← h]
      -- ⊢ ↑(algebraMap A K) ((c + 1) * xb * (ya * yb)) = ↑(algebraMap A K) ((xb * ya * …
      congr 1; ring
      -- ⊢ (c + 1) * xb * (ya * yb) = (xb * ya * c + xb * ya) * yb
               -- 🎉 no goals
#align valuation_ring.valuation ValuationRing.valuation

theorem mem_integer_iff (x : K) : x ∈ (valuation A K).integer ↔ ∃ a : A, algebraMap A K a = x := by
  constructor
  -- ⊢ x ∈ Valuation.integer (valuation A K) → ∃ a, ↑(algebraMap A K) a = x
  · rintro ⟨c, rfl⟩
    -- ⊢ ∃ a, ↑(algebraMap A K) a = c • 1
    use c
    -- ⊢ ↑(algebraMap A K) c = c • 1
    rw [Algebra.smul_def, mul_one]
    -- 🎉 no goals
  · rintro ⟨c, rfl⟩
    -- ⊢ ↑(algebraMap A K) c ∈ Valuation.integer (valuation A K)
    use c
    -- ⊢ c • 1 = ↑(algebraMap A K) c
    rw [Algebra.smul_def, mul_one]
    -- 🎉 no goals
#align valuation_ring.mem_integer_iff ValuationRing.mem_integer_iff

/-- The valuation ring `A` is isomorphic to the ring of integers of its associated valuation. -/
noncomputable def equivInteger : A ≃+* (valuation A K).integer :=
  RingEquiv.ofBijective
    (show A →ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
                                  -- ⊢ ↑((fun a => { val := ↑(algebraMap A K) a, property := (_ : ↑(algebraMap A K) …
                                        -- 🎉 no goals
        map_zero' := by ext1; exact (algebraMap A K).map_zero
                        -- ⊢ ↑(MulHom.toFun { toFun := fun a => { val := ↑(algebraMap A K) a, property := …
                              -- 🎉 no goals
        map_add' := fun _ _ => by ext1; exact (algebraMap A K).map_add _ _ })
                                  -- ⊢ ↑(MulHom.toFun { toFun := fun a => { val := ↑(algebraMap A K) a, property := …
                                        -- 🎉 no goals
    (by
      constructor
      · intro x y h
        -- ⊢ x = y
        apply_fun (algebraMap (valuation A K).integer K) at h
        -- ⊢ x = y
        exact IsFractionRing.injective _ _ h
        -- 🎉 no goals
      · rintro ⟨-, ha⟩
        -- ⊢ ∃ a,
        rw [mem_integer_iff] at ha
        -- ⊢ ∃ a,
        obtain ⟨a, rfl⟩ := ha
        -- ⊢ ∃ a_1,
        exact ⟨a, rfl⟩)
        -- 🎉 no goals
#align valuation_ring.equiv_integer ValuationRing.equivInteger

@[simp]
theorem coe_equivInteger_apply (a : A) : (equivInteger A K a : K) = algebraMap A K a := rfl
#align valuation_ring.coe_equiv_integer_apply ValuationRing.coe_equivInteger_apply

theorem range_algebraMap_eq : (valuation A K).integer = (algebraMap A K).range := by
  ext; exact mem_integer_iff _ _ _
  -- ⊢ x✝ ∈ Valuation.integer (valuation A K) ↔ x✝ ∈ RingHom.range (algebraMap A K)
       -- 🎉 no goals
#align valuation_ring.range_algebra_map_eq ValuationRing.range_algebraMap_eq

end

section

variable (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]

instance (priority := 100) localRing : LocalRing A :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self
    (by
      intro a
      -- ⊢ IsUnit a ∨ IsUnit (1 - a)
      obtain ⟨c, h | h⟩ := ValuationRing.cond a (1 - a)
      -- ⊢ IsUnit a ∨ IsUnit (1 - a)
      · left
        -- ⊢ IsUnit a
        apply isUnit_of_mul_eq_one _ (c + 1)
        -- ⊢ a * (c + 1) = 1
        simp [mul_add, h]
        -- 🎉 no goals
      · right
        -- ⊢ IsUnit (1 - a)
        apply isUnit_of_mul_eq_one _ (c + 1)
        -- ⊢ (1 - a) * (c + 1) = 1
        simp [mul_add, h])
        -- 🎉 no goals

instance [DecidableRel ((· ≤ ·) : Ideal A → Ideal A → Prop)] : LinearOrder (Ideal A) :=
  { (inferInstance : CompleteLattice (Ideal A)) with
    le_total := by
      intro α β
      -- ⊢ α ≤ β ∨ β ≤ α
      by_cases h : α ≤ β; · exact Or.inl h
      -- ⊢ α ≤ β ∨ β ≤ α
                            -- 🎉 no goals
      erw [not_forall] at h
      -- ⊢ α ≤ β ∨ β ≤ α
      push_neg at h
      -- ⊢ α ≤ β ∨ β ≤ α
      obtain ⟨a, h₁, h₂⟩ := h
      -- ⊢ α ≤ β ∨ β ≤ α
      right
      -- ⊢ β ≤ α
      intro b hb
      -- ⊢ b ∈ α
      obtain ⟨c, h | h⟩ := ValuationRing.cond a b
      -- ⊢ b ∈ α
      · rw [← h]
        -- ⊢ a * c ∈ α
        exact Ideal.mul_mem_right _ _ h₁
        -- 🎉 no goals
      · exfalso; apply h₂; rw [← h]
        -- ⊢ False
                 -- ⊢ a ∈ β
                           -- ⊢ b * c ∈ β
        apply Ideal.mul_mem_right _ _ hb
        -- 🎉 no goals
    decidableLE := inferInstance }

end

section

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*}

variable [Field K] [Algebra R K] [IsFractionRing R K]

theorem iff_dvd_total : ValuationRing R ↔ IsTotal R (· ∣ ·) := by
  classical
  refine ⟨fun H => ⟨fun a b => ?_⟩, fun H => ⟨fun a b => ?_⟩⟩
  · obtain ⟨c, rfl | rfl⟩ := ValuationRing.cond a b <;> simp
  · obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := @IsTotal.total _ _ H a b <;> use c <;> simp
#align valuation_ring.iff_dvd_total ValuationRing.iff_dvd_total

theorem iff_ideal_total : ValuationRing R ↔ IsTotal (Ideal R) (· ≤ ·) := by
  classical
  refine' ⟨fun _ => ⟨le_total⟩, fun H => iff_dvd_total.mpr ⟨fun a b => _⟩⟩
  have := @IsTotal.total _ _ H (Ideal.span {a}) (Ideal.span {b})
  simp_rw [Ideal.span_singleton_le_span_singleton] at this
  exact this.symm
#align valuation_ring.iff_ideal_total ValuationRing.iff_ideal_total

variable (K)

theorem dvd_total [h : ValuationRing R] (x y : R) : x ∣ y ∨ y ∣ x :=
  @IsTotal.total _ _ (iff_dvd_total.mp h) x y
#align valuation_ring.dvd_total ValuationRing.dvd_total

theorem unique_irreducible [ValuationRing R] ⦃p q : R⦄ (hp : Irreducible p) (hq : Irreducible q) :
    Associated p q := by
  have := dvd_total p q
  -- ⊢ Associated p q
  rw [Irreducible.dvd_comm hp hq, or_self_iff] at this
  -- ⊢ Associated p q
  exact associated_of_dvd_dvd (Irreducible.dvd_symm hq hp this) this
  -- 🎉 no goals
#align valuation_ring.unique_irreducible ValuationRing.unique_irreducible

variable (R)

theorem iff_isInteger_or_isInteger :
    ValuationRing R ↔ ∀ x : K, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ := by
  constructor
  -- ⊢ ValuationRing R → ∀ (x : K), IsLocalization.IsInteger R x ∨ IsLocalization.I …
  · intro H x
    -- ⊢ IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹
    obtain ⟨x : R, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    -- ⊢ IsLocalization.IsInteger R (↑(algebraMap R K) x / ↑(algebraMap R K) y) ∨ IsL …
    have := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hy)
    -- ⊢ IsLocalization.IsInteger R (↑(algebraMap R K) x / ↑(algebraMap R K) y) ∨ IsL …
    obtain ⟨s, rfl | rfl⟩ := ValuationRing.cond x y
    -- ⊢ IsLocalization.IsInteger R (↑(algebraMap R K) x / ↑(algebraMap R K) (x * s)) …
    · exact Or.inr
        ⟨s, eq_inv_of_mul_eq_one_left <| by rwa [mul_div, div_eq_one_iff_eq, map_mul, mul_comm]⟩
    · exact Or.inl ⟨s, by rwa [eq_div_iff, map_mul, mul_comm]⟩
      -- 🎉 no goals
  · intro H
    -- ⊢ ValuationRing R
    constructor
    -- ⊢ ∀ (a b : R), ∃ c, a * c = b ∨ b * c = a
    intro a b
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
    by_cases ha : a = 0; · subst ha; exact ⟨0, Or.inr <| mul_zero b⟩
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
                           -- ⊢ ∃ c, 0 * c = b ∨ b * c = 0
                                     -- 🎉 no goals
    by_cases hb : b = 0; · subst hb; exact ⟨0, Or.inl <| mul_zero a⟩
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
                           -- ⊢ ∃ c, a * c = 0 ∨ 0 * c = a
                                     -- 🎉 no goals
    replace ha := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
    replace hb := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
    obtain ⟨c, e⟩ | ⟨c, e⟩ := H (algebraMap R K a / algebraMap R K b)
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
    · rw [eq_div_iff hb, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm] at e
      -- ⊢ ∃ c, a * c = b ∨ b * c = a
      exact ⟨c, Or.inr e⟩
      -- 🎉 no goals
    · rw [inv_div, eq_div_iff ha, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm c] at e
      -- ⊢ ∃ c, a * c = b ∨ b * c = a
      exact ⟨c, Or.inl e⟩
      -- 🎉 no goals
#align valuation_ring.iff_is_integer_or_is_integer ValuationRing.iff_isInteger_or_isInteger

variable {K}

theorem isInteger_or_isInteger [h : ValuationRing R] (x : K) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ :=
  (iff_isInteger_or_isInteger R K).mp h x
#align valuation_ring.is_integer_or_is_integer ValuationRing.isInteger_or_isInteger

variable {R}

-- This implies that valuation rings are integrally closed through typeclass search.
instance (priority := 100) [ValuationRing R] : IsBezout R := by
  classical
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  rw [Ideal.span_insert]
  cases' le_total (Ideal.span {x} : Ideal R) (Ideal.span {y}) with h h
  · erw [sup_eq_right.mpr h]; exact ⟨⟨_, rfl⟩⟩
  · erw [sup_eq_left.mpr h]; exact ⟨⟨_, rfl⟩⟩

theorem iff_local_bezout_domain : ValuationRing R ↔ LocalRing R ∧ IsBezout R := by
  classical
  refine ⟨fun H => ⟨inferInstance, inferInstance⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  refine iff_dvd_total.mpr ⟨fun a b => ?_⟩
  obtain ⟨g, e : _ = Ideal.span _⟩ := IsBezout.span_pair_isPrincipal a b
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show a ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show b ∈ Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨x, y, e'⟩ := Ideal.mem_span_pair.mp
      (show g ∈ Ideal.span {a * g, b * g} by rw [e]; exact Ideal.subset_span (by simp))
  cases' eq_or_ne g 0 with h h
  · simp [h]
  have : x * a + y * b = 1 := by
    apply mul_left_injective₀ h; convert e' using 1 <;> ring
  cases' LocalRing.isUnit_or_isUnit_of_add_one this with h' h'
  left
  swap
  right
  all_goals exact mul_dvd_mul_right (isUnit_iff_forall_dvd.mp (isUnit_of_mul_isUnit_right h') _) _
#align valuation_ring.iff_local_bezout_domain ValuationRing.iff_local_bezout_domain

protected theorem tFAE (R : Type u) [CommRing R] [IsDomain R] :
    List.TFAE
      [ValuationRing R,
        ∀ x : FractionRing R, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹,
        IsTotal R (· ∣ ·), IsTotal (Ideal R) (· ≤ ·), LocalRing R ∧ IsBezout R] := by
  tfae_have 1 ↔ 2; · exact iff_isInteger_or_isInteger R _
  -- ⊢ ValuationRing R ↔ ∀ (x : FractionRing R), IsLocalization.IsInteger R x ∨ IsL …
                     -- 🎉 no goals
  tfae_have 1 ↔ 3; · exact iff_dvd_total
  -- ⊢ ValuationRing R ↔ IsTotal R fun x x_1 => x ∣ x_1
                     -- 🎉 no goals
  tfae_have 1 ↔ 4; · exact iff_ideal_total
  -- ⊢ ValuationRing R ↔ IsTotal (Ideal R) fun x x_1 => x ≤ x_1
                     -- 🎉 no goals
  tfae_have 1 ↔ 5; · exact iff_local_bezout_domain
  -- ⊢ ValuationRing R ↔ LocalRing R ∧ IsBezout R
                     -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align valuation_ring.tfae ValuationRing.tFAE

end

theorem _root_.Function.Surjective.valuationRing {R S : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Surjective f) :
    ValuationRing S :=
  ⟨fun a b => by
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hf a, hf b
    -- ⊢ ∃ c, ↑f a * c = ↑f b ∨ ↑f b * c = ↑f a
    obtain ⟨c, rfl | rfl⟩ := ValuationRing.cond a b
    -- ⊢ ∃ c_1, ↑f a * c_1 = ↑f (a * c) ∨ ↑f (a * c) * c_1 = ↑f a
    exacts [⟨f c, Or.inl <| (map_mul _ _ _).symm⟩, ⟨f c, Or.inr <| (map_mul _ _ _).symm⟩]⟩
    -- 🎉 no goals
#align function.surjective.valuation_ring Function.Surjective.valuationRing

section

variable {𝒪 : Type u} {K : Type v} {Γ : Type w} [CommRing 𝒪] [IsDomain 𝒪] [Field K] [Algebra 𝒪 K]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (hh : v.Integers 𝒪)

/-- If `𝒪` satisfies `v.integers 𝒪` where `v` is a valuation on a field, then `𝒪`
is a valuation ring. -/
theorem of_integers : ValuationRing 𝒪 := by
  constructor
  -- ⊢ ∀ (a b : 𝒪), ∃ c, a * c = b ∨ b * c = a
  intro a b
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
  cases' le_total (v (algebraMap 𝒪 K a)) (v (algebraMap 𝒪 K b)) with h h
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
    use c; exact Or.inr hc.symm
    -- ⊢ a * c = b ∨ b * c = a
           -- 🎉 no goals
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    -- ⊢ ∃ c, a * c = b ∨ b * c = a
    use c; exact Or.inl hc.symm
    -- ⊢ a * c = b ∨ b * c = a
           -- 🎉 no goals
#align valuation_ring.of_integers ValuationRing.of_integers

end

section

variable (K : Type u) [Field K]

/-- A field is a valuation ring. -/
instance (priority := 100) of_field : ValuationRing K := by
  constructor
  -- ⊢ ∀ (a b : K), ∃ c, a * c = b ∨ b * c = a
  intro a b
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
  by_cases b = 0
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
  · use 0; left; simp [h]
    -- ⊢ a * 0 = b ∨ b * 0 = a
           -- ⊢ a * 0 = b
                 -- 🎉 no goals
  · use a * b⁻¹; right; field_simp; rw [mul_comm]
    -- ⊢ a * (a * b⁻¹) = b ∨ b * (a * b⁻¹) = a
                 -- ⊢ b * (a * b⁻¹) = a
                        -- ⊢ b * a = a * b
                                    -- 🎉 no goals
#align valuation_ring.of_field ValuationRing.of_field

end

section

variable (A : Type u) [CommRing A] [IsDomain A] [DiscreteValuationRing A]

/-- A DVR is a valuation ring. -/
instance (priority := 100) of_discreteValuationRing : ValuationRing A := by
  constructor
  -- ⊢ ∀ (a b : A), ∃ c, a * c = b ∨ b * c = a
  intro a b
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
  by_cases ha : a = 0; · use 0; right; simp [ha]
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
                         -- ⊢ a * 0 = b ∨ b * 0 = a
                                -- ⊢ b * 0 = a
                                       -- 🎉 no goals
  by_cases hb : b = 0; · use 0; left; simp [hb]
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
                         -- ⊢ a * 0 = b ∨ b * 0 = a
                                -- ⊢ a * 0 = b
                                      -- 🎉 no goals
  obtain ⟨ϖ, hϖ⟩ := DiscreteValuationRing.exists_irreducible A
  -- ⊢ ∃ c, a * c = b ∨ b * c = a
  obtain ⟨m, u, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  -- ⊢ ∃ c, ↑u * ϖ ^ m * c = b ∨ b * c = ↑u * ϖ ^ m
  obtain ⟨n, v, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  -- ⊢ ∃ c, ↑u * ϖ ^ m * c = ↑v * ϖ ^ n ∨ ↑v * ϖ ^ n * c = ↑u * ϖ ^ m
  cases' le_total m n with h h
  -- ⊢ ∃ c, ↑u * ϖ ^ m * c = ↑v * ϖ ^ n ∨ ↑v * ϖ ^ n * c = ↑u * ϖ ^ m
  · use (u⁻¹ * v : Aˣ) * ϖ ^ (n - m); left
    -- ⊢ ↑u * ϖ ^ m * (↑(u⁻¹ * v) * ϖ ^ (n - m)) = ↑v * ϖ ^ n ∨ ↑v * ϖ ^ n * (↑(u⁻¹ * …
                                      -- ⊢ ↑u * ϖ ^ m * (↑(u⁻¹ * v) * ϖ ^ (n - m)) = ↑v * ϖ ^ n
    simp_rw [mul_comm (u : A), Units.val_mul, ← mul_assoc, mul_assoc _ (u : A)]
    -- ⊢ ϖ ^ m * (↑u * ↑u⁻¹) * ↑v * ϖ ^ (n - m) = ↑v * ϖ ^ n
    simp only [Units.mul_inv, mul_one, mul_comm _ (v : A), mul_assoc, ← pow_add]
    -- ⊢ ↑v * ϖ ^ (m + (n - m)) = ↑v * ϖ ^ n
    congr 2
    -- ⊢ m + (n - m) = n
    exact Nat.add_sub_of_le h
    -- 🎉 no goals
  · use (v⁻¹ * u : Aˣ) * ϖ ^ (m - n); right
    -- ⊢ ↑u * ϖ ^ m * (↑(v⁻¹ * u) * ϖ ^ (m - n)) = ↑v * ϖ ^ n ∨ ↑v * ϖ ^ n * (↑(v⁻¹ * …
                                      -- ⊢ ↑v * ϖ ^ n * (↑(v⁻¹ * u) * ϖ ^ (m - n)) = ↑u * ϖ ^ m
    simp_rw [mul_comm (v : A), Units.val_mul, ← mul_assoc, mul_assoc _ (v : A)]
    -- ⊢ ϖ ^ n * (↑v * ↑v⁻¹) * ↑u * ϖ ^ (m - n) = ↑u * ϖ ^ m
    simp only [Units.mul_inv, mul_one, mul_comm _ (u : A), mul_assoc, ← pow_add]
    -- ⊢ ↑u * ϖ ^ (n + (m - n)) = ↑u * ϖ ^ m
    congr 2
    -- ⊢ n + (m - n) = m
    exact Nat.add_sub_of_le h
    -- 🎉 no goals
#align valuation_ring.of_discrete_valuation_ring ValuationRing.of_discreteValuationRing

end

end ValuationRing
