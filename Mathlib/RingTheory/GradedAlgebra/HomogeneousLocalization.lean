/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.GradedAlgebra.Basic

#align_import ring_theory.graded_algebra.homogeneous_localization from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Homogeneous Localization

## Notation
- `ι` is a commutative monoid;
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ι → Submodule R A` is the grading of `A`;
- `x : Submonoid A` is a submonoid

## Main definitions and results

This file constructs the subring of `Aₓ` where the numerator and denominator have the same grading,
i.e. `{a/b ∈ Aₓ | ∃ (i : ι), a ∈ 𝒜ᵢ ∧ b ∈ 𝒜ᵢ}`.

* `HomogeneousLocalization.NumDenSameDeg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `NumDenSameDeg 𝒜 x` cannot have a ring structure for many reasons, for example if `c`
is a `NumDenSameDeg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `NumDenSameDeg 𝒜 x` by the kernel of `c ↦ c.num / c.den`.

* `HomogeneousLocalization.NumDenSameDeg.embedding`: for `x : Submonoid A` and any
  `c : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.den` of `Aₓ`.
* `HomogeneousLocalization`: `NumDenSameDeg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
* `HomogeneousLocalization.val`: if `f : HomogeneousLocalization 𝒜 x`, then `f.val` is an element
  of `Aₓ`. In another word, one can view `HomogeneousLocalization 𝒜 x` as a subring of `Aₓ`
  through `HomogeneousLocalization.val`.
* `HomogeneousLocalization.num`: if `f : HomogeneousLocalization 𝒜 x`, then `f.num : A` is the
  numerator of `f`.
* `HomogeneousLocalization.den`: if `f : HomogeneousLocalization 𝒜 x`, then `f.den : A` is the
  denominator of `f`.
* `HomogeneousLocalization.deg`: if `f : HomogeneousLocalization 𝒜 x`, then `f.deg : ι` is the
  degree of `f` such that `f.num ∈ 𝒜 f.deg` and `f.den ∈ 𝒜 f.deg`
  (see `HomogeneousLocalization.num_mem_deg` and `HomogeneousLocalization.den_mem_deg`).
* `HomogeneousLocalization.num_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.num_mem_deg` is a proof that `f.num ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.den_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.den_mem_deg` is a proof that `f.den ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.eq_num_div_den`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.val : Aₓ` is equal to `f.num / f.den`.

* `HomogeneousLocalization.localRing`: `HomogeneousLocalization 𝒜 x` is a local ring when `x` is
  the complement of some prime ideals.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable section

open DirectSum BigOperators Pointwise

open DirectSum SetLike

variable {ι R A : Type*}

variable [AddCommMonoid ι] [DecidableEq ι]

variable [CommRing R] [CommRing A] [Algebra R A]

variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

variable (x : Submonoid A)

local notation "at " x => Localization x

namespace HomogeneousLocalization

section

/-- Let `x` be a submonoid of `A`, then `NumDenSameDeg 𝒜 x` is a structure with a numerator and a
denominator with same grading such that the denominator is contained in `x`.
-/
-- @[nolint has_nonempty_instance] -- Porting note: This linter does not exist yet.
structure NumDenSameDeg where
  deg : ι
  (num den : 𝒜 deg)
  den_mem : (den : A) ∈ x
#align homogeneous_localization.num_denom_same_deg HomogeneousLocalization.NumDenSameDeg

end

namespace NumDenSameDeg

open SetLike.GradedMonoid Submodule

variable {𝒜}

@[ext]
theorem ext {c1 c2 : NumDenSameDeg 𝒜 x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hden : (c1.den : A) = c2.den) : c1 = c2 := by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  -- ⊢ { deg := i1, num := { val := n1, property := hn1 }, den := { val := d1, prop …
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  -- ⊢ { deg := i1, num := { val := n1, property := hn1 }, den := { val := d1, prop …
  dsimp only [Subtype.coe_mk] at *
  -- ⊢ { deg := i1, num := { val := n1, property := hn1 }, den := { val := d1, prop …
  subst hdeg hnum hden
  -- ⊢ { deg := i1, num := { val := n1, property := hn1 }, den := { val := d1, prop …
  congr
  -- 🎉 no goals
#align homogeneous_localization.num_denom_same_deg.ext HomogeneousLocalization.NumDenSameDeg.ext

instance : One (NumDenSameDeg 𝒜 x) where
  one :=
    { deg := 0
      -- Porting note: Changed `one_mem` to `GradedOne.one_mem`
      num := ⟨1, GradedOne.one_mem⟩
      den := ⟨1, GradedOne.one_mem⟩
      den_mem := Submonoid.one_mem _ }

@[simp]
theorem deg_one : (1 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_one HomogeneousLocalization.NumDenSameDeg.deg_one

@[simp]
theorem num_one : ((1 : NumDenSameDeg 𝒜 x).num : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_one HomogeneousLocalization.NumDenSameDeg.num_one

@[simp]
theorem den_one : ((1 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_one HomogeneousLocalization.NumDenSameDeg.den_one

instance : Zero (NumDenSameDeg 𝒜 x) where
  zero := ⟨0, 0, ⟨1, GradedOne.one_mem⟩, Submonoid.one_mem _⟩

@[simp]
theorem deg_zero : (0 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_zero HomogeneousLocalization.NumDenSameDeg.deg_zero

@[simp]
theorem num_zero : (0 : NumDenSameDeg 𝒜 x).num = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_zero HomogeneousLocalization.NumDenSameDeg.num_zero

@[simp]
theorem den_zero : ((0 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_zero HomogeneousLocalization.NumDenSameDeg.den_zero

instance : Mul (NumDenSameDeg 𝒜 x) where
  mul p q :=
    { deg := p.deg + q.deg
      -- Porting note: Changed `mul_mem` to `GradedMul.mul_mem`
      num := ⟨p.num * q.num, GradedMul.mul_mem p.num.prop q.num.prop⟩
      den := ⟨p.den * q.den, GradedMul.mul_mem p.den.prop q.den.prop⟩
      den_mem := Submonoid.mul_mem _ p.den_mem q.den_mem }

@[simp]
theorem deg_mul (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_mul HomogeneousLocalization.NumDenSameDeg.deg_mul

@[simp]
theorem num_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_mul HomogeneousLocalization.NumDenSameDeg.num_mul

@[simp]
theorem den_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).den : A) = c1.den * c2.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_mul HomogeneousLocalization.NumDenSameDeg.den_mul

instance : Add (NumDenSameDeg 𝒜 x) where
  add c1 c2 :=
    { deg := c1.deg + c2.deg
      num := ⟨c1.den * c2.num + c2.den * c1.num,
        add_mem (GradedMul.mul_mem c1.den.2 c2.num.2)
          (add_comm c2.deg c1.deg ▸ GradedMul.mul_mem c2.den.2 c1.num.2)⟩
      den := ⟨c1.den * c2.den, GradedMul.mul_mem c1.den.2 c2.den.2⟩
      den_mem := Submonoid.mul_mem _ c1.den_mem c2.den_mem }

@[simp]
theorem deg_add (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_add HomogeneousLocalization.NumDenSameDeg.deg_add

@[simp]
theorem num_add (c1 c2 : NumDenSameDeg 𝒜 x) :
    ((c1 + c2).num : A) = c1.den * c2.num + c2.den * c1.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_add HomogeneousLocalization.NumDenSameDeg.num_add

@[simp]
theorem den_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).den : A) = c1.den * c2.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_add HomogeneousLocalization.NumDenSameDeg.den_add

instance : Neg (NumDenSameDeg 𝒜 x) where
  neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

@[simp]
theorem deg_neg (c : NumDenSameDeg 𝒜 x) : (-c).deg = c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_neg HomogeneousLocalization.NumDenSameDeg.deg_neg

@[simp]
theorem num_neg (c : NumDenSameDeg 𝒜 x) : ((-c).num : A) = -c.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_neg HomogeneousLocalization.NumDenSameDeg.num_neg

@[simp]
theorem den_neg (c : NumDenSameDeg 𝒜 x) : ((-c).den : A) = c.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_neg HomogeneousLocalization.NumDenSameDeg.den_neg

instance : CommMonoid (NumDenSameDeg 𝒜 x) where
  one := 1
  mul := (· * ·)
  mul_assoc c1 c2 c3 := ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul c := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one c := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm c1 c2 := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

instance : Pow (NumDenSameDeg 𝒜 x) ℕ where
  pow c n :=
    ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den, by
        induction' n with n ih
        -- ⊢ ↑(GradedMonoid.GMonoid.gnpow Nat.zero c.den) ∈ x
        · simpa only [Nat.zero_eq, coe_gnpow, pow_zero] using Submonoid.one_mem _
          -- 🎉 no goals
        · simpa only [pow_succ', coe_gnpow] using x.mul_mem ih c.den_mem⟩
          -- 🎉 no goals

@[simp]
theorem deg_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : (c ^ n).deg = n • c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_pow HomogeneousLocalization.NumDenSameDeg.deg_pow

@[simp]
theorem num_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).num : A) = (c.num : A) ^ n :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_pow HomogeneousLocalization.NumDenSameDeg.num_pow

@[simp]
theorem den_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).den : A) = (c.den : A) ^ n :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_pow HomogeneousLocalization.NumDenSameDeg.den_pow

section SMul

variable {α : Type*} [SMul α R] [SMul α A] [IsScalarTower α R A]

instance : SMul α (NumDenSameDeg 𝒜 x) where
  smul m c := ⟨c.deg, m • c.num, c.den, c.den_mem⟩

@[simp]
theorem deg_smul (c : NumDenSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_smul HomogeneousLocalization.NumDenSameDeg.deg_smul

@[simp]
theorem num_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_smul HomogeneousLocalization.NumDenSameDeg.num_smul

@[simp]
theorem den_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).den : A) = c.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_smul HomogeneousLocalization.NumDenSameDeg.den_smul

end SMul

variable (𝒜)

/-- For `x : prime ideal of A` and any `p : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.den` of `Aₓ`.
-/
def embedding (p : NumDenSameDeg 𝒜 x) : at x :=
  Localization.mk p.num ⟨p.den, p.den_mem⟩
#align homogeneous_localization.num_denom_same_deg.embedding HomogeneousLocalization.NumDenSameDeg.embedding

end NumDenSameDeg

end HomogeneousLocalization

/-- For `x : prime ideal of A`, `HomogeneousLocalization 𝒜 x` is `NumDenSameDeg 𝒜 x` modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the numerator and
denominator share the same grading.
-/
-- @[nolint has_nonempty_instance] -- Porting note: This linter does not exist yet.
def HomogeneousLocalization : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)
#align homogeneous_localization HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

variable {𝒜} {x}

/-- View an element of `HomogeneousLocalization 𝒜 x` as an element of `Aₓ` by forgetting that the
numerator and denominator are of the same grading.
-/
def val (y : HomogeneousLocalization 𝒜 x) : at x :=
  Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id
#align homogeneous_localization.val HomogeneousLocalization.val

@[simp]
theorem val_mk'' (i : NumDenSameDeg 𝒜 x) :
    val (Quotient.mk'' i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩ :=
  rfl
#align homogeneous_localization.val_mk' HomogeneousLocalization.val_mk''

variable (x)

theorem val_injective : Function.Injective (HomogeneousLocalization.val (𝒜 := 𝒜) (x := x)) :=
  fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h
#align homogeneous_localization.val_injective HomogeneousLocalization.val_injective

instance hasPow : Pow (HomogeneousLocalization 𝒜 x) ℕ where
  pow z n :=
    (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
          change Localization.mk _ _ = Localization.mk _ _
          -- ⊢ Localization.mk ↑((fun x_1 => x_1 ^ n) c1).num { val := ↑((fun x_1 => x_1 ^  …
          simp only [num_pow, den_pow]
          -- ⊢ Localization.mk (↑c1.num ^ n) { val := ↑c1.den ^ n, property := (_ : (fun x_ …
          convert congr_arg (fun z : at x => z ^ n) h <;> erw [Localization.mk_pow] <;> rfl :
          -- ⊢ Localization.mk (↑c1.num ^ n) { val := ↑c1.den ^ n, property := (_ : (fun x_ …
                                                          -- ⊢ Localization.mk (↑c1.num ^ n) { val := ↑c1.den ^ n, property := (_ : (fun x_ …
                                                          -- ⊢ Localization.mk (↑c2.num ^ n) { val := ↑c2.den ^ n, property := (_ : (fun x_ …
                                                                                        -- 🎉 no goals
                                                                                        -- 🎉 no goals
        HomogeneousLocalization 𝒜 x → HomogeneousLocalization 𝒜 x)
      z
#align homogeneous_localization.has_pow HomogeneousLocalization.hasPow

section SMul

variable {α : Type*} [SMul α R] [SMul α A] [IsScalarTower α R A]

variable [IsScalarTower α A A]

instance : SMul α (HomogeneousLocalization 𝒜 x) where
  smul m := Quotient.map' (m • ·) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    -- ⊢ Localization.mk ↑((fun x_1 => m • x_1) c1).num { val := ↑((fun x_1 => m • x_ …
    simp only [num_smul, den_smul]
    -- ⊢ Localization.mk ↑(m • c1.num) { val := ↑c1.den, property := (_ : (fun x_1 => …
    convert congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk] <;> rfl
    -- ⊢ Localization.mk ↑(m • c1.num) { val := ↑c1.den, property := (_ : (fun x_1 => …
                                                    -- ⊢ Localization.mk ↑(m • c1.num) { val := ↑c1.den, property := (_ : (fun x_1 => …
                                                    -- ⊢ Localization.mk ↑(m • c2.num) { val := ↑c2.den, property := (_ : (fun x_1 => …
                                                                                  -- 🎉 no goals
                                                                                  -- 🎉 no goals

@[simp]
theorem smul_val (y : HomogeneousLocalization 𝒜 x) (n : α) : (n • y).val = n • y.val := by
  induction y using Quotient.inductionOn
  -- ⊢ val (n • Quotient.mk (Setoid.ker (embedding 𝒜 x)) a✝) = n • val (Quotient.mk …
  change Localization.mk _ _ = n • Localization.mk _ _
  -- ⊢ Localization.mk ↑((fun x_1 => n • x_1) a✝).num { val := ↑((fun x_1 => n • x_ …
  dsimp only
  -- ⊢ Localization.mk ↑(n • a✝).num { val := ↑(n • a✝).den, property := (_ : ↑(n • …
  rw [Localization.smul_mk]
  -- ⊢ Localization.mk ↑(n • a✝).num { val := ↑(n • a✝).den, property := (_ : ↑(n • …
  congr 1
  -- 🎉 no goals
#align homogeneous_localization.smul_val HomogeneousLocalization.smul_val

end SMul

instance : Neg (HomogeneousLocalization 𝒜 x) where
  neg := Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    -- ⊢ Localization.mk ↑(-c1).num { val := ↑(-c1).den, property := (_ : ↑(-c1).den  …
    simp only [num_neg, den_neg, ← Localization.neg_mk]
    -- ⊢ -Localization.mk ↑c1.num { val := ↑c1.den, property := (_ : (fun x_1 => x_1  …
    exact congr_arg Neg.neg h
    -- 🎉 no goals

instance : Add (HomogeneousLocalization 𝒜 x) where
  add :=
    Quotient.map₂' (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      -- ⊢ Localization.mk ↑((fun x_1 x_2 => x_1 + x_2) c1 c3).num { val := ↑((fun x_1  …
      simp only [num_add, den_add, ← Localization.add_mk]
      -- ⊢ Localization.mk (↑c1.den * ↑c3.num + ↑c3.den * ↑c1.num) { val := ↑c1.den * ↑ …
      convert congr_arg₂ (· + ·) h h' <;> erw [Localization.add_mk] <;> rfl
      -- ⊢ Localization.mk (↑c1.den * ↑c3.num + ↑c3.den * ↑c1.num) { val := ↑c1.den * ↑ …
                                          -- ⊢ Localization.mk (↑c1.den * ↑c3.num + ↑c3.den * ↑c1.num) { val := ↑c1.den * ↑ …
                                          -- ⊢ Localization.mk (↑c2.den * ↑c4.num + ↑c4.den * ↑c2.num) { val := ↑c2.den * ↑ …
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals

instance : Sub (HomogeneousLocalization 𝒜 x) where sub z1 z2 := z1 + -z2

instance : Mul (HomogeneousLocalization 𝒜 x) where
  mul :=
    Quotient.map₂' (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      -- ⊢ Localization.mk ↑((fun x_1 x_2 => x_1 * x_2) c1 c3).num { val := ↑((fun x_1  …
      simp only [num_mul, den_mul]
      -- ⊢ Localization.mk (↑c1.num * ↑c3.num) { val := ↑c1.den * ↑c3.den, property :=  …
      convert congr_arg₂ (· * ·) h h' <;> erw [Localization.mk_mul] <;> rfl
      -- ⊢ Localization.mk (↑c1.num * ↑c3.num) { val := ↑c1.den * ↑c3.den, property :=  …
                                          -- ⊢ Localization.mk (↑c1.num * ↑c3.num) { val := ↑c1.den * ↑c3.den, property :=  …
                                          -- ⊢ Localization.mk (↑c2.num * ↑c4.num) { val := ↑c2.den * ↑c4.den, property :=  …
                                                                        -- 🎉 no goals
                                                                        -- 🎉 no goals

instance : One (HomogeneousLocalization 𝒜 x) where one := Quotient.mk'' 1

instance : Zero (HomogeneousLocalization 𝒜 x) where zero := Quotient.mk'' 0

theorem zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0 :=
  rfl
#align homogeneous_localization.zero_eq HomogeneousLocalization.zero_eq

theorem one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1 :=
  rfl
#align homogeneous_localization.one_eq HomogeneousLocalization.one_eq

variable {x}

theorem zero_val : (0 : HomogeneousLocalization 𝒜 x).val = 0 :=
  Localization.mk_zero _
#align homogeneous_localization.zero_val HomogeneousLocalization.zero_val

theorem one_val : (1 : HomogeneousLocalization 𝒜 x).val = 1 :=
  Localization.mk_one
#align homogeneous_localization.one_val HomogeneousLocalization.one_val

@[simp]
theorem add_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 + y2).val = y1.val + y2.val := by
  induction y1 using Quotient.inductionOn
  -- ⊢ val (Quotient.mk (Setoid.ker (embedding 𝒜 x)) a✝ + y2) = val (Quotient.mk (S …
  induction y2 using Quotient.inductionOn
  -- ⊢ val (Quotient.mk (Setoid.ker (embedding 𝒜 x)) a✝¹ + Quotient.mk (Setoid.ker  …
  change Localization.mk _ _ = Localization.mk _ _ + Localization.mk _ _
  -- ⊢ Localization.mk ↑((fun x_1 x_2 => x_1 + x_2) a✝¹ a✝).num { val := ↑((fun x_1 …
  dsimp only
  -- ⊢ Localization.mk ↑(a✝¹ + a✝).num { val := ↑(a✝¹ + a✝).den, property := (_ : ↑ …
  rw [Localization.add_mk]
  -- ⊢ Localization.mk ↑(a✝¹ + a✝).num { val := ↑(a✝¹ + a✝).den, property := (_ : ↑ …
  rfl
  -- 🎉 no goals
#align homogeneous_localization.add_val HomogeneousLocalization.add_val

@[simp]
theorem mul_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 * y2).val = y1.val * y2.val := by
  induction y1 using Quotient.inductionOn
  -- ⊢ val (Quotient.mk (Setoid.ker (embedding 𝒜 x)) a✝ * y2) = val (Quotient.mk (S …
  induction y2 using Quotient.inductionOn
  -- ⊢ val (Quotient.mk (Setoid.ker (embedding 𝒜 x)) a✝¹ * Quotient.mk (Setoid.ker  …
  change Localization.mk _ _ = Localization.mk _ _ * Localization.mk _ _
  -- ⊢ Localization.mk ↑((fun x_1 x_2 => x_1 * x_2) a✝¹ a✝).num { val := ↑((fun x_1 …
  dsimp only
  -- ⊢ Localization.mk ↑(a✝¹ * a✝).num { val := ↑(a✝¹ * a✝).den, property := (_ : ↑ …
  rw [Localization.mk_mul]
  -- ⊢ Localization.mk ↑(a✝¹ * a✝).num { val := ↑(a✝¹ * a✝).den, property := (_ : ↑ …
  rfl
  -- 🎉 no goals
#align homogeneous_localization.mul_val HomogeneousLocalization.mul_val

@[simp]
theorem neg_val (y : HomogeneousLocalization 𝒜 x) : (-y).val = -y.val := by
  induction y using Quotient.inductionOn
  -- ⊢ val (-Quotient.mk (Setoid.ker (embedding 𝒜 x)) a✝) = -val (Quotient.mk (Seto …
  change Localization.mk _ _ = -Localization.mk _ _
  -- ⊢ Localization.mk ↑(-a✝).num { val := ↑(-a✝).den, property := (_ : ↑(-a✝).den  …
  dsimp only
  -- ⊢ Localization.mk ↑(-a✝).num { val := ↑(-a✝).den, property := (_ : ↑(-a✝).den  …
  rw [Localization.neg_mk]
  -- ⊢ Localization.mk ↑(-a✝).num { val := ↑(-a✝).den, property := (_ : ↑(-a✝).den  …
  rfl
  -- 🎉 no goals
#align homogeneous_localization.neg_val HomogeneousLocalization.neg_val

@[simp]
theorem sub_val (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y2.val := by
  rw [show y1 - y2 = y1 + -y2 from rfl, add_val, neg_val]; rfl
  -- ⊢ val y1 + -val y2 = val y1 - val y2
                                                           -- 🎉 no goals
#align homogeneous_localization.sub_val HomogeneousLocalization.sub_val

@[simp]
theorem pow_val (y : HomogeneousLocalization 𝒜 x) (n : ℕ) : (y ^ n).val = y.val ^ n := by
  induction y using Quotient.inductionOn
  -- ⊢ val (Quotient.mk (Setoid.ker (embedding 𝒜 x)) a✝ ^ n) = val (Quotient.mk (Se …
  change Localization.mk _ _ = Localization.mk _ _ ^ n
  -- ⊢ Localization.mk ↑((fun x_1 => x_1 ^ n) a✝).num { val := ↑((fun x_1 => x_1 ^  …
  rw [Localization.mk_pow]
  -- ⊢ Localization.mk ↑((fun x_1 => x_1 ^ n) a✝).num { val := ↑((fun x_1 => x_1 ^  …
  dsimp only
  -- ⊢ Localization.mk ↑(a✝ ^ n).num { val := ↑(a✝ ^ n).den, property := (_ : ↑(a✝  …
  congr 1
  -- 🎉 no goals
#align homogeneous_localization.pow_val HomogeneousLocalization.pow_val

instance : NatCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Nat.unaryCast⟩

instance : IntCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Int.castDef⟩

@[simp]
theorem natCast_val (n : ℕ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, zero_val, one_val, *]
                                    -- ⊢ val (Nat.unaryCast Nat.zero) = ↑Nat.zero
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals
#align homogeneous_localization.nat_cast_val HomogeneousLocalization.natCast_val

@[simp]
theorem intCast_val (n : ℤ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, zero_val, one_val, *]
                                  -- ⊢ val (Int.castDef (Int.ofNat a✝)) = ↑(Int.ofNat a✝)
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align homogeneous_localization.int_cast_val HomogeneousLocalization.intCast_val

instance homogenousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.val_injective x).commRing _ zero_val one_val add_val mul_val neg_val
    sub_val (smul_val x · ·) (smul_val x · ·) pow_val natCast_val intCast_val
#align homogeneous_localization.homogenous_localization_comm_ring HomogeneousLocalization.homogenousLocalizationCommRing

instance homogeneousLocalizationAlgebra :
    Algebra (HomogeneousLocalization 𝒜 x) (Localization x) where
  smul p q := p.val * q
  toFun := val
  map_one' := one_val
  map_mul' := mul_val
  map_zero' := zero_val
  map_add' := add_val
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl
#align homogeneous_localization.homogeneous_localization_algebra HomogeneousLocalization.homogeneousLocalizationAlgebra

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

variable {𝒜} {x}

/-- Numerator of an element in `HomogeneousLocalization x`. -/
def num (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).num
#align homogeneous_localization.num HomogeneousLocalization.num

/-- Denominator of an element in `HomogeneousLocalization x`. -/
def den (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).den
#align homogeneous_localization.denom HomogeneousLocalization.den

/-- For an element in `HomogeneousLocalization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : HomogeneousLocalization 𝒜 x) : ι :=
  (Quotient.out' f).deg
#align homogeneous_localization.deg HomogeneousLocalization.deg

theorem den_mem (f : HomogeneousLocalization 𝒜 x) : f.den ∈ x :=
  (Quotient.out' f).den_mem
#align homogeneous_localization.denom_mem HomogeneousLocalization.den_mem

theorem num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num ∈ 𝒜 f.deg :=
  (Quotient.out' f).num.2
#align homogeneous_localization.num_mem_deg HomogeneousLocalization.num_mem_deg

theorem den_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.den ∈ 𝒜 f.deg :=
  (Quotient.out' f).den.2
#align homogeneous_localization.denom_mem_deg HomogeneousLocalization.den_mem_deg

theorem eq_num_div_den (f : HomogeneousLocalization 𝒜 x) :
    f.val = Localization.mk f.num ⟨f.den, f.den_mem⟩ := by
  have := Quotient.out_eq' f
  -- ⊢ val f = Localization.mk (num f) { val := den f, property := (_ : den f ∈ x) }
  apply_fun HomogeneousLocalization.val at this
  -- ⊢ val f = Localization.mk (num f) { val := den f, property := (_ : den f ∈ x) }
  rw [← this]
  -- ⊢ val (Quotient.mk'' (Quotient.out' f)) = Localization.mk (num f) { val := den …
  rfl
  -- 🎉 no goals
#align homogeneous_localization.eq_num_div_denom HomogeneousLocalization.eq_num_div_den

theorem ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val :=
  { mp := fun h => h ▸ rfl
    mpr := fun h => by
      induction f using Quotient.inductionOn'
      -- ⊢ Quotient.mk'' a✝ = g
      induction g using Quotient.inductionOn'
      -- ⊢ Quotient.mk'' a✝¹ = Quotient.mk'' a✝
      rw [Quotient.eq'']
      -- ⊢ Setoid.r a✝¹ a✝
      simpa only [Quotient.liftOn'_mk] using h }
      -- 🎉 no goals
#align homogeneous_localization.ext_iff_val HomogeneousLocalization.ext_iff_val

section

variable (𝒜) (𝔭 : Ideal A) [Ideal.IsPrime 𝔭]

/-- Localizing a ring homogeneously at a prime ideal. -/
abbrev AtPrime :=
  HomogeneousLocalization 𝒜 𝔭.primeCompl
#align homogeneous_localization.at_prime HomogeneousLocalization.AtPrime

theorem isUnit_iff_isUnit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) : IsUnit f.val ↔ IsUnit f :=
  ⟨fun h1 => by
    rcases h1 with ⟨⟨a, b, eq0, eq1⟩, eq2 : a = f.val⟩
    -- ⊢ IsUnit f
    rw [eq2] at eq0 eq1
    -- ⊢ IsUnit f
    clear a eq2
    -- ⊢ IsUnit f
    induction' b using Localization.induction_on with data
    -- ⊢ IsUnit f
    rcases data with ⟨a, ⟨b, hb⟩⟩
    -- ⊢ IsUnit f
    dsimp only at eq0 eq1
    -- ⊢ IsUnit f
    have b_f_den_not_mem : b * f.den ∈ 𝔭.primeCompl :=
      fun r => Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r) (hb ·) (f.den_mem ·)
    rw [f.eq_num_div_den, Localization.mk_mul,
      show (⟨b, hb⟩ : 𝔭.primeCompl) * ⟨f.den, _⟩ = ⟨b * f.den, _⟩ from rfl,
      show (1 : Localization.AtPrime 𝔭) = Localization.mk 1 1 by erw [Localization.mk_self 1],
      Localization.mk_eq_mk', IsLocalization.eq] at eq1
    rcases eq1 with ⟨⟨c, hc⟩, eq1⟩
    -- ⊢ IsUnit f
    change c * (1 * (a * f.num)) = _ at eq1
    -- ⊢ IsUnit f
    simp only [one_mul, mul_one] at eq1
    -- ⊢ IsUnit f
    have mem1 : c * (a * f.num) ∈ 𝔭.primeCompl :=
      eq1.symm ▸ fun r => Or.elim (Ideal.IsPrime.mem_or_mem inferInstance r) (by tauto) (by tauto)
    have mem2 : f.num ∉ 𝔭 := by
      contrapose! mem1
      erw [Classical.not_not]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ mem1)
    refine' ⟨⟨f, Quotient.mk'' ⟨f.deg, ⟨f.den, f.den_mem_deg⟩, ⟨f.num, f.num_mem_deg⟩, mem2⟩, _, _⟩,
        rfl⟩
      <;> simp only [ext_iff_val, mul_val, val_mk'', f.eq_num_div_den, Localization.mk_mul, one_val]
          -- ⊢ Localization.mk (num f * den f) ({ val := den f, property := (_ : den f ∈ Id …
          -- ⊢ Localization.mk (den f * num f) ({ val := num f, property := (_ : ↑{ deg :=  …
      <;> convert Localization.mk_self (M := A) _
          -- ⊢ num f * den f = ↑({ val := den f, property := (_ : den f ∈ Ideal.primeCompl  …
          -- ⊢ den f * num f = ↑({ val := num f, property := (_ : ↑{ deg := deg f, num := { …
      <;> rw [mul_comm]
          -- ⊢ den f * num f = ↑({ val := den f, property := (_ : den f ∈ Ideal.primeCompl  …
          -- ⊢ num f * den f = ↑({ val := num f, property := (_ : ↑{ deg := deg f, num := { …
      <;> rfl ,
          -- 🎉 no goals
          -- 🎉 no goals
    fun ⟨⟨_, b, eq1, eq2⟩, rfl⟩ => by
    simp only [ext_iff_val, mul_val, one_val] at eq1 eq2
    -- ⊢ IsUnit (val f)
    exact ⟨⟨f.val, b.val, eq1, eq2⟩, rfl⟩⟩
    -- 🎉 no goals
#align homogeneous_localization.is_unit_iff_is_unit_val HomogeneousLocalization.isUnit_iff_isUnit_val

instance : Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  ⟨⟨0, 1, fun r => by simp [ext_iff_val, zero_val, one_val, zero_ne_one] at r⟩⟩
                      -- 🎉 no goals

instance localRing : LocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [← isUnit_iff_isUnit_val, sub_val, one_val]
    -- ⊢ IsUnit (val a) ∨ IsUnit (1 - val a)
    induction' a using Quotient.inductionOn' with a
    -- ⊢ IsUnit (val (Quotient.mk'' a)) ∨ IsUnit (1 - val (Quotient.mk'' a))
    simp only [HomogeneousLocalization.val_mk'']
    -- ⊢ IsUnit (Localization.mk ↑a.num { val := ↑a.den, property := (_ : ↑a.den ∈ Id …
    by_cases mem1 : a.num.1 ∈ 𝔭
    -- ⊢ IsUnit (Localization.mk ↑a.num { val := ↑a.den, property := (_ : ↑a.den ∈ Id …
    · right
      -- ⊢ IsUnit (1 - Localization.mk ↑a.num { val := ↑a.den, property := (_ : ↑a.den  …
      have : a.den.1 - a.num.1 ∈ 𝔭.primeCompl := fun h =>
        a.den_mem (sub_add_cancel a.den.val a.num.val ▸ Ideal.add_mem _ h mem1 : a.den.1 ∈ 𝔭)
      apply isUnit_of_mul_eq_one _ (Localization.mk a.den.1 ⟨a.den.1 - a.num.1, this⟩)
      -- ⊢ (1 - Localization.mk ↑a.num { val := ↑a.den, property := (_ : ↑a.den ∈ Ideal …
      simp only [sub_mul, Localization.mk_mul, one_mul, Localization.sub_mk, Submonoid.coe_mul]
      -- ⊢ Localization.mk (↑a.den * (↑a.den - ↑a.num) * ↑a.den - (↑a.den * (↑a.num * ↑ …
      convert Localization.mk_self (M := A) _
      -- ⊢ ↑a.den * (↑a.den - ↑a.num) * ↑a.den - (↑a.den * (↑a.num * ↑a.den) - ↑a.num * …
      simp only [Submonoid.coe_mul]
      -- ⊢ ↑a.den * (↑a.den - ↑a.num) * ↑a.den - (↑a.den * (↑a.num * ↑a.den) - ↑a.num * …
      ring
      -- 🎉 no goals
    · left
      -- ⊢ IsUnit (Localization.mk ↑a.num { val := ↑a.den, property := (_ : ↑a.den ∈ Id …
      change _ ∈ 𝔭.primeCompl at mem1
      -- ⊢ IsUnit (Localization.mk ↑a.num { val := ↑a.den, property := (_ : ↑a.den ∈ Id …
      apply isUnit_of_mul_eq_one _ (Localization.mk a.den.1 ⟨a.num.1, mem1⟩)
      -- ⊢ Localization.mk ↑a.num { val := ↑a.den, property := (_ : ↑a.den ∈ Ideal.prim …
      rw [Localization.mk_mul]
      -- ⊢ Localization.mk (↑a.num * ↑a.den) ({ val := ↑a.den, property := (_ : ↑a.den  …
      convert Localization.mk_self (M := A) _
      -- ⊢ ↑a.num * ↑a.den = ↑({ val := ↑a.den, property := (_ : ↑a.den ∈ Ideal.primeCo …
      rw [mul_comm]
      -- ⊢ ↑a.den * ↑a.num = ↑({ val := ↑a.den, property := (_ : ↑a.den ∈ Ideal.primeCo …
      rfl
      -- 🎉 no goals

end

section

variable (𝒜) (f : A)

/-- Localizing away from powers of `f` homogeneously. -/
abbrev Away :=
  HomogeneousLocalization 𝒜 (Submonoid.powers f)
#align homogeneous_localization.away HomogeneousLocalization.Away

end

end HomogeneousLocalization
