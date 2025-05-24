import Mathlib.HahnEmbedding.ArchimedeanClass

import Mathlib.GroupTheory.Divisible
import Mathlib.Algebra.Order.Hom.Monoid


theorem Rat.mul_den' (q₁ q₂ : ℚ) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [Rat.mul_den]
  symm
  apply (Nat.dvd_iff_div_mul_eq _ _).mp
  apply Nat.gcd_dvd_right

theorem Rat.mul_num' (q₁ q₂ : ℚ) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [Rat.mul_num]
  refine Eq.symm (Int.ediv_mul_cancel ?_)
  rw [← Int.dvd_natAbs]
  refine Int.ofNat_dvd.mpr ?_
  apply Nat.gcd_dvd_left

namespace RootableBy

@[to_additive div_one]
theorem root_one {M : Type*} [Monoid M] [RootableBy M ℕ] (a : M) :
    root a 1 = a := by
  rw [← pow_one (root a 1)]
  rw [root_cancel _ (by simp)]

@[to_additive zero_div]
theorem one_root (M : Type*) [Monoid M] [RootableBy M ℕ] [IsMulTorsionFree M] (n : ℕ) :
    root (1 : M) n = 1 := by
  by_cases h : n = 0
  · rw [h]
    rw [root_zero]
  · apply (pow_left_inj h).mp
    rw [root_cancel _ h]
    simp

@[to_additive div_neg]
theorem root_inv (M : Type*) [Group M] [RootableBy M ℕ] [IsMulTorsionFree M] (a : M) (n : ℕ):
    root a⁻¹ n = (root a n)⁻¹ := by
  by_cases h : n = 0
  · rw [h]
    rw [root_zero, root_zero]
    simp
  · apply pow_left_injective h
    simp only
    rw [root_cancel _ h, inv_pow, root_cancel _ h]

end RootableBy

namespace DivisibleBy

@[instance 100]
instance instSMul (M : Type*) [AddGroup M] [h : DivisibleBy M ℕ] : SMul ℚ M where
  smul (s : ℚ) (a : M) := div (s.num • a) s.den

theorem rat_smul_eq {M : Type*} [AddGroup M] [h : DivisibleBy M ℕ] (s : ℚ) (a : M) :
  s • a = div (s.num • a) s.den := rfl

@[instance 100]
instance instModule (M : Type*) [AddCommGroup M] [h : DivisibleBy M ℕ] [IsAddTorsionFree M] :
    Module ℚ M where
  one_smul := by
    intro a
    rw [rat_smul_eq]
    simp only [Rat.num_ofNat, one_smul, Rat.den_ofNat]
    rw [div_one]
  mul_smul := by
    intro x y a
    rw [rat_smul_eq, rat_smul_eq, rat_smul_eq]
    apply (nsmul_right_inj (by simp : (x.den * y.den) ≠ 0)).mp
    nth_rw 1 [Rat.mul_den']
    rw [mul_comm (x * y).den, ← smul_smul, div_cancel _ (by simp)]
    rw [mul_comm x.den, ← smul_smul, div_cancel _ (by simp),
      smul_comm y.den x.num, div_cancel _ (by simp)]
    have : (x.num * y.num).natAbs.gcd (y.den * x.den) • (x * y).num • a =
      ((x.num * y.num).natAbs.gcd (y.den * x.den) : ℤ) • (x * y).num • a := by symm; apply natCast_zsmul
    rw [this, smul_smul, smul_smul, mul_comm y.den, mul_comm _ (x * y).num]
    congr 1
    symm
    apply Rat.mul_num'
  smul_zero := by
    intro a
    rw [rat_smul_eq]
    simp only [smul_zero]
    rw [zero_div]
  smul_add := by
    intro a x y
    rw [rat_smul_eq, rat_smul_eq, rat_smul_eq]
    apply (nsmul_right_inj (by simp : a.den ≠ 0)).mp
    rw [smul_add a.den]
    rw [div_cancel _ (by simp), div_cancel _ (by simp), div_cancel _ (by simp)]
    rw [smul_add]
  add_smul := by
    intro x y a
    rw [rat_smul_eq, rat_smul_eq, rat_smul_eq]
    apply (nsmul_right_inj (by simp : (x.den * y.den * (x + y).den) ≠ 0)).mp
    rw [← smul_smul, div_cancel _ (by simp)]
    rw [mul_comm (x.den * y.den), smul_add]
    nth_rw 2 [mul_comm x.den y.den]
    rw [← mul_assoc, ← mul_assoc, ← smul_smul ((x + y).den * y.den) x.den, ← smul_smul ((x + y).den * x.den) y.den]
    rw [div_cancel _ (by simp), div_cancel _ (by simp)]
    have : (x.den * y.den) • (x + y).num • a = ((x.den * y.den) : ℤ) • (x + y).num • a := by symm; apply natCast_zsmul
    rw [this]
    have : ((x + y).den * y.den) • x.num • a = ((x + y).den * y.den : ℤ) • x.num • a := by symm; apply natCast_zsmul
    rw [this]
    have : ((x + y).den * x.den) • y.num • a = ((x + y).den * x.den : ℤ) • y.num • a := by symm; apply natCast_zsmul
    rw [this]
    rw [smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [mul_assoc ((x + y).den : ℤ), mul_assoc ((x + y).den : ℤ), ← mul_add]
    rw [mul_comm _ (x + y).num, mul_comm ((x + y).den : ℤ), ← mul_assoc]
    rw [mul_comm _ x.num, mul_comm _ y.num]
    apply Rat.add_num_den'
  zero_smul := by
    intro a
    rw [rat_smul_eq]
    simp only [Rat.num_ofNat, zero_smul, Rat.den_ofNat]
    rw [div_one]

end DivisibleBy


section Order

namespace RootableBy

@[to_additive nonneg_div_of_nonneg]
theorem one_le_root_of_one_le {M : Type*} [CommMonoid M] [LinearOrder M] [MulLeftStrictMono M] [IsOrderedMonoid M]
    [RootableBy M ℕ] {a : M} (ha : 1 ≤ a) (n : ℕ) : 1 ≤ root a n := by
  by_cases hn : n = 0
  · rw [hn, root_zero]
  · apply le_of_pow_le_pow_left' hn
    rw [root_cancel _ hn]
    simpa using ha

@[to_additive nonpos_div_of_nonpos]
theorem le_one_root_of_le_one {M : Type*} [CommMonoid M] [LinearOrder M] [MulLeftStrictMono M] [IsOrderedMonoid M]
    [RootableBy M ℕ] {a : M} (ha : a ≤ 1) (n : ℕ) : root a n ≤ 1 := by
  by_cases hn : n = 0
  · rw [hn, root_zero]
  · apply le_of_pow_le_pow_left' hn
    rw [root_cancel _ hn]
    simpa using ha

@[to_additive div_le_self]
theorem root_le_self {M : Type*} [CommMonoid M] [LinearOrder M] [MulLeftStrictMono M] [IsOrderedMonoid M] [RootableBy M ℕ]
    {a : M} {n : ℕ} (ha : 1 ≤ a) (hn : n ≠ 0) :
    root a n ≤ a := by
  nth_rw 2 [← root_cancel a hn]
  exact le_self_pow (one_le_root_of_one_le ha _) hn

@[to_additive abs_div]
theorem mabs_root {M : Type*} [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] [RootableBy M ℕ]
    (a : M) (n : ℕ) : |root a n|ₘ = root |a|ₘ n := by
  by_cases hn : n = 0
  · rw [hn, root_zero, root_zero]
    simp
  · obtain ha|ha := le_total 1 a
    · obtain h := one_le_root_of_one_le ha n
      rw [mabs_eq_self.mpr ha, mabs_eq_self.mpr h]
    · obtain h := le_one_root_of_le_one ha n
      rw [mabs_eq_inv_self.mpr ha, mabs_eq_inv_self.mpr h]
      rw [root_inv]

end RootableBy

end Order


section Completion

structure PreDivisibleCompletion (M : Type*) [AddCommMonoid M]  where
  num : M
  den : ℕ+

@[to_additive]
structure PreRootableCompletion (M : Type*) [CommMonoid M]  where
  num : M
  den : ℕ+

@[to_additive]
def PreRootableCompletion.mul {M : Type*} [CommMonoid M] (a b : PreRootableCompletion M) : PreRootableCompletion M where
  num := a.num ^ (b.den : ℕ) * b.num ^ (a.den : ℕ)
  den := a.den * b.den

@[to_additive]
def PreRootableCompletionEquiv (M : Type*) [CommMonoid M] (a b : PreRootableCompletion M) : Prop :=
  a.num ^ (b.den : ℕ) = b.num ^ (a.den : ℕ)

@[to_additive]
theorem PreRootableCompletion.equiv (M : Type*) [CommMonoid M] [IsMulTorsionFree M] :
    Equivalence (PreRootableCompletionEquiv M) where
  refl := by
    intro x
    rfl
  symm := by
    intro x y h
    exact h.symm
  trans := by
    intro x y z hxy hyz
    unfold PreRootableCompletionEquiv at hxy hyz ⊢
    apply_fun (· ^ (z.den : ℕ)) at hxy
    apply_fun (· ^ (x.den : ℕ)) at hyz
    rw [← pow_mul, mul_comm, pow_mul] at hxy
    rw [← pow_mul, ← pow_mul, mul_comm (z.den : ℕ), mul_comm (y.den : ℕ), pow_mul, pow_mul] at hyz
    obtain hxz := hxy.trans hyz
    exact (pow_left_inj (by simp)).mp hxz

@[to_additive]
def PreRootableCompletion.setoid (M : Type*) [CommMonoid M] [IsMulTorsionFree M] : Setoid (PreRootableCompletion M) where
  r := PreRootableCompletionEquiv M
  iseqv := PreRootableCompletion.equiv M

@[to_additive]
abbrev RootableCompletion (M : Type*) [CommMonoid M] [IsMulTorsionFree M] := Quotient (PreRootableCompletion.setoid M)

@[to_additive]
abbrev RootableCompletion.mk {M : Type*} [CommMonoid M] [IsMulTorsionFree M] (num : M) (den : ℕ+) :
    RootableCompletion M :=
  ⟦⟨num, den⟩⟧

@[to_additive]
theorem RootableCompletion.eq_iff {M : Type*} [CommMonoid M] [IsMulTorsionFree M] (n1 n2 : M) (d1 d2 : ℕ+) :
    RootableCompletion.mk n1 d1 = RootableCompletion.mk n2 d2 ↔ n1 ^ (d2 : ℕ) = n2 ^ (d1 : ℕ) := by
  rw [Quotient.eq_iff_equiv]
  rfl

@[to_additive]
theorem RootableCompletion.out_eq {M : Type*} [CommMonoid M] [IsMulTorsionFree M] (a : RootableCompletion M) :
    RootableCompletion.mk (a.out.num) (a.out.den) = a := by apply Quotient.out_eq

@[to_additive]
instance RootableCompletion.instMul (M : Type*) [CommMonoid M] [IsMulTorsionFree M] : Mul (RootableCompletion M) where
  mul := Quotient.lift₂  (fun a b ↦ ⟦a.mul b⟧) (by
    intro a b a' b' ha hb
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    simp only [PNat.mul_coe]
    rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← mul_assoc,
      mul_comm (b.den : ℕ) (a'.den : ℕ), mul_right_comm (a.den : ℕ) (a'.den : ℕ),
      mul_comm (a.den : ℕ) (b'.den : ℕ),
      mul_assoc, mul_assoc,
      pow_mul a.num, pow_mul b.num]
    rw [ha, hb]
    rw [← pow_mul, ← pow_mul]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    · ring -- hack
    · ring -- hack
  )

@[to_additive]
theorem RootableCompletion.mul_def {M : Type*} [CommMonoid M] [IsMulTorsionFree M] (n1 n2 : M) (d1 d2 : ℕ+) :
    RootableCompletion.mk n1 d1 * RootableCompletion.mk n2 d2 =
    RootableCompletion.mk (n1 ^ (d2 : ℕ) * n2 ^ (d1 : ℕ)) (d1 * d2) := by
  rfl

@[to_additive]
instance RootableCompletion.instOne (M : Type*) [CommMonoid M] [IsMulTorsionFree M] : One (RootableCompletion M) where
  one := RootableCompletion.mk 1 1

@[to_additive]
theorem RootableCompletion.one_def (M : Type*) [CommMonoid M] [IsMulTorsionFree M] :
    (1 : RootableCompletion M) = RootableCompletion.mk 1 1 := by rfl

@[to_additive]
noncomputable
instance RootableCompletion.instCommMonoid (M : Type*) [CommMonoid M] [IsMulTorsionFree M] : CommMonoid (RootableCompletion M) where
  mul_assoc := by
    intro a b c
    rw [← RootableCompletion.out_eq a, ← RootableCompletion.out_eq b, ← RootableCompletion.out_eq c]
    set A := a.out
    set B := b.out
    set C := c.out
    rw [RootableCompletion.mul_def]
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    unfold PreRootableCompletion.mul
    simp only [PNat.mul_coe]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, mul_pow]
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
      ← pow_mul]
    rw [← mul_assoc (A.num ^ _) (B.num ^ _)]
    congr 2
    · congr 1
      ring -- hack
    · congr 1
      ring -- hack
    · ring -- hack
  one_mul := by
    intro a
    rw [← RootableCompletion.out_eq a]
    set A := a.out
    rw [RootableCompletion.one_def]
    rw [RootableCompletion.mul_def]
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    simp
  mul_one := by
    intro a
    rw [← RootableCompletion.out_eq a]
    set A := a.out
    rw [RootableCompletion.one_def]
    rw [RootableCompletion.mul_def]
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    simp
  mul_comm := by
    intro a b
    rw [← RootableCompletion.out_eq a, ← RootableCompletion.out_eq b]
    set A := a.out
    set B := b.out
    rw [RootableCompletion.mul_def]
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    simp only [PNat.mul_coe]
    nth_rw 1 [mul_comm]
    nth_rw 2 [mul_comm]
  npow (n : ℕ) (a : RootableCompletion M) := ⟦⟨a.out.num ^ n, a.out.den⟩⟧
  npow_zero := by
    intro a
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    simp
  npow_succ := by
    intro n a
    rw [← RootableCompletion.out_eq a]
    set A := a.out
    rw [RootableCompletion.mul_def]
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    have : A.num ^ ((RootableCompletion.mk A.num A.den).out.den : ℕ) = (RootableCompletion.mk A.num A.den).out.num ^ (A.den : ℕ) := by
      obtain h := Quotient.mk_out (s := PreRootableCompletion.setoid M) A
      exact h.symm
    rw [this]
    simp only [PNat.mul_coe]
    rw [← mul_pow, ← mul_comm, pow_mul, pow_succ]

@[to_additive]
theorem RootableCompletion.pow_def {M : Type*} [CommMonoid M] [IsMulTorsionFree M] (n : M) (d: ℕ+) (m : ℕ) :
    (RootableCompletion.mk n d) ^ m=
    (RootableCompletion.mk (n ^ m) d) := by
  apply (RootableCompletion.eq_iff _ _ _ _).mpr
  rw [← pow_mul, ← pow_mul, mul_comm m, mul_comm m, pow_mul, pow_mul]
  congr 1
  apply (RootableCompletion.eq_iff _ _ _ _).mp
  rw [RootableCompletion.out_eq]

@[to_additive]
noncomputable
instance RootableCompletion.instCommGroup (M : Type*) [CommGroup M] [IsMulTorsionFree M] : CommGroup (RootableCompletion M) := {
  (RootableCompletion.instCommMonoid M : CommMonoid (RootableCompletion M)) with
  inv := fun a ↦ ⟦⟨a.out.num⁻¹, a.out.den⟩⟧
  inv_mul_cancel := by
    intro a
    rw [← RootableCompletion.out_eq a]
    set A := a.out
    rw [RootableCompletion.mul_def]
    simp only [inv_pow]
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    simp only [PNat.val_ofNat, pow_one, PNat.mul_coe, one_pow]
    apply inv_mul_eq_one.mpr
    obtain h := Quotient.mk_out (s := PreRootableCompletion.setoid M) A
    exact h
}

@[to_additive]
theorem RootableCompletion.inv_def {M : Type*} [CommGroup M] [IsMulTorsionFree M] (n : M) (d: ℕ+) :
    (RootableCompletion.mk n d)⁻¹ = RootableCompletion.mk n⁻¹ d := by
  apply (RootableCompletion.eq_iff _ _ _ _).mpr
  rw [inv_pow, inv_pow]
  congr 1
  apply (RootableCompletion.eq_iff _ _ _ _).mp
  rw [RootableCompletion.out_eq]

@[to_additive]
noncomputable
instance RootableCompletion.instRootableBy (M : Type*) [CommGroup M] [IsMulTorsionFree M] :
    RootableBy (RootableCompletion M) ℕ where
  root (a : RootableCompletion M) (n : ℕ) :=
    if h : n = 0 then
      1
    else
      ⟦⟨a.out.num, a.out.den * ⟨n, (Nat.zero_lt_of_ne_zero h)⟩⟩⟧
  root_zero := by
    intro a
    simp
  root_cancel := by
    intro n a h
    rw [← RootableCompletion.out_eq a]
    set A := a.out
    simp [h]
    rw [RootableCompletion.pow_def]
    apply (RootableCompletion.eq_iff _ _ _ _).mpr
    simp only [PNat.mul_coe, PNat.mk_coe]
    rw [← pow_mul, mul_comm, pow_mul, pow_mul]
    congr 1
    unfold A
    rw [RootableCompletion.out_eq]

@[to_additive]
instance RootableCompletion.instLE (M : Type*) [CommGroup M] [IsMulTorsionFree M] [LE M]:
    LE (RootableCompletion M) where
  le (a b : RootableCompletion M) := a.out.num ^ (b.out.den : ℕ) ≤ b.out.num ^ (a.out.den : ℕ)

@[to_additive]
theorem RootableCompletion.le_def {M : Type*} [CommGroup M] [IsMulTorsionFree M] [LE M] (a b : RootableCompletion M):
    a ≤ b ↔ a.out.num ^ (b.out.den : ℕ) ≤ b.out.num ^ (a.out.den : ℕ) := by rfl

@[to_additive]
theorem RootableCompletion.le_iff {M : Type*} [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] (n1 n2 : M) (d1 d2 : ℕ+):
    RootableCompletion.mk n1 d1 ≤ RootableCompletion.mk n2 d2 ↔ n1 ^ (d2 : ℕ) ≤ n2 ^ (d1 : ℕ) := by
  rw [RootableCompletion.le_def]
  set n1' := (Quotient.out (mk n1 d1)).num
  set d1' := (Quotient.out (mk n1 d1)).den
  set n2' := (Quotient.out (mk n2 d2)).num
  set d2' := (Quotient.out (mk n2 d2)).den
  rw [← pow_le_pow_iff_left' (by simp : (d1 * d2 : ℕ) ≠ 0) ]
  nth_rw 2 [← pow_le_pow_iff_left' (by simp : (d1' * d2' : ℕ) ≠ 0) ]
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
  rw [(by ring : (d2' * (d1 * d2) : ℕ) = (d1 * (d2 * d2') : ℕ))]
  rw [(by ring : (d1' * (d1 * d2) : ℕ) = (d2 * (d1 * d1') : ℕ))]
  rw [(by ring : (d2 * (d1' * d2') : ℕ) = (d1' * (d2 * d2') : ℕ))]
  rw [(by ring : (d1 * (d1' * d2') : ℕ) = (d2' * (d1 * d1') : ℕ))]
  rw [pow_mul n1', pow_mul n2', pow_mul n1, pow_mul n2]
  have h1 : n1' ^ (d1 : ℕ) = n1 ^ (d1' : ℕ) := by
    apply (RootableCompletion.eq_iff _ _ _ _).mp
    unfold n1' d1'
    apply RootableCompletion.out_eq
  have h2 : n2' ^ (d2 : ℕ) = n2 ^ (d2' : ℕ) := by
    apply (RootableCompletion.eq_iff _ _ _ _).mp
    unfold n2' d2'
    apply RootableCompletion.out_eq
  rw [h1, h2]

@[to_additive]
theorem RootableCompletion.le_iff_right {M : Type*} [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M]
    (n1 n2 : M) (d : ℕ+):
    RootableCompletion.mk n1 d ≤ RootableCompletion.mk n2 d ↔ n1 ≤ n2 := by
  rw [RootableCompletion.le_iff]
  exact pow_le_pow_iff_left' (by simp)

@[to_additive]
noncomputable
instance RootableCompletion.instLinearOrder (M : Type*) [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M]:
    LinearOrder (RootableCompletion M) where
  lt (a b : RootableCompletion M) := a ≤ b ∧ ¬ b ≤ a
  le_refl (a : RootableCompletion M) := by rw [RootableCompletion.le_def]
  le_trans (a b c : RootableCompletion M) := by
    rw [RootableCompletion.le_def, RootableCompletion.le_def, RootableCompletion.le_def]
    intro hab hbc
    obtain hab' := pow_le_pow_left' hab c.out.den
    obtain hbc' := pow_le_pow_left' hbc a.out.den
    rw [← pow_mul, ← pow_mul] at hab'
    nth_rw 1 [mul_comm] at hab'
    nth_rw 2 [mul_comm] at hab'
    rw [pow_mul, pow_mul] at hab'
    nth_rw 2 [← pow_mul] at hbc'
    rw [mul_comm, pow_mul] at hbc'
    obtain hac := hab'.trans hbc'
    exact le_of_pow_le_pow_left' (by simp) hac
  lt_iff_le_not_le (a b : RootableCompletion M) := by rfl
  le_antisymm (a b : RootableCompletion M) := by
    rw [RootableCompletion.le_def, RootableCompletion.le_def]
    intro hab hba
    obtain heq := le_antisymm hab hba
    rw [← RootableCompletion.out_eq a, ← RootableCompletion.out_eq b]
    exact (RootableCompletion.eq_iff _ _ _ _).mpr heq
  le_total (a b : RootableCompletion M) := by
    rw [RootableCompletion.le_def, RootableCompletion.le_def]
    exact le_total (a.out.num ^ (b.out.den : ℕ)) (b.out.num ^ (a.out.den : ℕ))
  toDecidableLE := by exact Classical.decRel LE.le

@[to_additive]
theorem RootableCompletion.max_right {M : Type*} [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M]
    (n1 n2 : M) (d : ℕ+):
    max (RootableCompletion.mk n1 d) (RootableCompletion.mk n2 d) = RootableCompletion.mk (max n1 n2) d := by
  obtain h|h := le_total n1 n2
  · simp only [h, sup_of_le_right, sup_eq_right]
    apply (RootableCompletion.le_iff_right _ _ _).mpr h
  · simp only [h, sup_of_le_left, sup_eq_left]
    apply (RootableCompletion.le_iff_right _ _ _).mpr h

@[to_additive]
noncomputable
instance RootableCompletion.instIsOrderedMonoid (M : Type*) [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M]:
    IsOrderedMonoid (RootableCompletion M) where
  mul_le_mul_left (a b : RootableCompletion M) := by
    rw [RootableCompletion.le_def]
    intro hab c
    rw [← RootableCompletion.out_eq a, ← RootableCompletion.out_eq b,  ← RootableCompletion.out_eq c]
    set A := a.out
    set B := b.out
    set C := c.out
    rw [RootableCompletion.mul_def, RootableCompletion.mul_def]
    rw [RootableCompletion.le_iff]
    simp only [PNat.mul_coe]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
    apply mul_le_mul'
    · rw [mul_comm (C.den : ℕ) (A.den : ℕ), ← mul_assoc, ← mul_assoc, mul_right_comm,
        mul_comm (A.den : ℕ) (B.den : ℕ)]
    · rw [mul_comm (C.den : ℕ) (A.den : ℕ), mul_comm (C.den : ℕ) (B.den : ℕ),
        ← mul_assoc, ← mul_assoc, mul_comm (C.den : ℕ) (A.den : ℕ), mul_comm (C.den : ℕ) (B.den : ℕ),
        mul_assoc, mul_assoc, pow_mul A.num, pow_mul B.num]
      apply pow_le_pow_left' hab

@[to_additive]
theorem RootableCompletion.mk_mabs {M : Type*} [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M]
    (n : M) (d : ℕ+) : |RootableCompletion.mk n d|ₘ = RootableCompletion.mk |n|ₘ d := by
  unfold mabs
  rw [RootableCompletion.inv_def, RootableCompletion.max_right]

@[to_additive]
noncomputable
def RootableCompletion.orderMonoidHom (M : Type*) [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] :
    M →*o RootableCompletion M where
  toFun := (RootableCompletion.mk · 1)
  map_one' := by rw [RootableCompletion.one_def]
  map_mul' (a b) := by
    rw [RootableCompletion.mul_def]
    simp
  monotone' := by
    intro a b hab
    rw [RootableCompletion.le_iff]
    simpa using hab

@[to_additive]
theorem RootableCompletion.orderMonoidHom_injective (M : Type*)
    [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] :
    Function.Injective (RootableCompletion.orderMonoidHom M) := by
  intro a b hab
  obtain h := (RootableCompletion.eq_iff _ _ _ _).mp hab
  simpa using h

end Completion

section archimedean

@[to_additive]
noncomputable
abbrev RootableCompletion.classOrderHom (M : Type*)
    [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] :
    mulArchimedeanClass M →o mulArchimedeanClass (RootableCompletion M) :=
  mulArchimedeanClass.orderHom (RootableCompletion.orderMonoidHom M)

@[to_additive]
theorem RootableCompletion.classOrderHom_injective (M : Type*)
    [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] :
    Function.Injective (RootableCompletion.classOrderHom M) :=
  mulArchimedeanClass.orderHom_injective (RootableCompletion.orderMonoidHom_injective M)

@[to_additive]
theorem RootableCompletion.classOrderHom_surjective (M : Type*)
    [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] :
    Function.Surjective (RootableCompletion.classOrderHom M) := by
  intro a
  use mulArchimedeanClass.mk a.out.out.num
  rw [← mulArchimedeanClass.map_mk]
  unfold orderMonoidHom
  simp only [OrderMonoidHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← mulArchimedeanClass.out_eq a]
  rw [mulArchimedeanClass.eq]
  set A := a.out
  refine ⟨⟨A.out.den, by simp, ?_⟩, ⟨1, by simp, ?_⟩⟩
  · nth_rw 2 [← RootableCompletion.out_eq A]
    rw [RootableCompletion.mk_mabs, RootableCompletion.mk_mabs, RootableCompletion.pow_def]
    rw [RootableCompletion.le_iff]
    simp
  · nth_rw 1 [← RootableCompletion.out_eq A]
    rw [RootableCompletion.mk_mabs, RootableCompletion.mk_mabs, RootableCompletion.pow_def]
    rw [RootableCompletion.le_iff]
    simp only [PNat.val_ofNat, pow_one]
    apply le_self_pow (by simp) (by simp)

@[to_additive]
noncomputable
def RootableCompletion.classIso (M : Type*)
    [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] :
    mulArchimedeanClass M ≃o mulArchimedeanClass (RootableCompletion M) where
  toFun := classOrderHom M
  invFun := Function.surjInv (classOrderHom_surjective M)
  left_inv := by
    apply Function.leftInverse_surjInv
    constructor
    · apply RootableCompletion.classOrderHom_injective
    · apply RootableCompletion.classOrderHom_surjective
  right_inv := Function.rightInverse_surjInv (classOrderHom_surjective M)
  map_rel_iff' := by
    intro a b
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      exact ((OrderHomClass.monotone (classOrderHom M)).strictMono_of_injective
        (classOrderHom_injective M)).le_iff_le.mp h
    · intro h
      exact OrderHomClass.monotone _ h


@[to_additive]
noncomputable
def RootableCompletion.classIso_without_one (M : Type*)
    [CommGroup M] [IsMulTorsionFree M] [LinearOrder M] [IsOrderedMonoid M] :
    {A : mulArchimedeanClass M // A ≠ 1} ≃o {A : mulArchimedeanClass (RootableCompletion M) // A ≠ 1} := {
  Equiv.subtypeEquiv (classIso M) (by
    intro a
    apply Iff.ne
    constructor
    · intro h
      rw [h]
      unfold classIso classOrderHom
      simp
    · intro h
      simp only [EquivLike.coe_coe] at h
      apply_fun classIso M
      rw [h]
      unfold classIso classOrderHom
      simp
  ) with
  map_rel_iff' := by
    intro a b
    rw [Equiv.subtypeEquiv_apply, Equiv.subtypeEquiv_apply]
    simp
}

end archimedean
