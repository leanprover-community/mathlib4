/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Galois theory for cyclotomic fields

In this file, we study the Galois theory of cyclotomic extensions of `ℚ`.

## Main definitions and results

- `IsCyclotomicExtension.Rat.galEquivZMod`: the isomorphism between `Gal(ℚ(ζₙ)/ℚ)` and `(ℤ/nℤ)ˣ`
  that sends `σ` to the class `a` such that `σ (ζₙ) = ζₙ ^ a`.
- `IsCyclotomicExtension.Rat.isInertiaField`: if `n = p ^ k * m` with `p` prime and `¬ p ∣ m`, then
  `ℚ(ζₘ)` is the inertia field of any prime of `𝓞(ℚ(ζₙ))` lying over `p`.

-/

@[expose] public section

namespace IsCyclotomicExtension.Rat

open NumberField IsCyclotomicExtension

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {n} ℚ K]

include hK in
/--
The isomorphism between `Gal(ℚ(ζₙ)/ℚ)` and `(ℤ/nℤ)ˣ` that sends `σ` to the class `a` such that
`σ (ζₙ) = ζₙ ^ a`.
-/
noncomputable abbrev galEquivZMod : Gal(K/ℚ) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.autEquivPow K <| Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)

theorem galEquivZMod_apply_of_pow_eq (σ : Gal(K/ℚ)) {x : K} (hx : x ^ n = 1) :
    σ x = x ^ (galEquivZMod n K σ).val.val := by
  obtain ⟨a, -, rfl⟩ := (zeta_spec n ℚ K).eq_pow_of_pow_eq_one hx
  rw [map_pow, pow_right_comm, galEquivZMod, autEquivPow_apply, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, IsPrimitiveRoot.autToPow_spec]

set_option backward.isDefEq.respectTransparency false in
theorem galEquivZMod_smul_of_pow_eq (σ : Gal(K/ℚ)) {x : 𝓞 K} (hx : x ^ n = 1) :
    σ • x = x ^ (galEquivZMod n K σ).val.val := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  apply galEquivZMod_apply_of_pow_eq n K σ <| by rw [← Subalgebra.coe_pow, hx, OneMemClass.coe_one]

section restrict

variable {m : ℕ} [NeZero m] (F : Type*) [Field F] [NumberField F]
  [hF : IsCyclotomicExtension {m} ℚ F] [Algebra F K] [IsGalois ℚ F]

/--
Let `m ∣ n`. Then, the following diagram commutes:
Gal(ℚ(ζₙ)/ℚ) → (ℤ/nℤ)ˣ
  ↓              ↓
Gal(ℚ(ζₘ)/ℚ) → (ℤ/mℤ)ˣ
where the horizontal maps are `galEquivZMod`, the left map is the restriction map and the right map
is the natural map.
-/
theorem galEquivZMod_restrictNormal_apply (h : m ∣ n) (σ : Gal(K/ℚ)) :
    galEquivZMod m F (σ.restrictNormal F) = ZMod.unitsMap h (galEquivZMod n K σ) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ F
  let ζ := IsCyclotomicExtension.zeta m ℚ F
  suffices ζ ^ (galEquivZMod m F (σ.restrictNormal F)).val.val = ζ ^ (galEquivZMod n K σ).val.val by
    rw [(hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id] at this
    rwa [Units.ext_iff]
  apply FaithfulSMul.algebraMap_injective F K
  rw [map_pow, map_pow, ← galEquivZMod_apply_of_pow_eq, ← AlgEquiv.restrictNormal_commutes,
      galEquivZMod_apply_of_pow_eq m _ _ hζ.pow_eq_one, map_pow]
  rw [← map_pow, (hζ.pow_eq_one_iff_dvd _).mpr h, map_one]

end restrict

open Ideal

set_option backward.isDefEq.respectTransparency false in
/--
Let `K = ℚ(ζₙ)` with `n = p ^ k * m` where `p` is prime and `¬ p ∣ m`. Then the subfield
`F = ℚ(ζₘ)` is the inertia field of any prime `P` of `𝓞 K` lying over `p`.
-/
theorem isInertiaField (m p k : ℕ) (hn : n = p ^ k * m) [hp : Fact (p.Prime)] (hm : ¬ p ∣ m)
    (F : IntermediateField ℚ K) [hF : IsCyclotomicExtension {m} ℚ F] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (span {(p : ℤ)})] :
    IsInertiaField ℚ K P F := by
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  have hp' : span {(p : ℤ)} ≠ ⊥ := by simpa using hp.out.ne_zero
  have : IsGalois ℚ K := isGalois {n} ℚ K
  let 𝓟F : Ideal (𝓞 F) := comap (algebraMap (𝓞 F) (𝓞 K)) P
  have : P.LiesOver 𝓟F := over_under P
  have : 𝓟F.IsPrime := IsPrime.under (𝓞 F) P
  have : 𝓟F.LiesOver (span {(p : ℤ)}) := under_liesOver_of_liesOver (𝓞 F) P (span {(p : ℤ)})
  have hPF : 𝓟F ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp' _
  have h := ramificationIdx_eq_of_not_dvd p F 𝓟F hm
  refine (IntermediateField.isInertiaField_iff ℤ ℚ K P F (𝓞 F) 𝓟F hp').mpr ⟨?_, h⟩
  obtain rfl | hk := Nat.eq_zero_or_eq_succ_pred k
  · have : F = ⊤ := by
      convert IntermediateField.isCyclotomicExtension_eq {n} ℚ K _ _
      · rwa [hn, pow_zero, one_mul]
      · exact IsCyclotomicExtension.equiv {n} ℚ K IntermediateField.topEquiv.symm
    refine Nat.le_antisymm (ramificationIdx_le_finrank F K 𝓟F P) ?_
    rw [IntermediateField.finrank_eq_one_iff_eq_top.mpr this]
    exact Nat.one_le_iff_ne_zero.mpr <|
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hPF
  rw [hk] at hn
  suffices Module.finrank F K = p ^ k.pred * (p - 1) by
    have h' := ramificationIdx_algebra_tower' (span {(p : ℤ)}) 𝓟F P
    rwa [h, one_mul, ramificationIdx_eq n K P hn hm, ← this, eq_comm] at h'
  rw [← mul_right_inj' ((Module.finrank_pos (R := ℚ) (M := F)).ne'),
    Module.finrank_mul_finrank ℚ F K, finrank n, finrank m, hn, Nat.totient_mul,
    Nat.totient_prime_pow_succ hp.out, mul_comm]
  exact Nat.Coprime.pow_left k.pred.succ <| by rwa [hp.out.coprime_iff_not_dvd]

end IsCyclotomicExtension.Rat
