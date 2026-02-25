/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Galois theory for cyclotomic fields

In this file, we study the Galois theory of cyclotomic extensions of `ℚ`.

## Main definitions and results

- `IsCyclotomicExtension.Rat.galEquivZMod`: the isomorphism between `Gal(ℚ(ζₙ)/ℚ)` and `(ℤ/nℤ)ˣ`
  that sends `σ` to the class `a` such that `σ (ζₙ) = ζₙ ^ a`.

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

section stabilizer

open Pointwise MulAction Ideal

variable (p : ℕ) [hp : Fact (Nat.Prime p)] (P : Ideal (𝓞 K)) [hP₁ : P.IsMaximal]
    [hP₂ : P.LiesOver (Ideal.span {(p : ℤ)})] (hn : p.Coprime n)

attribute [local instance] Ideal.Quotient.field

theorem galEquivZMod_mem_zpowers_of_mem_stabilizer {σ : Gal(K/ℚ)} (hσ : σ ∈ stabilizer Gal(K/ℚ) P) :
    galEquivZMod n K σ ∈ Subgroup.zpowers (ZMod.unitOfCoprime p hn) := by
  let 𝕜 := (𝓞 K) ⧸ P
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ K
  let τ := IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(p : ℤ)}) P
     (ℤ ⧸ span {(p : ℤ)}) 𝕜 ⟨σ, hσ⟩
  have : CharP (ℤ ⧸ span {(p : ℤ)}) p := sorry
  have : Finite 𝕜 := sorry -- use HasFiniteQuotients !
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ℤ ⧸ span {(p : ℤ)}) p 𝕜 τ
  sorry

#exit

  have hζ := IsCyclotomicExtension.zeta_spec m ℚ K
  let 𝕜 := (𝓞 K) ⧸ P
  let τ := IsFractionRing.stabilizerHom Gal(K/ℚ) (Ideal.span {(p : ℤ)}) P
     (ℤ ⧸ span {(p : ℤ)}) 𝕜 ⟨σ, hσ⟩
  obtain ⟨i, hi⟩ := toto (ℤ ⧸ span {(p : ℤ)}) p 𝕜 τ
  refine ⟨i, ?_⟩
  dsimp only
  have t₁ := hi (Ideal.Quotient.mk P hζ.toInteger)
  simp only [τ] at t₁
  have t₂ := IsFractionRing.stabilizerHom_apply_apply_mk Gal(K/ℚ) (Ideal.span {(p : ℤ)}) P
    (ℤ ⧸ span {(p : ℤ)}) 𝕜 ⟨σ, hσ⟩ hζ.toInteger
  simp only [Algebra.algebraMap_self, RingHomCompTriple.comp_apply, 𝕜] at t₂
  have t₃ := hζ.toInteger_isPrimitiveRoot.idealQuotient_mk (I := P) ?_ ?_
  · rw [t₂] at t₁
    rw [galEquiv_smul_of_pow_eq m, map_pow, IsOfFinOrder.pow_inj_mod] at t₁
    · rw [zpow_natCast]
      rw [Units.ext_iff]
      simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
      rw [← t₃.eq_orderOf] at t₁
      rw [Int.card_ideal_quot] at t₁
      rw [← ZMod.natCast_eq_natCast_iff'] at t₁
      simp at t₁
      exact t₁.symm
    · apply IsPrimitiveRoot.isOfFinOrder t₃
    · exact hζ.toInteger_isPrimitiveRoot.pow_eq_one
  · rw [Ne.eq_def, absNorm_eq_one_iff]
    exact IsPrime.ne_top'
  · rw [Ideal.absNorm_eq_pow_inertiaDeg' _ hp.out]
    apply Nat.Coprime.pow_left
    exact hm

end stabilizer

end IsCyclotomicExtension.Rat
