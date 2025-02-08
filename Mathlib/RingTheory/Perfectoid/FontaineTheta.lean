/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.RingTheory.Perfectoid.Untilt
import Mathlib.RingTheory.WittVector.Complete

/-!
# Fontaine's θ map
In this file, we define Fontaine's `θ` map, which is a ring
homomorphism from the Witt vector `𝕎(A^♭)` of the tilt of a perfectoid ring `A`
to `A` itself. Our definition of `θ` does not require that `A` is perfectoid in the first place.

## Main definitions
* `fontaineTheta` : Fontaine's θ map, which is a ring homomorphism from `𝕎(A^♭)` to `A`.
* `BDeRhamPlus` : The period ring `B_{dR}^+`.

## Main theorems
* `fontaineTheta_surjective` : Fontaine's θ map is surjective.

## Tags
Fontaine's theta map, period rings, perfectoid theory, p-adic Hodge theory

## TODO
Currently, the period ring `B_{dR}^+` takes the integeral perfectoid ring `O` as the input.
After the perfectoid theory is developed, we should modify it to
take a perfectoid field as the input.
-/


section

-- section
-- -- Mathlib.LinearAlgebra.Quotient.Defs, before Submodule.quotEquivOfEq
-- variable (S T : Ideal R) [S.IsTwoSided] [T.IsTwoSided]

-- /-- The linear map from the quotient by a smaller submodule to the quotient by a larger submodule.

-- This is the `Submodule.Quotient` version of `Quot.factor` -/
-- def factor (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
--   Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

-- @[simp]
-- theorem factor_mk (H : S ≤ T) (x : R) : Ideal.Quotient.factor S T H (mk S x) = mk T x :=
--   rfl

-- @[simp]
-- theorem factor_comp_mk (H : S ≤ T) : (factor S T H).comp (mk S) = mk T := by
--   ext x
--   rw [RingHom.comp_apply, factor_mk]
-- end

#check SModEq.mono

-- RingTheory.AdicCompletion.Basic
theorem IsPrecomplete.exists_of_SModEq_succ {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M]
    {f : ℕ → M} (hf : ∀ {m}, f m ≡ f (m + 1) [SMOD (I ^ m • ⊤ : Submodule R M)]) :
    ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  refine IsPrecomplete.prec' _ ?_
  intro m n h
  have : n = m + (n - m) := (Nat.add_sub_of_le h).symm
  rw [this]
  induction n - m with
  | zero => rfl
  | succ k ih =>
    refine ih.trans (SModEq.mono ?_ hf)
    apply Submodule.smul_mono_left (Ideal.pow_le_pow_right _)
    simp only [le_add_iff_nonneg_right, zero_le]

theorem IsPrecomplete.prec_function {α R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M]
    {f : ℕ → α → M} (hf : ∀ {m n a}, m ≤ n → f m a ≡ f n a [SMOD (I ^ m • ⊤ : Submodule R M)]) :
    ∃ F : α → M, ∀ n a, f n a ≡ F a [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun a ↦ Classical.choose <| IsPrecomplete.prec' _ (hf (a := a)),
    fun n a => (Classical.choose_spec <| IsPrecomplete.prec' _ (hf (a := a))) n⟩

theorem IsPrecomplete.exists_function' {α R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M] {f : ℕ → α → M}  (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) : ∃ F : α → M, ∀ n, ∃ L, ∀ m : α, I^n ∣ F m - L := sorry

def IsAdicComplete.limAddHom

def IsAdicComplete.limRingHom

end

open Ideal PreTilt
noncomputable section

variable {O : Type*} [CommRing O]
  {p : ℕ} [Fact (Nat.Prime p)] [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

local notation A "^♭" => PreTilt A p
local notation "♯" x => PreTilt.untilt x
local notation "𝕎" => WittVector p

/-!
## the underlying function of θ
In this section, we define the underlying function of `θ`.

* `fontaineThetaAux n` is the sum of the first `n`-terms of the summation used in `θ`.
* `fontaineThetaFun` is the p-adic limit of the sequence `fontaineThetaAux`.
-/
section Function

def fontaineThetaAux (x : 𝕎 (O^♭)) (n : ℕ) : O :=
  ∑ (i ≤ n), p^i * ♯ ((frobeniusEquiv _ p).symm^[n] (x.coeff n))

lemma pow_dvd_fontaineThetaAux_sub (x : 𝕎 (O^♭)) {m n : ℕ} (h : m ≤ n) :
  (p : O) ^ m ∣ fontaineThetaAux x m - fontaineThetaAux x n := by
  sorry

lemma exists_pow_dvd_fontaineThetaAux_sub (x : 𝕎 (O^♭)) :
    ∃ L, ∀ (n : ℕ), (p : O) ^ n ∣ fontaineThetaAux x n - L :=
  IsPrecomplete.exists_pow_dvd inferInstance (pow_dvd_fontaineThetaAux_sub x)

def fontaineThetaFun (x : 𝕎 (O^♭)) : O :=
  Classical.choose <| exists_pow_dvd_fontaineThetaAux_sub x

lemma pow_dvd_fontaineThetaAux_sub_fontaineThetaFun (x : 𝕎 (O^♭)) (n : ℕ) :
  (p : O) ^ n ∣ fontaineThetaAux x n - fontaineThetaFun x :=
  (Classical.choose_spec <| exists_pow_dvd_fontaineThetaAux_sub x) n

end Function

/-!
## θ is a ring homomorphism
In this section, we show that `fontaineThetaFun` is actually a
ring homomorphism, and define the ring homomorphism `fontaineTheta`.

To prove this, we prove that `fontaineThetaFun` mod `p^n` is a ring homomorphism by
decompose it as a composition of several ring homomorphisms as below.
`𝕎(O^♭) --𝕎(Frob^-n)->  𝕎(O^♭) --𝕎(coeff 0)-> 𝕎(O/p) --gh_n-> O/p^(n+1)`
Here, the ring map `gh_n` fits in the following diagram.

```
𝕎(A)--ghost_n-> A
↓                ↓
𝕎(A/p) --gh_n->A/p^(n+1)
```

-/
section RingHom

def ghostMapModP (n : ℕ): 𝕎 (O ⧸ span {(p : O)}) →+* O ⧸ span {(p : O)}^(n + 1) := sorry
-- Quotient.lift

def fontaineThetaModP (n : ℕ): 𝕎 (O^♭) →+* O ⧸ span {(p : O)}^(n + 1) := sorry

theorem fontaineThetaModP_eq_fontainThetaFun_mod_p (x : 𝕎 (O^♭)) (n : ℕ) :
  fontaineThetaModP n x = fontaineThetaAux x n := sorry

def fontaineTheta : 𝕎 (O^♭) →+* O where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

end RingHom

theorem fontaineTheta_surjective : Function.Surjective (fontaineTheta : 𝕎 (O^♭) → O) := sorry


section PeriodRing

def BDeRhamPlus (O : Type*) [CommRing O] [Fact (Nat.Prime p)]
  [Fact ¬IsUnit (p : O)] : Type* := sorry

notation "𝔹_dR(" O ")" => BDeRhamPlus O

end PeriodRing

end
