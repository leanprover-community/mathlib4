/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/

import Mathlib.RingTheory.Perfectoid.Untilt
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.LinearAlgebra.Quotient.Defs

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
-- variable {R M: Type*} [Ring R] [AddCommGroup M] [Module R M]
--     (p q : Submodule R M)

-- /-- The linear map from the quotient by a smaller submodule to the quotient by a larger submodule.

-- This is the `Submodule.Quotient` version of `Quot.factor` -/
-- def factor (H : p ≤ q) : M ⧸ p →ₗ[R] M ⧸ q :=
--   Submodule.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

-- @[simp]
-- theorem factor_mk (H : S ≤ T) (x : R) : Ideal.Quotient.factor S T H (mk S x) = mk T x :=
--   rfl

-- @[simp]
-- theorem factor_comp_mk (H : S ≤ T) : (factor S T H).comp (mk S) = mk T := by
--   ext x
--   rw [RingHom.comp_apply, factor_mk]
-- end

-- -- SModEq
-- theorem SModEq.mkQ_eq_mkQ {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
--     {U : Submodule R M} {x y : M} : x ≡ y [SMOD U] ↔ U.mkQ x = U.mkQ y := by
--   simp only [SModEq.def, Submodule.mkQ_apply]

@[simp]
theorem Submodule.Quotient.mk_out {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {U : Submodule R M} (x : M ⧸ U) : Submodule.Quotient.mk (x.out) = x :=
  Quotient.out_eq x

-- RingTheory.AdicCompletion.Basic
theorem IsPrecomplete.of_SModEq_succ {R : Type*} [CommRing R] {I : Ideal R}
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

-- may not add
theorem IsPrecomplete.function_prec {α R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M]
    {f : ℕ → α → M} (hf : ∀ {m n a}, m ≤ n → f m a ≡ f n a [SMOD (I ^ m • ⊤ : Submodule R M)]) :
    ∃ F : α → M, ∀ n a, f n a ≡ F a [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun a ↦ Classical.choose <| IsPrecomplete.prec' _ (hf (a := a)),
    fun n a => (Classical.choose_spec <| IsPrecomplete.prec' _ (hf (a := a))) n⟩

-- may not add
theorem IsPrecomplete.function_of_SModEq_succ {α R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M]
    {f : ℕ → α → M} (hf : ∀ {m a}, f m a ≡ f (m + 1) a [SMOD (I ^ m • ⊤ : Submodule R M)]) :
    ∃ F : α → M, ∀ n a, f n a ≡ F a [SMOD (I ^ n • ⊤ : Submodule R M)] :=
    ⟨fun a ↦ Classical.choose <| IsPrecomplete.of_SModEq_succ (hf (a := a)),
    fun n a => (Classical.choose_spec <| IsPrecomplete.of_SModEq_succ (hf (a := a))) n⟩

-- useful in AdicComplete case
def Submodule.mapQPowSucc {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ) :
    M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) :=
  mapQ _ _ LinearMap.id (comap_id (I ^ n • ⊤ : Submodule R M) ▸
      Submodule.smul_mono_left (Ideal.pow_le_pow_right n.le_succ))

@[simp]
theorem Submodule.mapQPowSucc_mk {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ) (x : M) :
    Submodule.mapQPowSucc n (Submodule.Quotient.mk x) =
    (Submodule.Quotient.mk x : M ⧸ I ^ n • ⊤) := by
  simp [Submodule.mapQPowSucc]

@[simp]
theorem Submodule.mk_out_eq_mapQPowSucc {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] (n : ℕ) (x : M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M)) :
    Submodule.Quotient.mk x.out = Submodule.mapQPowSucc n x := by
  nth_rw 2 [← Submodule.Quotient.mk_out x]
  simp only [mapQPowSucc_mk]

def Ideal.Quotient.factorPowSucc {R : Type*} [CommRing R] {I : Ideal R} (n : ℕ) :
    R ⧸ I ^ (n + 1) →+* R ⧸ I ^ n :=
  Ideal.Quotient.factor _ _ (Ideal.pow_le_pow_right n.le_succ)

@[simp]
theorem Ideal.Quotient.factorPowSucc_mk {R : Type*} [CommRing R] {I : Ideal R} (n : ℕ) (x : R) :
    Ideal.Quotient.factorPowSucc n (Ideal.Quotient.mk (I ^ (n + 1)) x) =
    Ideal.Quotient.mk (I ^ n) x := by
  simp [Ideal.Quotient.factorPowSucc]

@[simp]
theorem Ideal.Quotient.mk_out_eq_mapQPowSucc {R : Type*} [CommRing R] {I : Ideal R} (n : ℕ)
    (x : R ⧸ I ^ (n + 1)) : Ideal.Quotient.mk (I ^ n) x.out = Ideal.Quotient.factorPowSucc n x := by
  nth_rw 2 [← Ideal.Quotient.mk_out x]
  simp only [Ideal.Quotient.factorPowSucc_mk]

open Submodule Ideal Quotient

theorem IsPrecomplete.of_eq_mapQPowSucc {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M]
    {f : (n : ℕ) → M ⧸ (I ^ n • ⊤)} (hf : ∀ {m}, f m = mapQPowSucc m (f (m + 1))) :
    ∃ L : M, ∀ n, f n = mkQ _ L := by
  let f' := fun n => (f n).out
  have hf' : ∀ {m : ℕ}, f' m ≡ f' (m + 1) [SMOD (I ^ m • ⊤ : Submodule R M)] := by
    intro m
    rw [SModEq]
    simpa [f'] using hf
  refine ⟨Classical.choose <| of_SModEq_succ (I := I) (f := f') hf', ?_⟩
  simpa [SModEq, f'] using (Classical.choose_spec <| of_SModEq_succ (I := I) (f := f') hf')

-- may not add
theorem IsPrecomplete.function_of_eq_mapQPowSucc {α R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsPrecomplete I M]
    {f : (n : ℕ) → α → M ⧸ (I ^ n • ⊤)}
    (hf : ∀ {m a}, f m a = Submodule.mapQPowSucc m (f (m + 1) a)) :
    ∃ F : α → M, ∀ n a, f n a = mkQ (I ^ n • ⊤) (F a) :=
    ⟨fun a ↦ Classical.choose <| IsPrecomplete.of_eq_mapQPowSucc (hf (a := a)),
    fun n a => (Classical.choose_spec <| IsPrecomplete.of_eq_mapQPowSucc (hf (a := a))) n⟩

theorem IsHausdorff.eq_of_SModEq {R : Type*} [CommRing R] {I : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M] [IsHausdorff I M]
    {x y : M} (h : ∀ n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]) : x = y := by
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I)
  exact fun n ↦ sub_smodEq_zero.mp (h n)

theorem IsHausdorff.map_add {R : Type*} [CommRing R] {I : Ideal R}
    {N M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [IsHausdorff I M]
    {f : (n : ℕ) → N → M ⧸ (I ^ n • ⊤)} (hf : ∀ (n x y), f n (x + y) = f n x + f n y) {F : N → M}
    (hF : ∀ (n x), f n x = mkQ (I^n • ⊤ : Submodule R M) (F x)) (x y : N) :
    F (x + y) = F x + F y := by
  refine eq_of_SModEq (I := I) (fun n ↦ ?_)
  simp only [mkQ_apply] at hF
  simp only [SModEq, ← hF, mk_add]
  exact hf _ _ _

noncomputable
def IsAdicComplete.limAddHom {R : Type*} [CommRing R] {I : Ideal R}
    {N M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [IsAdicComplete I M]
    {f : (n : ℕ) → N →ₗ[R] M ⧸ (I ^ n • ⊤)}
    (hf : ∀ {m a}, f m a = mapQPowSucc m (f (m + 1) a)) :
    N →ₗ[R] M where
      toFun := Classical.choose <|
        IsPrecomplete.function_of_eq_mapQPowSucc (I := I) (f := fun n ↦ f n) hf
      map_add' := IsHausdorff.map_add (fun n ↦ (f n).map_add') <|
        Classical.choose_spec <|
          IsPrecomplete.function_of_eq_mapQPowSucc (I := I) (f := fun n ↦ f n) hf
      map_smul' := sorry

theorem IsAdicComplete.eq_mkQ_limAddHom {R : Type*} [CommRing R] {I : Ideal R}
    {N M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [IsAdicComplete I M]
    {f : (n : ℕ) → N →ₗ[R] M ⧸ (I ^ n • ⊤)}
    (hf : ∀ {m a}, f m a = mapQPowSucc m (f (m + 1) a))
    (n a) : f n a = (mkQ (I^n • ⊤ : Submodule R M) (limAddHom hf a)) :=
  (Classical.choose_spec <|
    IsPrecomplete.function_of_eq_mapQPowSucc (I := I) (f := fun n ↦ f n) hf) n a

theorem IsAdicComplete.eq_mkQ_comp_limAddHom {R : Type*} [CommRing R] {I : Ideal R}
    {N M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup M] [Module R M] [IsAdicComplete I M]
    {f : (n : ℕ) → N →ₗ[R] M ⧸ (I ^ n • ⊤)}
    (hf : ∀ {m a}, f m a = mapQPowSucc m (f (m + 1) a))
    (n) : f n = (mkQ (I^n • ⊤ : Submodule R M)).comp (limAddHom hf) :=
  LinearMap.ext (IsAdicComplete.eq_mkQ_limAddHom hf n)

noncomputable
def IsAdicComplete.limRingHom
    {R S: Type*} [CommRing R] [Ring S] {I : Ideal R}
    [IsAdicComplete I R]
    {f : (n : ℕ) → S →+* R ⧸ I ^ n}
    (hf : ∀ {m a}, f m a = factorPowSucc m (f (m + 1) a)) :
    S →+* R where
      toFun := sorry
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry

theorem IsAdicComplete.eq_mk_limRingHom {R S: Type*} [CommRing R] [Ring S] {I : Ideal R}
    [IsAdicComplete I R]
    {f : (n : ℕ) → S →+* R ⧸ I ^ n}
    (hf : ∀ {m a}, f m a = factorPowSucc m (f (m + 1) a))
    (n a) : f n a = Ideal.Quotient.mk (I^n) (limRingHom hf a) := sorry

theorem IsAdicComplete.eq_mk_comp_limRingHom {R S: Type*} [CommRing R] [Ring S] {I : Ideal R}
    [IsAdicComplete I R]
    {f : (n : ℕ) → S →+* R ⧸ I ^ n}
    (hf : ∀ {m a}, f m a = factorPowSucc m (f (m + 1) a))
    (n) : f n = (Ideal.Quotient.mk (I^n)).comp (limRingHom hf) :=
  RingHom.ext (IsAdicComplete.eq_mk_limRingHom hf n)

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
