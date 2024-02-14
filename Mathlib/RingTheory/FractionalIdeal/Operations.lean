/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.IntegralClosure
import Mathlib.RingTheory.FractionalIdeal.Basic

#align_import ring_theory.fractional_ideal from "leanprover-community/mathlib"@"ed90a7d327c3a5caf65a6faf7e8a0d63c4605df7"

/-!
# More operations on fractional ideals

## Main definitions
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R⁰ = R \ {0}` (i.e. the field of fractions).
 * `FractionalIdeal R⁰ K` is the type of fractional ideals in the field of fractions
 * `Div (FractionalIdeal R⁰ K)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statement

  * `isNoetherian` states that every fractional ideal of a noetherian integral domain is noetherian

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/


open IsLocalization Pointwise nonZeroDivisors

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P] [loc : IsLocalization S P]

section

variable {P' : Type*} [CommRing P'] [Algebra R P'] [loc' : IsLocalization S P']

variable {P'' : Type*} [CommRing P''] [Algebra R P''] [loc'' : IsLocalization S P'']

theorem _root_.IsFractional.map (g : P →ₐ[R] P') {I : Submodule R P} :
    IsFractional S I → IsFractional S (Submodule.map g.toLinearMap I)
  | ⟨a, a_nonzero, hI⟩ =>
    ⟨a, a_nonzero, fun b hb => by
      obtain ⟨b', b'_mem, hb'⟩ := Submodule.mem_map.mp hb
      rw [AlgHom.toLinearMap_apply] at hb'
      obtain ⟨x, hx⟩ := hI b' b'_mem
      use x
      rw [← g.commutes, hx, g.map_smul, hb']⟩
#align is_fractional.map IsFractional.map

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map (g : P →ₐ[R] P') : FractionalIdeal S P → FractionalIdeal S P' := fun I =>
  ⟨Submodule.map g.toLinearMap I, I.isFractional.map g⟩
#align fractional_ideal.map FractionalIdeal.map

@[simp, norm_cast]
theorem coe_map (g : P →ₐ[R] P') (I : FractionalIdeal S P) :
    ↑(map g I) = Submodule.map g.toLinearMap I :=
  rfl
#align fractional_ideal.coe_map FractionalIdeal.coe_map

@[simp]
theorem mem_map {I : FractionalIdeal S P} {g : P →ₐ[R] P'} {y : P'} :
    y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
  Submodule.mem_map
#align fractional_ideal.mem_map FractionalIdeal.mem_map

variable (I J : FractionalIdeal S P) (g : P →ₐ[R] P')

@[simp]
theorem map_id : I.map (AlgHom.id _ _) = I :=
  coeToSubmodule_injective (Submodule.map_id (I : Submodule R P))
#align fractional_ideal.map_id FractionalIdeal.map_id

@[simp]
theorem map_comp (g' : P' →ₐ[R] P'') : I.map (g'.comp g) = (I.map g).map g' :=
  coeToSubmodule_injective (Submodule.map_comp g.toLinearMap g'.toLinearMap I)
#align fractional_ideal.map_comp FractionalIdeal.map_comp

@[simp, norm_cast]
theorem map_coeIdeal (I : Ideal R) : (I : FractionalIdeal S P).map g = I := by
  ext x
  simp only [mem_coeIdeal]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (g.commutes y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, g.commutes y⟩
#align fractional_ideal.map_coe_ideal FractionalIdeal.map_coeIdeal

@[simp]
theorem map_one : (1 : FractionalIdeal S P).map g = 1 :=
  map_coeIdeal g ⊤
#align fractional_ideal.map_one FractionalIdeal.map_one

@[simp]
theorem map_zero : (0 : FractionalIdeal S P).map g = 0 :=
  map_coeIdeal g 0
#align fractional_ideal.map_zero FractionalIdeal.map_zero

@[simp]
theorem map_add : (I + J).map g = I.map g + J.map g :=
  coeToSubmodule_injective (Submodule.map_sup _ _ _)
#align fractional_ideal.map_add FractionalIdeal.map_add

@[simp]
theorem map_mul : (I * J).map g = I.map g * J.map g := by
  simp only [mul_def]
  exact coeToSubmodule_injective (Submodule.map_mul _ _ _)
#align fractional_ideal.map_mul FractionalIdeal.map_mul

@[simp]
theorem map_map_symm (g : P ≃ₐ[R] P') : (I.map (g : P →ₐ[R] P')).map (g.symm : P' →ₐ[R] P) = I := by
  rw [← map_comp, g.symm_comp, map_id]
#align fractional_ideal.map_map_symm FractionalIdeal.map_map_symm

@[simp]
theorem map_symm_map (I : FractionalIdeal S P') (g : P ≃ₐ[R] P') :
    (I.map (g.symm : P' →ₐ[R] P)).map (g : P →ₐ[R] P') = I := by
  rw [← map_comp, g.comp_symm, map_id]
#align fractional_ideal.map_symm_map FractionalIdeal.map_symm_map

theorem map_mem_map {f : P →ₐ[R] P'} (h : Function.Injective f) {x : P} {I : FractionalIdeal S P} :
    f x ∈ map f I ↔ x ∈ I :=
  mem_map.trans ⟨fun ⟨_, hx', x'_eq⟩ => h x'_eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩
#align fractional_ideal.map_mem_map FractionalIdeal.map_mem_map

theorem map_injective (f : P →ₐ[R] P') (h : Function.Injective f) :
    Function.Injective (map f : FractionalIdeal S P → FractionalIdeal S P') := fun _ _ hIJ =>
  ext fun _ => (map_mem_map h).symm.trans (hIJ.symm ▸ map_mem_map h)
#align fractional_ideal.map_injective FractionalIdeal.map_injective

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def mapEquiv (g : P ≃ₐ[R] P') : FractionalIdeal S P ≃+* FractionalIdeal S P' where
  toFun := map g
  invFun := map g.symm
  map_add' I J := map_add I J _
  map_mul' I J := map_mul I J _
  left_inv I := by rw [← map_comp, AlgEquiv.symm_comp, map_id]
  right_inv I := by rw [← map_comp, AlgEquiv.comp_symm, map_id]
#align fractional_ideal.map_equiv FractionalIdeal.mapEquiv

@[simp]
theorem coeFun_mapEquiv (g : P ≃ₐ[R] P') :
    (mapEquiv g : FractionalIdeal S P → FractionalIdeal S P') = map g :=
  rfl
#align fractional_ideal.coe_fun_map_equiv FractionalIdeal.coeFun_mapEquiv

@[simp]
theorem mapEquiv_apply (g : P ≃ₐ[R] P') (I : FractionalIdeal S P) : mapEquiv g I = map (↑g) I :=
  rfl
#align fractional_ideal.map_equiv_apply FractionalIdeal.mapEquiv_apply

@[simp]
theorem mapEquiv_symm (g : P ≃ₐ[R] P') :
    ((mapEquiv g).symm : FractionalIdeal S P' ≃+* _) = mapEquiv g.symm :=
  rfl
#align fractional_ideal.map_equiv_symm FractionalIdeal.mapEquiv_symm

@[simp]
theorem mapEquiv_refl : mapEquiv AlgEquiv.refl = RingEquiv.refl (FractionalIdeal S P) :=
  RingEquiv.ext fun x => by simp
#align fractional_ideal.map_equiv_refl FractionalIdeal.mapEquiv_refl

theorem isFractional_span_iff {s : Set P} :
    IsFractional S (span R s) ↔ ∃ a ∈ S, ∀ b : P, b ∈ s → IsInteger R (a • b) :=
  ⟨fun ⟨a, a_mem, h⟩ => ⟨a, a_mem, fun b hb => h b (subset_span hb)⟩, fun ⟨a, a_mem, h⟩ =>
    ⟨a, a_mem, fun b hb =>
      span_induction hb h
        (by
          rw [smul_zero]
          exact isInteger_zero)
        (fun x y hx hy => by
          rw [smul_add]
          exact isInteger_add hx hy)
        fun s x hx => by
        rw [smul_comm]
        exact isInteger_smul hx⟩⟩
#align fractional_ideal.is_fractional_span_iff FractionalIdeal.isFractional_span_iff

theorem isFractional_of_fg {I : Submodule R P} (hI : I.FG) : IsFractional S I := by
  rcases hI with ⟨I, rfl⟩
  rcases exist_integer_multiples_of_finset S I with ⟨⟨s, hs1⟩, hs⟩
  rw [isFractional_span_iff]
  exact ⟨s, hs1, hs⟩
#align fractional_ideal.is_fractional_of_fg FractionalIdeal.isFractional_of_fg

theorem mem_span_mul_finite_of_mem_mul {I J : FractionalIdeal S P} {x : P} (hx : x ∈ I * J) :
    ∃ T T' : Finset P, (T : Set P) ⊆ I ∧ (T' : Set P) ⊆ J ∧ x ∈ span R (T * T' : Set P) :=
  Submodule.mem_span_mul_finite_of_mem_mul (by simpa using mem_coe.mpr hx)
#align fractional_ideal.mem_span_mul_finite_of_mem_mul FractionalIdeal.mem_span_mul_finite_of_mem_mul

variable (S)

theorem coeIdeal_fg (inj : Function.Injective (algebraMap R P)) (I : Ideal R) :
    FG ((I : FractionalIdeal S P) : Submodule R P) ↔ I.FG :=
  coeSubmodule_fg _ inj _
#align fractional_ideal.coe_ideal_fg FractionalIdeal.coeIdeal_fg

variable {S}

theorem fg_unit (I : (FractionalIdeal S P)ˣ) : FG (I : Submodule R P) :=
  Submodule.fg_unit <| Units.map (coeSubmoduleHom S P).toMonoidHom I
#align fractional_ideal.fg_unit FractionalIdeal.fg_unit

theorem fg_of_isUnit (I : FractionalIdeal S P) (h : IsUnit I) : FG (I : Submodule R P) :=
  fg_unit h.unit
#align fractional_ideal.fg_of_is_unit FractionalIdeal.fg_of_isUnit

theorem _root_.Ideal.fg_of_isUnit (inj : Function.Injective (algebraMap R P)) (I : Ideal R)
    (h : IsUnit (I : FractionalIdeal S P)) : I.FG := by
  rw [← coeIdeal_fg S inj I]
  exact FractionalIdeal.fg_of_isUnit I h
#align ideal.fg_of_is_unit Ideal.fg_of_isUnit

variable (S P P')

/-- `canonicalEquiv f f'` is the canonical equivalence between the fractional
ideals in `P` and in `P'`, which are both localizations of `R` at `S`. -/
noncomputable irreducible_def canonicalEquiv : FractionalIdeal S P ≃+* FractionalIdeal S P' :=
  mapEquiv
    { ringEquivOfRingEquiv P P' (RingEquiv.refl R)
        (show S.map _ = S by rw [RingEquiv.toMonoidHom_refl, Submonoid.map_id]) with
      commutes' := fun r => ringEquivOfRingEquiv_eq _ _ }
#align fractional_ideal.canonical_equiv FractionalIdeal.canonicalEquiv

@[simp]
theorem mem_canonicalEquiv_apply {I : FractionalIdeal S P} {x : P'} :
    x ∈ canonicalEquiv S P P' I ↔
      ∃ y ∈ I,
        IsLocalization.map P' (RingHom.id R) (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy)
            (y : P) =
          x := by
  rw [canonicalEquiv, mapEquiv_apply, mem_map]
  exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩
#align fractional_ideal.mem_canonical_equiv_apply FractionalIdeal.mem_canonicalEquiv_apply

@[simp]
theorem canonicalEquiv_symm : (canonicalEquiv S P P').symm = canonicalEquiv S P' P :=
  RingEquiv.ext fun I =>
    SetLike.ext_iff.mpr fun x => by
      rw [mem_canonicalEquiv_apply, canonicalEquiv, mapEquiv_symm, mapEquiv_apply,
        mem_map]
      exact ⟨fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩, fun ⟨y, mem, Eq⟩ => ⟨y, mem, Eq⟩⟩
#align fractional_ideal.canonical_equiv_symm FractionalIdeal.canonicalEquiv_symm

theorem canonicalEquiv_flip (I) : canonicalEquiv S P P' (canonicalEquiv S P' P I) = I := by
  rw [← canonicalEquiv_symm]; erw [RingEquiv.apply_symm_apply]
#align fractional_ideal.canonical_equiv_flip FractionalIdeal.canonicalEquiv_flip

@[simp]
theorem canonicalEquiv_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] (I : FractionalIdeal S P) :
    canonicalEquiv S P' P'' (canonicalEquiv S P P' I) = canonicalEquiv S P P'' I := by
  ext
  simp only [IsLocalization.map_map, RingHomInvPair.comp_eq₂, mem_canonicalEquiv_apply,
    exists_prop, exists_exists_and_eq_and]
#align fractional_ideal.canonical_equiv_canonical_equiv FractionalIdeal.canonicalEquiv_canonicalEquiv

theorem canonicalEquiv_trans_canonicalEquiv (P'' : Type*) [CommRing P''] [Algebra R P'']
    [IsLocalization S P''] :
    (canonicalEquiv S P P').trans (canonicalEquiv S P' P'') = canonicalEquiv S P P'' :=
  RingEquiv.ext (canonicalEquiv_canonicalEquiv S P P' P'')
#align fractional_ideal.canonical_equiv_trans_canonical_equiv FractionalIdeal.canonicalEquiv_trans_canonicalEquiv

@[simp]
theorem canonicalEquiv_coeIdeal (I : Ideal R) : canonicalEquiv S P P' I = I := by
  ext
  simp [IsLocalization.map_eq]
#align fractional_ideal.canonical_equiv_coe_ideal FractionalIdeal.canonicalEquiv_coeIdeal

@[simp]
theorem canonicalEquiv_self : canonicalEquiv S P P = RingEquiv.refl _ := by
  rw [← canonicalEquiv_trans_canonicalEquiv S P P]
  convert (canonicalEquiv S P P).symm_trans_self
  exact (canonicalEquiv_symm S P P).symm
#align fractional_ideal.canonical_equiv_self FractionalIdeal.canonicalEquiv_self

end

section IsFractionRing

/-!
### `IsFractionRing` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `FractionalIdeal R⁰ K` where `IsFractionRing R K`.
-/


variable {K K' : Type*} [Field K] [Field K']

variable [Algebra R K] [IsFractionRing R K] [Algebra R K'] [IsFractionRing R K']

variable {I J : FractionalIdeal R⁰ K} (h : K →ₐ[R] K')

/-- Nonzero fractional ideals contain a nonzero integer. -/
theorem exists_ne_zero_mem_isInteger [Nontrivial R] (hI : I ≠ 0) :
    ∃ x, x ≠ 0 ∧ algebraMap R K x ∈ I := by
  obtain ⟨y : K, y_mem, y_not_mem⟩ :=
    SetLike.exists_of_lt (by simpa only using bot_lt_iff_ne_bot.mpr hI)
  have y_ne_zero : y ≠ 0 := by simpa using y_not_mem
  obtain ⟨z, ⟨x, hx⟩⟩ := exists_integer_multiple R⁰ y
  refine' ⟨x, _, _⟩
  · rw [Ne.def, ← @IsFractionRing.to_map_eq_zero_iff R _ K, hx, Algebra.smul_def]
    exact mul_ne_zero (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2) y_ne_zero
  · rw [hx]
    exact smul_mem _ _ y_mem
#align fractional_ideal.exists_ne_zero_mem_is_integer FractionalIdeal.exists_ne_zero_mem_isInteger

theorem map_ne_zero [Nontrivial R] (hI : I ≠ 0) : I.map h ≠ 0 := by
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_isInteger hI
  contrapose! x_ne_zero with map_eq_zero
  refine' IsFractionRing.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr _))
  exact ⟨algebraMap R K x, hx, h.commutes x⟩
#align fractional_ideal.map_ne_zero FractionalIdeal.map_ne_zero

@[simp]
theorem map_eq_zero_iff [Nontrivial R] : I.map h = 0 ↔ I = 0 :=
  ⟨not_imp_not.mp (map_ne_zero _), fun hI => hI.symm ▸ map_zero h⟩
#align fractional_ideal.map_eq_zero_iff FractionalIdeal.map_eq_zero_iff

theorem coeIdeal_injective : Function.Injective (fun (I : Ideal R) ↦ (I : FractionalIdeal R⁰ K)) :=
  coeIdeal_injective' le_rfl
#align fractional_ideal.coe_ideal_injective FractionalIdeal.coeIdeal_injective

theorem coeIdeal_inj {I J : Ideal R} :
    (I : FractionalIdeal R⁰ K) = (J : FractionalIdeal R⁰ K) ↔ I = J :=
  coeIdeal_inj' le_rfl
#align fractional_ideal.coe_ideal_inj FractionalIdeal.coeIdeal_inj

@[simp]
theorem coeIdeal_eq_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 0 ↔ I = ⊥ :=
  coeIdeal_eq_zero' le_rfl
#align fractional_ideal.coe_ideal_eq_zero FractionalIdeal.coeIdeal_eq_zero

theorem coeIdeal_ne_zero {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 0 ↔ I ≠ ⊥ :=
  coeIdeal_ne_zero' le_rfl
#align fractional_ideal.coe_ideal_ne_zero FractionalIdeal.coeIdeal_ne_zero

@[simp]
theorem coeIdeal_eq_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) = 1 ↔ I = 1 := by
  simpa only [Ideal.one_eq_top] using coeIdeal_inj
#align fractional_ideal.coe_ideal_eq_one FractionalIdeal.coeIdeal_eq_one

theorem coeIdeal_ne_one {I : Ideal R} : (I : FractionalIdeal R⁰ K) ≠ 1 ↔ I ≠ 1 :=
  not_iff_not.mpr coeIdeal_eq_one
#align fractional_ideal.coe_ideal_ne_one FractionalIdeal.coeIdeal_ne_one

theorem num_eq_zero_iff [Nontrivial R] {I : FractionalIdeal R⁰ K} : I.num = 0 ↔ I = 0 :=
   ⟨fun h ↦ zero_of_num_eq_bot zero_not_mem_nonZeroDivisors h,
     fun h ↦ h ▸ num_zero_eq (IsFractionRing.injective R K)⟩

end IsFractionRing

section Quotient

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = nonZeroDivisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/


open Classical

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]

variable [Algebra R₁ K] [frac : IsFractionRing R₁ K]

instance : Nontrivial (FractionalIdeal R₁⁰ K) :=
  ⟨⟨0, 1, fun h =>
      have this : (1 : K) ∈ (0 : FractionalIdeal R₁⁰ K) := by
        rw [← (algebraMap R₁ K).map_one]
        simpa only [h] using coe_mem_one R₁⁰ 1
      one_ne_zero ((mem_zero_iff _).mp this)⟩⟩

theorem ne_zero_of_mul_eq_one (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) : I ≠ 0 := fun hI =>
  zero_ne_one' (FractionalIdeal R₁⁰ K)
    (by
      convert h
      simp [hI])
#align fractional_ideal.ne_zero_of_mul_eq_one FractionalIdeal.ne_zero_of_mul_eq_one

variable [IsDomain R₁]

theorem _root_.IsFractional.div_of_nonzero {I J : Submodule R₁ K} :
    IsFractional R₁⁰ I → IsFractional R₁⁰ J → J ≠ 0 → IsFractional R₁⁰ (I / J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩, h => by
    obtain ⟨y, mem_J, not_mem_zero⟩ :=
      SetLike.exists_of_lt (show 0 < J by simpa only using bot_lt_iff_ne_bot.mpr h)
    obtain ⟨y', hy'⟩ := hJ y mem_J
    use aI * y'
    constructor
    · apply (nonZeroDivisors R₁).mul_mem haI (mem_nonZeroDivisors_iff_ne_zero.mpr _)
      intro y'_eq_zero
      have : algebraMap R₁ K aJ * y = 0 := by
        rw [← Algebra.smul_def, ← hy', y'_eq_zero, RingHom.map_zero]
      have y_zero :=
        (mul_eq_zero.mp this).resolve_left
          (mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).1 (IsFractionRing.injective _ _) _)
            (mem_nonZeroDivisors_iff_ne_zero.mp haJ))
      apply not_mem_zero
      simpa
    intro b hb
    convert hI _ (hb _ (Submodule.smul_mem _ aJ mem_J)) using 1
    rw [← hy', mul_comm b, ← Algebra.smul_def, mul_smul]
#align is_fractional.div_of_nonzero IsFractional.div_of_nonzero

theorem fractional_div_of_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    IsFractional R₁⁰ (I / J : Submodule R₁ K) :=
  I.isFractional.div_of_nonzero J.isFractional fun H =>
    h <| coeToSubmodule_injective <| H.trans coe_zero.symm
#align fractional_ideal.fractional_div_of_nonzero FractionalIdeal.fractional_div_of_nonzero

noncomputable instance : Div (FractionalIdeal R₁⁰ K) :=
  ⟨fun I J => if h : J = 0 then 0 else ⟨I / J, fractional_div_of_nonzero h⟩⟩

variable {I J : FractionalIdeal R₁⁰ K}

@[simp]
theorem div_zero {I : FractionalIdeal R₁⁰ K} : I / 0 = 0 :=
  dif_pos rfl
#align fractional_ideal.div_zero FractionalIdeal.div_zero

theorem div_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) :
    I / J = ⟨I / J, fractional_div_of_nonzero h⟩ :=
  dif_neg h
#align fractional_ideal.div_nonzero FractionalIdeal.div_nonzero

@[simp]
theorem coe_div {I J : FractionalIdeal R₁⁰ K} (hJ : J ≠ 0) :
    (↑(I / J) : Submodule R₁ K) = ↑I / (↑J : Submodule R₁ K) :=
  congr_arg _ (dif_neg hJ)
#align fractional_ideal.coe_div FractionalIdeal.coe_div

theorem mem_div_iff_of_nonzero {I J : FractionalIdeal R₁⁰ K} (h : J ≠ 0) {x} :
    x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I := by
  rw [div_nonzero h]
  exact Submodule.mem_div_iff_forall_mul_mem
#align fractional_ideal.mem_div_iff_of_nonzero FractionalIdeal.mem_div_iff_of_nonzero

theorem mul_one_div_le_one {I : FractionalIdeal R₁⁰ K} : I * (1 / I) ≤ 1 := by
  by_cases hI : I = 0
  · rw [hI, div_zero, mul_zero]
    exact zero_le 1
  · rw [← coe_le_coe, coe_mul, coe_div hI, coe_one]
    apply Submodule.mul_one_div_le_one
#align fractional_ideal.mul_one_div_le_one FractionalIdeal.mul_one_div_le_one

theorem le_self_mul_one_div {I : FractionalIdeal R₁⁰ K} (hI : I ≤ (1 : FractionalIdeal R₁⁰ K)) :
    I ≤ I * (1 / I) := by
  by_cases hI_nz : I = 0
  · rw [hI_nz, div_zero, mul_zero]
  · rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one]
    rw [← coe_le_coe, coe_one] at hI
    exact Submodule.le_self_mul_one_div hI
#align fractional_ideal.le_self_mul_one_div FractionalIdeal.le_self_mul_one_div

theorem le_div_iff_of_nonzero {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
    I ≤ J / J' ↔ ∀ x ∈ I, ∀ y ∈ J', x * y ∈ J :=
  ⟨fun h _ hx => (mem_div_iff_of_nonzero hJ').mp (h hx), fun h x hx =>
    (mem_div_iff_of_nonzero hJ').mpr (h x hx)⟩
#align fractional_ideal.le_div_iff_of_nonzero FractionalIdeal.le_div_iff_of_nonzero

theorem le_div_iff_mul_le {I J J' : FractionalIdeal R₁⁰ K} (hJ' : J' ≠ 0) :
    I ≤ J / J' ↔ I * J' ≤ J := by
  rw [div_nonzero hJ']
  -- Porting note: this used to be { convert; rw }, flipped the order.
  rw [← coe_le_coe (I := I * J') (J := J), coe_mul]
  exact Submodule.le_div_iff_mul_le
#align fractional_ideal.le_div_iff_mul_le FractionalIdeal.le_div_iff_mul_le

@[simp]
theorem div_one {I : FractionalIdeal R₁⁰ K} : I / 1 = I := by
  rw [div_nonzero (one_ne_zero' (FractionalIdeal R₁⁰ K))]
  ext
  constructor <;> intro h
  · simpa using mem_div_iff_forall_mul_mem.mp h 1 ((algebraMap R₁ K).map_one ▸ coe_mem_one R₁⁰ 1)
  · apply mem_div_iff_forall_mul_mem.mpr
    rintro y ⟨y', _, rfl⟩
    -- Porting note: this used to be { convert; rw }, flipped the order.
    rw [mul_comm, Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem _ y' h
#align fractional_ideal.div_one FractionalIdeal.div_one

theorem eq_one_div_of_mul_eq_one_right (I J : FractionalIdeal R₁⁰ K) (h : I * J = 1) :
    J = 1 / I := by
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h
  suffices h' : I * (1 / I) = 1
  · exact
      congr_arg Units.inv <|
        @Units.ext _ _ (Units.mkOfMulEqOne _ _ h) (Units.mkOfMulEqOne _ _ h') rfl
  apply le_antisymm
  · apply mul_le.mpr _
    intro x hx y hy
    rw [mul_comm]
    exact (mem_div_iff_of_nonzero hI).mp hy x hx
  rw [← h]
  apply mul_left_mono I
  apply (le_div_iff_of_nonzero hI).mpr _
  intro y hy x hx
  rw [mul_comm]
  exact mul_mem_mul hx hy
#align fractional_ideal.eq_one_div_of_mul_eq_one_right FractionalIdeal.eq_one_div_of_mul_eq_one_right

theorem mul_div_self_cancel_iff {I : FractionalIdeal R₁⁰ K} : I * (1 / I) = 1 ↔ ∃ J, I * J = 1 :=
  ⟨fun h => ⟨1 / I, h⟩, fun ⟨J, hJ⟩ => by rwa [← eq_one_div_of_mul_eq_one_right I J hJ]⟩
#align fractional_ideal.mul_div_self_cancel_iff FractionalIdeal.mul_div_self_cancel_iff

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

@[simp]
theorem map_div (I J : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (I / J).map (h : K →ₐ[R₁] K') = I.map h / J.map h := by
  by_cases H : J = 0
  · rw [H, div_zero, map_zero, div_zero]
  · -- Porting note: `simp` wouldn't apply these lemmas so do them manually using `rw`
    rw [← coeToSubmodule_inj, div_nonzero H, div_nonzero (map_ne_zero _ H)]
    simp [Submodule.map_div]
#align fractional_ideal.map_div FractionalIdeal.map_div

-- Porting note: doesn't need to be @[simp] because this follows from `map_one` and `map_div`
theorem map_one_div (I : FractionalIdeal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
    (1 / I).map (h : K →ₐ[R₁] K') = 1 / I.map h := by rw [map_div, map_one]
#align fractional_ideal.map_one_div FractionalIdeal.map_one_div

end Quotient

section Field

variable {R₁ K L : Type*} [CommRing R₁] [Field K] [Field L]

variable [Algebra R₁ K] [IsFractionRing R₁ K] [Algebra K L] [IsFractionRing K L]

theorem eq_zero_or_one (I : FractionalIdeal K⁰ L) : I = 0 ∨ I = 1 := by
  rw [or_iff_not_imp_left]
  intro hI
  simp_rw [@SetLike.ext_iff _ _ _ I 1, mem_one_iff]
  intro x
  constructor
  · intro x_mem
    obtain ⟨n, d, rfl⟩ := IsLocalization.mk'_surjective K⁰ x
    refine' ⟨n / d, _⟩
    rw [map_div₀, IsFractionRing.mk'_eq_div]
  · rintro ⟨x, rfl⟩
    obtain ⟨y, y_ne, y_mem⟩ := exists_ne_zero_mem_isInteger hI
    rw [← div_mul_cancel x y_ne, RingHom.map_mul, ← Algebra.smul_def]
    exact smul_mem (M := L) I (x / y) y_mem
#align fractional_ideal.eq_zero_or_one FractionalIdeal.eq_zero_or_one

theorem eq_zero_or_one_of_isField (hF : IsField R₁) (I : FractionalIdeal R₁⁰ K) : I = 0 ∨ I = 1 :=
  letI : Field R₁ := hF.toField
  eq_zero_or_one I
#align fractional_ideal.eq_zero_or_one_of_is_field FractionalIdeal.eq_zero_or_one_of_isField

end Field

section PrincipalIdeal

variable {R₁ : Type*} [CommRing R₁] {K : Type*} [Field K]

variable [Algebra R₁ K] [IsFractionRing R₁ K]

open Classical

variable (R₁)

/-- `FractionalIdeal.span_finset R₁ s f` is the fractional ideal of `R₁` generated by `f '' s`. -/
-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
def spanFinset {ι : Type*} (s : Finset ι) (f : ι → K) : FractionalIdeal R₁⁰ K :=
  ⟨Submodule.span R₁ (f '' s), by
    obtain ⟨a', ha'⟩ := IsLocalization.exist_integer_multiples R₁⁰ s f
    refine' ⟨a', a'.2, fun x hx => Submodule.span_induction hx _ _ _ _⟩
    · rintro _ ⟨i, hi, rfl⟩
      exact ha' i hi
    · rw [smul_zero]
      exact IsLocalization.isInteger_zero
    · intro x y hx hy
      rw [smul_add]
      exact IsLocalization.isInteger_add hx hy
    · intro c x hx
      rw [smul_comm]
      exact IsLocalization.isInteger_smul hx⟩
#align fractional_ideal.span_finset FractionalIdeal.spanFinset

@[simp] lemma spanFinset_coe {ι : Type*} (s : Finset ι) (f : ι → K) :
    (spanFinset R₁ s f : Submodule R₁ K) = Submodule.span R₁ (f '' s) :=
  rfl

variable {R₁}

@[simp]
theorem spanFinset_eq_zero {ι : Type*} {s : Finset ι} {f : ι → K} :
    spanFinset R₁ s f = 0 ↔ ∀ j ∈ s, f j = 0 := by
  simp only [← coeToSubmodule_inj, spanFinset_coe, coe_zero, Submodule.span_eq_bot,
    Set.mem_image, Finset.mem_coe, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
#align fractional_ideal.span_finset_eq_zero FractionalIdeal.spanFinset_eq_zero

theorem spanFinset_ne_zero {ι : Type*} {s : Finset ι} {f : ι → K} :
    spanFinset R₁ s f ≠ 0 ↔ ∃ j ∈ s, f j ≠ 0 := by simp
#align fractional_ideal.span_finset_ne_zero FractionalIdeal.spanFinset_ne_zero

open Submodule.IsPrincipal

theorem isFractional_span_singleton (x : P) : IsFractional S (span R {x} : Submodule R P) :=
  let ⟨a, ha⟩ := exists_integer_multiple S x
  isFractional_span_iff.mpr ⟨a, a.2, fun _ hx' => (Set.mem_singleton_iff.mp hx').symm ▸ ha⟩
#align fractional_ideal.is_fractional_span_singleton FractionalIdeal.isFractional_span_singleton

variable (S)

/-- `spanSingleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
irreducible_def spanSingleton (x : P) : FractionalIdeal S P :=
  ⟨span R {x}, isFractional_span_singleton x⟩
#align fractional_ideal.span_singleton FractionalIdeal.spanSingleton

-- local attribute [semireducible] span_singleton
@[simp]
theorem coe_spanSingleton (x : P) : (spanSingleton S x : Submodule R P) = span R {x} := by
  rw [spanSingleton]
  rfl
#align fractional_ideal.coe_span_singleton FractionalIdeal.coe_spanSingleton

@[simp]
theorem mem_spanSingleton {x y : P} : x ∈ spanSingleton S y ↔ ∃ z : R, z • y = x := by
  rw [spanSingleton]
  exact Submodule.mem_span_singleton
#align fractional_ideal.mem_span_singleton FractionalIdeal.mem_spanSingleton

theorem mem_spanSingleton_self (x : P) : x ∈ spanSingleton S x :=
  (mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩
#align fractional_ideal.mem_span_singleton_self FractionalIdeal.mem_spanSingleton_self

variable (P) in
/-- A version of `FractionalIdeal.den_mul_self_eq_num` in terms of fractional ideals. -/
theorem den_mul_self_eq_num' (I : FractionalIdeal S P) :
    spanSingleton S (algebraMap R P I.den) * I = I.num := by
  apply coeToSubmodule_injective
  dsimp only
  rw [coe_mul, ← smul_eq_mul, coe_spanSingleton, smul_eq_mul, Submodule.span_singleton_mul]
  convert I.den_mul_self_eq_num using 1
  ext
  erw [Set.mem_smul_set, Set.mem_smul_set]
  simp [Algebra.smul_def]

variable {S}

@[simp]
theorem spanSingleton_le_iff_mem {x : P} {I : FractionalIdeal S P} :
    spanSingleton S x ≤ I ↔ x ∈ I := by
  rw [← coe_le_coe, coe_spanSingleton, Submodule.span_singleton_le_iff_mem, mem_coe]
#align fractional_ideal.span_singleton_le_iff_mem FractionalIdeal.spanSingleton_le_iff_mem

theorem spanSingleton_eq_spanSingleton [NoZeroSMulDivisors R P] {x y : P} :
    spanSingleton S x = spanSingleton S y ↔ ∃ z : Rˣ, z • x = y := by
  rw [← Submodule.span_singleton_eq_span_singleton, spanSingleton, spanSingleton]
  exact Subtype.mk_eq_mk
#align fractional_ideal.span_singleton_eq_span_singleton FractionalIdeal.spanSingleton_eq_spanSingleton

theorem eq_spanSingleton_of_principal (I : FractionalIdeal S P) [IsPrincipal (I : Submodule R P)] :
    I = spanSingleton S (generator (I : Submodule R P)) := by
  -- Porting note: this used to be `coeToSubmodule_injective (span_singleton_generator ↑I).symm`
  -- but Lean 4 struggled to unify everything. Turned it into an explicit `rw`.
  rw [spanSingleton, ← coeToSubmodule_inj, coe_mk, span_singleton_generator]
#align fractional_ideal.eq_span_singleton_of_principal FractionalIdeal.eq_spanSingleton_of_principal

theorem isPrincipal_iff (I : FractionalIdeal S P) :
    IsPrincipal (I : Submodule R P) ↔ ∃ x, I = spanSingleton S x :=
  ⟨fun h => ⟨@generator _ _ _ _ _ (↑I) h, @eq_spanSingleton_of_principal _ _ _ _ _ _ _ I h⟩,
    fun ⟨x, hx⟩ => { principal' := ⟨x, Eq.trans (congr_arg _ hx) (coe_spanSingleton _ x)⟩ }⟩
#align fractional_ideal.is_principal_iff FractionalIdeal.isPrincipal_iff

@[simp]
theorem spanSingleton_zero : spanSingleton S (0 : P) = 0 := by
  ext
  simp [Submodule.mem_span_singleton, eq_comm]
#align fractional_ideal.span_singleton_zero FractionalIdeal.spanSingleton_zero

theorem spanSingleton_eq_zero_iff {y : P} : spanSingleton S y = 0 ↔ y = 0 :=
  ⟨fun h =>
    span_eq_bot.mp (by simpa using congr_arg Subtype.val h : span R {y} = ⊥) y (mem_singleton y),
    fun h => by simp [h]⟩
#align fractional_ideal.span_singleton_eq_zero_iff FractionalIdeal.spanSingleton_eq_zero_iff

theorem spanSingleton_ne_zero_iff {y : P} : spanSingleton S y ≠ 0 ↔ y ≠ 0 :=
  not_congr spanSingleton_eq_zero_iff
#align fractional_ideal.span_singleton_ne_zero_iff FractionalIdeal.spanSingleton_ne_zero_iff

@[simp]
theorem spanSingleton_one : spanSingleton S (1 : P) = 1 := by
  ext
  refine' (mem_spanSingleton S).trans ((exists_congr _).trans (mem_one_iff S).symm)
  intro x'
  rw [Algebra.smul_def, mul_one]
#align fractional_ideal.span_singleton_one FractionalIdeal.spanSingleton_one

@[simp]
theorem spanSingleton_mul_spanSingleton (x y : P) :
    spanSingleton S x * spanSingleton S y = spanSingleton S (x * y) := by
  apply coeToSubmodule_injective
  simp only [coe_mul, coe_spanSingleton, span_mul_span, singleton_mul_singleton]
#align fractional_ideal.span_singleton_mul_span_singleton FractionalIdeal.spanSingleton_mul_spanSingleton

@[simp]
theorem spanSingleton_pow (x : P) (n : ℕ) : spanSingleton S x ^ n = spanSingleton S (x ^ n) := by
  induction' n with n hn
  · rw [pow_zero, pow_zero, spanSingleton_one]
  · rw [pow_succ, hn, spanSingleton_mul_spanSingleton, pow_succ]
#align fractional_ideal.span_singleton_pow FractionalIdeal.spanSingleton_pow

@[simp]
theorem coeIdeal_span_singleton (x : R) :
    (↑(Ideal.span {x} : Ideal R) : FractionalIdeal S P) = spanSingleton S (algebraMap R P x) := by
  ext y
  refine' (mem_coeIdeal S).trans (Iff.trans _ (mem_spanSingleton S).symm)
  constructor
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨x', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    use x'
    rw [smul_eq_mul, RingHom.map_mul, Algebra.smul_def]
  · rintro ⟨y', rfl⟩
    refine' ⟨y' * x, Submodule.mem_span_singleton.mpr ⟨y', rfl⟩, _⟩
    rw [RingHom.map_mul, Algebra.smul_def]
#align fractional_ideal.coe_ideal_span_singleton FractionalIdeal.coeIdeal_span_singleton

@[simp]
theorem canonicalEquiv_spanSingleton {P'} [CommRing P'] [Algebra R P'] [IsLocalization S P']
    (x : P) :
    canonicalEquiv S P P' (spanSingleton S x) =
      spanSingleton S
        (IsLocalization.map P' (RingHom.id R)
          (fun y (hy : y ∈ S) => show RingHom.id R y ∈ S from hy) x) := by
  apply SetLike.ext_iff.mpr
  intro y
  constructor <;> intro h
  · rw [mem_spanSingleton]
    obtain ⟨x', hx', rfl⟩ := (mem_canonicalEquiv_apply _ _ _).mp h
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp hx'
    use z
    rw [IsLocalization.map_smul, RingHom.id_apply]
  · rw [mem_canonicalEquiv_apply]
    obtain ⟨z, rfl⟩ := (mem_spanSingleton _).mp h
    use z • x
    use (mem_spanSingleton _).mpr ⟨z, rfl⟩
    simp [IsLocalization.map_smul]
#align fractional_ideal.canonical_equiv_span_singleton FractionalIdeal.canonicalEquiv_spanSingleton

theorem mem_singleton_mul {x y : P} {I : FractionalIdeal S P} :
    y ∈ spanSingleton S x * I ↔ ∃ y' ∈ I, y = x * y' := by
  constructor
  · intro h
    refine FractionalIdeal.mul_induction_on h ?_ ?_
    · intro x' hx' y' hy'
      obtain ⟨a, ha⟩ := (mem_spanSingleton S).mp hx'
      use a • y', Submodule.smul_mem (I : Submodule R P) a hy'
      rw [← ha, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    · rintro _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
      exact ⟨y + y', Submodule.add_mem (I : Submodule R P) hy hy', (mul_add _ _ _).symm⟩
  · rintro ⟨y', hy', rfl⟩
    exact mul_mem_mul ((mem_spanSingleton S).mpr ⟨1, one_smul _ _⟩) hy'
#align fractional_ideal.mem_singleton_mul FractionalIdeal.mem_singleton_mul

variable (K)

theorem mk'_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {x y : R₁} (hy : y ∈ R₁⁰) :
    spanSingleton R₁⁰ (IsLocalization.mk' K x ⟨y, hy⟩) * I = (J : FractionalIdeal R₁⁰ K) ↔
      Ideal.span {x} * I = Ideal.span {y} * J := by
  have :
    spanSingleton R₁⁰ (IsLocalization.mk' _ (1 : R₁) ⟨y, hy⟩) *
        spanSingleton R₁⁰ (algebraMap R₁ K y) =
      1 := by
    rw [spanSingleton_mul_spanSingleton, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one,
      IsLocalization.mk'_self, spanSingleton_one]
  let y' : (FractionalIdeal R₁⁰ K)ˣ := Units.mkOfMulEqOne _ _ this
  have coe_y' : ↑y' = spanSingleton R₁⁰ (IsLocalization.mk' K (1 : R₁) ⟨y, hy⟩) := rfl
  refine' Iff.trans _ (y'.mul_right_inj.trans coeIdeal_inj)
  rw [coe_y', coeIdeal_mul, coeIdeal_span_singleton, coeIdeal_mul, coeIdeal_span_singleton, ←
    mul_assoc, spanSingleton_mul_spanSingleton, ← mul_assoc, spanSingleton_mul_spanSingleton,
    mul_comm (mk' _ _ _), ← IsLocalization.mk'_eq_mul_mk'_one, mul_comm (mk' _ _ _), ←
    IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_self, spanSingleton_one, one_mul]
#align fractional_ideal.mk'_mul_coe_ideal_eq_coe_ideal FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal

variable {K}

theorem spanSingleton_mul_coeIdeal_eq_coeIdeal {I J : Ideal R₁} {z : K} :
    spanSingleton R₁⁰ z * (I : FractionalIdeal R₁⁰ K) = J ↔
      Ideal.span {((IsLocalization.sec R₁⁰ z).1 : R₁)} * I =
        Ideal.span {((IsLocalization.sec R₁⁰ z).2 : R₁)} * J := by
  rw [← mk'_mul_coeIdeal_eq_coeIdeal K (IsLocalization.sec R₁⁰ z).2.prop,
    IsLocalization.mk'_sec K z]
#align fractional_ideal.span_singleton_mul_coe_ideal_eq_coe_ideal FractionalIdeal.spanSingleton_mul_coeIdeal_eq_coeIdeal

variable [IsDomain R₁]

theorem one_div_spanSingleton (x : K) : 1 / spanSingleton R₁⁰ x = spanSingleton R₁⁰ x⁻¹ :=
  if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one_right _ _ (by simp [h])).symm
#align fractional_ideal.one_div_span_singleton FractionalIdeal.one_div_spanSingleton

@[simp]
theorem div_spanSingleton (J : FractionalIdeal R₁⁰ K) (d : K) :
    J / spanSingleton R₁⁰ d = spanSingleton R₁⁰ d⁻¹ * J := by
  rw [← one_div_spanSingleton]
  by_cases hd : d = 0
  · simp only [hd, spanSingleton_zero, div_zero, zero_mul]
  have h_spand : spanSingleton R₁⁰ d ≠ 0 := mt spanSingleton_eq_zero_iff.mp hd
  apply le_antisymm
  · intro x hx
    dsimp only [val_eq_coe] at hx ⊢ -- Porting note: get rid of the partially applied `coe`s
    rw [coe_div h_spand, Submodule.mem_div_iff_forall_mul_mem] at hx
    specialize hx d (mem_spanSingleton_self R₁⁰ d)
    have h_xd : x = d⁻¹ * (x * d) := by field_simp
    rw [coe_mul, one_div_spanSingleton, h_xd]
    exact Submodule.mul_mem_mul (mem_spanSingleton_self R₁⁰ _) hx
  · rw [le_div_iff_mul_le h_spand, mul_assoc, mul_left_comm, one_div_spanSingleton,
      spanSingleton_mul_spanSingleton, inv_mul_cancel hd, spanSingleton_one, mul_one]
#align fractional_ideal.div_span_singleton FractionalIdeal.div_spanSingleton

theorem exists_eq_spanSingleton_mul (I : FractionalIdeal R₁⁰ K) :
    ∃ (a : R₁) (aI : Ideal R₁), a ≠ 0 ∧ I = spanSingleton R₁⁰ (algebraMap R₁ K a)⁻¹ * aI := by
  obtain ⟨a_inv, nonzero, ha⟩ := I.isFractional
  have nonzero := mem_nonZeroDivisors_iff_ne_zero.mp nonzero
  have map_a_nonzero : algebraMap R₁ K a_inv ≠ 0 :=
    mt IsFractionRing.to_map_eq_zero_iff.mp nonzero
  refine'
    ⟨a_inv,
      Submodule.comap (Algebra.linearMap R₁ K) ↑(spanSingleton R₁⁰ (algebraMap R₁ K a_inv) * I),
      nonzero, ext fun x => Iff.trans ⟨_, _⟩ mem_singleton_mul.symm⟩
  · intro hx
    obtain ⟨x', hx'⟩ := ha x hx
    rw [Algebra.smul_def] at hx'
    refine' ⟨algebraMap R₁ K x', (mem_coeIdeal _).mpr ⟨x', mem_singleton_mul.mpr _, rfl⟩, _⟩
    · exact ⟨x, hx, hx'⟩
    · rw [hx', ← mul_assoc, inv_mul_cancel map_a_nonzero, one_mul]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x', hx', rfl⟩ := (mem_coeIdeal _).mp hy
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx'
    rw [Algebra.linearMap_apply] at hx'
    rwa [hx', ← mul_assoc, inv_mul_cancel map_a_nonzero, one_mul]
#align fractional_ideal.exists_eq_span_singleton_mul FractionalIdeal.exists_eq_spanSingleton_mul

instance isPrincipal {R} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra R K]
    [IsFractionRing R K] (I : FractionalIdeal R⁰ K) : (I : Submodule R K).IsPrincipal := by
  obtain ⟨a, aI, -, ha⟩ := exists_eq_spanSingleton_mul I
  use (algebraMap R K a)⁻¹ * algebraMap R K (generator aI)
  suffices I = spanSingleton R⁰ ((algebraMap R K a)⁻¹ * algebraMap R K (generator aI)) by
    rw [spanSingleton] at this
    exact congr_arg Subtype.val this
  conv_lhs => rw [ha, ← span_singleton_generator aI]
  rw [Ideal.submodule_span_eq, coeIdeal_span_singleton (generator aI),
    spanSingleton_mul_spanSingleton]
#align fractional_ideal.is_principal FractionalIdeal.isPrincipal

theorem le_spanSingleton_mul_iff {x : P} {I J : FractionalIdeal S P} :
    I ≤ spanSingleton S x * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
  show (∀ {zI} (hzI : zI ∈ I), zI ∈ spanSingleton _ x * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI by
    simp only [mem_singleton_mul, eq_comm]
#align fractional_ideal.le_span_singleton_mul_iff FractionalIdeal.le_spanSingleton_mul_iff

theorem spanSingleton_mul_le_iff {x : P} {I J : FractionalIdeal S P} :
    spanSingleton _ x * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J := by
  simp only [mul_le, mem_singleton_mul, mem_spanSingleton]
  constructor
  · intro h zI hzI
    exact h x ⟨1, one_smul _ _⟩ zI hzI
  · rintro h _ ⟨z, rfl⟩ zI hzI
    rw [Algebra.smul_mul_assoc]
    exact Submodule.smul_mem J.1 _ (h zI hzI)
#align fractional_ideal.span_singleton_mul_le_iff FractionalIdeal.spanSingleton_mul_le_iff

theorem eq_spanSingleton_mul {x : P} {I J : FractionalIdeal S P} :
    I = spanSingleton _ x * J ↔ (∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀ z ∈ J, x * z ∈ I := by
  simp only [le_antisymm_iff, le_spanSingleton_mul_iff, spanSingleton_mul_le_iff]
#align fractional_ideal.eq_span_singleton_mul FractionalIdeal.eq_spanSingleton_mul

theorem num_le (I : FractionalIdeal S P) :
    (I.num : FractionalIdeal S P) ≤ I := by
  rw [← I.den_mul_self_eq_num', spanSingleton_mul_le_iff]
  intro _ h
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ h

end PrincipalIdeal

variable {R₁ : Type*} [CommRing R₁]

variable {K : Type*} [Field K] [Algebra R₁ K] [frac : IsFractionRing R₁ K]

attribute [local instance] Classical.propDecidable

theorem isNoetherian_zero : IsNoetherian R₁ (0 : FractionalIdeal R₁⁰ K) :=
  isNoetherian_submodule.mpr fun I (hI : I ≤ (0 : FractionalIdeal R₁⁰ K)) => by
    rw [coe_zero, le_bot_iff] at hI
    rw [hI]
    exact fg_bot
#align fractional_ideal.is_noetherian_zero FractionalIdeal.isNoetherian_zero

theorem isNoetherian_iff {I : FractionalIdeal R₁⁰ K} :
    IsNoetherian R₁ I ↔ ∀ J ≤ I, (J : Submodule R₁ K).FG :=
  isNoetherian_submodule.trans ⟨fun h _ hJ => h _ hJ, fun h J hJ => h ⟨J, isFractional_of_le hJ⟩ hJ⟩
#align fractional_ideal.is_noetherian_iff FractionalIdeal.isNoetherian_iff

theorem isNoetherian_coeIdeal [IsNoetherianRing R₁] (I : Ideal R₁) :
    IsNoetherian R₁ (I : FractionalIdeal R₁⁰ K) := by
  rw [isNoetherian_iff]
  intro J hJ
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coeIdeal.mp (le_trans hJ coeIdeal_le_one)
  exact (IsNoetherian.noetherian J).map _
#align fractional_ideal.is_noetherian_coe_ideal FractionalIdeal.isNoetherian_coeIdeal

variable [IsDomain R₁]

theorem isNoetherian_spanSingleton_inv_to_map_mul (x : R₁) {I : FractionalIdeal R₁⁰ K}
    (hI : IsNoetherian R₁ I) :
    IsNoetherian R₁ (spanSingleton R₁⁰ (algebraMap R₁ K x)⁻¹ * I : FractionalIdeal R₁⁰ K) := by
  by_cases hx : x = 0
  · rw [hx, RingHom.map_zero, inv_zero, spanSingleton_zero, zero_mul]
    exact isNoetherian_zero
  have h_gx : algebraMap R₁ K x ≠ 0 :=
    mt ((injective_iff_map_eq_zero (algebraMap R₁ K)).mp (IsFractionRing.injective _ _) x) hx
  have h_spanx : spanSingleton R₁⁰ (algebraMap R₁ K x) ≠ 0 := spanSingleton_ne_zero_iff.mpr h_gx
  rw [isNoetherian_iff] at hI ⊢
  intro J hJ
  rw [← div_spanSingleton, le_div_iff_mul_le h_spanx] at hJ
  obtain ⟨s, hs⟩ := hI _ hJ
  use s * {(algebraMap R₁ K x)⁻¹}
  rw [Finset.coe_mul, Finset.coe_singleton, ← span_mul_span, hs, ← coe_spanSingleton R₁⁰, ←
    coe_mul, mul_assoc, spanSingleton_mul_spanSingleton, mul_inv_cancel h_gx, spanSingleton_one,
    mul_one]
#align fractional_ideal.is_noetherian_span_singleton_inv_to_map_mul FractionalIdeal.isNoetherian_spanSingleton_inv_to_map_mul

/-- Every fractional ideal of a noetherian integral domain is noetherian. -/
theorem isNoetherian [IsNoetherianRing R₁] (I : FractionalIdeal R₁⁰ K) : IsNoetherian R₁ I := by
  obtain ⟨d, J, _, rfl⟩ := exists_eq_spanSingleton_mul I
  apply isNoetherian_spanSingleton_inv_to_map_mul
  apply isNoetherian_coeIdeal
#align fractional_ideal.is_noetherian FractionalIdeal.isNoetherian

section Adjoin

variable (S)
variable (x : P) (hx : IsIntegral R x)

/-- `A[x]` is a fractional ideal for every integral `x`. -/
theorem isFractional_adjoin_integral :
    IsFractional S (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  isFractional_of_fg hx.fg_adjoin_singleton
#align fractional_ideal.is_fractional_adjoin_integral FractionalIdeal.isFractional_adjoin_integral

/-- `FractionalIdeal.adjoinIntegral (S : Submonoid R) x hx` is `R[x]` as a fractional ideal,
where `hx` is a proof that `x : P` is integral over `R`. -/
-- Porting note: `@[simps]` generated a `Subtype.val` coercion instead of a
-- `FractionalIdeal.coeToSubmodule` coercion
def adjoinIntegral : FractionalIdeal S P :=
  ⟨_, isFractional_adjoin_integral S x hx⟩
#align fractional_ideal.adjoin_integral FractionalIdeal.adjoinIntegral

@[simp]
theorem adjoinIntegral_coe :
    (adjoinIntegral S x hx : Submodule R P) =
      (Subalgebra.toSubmodule (Algebra.adjoin R ({x} : Set P))) :=
  rfl

theorem mem_adjoinIntegral_self : x ∈ adjoinIntegral S x hx :=
  Algebra.subset_adjoin (Set.mem_singleton x)
#align fractional_ideal.mem_adjoin_integral_self FractionalIdeal.mem_adjoinIntegral_self

end Adjoin

end FractionalIdeal
