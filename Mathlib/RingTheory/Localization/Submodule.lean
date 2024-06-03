/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Noetherian

#align_import ring_theory.localization.submodule from "leanprover-community/mathlib"@"1ebb20602a8caef435ce47f6373e1aa40851a177"

/-!
# Submodules in localizations of commutative rings

## Implementation notes

See `RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S]
variable [Algebra R S] {P : Type*} [CommRing P]

namespace IsLocalization

-- This was previously a `hasCoe` instance, but if `S = R` then this will loop.
-- It could be a `hasCoeT` instance, but we keep it explicit here to avoid slowing down
-- the rest of the library.
/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
def coeSubmodule (I : Ideal R) : Submodule R S :=
  Submodule.map (Algebra.linearMap R S) I
#align is_localization.coe_submodule IsLocalization.coeSubmodule

theorem mem_coeSubmodule (I : Ideal R) {x : S} :
    x ∈ coeSubmodule S I ↔ ∃ y : R, y ∈ I ∧ algebraMap R S y = x :=
  Iff.rfl
#align is_localization.mem_coe_submodule IsLocalization.mem_coeSubmodule

theorem coeSubmodule_mono {I J : Ideal R} (h : I ≤ J) : coeSubmodule S I ≤ coeSubmodule S J :=
  Submodule.map_mono h
#align is_localization.coe_submodule_mono IsLocalization.coeSubmodule_mono

@[simp]
theorem coeSubmodule_bot : coeSubmodule S (⊥ : Ideal R) = ⊥ := by
  rw [coeSubmodule, Submodule.map_bot]
#align is_localization.coe_submodule_bot IsLocalization.coeSubmodule_bot

@[simp]
theorem coeSubmodule_top : coeSubmodule S (⊤ : Ideal R) = 1 := by
  rw [coeSubmodule, Submodule.map_top, Submodule.one_eq_range]
#align is_localization.coe_submodule_top IsLocalization.coeSubmodule_top

@[simp]
theorem coeSubmodule_sup (I J : Ideal R) :
    coeSubmodule S (I ⊔ J) = coeSubmodule S I ⊔ coeSubmodule S J :=
  Submodule.map_sup _ _ _
#align is_localization.coe_submodule_sup IsLocalization.coeSubmodule_sup

@[simp]
theorem coeSubmodule_mul (I J : Ideal R) :
    coeSubmodule S (I * J) = coeSubmodule S I * coeSubmodule S J :=
  Submodule.map_mul _ _ (Algebra.ofId R S)
#align is_localization.coe_submodule_mul IsLocalization.coeSubmodule_mul

theorem coeSubmodule_fg (hS : Function.Injective (algebraMap R S)) (I : Ideal R) :
    Submodule.FG (coeSubmodule S I) ↔ Submodule.FG I :=
  ⟨Submodule.fg_of_fg_map _ (LinearMap.ker_eq_bot.mpr hS), Submodule.FG.map _⟩
#align is_localization.coe_submodule_fg IsLocalization.coeSubmodule_fg

@[simp]
theorem coeSubmodule_span (s : Set R) :
    coeSubmodule S (Ideal.span s) = Submodule.span R (algebraMap R S '' s) := by
  rw [IsLocalization.coeSubmodule, Ideal.span, Submodule.map_span]
  rfl
#align is_localization.coe_submodule_span IsLocalization.coeSubmodule_span

-- @[simp] -- Porting note (#10618): simp can prove this
theorem coeSubmodule_span_singleton (x : R) :
    coeSubmodule S (Ideal.span {x}) = Submodule.span R {(algebraMap R S) x} := by
  rw [coeSubmodule_span, Set.image_singleton]
#align is_localization.coe_submodule_span_singleton IsLocalization.coeSubmodule_span_singleton

variable {g : R →+* P}
variable {T : Submonoid P} (hy : M ≤ T.comap g) {Q : Type*} [CommRing Q]
variable [Algebra P Q] [IsLocalization T Q]
variable [IsLocalization M S]

section

theorem isNoetherianRing (h : IsNoetherianRing R) : IsNoetherianRing S := by
  rw [isNoetherianRing_iff, isNoetherian_iff_wellFounded] at h ⊢
  exact OrderEmbedding.wellFounded (IsLocalization.orderEmbedding M S).dual h
#align is_localization.is_noetherian_ring IsLocalization.isNoetherianRing

end

variable {S M}

@[mono]
theorem coeSubmodule_le_coeSubmodule (h : M ≤ nonZeroDivisors R) {I J : Ideal R} :
    coeSubmodule S I ≤ coeSubmodule S J ↔ I ≤ J :=
  -- Note: #8386 had to specify the value of `f` here:
  Submodule.map_le_map_iff_of_injective (f := Algebra.linearMap R S) (IsLocalization.injective _ h)
    _ _
#align is_localization.coe_submodule_le_coe_submodule IsLocalization.coeSubmodule_le_coeSubmodule


@[mono]
theorem coeSubmodule_strictMono (h : M ≤ nonZeroDivisors R) :
    StrictMono (coeSubmodule S : Ideal R → Submodule R S) :=
  strictMono_of_le_iff_le fun _ _ => (coeSubmodule_le_coeSubmodule h).symm
#align is_localization.coe_submodule_strict_mono IsLocalization.coeSubmodule_strictMono

variable (S)

theorem coeSubmodule_injective (h : M ≤ nonZeroDivisors R) :
    Function.Injective (coeSubmodule S : Ideal R → Submodule R S) :=
  injective_of_le_imp_le _ fun hl => (coeSubmodule_le_coeSubmodule h).mp hl
#align is_localization.coe_submodule_injective IsLocalization.coeSubmodule_injective

theorem coeSubmodule_isPrincipal {I : Ideal R} (h : M ≤ nonZeroDivisors R) :
    (coeSubmodule S I).IsPrincipal ↔ I.IsPrincipal := by
  constructor <;> rintro ⟨⟨x, hx⟩⟩
  · have x_mem : x ∈ coeSubmodule S I := hx.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨x, _, rfl⟩ := (mem_coeSubmodule _ _).mp x_mem
    refine ⟨⟨x, coeSubmodule_injective S h ?_⟩⟩
    rw [Ideal.submodule_span_eq, hx, coeSubmodule_span_singleton]
  · refine ⟨⟨algebraMap R S x, ?_⟩⟩
    rw [hx, Ideal.submodule_span_eq, coeSubmodule_span_singleton]
#align is_localization.coe_submodule_is_principal IsLocalization.coeSubmodule_isPrincipal

variable {S} (M)

theorem mem_span_iff {N : Type*} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    {x : N} {a : Set N} :
    x ∈ Submodule.span S a ↔ ∃ y ∈ Submodule.span R a, ∃ z : M, x = mk' S 1 z • y := by
  constructor
  · intro h
    refine Submodule.span_induction h ?_ ?_ ?_ ?_
    · rintro x hx
      exact ⟨x, Submodule.subset_span hx, 1, by rw [mk'_one, _root_.map_one, one_smul]⟩
    · exact ⟨0, Submodule.zero_mem _, 1, by rw [mk'_one, _root_.map_one, one_smul]⟩
    · rintro _ _ ⟨y, hy, z, rfl⟩ ⟨y', hy', z', rfl⟩
      refine
        ⟨(z' : R) • y + (z : R) • y',
          Submodule.add_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hy'), z * z', ?_⟩
      rw [smul_add, ← IsScalarTower.algebraMap_smul S (z : R), ←
        IsScalarTower.algebraMap_smul S (z' : R), smul_smul, smul_smul]
      congr 1
      · rw [← mul_one (1 : R), mk'_mul, mul_assoc, mk'_spec, _root_.map_one, mul_one, mul_one]
      · rw [← mul_one (1 : R), mk'_mul, mul_right_comm, mk'_spec, _root_.map_one, mul_one, one_mul]
    · rintro a _ ⟨y, hy, z, rfl⟩
      obtain ⟨y', z', rfl⟩ := mk'_surjective M a
      refine ⟨y' • y, Submodule.smul_mem _ _ hy, z' * z, ?_⟩
      rw [← IsScalarTower.algebraMap_smul S y', smul_smul, ← mk'_mul, smul_smul,
        mul_comm (mk' S _ _), mul_mk'_eq_mk'_of_mul]
  · rintro ⟨y, hy, z, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.span_subset_span R S _ hy)
#align is_localization.mem_span_iff IsLocalization.mem_span_iff

theorem mem_span_map {x : S} {a : Set R} :
    x ∈ Ideal.span (algebraMap R S '' a) ↔ ∃ y ∈ Ideal.span a, ∃ z : M, x = mk' S y z := by
  refine (mem_span_iff M).trans ?_
  constructor
  · rw [← coeSubmodule_span]
    rintro ⟨_, ⟨y, hy, rfl⟩, z, hz⟩
    refine ⟨y, hy, z, ?_⟩
    rw [hz, Algebra.linearMap_apply, smul_eq_mul, mul_comm, mul_mk'_eq_mk'_of_mul, mul_one]
  · rintro ⟨y, hy, z, hz⟩
    refine ⟨algebraMap R S y, Submodule.map_mem_span_algebraMap_image _ _ hy, z, ?_⟩
    rw [hz, smul_eq_mul, mul_comm, mul_mk'_eq_mk'_of_mul, mul_one]
#align is_localization.mem_span_map IsLocalization.mem_span_map

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {A K : Type*} [CommRing A]

section CommRing

variable [CommRing K] [Algebra R K] [IsFractionRing R K] [Algebra A K] [IsFractionRing A K]

@[simp, mono]
theorem coeSubmodule_le_coeSubmodule {I J : Ideal R} :
    coeSubmodule K I ≤ coeSubmodule K J ↔ I ≤ J :=
  IsLocalization.coeSubmodule_le_coeSubmodule le_rfl
#align is_fraction_ring.coe_submodule_le_coe_submodule IsFractionRing.coeSubmodule_le_coeSubmodule

@[mono]
theorem coeSubmodule_strictMono : StrictMono (coeSubmodule K : Ideal R → Submodule R K) :=
  strictMono_of_le_iff_le fun _ _ => coeSubmodule_le_coeSubmodule.symm
#align is_fraction_ring.coe_submodule_strict_mono IsFractionRing.coeSubmodule_strictMono

variable (R K)

theorem coeSubmodule_injective : Function.Injective (coeSubmodule K : Ideal R → Submodule R K) :=
  injective_of_le_imp_le _ fun hl => coeSubmodule_le_coeSubmodule.mp hl
#align is_fraction_ring.coe_submodule_injective IsFractionRing.coeSubmodule_injective

@[simp]
theorem coeSubmodule_isPrincipal {I : Ideal R} : (coeSubmodule K I).IsPrincipal ↔ I.IsPrincipal :=
  IsLocalization.coeSubmodule_isPrincipal _ le_rfl
#align is_fraction_ring.coe_submodule_is_principal IsFractionRing.coeSubmodule_isPrincipal

end CommRing

end IsFractionRing
