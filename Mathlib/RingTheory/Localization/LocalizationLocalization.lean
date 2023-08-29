/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.FractionRing

#align_import ring_theory.localization.localization_localization from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Localizations of localizations

## Implementation notes

See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type*} [CommRing R] (M : Submonoid R) {S : Type*} [CommRing S]

variable [Algebra R S] {P : Type*} [CommRing P]

open Function BigOperators

namespace IsLocalization

section LocalizationLocalization

variable (N : Submonoid S) (T : Type*) [CommRing T] [Algebra R T]

section

variable [Algebra S T] [IsScalarTower R S T]

-- This should only be defined when `S` is the localization `M⁻¹R`, hence the nolint.
/-- Localizing wrt `M ⊆ R` and then wrt `N ⊆ S = M⁻¹R` is equal to the localization of `R` wrt this
module. See `localization_localization_isLocalization`.
-/
@[nolint unusedArguments]
def localizationLocalizationSubmodule : Submonoid R :=
  (N ⊔ M.map (algebraMap R S)).comap (algebraMap R S)
#align is_localization.localization_localization_submodule IsLocalization.localizationLocalizationSubmodule

variable {M N}

@[simp]
theorem mem_localizationLocalizationSubmodule {x : R} :
    x ∈ localizationLocalizationSubmodule M N ↔
      ∃ (y : N) (z : M), algebraMap R S x = y * algebraMap R S z := by
  rw [localizationLocalizationSubmodule, Submonoid.mem_comap, Submonoid.mem_sup]
  -- ⊢ (∃ y, y ∈ N ∧ ∃ z, z ∈ Submonoid.map (algebraMap R S) M ∧ y * z = ↑(algebraM …
  constructor
  -- ⊢ (∃ y, y ∈ N ∧ ∃ z, z ∈ Submonoid.map (algebraMap R S) M ∧ y * z = ↑(algebraM …
  · rintro ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩
    -- ⊢ ∃ y z, ↑(algebraMap R S) x = ↑y * ↑(algebraMap R S) ↑z
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, e.symm⟩
    -- 🎉 no goals
  · rintro ⟨y, z, e⟩
    -- ⊢ ∃ y, y ∈ N ∧ ∃ z, z ∈ Submonoid.map (algebraMap R S) M ∧ y * z = ↑(algebraMa …
    exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩
    -- 🎉 no goals
#align is_localization.mem_localization_localization_submodule IsLocalization.mem_localizationLocalizationSubmodule

variable (M N) [IsLocalization M S]

theorem localization_localization_map_units [IsLocalization N T]
    (y : localizationLocalizationSubmodule M N) : IsUnit (algebraMap R T y) := by
  obtain ⟨y', z, eq⟩ := mem_localizationLocalizationSubmodule.mp y.prop
  -- ⊢ IsUnit (↑(algebraMap R T) ↑y)
  rw [IsScalarTower.algebraMap_apply R S T, eq, RingHom.map_mul, IsUnit.mul_iff]
  -- ⊢ IsUnit (↑(algebraMap S T) ↑y') ∧ IsUnit (↑(algebraMap S T) (↑(algebraMap R S …
  exact ⟨IsLocalization.map_units T y', (IsLocalization.map_units _ z).map (algebraMap S T)⟩
  -- 🎉 no goals
#align is_localization.localization_localization_map_units IsLocalization.localization_localization_map_units

theorem localization_localization_surj [IsLocalization N T] (x : T) :
    ∃ y : R × localizationLocalizationSubmodule M N, x * algebraMap R T y.2 = algebraMap R T y.1
    := by
  rcases IsLocalization.surj N x with ⟨⟨y, s⟩, eq₁⟩
  -- ⊢ ∃ y, x * ↑(algebraMap R T) ↑y.snd = ↑(algebraMap R T) y.fst
  -- x = y / s
  rcases IsLocalization.surj M y with ⟨⟨z, t⟩, eq₂⟩
  -- ⊢ ∃ y, x * ↑(algebraMap R T) ↑y.snd = ↑(algebraMap R T) y.fst
  -- y = z / t
  rcases IsLocalization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩
  -- ⊢ ∃ y, x * ↑(algebraMap R T) ↑y.snd = ↑(algebraMap R T) y.fst
  -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃
  -- ⊢ ∃ y, x * ↑(algebraMap R T) ↑y.snd = ↑(algebraMap R T) y.fst
  refine ⟨⟨z * t', z' * t, ?_⟩, ?_⟩ -- x = y / s = (z * t') / (z' * t)
  -- ⊢ z' * ↑t ∈ localizationLocalizationSubmodule M N
  · rw [mem_localizationLocalizationSubmodule]
    -- ⊢ ∃ y z, ↑(algebraMap R S) (z' * ↑t) = ↑y * ↑(algebraMap R S) ↑z
    refine' ⟨s, t * t', _⟩
    -- ⊢ ↑(algebraMap R S) (z' * ↑t) = ↑s * ↑(algebraMap R S) ↑(t * t')
    rw [RingHom.map_mul, ← eq₃, mul_assoc, ← RingHom.map_mul, mul_comm t, Submonoid.coe_mul]
    -- 🎉 no goals
  · simp only [Subtype.coe_mk, RingHom.map_mul, IsScalarTower.algebraMap_apply R S T, ← eq₃, ← eq₂,
      ← eq₁]
    ring
    -- 🎉 no goals
#align is_localization.localization_localization_surj IsLocalization.localization_localization_surj

theorem localization_localization_eq_iff_exists [IsLocalization N T] (x y : R) :
    algebraMap R T x = algebraMap R T y ↔
      ∃ c : localizationLocalizationSubmodule M N, ↑c * x = ↑c * y := by
  rw [IsScalarTower.algebraMap_apply R S T, IsScalarTower.algebraMap_apply R S T,
    IsLocalization.eq_iff_exists N T]
  constructor
  -- ⊢ (∃ c, ↑c * ↑(algebraMap R S) x = ↑c * ↑(algebraMap R S) y) → ∃ c, ↑c * x = ↑ …
  · rintro ⟨z, eq₁⟩
    -- ⊢ ∃ c, ↑c * x = ↑c * y
    rcases IsLocalization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩
    -- ⊢ ∃ c, ↑c * x = ↑c * y
    dsimp only at eq₂
    -- ⊢ ∃ c, ↑c * x = ↑c * y
    suffices : (algebraMap R S) (x * z' : R) = (algebraMap R S) (y * z')
    -- ⊢ ∃ c, ↑c * x = ↑c * y
    · obtain ⟨c, eq₃ : ↑c * (x * z') = ↑c * (y * z')⟩ := (IsLocalization.eq_iff_exists M S).mp this
      -- ⊢ ∃ c, ↑c * x = ↑c * y
      refine ⟨⟨c * z', ?_⟩, ?_⟩
      -- ⊢ ↑c * z' ∈ localizationLocalizationSubmodule M N
      · rw [mem_localizationLocalizationSubmodule]
        -- ⊢ ∃ y z, ↑(algebraMap R S) (↑c * z') = ↑y * ↑(algebraMap R S) ↑z
        refine ⟨z, c * s, ?_⟩
        -- ⊢ ↑(algebraMap R S) (↑c * z') = ↑z * ↑(algebraMap R S) ↑(c * s)
        rw [map_mul, ← eq₂, Submonoid.coe_mul, map_mul, mul_left_comm]
        -- 🎉 no goals
      · rwa [mul_comm _ z', mul_comm _ z', ← mul_assoc, ← mul_assoc] at eq₃
        -- 🎉 no goals
    · rw [map_mul, map_mul, ← eq₂, ← mul_assoc, ← mul_assoc, mul_comm _ (z : S), eq₁,
      mul_comm _ (z : S)]
  · rintro ⟨⟨c, hc⟩, eq₁ : c * x = c * y⟩
    -- ⊢ ∃ c, ↑c * ↑(algebraMap R S) x = ↑c * ↑(algebraMap R S) y
    rw [mem_localizationLocalizationSubmodule] at hc
    -- ⊢ ∃ c, ↑c * ↑(algebraMap R S) x = ↑c * ↑(algebraMap R S) y
    rcases hc with ⟨z₁, z, eq₂⟩
    -- ⊢ ∃ c, ↑c * ↑(algebraMap R S) x = ↑c * ↑(algebraMap R S) y
    use z₁
    -- ⊢ ↑z₁ * ↑(algebraMap R S) x = ↑z₁ * ↑(algebraMap R S) y
    refine (IsLocalization.map_units S z).mul_right_inj.mp ?_
    -- ⊢ ↑(algebraMap R S) ↑z * (↑z₁ * ↑(algebraMap R S) x) = ↑(algebraMap R S) ↑z *  …
    rw [← mul_assoc, mul_comm _ (z₁ : S), ← eq₂, ← map_mul, eq₁, map_mul, eq₂, ← mul_assoc,
      mul_comm _ (z₁ : S)]
#align is_localization.localization_localization_eq_iff_exists IsLocalization.localization_localization_eq_iff_exists

/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, we have
`N ⁻¹ S = T = (f⁻¹ (N • f(M))) ⁻¹ R`. I.e., the localization of a localization is a localization.
-/
theorem localization_localization_isLocalization [IsLocalization N T] :
    IsLocalization (localizationLocalizationSubmodule M N) T :=
  { map_units' := localization_localization_map_units M N T
    surj' := localization_localization_surj M N T
    eq_iff_exists' := localization_localization_eq_iff_exists M N T _ _ }
#align is_localization.localization_localization_is_localization IsLocalization.localization_localization_isLocalization

/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, if
`N` contains all the units of `S`, then `N ⁻¹ S = T = (f⁻¹ N) ⁻¹ R`. I.e., the localization of a
localization is a localization.
-/
theorem localization_localization_isLocalization_of_has_all_units [IsLocalization N T]
    (H : ∀ x : S, IsUnit x → x ∈ N) : IsLocalization (N.comap (algebraMap R S)) T := by
  convert localization_localization_isLocalization M N T using 1
  -- ⊢ Submonoid.comap (algebraMap R S) N = localizationLocalizationSubmodule M N
  dsimp [localizationLocalizationSubmodule]
  -- ⊢ Submonoid.comap (algebraMap R S) N = Submonoid.comap (algebraMap R S) (N ⊔ S …
  congr
  -- ⊢ N = N ⊔ Submonoid.map (algebraMap R S) M
  symm
  -- ⊢ N ⊔ Submonoid.map (algebraMap R S) M = N
  rw [sup_eq_left]
  -- ⊢ Submonoid.map (algebraMap R S) M ≤ N
  rintro _ ⟨x, hx, rfl⟩
  -- ⊢ ↑(algebraMap R S) x ∈ N
  exact H _ (IsLocalization.map_units _ ⟨x, hx⟩)
  -- 🎉 no goals
#align is_localization.localization_localization_is_localization_of_has_all_units IsLocalization.localization_localization_isLocalization_of_has_all_units

/--
Given a submodule `M ⊆ R` and a prime ideal `p` of `S = M⁻¹R`, with `f : R →+* S` the localization
map, then `T = Sₚ` is the localization of `R` at `f⁻¹(p)`.
-/
theorem isLocalization_isLocalization_atPrime_isLocalization (p : Ideal S) [Hp : p.IsPrime]
    [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T (p.comap (algebraMap R S)) := by
  apply localization_localization_isLocalization_of_has_all_units M p.primeCompl T
  -- ⊢ ∀ (x : S), IsUnit x → x ∈ Ideal.primeCompl p
  intro x hx hx'
  -- ⊢ False
  exact (Hp.1 : ¬_) (p.eq_top_of_isUnit_mem hx' hx)
  -- 🎉 no goals
#align is_localization.is_localization_is_localization_at_prime_is_localization IsLocalization.isLocalization_isLocalization_atPrime_isLocalization

instance (p : Ideal (Localization M)) [p.IsPrime] : Algebra R (Localization.AtPrime p) :=
  inferInstance

instance (p : Ideal (Localization M)) [p.IsPrime] :
    IsScalarTower R (Localization M) (Localization.AtPrime p) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance localization_localization_atPrime_is_localization (p : Ideal (Localization M))
    [p.IsPrime] : IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap R _)) :=
  isLocalization_isLocalization_atPrime_isLocalization M _ _
#align is_localization.localization_localization_at_prime_is_localization IsLocalization.localization_localization_atPrime_is_localization

/-- Given a submodule `M ⊆ R` and a prime ideal `p` of `M⁻¹R`, with `f : R →+* S` the localization
map, then `(M⁻¹R)ₚ` is isomorphic (as an `R`-algebra) to the localization of `R` at `f⁻¹(p)`.
-/
noncomputable def localizationLocalizationAtPrimeIsoLocalization (p : Ideal (Localization M))
    [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃ₐ[R] Localization.AtPrime p :=
  IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _
#align is_localization.localization_localization_at_prime_iso_localization IsLocalization.localizationLocalizationAtPrimeIsoLocalization

end

variable (S)

/-- Given submonoids `M ≤ N` of `R`, this is the canonical algebra structure
of `M⁻¹S` acting on `N⁻¹S`. -/
noncomputable def localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] : Algebra S T :=
  (@IsLocalization.lift R _ M S _ _ T _ _ (algebraMap R T)
    (fun y => map_units T ⟨↑y, h y.prop⟩)).toAlgebra
#align is_localization.localization_algebra_of_submonoid_le IsLocalization.localizationAlgebraOfSubmonoidLe

/-- If `M ≤ N` are submonoids of `R`, then the natural map `M⁻¹S →+* N⁻¹S` commutes with the
localization maps -/
theorem localization_isScalarTower_of_submonoid_le (M N : Submonoid R) (h : M ≤ N)
    [IsLocalization M S] [IsLocalization N T] :
    @IsScalarTower R S T _ (localizationAlgebraOfSubmonoidLe S T M N h).toSMul _ :=
  letI := localizationAlgebraOfSubmonoidLe S T M N h
  IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
#align is_localization.localization_is_scalar_tower_of_submonoid_le IsLocalization.localization_isScalarTower_of_submonoid_le

noncomputable instance (x : Ideal R) [H : x.IsPrime] [IsDomain R] :
    Algebra (Localization.AtPrime x) (Localization (nonZeroDivisors R)) :=
  localizationAlgebraOfSubmonoidLe _ _ x.primeCompl (nonZeroDivisors R)
    (by
      intro a ha
      -- ⊢ a ∈ nonZeroDivisors R
      rw [mem_nonZeroDivisors_iff_ne_zero]
      -- ⊢ a ≠ 0
      exact fun h => ha (h.symm ▸ x.zero_mem))
      -- 🎉 no goals

/-- If `M ≤ N` are submonoids of `R`, then `N⁻¹S` is also the localization of `M⁻¹S` at `N`. -/
theorem isLocalization_of_submonoid_le (M N : Submonoid R) (h : M ≤ N) [IsLocalization M S]
    [IsLocalization N T] [Algebra S T] [IsScalarTower R S T] :
    IsLocalization (N.map (algebraMap R S)) T :=
  { map_units' := by
      rintro ⟨_, ⟨y, hy, rfl⟩⟩
      -- ⊢ IsUnit (↑(algebraMap S T) ↑{ val := ↑(algebraMap R S) y, property := (_ : ∃  …
      convert IsLocalization.map_units T ⟨y, hy⟩
      -- ⊢ ↑(algebraMap S T) ↑{ val := ↑(algebraMap R S) y, property := (_ : ∃ a, a ∈ ↑ …
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
      -- 🎉 no goals
    surj' := fun y => by
      obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj N y
      -- ⊢ ∃ x, y * ↑(algebraMap S T) ↑x.snd = ↑(algebraMap S T) x.fst
      refine ⟨⟨algebraMap R S x, _, _, s.prop, rfl⟩, ?_⟩
      -- ⊢ y * ↑(algebraMap S T) ↑(↑(algebraMap R S) x, { val := ↑(algebraMap R S) ↑s,  …
      simpa [← IsScalarTower.algebraMap_apply] using e
      -- 🎉 no goals
    eq_iff_exists' := fun {x₁ x₂} => by
      obtain ⟨⟨y₁, s₁⟩, e₁⟩ := IsLocalization.surj M x₁
      -- ⊢ ↑(algebraMap S T) x₁ = ↑(algebraMap S T) x₂ ↔ ∃ c, ↑c * x₁ = ↑c * x₂
      obtain ⟨⟨y₂, s₂⟩, e₂⟩ := IsLocalization.surj M x₂
      -- ⊢ ↑(algebraMap S T) x₁ = ↑(algebraMap S T) x₂ ↔ ∃ c, ↑c * x₁ = ↑c * x₂
      refine' Iff.trans _ (Set.exists_image_iff (algebraMap R S) N fun c => c * x₁ = c * x₂).symm
      -- ⊢ ↑(algebraMap S T) x₁ = ↑(algebraMap S T) x₂ ↔ ∃ a, ↑(algebraMap R S) ↑a * x₁ …
      dsimp only at e₁ e₂ ⊢
      -- ⊢ ↑(algebraMap S T) x₁ = ↑(algebraMap S T) x₂ ↔ ∃ a, ↑(algebraMap R S) ↑a * x₁ …
      suffices : algebraMap R T (y₁ * s₂) = algebraMap R T (y₂ * s₁) ↔
        ∃ a : N, algebraMap R S (a * (y₁ * s₂)) = algebraMap R S (a * (y₂ * s₁))
      · have h₁ := @IsUnit.mul_left_inj T _ _ (algebraMap S T x₁) (algebraMap S T x₂)
          (IsLocalization.map_units T ⟨(s₁ : R), h s₁.prop⟩)
        have h₂ := @IsUnit.mul_left_inj T _ _ ((algebraMap S T x₁) * (algebraMap R T s₁))
          ((algebraMap S T x₂) * (algebraMap R T s₁))
          (IsLocalization.map_units T ⟨(s₂ : R), h s₂.prop⟩)
        simp only [IsScalarTower.algebraMap_apply R S T, Subtype.coe_mk] at h₁ h₂
        -- ⊢ ↑(algebraMap S T) x₁ = ↑(algebraMap S T) x₂ ↔ ∃ a, ↑(algebraMap R S) ↑a * x₁ …
        simp only [IsScalarTower.algebraMap_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
          mul_right_comm _ (algebraMap R S s₂),
          mul_right_comm _ (algebraMap S T (algebraMap R S s₂)),
          (IsLocalization.map_units S s₁).mul_left_inj,
          (IsLocalization.map_units S s₂).mul_left_inj] at this
        rw [h₂, h₁] at this
        -- ⊢ ↑(algebraMap S T) x₁ = ↑(algebraMap S T) x₂ ↔ ∃ a, ↑(algebraMap R S) ↑a * x₁ …
        simpa only [mul_comm] using this
        -- 🎉 no goals
      · simp_rw [IsLocalization.eq_iff_exists N T, IsLocalization.eq_iff_exists M S]
        -- ⊢ (∃ c, ↑c * (y₁ * ↑s₂) = ↑c * (y₂ * ↑s₁)) ↔ ∃ a c, ↑c * (↑a * (y₁ * ↑s₂)) = ↑ …
        constructor
        -- ⊢ (∃ c, ↑c * (y₁ * ↑s₂) = ↑c * (y₂ * ↑s₁)) → ∃ a c, ↑c * (↑a * (y₁ * ↑s₂)) = ↑ …
        · rintro ⟨a, e⟩
          -- ⊢ ∃ a c, ↑c * (↑a * (y₁ * ↑s₂)) = ↑c * (↑a * (y₂ * ↑s₁))
          exact ⟨a, 1, by convert e using 1 <;> simp⟩
          -- 🎉 no goals
        · rintro ⟨a, b, e⟩
          -- ⊢ ∃ c, ↑c * (y₁ * ↑s₂) = ↑c * (y₂ * ↑s₁)
          exact ⟨a * (⟨_, h b.prop⟩ : N), by convert e using 1 <;> simp <;> ring⟩ }
          -- 🎉 no goals
#align is_localization.is_localization_of_submonoid_le IsLocalization.isLocalization_of_submonoid_le

/-- If `M ≤ N` are submonoids of `R` such that `∀ x : N, ∃ m : R, m * x ∈ M`, then the
localization at `N` is equal to the localizaton of `M`. -/
theorem isLocalization_of_is_exists_mul_mem (M N : Submonoid R) [IsLocalization M S] (h : M ≤ N)
    (h' : ∀ x : N, ∃ m : R, m * x ∈ M) : IsLocalization N S :=
  { map_units' := fun y => by
      obtain ⟨m, hm⟩ := h' y
      -- ⊢ IsUnit (↑(algebraMap R S) ↑y)
      have := IsLocalization.map_units S ⟨_, hm⟩
      -- ⊢ IsUnit (↑(algebraMap R S) ↑y)
      erw [map_mul] at this
      -- ⊢ IsUnit (↑(algebraMap R S) ↑y)
      exact (IsUnit.mul_iff.mp this).2
      -- 🎉 no goals
    surj' := fun z => by
      obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M z
      -- ⊢ ∃ x, z * ↑(algebraMap R S) ↑x.snd = ↑(algebraMap R S) x.fst
      exact ⟨⟨y, _, h s.prop⟩, e⟩
      -- 🎉 no goals
    eq_iff_exists' := fun {_ _} => by
      rw [IsLocalization.eq_iff_exists M]
      -- ⊢ (∃ c, ↑c * x✝¹ = ↑c * x✝) ↔ ∃ c, ↑c * x✝¹ = ↑c * x✝
      refine ⟨fun ⟨x, hx⟩ => ⟨⟨_, h x.prop⟩, hx⟩, ?_⟩
      -- ⊢ (∃ c, ↑c * x✝¹ = ↑c * x✝) → ∃ c, ↑c * x✝¹ = ↑c * x✝
      rintro ⟨x, h⟩
      -- ⊢ ∃ c, ↑c * x✝¹ = ↑c * x✝
      obtain ⟨m, hm⟩ := h' x
      -- ⊢ ∃ c, ↑c * x✝¹ = ↑c * x✝
      refine ⟨⟨_, hm⟩, ?_⟩
      -- ⊢ ↑{ val := m * ↑x, property := hm } * x✝¹ = ↑{ val := m * ↑x, property := hm  …
      simp [h, mul_assoc] }
      -- 🎉 no goals
#align is_localization.is_localization_of_is_exists_mul_mem IsLocalization.isLocalization_of_is_exists_mul_mem

end LocalizationLocalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

theorem isFractionRing_of_isLocalization (S T : Type*) [CommRing S] [CommRing T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] [IsLocalization M S] [IsFractionRing R T]
    (hM : M ≤ nonZeroDivisors R) : IsFractionRing S T := by
  have := isLocalization_of_submonoid_le S T M (nonZeroDivisors R) hM
  -- ⊢ IsFractionRing S T
  refine @isLocalization_of_is_exists_mul_mem _ _ _ _ _ _ _ this ?_ ?_
  -- ⊢ Submonoid.map (algebraMap R S) (nonZeroDivisors R) ≤ nonZeroDivisors S
  · exact map_nonZeroDivisors_le M S
    -- 🎉 no goals
  · rintro ⟨x, hx⟩
    -- ⊢ ∃ m, m * ↑{ val := x, property := hx } ∈ Submonoid.map (algebraMap R S) (non …
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M x
    -- ⊢ ∃ m, m * ↑{ val := x, property := hx } ∈ Submonoid.map (algebraMap R S) (non …
    use algebraMap R S s
    -- ⊢ ↑(algebraMap R S) ↑s * ↑{ val := x, property := hx } ∈ Submonoid.map (algebr …
    rw [mul_comm, Subtype.coe_mk, e]
    -- ⊢ ↑(algebraMap R S) (y, s).fst ∈ Submonoid.map (algebraMap R S) (nonZeroDiviso …
    refine' Set.mem_image_of_mem (algebraMap R S) _
    -- ⊢ (y, s).fst ∈ ↑(nonZeroDivisors R)
    intro z hz
    -- ⊢ z = 0
    apply IsLocalization.injective S hM
    -- ⊢ ↑(algebraMap R S) z = ↑(algebraMap R S) 0
    rw [map_zero]
    -- ⊢ ↑(algebraMap R S) z = 0
    apply hx
    -- ⊢ ↑(algebraMap R S) z * x = 0
    rw [← (map_units S s).mul_left_inj, mul_assoc, e, ← map_mul, hz, map_zero,
      zero_mul]
#align is_fraction_ring.is_fraction_ring_of_is_localization IsFractionRing.isFractionRing_of_isLocalization

theorem isFractionRing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization M S] [IsFractionRing R T] : IsFractionRing S T := by
  haveI := IsFractionRing.nontrivial R T
  -- ⊢ IsFractionRing S T
  haveI := (algebraMap S T).domain_nontrivial
  -- ⊢ IsFractionRing S T
  apply isFractionRing_of_isLocalization M S T
  -- ⊢ M ≤ nonZeroDivisors R
  intro x hx
  -- ⊢ x ∈ nonZeroDivisors R
  rw [mem_nonZeroDivisors_iff_ne_zero]
  -- ⊢ x ≠ 0
  intro hx'
  -- ⊢ False
  apply @zero_ne_one S
  -- ⊢ 0 = 1
  rw [← (algebraMap R S).map_one, ← @mk'_one R _ M, @comm _ Eq, mk'_eq_zero_iff]
  -- ⊢ ∃ m, ↑m * 1 = 0
  exact ⟨⟨x, hx⟩, by simp [hx']⟩
  -- 🎉 no goals
#align is_fraction_ring.is_fraction_ring_of_is_domain_of_is_localization IsFractionRing.isFractionRing_of_isDomain_of_isLocalization

end IsFractionRing
