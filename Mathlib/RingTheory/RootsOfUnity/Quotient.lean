/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Roots of unity in a quotient ring

For `I` an ideal of a commutative ring `R`, reduction modulo `I` sends the `n`-th roots of unity
of `R` to `n`-th roots of unity of `R ⧸ I`.

## Main definitions and results

* `Ideal.rootsOfUnityMapQuot`: the group homomorphism from the `n`-th roots of unity of `R` to
  `(R ⧸ I)ˣ` induced by the quotient map.

* `Ideal.rootsOfUnityMapQuot_injective_of_notMem`: if `R` is a domain and `(n : R) ∉ I`, then
  the map `Ideal.rootsOfUnityMapQuot` is injective.

* `Ideal.rootsOfUnityMapQuot_injective`: if the absolute norm of `I` is different from `1` and
  coprime with `n`, then the map `Ideal.rootsOfUnityMapQuot` is injective.

-/

public section

variable {R : Type*} [CommRing R] (I : Ideal R)

namespace Ideal

/-- The group homomorphism from the `n`-th roots of unity of `R` to `(R ⧸ I)ˣ` induced by the
quotient map `R → R ⧸ I`. -/
def rootsOfUnityMapQuot (n : ℕ) : rootsOfUnity n R →* (R ⧸ I)ˣ :=
  (rootsOfUnity n (R ⧸ I)).subtype.comp (restrictRootsOfUnity (Ideal.Quotient.mk I) n)

@[deprecated "use `coe_rootsOfUnityMapQuot`" (since := "2026-10-07")]
theorem rootsOfUnityMapQuot_apply (n : ℕ) {x : Rˣ} (hx : x ∈ rootsOfUnity n R) :
    rootsOfUnityMapQuot I n ⟨x, hx⟩ = Ideal.Quotient.mk I x := by rfl

@[simp]
theorem coe_rootsOfUnityMapQuot (n : ℕ) (ζ : rootsOfUnity n R) :
    (I.rootsOfUnityMapQuot n ζ : R ⧸ I) = Ideal.Quotient.mk I (ζ : Rˣ) := by
  rfl

/-- If `R` is a domain and `(n : R) ∉ I`, then reduction modulo `I` is injective on the `n`-th
roots of unity. -/
theorem rootsOfUnityMapQuot_injective_of_notMem [IsDomain R] {n : ℕ} (hn : (n : R) ∉ I) :
    Function.Injective (I.rootsOfUnityMapQuot n) := by
  refine (injective_iff_map_eq_one _).mpr fun ζ h ↦ ?_
  by_contra hζ
  obtain ⟨c, hc⟩ := sub_one_dvd_natCast_of_pow_eq_one (n := n)
    (by simpa using congr_arg Units.val ((mem_rootsOfUnity n _).mp ζ.prop))
    (fun h₁ ↦ hζ (Subtype.ext (Units.ext h₁)))
  refine hn (hc ▸ I.mul_mem_right c ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
  exact congr_arg Units.val h

end Ideal

section absNorm

variable [IsDedekindDomain R] [Module.Free ℤ R] [Module.Finite ℤ R] {I}

-- A nontrivial free `ℤ`-module is infinite; local to this section to supply `Infinite R`.
local instance : Infinite R := Module.Free.infinite ℤ R

namespace Ideal

/-- If the absolute norm of `I` is different from `1` and coprime with `n`, then reduction modulo
`I` is injective on the `n`-th roots of unity. -/
theorem rootsOfUnityMapQuot_injective (n : ℕ) (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime n) :
    Function.Injective (rootsOfUnityMapQuot I n) := by
  refine rootsOfUnityMapQuot_injective_of_notMem I fun hn ↦ hI₁ ?_
  refine (hI₂.pow_right (Module.finrank ℤ R)).eq_one_of_dvd ?_
  have := absNorm_dvd_norm_of_mem hn
  rw [← map_natCast (algebraMap ℤ R), Algebra.norm_algebraMap] at this
  exact_mod_cast this

theorem rootsOfUnityMapQuot_inj (n : ℕ) (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime n) {x y : rootsOfUnity n R} :
    rootsOfUnityMapQuot I n x = rootsOfUnityMapQuot I n y ↔ x = y :=
  (rootsOfUnityMapQuot_injective n hI₁ hI₂).eq_iff

end Ideal

/-- If the absolute norm of `I` is different from `1` and coprime with `n`, then the reduction
modulo `I` of a primitive `n`-th root of unity is a primitive `n`-th root of unity. -/
theorem IsPrimitiveRoot.idealQuotient_mk {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n)
    (hI₁ : Ideal.absNorm I ≠ 1) (hI₂ : (Ideal.absNorm I).Coprime n) :
    IsPrimitiveRoot (Ideal.Quotient.mk I ζ) n := by
  have : NeZero n := ⟨by
    rintro rfl
    exact hI₁ (Nat.coprime_zero_right _ |>.mp hI₂)⟩
  have h : IsPrimitiveRoot hζ.toRootsOfUnity n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp <| IsPrimitiveRoot.coe_units_iff.mp hζ
  simpa using IsPrimitiveRoot.coe_units_iff.mpr <|
    h.map_of_injective <| Ideal.rootsOfUnityMapQuot_injective n hI₁ hI₂

/-- If a primitive `n`-th root of unity, with `2 ≤ n`, is `1` modulo a proper ideal `I`, then the
absolute norm of `I` is not coprime with `n`. -/
theorem IsPrimitiveRoot.not_coprime_absNorm_of_mk_eq_one {n : ℕ} {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hI : Ideal.absNorm I ≠ 1)
    (h : Ideal.Quotient.mk I ζ = 1) : ¬ (Ideal.absNorm I).Coprime n := fun hc ↦
  (hζ.idealQuotient_mk hI hc).ne_one hn h

end absNorm
