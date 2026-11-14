/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.Quotient

/-!
# The Teichmüller character

Let `I` be an ideal of a commutative ring `R` such that reduction modulo `I` is a bijection from
the `n`-th roots of unity of `R` onto the units of `R ⧸ I`, a property recorded by the class
`Ideal.HasTeichmullerLift`. Inverting that bijection and extending by zero gives a multiplicative
character of `R ⧸ I` with values in `R`, the Teichmüller character, which is a multiplicative
section of the reduction map.

## Main definitions

* `Ideal.HasTeichmullerLift`: the property that every unit of `R ⧸ I` is the reduction of a
  unique `n`-th root of unity of `R`, its Teichmüller lift.
* `Ideal.HasTeichmullerLift.equiv`: the isomorphism, given by reduction modulo `I`, from the `n`-th
  roots of unity of `R` onto the units of `R ⧸ I`.
* `MulChar.teichmuller`: the Teichmüller character of `R ⧸ I`, with values in `R`.

## Main results

* `MulChar.teichmuller_mk_coe`: the Teichmüller character sends the reduction of an `n`-th root of
  unity back to it.
* `MulChar.mk_teichmuller_apply_coe`, `MulChar.mk_teichmuller_apply`: the Teichmüller character is
  a section of the reduction map on units, and everywhere when `I` is maximal.
* `MulChar.orderOf_teichmuller`: the Teichmüller character has order `n`.
* `MulChar.exists_teichmuller_zpow_apply_eq_pow`: over a domain containing a primitive `n`-th root
  of unity `ζ`, the values of the powers of the Teichmüller character at units are powers of `ζ`.
* `MulChar.map_ringHomComp_teichmuller_zpow_apply`: if `σ (f ζ) = f ζ ^ m`, then `σ` sends
  `(teichmuller I n ^ a).ringHomComp f` to `(teichmuller I n ^ (a * m)).ringHomComp f`.

## Tags

Teichmüller character, multiplicative character, roots of unity

-/

public section

variable {R : Type*} [CommRing R]

/-- The ideal `I` has Teichmüller lifts of order `n` if every unit of `R ⧸ I` is the reduction of
a unique `n`-th root of unity of `R`. -/
class Ideal.HasTeichmullerLift (I : Ideal R) (n : ℕ) : Prop where
  bijective_rootsOfUnityMapQuot : Function.Bijective (I.rootsOfUnityMapQuot n)

/-- If the domain `R` has enough `n`-th roots of unity, the integer `n` does not lie in `I` and
the group of units of `R ⧸ I` has order `n`, then `I` has Teichmüller lifts of order `n`. -/
theorem Ideal.HasTeichmullerLift.of_card [IsDomain R] {I : Ideal R} {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity R n] (hn : (n : R) ∉ I) (hcard : Nat.card (R ⧸ I)ˣ = n) :
    I.HasTeichmullerLift n :=
  have : Finite (R ⧸ I)ˣ := Nat.finite_of_card_ne_zero (hcard ▸ NeZero.ne n)
  ⟨(Nat.bijective_iff_injective_and_card _).mpr ⟨I.rootsOfUnityMapQuot_injective_of_notMem hn, by
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity, hcard]⟩⟩

/-- If the domain `R` has enough `n`-th roots of unity and the units of the quotient of `R` by the
prime ideal `I` form a group of order `n`, then `I` has Teichmüller lifts of order `n`. -/
theorem Ideal.HasTeichmullerLift.of_card_of_isPrime [IsDomain R] {I : Ideal R} {n : ℕ} [NeZero n]
    [HasEnoughRootsOfUnity R n] [I.IsPrime] (hcard : Nat.card (R ⧸ I)ˣ = n) :
    I.HasTeichmullerLift n := by
  refine .of_card (fun hmem ↦ ?_) hcard
  replace hmem : (n : R ⧸ I) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have : NeZero (ringChar (R ⧸ I)) :=
    ⟨fun h ↦ NeZero.ne n <| Nat.zero_dvd.mp <| h ▸ ringChar.dvd hmem⟩
  have : Fact (ringChar (R ⧸ I)).Prime := CharP.char_is_prime_of_pos (R ⧸ I) _
  have : Finite (R ⧸ I)ˣ := Nat.finite_of_card_ne_zero (hcard ▸ NeZero.ne n)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (R ⧸ I)ˣ)
  exact ExpChar.not_dvd_orderOf (ringChar (R ⧸ I)) CharP.ringChar_ne_one g
    (isOfFinOrder_of_finite g) (by rwa [hg, hcard, ← ringChar.spec])

/-- If `I` has Teichmüller lifts of order `n`, reduction modulo `I` is an isomorphism from the
`n`-th roots of unity of `R` onto the units of `R ⧸ I`. -/
noncomputable def Ideal.HasTeichmullerLift.equiv (I : Ideal R) (n : ℕ)
    [h : I.HasTeichmullerLift n] : rootsOfUnity n R ≃* (R ⧸ I)ˣ :=
  MulEquiv.ofBijective _ h.bijective_rootsOfUnityMapQuot

@[simp]
theorem Ideal.HasTeichmullerLift.equiv_apply (I : Ideal R) (n : ℕ) [I.HasTeichmullerLift n]
    (ζ : rootsOfUnity n R) : equiv I n ζ = I.rootsOfUnityMapQuot n ζ := by
  simp [equiv]

namespace MulChar

/-- The Teichmüller character of `R ⧸ I`: the multiplicative character with values in `R`
obtained by inverting the reduction of the `n`-th roots of unity and extending by zero. -/
noncomputable def teichmuller (I : Ideal R) (n : ℕ) [I.HasTeichmullerLift n] :
    MulChar (R ⧸ I) R :=
  MulChar.ofUnitHom <| (rootsOfUnity n R).subtype.comp
    (Ideal.HasTeichmullerLift.equiv I n).symm.toMonoidHom

variable {n : ℕ} {I : Ideal R} [I.HasTeichmullerLift n]

/-- The value of the Teichmüller character at a unit. -/
theorem teichmuller_apply_coe (x : (R ⧸ I)ˣ) :
    teichmuller I n x = ((Ideal.HasTeichmullerLift.equiv I n).symm x : Rˣ) := by
  simp [teichmuller]

/-- The Teichmüller character sends the reduction of an `n`-th root of unity back to it. -/
@[simp]
theorem teichmuller_mk_coe (ζ : rootsOfUnity n R) :
    teichmuller I n (Ideal.Quotient.mk I ((ζ : Rˣ) : R)) = ((ζ : Rˣ) : R) := by
  rw [← Ideal.coe_rootsOfUnityMapQuot, teichmuller_apply_coe,
    ← Ideal.HasTeichmullerLift.equiv_apply, MulEquiv.symm_apply_apply]

/-- The values of the Teichmüller character at units are `n`-th roots of unity. -/
@[simp]
theorem teichmuller_apply_coe_pow_eq_one (x : (R ⧸ I)ˣ) : teichmuller I n x ^ n = 1 := by
  rw [teichmuller_apply_coe, ← Units.val_pow_eq_pow_val,
    (mem_rootsOfUnity _ _).mp ((Ideal.HasTeichmullerLift.equiv I n).symm x).prop, Units.val_one]

/-- On units, the Teichmüller character is a section of the reduction map `R → R ⧸ I`. -/
@[simp]
theorem mk_teichmuller_apply_coe (x : (R ⧸ I)ˣ) :
    Ideal.Quotient.mk I (teichmuller I n x) = x := by
  obtain ⟨ζ, rfl⟩ := (Ideal.HasTeichmullerLift.equiv I n).surjective x
  simp

attribute [local instance] Ideal.Quotient.field in
/-- The Teichmüller character is a section of the reduction map `R → R ⧸ I`. -/
@[simp]
theorem mk_teichmuller_apply [I.IsMaximal] (x : R ⧸ I) :
    Ideal.Quotient.mk I (teichmuller I n x) = x := by
  obtain rfl | ⟨u, rfl⟩ := GroupWithZero.eq_zero_or_unit x
  · simp
  · exact mk_teichmuller_apply_coe u

/-- The Teichmüller character is nontrivial if and only if the group of units of `R ⧸ I` is
nontrivial. -/
theorem teichmuller_ne_one_iff : teichmuller I n ≠ 1 ↔ Nontrivial (R ⧸ I)ˣ := by
  rw [MulChar.ne_one_iff, nontrivial_iff_exists_ne 1]
  simp [teichmuller_apply_coe]

/-- The `n`-th power of the Teichmüller character is trivial. -/
@[simp]
theorem teichmuller_pow_eq_one : teichmuller I n ^ n = 1 := by
  ext x
  rw [MulChar.pow_apply_coe, teichmuller_apply_coe_pow_eq_one, MulChar.one_apply_coe]

/-- A power of the Teichmüller character whose exponent is divisible by `n` is trivial. -/
theorem teichmuller_zpow_eq_one_of_dvd {a : ℤ} (ha : (n : ℤ) ∣ a) : teichmuller I n ^ a = 1 := by
  obtain ⟨c, rfl⟩ := ha
  rw [zpow_mul, zpow_natCast, teichmuller_pow_eq_one, one_zpow]

/-- The Teichmüller character has order `n`. -/
theorem orderOf_teichmuller [NeZero n] [HasEnoughRootsOfUnity R n] :
    orderOf (teichmuller I n) = n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot R n
  refine (orderOf_eq_iff (NeZero.pos _)).mpr ⟨teichmuller_pow_eq_one,
    fun m hmn hm ↦ MulChar.ne_one_iff.mpr ⟨I.rootsOfUnityMapQuot n hζ.toRootsOfUnity, ?_⟩⟩
  rw [MulChar.pow_apply_coe, Ideal.coe_rootsOfUnityMapQuot, teichmuller_mk_coe,
    IsPrimitiveRoot.val_toRootsOfUnity_coe, ne_eq, hζ.pow_eq_one_iff_dvd]
  exact Nat.not_dvd_of_pos_of_lt hm hmn

/-- The values at units of the powers of the Teichmüller character are powers of a primitive
`n`-th root of unity `ζ`. -/
theorem exists_teichmuller_zpow_apply_eq_pow [IsDomain R] [NeZero n] {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) (a : ℤ) (x : (R ⧸ I)ˣ) :
    ∃ m < n, (teichmuller I n ^ a) x = ζ ^ m := by
  obtain ⟨k, hk, hk'⟩ := hζ.eq_pow_of_pow_eq_one (ξ := (teichmuller I n ^ a) x) <| by
    rw [← MulChar.pow_apply_coe, ← zpow_natCast, ← zpow_mul,
      teichmuller_zpow_eq_one_of_dvd (dvd_mul_left _ _), MulChar.one_apply_coe]
  exact ⟨k, hk, hk'.symm⟩

/-- A ring homomorphism sending `ζ` to `ζ ^ m` multiplies by `m` the exponent of a power of the
Teichmüller character. -/
theorem map_ringHomComp_teichmuller_zpow_apply [IsDomain R] [NeZero n] {S : Type*}
    [CommRing S] {F : Type*} [FunLike F S S] [MonoidWithZeroHomClass F S S] (σ : F) (f : R →+* S)
    (m : ℕ) {ζ : R} (hζ : IsPrimitiveRoot ζ n) (hσ : σ (f ζ) = (f ζ) ^ m) (a : ℤ)
    (x : R ⧸ I) :
    σ ((teichmuller I n ^ a).ringHomComp f x) = (teichmuller I n ^ (a * m)).ringHomComp f x := by
  by_cases hx : IsUnit x
  · lift x to (R ⧸ I)ˣ using hx
    obtain ⟨t, -, ht⟩ := exists_teichmuller_zpow_apply_eq_pow hζ a x
    rw [MulChar.ringHomComp_apply, ht, map_pow, map_pow, hσ, MulChar.ringHomComp_apply,
      zpow_mul, zpow_natCast, MulChar.pow_apply_coe, ht, map_pow, map_pow, pow_right_comm]
  · simp [MulChar.map_nonunit _ hx]

end MulChar
