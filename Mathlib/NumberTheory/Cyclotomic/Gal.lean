/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of `K(ζₙ)` and `(ZMod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

## Main results

* `IsPrimitiveRoot.autToPow_injective`: `IsPrimitiveRoot.autToPow` is injective
  in the case that it's considered over a cyclotomic field extension.
* `IsCyclotomicExtension.autEquivPow`: If the `n`th cyclotomic polynomial is irreducible in `K`,
  then `IsPrimitiveRoot.autToPow` is a `MulEquiv` (for example, in `ℚ` and certain `𝔽ₚ`).
* `galXPowEquivUnitsZMod`, `galCyclotomicEquivUnitsZMod`: Repackage
  `IsCyclotomicExtension.autEquivPow` in terms of `Polynomial.Gal`.
* `IsCyclotomicExtension.Aut.commGroup`: Cyclotomic extensions are abelian.

## References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

## TODO

* We currently can get away with the fact that the power of a primitive root is a primitive root,
  but the correct long-term solution for computing other explicit Galois groups is creating
  `PowerBasis.map_conjugate`; but figuring out the exact correct assumptions + proof for this is
  mathematically nontrivial. (Current thoughts: the correct condition is that the annihilating
  ideal of both elements is equal. This may not hold in an ID, and definitely holds in an ICD.)

-/


variable {n : ℕ} [NeZero n] (K : Type*) [Field K] {L : Type*} {μ : L}

open Polynomial IsCyclotomicExtension

open scoped Cyclotomic

namespace IsPrimitiveRoot

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

/-- `IsPrimitiveRoot.autToPow` is injective in the case that it's considered over a cyclotomic
field extension. -/
theorem autToPow_injective : Function.Injective <| hμ.autToPow K := by
  intro f g hfg
  apply_fun Units.val at hfg
  simp only [IsPrimitiveRoot.coe_autToPow_apply] at hfg
  generalize_proofs hf' hg' at hfg
  have hf := hf'.choose_spec
  have hg := hg'.choose_spec
  generalize_proofs hζ at hf hg
  suffices f (hμ.toRootsOfUnity : Lˣ) = g (hμ.toRootsOfUnity : Lˣ) by
    apply AlgEquiv.coe_algHom_injective
    apply (hμ.powerBasis K).algHom_ext
    exact this
  rw [ZMod.natCast_eq_natCast_iff] at hfg
  refine (hf.trans ?_).trans hg.symm
  rw [← rootsOfUnity.coe_pow _ hf'.choose, ← rootsOfUnity.coe_pow _ hg'.choose]
  congr 2
  rw [pow_eq_pow_iff_modEq]
  convert hfg
  conv => enter [2]; rw [hμ.eq_orderOf, ← hμ.val_toRootsOfUnity_coe]
  rw [orderOf_units, Subgroup.orderOf_coe]

end IsPrimitiveRoot

namespace IsCyclotomicExtension

@[deprecated (since := "2025-06-26")]
alias Aut.commGroup := isMulCommutative

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

variable {K} (L)

/-- The `MulEquiv` that takes an automorphism `f` to the element `k : (ZMod n)ˣ` such that
  `f μ = μ ^ k` for any root of unity `μ`. A strengthening of `IsPrimitiveRoot.autToPow`. -/
@[simps]
noncomputable def autEquivPow (h : Irreducible (cyclotomic n K)) : (L ≃ₐ[K] L) ≃* (ZMod n)ˣ :=
  let hζ := zeta_spec n K L
  let hμ t := hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime t)
  { (zeta_spec n K L).autToPow K with
    invFun := fun t =>
      (hζ.powerBasis K).equivOfMinpoly ((hμ t).powerBasis K)
        (by
          haveI := IsCyclotomicExtension.neZero' n K L
          simp only [IsPrimitiveRoot.powerBasis_gen]
          have hr :=
            IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
              ((zeta_spec n K L).pow_of_coprime _ (ZMod.val_coe_unit_coprime t)) h
          exact ((zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr)
    left_inv := fun f => by
      simp only [MonoidHom.toFun_eq_coe]
      apply AlgEquiv.coe_algHom_injective
      apply (hζ.powerBasis K).algHom_ext
      simp only [AlgHom.coe_coe]
      rw [PowerBasis.equivOfMinpoly_gen]
      simp only [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.autToPow_spec]
    right_inv := fun x => by
      simp only [MonoidHom.toFun_eq_coe]
      generalize_proofs _ h
      have key := hζ.autToPow_spec K ((hζ.powerBasis K).equivOfMinpoly ((hμ x).powerBasis K) h)
      have := (hζ.powerBasis K).equivOfMinpoly_gen ((hμ x).powerBasis K) h
      rw [hζ.powerBasis_gen K] at this
      rw [this, IsPrimitiveRoot.powerBasis_gen] at key
      -- Porting note: was
      -- `rw ← hζ.coe_to_roots_of_unity_coe at key {occs := occurrences.pos [1, 5]}`.
      conv at key =>
        congr; congr
        rw [← hζ.val_toRootsOfUnity_coe]
        rfl; rfl
        rw [← hζ.val_toRootsOfUnity_coe]
      simp only [← rootsOfUnity.coe_pow] at key
      replace key := rootsOfUnity.coe_injective key
      rw [pow_eq_pow_iff_modEq, ← Subgroup.orderOf_coe, ← orderOf_units, hζ.val_toRootsOfUnity_coe,
        ← (zeta_spec n K L).eq_orderOf, ← ZMod.natCast_eq_natCast_iff] at key
      simp only [ZMod.natCast_val, ZMod.cast_id', id] at key
      exact Units.ext key }

variable (h : Irreducible (cyclotomic n K)) {L}

/-- Maps `μ` to the `AlgEquiv` that sends `IsCyclotomicExtension.zeta` to `μ`. -/
noncomputable def fromZetaAut : L ≃ₐ[K] L :=
  let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one
  (autEquivPow L h).symm <|
    ZMod.unitOfCoprime hζ.choose <|
      ((zeta_spec n K L).pow_iff_coprime (NeZero.pos _) hζ.choose).mp <| hζ.choose_spec.2.symm ▸ hμ

theorem fromZetaAut_spec : fromZetaAut hμ h (zeta n K L) = μ := by
  simp_rw [fromZetaAut, autEquivPow_symm_apply]
  generalize_proofs hζ h _ hμ _
  nth_rewrite 4 [← hζ.powerBasis_gen K]
  rw [PowerBasis.equivOfMinpoly_gen, hμ.powerBasis_gen K]
  convert h.choose_spec.2
  exact ZMod.val_cast_of_lt h.choose_spec.1

end IsCyclotomicExtension

section Gal

variable [Field L] [Algebra K L] [IsCyclotomicExtension {n} K L]
  (h : Irreducible (cyclotomic n K)) {K}

/-- `IsCyclotomicExtension.autEquivPow` repackaged in terms of `Gal`.
Asserts that the Galois group of `cyclotomic n K` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galCyclotomicEquivUnitsZMod : (cyclotomic n K).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
          (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (cyclotomic n K).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

/-- `IsCyclotomicExtension.autEquivPow` repackaged in terms of `Gal`.
Asserts that the Galois group of `X ^ n - 1` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galXPowEquivUnitsZMod : (X ^ n - 1 : K[X]).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
      (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (X ^ n - 1 : K[X]).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)

end Gal
