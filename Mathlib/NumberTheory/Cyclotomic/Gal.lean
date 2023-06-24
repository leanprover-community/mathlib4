/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module number_theory.cyclotomic.gal
! leanprover-community/mathlib commit e3f4be1fcb5376c4948d7f095bec45350bfb9d1a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of `K(ζₙ)` and `(zmod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

## Main results

* `is_primitive_root.aut_to_pow_injective`: `is_primitive_root.aut_to_pow` is injective
  in the case that it's considered over a cyclotomic field extension.
* `is_cyclotomic_extension.aut_equiv_pow`: If the `n`th cyclotomic polynomial is irreducible in `K`,
  then `is_primitive_root.aut_to_pow` is a `mul_equiv` (for example, in `ℚ` and certain `𝔽ₚ`).
* `gal_X_pow_equiv_units_zmod`, `gal_cyclotomic_equiv_units_zmod`: Repackage
  `is_cyclotomic_extension.aut_equiv_pow` in terms of `polynomial.gal`.
* `is_cyclotomic_extension.aut.comm_group`: Cyclotomic extensions are abelian.

## References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

## TODO

* We currently can get away with the fact that the power of a primitive root is a primitive root,
  but the correct long-term solution for computing other explicit Galois groups is creating
  `power_basis.map_conjugate`; but figuring out the exact correct assumptions + proof for this is
  mathematically nontrivial. (Current thoughts: the correct condition is that the annihilating
  ideal of both elements is equal. This may not hold in an ID, and definitely holds in an ICD.)

-/


variable {n : ℕ+} (K : Type _) [Field K] {L : Type _} {μ : L}

open Polynomial IsCyclotomicExtension

open scoped Cyclotomic

namespace IsPrimitiveRoot

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([2]) } -/
/-- `is_primitive_root.aut_to_pow` is injective in the case that it's considered over a cyclotomic
field extension. -/
theorem autToPow_injective : Function.Injective <| hμ.autToPow K := by
  intro f g hfg
  apply_fun Units.val at hfg
  simp only [IsPrimitiveRoot.coe_autToPow_apply] at hfg
  -- Porting note: was `generalize_proofs hf' hg' at hfg`
  revert hfg
  generalize_proofs hf' hg'
  intro hfg
  have hf := hf'.choose_spec
  have hg := hg'.choose_spec
  -- Porting note: was `generalize_proofs hζ at hf hg`
  revert hf hg
  generalize_proofs hζ
  intro hf hg
  suffices f (hμ.toRootsOfUnity : Lˣ) = g (hμ.toRootsOfUnity : Lˣ) by
    apply AlgEquiv.coe_algHom_injective
    apply (hμ.powerBasis K).algHom_ext
    exact this
  rw [ZMod.eq_iff_modEq_nat] at hfg
  refine' (hf.trans _).trans hg.symm
  rw [← rootsOfUnity.coe_pow _ hf'.choose, ← rootsOfUnity.coe_pow _ hg'.choose]
  congr 2
  rw [pow_eq_pow_iff_modEq]
  convert hfg
  rw [hμ.eq_orderOf]
  -- Porting note: was `{occs := occurrences.pos [2]}`
  conv_rhs => rw [← hμ.toRootsOfUnity_coe_val]
  rw [orderOf_units, orderOf_subgroup]
#align is_primitive_root.aut_to_pow_injective IsPrimitiveRoot.autToPow_injective

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

/-- Cyclotomic extensions are abelian. -/
noncomputable def Aut.commGroup : CommGroup (L ≃ₐ[K] L) :=
  ((zeta_spec n K L).autToPow_injective K).commGroup _ (map_one _) (map_mul _) (map_inv _)
    (map_div _) (map_pow _) (map_zpow _)
#align is_cyclotomic_extension.aut.comm_group IsCyclotomicExtension.Aut.commGroup

variable (h : Irreducible (cyclotomic n K)) {K} (L)

/-- The `mul_equiv` that takes an automorphism `f` to the element `k : (zmod n)ˣ` such that
  `f μ = μ ^ k` for any root of unity `μ`. A  strengthening of `is_primitive_root.aut_to_pow`. -/
@[simps]
noncomputable def autEquivPow : (L ≃ₐ[K] L) ≃* (ZMod n)ˣ :=
  let hζ := zeta_spec n K L
  let hμ t := hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime t)
  { (zeta_spec n K L).autToPow K with
    invFun := fun t =>
      (hζ.powerBasis K).equivOfMinpoly ((hμ t).powerBasis K)
        (by
          haveI := IsCyclotomicExtension.ne_zero' n K L
          simp only [IsPrimitiveRoot.powerBasis_gen]
          have hr :=
            IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
              ((zeta_spec n K L).pow_of_coprime _ (ZMod.val_coe_unit_coprime t)) h
          exact ((zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr)
    left_inv := fun f => by
      simp only [MonoidHom.toFun_eq_coe]
      apply AlgEquiv.coe_algHom_injective
      apply (hζ.powerBasis K).algHom_ext
-- Porting note: the proof is slightly different because of coercions.
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
-- Porting note: was `rw ← hζ.coe_to_roots_of_unity_coe at key {occs := occurrences.pos [1, 5]}`.
      conv at key =>
        congr; congr
        rw [← hζ.toRootsOfUnity_coe_val]
        rfl; rfl
        rw [← hζ.toRootsOfUnity_coe_val]
      simp only [← rootsOfUnity.coe_pow] at key
      replace key := rootsOfUnity.coe_injective key
      rw [pow_eq_pow_iff_modEq, ← orderOf_subgroup, ← orderOf_units, hζ.toRootsOfUnity_coe_val, ←
        (zeta_spec n K L).eq_orderOf, ← ZMod.eq_iff_modEq_nat] at key
      simp only [ZMod.nat_cast_val, ZMod.cast_id', id.def] at key
      exact Units.ext key }
#align is_cyclotomic_extension.aut_equiv_pow IsCyclotomicExtension.autEquivPow

variable {L}

/-- Maps `μ` to the `alg_equiv` that sends `is_cyclotomic_extension.zeta` to `μ`. -/
noncomputable def fromZetaAut : L ≃ₐ[K] L :=
  let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one n.pos
  (autEquivPow L h).symm <|
    ZMod.unitOfCoprime hζ.choose <|
      ((zeta_spec n K L).pow_iff_coprime n.pos hζ.choose).mp <| hζ.choose_spec.2.symm ▸ hμ
#align is_cyclotomic_extension.from_zeta_aut IsCyclotomicExtension.fromZetaAut

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([4]) } -/
theorem fromZetaAut_spec : fromZetaAut hμ h (zeta n K L) = μ := by
  simp_rw [fromZetaAut, autEquivPow_symm_apply]
  generalize_proofs hζ h _ hμ _
  rw [← hζ.powerBasis_gen K]
  rw [PowerBasis.equivOfMinpoly_gen, hμ.powerBasis_gen K]
  convert h.choose_spec.choose_spec
  exact ZMod.val_cast_of_lt h.some_spec.some
#align is_cyclotomic_extension.from_zeta_aut_spec IsCyclotomicExtension.fromZetaAut_spec

end IsCyclotomicExtension

section Gal

variable [Field L] (hμ : IsPrimitiveRoot μ n) [Algebra K L] [IsCyclotomicExtension {n} K L]
  (h : Irreducible (cyclotomic n K)) {K}

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`.
Asserts that the Galois group of `cyclotomic n K` is equivalent to `(zmod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galCyclotomicEquivUnitsZMod : (cyclotomic n K).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
          (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (cyclotomic n K).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)
#align gal_cyclotomic_equiv_units_zmod galCyclotomicEquivUnitsZMod

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`.
Asserts that the Galois group of `X ^ n - 1` is equivalent to `(zmod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galXPowEquivUnitsZMod : (X ^ (n : ℕ) - 1 : K[X]).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
      (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (X ^ (n : ℕ) - 1 : K[X]).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)
set_option linter.uppercaseLean3 false
#align gal_X_pow_equiv_units_zmod galXPowEquivUnitsZMod

end Gal
