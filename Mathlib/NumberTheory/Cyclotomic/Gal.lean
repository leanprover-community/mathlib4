/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.PolynomialGaloisGroup

#align_import number_theory.cyclotomic.gal from "leanprover-community/mathlib"@"e3f4be1fcb5376c4948d7f095bec45350bfb9d1a"

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


variable {n : ℕ+} (K : Type*) [Field K] {L : Type*} {μ : L}

open Polynomial IsCyclotomicExtension

open scoped Cyclotomic

namespace IsPrimitiveRoot

variable [CommRing L] [IsDomain L] (hμ : IsPrimitiveRoot μ n) [Algebra K L]
  [IsCyclotomicExtension {n} K L]

/-- `IsPrimitiveRoot.autToPow` is injective in the case that it's considered over a cyclotomic
field extension. -/
theorem autToPow_injective : Function.Injective <| hμ.autToPow K := by
  intro f g hfg
  -- ⊢ f = g
  apply_fun Units.val at hfg
  -- ⊢ f = g
  simp only [IsPrimitiveRoot.coe_autToPow_apply] at hfg
  -- ⊢ f = g
  -- Porting note: was `generalize_proofs hf' hg' at hfg`
  revert hfg
  -- ⊢ ↑(Exists.choose (_ : ∃ m, ↑f ↑↑(toRootsOfUnity hμ) = ↑↑(toRootsOfUnity hμ) ^ …
  generalize_proofs hf' hg'
  -- ⊢ ↑(Exists.choose hf') = ↑(Exists.choose hg') → f = g
  intro hfg
  -- ⊢ f = g
  have hf := hf'.choose_spec
  -- ⊢ f = g
  have hg := hg'.choose_spec
  -- ⊢ f = g
  -- Porting note: was `generalize_proofs hζ at hf hg`
  revert hf hg
  -- ⊢ ↑f ↑↑(toRootsOfUnity hμ) = ↑↑(toRootsOfUnity hμ) ^ Exists.choose hf' → ↑g ↑↑ …
  generalize_proofs hζ
  -- ⊢ ↑f ↑↑(toRootsOfUnity hμ) = ↑↑(toRootsOfUnity hμ) ^ Exists.choose hf' → ↑g ↑↑ …
  intro hf hg
  -- ⊢ f = g
  suffices f (hμ.toRootsOfUnity : Lˣ) = g (hμ.toRootsOfUnity : Lˣ) by
    apply AlgEquiv.coe_algHom_injective
    apply (hμ.powerBasis K).algHom_ext
    exact this
  rw [ZMod.eq_iff_modEq_nat] at hfg
  -- ⊢ ↑f ↑↑(toRootsOfUnity hμ) = ↑g ↑↑(toRootsOfUnity hμ)
  refine' (hf.trans _).trans hg.symm
  -- ⊢ ↑↑(toRootsOfUnity hμ) ^ Exists.choose hf' = ↑↑(toRootsOfUnity hμ) ^ Exists.c …
  rw [← rootsOfUnity.coe_pow _ hf'.choose, ← rootsOfUnity.coe_pow _ hg'.choose]
  -- ⊢ ↑↑(toRootsOfUnity hμ ^ Exists.choose hf') = ↑↑(toRootsOfUnity hμ ^ Exists.ch …
  congr 2
  -- ⊢ toRootsOfUnity hμ ^ Exists.choose hf' = toRootsOfUnity hμ ^ Exists.choose hg'
  rw [pow_eq_pow_iff_modEq]
  -- ⊢ Exists.choose hf' ≡ Exists.choose hg' [MOD orderOf (toRootsOfUnity hμ)]
  convert hfg
  -- ⊢ orderOf (toRootsOfUnity hμ) = ↑n
  rw [hμ.eq_orderOf]
  -- ⊢ orderOf (toRootsOfUnity hμ) = orderOf μ
  -- Porting note: was `{occs := occurrences.pos [2]}`
  conv_rhs => rw [← hμ.val_toRootsOfUnity_coe]
  -- ⊢ orderOf (toRootsOfUnity hμ) = orderOf ↑↑(toRootsOfUnity hμ)
  rw [orderOf_units, orderOf_subgroup]
  -- 🎉 no goals
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

/-- The `MulEquiv` that takes an automorphism `f` to the element `k : (ZMod n)ˣ` such that
  `f μ = μ ^ k` for any root of unity `μ`. A strengthening of `IsPrimitiveRoot.autToPow`. -/
@[simps]
noncomputable def autEquivPow : (L ≃ₐ[K] L) ≃* (ZMod n)ˣ :=
  let hζ := zeta_spec n K L
  let hμ t := hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime t)
  { (zeta_spec n K L).autToPow K with
    invFun := fun t =>
      (hζ.powerBasis K).equivOfMinpoly ((hμ t).powerBasis K)
        (by
          haveI := IsCyclotomicExtension.neZero' n K L
          -- ⊢ minpoly K (IsPrimitiveRoot.powerBasis K hζ).gen = minpoly K (IsPrimitiveRoot …
          simp only [IsPrimitiveRoot.powerBasis_gen]
          -- ⊢ minpoly K (zeta n K L) = minpoly K (zeta n K L ^ ZMod.val ↑t)
          have hr :=
            IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
              ((zeta_spec n K L).pow_of_coprime _ (ZMod.val_coe_unit_coprime t)) h
          exact ((zeta_spec n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr)
          -- 🎉 no goals
    left_inv := fun f => by
      simp only [MonoidHom.toFun_eq_coe]
      -- ⊢ PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K hζ) (IsPrimitiveRoot …
      apply AlgEquiv.coe_algHom_injective
      -- ⊢ ↑(PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K hζ) (IsPrimitiveRo …
      apply (hζ.powerBasis K).algHom_ext
      -- ⊢ ↑↑(PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K hζ) (IsPrimitiveR …
-- Porting note: the proof is slightly different because of coercions.
      simp only [AlgHom.coe_coe]
      -- ⊢ ↑(PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K hζ) (IsPrimitiveRo …
      rw [PowerBasis.equivOfMinpoly_gen]
      -- ⊢ (IsPrimitiveRoot.powerBasis K (_ : IsPrimitiveRoot (zeta n K L ^ ZMod.val ↑( …
      simp only [IsPrimitiveRoot.powerBasis_gen, IsPrimitiveRoot.autToPow_spec]
      -- 🎉 no goals
    right_inv := fun x => by
      simp only [MonoidHom.toFun_eq_coe]
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K (_ : IsPrimitiveRoot (zeta n K L) ↑n)) (PowerBa …
      generalize_proofs _ h
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
      have key := hζ.autToPow_spec K ((hζ.powerBasis K).equivOfMinpoly ((hμ x).powerBasis K) h)
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
      have := (hζ.powerBasis K).equivOfMinpoly_gen ((hμ x).powerBasis K) h
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
      rw [hζ.powerBasis_gen K] at this
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
      rw [this, IsPrimitiveRoot.powerBasis_gen] at key
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
-- Porting note: was `rw ← hζ.coe_to_roots_of_unity_coe at key {occs := occurrences.pos [1, 5]}`.
      conv at key =>
        congr; congr
        rw [← hζ.val_toRootsOfUnity_coe]
        rfl; rfl
        rw [← hζ.val_toRootsOfUnity_coe]
      simp only [← rootsOfUnity.coe_pow] at key
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
      replace key := rootsOfUnity.coe_injective key
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
      rw [pow_eq_pow_iff_modEq, ← orderOf_subgroup, ← orderOf_units, hζ.val_toRootsOfUnity_coe, ←
        (zeta_spec n K L).eq_orderOf, ← ZMod.eq_iff_modEq_nat] at key
      simp only [ZMod.nat_cast_val, ZMod.cast_id', id.def] at key
      -- ⊢ ↑(IsPrimitiveRoot.autToPow K h✝) (PowerBasis.equivOfMinpoly (IsPrimitiveRoot …
      exact Units.ext key }
      -- 🎉 no goals
#align is_cyclotomic_extension.aut_equiv_pow IsCyclotomicExtension.autEquivPow

variable {L}

/-- Maps `μ` to the `AlgEquiv` that sends `IsCyclotomicExtension.zeta` to `μ`. -/
noncomputable def fromZetaAut : L ≃ₐ[K] L :=
  let hζ := (zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one n.pos
  (autEquivPow L h).symm <|
    ZMod.unitOfCoprime hζ.choose <|
      ((zeta_spec n K L).pow_iff_coprime n.pos hζ.choose).mp <| hζ.choose_spec.2.symm ▸ hμ
#align is_cyclotomic_extension.from_zeta_aut IsCyclotomicExtension.fromZetaAut

theorem fromZetaAut_spec : fromZetaAut hμ h (zeta n K L) = μ := by
  simp_rw [fromZetaAut, autEquivPow_symm_apply]
  -- ⊢ ↑(PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K (_ : IsPrimitiveRo …
-- Porting note: `generalize_proofs` did not generalize the same proofs, making the proof different.
  generalize_proofs h1 h2
  -- ⊢ ↑(PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K (_ : IsPrimitiveRo …
  nth_rewrite 4 [← (zeta_spec n K L).powerBasis_gen K]
  -- ⊢ ↑(PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K (_ : IsPrimitiveRo …
  have := Exists.choose_spec ((zeta_spec n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one n.pos)
  -- ⊢ ↑(PowerBasis.equivOfMinpoly (IsPrimitiveRoot.powerBasis K (_ : IsPrimitiveRo …
  rw [PowerBasis.equivOfMinpoly_gen, h1.powerBasis_gen K, ZMod.coe_unitOfCoprime,
    ZMod.val_cast_of_lt this.1]
  exact this.2
  -- 🎉 no goals
#align is_cyclotomic_extension.from_zeta_aut_spec IsCyclotomicExtension.fromZetaAut_spec

end IsCyclotomicExtension

section Gal

variable [Field L] (hμ : IsPrimitiveRoot μ n) [Algebra K L] [IsCyclotomicExtension {n} K L]
  (h : Irreducible (cyclotomic n K)) {K}

/-- `IsCyclotomicExtension.autEquivPow` repackaged in terms of `gal`.
Asserts that the Galois group of `cyclotomic n K` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galCyclotomicEquivUnitsZMod : (cyclotomic n K).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
          (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (cyclotomic n K).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)
#align gal_cyclotomic_equiv_units_zmod galCyclotomicEquivUnitsZMod

/-- `IsCyclotomicExtension.autEquivPow` repackaged in terms of `gal`.
Asserts that the Galois group of `X ^ n - 1` is equivalent to `(ZMod n)ˣ`
if `cyclotomic n K` is irreducible in the base field. -/
noncomputable def galXPowEquivUnitsZMod : (X ^ (n : ℕ) - 1 : K[X]).Gal ≃* (ZMod n)ˣ :=
  (AlgEquiv.autCongr
      (IsSplittingField.algEquiv L _ : L ≃ₐ[K] (X ^ (n : ℕ) - 1 : K[X]).SplittingField)).symm.trans
    (IsCyclotomicExtension.autEquivPow L h)
set_option linter.uppercaseLean3 false
#align gal_X_pow_equiv_units_zmod galXPowEquivUnitsZMod

end Gal
