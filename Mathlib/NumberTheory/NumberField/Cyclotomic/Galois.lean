/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.MulChar.Duality

/-!
# Galois theory for cyclotomic fields

In this file, we study the Galois theory of cyclotomic extensions of `ℚ`.

Let `n` be an integer. There is an isomorphism between `Gal(ℚ(ζₙ)/ℚ)` and `(ℤ/nℤ)ˣ` that sends `σ`
to `a_σ` such that `σ (ζₙ) = ζₙ ^ a_σ`.

Following [Washington][washington.cyclotomic], we define the bijection between subfields
of `ℚ(ζₙ)` and subgroups of the group `Xₙ` of Dirichlet characters of level `n` such that
`F` corresponds to `Y` iff the subgroup `H` of `(ℤ/nℤ)ˣ` corresponding to `F` by the above
isomorphism is the orthogonal of `Y` for the nondegenerate pairing on `(ℤ/nℤ)ˣ × Xₙ`
defined by `(n, χ) ↦ χ n`.

## Main definitions and results

- `IsCyclotomicExtension.Rat.galEquivZMod`: the isomorphism between `Gal(ℚ(ζₙ)/ℚ)` and `(ℤ/nℤ)ˣ`
  that sends `σ` to the class `a` such that `σ (ζₙ) = ζₙ ^ a`.
- `IsCyclotomicExtension.Rat.intermediateFieldEquivSubgroupChar`: the bijection between the
  intermediate fields of `ℚ(ζₙ)/ℚ` and subgroups of `Xₙ`.
- `IsCyclotomicExtension.Rat.mem_intermediateFieldEquivSubgroupChar_iff` : assume that `m ∣ n`,
  then the image of `ℚ(ζₘ) ⊆ ℚ(ζₙ)` by `intermediateFieldEquivSubgroupChar` is the set of
  characters whose conductor divides `m`.

-/

@[expose] public section

namespace IsCyclotomicExtension.Rat

open NumberField IsCyclotomicExtension

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [hK : IsCyclotomicExtension {n} ℚ K]

include hK in
/--
The isomorphism between `Gal(ℚ(ζₙ)/ℚ)` and `(ℤ/nℤ)ˣ` that sends `σ` to the class `a` such that
`σ (ζₙ) = ζₙ ^ a`.
-/
noncomputable abbrev galEquivZMod : Gal(K/ℚ) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.autEquivPow K <| Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)

theorem galEquivZMod_apply_of_pow_eq (σ : Gal(K/ℚ)) {x : K} (hx : x ^ n = 1) :
    σ x = x ^ (galEquivZMod n K σ).val.val := by
  obtain ⟨a, -, rfl⟩ := (zeta_spec n ℚ K).eq_pow_of_pow_eq_one hx
  rw [map_pow, pow_right_comm, galEquivZMod, autEquivPow_apply, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, IsPrimitiveRoot.autToPow_spec]

set_option backward.isDefEq.respectTransparency false in
theorem galEquivZMod_smul_of_pow_eq (σ : Gal(K/ℚ)) {x : 𝓞 K} (hx : x ^ n = 1) :
    σ • x = x ^ (galEquivZMod n K σ).val.val := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  apply galEquivZMod_apply_of_pow_eq n K σ <| by rw [← Subalgebra.coe_pow, hx, OneMemClass.coe_one]

section restrict

variable {m : ℕ} [NeZero m] (F : Type*) [Field F] [NumberField F]
  [hF : IsCyclotomicExtension {m} ℚ F] [Algebra F K] [IsGalois ℚ F]

/--
Let `m ∣ n`. Then, the following diagram commutes:
Gal(ℚ(ζₙ)/ℚ) → (ℤ/nℤ)ˣ
  ↓              ↓
Gal(ℚ(ζₘ)/ℚ) → (ℤ/mℤ)ˣ
where the horizontal maps are `galEquivZMod`, the left map is the restriction map and the right map
is the natural map.
-/
theorem galEquivZMod_restrictNormal_apply (h : m ∣ n) (σ : Gal(K/ℚ)) :
    galEquivZMod m F (σ.restrictNormal F) = ZMod.unitsMap h (galEquivZMod n K σ) := by
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ F
  let ζ := IsCyclotomicExtension.zeta m ℚ F
  suffices ζ ^ (galEquivZMod m F (σ.restrictNormal F)).val.val = ζ ^ (galEquivZMod n K σ).val.val by
    rw [(hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, ZMod.natCast_val, ZMod.cast_id] at this
    rwa [Units.ext_iff]
  apply FaithfulSMul.algebraMap_injective F K
  rw [map_pow, map_pow, ← galEquivZMod_apply_of_pow_eq, ← AlgEquiv.restrictNormal_commutes,
      galEquivZMod_apply_of_pow_eq m _ _ hζ.pow_eq_one, map_pow]
  rw [← map_pow, (hζ.pow_eq_one_iff_dvd _).mpr h, map_one]

end restrict

open MulChar DirichletCharacter

variable (R : Type*) [CommRing R] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]

/--
The bijection between the subgroups of `Gal(ℚ(ζₙ)/ℚ)` and the subgroups of the group
of Dirichlet characters of level `n`.
-/
noncomputable def subgroupGalEquivSubgroupChar :
    Subgroup Gal(K/ℚ) ≃o (Subgroup (DirichletCharacter R n))ᵒᵈ :=
  (galEquivZMod n K).mapSubgroup.trans <| subgroupOrderIsoSubgroupMulChar (ZMod n) R

@[simp]
theorem mem_subgroupGalEquivSubgroupChar_iff (χ : DirichletCharacter R n) (H : Subgroup Gal(K/ℚ)) :
    χ ∈ (subgroupGalEquivSubgroupChar n K R H).ofDual ↔
      ∀ σ ∈ H, χ (galEquivZMod n K σ) = 1 := by
  simp [subgroupGalEquivSubgroupChar]

@[simp]
theorem mem_subgroupGalEquivSubgroupChar_symm_iff (σ : Gal(K/ℚ))
    (Y : Subgroup (DirichletCharacter R n)) :
    σ ∈ (subgroupGalEquivSubgroupChar n K R).symm (OrderDual.toDual Y) ↔
      ∀ χ ∈ Y, χ (galEquivZMod n K σ) = 1 := by
  simp only [subgroupGalEquivSubgroupChar, OrderIso.symm_trans_apply, MulEquiv.symm_mapSubgroup,
    MulEquiv.coe_mapSubgroup, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    mem_subgroupOrderIsoSubgroupMulChar_symm_iff]

variable [IsGalois ℚ K]

/--
The bijection between the intermediate fields of `ℚ(ζₙ)/ℚ` and the subgroups of the group
of Dirichlet characters of level `n`.
-/
noncomputable def intermediateFieldEquivSubgroupChar :
    IntermediateField ℚ K ≃o Subgroup (DirichletCharacter R n) :=
  IsGalois.intermediateFieldEquivSubgroup.trans <|
      (subgroupGalEquivSubgroupChar n K R).dual.trans (OrderIso.dualDual _).symm

@[simp]
theorem mem_intermediateFieldEquivSubgroupChar (F : IntermediateField ℚ K)
    (χ : DirichletCharacter R n) :
    χ ∈ intermediateFieldEquivSubgroupChar n K R F ↔
      ∀ σ : Gal(K/ℚ), σ ∈ F.fixingSubgroup → χ (galEquivZMod n K σ) = 1 := by
  simp [intermediateFieldEquivSubgroupChar]

set_option backward.isDefEq.respectTransparency false in
/--
Assume that `m ∣ n`, then the image of `ℚ(ζₘ) ⊆ ℚ(ζₙ)` by `intermediateFieldEquivSubgroupChar` is
the set of characters whose conductor divides `m`.
-/
theorem mem_intermediateFieldEquivSubgroupChar_iff (F : IntermediateField ℚ K)
    {m : ℕ} [NeZero m] [IsGalois ℚ F] [IsCyclotomicExtension {m} ℚ F] (hdiv : m ∣ n)
    (χ : DirichletCharacter R n) :
    χ ∈ intermediateFieldEquivSubgroupChar n K R F ↔ χ.conductor ∣ m := by
  simp_rw [← χ.mem_conductorSet_iff_conductor_dvd (NeZero.ne n) hdiv, χ.mem_conductorSet_iff,
    factorsThrough_iff_ker_unitsMap hdiv, mem_intermediateFieldEquivSubgroupChar,
    SetLike.le_def, ← (galEquivZMod n K).forall_congr_right, MonoidHom.mem_ker,
    MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← (galEquivZMod_restrictNormal_apply n K F hdiv _),
    EmbeddingLike.map_eq_one_iff, AlgEquiv.restrictNormal_eq_one_iff,
    IntermediateField.mem_fixingSubgroup_iff, Units.ext_iff, toUnitHom_eq, coe_equivToUnitHom,
    Units.val_one]

end IsCyclotomicExtension.Rat
