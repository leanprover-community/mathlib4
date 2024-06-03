/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Weights.Basic

/-!
# Weights and roots of Lie modules and Lie algebras with respect to Cartan subalgebras

Given a Lie algebra `L` which is not necessarily nilpotent, it may be useful to study its
representations by restricting them to a nilpotent subalgebra (e.g., a Cartan subalgebra). In the
particular case when we view `L` as a module over itself via the adjoint action, the weight spaces
of `L` restricted to a nilpotent subalgebra are known as root spaces.

Basic definitions and properties of the above ideas are provided in this file.

## Main definitions

  * `LieAlgebra.rootSpace`
  * `LieAlgebra.corootSpace`
  * `LieAlgebra.rootSpaceWeightSpaceProduct`
  * `LieAlgebra.rootSpaceProduct`
  * `LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan`

-/

suppress_compilation

open Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieAlgebra.IsNilpotent R H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

open scoped TensorProduct
open TensorProduct.LieModule LieModule

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of a map `χ : H → R` is the weight
space of `L` regarded as a module of `H` via the adjoint action. -/
abbrev rootSpace (χ : H → R) : LieSubmodule R H L :=
  weightSpace L χ
#align lie_algebra.root_space LieAlgebra.rootSpace

theorem zero_rootSpace_eq_top_of_nilpotent [IsNilpotent R L] :
    rootSpace (⊤ : LieSubalgebra R L) 0 = ⊤ :=
  zero_weightSpace_eq_top_of_nilpotent L
#align lie_algebra.zero_root_space_eq_top_of_nilpotent LieAlgebra.zero_rootSpace_eq_top_of_nilpotent

@[simp]
theorem rootSpace_comap_eq_weightSpace (χ : H → R) :
    (rootSpace H χ).comap H.incl' = weightSpace H χ :=
  comap_weightSpace_eq_of_injective Subtype.coe_injective
#align lie_algebra.root_space_comap_eq_weight_space LieAlgebra.rootSpace_comap_eq_weightSpace

variable {H}

theorem lie_mem_weightSpace_of_mem_weightSpace {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ weightSpace M χ₂) : ⁅x, m⁆ ∈ weightSpace M (χ₁ + χ₂) := by
  rw [weightSpace, LieSubmodule.mem_iInf]
  intro y
  replace hx : x ∈ weightSpaceOf L (χ₁ y) y := by
    rw [rootSpace, weightSpace, LieSubmodule.mem_iInf] at hx; exact hx y
  replace hm : m ∈ weightSpaceOf M (χ₂ y) y := by
    rw [weightSpace, LieSubmodule.mem_iInf] at hm; exact hm y
  exact lie_mem_maxGenEigenspace_toEnd hx hm
#align lie_algebra.lie_mem_weight_space_of_mem_weight_space LieAlgebra.lie_mem_weightSpace_of_mem_weightSpace

lemma toEnd_pow_apply_mem {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ weightSpace M χ₂) (n) :
    (toEnd R L M x ^ n : Module.End R M) m ∈ weightSpace M (n • χ₁ + χ₂) := by
  induction n
  · simpa using hm
  · next n IH =>
    simp only [pow_succ', LinearMap.mul_apply, toEnd_apply_apply,
      Nat.cast_add, Nat.cast_one, rootSpace]
    convert lie_mem_weightSpace_of_mem_weightSpace hx IH using 2
    rw [succ_nsmul, ← add_assoc, add_comm (n • _)]

variable (R L H M)

/-- Auxiliary definition for `rootSpaceWeightSpaceProduct`,
which is close to the deterministic timeout limit.
-/
def rootSpaceWeightSpaceProductAux {χ₁ χ₂ χ₃ : H → R} (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ →ₗ[R] weightSpace M χ₂ →ₗ[R] weightSpace M χ₃ where
  toFun x :=
    { toFun := fun m =>
        ⟨⁅(x : L), (m : M)⁆, hχ ▸ lie_mem_weightSpace_of_mem_weightSpace x.property m.property⟩
      map_add' := fun m n => by simp only [LieSubmodule.coe_add, lie_add]; rfl
      map_smul' := fun t m => by
        dsimp only
        conv_lhs =>
          congr
          rw [LieSubmodule.coe_smul, lie_smul]
        rfl }
  map_add' x y := by
    ext m
    simp only [AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, add_lie, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply, AddSubmonoid.mk_add_mk]
  map_smul' t x := by
    simp only [RingHom.id_apply]
    ext m
    simp only [SetLike.val_smul, smul_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      SetLike.mk_smul_mk]
#align lie_algebra.root_space_weight_space_product_aux LieAlgebra.rootSpaceWeightSpaceProductAux

-- Porting note (#11083): this def is _really_ slow
-- See https://github.com/leanprover-community/mathlib4/issues/5028
/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors and weight vectors, compatible with the actions of `H`. -/
def rootSpaceWeightSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] weightSpace M χ₂ →ₗ⁅R,H⁆ weightSpace M χ₃ :=
  liftLie R H (rootSpace H χ₁) (weightSpace M χ₂) (weightSpace M χ₃)
    { toLinearMap := rootSpaceWeightSpaceProductAux R L H M hχ
      map_lie' := fun {x y} => by
        ext m
        simp only [rootSpaceWeightSpaceProductAux, LieSubmodule.coe_bracket,
          LieSubalgebra.coe_bracket_of_module, lie_lie, LinearMap.coe_mk, AddHom.coe_mk,
          Subtype.coe_mk, LieHom.lie_apply, LieSubmodule.coe_sub] }
#align lie_algebra.root_space_weight_space_product LieAlgebra.rootSpaceWeightSpaceProduct

@[simp]
theorem coe_rootSpaceWeightSpaceProduct_tmul (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃)
    (x : rootSpace H χ₁) (m : weightSpace M χ₂) :
    (rootSpaceWeightSpaceProduct R L H M χ₁ χ₂ χ₃ hχ (x ⊗ₜ m) : M) = ⁅(x : L), (m : M)⁆ := by
  simp only [rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux, coe_liftLie_eq_lift_coe,
    AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, lift_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_mk]
#align lie_algebra.coe_root_space_weight_space_product_tmul LieAlgebra.coe_rootSpaceWeightSpaceProduct_tmul

theorem mapsTo_toEnd_weightSpace_add_of_mem_rootSpace (α χ : H → R)
    {x : L} (hx : x ∈ rootSpace H α) :
    MapsTo (toEnd R L M x) (weightSpace M χ) (weightSpace M (α + χ)) := by
  intro m hm
  let x' : rootSpace H α := ⟨x, hx⟩
  let m' : weightSpace M χ := ⟨m, hm⟩
  exact (rootSpaceWeightSpaceProduct R L H M α χ (α + χ) rfl (x' ⊗ₜ m')).property

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors, compatible with the actions of `H`. -/
def rootSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] rootSpace H χ₂ →ₗ⁅R,H⁆ rootSpace H χ₃ :=
  rootSpaceWeightSpaceProduct R L H L χ₁ χ₂ χ₃ hχ
#align lie_algebra.root_space_product LieAlgebra.rootSpaceProduct

@[simp]
theorem rootSpaceProduct_def : rootSpaceProduct R L H = rootSpaceWeightSpaceProduct R L H L := rfl
#align lie_algebra.root_space_product_def LieAlgebra.rootSpaceProduct_def

theorem rootSpaceProduct_tmul
    (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpace H χ₁) (y : rootSpace H χ₂) :
    (rootSpaceProduct R L H χ₁ χ₂ χ₃ hχ (x ⊗ₜ y) : L) = ⁅(x : L), (y : L)⁆ := by
  simp only [rootSpaceProduct_def, coe_rootSpaceWeightSpaceProduct_tmul]
#align lie_algebra.root_space_product_tmul LieAlgebra.rootSpaceProduct_tmul

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of the zero map `0 : H → R` is a Lie
subalgebra of `L`. -/
def zeroRootSubalgebra : LieSubalgebra R L :=
  { toSubmodule := (rootSpace H 0 : Submodule R L)
    lie_mem' := fun {x y hx hy} => by
      let xy : rootSpace H 0 ⊗[R] rootSpace H 0 := ⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩
      suffices (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy : L) ∈ rootSpace H 0 by
        rwa [rootSpaceProduct_tmul, Subtype.coe_mk, Subtype.coe_mk] at this
      exact (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy).property }
#align lie_algebra.zero_root_subalgebra LieAlgebra.zeroRootSubalgebra

@[simp]
theorem coe_zeroRootSubalgebra : (zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0 := rfl
#align lie_algebra.coe_zero_root_subalgebra LieAlgebra.coe_zeroRootSubalgebra

theorem mem_zeroRootSubalgebra (x : L) :
    x ∈ zeroRootSubalgebra R L H ↔ ∀ y : H, ∃ k : ℕ, (toEnd R H L y ^ k) x = 0 := by
  change x ∈ rootSpace H 0 ↔ _
  simp only [mem_weightSpace, Pi.zero_apply, zero_smul, sub_zero]
#align lie_algebra.mem_zero_root_subalgebra LieAlgebra.mem_zeroRootSubalgebra

theorem toLieSubmodule_le_rootSpace_zero : H.toLieSubmodule ≤ rootSpace H 0 := by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_weightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := (inferInstance : IsNilpotent R H)
  use k
  let f : Module.End R H := toEnd R H H y
  let g : Module.End R L := toEnd R H L y
  have hfg : g.comp (H : Submodule R L).subtype = (H : Submodule R L).subtype.comp f := by
    ext z
    simp only [toEnd_apply_apply, Submodule.subtype_apply,
      LieSubalgebra.coe_bracket_of_module, LieSubalgebra.coe_bracket, Function.comp_apply,
      LinearMap.coe_comp]
    rfl
  change (g ^ k).comp (H : Submodule R L).subtype ⟨x, hx⟩ = 0
  rw [LinearMap.commute_pow_left_of_commute hfg k]
  have h := iterate_toEnd_mem_lowerCentralSeries R H H y ⟨x, hx⟩ k
  rw [hk, LieSubmodule.mem_bot] at h
  simp only [Submodule.subtype_apply, Function.comp_apply, LinearMap.pow_apply, LinearMap.coe_comp,
    Submodule.coe_eq_zero]
  exact h
#align lie_algebra.to_lie_submodule_le_root_space_zero LieAlgebra.toLieSubmodule_le_rootSpace_zero

/-- This enables the instance `Zero (Weight R H L)`. -/
instance [Nontrivial H] : Nontrivial (weightSpace L (0 : H → R)) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, e⟩ := exists_pair_ne H
  exact ⟨⟨x, toLieSubmodule_le_rootSpace_zero R L H hx⟩,
    ⟨y, toLieSubmodule_le_rootSpace_zero R L H hy⟩, by simpa using e⟩

theorem le_zeroRootSubalgebra : H ≤ zeroRootSubalgebra R L H := by
  rw [← LieSubalgebra.coe_submodule_le_coe_submodule, ← H.coe_toLieSubmodule,
    coe_zeroRootSubalgebra, LieSubmodule.coeSubmodule_le_coeSubmodule]
  exact toLieSubmodule_le_rootSpace_zero R L H
#align lie_algebra.le_zero_root_subalgebra LieAlgebra.le_zeroRootSubalgebra

@[simp]
theorem zeroRootSubalgebra_normalizer_eq_self :
    (zeroRootSubalgebra R L H).normalizer = zeroRootSubalgebra R L H := by
  refine le_antisymm ?_ (LieSubalgebra.le_normalizer _)
  intro x hx
  rw [LieSubalgebra.mem_normalizer_iff] at hx
  rw [mem_zeroRootSubalgebra]
  rintro ⟨y, hy⟩
  specialize hx y (le_zeroRootSubalgebra R L H hy)
  rw [mem_zeroRootSubalgebra] at hx
  obtain ⟨k, hk⟩ := hx ⟨y, hy⟩
  rw [← lie_skew, LinearMap.map_neg, neg_eq_zero] at hk
  use k + 1
  rw [LinearMap.iterate_succ, LinearMap.coe_comp, Function.comp_apply, toEnd_apply_apply,
    LieSubalgebra.coe_bracket_of_module, Submodule.coe_mk, hk]
#align lie_algebra.zero_root_subalgebra_normalizer_eq_self LieAlgebra.zeroRootSubalgebra_normalizer_eq_self

/-- If the zero root subalgebra of a nilpotent Lie subalgebra `H` is just `H` then `H` is a Cartan
subalgebra.

When `L` is Noetherian, it follows from Engel's theorem that the converse holds. See
`LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan` -/
theorem is_cartan_of_zeroRootSubalgebra_eq (h : zeroRootSubalgebra R L H = H) :
    H.IsCartanSubalgebra :=
  { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact zeroRootSubalgebra_normalizer_eq_self R L H }
#align lie_algebra.is_cartan_of_zero_root_subalgebra_eq LieAlgebra.is_cartan_of_zeroRootSubalgebra_eq

@[simp]
theorem zeroRootSubalgebra_eq_of_is_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
    [IsNoetherian R L] : zeroRootSubalgebra R L H = H := by
  refine le_antisymm ?_ (le_zeroRootSubalgebra R L H)
  suffices rootSpace H 0 ≤ H.toLieSubmodule by exact fun x hx => this hx
  obtain ⟨k, hk⟩ := (rootSpace H 0).isNilpotent_iff_exists_self_le_ucs.mp (by infer_instance)
  exact hk.trans (LieSubmodule.ucs_le_of_normalizer_eq_self (by simp) k)
#align lie_algebra.zero_root_subalgebra_eq_of_is_cartan LieAlgebra.zeroRootSubalgebra_eq_of_is_cartan

theorem zeroRootSubalgebra_eq_iff_is_cartan [IsNoetherian R L] :
    zeroRootSubalgebra R L H = H ↔ H.IsCartanSubalgebra :=
  ⟨is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩
#align lie_algebra.zero_root_subalgebra_eq_iff_is_cartan LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan

@[simp]
theorem rootSpace_zero_eq (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L] :
    rootSpace H 0 = H.toLieSubmodule := by
  rw [← LieSubmodule.coe_toSubmodule_eq_iff, ← coe_zeroRootSubalgebra,
    zeroRootSubalgebra_eq_of_is_cartan R L H, LieSubalgebra.coe_toLieSubmodule]

variable {R L H}
variable [H.IsCartanSubalgebra] [IsNoetherian R L] (α : H → R)

/-- Given a root `α` relative to a Cartan subalgebra `H`, this is the span of all products of
an element of the `α` root space and an element of the `-α` root space. Informally it is often
denoted `⁅H(α), H(-α)⁆`.

If the Killing form is non-degenerate and the coefficients are a perfect field, this space is
one-dimensional. See `LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton` and
`LieAlgebra.IsKilling.coe_corootSpace_eq_span_singleton'`.

Note that the name "coroot space" is not standard as this space does not seem to have a name in the
informal literature. -/
def corootSpace : LieIdeal R H :=
  LieModuleHom.range <| ((rootSpace H 0).incl.comp <|
    rootSpaceProduct R L H α (-α) 0 (add_neg_self α)).codRestrict H.toLieSubmodule (by
  rw [← rootSpace_zero_eq]
  exact fun p ↦ (rootSpaceProduct R L H α (-α) 0 (add_neg_self α) p).property)

lemma mem_corootSpace {x : H} :
    x ∈ corootSpace α ↔
    (x : L) ∈ Submodule.span R {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} := by
  have : x ∈ corootSpace α ↔
      (x : L) ∈ LieSubmodule.map H.toLieSubmodule.incl (corootSpace α) := by
    rw [corootSpace]
    simpa using exists_congr fun _ ↦ H.toLieSubmodule.injective_incl.eq_iff.symm
  simp_rw [this, corootSpace, ← LieModuleHom.map_top, ← LieSubmodule.mem_coeSubmodule,
    LieSubmodule.coeSubmodule_map, LieSubmodule.top_coeSubmodule, ← TensorProduct.span_tmul_eq_top,
    LinearMap.map_span, Set.image, Set.mem_setOf_eq, exists_exists_exists_and_eq]
  change (x : L) ∈ Submodule.span R
    {x | ∃ (a : rootSpace H α) (b : rootSpace H (-α)), ⁅(a : L), (b : L)⁆ = x} ↔ _
  simp

lemma mem_corootSpace' {x : H} :
    x ∈ corootSpace α ↔
    x ∈ Submodule.span R ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H) := by
  set s : Set H := ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H)
  suffices H.subtype '' s = {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} by
    obtain ⟨x, hx⟩ := x
    erw [← (H : Submodule R L).injective_subtype.mem_set_image (s := Submodule.span R s)]
    change _ ↔ x ∈ (Submodule.span R s).map H.subtype
    rw [Submodule.map_span, mem_corootSpace, ← this]
    rfl
  ext u
  simp only [Submodule.coeSubtype, mem_image, Subtype.exists, LieSubalgebra.mem_coe_submodule,
    exists_and_right, exists_eq_right, mem_setOf_eq, s]
  refine ⟨fun ⟨_, y, hy, z, hz, hyz⟩ ↦ ⟨y, hy, z, hz, hyz⟩,
    fun ⟨y, hy, z, hz, hyz⟩ ↦ ⟨?_, y, hy, z, hz, hyz⟩⟩
  convert (rootSpaceProduct R L H α (-α) 0 (add_neg_self α) (⟨y, hy⟩ ⊗ₜ[R] ⟨z, hz⟩)).property
  simp [hyz]

end LieAlgebra
