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

open Set

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
  {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieAlgebra

open scoped TensorProduct
open TensorProduct.LieModule LieModule

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of a map `χ : H → R` is the weight
space of `L` regarded as a module of `H` via the adjoint action. -/
abbrev rootSpace (χ : H → R) : LieSubmodule R H L :=
  genWeightSpace L χ

theorem zero_rootSpace_eq_top_of_nilpotent [LieRing.IsNilpotent L] :
    rootSpace (⊤ : LieSubalgebra R L) 0 = ⊤ :=
  zero_genWeightSpace_eq_top_of_nilpotent L

@[simp]
theorem rootSpace_comap_eq_genWeightSpace (χ : H → R) :
    (rootSpace H χ).comap H.incl' = genWeightSpace H χ :=
  comap_genWeightSpace_eq_of_injective Subtype.coe_injective

variable {H}

theorem lie_mem_genWeightSpace_of_mem_genWeightSpace {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ genWeightSpace M χ₂) :
    ⁅x, m⁆ ∈ genWeightSpace M (χ₁ + χ₂) := by
  rw [genWeightSpace, LieSubmodule.mem_iInf]
  intro y
  replace hx : x ∈ genWeightSpaceOf L (χ₁ y) y := by
    rw [rootSpace, genWeightSpace, LieSubmodule.mem_iInf] at hx; exact hx y
  replace hm : m ∈ genWeightSpaceOf M (χ₂ y) y := by
    rw [genWeightSpace, LieSubmodule.mem_iInf] at hm; exact hm y
  exact lie_mem_maxGenEigenspace_toEnd hx hm

lemma toEnd_pow_apply_mem {χ₁ χ₂ : H → R} {x : L} {m : M}
    (hx : x ∈ rootSpace H χ₁) (hm : m ∈ genWeightSpace M χ₂) (n) :
    (toEnd R L M x ^ n : Module.End R M) m ∈ genWeightSpace M (n • χ₁ + χ₂) := by
  induction n with
  | zero => simpa using hm
  | succ n IH =>
    simp only [pow_succ', Module.End.mul_apply, toEnd_apply_apply]
    convert lie_mem_genWeightSpace_of_mem_genWeightSpace hx IH using 2
    rw [succ_nsmul, ← add_assoc, add_comm (n • _)]

variable (R L H M)

/-- Auxiliary definition for `rootSpaceWeightSpaceProduct`,
which is close to the deterministic timeout limit.
-/
def rootSpaceWeightSpaceProductAux {χ₁ χ₂ χ₃ : H → R} (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ →ₗ[R] genWeightSpace M χ₂ →ₗ[R] genWeightSpace M χ₃ where
  toFun x :=
    { toFun := fun m =>
        ⟨⁅(x : L), (m : M)⁆,
          hχ ▸ lie_mem_genWeightSpace_of_mem_genWeightSpace x.property m.property⟩
      map_add' := fun m n => by simp only [LieSubmodule.coe_add, lie_add, AddMemClass.mk_add_mk]
      map_smul' := fun t m => by simp }
  map_add' x y := by
    ext m
    simp only [LieSubmodule.coe_add, add_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
      AddMemClass.mk_add_mk]
  map_smul' t x := by
    simp only [RingHom.id_apply]
    ext m
    simp only [SetLike.val_smul, smul_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      SetLike.mk_smul_mk]

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors and weight vectors, compatible with the actions of `H`. -/
def rootSpaceWeightSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] genWeightSpace M χ₂ →ₗ⁅R,H⁆ genWeightSpace M χ₃ :=
  liftLie R H (rootSpace H χ₁) (genWeightSpace M χ₂) (genWeightSpace M χ₃)
    { toLinearMap := rootSpaceWeightSpaceProductAux R L H M hχ
      map_lie' := fun {x y} => by
        ext m
        simp only [rootSpaceWeightSpaceProductAux]
        dsimp
        simp only [lie_lie] }

@[simp]
theorem coe_rootSpaceWeightSpaceProduct_tmul (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃)
    (x : rootSpace H χ₁) (m : genWeightSpace M χ₂) :
    (rootSpaceWeightSpaceProduct R L H M χ₁ χ₂ χ₃ hχ (x ⊗ₜ m) : M) = ⁅(x : L), (m : M)⁆ := by
  simp only [rootSpaceWeightSpaceProduct, rootSpaceWeightSpaceProductAux, coe_liftLie_eq_lift_coe,
    lift_apply, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_mk]

theorem mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace (α χ : H → R)
    {x : L} (hx : x ∈ rootSpace H α) :
    MapsTo (toEnd R L M x) (genWeightSpace M χ) (genWeightSpace M (α + χ)) := by
  intro m hm
  let x' : rootSpace H α := ⟨x, hx⟩
  let m' : genWeightSpace M χ := ⟨m, hm⟩
  exact (rootSpaceWeightSpaceProduct R L H M α χ (α + χ) rfl (x' ⊗ₜ m')).property

/-- Given a nilpotent Lie subalgebra `H ⊆ L` together with `χ₁ χ₂ : H → R`, there is a natural
`R`-bilinear product of root vectors, compatible with the actions of `H`. -/
def rootSpaceProduct (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) :
    rootSpace H χ₁ ⊗[R] rootSpace H χ₂ →ₗ⁅R,H⁆ rootSpace H χ₃ :=
  rootSpaceWeightSpaceProduct R L H L χ₁ χ₂ χ₃ hχ

@[simp]
theorem rootSpaceProduct_def : rootSpaceProduct R L H = rootSpaceWeightSpaceProduct R L H L := rfl

theorem rootSpaceProduct_tmul
    (χ₁ χ₂ χ₃ : H → R) (hχ : χ₁ + χ₂ = χ₃) (x : rootSpace H χ₁) (y : rootSpace H χ₂) :
    (rootSpaceProduct R L H χ₁ χ₂ χ₃ hχ (x ⊗ₜ y) : L) = ⁅(x : L), (y : L)⁆ := by
  simp only [rootSpaceProduct_def, coe_rootSpaceWeightSpaceProduct_tmul]

/-- Given a nilpotent Lie subalgebra `H ⊆ L`, the root space of the zero map `0 : H → R` is a Lie
subalgebra of `L`. -/
def zeroRootSubalgebra : LieSubalgebra R L :=
  { toSubmodule := (rootSpace H 0 : Submodule R L)
    lie_mem' := fun {x y hx hy} => by
      let xy : rootSpace H 0 ⊗[R] rootSpace H 0 := ⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩
      suffices (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy : L) ∈ rootSpace H 0 by
        rwa [rootSpaceProduct_tmul, Subtype.coe_mk, Subtype.coe_mk] at this
      exact (rootSpaceProduct R L H 0 0 0 (add_zero 0) xy).property }

@[simp]
theorem coe_zeroRootSubalgebra : (zeroRootSubalgebra R L H : Submodule R L) = rootSpace H 0 := rfl

theorem mem_zeroRootSubalgebra (x : L) :
    x ∈ zeroRootSubalgebra R L H ↔ ∀ y : H, ∃ k : ℕ, (toEnd R H L y ^ k) x = 0 := by
  change x ∈ rootSpace H 0 ↔ _
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero]

theorem toLieSubmodule_le_rootSpace_zero : H.toLieSubmodule ≤ rootSpace H 0 := by
  intro x hx
  simp only [LieSubalgebra.mem_toLieSubmodule] at hx
  simp only [mem_genWeightSpace, Pi.zero_apply, sub_zero, zero_smul]
  intro y
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R H H
  use k
  let f : Module.End R H := toEnd R H H y
  let g : Module.End R L := toEnd R H L y
  have hfg : g.comp (H : Submodule R L).subtype = (H : Submodule R L).subtype.comp f := rfl
  change (g ^ k).comp (H : Submodule R L).subtype ⟨x, hx⟩ = 0
  rw [Module.End.commute_pow_left_of_commute hfg k]
  have h := iterate_toEnd_mem_lowerCentralSeries R H H y ⟨x, hx⟩ k
  rw [hk, LieSubmodule.mem_bot] at h
  simp only [Submodule.subtype_apply, Function.comp_apply, Module.End.pow_apply, LinearMap.coe_comp,
    Submodule.coe_eq_zero]
  exact h

/-- This enables the instance `Zero (Weight R H L)`. -/
instance [Nontrivial H] : Nontrivial (genWeightSpace L (0 : H → R)) := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, e⟩ := exists_pair_ne H
  exact ⟨⟨x, toLieSubmodule_le_rootSpace_zero R L H hx⟩,
    ⟨y, toLieSubmodule_le_rootSpace_zero R L H hy⟩, by simpa using e⟩

theorem le_zeroRootSubalgebra : H ≤ zeroRootSubalgebra R L H := by
  rw [← LieSubalgebra.toSubmodule_le_toSubmodule, ← H.coe_toLieSubmodule,
    coe_zeroRootSubalgebra, LieSubmodule.toSubmodule_le_toSubmodule]
  exact toLieSubmodule_le_rootSpace_zero R L H

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
  rw [Module.End.iterate_succ, LinearMap.coe_comp, Function.comp_apply, toEnd_apply_apply,
    LieSubalgebra.coe_bracket_of_module, Submodule.coe_mk, hk]

/-- If the zero root subalgebra of a nilpotent Lie subalgebra `H` is just `H` then `H` is a Cartan
subalgebra.

When `L` is Noetherian, it follows from Engel's theorem that the converse holds. See
`LieAlgebra.zeroRootSubalgebra_eq_iff_is_cartan` -/
theorem is_cartan_of_zeroRootSubalgebra_eq (h : zeroRootSubalgebra R L H = H) :
    H.IsCartanSubalgebra :=
  { nilpotent := inferInstance
    self_normalizing := by rw [← h]; exact zeroRootSubalgebra_normalizer_eq_self R L H }

@[simp]
theorem zeroRootSubalgebra_eq_of_is_cartan (H : LieSubalgebra R L) [H.IsCartanSubalgebra]
    [IsNoetherian R L] : zeroRootSubalgebra R L H = H := by
  refine le_antisymm ?_ (le_zeroRootSubalgebra R L H)
  suffices rootSpace H 0 ≤ H.toLieSubmodule by exact fun x hx => this hx
  obtain ⟨k, hk⟩ := (rootSpace H 0).isNilpotent_iff_exists_self_le_ucs.mp (by infer_instance)
  exact hk.trans (LieSubmodule.ucs_le_of_normalizer_eq_self (by simp) k)

theorem zeroRootSubalgebra_eq_iff_is_cartan [IsNoetherian R L] :
    zeroRootSubalgebra R L H = H ↔ H.IsCartanSubalgebra :=
  ⟨is_cartan_of_zeroRootSubalgebra_eq R L H, by intros; simp⟩

@[simp]
theorem rootSpace_zero_eq (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [IsNoetherian R L] :
    rootSpace H 0 = H.toLieSubmodule := by
  rw [← LieSubmodule.toSubmodule_inj, ← coe_zeroRootSubalgebra,
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
    rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α)).codRestrict H.toLieSubmodule (by
  rw [← rootSpace_zero_eq]
  exact fun p ↦ (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) p).property)

lemma mem_corootSpace {x : H} :
    x ∈ corootSpace α ↔
    (x : L) ∈ Submodule.span R {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} := by
  have : x ∈ corootSpace α ↔
      (x : L) ∈ LieSubmodule.map H.toLieSubmodule.incl (corootSpace α) := by
    rw [corootSpace]
    simp only [rootSpaceProduct_def, LieModuleHom.mem_range, LieSubmodule.mem_map,
      LieSubmodule.incl_apply, SetLike.coe_eq_coe, exists_eq_right]
    rfl
  simp_rw [this, corootSpace, ← LieModuleHom.map_top, ← LieSubmodule.mem_toSubmodule,
    LieSubmodule.toSubmodule_map, LieSubmodule.top_toSubmodule, ← TensorProduct.span_tmul_eq_top,
    LinearMap.map_span, Set.image, Set.mem_setOf_eq, exists_exists_exists_and_eq]
  change (x : L) ∈ Submodule.span R
    {x | ∃ (a : rootSpace H α) (b : rootSpace H (-α)), ⁅(a : L), (b : L)⁆ = x} ↔ _
  simp

lemma mem_corootSpace' {x : H} :
    x ∈ corootSpace α ↔
    x ∈ Submodule.span R ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H) := by
  set s : Set H := ({⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} : Set H)
  suffices H.subtype '' s = {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} by
    erw [← (H : Submodule R L).injective_subtype.mem_set_image (s := Submodule.span R s)]
    rw [mem_image]
    simp_rw [SetLike.mem_coe]
    rw [← Submodule.mem_map, Submodule.coe_subtype, Submodule.map_span, mem_corootSpace, ← this]
  ext u
  simp only [Submodule.coe_subtype, mem_image, Subtype.exists, LieSubalgebra.mem_toSubmodule,
    exists_and_right, exists_eq_right, mem_setOf_eq, s]
  refine ⟨fun ⟨_, y, hy, z, hz, hyz⟩ ↦ ⟨y, hy, z, hz, hyz⟩,
    fun ⟨y, hy, z, hz, hyz⟩ ↦ ⟨?_, y, hy, z, hz, hyz⟩⟩
  convert
    (rootSpaceProduct R L H α (-α) 0 (add_neg_cancel α) (⟨y, hy⟩ ⊗ₜ[R] ⟨z, hz⟩)).property using 0
  simp [hyz]

end LieAlgebra
