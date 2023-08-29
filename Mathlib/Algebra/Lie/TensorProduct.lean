/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Abelian

#align_import algebra.lie.tensor_product from "leanprover-community/mathlib"@"657df4339ae6ceada048c8a2980fb10e393143ec"

/-!
# Tensor products of Lie modules

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/


universe u v w w₁ w₂ w₃

variable {R : Type u} [CommRing R]

open LieModule

namespace TensorProduct

open scoped TensorProduct

namespace LieModule

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

attribute [local ext] TensorProduct.ext

/-- It is useful to define the bracket via this auxiliary function so that we have a type-theoretic
expression of the fact that `L` acts by linear endomorphisms. It simplifies the proofs in
`lieRingModule` below. -/
def hasBracketAux (x : L) : Module.End R (M ⊗[R] N) :=
  (toEndomorphism R L M x).rTensor N + (toEndomorphism R L N x).lTensor M
#align tensor_product.lie_module.has_bracket_aux TensorProduct.LieModule.hasBracketAux

/-- The tensor product of two Lie modules is a Lie ring module. -/
instance lieRingModule : LieRingModule L (M ⊗[R] N) where
  bracket x := hasBracketAux x
  add_lie x y t := by
    simp only [hasBracketAux, LinearMap.lTensor_add, LinearMap.rTensor_add, LieHom.map_add,
      LinearMap.add_apply]
    abel
    -- 🎉 no goals
    -- 🎉 no goals
  lie_add x := LinearMap.map_add _
  leibniz_lie x y t := by
    suffices (hasBracketAux x).comp (hasBracketAux y) =
        hasBracketAux ⁅x, y⁆ + (hasBracketAux y).comp (hasBracketAux x) by
      simp only [← LinearMap.add_apply]; rw [← LinearMap.comp_apply, this]; rfl
    ext m n
    -- ⊢ ↑(↑(LinearMap.compr₂ (mk R M N) (LinearMap.comp (hasBracketAux x) (hasBracke …
    simp only [hasBracketAux, LieRing.of_associative_ring_bracket, LinearMap.mul_apply, mk_apply,
      LinearMap.lTensor_sub, LinearMap.compr₂_apply, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, LieHom.map_lie, toEndomorphism_apply_apply, LinearMap.add_apply,
      LinearMap.map_add, LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_tmul]
    abel
    -- 🎉 no goals
    -- 🎉 no goals
#align tensor_product.lie_module.lie_ring_module TensorProduct.LieModule.lieRingModule

/-- The tensor product of two Lie modules is a Lie module. -/
instance lieModule : LieModule R L (M ⊗[R] N) where
  smul_lie c x t := by
    change hasBracketAux (c • x) _ = c • hasBracketAux _ _
    -- ⊢ ↑(hasBracketAux (c • x)) t = c • ↑(hasBracketAux x) t
    simp only [hasBracketAux, smul_add, LinearMap.rTensor_smul, LinearMap.smul_apply,
      LinearMap.lTensor_smul, LieHom.map_smul, LinearMap.add_apply]
  lie_smul c x := LinearMap.map_smul _ c
#align tensor_product.lie_module.lie_module TensorProduct.LieModule.lieModule

@[simp]
theorem lie_tmul_right (x : L) (m : M) (n : N) : ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, m⁆ ⊗ₜ n + m ⊗ₜ ⁅x, n⁆ :=
  show hasBracketAux x (m ⊗ₜ[R] n) = _ by
    simp only [hasBracketAux, LinearMap.rTensor_tmul, toEndomorphism_apply_apply,
      LinearMap.add_apply, LinearMap.lTensor_tmul]
#align tensor_product.lie_module.lie_tmul_right TensorProduct.LieModule.lie_tmul_right

variable (R L M N P Q)

/-- The universal property for tensor product of modules of a Lie algebra: the `R`-linear
tensor-hom adjunction is equivariant with respect to the `L` action. -/
def lift : (M →ₗ[R] N →ₗ[R] P) ≃ₗ⁅R,L⁆ M ⊗[R] N →ₗ[R] P :=
  { TensorProduct.lift.equiv R M N P with
    map_lie' := fun {x f} => by
      ext m n
      -- ⊢ ↑(↑(LinearMap.compr₂ (mk R M N) (AddHom.toFun src✝.toAddHom ⁅x, f⁆)) m) n =  …
      simp only [mk_apply, LinearMap.compr₂_apply, lie_tmul_right, LinearMap.sub_apply,
        lift.equiv_apply, LinearEquiv.toFun_eq_coe, LieHom.lie_apply, LinearMap.map_add]
      abel }
      -- 🎉 no goals
      -- 🎉 no goals
#align tensor_product.lie_module.lift TensorProduct.LieModule.lift

@[simp]
theorem lift_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) : lift R L M N P f (m ⊗ₜ n) = f m n :=
  rfl
#align tensor_product.lie_module.lift_apply TensorProduct.LieModule.lift_apply

/-- A weaker form of the universal property for tensor product of modules of a Lie algebra.

Note that maps `f` of type `M →ₗ⁅R,L⁆ N →ₗ[R] P` are exactly those `R`-bilinear maps satisfying
`⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆` for all `x, m, n` (see e.g, `LieModuleHom.map_lie₂`). -/
def liftLie : (M →ₗ⁅R,L⁆ N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ⁅R,L⁆ P :=
  maxTrivLinearMapEquivLieModuleHom.symm ≪≫ₗ ↑(maxTrivEquiv (lift R L M N P)) ≪≫ₗ
    maxTrivLinearMapEquivLieModuleHom
#align tensor_product.lie_module.lift_lie TensorProduct.LieModule.liftLie

@[simp]
theorem coe_liftLie_eq_lift_coe (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) :
    ⇑(liftLie R L M N P f) = lift R L M N P f := by
  suffices (liftLie R L M N P f : M ⊗[R] N →ₗ[R] P) = lift R L M N P f by
    rw [← this, LieModuleHom.coe_toLinearMap]
  ext m n
  -- ⊢ ↑(↑(LinearMap.compr₂ (mk R M N) ↑(↑(liftLie R L M N P) f)) m) n = ↑(↑(Linear …
  simp only [liftLie, LinearEquiv.trans_apply, LieModuleEquiv.coe_to_linearEquiv,
    coe_linearMap_maxTrivLinearMapEquivLieModuleHom, coe_maxTrivEquiv_apply,
    coe_linearMap_maxTrivLinearMapEquivLieModuleHom_symm]
#align tensor_product.lie_module.coe_lift_lie_eq_lift_coe TensorProduct.LieModule.coe_liftLie_eq_lift_coe

theorem liftLie_apply (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (m : M) (n : N) :
    liftLie R L M N P f (m ⊗ₜ n) = f m n := by
  simp only [coe_liftLie_eq_lift_coe, LieModuleHom.coe_toLinearMap, lift_apply]
  -- 🎉 no goals
#align tensor_product.lie_module.lift_lie_apply TensorProduct.LieModule.liftLie_apply

variable {R L M N P Q}

/-- A pair of Lie module morphisms `f : M → P` and `g : N → Q`, induce a Lie module morphism:
`M ⊗ N → P ⊗ Q`. -/
nonrec def map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) : M ⊗[R] N →ₗ⁅R,L⁆ P ⊗[R] Q :=
  { map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) with
    map_lie' := fun {x t} => by
      simp only [LinearMap.toFun_eq_coe]
      -- ⊢ ↑(TensorProduct.map ↑f ↑g) ⁅x, t⁆ = ⁅x, ↑(TensorProduct.map ↑f ↑g) t⁆
      refine' t.induction_on _ _ _
      · simp only [LinearMap.map_zero, lie_zero]
        -- 🎉 no goals
      · intro m n
        -- ⊢ ↑(TensorProduct.map ↑f ↑g) ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, ↑(TensorProduct.map ↑f ↑g) ( …
        simp only [LieModuleHom.coe_toLinearMap, lie_tmul_right, LieModuleHom.map_lie, map_tmul,
          LinearMap.map_add]
      · intro t₁ t₂ ht₁ ht₂; simp only [ht₁, ht₂, lie_add, LinearMap.map_add] }
        -- ⊢ ↑(TensorProduct.map ↑f ↑g) ⁅x, t₁ + t₂⁆ = ⁅x, ↑(TensorProduct.map ↑f ↑g) (t₁ …
                             -- 🎉 no goals
#align tensor_product.lie_module.map TensorProduct.LieModule.map

@[simp]
theorem coe_linearMap_map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) :
    (map f g : M ⊗[R] N →ₗ[R] P ⊗[R] Q) = TensorProduct.map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :=
  rfl
#align tensor_product.lie_module.coe_linear_map_map TensorProduct.LieModule.coe_linearMap_map

@[simp]
nonrec theorem map_tmul (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) (m : M) (n : N) :
    map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
  map_tmul _ _ _ _
#align tensor_product.lie_module.map_tmul TensorProduct.LieModule.map_tmul

/-- Given Lie submodules `M' ⊆ M` and `N' ⊆ N`, this is the natural map: `M' ⊗ N' → M ⊗ N`. -/
def mapIncl (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : M' ⊗[R] N' →ₗ⁅R,L⁆ M ⊗[R] N :=
  map M'.incl N'.incl
#align tensor_product.lie_module.map_incl TensorProduct.LieModule.mapIncl

@[simp]
theorem mapIncl_def (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) :
    mapIncl M' N' = map M'.incl N'.incl :=
  rfl
#align tensor_product.lie_module.map_incl_def TensorProduct.LieModule.mapIncl_def

end LieModule

end TensorProduct

namespace LieModule

open scoped TensorProduct

variable (R) (L : Type v) (M : Type w)

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The action of the Lie algebra on one of its modules, regarded as a morphism of Lie modules. -/
def toModuleHom : L ⊗[R] M →ₗ⁅R,L⁆ M :=
  TensorProduct.LieModule.liftLie R L L M M
    { (toEndomorphism R L M : L →ₗ[R] M →ₗ[R] M) with
      map_lie' := fun {x m} => by ext n; simp [LieRing.of_associative_ring_bracket] }
                                  -- ⊢ ↑(AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : …
                                         -- 🎉 no goals
#align lie_module.to_module_hom LieModule.toModuleHom

@[simp]
theorem toModuleHom_apply (x : L) (m : M) : toModuleHom R L M (x ⊗ₜ m) = ⁅x, m⁆ := by
  simp only [toModuleHom, TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LinearMap.coe_mk, LinearMap.coe_toAddHom, LieHom.coe_toLinearMap, toEndomorphism_apply_apply]
#align lie_module.to_module_hom_apply LieModule.toModuleHom_apply

end LieModule

namespace LieSubmodule

open scoped TensorProduct

open TensorProduct.LieModule

open LieModule

variable {L : Type v} {M : Type w}
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (I : LieIdeal R L) (N : LieSubmodule R L M)

/-- A useful alternative characterisation of Lie ideal operations on Lie submodules.

Given a Lie ideal `I ⊆ L` and a Lie submodule `N ⊆ M`, by tensoring the inclusion maps and then
applying the action of `L` on `M`, we obtain morphism of Lie modules `f : I ⊗ N → L ⊗ M → M`.

This lemma states that `⁅I, N⁆ = range f`. -/
theorem lieIdeal_oper_eq_tensor_map_range :
    ⁅I, N⁆ = ((toModuleHom R L M).comp (mapIncl I N : (↥I) ⊗[R] (↥N) →ₗ⁅R,L⁆ L ⊗[R] M)).range := by
  rw [← coe_toSubmodule_eq_iff, lieIdeal_oper_eq_linear_span, LieModuleHom.coeSubmodule_range,
    LieModuleHom.coe_linearMap_comp, LinearMap.range_comp, mapIncl_def, coe_linearMap_map,
    TensorProduct.map_range_eq_span_tmul, Submodule.map_span]
  congr; ext m; constructor
  -- ⊢ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} = ↑↑(toModuleHom R L M) '' {t | ∃ m n, ↑↑(incl I)  …
         -- ⊢ m ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} ↔ m ∈ ↑↑(toModuleHom R L M) '' {t | ∃ m n, ↑↑( …
                -- ⊢ m ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m} → m ∈ ↑↑(toModuleHom R L M) '' {t | ∃ m n, ↑↑( …
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩; use x ⊗ₜ n; constructor
    -- ⊢ ⁅↑{ val := x, property := hx }, ↑{ val := n, property := hn }⁆ ∈ ↑↑(toModule …
                                    -- ⊢ x ⊗ₜ[R] n ∈ {t | ∃ m n, ↑↑(incl I) m ⊗ₜ[R] ↑↑(incl N) n = t} ∧ ↑↑(toModuleHo …
                                                -- ⊢ x ⊗ₜ[R] n ∈ {t | ∃ m n, ↑↑(incl I) m ⊗ₜ[R] ↑↑(incl N) n = t}
    · use ⟨x, hx⟩, ⟨n, hn⟩; simp
      -- ⊢ ↑↑(incl I) { val := x, property := hx } ⊗ₜ[R] ↑↑(incl N) { val := n, propert …
                            -- 🎉 no goals
    · simp
      -- 🎉 no goals
  · rintro ⟨t, ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, h⟩; rw [← h]; use ⟨x, hx⟩, ⟨n, hn⟩; simp
    -- ⊢ m ∈ {m | ∃ x n, ⁅↑x, ↑n⁆ = m}
                                            -- ⊢ ↑↑(toModuleHom R L M) (↑↑(incl I) { val := x, property := hx } ⊗ₜ[R] ↑↑(incl …
                                                      -- ⊢ ⁅↑{ val := x, property := hx }, ↑{ val := n, property := hn }⁆ = ↑↑(toModule …
                                                                            -- 🎉 no goals
#align lie_submodule.lie_ideal_oper_eq_tensor_map_range LieSubmodule.lieIdeal_oper_eq_tensor_map_range

end LieSubmodule
