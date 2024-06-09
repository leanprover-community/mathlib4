/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RepresentationTheory.Rep

#align_import representation_theory.group_cohomology.resolution from "leanprover-community/mathlib"@"cec81510e48e579bde6acd8568c06a87af045b63"

/-!
# The structure of the `k[G]`-module `k[Gⁿ]`

This file contains facts about an important `k[G]`-module structure on `k[Gⁿ]`, where `k` is a
commutative ring and `G` is a group. The module structure arises from the representation
`G →* End(k[Gⁿ])` induced by the diagonal action of `G` on `Gⁿ.`

In particular, we define an isomorphism of `k`-linear `G`-representations between `k[Gⁿ⁺¹]` and
`k[G] ⊗ₖ k[Gⁿ]` (on which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`).

This allows us to define a `k[G]`-basis on `k[Gⁿ⁺¹]`, by mapping the natural `k[G]`-basis of
`k[G] ⊗ₖ k[Gⁿ]` along the isomorphism.

We then define the standard resolution of `k` as a trivial representation, by
taking the alternating face map complex associated to an appropriate simplicial `k`-linear
`G`-representation. This simplicial object is the `linearization` of the simplicial `G`-set given
by the universal cover of the classifying space of `G`, `EG`. We prove this simplicial `G`-set `EG`
is isomorphic to the Čech nerve of the natural arrow of `G`-sets `G ⟶ {pt}`.

We then use this isomorphism to deduce that as a complex of `k`-modules, the standard resolution
of `k` as a trivial `G`-representation is homotopy equivalent to the complex with `k` at 0 and 0
elsewhere.

Putting this material together allows us to define `groupCohomology.projectiveResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

## Main definitions

 * `groupCohomology.resolution.actionDiagonalSucc`
 * `groupCohomology.resolution.diagonalSucc`
 * `groupCohomology.resolution.ofMulActionBasis`
 * `classifyingSpaceUniversalCover`
 * `groupCohomology.resolution.forget₂ToModuleCatHomotopyEquiv`
 * `groupCohomology.projectiveResolution`

## Implementation notes

We express `k[G]`-module structures on a module `k`-module `V` using the `Representation`
definition. We avoid using instances `Module (G →₀ k) V` so that we do not run into possible
scalar action diamonds.

We also use the category theory library to bundle the type `k[Gⁿ]` - or more generally `k[H]` when
`H` has `G`-action - and the representation together, as a term of type `Rep k G`, and call it
`Rep.ofMulAction k G H.` This enables us to express the fact that certain maps are
`G`-equivariant by constructing morphisms in the category `Rep k G`, i.e., representations of `G`
over `k`.
-/

/- Porting note: most altered proofs in this file involved changing `simp` to `rw` or `erw`, so
https://github.com/leanprover-community/mathlib4/issues/5026 and
https://github.com/leanprover-community/mathlib4/issues/5164 are relevant. -/
noncomputable section

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory

local notation "Gⁿ" => Fin n → G

set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) → G

namespace groupCohomology.resolution

open Finsupp hiding lift
open MonoidalCategory
open Fin (partialProd)

section Basis

variable (k G n) [Group G]

section Action

open Action

/-- An isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on `Gⁿ⁺¹` and
`G` but trivially on `Gⁿ`. The map sends `(g₀, ..., gₙ) ↦ (g₀, (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`,
and the inverse is `(g₀, (g₁, ..., gₙ)) ↦ (g₀, g₀g₁, g₀g₁g₂, ..., g₀g₁...gₙ).` -/
def actionDiagonalSucc (G : Type u) [Group G] :
    ∀ n : ℕ, diagonal G (n + 1) ≅ leftRegular G ⊗ Action.mk (Fin n → G) 1
  | 0 =>
    diagonalOneIsoLeftRegular G ≪≫
      (ρ_ _).symm ≪≫ tensorIso (Iso.refl _) (tensorUnitIso (Equiv.equivOfUnique PUnit _).toIso)
  | n + 1 =>
    diagonalSucc _ _ ≪≫
      tensorIso (Iso.refl _) (actionDiagonalSucc G n) ≪≫
        leftRegularTensorIso _ _ ≪≫
          tensorIso (Iso.refl _)
            (mkIso (Equiv.piFinSuccAbove (fun _ => G) 0).symm.toIso fun _ => rfl)
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.Action_diagonal_succ groupCohomology.resolution.actionDiagonalSucc

theorem actionDiagonalSucc_hom_apply {G : Type u} [Group G] {n : ℕ} (f : Fin (n + 1) → G) :
    (actionDiagonalSucc G n).hom.hom f = (f 0, fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) := by
  induction' n with n hn
  · exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  · refine Prod.ext rfl (funext fun x => ?_)
/- Porting note (#11039): broken proof was
    · dsimp only [actionDiagonalSucc]
      simp only [Iso.trans_hom, comp_hom, types_comp_apply, diagonalSucc_hom_hom,
        leftRegularTensorIso_hom_hom, tensorIso_hom, mkIso_hom_hom, Equiv.toIso_hom,
        Action.tensorHom, Equiv.piFinSuccAbove_symm_apply, tensor_apply, types_id_apply,
        tensor_rho, MonoidHom.one_apply, End.one_def, hn fun j : Fin (n + 1) => f j.succ,
        Fin.insertNth_zero']
      refine' Fin.cases (Fin.cons_zero _ _) (fun i => _) x
      · simp only [Fin.cons_succ, mul_left_inj, inv_inj, Fin.castSucc_fin_succ] -/
    dsimp [actionDiagonalSucc]
    erw [hn (fun (j : Fin (n + 1)) => f j.succ)]
    exact Fin.cases rfl (fun i => rfl) x
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.Action_diagonal_succ_hom_apply groupCohomology.resolution.actionDiagonalSucc_hom_apply

theorem actionDiagonalSucc_inv_apply {G : Type u} [Group G] {n : ℕ} (g : G) (f : Fin n → G) :
    (actionDiagonalSucc G n).inv.hom (g, f) = (g • Fin.partialProd f : Fin (n + 1) → G) := by
  revert g
  induction' n with n hn
  · intro g
    funext (x : Fin 1)
    simp only [Subsingleton.elim x 0, Pi.smul_apply, Fin.partialProd_zero, smul_eq_mul, mul_one]
    rfl
  · intro g
/- Porting note (#11039): broken proof was
    ext
    dsimp only [actionDiagonalSucc]
    simp only [Iso.trans_inv, comp_hom, hn, diagonalSucc_inv_hom, types_comp_apply, tensorIso_inv,
      Iso.refl_inv, Action.tensorHom, id_hom, tensor_apply, types_id_apply,
      leftRegularTensorIso_inv_hom, tensor_rho, leftRegular_ρ_apply, Pi.smul_apply, smul_eq_mul]
    refine' Fin.cases _ _ x
    · simp only [Fin.cons_zero, Fin.partialProd_zero, mul_one]
    · intro i
      simpa only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Fin.partialProd_succ', mul_assoc] -/
    funext x
    dsimp [actionDiagonalSucc]
    erw [hn, Equiv.piFinSuccAbove_symm_apply]
    refine Fin.cases ?_ (fun i => ?_) x
    · simp only [Fin.insertNth_zero, Fin.cons_zero, Fin.partialProd_zero, mul_one]
    · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Fin.partialProd_succ', ← mul_assoc]
      rfl
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.Action_diagonal_succ_inv_apply groupCohomology.resolution.actionDiagonalSucc_inv_apply

end Action

section Rep

open Rep

/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
def diagonalSucc (n : ℕ) :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G ((Fin n → G) →₀ k) :=
  (linearization k G).mapIso (actionDiagonalSucc G n) ≪≫
    (asIso ((linearization k G).μ (Action.leftRegular G) _)).symm ≪≫
      tensorIso (Iso.refl _) (linearizationTrivialIso k G (Fin n → G))
#align group_cohomology.resolution.diagonal_succ groupCohomology.resolution.diagonalSucc

variable {k G n}

theorem diagonalSucc_hom_single (f : Gⁿ⁺¹) (a : k) :
    (diagonalSucc k G n).hom.hom (single f a) =
      single (f 0) 1 ⊗ₜ single (fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) a := by
/- Porting note (#11039): broken proof was
  dsimp only [diagonalSucc]
  simpa only [Iso.trans_hom, Iso.symm_hom, Action.comp_hom, ModuleCat.comp_def,
    LinearMap.comp_apply, Functor.mapIso_hom,
    linearization_map_hom_single (actionDiagonalSucc G n).hom f a, asIso_inv,
    linearization_μ_inv_hom, actionDiagonalSucc_hom_apply, finsuppTensorFinsupp',
    LinearEquiv.trans_symm, lcongr_symm, LinearEquiv.trans_apply, lcongr_single,
    TensorProduct.lid_symm_apply, finsuppTensorFinsupp_symm_single, LinearEquiv.coe_toLinearMap] -/
  change (𝟙 ((linearization k G).1.obj (Action.leftRegular G)).V
      ⊗ (linearizationTrivialIso k G (Fin n → G)).hom.hom)
    ((inv ((linearization k G).μ (Action.leftRegular G) { V := Fin n → G, ρ := 1 })).hom
      ((lmapDomain k k (actionDiagonalSucc G n).hom.hom) (single f a))) = _
  simp only [CategoryTheory.Functor.map_id, linearization_μ_inv_hom]
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [lmapDomain_apply, mapDomain_single, LinearEquiv.coe_toLinearMap, finsuppTensorFinsupp',
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, lcongr_symm, Equiv.refl_symm]
  erw [lcongr_single]
  rw [TensorProduct.lid_symm_apply, actionDiagonalSucc_hom_apply, finsuppTensorFinsupp_symm_single]
  rfl
#align group_cohomology.resolution.diagonal_succ_hom_single groupCohomology.resolution.diagonalSucc_hom_single

theorem diagonalSucc_inv_single_single (g : G) (f : Gⁿ) (a b : k) :
    (diagonalSucc k G n).inv.hom (Finsupp.single g a ⊗ₜ Finsupp.single f b) =
      single (g • partialProd f) (a * b) := by
/- Porting note (#11039): broken proof was
  dsimp only [diagonalSucc]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.refl_inv, tensorIso_inv, Action.tensorHom,
    Action.comp_hom, ModuleCat.comp_def, LinearMap.comp_apply, asIso_hom, Functor.mapIso_inv,
    ModuleCat.MonoidalCategory.hom_apply, linearizationTrivialIso_inv_hom_apply,
    linearization_μ_hom, Action.id_hom ((linearization k G).obj _), actionDiagonalSucc_inv_apply,
    ModuleCat.id_apply, LinearEquiv.coe_toLinearMap,
    finsuppTensorFinsupp'_single_tmul_single k (Action.leftRegular G).V,
    linearization_map_hom_single (actionDiagonalSucc G n).inv (g, f) (a * b)] -/
  change mapDomain (actionDiagonalSucc G n).inv.hom
    (lcongr (Equiv.refl (G × (Fin n → G))) (TensorProduct.lid k k)
      (finsuppTensorFinsupp k k k k G (Fin n → G) (single g a ⊗ₜ[k] single f b)))
    = single (g • partialProd f) (a * b)
  rw [finsuppTensorFinsupp_single, lcongr_single, mapDomain_single, Equiv.refl_apply,
    actionDiagonalSucc_inv_apply]
  rfl
#align group_cohomology.resolution.diagonal_succ_inv_single_single groupCohomology.resolution.diagonalSucc_inv_single_single

theorem diagonalSucc_inv_single_left (g : G) (f : Gⁿ →₀ k) (r : k) :
    (diagonalSucc k G n).inv.hom (Finsupp.single g r ⊗ₜ f) =
      Finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (fun f => single (g • partialProd f) r) f := by
  refine f.induction ?_ ?_
/- Porting note (#11039): broken proof was
  · simp only [TensorProduct.tmul_zero, map_zero]
  · intro a b x ha hb hx
    simp only [lift_apply, smul_single', mul_one, TensorProduct.tmul_add, map_add,
      diagonalSucc_inv_single_single, hx, Finsupp.sum_single_index, mul_comm b,
      zero_mul, single_zero] -/
  · rw [TensorProduct.tmul_zero, map_zero]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [map_zero]
  · intro _ _ _ _ _ hx
    rw [TensorProduct.tmul_add, map_add]; erw [map_add, hx]
    simp_rw [lift_apply, smul_single, smul_eq_mul]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [diagonalSucc_inv_single_single]
    rw [sum_single_index, mul_comm]
    rw [zero_mul, single_zero]
#align group_cohomology.resolution.diagonal_succ_inv_single_left groupCohomology.resolution.diagonalSucc_inv_single_left

theorem diagonalSucc_inv_single_right (g : G →₀ k) (f : Gⁿ) (r : k) :
    (diagonalSucc k G n).inv.hom (g ⊗ₜ Finsupp.single f r) =
      Finsupp.lift _ k G (fun a => single (a • partialProd f) r) g := by
  refine g.induction ?_ ?_
/- Porting note (#11039): broken proof was
  · simp only [TensorProduct.zero_tmul, map_zero]
  · intro a b x ha hb hx
    simp only [lift_apply, smul_single', map_add, hx, diagonalSucc_inv_single_single,
      TensorProduct.add_tmul, Finsupp.sum_single_index, zero_mul, single_zero] -/
  · rw [TensorProduct.zero_tmul, map_zero]
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [map_zero]
  · intro _ _ _ _ _ hx
    rw [TensorProduct.add_tmul, map_add]; erw [map_add, hx]
    simp_rw [lift_apply, smul_single']
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [diagonalSucc_inv_single_single]
    rw [sum_single_index]
    rw [zero_mul, single_zero]
#align group_cohomology.resolution.diagonal_succ_inv_single_right groupCohomology.resolution.diagonalSucc_inv_single_right

end Rep

open scoped TensorProduct

open Representation

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `TensorProduct.leftModule`, whilst that of the righthand side comes from
`Representation.asModule`. Allows us to use `Algebra.TensorProduct.basis` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k) ≃ₗ[MonoidAlgebra k G]
      (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  { (Rep.equivalenceModuleMonoidAlgebra.1.mapIso (diagonalSucc k G n).symm).toLinearEquiv with
    map_smul' := fun r x => by
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      erw [RingHom.id_apply, LinearEquiv.toFun_eq_coe, ← LinearEquiv.map_smul]
      congr 1
/- Porting note (#11039): broken proof was
      refine' x.induction_on _ (fun x y => _) fun y z hy hz => _
      · simp only [smul_zero]
      · simp only [TensorProduct.smul_tmul']
        show (r * x) ⊗ₜ y = _
        rw [← ofMulAction_self_smul_eq_mul, smul_tprod_one_asModule]
      · rw [smul_add, hz, hy, smul_add] -/
      show _ = Representation.asAlgebraHom (tensorObj (Rep.leftRegular k G)
        (Rep.trivial k G ((Fin n → G) →₀ k))).ρ r _
      refine x.induction_on ?_ (fun x y => ?_) fun y z hy hz => ?_
      · rw [smul_zero, map_zero]
      · rw [TensorProduct.smul_tmul', smul_eq_mul, ← ofMulAction_self_smul_eq_mul]
        exact (smul_tprod_one_asModule (Representation.ofMulAction k G G) r x y).symm
      · rw [smul_add, hz, hy, map_add] }
#align group_cohomology.resolution.of_mul_action_basis_aux groupCohomology.resolution.ofMulActionBasisAux

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Basis.map
    (Algebra.TensorProduct.basis (MonoidAlgebra k G)
      (Finsupp.basisSingleOne : Basis (Fin n → G) k ((Fin n → G) →₀ k)))
    (ofMulActionBasisAux k G n)
#align group_cohomology.resolution.of_mul_action_basis groupCohomology.resolution.ofMulActionBasis

theorem ofMulAction_free :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Module.Free.of_basis (ofMulActionBasis k G n)
#align group_cohomology.resolution.of_mul_action_free groupCohomology.resolution.ofMulAction_free

end Basis

end groupCohomology.resolution

namespace Rep

variable (n) [Group G] (A : Rep k G)

open groupCohomology.resolution

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
noncomputable def diagonalHomEquiv :
    (Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k
        ((diagonalSucc k G n).trans ((Representation.ofMulAction k G G).repOfTprodIso 1))
        (Iso.refl _) ≪≫ₗ
      (Rep.MonoidalClosed.linearHomEquivComm _ _ _ ≪≫ₗ Rep.leftRegularHomEquiv _) ≪≫ₗ
    (Finsupp.llift A k k (Fin n → G)).symm
set_option linter.uppercaseLean3 false in
#align Rep.diagonal_hom_equiv Rep.diagonalHomEquiv

variable {n A}

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that this
sends a morphism of representations `f : k[Gⁿ⁺¹] ⟶ A` to the function
`(g₁, ..., gₙ) ↦ f(1, g₁, g₁g₂, ..., g₁g₂...gₙ).` -/
theorem diagonalHomEquiv_apply (f : Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) (x : Fin n → G) :
    diagonalHomEquiv n A f x = f.hom (Finsupp.single (Fin.partialProd x) 1) := by
/- Porting note (#11039): broken proof was
  unfold diagonalHomEquiv
  simpa only [LinearEquiv.trans_apply, Rep.leftRegularHomEquiv_apply,
    MonoidalClosed.linearHomEquivComm_hom, Finsupp.llift_symm_apply, TensorProduct.curry_apply,
    Linear.homCongr_apply, Iso.refl_hom, Iso.trans_inv, Action.comp_hom, ModuleCat.comp_def,
    LinearMap.comp_apply, Representation.repOfTprodIso_inv_apply,
    diagonalSucc_inv_single_single (1 : G) x, one_smul, one_mul] -/
  change f.hom ((diagonalSucc k G n).inv.hom (Finsupp.single 1 1 ⊗ₜ[k] Finsupp.single x 1)) = _
  rw [diagonalSucc_inv_single_single, one_smul, one_mul]
set_option linter.uppercaseLean3 false in
#align Rep.diagonal_hom_equiv_apply Rep.diagonalHomEquiv_apply

/-- Given a `k`-linear `G`-representation `A`, `diagonalHomEquiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that the
inverse map sends a function `f : Gⁿ → A` to the representation morphism sending
`(g₀, ... gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`, where `ρ` is the representation attached
to `A`. -/
theorem diagonalHomEquiv_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single x 1) =
      A.ρ (x 0) (f fun i : Fin n => (x (Fin.castSucc i))⁻¹ * x i.succ) := by
  unfold diagonalHomEquiv
/- Porting note (#11039): broken proof was
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Rep.leftRegularHomEquiv_symm_apply, Linear.homCongr_symm_apply, Action.comp_hom, Iso.refl_inv,
    Category.comp_id, Rep.MonoidalClosed.linearHomEquivComm_symm_hom, Iso.trans_hom,
    ModuleCat.comp_def, LinearMap.comp_apply, Representation.repOfTprodIso_apply,
    diagonalSucc_hom_single x (1 : k), TensorProduct.uncurry_apply, Rep.leftRegularHom_hom,
    Finsupp.lift_apply, ihom_obj_ρ_def, Rep.ihom_obj_ρ_apply, Finsupp.sum_single_index, zero_smul,
    one_smul, Rep.of_ρ, Rep.Action_ρ_eq_ρ, Rep.trivial_def (x 0)⁻¹, Finsupp.llift_apply A k k] -/
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    leftRegularHomEquiv_symm_apply, Linear.homCongr_symm_apply, Iso.trans_hom, Iso.refl_inv,
    Category.comp_id, Action.comp_hom, MonoidalClosed.linearHomEquivComm_symm_hom]
  -- Porting note: This is a sure sign that coercions for morphisms in `ModuleCat`
  -- are still not set up properly.
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [ModuleCat.coe_comp]
  simp only [ModuleCat.coe_comp, Function.comp_apply]
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [diagonalSucc_hom_single]
  erw [TensorProduct.uncurry_apply, Finsupp.lift_apply, Finsupp.sum_single_index]
  · simp only [one_smul]
    erw [Representation.linHom_apply]
    simp only [LinearMap.comp_apply, MonoidHom.one_apply, LinearMap.one_apply]
    erw [Finsupp.llift_apply]
    rw [Finsupp.lift_apply]
    erw [Finsupp.sum_single_index]
    · rw [one_smul]
    · rw [zero_smul]
  · rw [zero_smul]
set_option linter.uppercaseLean3 false in
#align Rep.diagonal_hom_equiv_symm_apply Rep.diagonalHomEquiv_symm_apply

/-- Auxiliary lemma for defining group cohomology, used to show that the isomorphism
`diagonalHomEquiv` commutes with the differentials in two complexes which compute
group cohomology. -/
theorem diagonalHomEquiv_symm_partialProd_succ (f : (Fin n → G) → A) (g : Fin (n + 1) → G)
    (a : Fin (n + 1)) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single (Fin.partialProd g ∘ a.succ.succAbove) 1)
      = f (Fin.contractNth a (· * ·) g) := by
  simp only [diagonalHomEquiv_symm_apply, Function.comp_apply, Fin.succ_succAbove_zero,
    Fin.partialProd_zero, map_one, Fin.succ_succAbove_succ, LinearMap.one_apply,
    Fin.partialProd_succ]
  congr
  ext
  rw [← Fin.partialProd_succ, Fin.inv_partialProd_mul_eq_contractNth]
set_option linter.uppercaseLean3 false in
#align Rep.diagonal_hom_equiv_symm_partial_prod_succ Rep.diagonalHomEquiv_symm_partialProd_succ

end Rep

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) <| MonCat.of G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl
#align classifying_space_universal_cover classifyingSpaceUniversalCover

namespace classifyingSpaceUniversalCover

open CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- When the category is `G`-Set, `cechNerveTerminalFrom` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso :
    cechNerveTerminalFrom (Action.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun n => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc, limit.isoLimitCone_hom_π, limit.lift_π, Category.assoc]
    exact (limit.isoLimitCone_hom_π _ _).symm
#align classifying_space_universal_cover.cech_nerve_terminal_from_iso classifyingSpaceUniversalCover.cechNerveTerminalFromIso

/-- As a simplicial set, `cechNerveTerminalFrom` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ :=
  NatIso.ofComponents (fun _ => Types.productIso _) fun _ =>
    Matrix.ext fun _ _ => Types.Limit.lift_π_apply (Discrete.functor fun _ ↦ G) _ _ _
#align classifying_space_universal_cover.cech_nerve_terminal_from_iso_comp_forget classifyingSpaceUniversalCover.cechNerveTerminalFromIsoCompForget

variable (k)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `Fin 1 → G` to the terminal object in `Type u`. -/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun _ _ _ => Subsingleton.elim _ _
#align classifying_space_universal_cover.comp_forget_augmented classifyingSpaceUniversalCover.compForgetAugmented

/-- The augmented Čech nerve of the map from `Fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (Arrow.mk <| terminal.from G).augmentedCechNerve :=
  AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨fun _ => (1 : G),
      @Subsingleton.elim _ (@Unique.instSubsingleton _ (Limits.uniqueToTerminal _)) _ _⟩
#align classifying_space_universal_cover.extra_degeneracy_augmented_cech_nerve classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `Fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) := by
  refine
    ExtraDegeneracy.ofIso (?_ : (Arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extraDegeneracyAugmentedCechNerve G)
  exact
    Comma.isoMk (CechNerveTerminalFrom.iso G ≪≫ cechNerveTerminalFromIsoCompForget G)
      (Iso.refl _) (by ext : 1; exact IsTerminal.hom_ext terminalIsTerminal _ _)
#align classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented

/-- The free functor `Type u ⥤ ModuleCat.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `Fin 1 → G` to the terminal object
in `Type u`. -/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj (compForgetAugmented G)
set_option linter.uppercaseLean3 false in
#align classifying_space_universal_cover.comp_forget_augmented.to_Module classifyingSpaceUniversalCover.compForgetAugmented.toModule

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `Fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ ModuleCat.{u} k`, the resulting augmented simplicial `k`-module has an extra
degeneracy. -/
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  ExtraDegeneracy.map (extraDegeneracyCompForgetAugmented G) (ModuleCat.free k)
set_option linter.uppercaseLean3 false in
#align classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented_to_Module classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmentedToModule

end classifyingSpaceUniversalCover

variable (k)

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def groupCohomology.resolution [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1)
#align group_cohomology.resolution groupCohomology.resolution

namespace groupCohomology.resolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))
#align group_cohomology.resolution.d groupCohomology.resolution.d

variable {k G}

@[simp]
theorem d_of {G : Type u} {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) := by
  simp [d]
#align group_cohomology.resolution.d_of groupCohomology.resolution.d_of

variable (k G)

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso (n : ℕ) : (groupCohomology.resolution k G).X n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.X_iso groupCohomology.resolution.xIso

instance x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((groupCohomology.resolution k G).X n) :=
  Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (Fin (n + 1) → G)).asModule)
      _ (ofMulActionBasis k G n)
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.X_projective groupCohomology.resolution.x_projective

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : ((groupCohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  dsimp [groupCohomology.resolution]
/- Porting note (#11039): broken proof was
  simpa [← @intCast_smul k, simplicial_object.δ] -/
  simp_rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, SimplicialObject.δ,
    Functor.comp_map, ← intCast_smul (k := k) ((-1) ^ _ : ℤ), Int.cast_pow, Int.cast_neg,
    Int.cast_one, Action.sum_hom, Action.smul_hom, Rep.linearization_map_hom]
  rw [LinearMap.coeFn_sum, Fintype.sum_apply]
  erw [d_of (k := k) x]
/- Porting note: want to rewrite `LinearMap.smul_apply` but simp/simp_rw won't do it; I need erw,
so using Finset.sum_congr to get rid of the binder -/
  refine Finset.sum_congr rfl fun _ _ => ?_
  erw [LinearMap.smul_apply]
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.smul_single', mul_one]
  rfl
#align group_cohomology.resolution.d_eq groupCohomology.resolution.d_eq

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (groupCohomology.resolution k G)
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.forget₂_to_Module groupCohomology.resolution.forget₂ToModuleCat

/-- If we apply the free functor `Type u ⥤ ModuleCat.{u} k` to the universal cover of the
classifying space of `G` as a simplicial set, then take the alternating face map complex, the result
is isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      groupCohomology.resolution.forget₂ToModuleCat k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1))
#align group_cohomology.resolution.comp_forget_augmented_iso groupCohomology.resolution.compForgetAugmentedIso

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleCatHomotopyEquiv :
    HomotopyEquiv (groupCohomology.resolution.forget₂ToModuleCat k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (Rep k G) _).obj <| Rep.trivial k G k)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u)
              Types.terminalIso.toEquiv.unique).toModuleIso)
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.forget₂_to_Module_homotopy_equiv groupCohomology.resolution.forget₂ToModuleCatHomotopyEquiv

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k where
  hom := Finsupp.total _ _ _ fun _ => (1 : k)
  comm g := Finsupp.lhom_ext' fun _ => LinearMap.ext_ring (by
    show
      Finsupp.total (Fin 1 → G) k k (fun _ => (1 : k)) (Finsupp.mapDomain _ (Finsupp.single _ _)) =
        Finsupp.total (Fin 1 → G) k k (fun _ => (1 : k)) (Finsupp.single _ _)
    simp only [Finsupp.mapDomain_single, Finsupp.total_single])
#align group_cohomology.resolution.ε groupCohomology.resolution.ε

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  show (HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _).f 0 = _
  simp only [HomologicalComplex.comp_f]
  dsimp
  convert Category.id_comp (X := (forget₂ToModuleCat k G).X 0) _
  · dsimp only [HomotopyEquiv.ofIso, compForgetAugmentedIso]
    simp only [Iso.symm_hom, eqToIso.inv, HomologicalComplex.eqToHom_f, eqToHom_refl]
  trans (Finsupp.total _ _ _ fun _ => (1 : k)).comp ((ModuleCat.free k).map (terminal.from _))
  · dsimp
    erw [Finsupp.lmapDomain_total (α := Fin 1 → G) (R := k) (α' := ⊤_ Type u)
        (v := fun _ => (1 : k)) (v' := fun _ => (1 : k))
        (terminal.from
          ((classifyingSpaceUniversalCover G).obj (Opposite.op (SimplexCategory.mk 0))).V)
        LinearMap.id fun i => rfl,
      LinearMap.id_comp]
    rfl
  · congr
    · ext x
      dsimp (config := { unfoldPartialApp := true }) [HomotopyEquiv.ofIso,
        Finsupp.LinearEquiv.finsuppUnique]
      rw [Finsupp.total_single, one_smul, @Unique.eq_default _ Types.terminalIso.toEquiv.unique x,
        ChainComplex.single₀_map_f_zero, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        Finsupp.equivFunOnFinite_apply, Finsupp.single_eq_same]
    · exact @Subsingleton.elim _ (@Unique.instSubsingleton _ (Limits.uniqueToTerminal _)) _ _
set_option linter.uppercaseLean3 false in
#align group_cohomology.resolution.forget₂_to_Module_homotopy_equiv_f_0_eq groupCohomology.resolution.forget₂ToModuleCatHomotopyEquiv_f_0_eq

theorem d_comp_ε : (groupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 := by
  ext : 1
  refine LinearMap.ext fun x => ?_
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq,
      ← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 this _
#align group_cohomology.resolution.d_comp_ε groupCohomology.resolution.d_comp_ε

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def εToSingle₀ :
    groupCohomology.resolution k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((groupCohomology.resolution k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩
#align group_cohomology.resolution.ε_to_single₀ groupCohomology.resolution.εToSingle₀

theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _ =
      (forget₂ToModuleCatHomotopyEquiv k G).hom := by
  dsimp
  ext1
  dsimp
  simpa using (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm
#align group_cohomology.resolution.ε_to_single₀_comp_eq groupCohomology.resolution.εToSingle₀_comp_eq

theorem quasiIso_forget₂_εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) := by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)
#align group_cohomology.resolution.quasi_iso_of_forget₂_ε_to_single₀ groupCohomology.resolution.quasiIso_forget₂_εToSingle₀

instance : QuasiIso (εToSingle₀ k G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀

end Exactness

end groupCohomology.resolution

open groupCohomology.resolution HomologicalComplex.Hom

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def groupCohomology.projectiveResolution : ProjectiveResolution (Rep.trivial k G k) where
  π := εToSingle₀ k G
set_option linter.uppercaseLean3 false in
#align group_cohomology.ProjectiveResolution groupCohomology.projectiveResolution

instance : EnoughProjectives (Rep k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2
    ModuleCat.moduleCat_enoughProjectives.{u}

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `groupCohomology.resolution k G`. -/
def groupCohomology.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((groupCohomology.resolution k G).linearYonedaObj k V).homology n :=
  (groupCohomology.projectiveResolution k G).isoExt n V
set_option linter.uppercaseLean3 false in
#align group_cohomology.Ext_iso groupCohomology.extIso
