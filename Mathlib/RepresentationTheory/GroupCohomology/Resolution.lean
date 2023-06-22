/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston

! This file was ported from Lean 3 source module representation_theory.group_cohomology.resolution
! leanprover-community/mathlib commit cec81510e48e579bde6acd8568c06a87af045b63
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.RepresentationTheory.Rep

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

Putting this material together allows us to define `group_cohomology.ProjectiveResolution`, the
standard projective resolution of `k` as a trivial `k`-linear `G`-representation.

## Main definitions

 * `group_cohomology.resolution.Action_diagonal_succ`
 * `group_cohomology.resolution.diagonal_succ`
 * `group_cohomology.resolution.of_mul_action_basis`
 * `classifying_space_universal_cover`
 * `group_cohomology.resolution.forget₂_to_Module_homotopy_equiv`
 * `group_cohomology.ProjectiveResolution`

## Implementation notes

We express `k[G]`-module structures on a module `k`-module `V` using the `representation`
definition. We avoid using instances `module (G →₀ k) V` so that we do not run into possible
scalar action diamonds.

We also use the category theory library to bundle the type `k[Gⁿ]` - or more generally `k[H]` when
`H` has `G`-action - and the representation together, as a term of type `Rep k G`, and call it
`Rep.of_mul_action k G H.` This enables us to express the fact that certain maps are
`G`-equivariant by constructing morphisms in the category `Rep k G`, i.e., representations of `G`
over `k`.
-/


noncomputable section

universe u v w

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory

local notation "Gⁿ" => Fin n → G

local notation "Gⁿ⁺¹" => Fin (n + 1) → G

namespace GroupCohomology.resolution

open Finsupp hiding lift

open Fin (partialProd)

section Basis

variable (k G n) [Group G]

section Action

open Action

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
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
      tensorIso (Iso.refl _) (Action_diagonal_succ n) ≪≫
        leftRegularTensorIso _ _ ≪≫
          tensorIso (Iso.refl _)
            (mkIso (Equiv.piFinSuccAboveEquiv (fun j => G) 0).symm.toIso fun g => rfl)
#align group_cohomology.resolution.Action_diagonal_succ GroupCohomology.Resolution.actionDiagonalSucc

theorem actionDiagonalSucc_hom_apply {G : Type u} [Group G] {n : ℕ} (f : Fin (n + 1) → G) :
    (actionDiagonalSucc G n).hom.hom f = (f 0, fun i => (f i.cast_succ)⁻¹ * f i.succ) := by
  induction' n with n hn
  · exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  · ext
    · rfl
    · dsimp only [Action_diagonal_succ]
      simp only [iso.trans_hom, comp_hom, types_comp_apply, diagonal_succ_hom_hom,
        left_regular_tensor_iso_hom_hom, tensor_iso_hom, mk_iso_hom_hom, Equiv.toIso_hom,
        tensor_hom, Equiv.piFinSuccAboveEquiv_symm_apply, tensor_apply, types_id_apply, tensor_rho,
        MonoidHom.one_apply, End.one_def, hn fun j : Fin (n + 1) => f j.succ, Fin.insertNth_zero']
      refine' Fin.cases (Fin.cons_zero _ _) (fun i => _) x
      · simp only [Fin.cons_succ, mul_left_inj, inv_inj, Fin.castSucc_fin_succ]
#align group_cohomology.resolution.Action_diagonal_succ_hom_apply GroupCohomology.Resolution.actionDiagonalSucc_hom_apply

theorem actionDiagonalSucc_inv_apply {G : Type u} [Group G] {n : ℕ} (g : G) (f : Fin n → G) :
    (actionDiagonalSucc G n).inv.hom (g, f) = (g • Fin.partialProd f : Fin (n + 1) → G) := by
  revert g
  induction' n with n hn
  · intro g
    ext
    simpa only [Subsingleton.elim x 0, Pi.smul_apply, Fin.partialProd_zero, smul_eq_mul, mul_one]
  · intro g
    ext
    dsimp only [Action_diagonal_succ]
    simp only [iso.trans_inv, comp_hom, hn, diagonal_succ_inv_hom, types_comp_apply, tensor_iso_inv,
      iso.refl_inv, tensor_hom, id_hom, tensor_apply, types_id_apply,
      left_regular_tensor_iso_inv_hom, tensor_rho, left_regular_ρ_apply, Pi.smul_apply, smul_eq_mul]
    refine' Fin.cases _ _ x
    · simp only [Fin.cons_zero, Fin.partialProd_zero, mul_one]
    · intro i
      simpa only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Fin.partialProd_succ', mul_assoc]
#align group_cohomology.resolution.Action_diagonal_succ_inv_apply GroupCohomology.Resolution.actionDiagonalSucc_inv_apply

end Action

section Rep

open Rep

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An isomorphism of `k`-linear representations of `G` from `k[Gⁿ⁺¹]` to `k[G] ⊗ₖ k[Gⁿ]` (on
which `G` acts by `ρ(g₁)(g₂ ⊗ x) = (g₁ * g₂) ⊗ x`) sending `(g₀, ..., gₙ)` to
`g₀ ⊗ (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ)`. The inverse sends `g₀ ⊗ (g₁, ..., gₙ)` to
`(g₀, g₀g₁, ..., g₀g₁...gₙ)`. -/
def diagonalSucc (n : ℕ) :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G ((Fin n → G) →₀ k) :=
  (linearization k G).mapIso (actionDiagonalSucc G n) ≪≫
    (asIso ((linearization k G).μ (Action.leftRegular G) _)).symm ≪≫
      tensorIso (Iso.refl _) (linearizationTrivialIso k G (Fin n → G))
#align group_cohomology.resolution.diagonal_succ GroupCohomology.Resolution.diagonalSucc

variable {k G n}

theorem diagonalSucc_hom_single (f : Gⁿ⁺¹) (a : k) :
    (diagonalSucc k G n).hom.hom (single f a) =
      single (f 0) 1 ⊗ₜ single (fun i => (f i.cast_succ)⁻¹ * f i.succ) a := by
  dsimp only [diagonal_succ]
  simpa only [iso.trans_hom, iso.symm_hom, Action.comp_hom, ModuleCat.comp_def,
    LinearMap.comp_apply, functor.map_iso_hom,
    linearization_map_hom_single (Action_diagonal_succ G n).hom f a, as_iso_inv,
    linearization_μ_inv_hom, Action_diagonal_succ_hom_apply, finsuppTensorFinsupp',
    LinearEquiv.trans_symm, lcongr_symm, LinearEquiv.trans_apply, lcongr_single,
    TensorProduct.lid_symm_apply, finsuppTensorFinsupp_symm_single, LinearEquiv.coe_toLinearMap]
#align group_cohomology.resolution.diagonal_succ_hom_single GroupCohomology.Resolution.diagonalSucc_hom_single

theorem diagonalSucc_inv_single_single (g : G) (f : Gⁿ) (a b : k) :
    (diagonalSucc k G n).inv.hom (Finsupp.single g a ⊗ₜ Finsupp.single f b) =
      single (g • partialProd f) (a * b) := by
  dsimp only [diagonal_succ]
  simp only [iso.trans_inv, iso.symm_inv, iso.refl_inv, tensor_iso_inv, Action.tensorHom,
    Action.comp_hom, ModuleCat.comp_def, LinearMap.comp_apply, as_iso_hom, functor.map_iso_inv,
    ModuleCat.MonoidalCategory.hom_apply, linearization_trivial_iso_inv_hom_apply,
    linearization_μ_hom, Action.id_hom ((linearization k G).obj _), Action_diagonal_succ_inv_apply,
    ModuleCat.id_apply, LinearEquiv.coe_toLinearMap,
    finsuppTensorFinsupp'_single_tmul_single k (Action.leftRegular G).V,
    linearization_map_hom_single (Action_diagonal_succ G n).inv (g, f) (a * b)]
#align group_cohomology.resolution.diagonal_succ_inv_single_single GroupCohomology.Resolution.diagonalSucc_inv_single_single

theorem diagonalSucc_inv_single_left (g : G) (f : Gⁿ →₀ k) (r : k) :
    (diagonalSucc k G n).inv.hom (Finsupp.single g r ⊗ₜ f) =
      Finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (fun f => single (g • partialProd f) r) f := by
  refine' f.induction _ _
  · simp only [TensorProduct.tmul_zero, map_zero]
  · intro a b x ha hb hx
    simp only [lift_apply, smul_single', mul_one, TensorProduct.tmul_add, map_add,
      diagonal_succ_inv_single_single, hx, Finsupp.sum_single_index, mul_comm b,
      MulZeroClass.zero_mul, single_zero]
#align group_cohomology.resolution.diagonal_succ_inv_single_left GroupCohomology.Resolution.diagonalSucc_inv_single_left

theorem diagonalSucc_inv_single_right (g : G →₀ k) (f : Gⁿ) (r : k) :
    (diagonalSucc k G n).inv.hom (g ⊗ₜ Finsupp.single f r) =
      Finsupp.lift _ k G (fun a => single (a • partialProd f) r) g := by
  refine' g.induction _ _
  · simp only [TensorProduct.zero_tmul, map_zero]
  · intro a b x ha hb hx
    simp only [lift_apply, smul_single', map_add, hx, diagonal_succ_inv_single_single,
      TensorProduct.add_tmul, Finsupp.sum_single_index, MulZeroClass.zero_mul, single_zero]
#align group_cohomology.resolution.diagonal_succ_inv_single_right GroupCohomology.Resolution.diagonalSucc_inv_single_right

end Rep

variable (k G n)

open scoped TensorProduct

open Representation

/-- The `k[G]`-linear isomorphism `k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹]`, where the `k[G]`-module structure on
the lefthand side is `tensor_product.left_module`, whilst that of the righthand side comes from
`representation.as_module`. Allows us to use `basis.algebra_tensor_product` to get a `k[G]`-basis
of the righthand side. -/
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k) ≃ₗ[MonoidAlgebra k G]
      (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  { (Rep.equivalenceModuleMonoidAlgebra.1.mapIso (diagonalSucc k G n).symm).toLinearEquiv with
    map_smul' := fun r x => by
      rw [RingHom.id_apply, LinearEquiv.toFun_eq_coe, ← LinearEquiv.map_smul]
      congr 1
      refine' x.induction_on _ (fun x y => _) fun y z hy hz => _
      · simp only [smul_zero]
      · simp only [TensorProduct.smul_tmul']
        show (r * x) ⊗ₜ y = _
        rw [← of_mul_action_self_smul_eq_mul, smul_tprod_one_as_module]
      · rw [smul_add, hz, hy, smul_add] }
#align group_cohomology.resolution.of_mul_action_basis_aux GroupCohomology.Resolution.ofMulActionBasisAux

/-- A `k[G]`-basis of `k[Gⁿ⁺¹]`, coming from the `k[G]`-linear isomorphism
`k[G] ⊗ₖ k[Gⁿ] ≃ k[Gⁿ⁺¹].` -/
def ofMulActionBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  @Basis.map _ (MonoidAlgebra k G) (MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k)) _ _ _ _ _ _
    (@Algebra.TensorProduct.basis k _ (MonoidAlgebra k G) _ _ ((Fin n → G) →₀ k) _ _ (Fin n → G)
      ⟨LinearEquiv.refl k _⟩)
    (ofMulActionBasisAux k G n)
#align group_cohomology.resolution.of_mul_action_basis GroupCohomology.Resolution.ofMulActionBasis

theorem ofMulAction_free :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Module.Free.of_basis (ofMulActionBasis k G n)
#align group_cohomology.resolution.of_mul_action_free GroupCohomology.Resolution.ofMulAction_free

end Basis

end GroupCohomology.resolution

namespace Rep

variable (n) [Group G] (A : Rep k G)

open GroupCohomology.resolution

/-- Given a `k`-linear `G`-representation `A`, the set of representation morphisms
`Hom(k[Gⁿ⁺¹], A)` is `k`-linearly isomorphic to the set of functions `Gⁿ → A`. -/
noncomputable def diagonalHomEquiv :
    (Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k
        ((diagonalSucc k G n).trans ((Representation.ofMulAction k G G).repOfTprodIso 1))
        (Iso.refl _) ≪≫ₗ
      (Rep.MonoidalClosed.linearHomEquivComm _ _ _ ≪≫ₗ Rep.leftRegularHomEquiv _) ≪≫ₗ
    (Finsupp.llift A k k (Fin n → G)).symm
#align Rep.diagonal_hom_equiv Rep.diagonalHomEquiv

variable {n A}

/-- Given a `k`-linear `G`-representation `A`, `diagonal_hom_equiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that this
sends a morphism of representations `f : k[Gⁿ⁺¹] ⟶ A` to the function
`(g₁, ..., gₙ) ↦ f(1, g₁, g₁g₂, ..., g₁g₂...gₙ).` -/
theorem diagonalHomEquiv_apply (f : Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) (x : Fin n → G) :
    diagonalHomEquiv n A f x = f.hom (Finsupp.single (Fin.partialProd x) 1) := by
  unfold diagonal_hom_equiv
  simpa only [LinearEquiv.trans_apply, Rep.leftRegularHomEquiv_apply,
    monoidal_closed.linear_hom_equiv_comm_hom, Finsupp.llift_symm_apply, TensorProduct.curry_apply,
    linear.hom_congr_apply, iso.refl_hom, iso.trans_inv, Action.comp_hom, ModuleCat.comp_def,
    LinearMap.comp_apply, Representation.repOfTprodIso_inv_apply,
    diagonal_succ_inv_single_single (1 : G) x, one_smul, one_mul]
#align Rep.diagonal_hom_equiv_apply Rep.diagonalHomEquiv_apply

/-- Given a `k`-linear `G`-representation `A`, `diagonal_hom_equiv` is a `k`-linear isomorphism of
the set of representation morphisms `Hom(k[Gⁿ⁺¹], A)` with `Fun(Gⁿ, A)`. This lemma says that the
inverse map sends a function `f : Gⁿ → A` to the representation morphism sending
`(g₀, ... gₙ) ↦ ρ(g₀)(f(g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`, where `ρ` is the representation attached
to `A`. -/
theorem diagonalHomEquiv_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single x 1) =
      A.ρ (x 0) (f fun i : Fin n => (x i.cast_succ)⁻¹ * x i.succ) := by
  unfold diagonal_hom_equiv
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Rep.leftRegularHomEquiv_symm_apply, linear.hom_congr_symm_apply, Action.comp_hom, iso.refl_inv,
    category.comp_id, Rep.MonoidalClosed.linearHomEquivComm_symm_hom, iso.trans_hom,
    ModuleCat.comp_def, LinearMap.comp_apply, Representation.repOfTprodIso_apply,
    diagonal_succ_hom_single x (1 : k), TensorProduct.uncurry_apply, Rep.leftRegularHom_hom,
    Finsupp.lift_apply, ihom_obj_ρ_def, Rep.ihom_obj_ρ_apply, Finsupp.sum_single_index, zero_smul,
    one_smul, Rep.of_ρ, Rep.Action_ρ_eq_ρ, Rep.trivial_def (x 0)⁻¹, Finsupp.llift_apply A k k]
#align Rep.diagonal_hom_equiv_symm_apply Rep.diagonalHomEquiv_symm_apply

/-- Auxiliary lemma for defining group cohomology, used to show that the isomorphism
`diagonal_hom_equiv` commutes with the differentials in two complexes which compute
group cohomology. -/
theorem diagonalHomEquiv_symm_partialProd_succ (f : (Fin n → G) → A) (g : Fin (n + 1) → G)
    (a : Fin (n + 1)) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single (Fin.partialProd g ∘ a.succ.succAbove) 1) =
      f (Fin.contractNth a (· * ·) g) := by
  simp only [diagonal_hom_equiv_symm_apply, Function.comp_apply, Fin.succ_succAbove_zero,
    Fin.partialProd_zero, map_one, Fin.succ_succAbove_succ, LinearMap.one_apply,
    Fin.partialProd_succ]
  congr
  ext
  rw [← Fin.partialProd_succ, Fin.inv_partialProd_mul_eq_contractNth]
#align Rep.diagonal_hom_equiv_symm_partial_prod_succ Rep.diagonalHomEquiv_symm_partialProd_succ

end Rep

variable (G)

/-- The simplicial `G`-set sending `[n]` to `Gⁿ⁺¹` equipped with the diagonal action of `G`. -/
def classifyingSpaceUniversalCover [Monoid G] : SimplicialObject (Action (Type u) <| MonCat.of G)
    where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map m n f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm' := fun g => rfl }
  map_id' n := rfl
  map_comp' i j k f g := rfl
#align classifying_space_universal_cover classifyingSpaceUniversalCover

namespace classifyingSpaceUniversalCover

open CategoryTheory CategoryTheory.Limits

variable [Monoid G]

/-- When the category is `G`-Set, `cech_nerve_terminal_from` of `G` with the left regular action is
isomorphic to `EG`, the universal cover of the classifying space of `G` as a simplicial `G`-set. -/
def cechNerveTerminalFromIso :
    cechNerveTerminalFrom (Action.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun n => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun m n f =>
    by
    refine' is_limit.hom_ext (Action.ofMulActionLimitCone.{u, 0} _ _).2 fun j => _
    dsimp only [cech_nerve_terminal_from, pi.lift]
    dsimp
    rw [category.assoc, limit.iso_limit_cone_hom_π, limit.lift_π, category.assoc]
    exact (limit.iso_limit_cone_hom_π _ _).symm
#align classifying_space_universal_cover.cech_nerve_terminal_from_iso classifyingSpaceUniversalCover.cechNerveTerminalFromIso

/-- As a simplicial set, `cech_nerve_terminal_from` of a monoid `G` is isomorphic to the universal
cover of the classifying space of `G` as a simplicial set. -/
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ :=
  NatIso.ofComponents (fun n => Types.productIso _) fun m n f =>
    Matrix.ext fun i j => Types.Limit.lift_π_apply _ _ _ _
#align classifying_space_universal_cover.cech_nerve_terminal_from_iso_comp_forget classifyingSpaceUniversalCover.cechNerveTerminalFromIsoCompForget

variable (k G)

open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`. -/
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun i g h => Subsingleton.elim _ _
#align classifying_space_universal_cover.comp_forget_augmented classifyingSpaceUniversalCover.compForgetAugmented

/-- The augmented Čech nerve of the map from `fin 1 → G` to the terminal object in `Type u` has an
extra degeneracy. -/
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (Arrow.mk <| terminal.from G).augmentedCechNerve :=
  AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨fun x => (1 : G),
      @Subsingleton.elim _ (@Unique.subsingleton _ (Limits.uniqueToTerminal _)) _ _⟩
#align classifying_space_universal_cover.extra_degeneracy_augmented_cech_nerve classifyingSpaceUniversalCover.extraDegeneracyAugmentedCechNerve

/-- The universal cover of the classifying space of `G` as a simplicial set, augmented by the map
from `fin 1 → G` to the terminal object in `Type u`, has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) := by
  refine'
    extra_degeneracy.of_iso (_ : (arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extra_degeneracy_augmented_cech_nerve G)
  exact
    comma.iso_mk (cech_nerve_terminal_from.iso G ≪≫ cech_nerve_terminal_from_iso_comp_forget G)
      (iso.refl _) (by ext : 2 <;> apply is_terminal.hom_ext terminal_is_terminal)
#align classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented

/-- The free functor `Type u ⥤ Module.{u} k` applied to the universal cover of the classifying
space of `G` as a simplicial set, augmented by the map from `fin 1 → G` to the terminal object
in `Type u`. -/
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj (compForgetAugmented G)
#align classifying_space_universal_cover.comp_forget_augmented.to_Module classifyingSpaceUniversalCover.compForgetAugmented.toModule

/-- If we augment the universal cover of the classifying space of `G` as a simplicial set by the
map from `fin 1 → G` to the terminal object in `Type u`, then apply the free functor
`Type u ⥤ Module.{u} k`, the resulting augmented simplicial `k`-module has an extra degeneracy. -/
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  ExtraDegeneracy.map (extraDegeneracyCompForgetAugmented G) (ModuleCat.free k)
#align classifying_space_universal_cover.extra_degeneracy_comp_forget_augmented_to_Module classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmentedToModule

end classifyingSpaceUniversalCover

variable (k)

/-- The standard resolution of `k` as a trivial representation, defined as the alternating
face map complex of a simplicial `k`-linear `G`-representation. -/
def GroupCohomology.resolution [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1)
#align group_cohomology.resolution GroupCohomology.resolution

namespace GroupCohomology.resolution

open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits

variable (k G) [Monoid G]

/-- The `k`-linear map underlying the differential in the standard resolution of `k` as a trivial
`k`-linear `G`-representation. It sends `(g₀, ..., gₙ) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ)`. -/
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).Sum fun p =>
      Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))
#align group_cohomology.resolution.d GroupCohomology.resolution.d

variable {k G}

@[simp]
theorem d_of {G : Type u} {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.Sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) :=
  by simp [d]
#align group_cohomology.resolution.d_of GroupCohomology.resolution.d_of

variable (k G)

/-- The `n`th object of the standard resolution of `k` is definitionally isomorphic to `k[Gⁿ⁺¹]`
equipped with the representation induced by the diagonal action of `G`. -/
def xIso (n : ℕ) : (GroupCohomology.resolution k G).pt n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _
#align group_cohomology.resolution.X_iso GroupCohomology.resolution.xIso

theorem x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((GroupCohomology.resolution k G).pt n) :=
  Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (Fin (n + 1) → G)).asModule)
      _ (ofMulActionBasis k G n)
#align group_cohomology.resolution.X_projective GroupCohomology.resolution.x_projective

/-- Simpler expression for the differential in the standard resolution of `k` as a
`G`-representation. It sends `(g₀, ..., gₙ₊₁) ↦ ∑ (-1)ⁱ • (g₀, ..., ĝᵢ, ..., gₙ₊₁)`. -/
theorem d_eq (n : ℕ) : ((GroupCohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) := by
  ext x y
  dsimp [GroupCohomology.resolution]
  simpa [← @intCast_smul k, simplicial_object.δ]
#align group_cohomology.resolution.d_eq GroupCohomology.resolution.d_eq

section Exactness

/-- The standard resolution of `k` as a trivial representation as a complex of `k`-modules. -/
def forget₂ToModule :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (GroupCohomology.resolution k G)
#align group_cohomology.resolution.forget₂_to_Module GroupCohomology.resolution.forget₂ToModule

/-- If we apply the free functor `Type u ⥤ Module.{u} k` to the universal cover of the classifying
space of `G` as a simplicial set, then take the alternating face map complex, the result is
isomorphic to the standard resolution of the trivial `G`-representation `k` as a complex of
`k`-modules. -/
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      GroupCohomology.resolution.forget₂ToModule k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ (Rep.linearization k G).1.1))
#align group_cohomology.resolution.comp_forget_augmented_iso GroupCohomology.resolution.compForgetAugmentedIso

/-- As a complex of `k`-modules, the standard resolution of the trivial `G`-representation `k` is
homotopy equivalent to the complex which is `k` at 0 and 0 elsewhere. -/
def forget₂ToModuleHomotopyEquiv :
    HomotopyEquiv (GroupCohomology.resolution.forget₂ToModule k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (Rep k G) _).obj <| Rep.trivial k G k)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u)
              Types.terminalIso.toEquiv.unique).toModuleIso)
#align group_cohomology.resolution.forget₂_to_Module_homotopy_equiv GroupCohomology.resolution.forget₂ToModuleHomotopyEquiv

/-- The hom of `k`-linear `G`-representations `k[G¹] → k` sending `∑ nᵢgᵢ ↦ ∑ nᵢ`. -/
def ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k where
  hom := Finsupp.total _ _ _ fun f => (1 : k)
  comm' g := by
    ext
    show
      Finsupp.total (Fin 1 → G) k k (fun f => (1 : k)) (Finsupp.mapDomain _ (Finsupp.single _ _)) =
        Finsupp.total _ _ _ _ (Finsupp.single _ _)
    simp only [Finsupp.mapDomain_single, Finsupp.total_single]
#align group_cohomology.resolution.ε GroupCohomology.resolution.ε

/-- The homotopy equivalence of complexes of `k`-modules between the standard resolution of `k` as
a trivial `G`-representation, and the complex which is `k` at 0 and 0 everywhere else, acts as
`∑ nᵢgᵢ ↦ ∑ nᵢ : k[G¹] → k` at 0. -/
theorem forget₂ToModuleHomotopyEquiv_f_0_eq :
    (forget₂ToModuleHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  show (HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _).f 0 = _
  simp only [HomologicalComplex.comp_f]
  convert category.id_comp _
  · dsimp only [HomotopyEquiv.ofIso, comp_forget_augmented_iso, map_alternating_face_map_complex]
    simp only [iso.symm_hom, eq_to_iso.inv, HomologicalComplex.eqToHom_f, eq_to_hom_refl]
  trans (Finsupp.total _ _ _ fun f => (1 : k)).comp ((ModuleCat.free k).map (terminal.from _))
  · dsimp
    rw [@Finsupp.lmapDomain_total (Fin 1 → G) k k _ _ _ (⊤_ Type u) k _ _ (fun i => (1 : k))
        (fun i => (1 : k))
        (terminal.from
          ((classifyingSpaceUniversalCover G).obj (Opposite.op (SimplexCategory.mk 0))).V)
        LinearMap.id fun i => rfl,
      LinearMap.id_comp]
    rfl
  · congr
    · ext
      dsimp [HomotopyEquiv.ofIso]
      rw [Finsupp.total_single, one_smul, @Unique.eq_default _ types.terminal_iso.to_equiv.unique a,
        Finsupp.single_eq_same]
    · exact @Subsingleton.elim _ (@Unique.subsingleton _ (limits.unique_to_terminal _)) _ _
#align group_cohomology.resolution.forget₂_to_Module_homotopy_equiv_f_0_eq GroupCohomology.resolution.forget₂ToModuleHomotopyEquiv_f_0_eq

theorem d_comp_ε : (GroupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 := by
  ext1
  refine' LinearMap.ext fun x => _
  have : (forget₂_to_Module k G).d 1 0 ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂_to_Module_homotopy_equiv_f_0_eq, ←
        (forget₂_to_Module_homotopy_equiv k G).1.2 1 0 rfl] <;>
      exact comp_zero
  exact LinearMap.ext_iff.1 this _
#align group_cohomology.resolution.d_comp_ε GroupCohomology.resolution.d_comp_ε

/-- The chain map from the standard resolution of `k` to `k[0]` given by `∑ nᵢgᵢ ↦ ∑ nᵢ` in
degree zero. -/
def εToSingle₀ :
    GroupCohomology.resolution k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((GroupCohomology.resolution k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩
#align group_cohomology.resolution.ε_to_single₀ GroupCohomology.resolution.εToSingle₀

theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (ChainComplex.single₀MapHomologicalComplex _).hom.app _ =
      (forget₂ToModuleHomotopyEquiv k G).hom := by
  refine' ChainComplex.to_single₀_ext _ _ _
  dsimp
  rw [category.comp_id]
  exact (forget₂_to_Module_homotopy_equiv_f_0_eq k G).symm
#align group_cohomology.resolution.ε_to_single₀_comp_eq GroupCohomology.resolution.εToSingle₀_comp_eq

theorem quasiIsoOfForget₂εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) := by
  have h : QuasiIso (forget₂_to_Module_homotopy_equiv k G).hom := HomotopyEquiv.toQuasiIso _
  rw [← ε_to_single₀_comp_eq k G] at h
  haveI := h
  exact quasiIso_of_comp_right _ ((ChainComplex.single₀MapHomologicalComplex _).hom.app _)
#align group_cohomology.resolution.quasi_iso_of_forget₂_ε_to_single₀ GroupCohomology.resolution.quasiIsoOfForget₂εToSingle₀

instance : QuasiIso (εToSingle₀ k G) :=
  (forget₂ _ (ModuleCat.{u} k)).quasiIso_of_map_quasiIso _ (quasiIsoOfForget₂εToSingle₀ k G)

end Exactness

end GroupCohomology.resolution

open GroupCohomology.resolution

variable [Group G]

/-- The standard projective resolution of `k` as a trivial `k`-linear `G`-representation. -/
def GroupCohomology.projectiveResolution : ProjectiveResolution (Rep.trivial k G k) :=
  (εToSingle₀ k G).toSingle₀ProjectiveResolution (x_projective k G)
#align group_cohomology.ProjectiveResolution GroupCohomology.projectiveResolution

instance : EnoughProjectives (Rep k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2
    ModuleCat.moduleCat_enoughProjectives.{u}

/-- Given a `k`-linear `G`-representation `V`, `Extⁿ(k, V)` (where `k` is a trivial `k`-linear
`G`-representation) is isomorphic to the `n`th cohomology group of `Hom(P, V)`, where `P` is the
standard resolution of `k` called `group_cohomology.resolution k G`. -/
def GroupCohomology.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      (((((linearYoneda k (Rep k G)).obj V).rightOp.mapHomologicalComplex _).obj
              (GroupCohomology.resolution k G)).homology
          n).unop := by
  let this.1 :=
      (((linear_yoneda k (Rep k G)).obj V).rightOp.leftDerivedObjIso n
            (GroupCohomology.projectiveResolution k G)).unop.symm <;>
    exact this
#align group_cohomology.Ext_iso GroupCohomology.extIso
