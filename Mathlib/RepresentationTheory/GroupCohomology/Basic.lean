/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.GroupCohomology.Resolution

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))$$
$$+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
$$+ (-1)^{n + 1}\cdot f(g_0, \dots, g_{n - 1})$$ (where `ρ` is the representation attached to `A`).

We have a `k`-linear isomorphism $\mathrm{Fun}(G^n, A) \cong \mathrm{Hom}(k[G^{n + 1}], A)$, where
the righthand side is morphisms in `Rep k G`, and the representation on $k[G^{n + 1}]$
is induced by the diagonal action of `G`. If we conjugate the $n$th differential in
$\mathrm{Hom}(P, A)$ by this isomorphism, where `P` is the standard resolution of `k` as a trivial
`k`-linear `G`-representation, then the resulting map agrees with the differential $d^n$ defined
above, a fact we prove.

This gives us for free a proof that our $d^n$ squares to zero. It also gives us an isomorphism
$\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A),$ where $\mathrm{Ext}$ is taken in the category
`Rep k G`.

To talk about cohomology in low degree, please see the file
`Mathlib/RepresentationTheory/GroupCohomology/LowDegree.lean`, which gives simpler expressions for
`H⁰`, `H¹`, `H²` than the definition `groupCohomology` in this file.

## Main definitions

* `groupCohomology.linearYonedaObjResolution A`: a complex whose objects are the representation
  morphisms $\mathrm{Hom}(k[G^{n + 1}], A)$ and whose cohomology is the group cohomology
  $\mathrm{H}^n(G, A)$.
* `groupCohomology.inhomogeneousCochains A`: a complex whose objects are
  $\mathrm{Fun}(G^n, A)$ and whose cohomology is the group cohomology $\mathrm{H}^n(G, A).$
* `groupCohomology.inhomogeneousCochainsIso A`: an isomorphism between the above two complexes.
* `groupCohomology A n`: this is $\mathrm{H}^n(G, A),$ defined as the $n$th cohomology of the
  second complex, `inhomogeneousCochains A`.
* `groupCohomologyIsoExt A n`: an isomorphism $\mathrm{H}^n(G, A) \cong \mathrm{Ext}^n(k, A)$
  (where $\mathrm{Ext}$ is taken in the category `Rep k G`) induced by `inhomogeneousCochainsIso A`.

## Implementation notes

Group cohomology is typically stated for `G`-modules, or equivalently modules over the group ring
`ℤ[G].` However, `ℤ` can be generalized to any commutative ring `k`, which is what we use.
Moreover, we express `k[G]`-module structures on a module `k`-module `A` using the `Rep`
definition. We avoid using instances `Module (MonoidAlgebra k G) A` so that we do not run into
possible scalar action diamonds.

## TODO

* API for cohomology in low degree: $\mathrm{H}^0, \mathrm{H}^1$ and $\mathrm{H}^2.$ For example,
  the inflation-restriction exact sequence.
* The long exact sequence in cohomology attached to a short exact sequence of representations.
* Upgrading `groupCohomologyIsoExt` to an isomorphism of derived functors.
* Profinite cohomology.

Longer term:
* The Hochschild-Serre spectral sequence (this is perhaps a good toy example for the theory of
  spectral sequences in general).
-/


noncomputable section

universe u

variable {k G : Type u} [CommRing k] {n : ℕ}

open CategoryTheory

namespace groupCohomology

variable [Monoid G]

/-- The complex `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `k`-linear
`G`-representation. -/
abbrev linearYonedaObjResolution (A : Rep k G) : CochainComplex (ModuleCat.{u} k) ℕ :=
  (Rep.standardComplex k G).linearYonedaObj k A

theorem linearYonedaObjResolution_d_apply
    {A : Rep k G} (i j : ℕ) (x : (Rep.standardComplex k G).X i ⟶ A) :
    (linearYonedaObjResolution A).d i j x = (Rep.standardComplex k G).d j i ≫ x :=
  rfl

end groupCohomology

namespace inhomogeneousCochains

open Rep groupCohomology

/-- The differential in the complex of inhomogeneous cochains used to
calculate group cohomology. -/
@[simps]
def d [Monoid G] (n : ℕ) (A : Rep k G) : ((Fin n → G) → A) →ₗ[k] (Fin (n + 1) → G) → A where
  toFun f g :=
    A.ρ (g 0) (f fun i => g i.succ) +
      Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
  map_add' f g := by
    ext x
/- Porting note: changed from `simp only` which needed extra heartbeats -/
    simp_rw [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib, add_add_add_comm]
  map_smul' r f := by
    ext x
/- Porting note: changed from `simp only` which needed extra heartbeats -/
    simp_rw [Pi.smul_apply, RingHom.id_apply, map_smul, smul_add, Finset.smul_sum, ← smul_assoc,
      smul_eq_mul, mul_comm r]

variable [Group G] (n) (A : Rep k G)

/-- The theorem that our isomorphism `Fun(Gⁿ, A) ≅ Hom(k[Gⁿ⁺¹], A)` (where the righthand side is
morphisms in `Rep k G`) commutes with the differentials in the complex of inhomogeneous cochains
and the homogeneous `linearYonedaObjResolution`. -/
theorem d_eq :
    d n A =
      ((diagonalHomEquiv n A).toModuleIso.inv ≫
        (linearYonedaObjResolution A).d n (n + 1) ≫
          (diagonalHomEquiv (n + 1) A).toModuleIso.hom).hom := by
  ext f g
/- Porting note (https://github.com/leanprover-community/mathlib4/issues/11039): broken proof was
  simp only [ModuleCat.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.toModuleIso_inv, linearYonedaObjResolution_d_apply, LinearEquiv.toModuleIso_hom,
    diagonalHomEquiv_apply, Action.comp_hom, Resolution.d_eq k G n,
    Resolution.d_of (Fin.partialProd g), LinearMap.map_sum,
    ← Finsupp.smul_single_one _ ((-1 : k) ^ _), map_smul, d_apply]
  simp only [@Fin.sum_univ_succ _ _ (n + 1), Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
    diagonalHomEquiv_symm_apply f (Fin.partialProd g ∘ @Fin.succ (n + 1)), Function.comp_apply,
    Fin.partialProd_succ, Fin.castSucc_zero, Fin.partialProd_zero, one_mul]
  congr 1
  · congr
    ext
    have := Fin.partialProd_right_inv g (Fin.castSucc x)
    simp only [mul_inv_rev, Fin.castSucc_fin_succ] at *
    rw [mul_assoc, ← mul_assoc _ _ (g x.succ), this, inv_mul_cancel_left]
  · exact Finset.sum_congr rfl fun j hj => by
      rw [diagonalHomEquiv_symm_partialProd_succ, Fin.val_succ] -/
  -- https://github.com/leanprover-community/mathlib4/issues/5026
  -- https://github.com/leanprover-community/mathlib4/issues/5164
  change d n A f g = diagonalHomEquiv (n + 1) A
    ((standardComplex k G).d (n + 1) n ≫ (diagonalHomEquiv n A).symm f) g
  rw [diagonalHomEquiv_apply, Action.comp_hom, ConcreteCategory.comp_apply, standardComplex.d_eq]
  erw [standardComplex.d_of (Fin.partialProd g)]
  simp only [map_sum, ← Finsupp.smul_single_one _ ((-1 : k) ^ _)]
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [d_apply, @Fin.sum_univ_succ _ _ (n + 1), Fin.val_zero, pow_zero, one_smul,
    Fin.succAbove_zero, diagonalHomEquiv_symm_apply f (Fin.partialProd g ∘ @Fin.succ (n + 1))]
  simp_rw [Function.comp_apply, Fin.partialProd_succ, Fin.castSucc_zero,
    Fin.partialProd_zero, one_mul]
  rcongr x
  · have := Fin.partialProd_right_inv g (Fin.castSucc x)
    simp only [mul_inv_rev, Fin.castSucc_fin_succ] at this ⊢
    rw [mul_assoc, ← mul_assoc _ _ (g x.succ), this, inv_mul_cancel_left]
  · -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [map_smul, diagonalHomEquiv_symm_partialProd_succ, Fin.val_succ]

end inhomogeneousCochains

namespace groupCohomology

variable [Group G] (n) (A : Rep k G)

open inhomogeneousCochains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n → G) → A))
    (fun n => ModuleCat.ofHom (inhomogeneousCochains.d n A)) fun n => by
/- Porting note (https://github.com/leanprover-community/mathlib4/issues/11039): broken proof was
    ext x y
    have := LinearMap.ext_iff.1 ((linearYonedaObjResolution A).d_comp_d n (n + 1) (n + 2))
    simp only [ModuleCat.coe_comp, Function.comp_apply] at this
    simp only [ModuleCat.coe_comp, Function.comp_apply, d_eq, LinearEquiv.toModuleIso_hom,
      LinearEquiv.toModuleIso_inv, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, this,
      LinearMap.zero_apply, map_zero, Pi.zero_apply] -/
    ext x
    have : ∀ x, _ = (0 : _ →ₗ[_] _) x := LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.mp
      ((linearYonedaObjResolution A).d_comp_d n (n + 1) (n + 2)))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    dsimp only
    simp only [d_eq, LinearEquiv.toModuleIso_inv, LinearEquiv.toModuleIso_hom,
      ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.coe_coe, ModuleCat.hom_zero,
      ModuleCat.ofHom_comp]
    /- Porting note: I can see I need to rewrite `LinearEquiv.coe_coe` twice to at
      least reduce the need for `symm_apply_apply` to be an `erw`. However, even `erw` refuses to
      rewrite the second `coe_coe`... -/
    erw [LinearEquiv.symm_apply_apply, this]
    simp only [LinearMap.zero_apply, ChainComplex.linearYonedaObj_X, linearYoneda_obj_obj_carrier,
      map_zero, Pi.zero_apply, LinearMap.zero_apply]
    rfl

theorem inhomogeneousCochains.d_def (n : ℕ) :
    (inhomogeneousCochains A).d n (n + 1) = ModuleCat.ofHom (inhomogeneousCochains.d n A) :=
  CochainComplex.of_d _ _ _ _

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `G`-representation. -/
def inhomogeneousCochainsIso : inhomogeneousCochains A ≅ linearYonedaObjResolution A := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i =>
    (Rep.diagonalHomEquiv i A).toModuleIso.symm) ?_
  rintro i j (h : i + 1 = j)
  subst h
  ext
  simp only [ChainComplex.linearYonedaObj_X, linearYoneda_obj_obj_carrier, CochainComplex.of_x,
    linearYoneda_obj_obj_isAddCommGroup, linearYoneda_obj_obj_isModule, Iso.symm_hom,
    LinearEquiv.toModuleIso_inv, ChainComplex.linearYonedaObj_d, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, Linear.leftComp_apply,
    inhomogeneousCochains.d_def, d_eq, LinearEquiv.toModuleIso_hom, ModuleCat.ofHom_comp,
    Category.assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
    LinearMap.id_comp, LinearEquiv.coe_coe]
  rfl

/-- The `n`-cocycles `Zⁿ(G, A)` of a `k`-linear `G`-representation `A`, i.e. the kernel of the
`n`th differential in the complex of inhomogeneous cochains. -/
abbrev cocycles (n : ℕ) : ModuleCat k := (inhomogeneousCochains A).cycles n

/-- The natural inclusion of the `n`-cocycles `Zⁿ(G, A)` into the `n`-cochains `Cⁿ(G, A).` -/
abbrev iCocycles (n : ℕ) : cocycles A n ⟶ ModuleCat.of k ((Fin n → G) → A) :=
  (inhomogeneousCochains A).iCycles n

/-- This is the map from `i`-cochains to `j`-cocycles induced by the differential in the complex of
inhomogeneous cochains. -/
abbrev toCocycles (i j : ℕ) : ModuleCat.of k ((Fin i → G) → A) ⟶ cocycles A j :=
  (inhomogeneousCochains A).toCycles i j

end groupCohomology

open groupCohomology

/-- The group cohomology of a `k`-linear `G`-representation `A`, as the cohomology of its complex
of inhomogeneous cochains. -/
def groupCohomology [Group G] (A : Rep k G) (n : ℕ) : ModuleCat k :=
  (inhomogeneousCochains A).homology n

/-- The natural map from `n`-cocycles to `n`th group cohomology for a `k`-linear
`G`-representation `A`. -/
abbrev groupCohomologyπ [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def groupCohomologyIsoExt [Group G] [DecidableEq G] (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (Rep.standardResolution.extIso k G A n).symm
