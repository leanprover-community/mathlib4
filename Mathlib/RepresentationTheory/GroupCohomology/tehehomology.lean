/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Homology.Opposite
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.RepresentationTheory.GroupCohomology.Resolution
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.CategoryTheory.Abelian.LeftDerived

#align_import representation_theory.group_cohomology.basic from "leanprover-community/mathlib"@"cc5dd6244981976cc9da7afc4eee5682b037a013"

/-!
# The group cohomology of a `k`-linear `G`-representation

Let `k` be a commutative ring and `G` a group. This file defines the group cohomology of
`A : Rep k G` to be the cohomology of the complex
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
with differential $d^n$ sending $f: G^n \to A$ to the function mapping $(g_0, \dots, g_n)$ to
$$\rho(g_0)(f(g_1, \dots, g_n))
+ \sum_{i = 0}^{n - 1} (-1)^{i + 1}\cdot f(g_0, \dots, g_ig_{i + 1}, \dots, g_n)$$
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
`RepresentationTheory.GroupCohomology.LowDegree`, which gives simpler expressions for `H⁰, H¹, H²`
than the definition `groupCohomology` in this file.

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
open CategoryTheory CategoryTheory.Limits

namespace Representation

variable {k G : Type*} [CommRing k] [Group G] {A B C D : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
  (ρ : Representation k G A) (τ : Representation k G B)
  (η : Representation k G C) (ν : Representation k G D) {n : ℕ}

@[simp]
theorem inv_self_apply (g : G) (x : A) :
    ρ g⁻¹ (ρ g x) = x :=
  show (ρ g⁻¹ * ρ g) x = x by rw [← map_mul, inv_mul_self, map_one, LinearMap.one_apply]

@[simp]
theorem self_inv_apply (g : G) (x : A) :
    ρ g (ρ g⁻¹ x) = x :=
  show (ρ g * ρ g⁻¹) x = x by rw [← map_mul, mul_inv_self, map_one, LinearMap.one_apply]

def inv : Representation k Gᵐᵒᵖ A :=
ρ.comp (MulEquiv.inv' G).symm.toMonoidHom

@[simp] lemma inv_apply (g : Gᵐᵒᵖ) (x : A) :
  ρ.inv g x = ρ g.unop⁻¹ x := rfl

abbrev coinvariantsKer := Submodule.span k (Set.range <| fun (x : G × A) => ρ x.1 x.2 - x.2)

lemma mem_coinvariantsKer (g : G) (x a : A) (h : ρ g x - x = a) : a ∈ coinvariantsKer ρ :=
Submodule.subset_span ⟨(g, x), h⟩

abbrev coinvariants := A ⧸ coinvariantsKer ρ

def coinvariantsLift (f : A →ₗ[k] B) (h : ∀ (x : G) (a : A), f (ρ x a) = f a) :
    ρ.coinvariants →ₗ[k] B :=
  Submodule.liftQ _ f <| Submodule.span_le.2 fun x ⟨⟨g, y⟩, hy⟩ => by
    simp only [← hy, SetLike.mem_coe, LinearMap.mem_ker, map_sub, h, sub_self]

@[simp] theorem coinvariantsLift_mkQ (f : A →ₗ[k] B) {h : ∀ (x : G) (a : A), f (ρ x a) = f a} :
  coinvariantsLift ρ f h ∘ₗ (coinvariantsKer ρ).mkQ = f := rfl

def coinvariantsLift' (f : ρ.hom (Representation.trivial k (G := G) (V := B))) :
    ρ.coinvariants →ₗ[k] B :=
  coinvariantsLift _ f.hom <| hom.comm_apply _ _ _

variable {ρ τ}

def coinvariantsMap (f : ρ.hom τ) :
    ρ.coinvariants →ₗ[k] τ.coinvariants :=
  coinvariantsLift _ (Submodule.mkQ _ ∘ₗ f.hom) fun x a => (Submodule.Quotient.eq _).2 <|
    Submodule.subset_span <| by rw [hom.comm_apply]; exact Set.mem_range_self (x, f.hom a)

@[simp] theorem coinvariantsMap_mkQ (f : ρ.hom τ) :
  coinvariantsMap f ∘ₗ (coinvariantsKer ρ).mkQ = (coinvariantsKer τ).mkQ ∘ₗ f.hom := rfl

variable (B ρ)

@[simp] def coinvariantsHomEquiv :
    (ρ.coinvariants →ₗ[k] B) ≃ ρ.hom (Representation.trivial k (G := G) (V := B)) where
      toFun := fun f => {
        hom := f ∘ₗ ρ.coinvariantsKer.mkQ
        comm := fun g => by
          ext x
          simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, apply_eq_self,
            (Submodule.Quotient.eq ρ.coinvariantsKer).2 (mem_coinvariantsKer _ g x _ rfl)] }
      invFun := fun f => coinvariantsLift' _ f
      left_inv := fun x => Submodule.linearMap_qext _ rfl
      right_inv := fun x => hom.ext _ _ rfl

variable {B ρ η ν}

@[simps] def tprodMap (f : ρ.hom τ) (g : η.hom ν) :
    (ρ.tprod η).hom (τ.tprod ν) where
      hom := TensorProduct.map f.hom g.hom
      comm := fun x => TensorProduct.ext' fun x y => by
        simp only [tprod_apply, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
          hom.comm_apply]

variable (ρ τ)

abbrev tensor2Obj := coinvariants (ρ.tprod τ)

variable {ρ τ}

def tensor2Map (f : ρ.hom τ) (g : η.hom ν) :
    coinvariantsMap (tprodMap (hom.id (ρ := τ)) g) ∘ₗ coinvariantsMap (tprodMap f (hom.id (ρ := η)))
      = coinvariantsMap (tprodMap f (hom.id (ρ := ν)))
        ∘ₗ coinvariantsMap (tprodMap (hom.id (ρ := ρ)) g) :=
  Submodule.linearMap_qext _ <| by
    simp_rw [LinearMap.comp_assoc, coinvariantsMap_mkQ, tprodMap_hom, hom.id_hom,
      ← LinearMap.comp_assoc, coinvariantsMap_mkQ, tprodMap_hom, hom.id_hom,
      LinearMap.comp_assoc, ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]

variable (ρ)

def tensor2Hom : tensor2Obj ρ (ofMulAction k G G) →ₗ[k] A :=
  coinvariantsLift _ (TensorProduct.lift (Finsupp.total _ _ _ (fun g => ρ g⁻¹))
    ∘ₗ (TensorProduct.comm _ _ _).toLinearMap) fun g a => by
    show ((TensorProduct.lift _ ∘ₗ _) ∘ₗ tprod _ _ g) a = _
    refine' LinearMap.ext_iff.1 (TensorProduct.ext _) a
    ext x h
    simp only [tprod_apply, LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe, TensorProduct.map_tmul,
      ofMulAction_single, smul_eq_mul, TensorProduct.comm_tmul, TensorProduct.lift.tmul,
      Finsupp.total_single, mul_inv_rev, map_mul, one_smul, LinearMap.mul_apply, inv_self_apply]

@[simp] lemma tensor2Hom_apply (x : A) (g : G) (r : k) :
    tensor2Hom ρ (Submodule.Quotient.mk (p := coinvariantsKer _) (x ⊗ₜ Finsupp.single g r))
      = r • ρ g⁻¹ x := by
  simp only [tensor2Hom, coinvariantsLift, Submodule.mkQ_apply, Submodule.liftQ_apply,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.comm_tmul,
    TensorProduct.lift.tmul, Finsupp.total_single, LinearMap.smul_apply]

def tensor2Inv : A →ₗ[k] tensor2Obj ρ (ofMulAction k G G) :=
  Submodule.mkQ _ ∘ₗ (TensorProduct.mk k A (G →₀ k)).flip (Finsupp.single 1 1)

def tensor2Iso : (tensor2Obj ρ (ofMulAction k G G)) ≃ₗ[k] A where
  toFun := tensor2Hom ρ
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := tensor2Inv ρ
  left_inv := LinearMap.congr_fun (f := (tensor2Inv ρ) ∘ₗ tensor2Hom ρ) (g := LinearMap.id) <|
    Submodule.linearMap_qext _ <| TensorProduct.ext <| by
      ext a g
      simp only [tensor2Inv, LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
        LinearMap.compr₂_apply, TensorProduct.mk_apply, Submodule.mkQ_apply, tensor2Hom_apply,
        one_smul, LinearMap.flip_apply, LinearMap.id_comp]
      rw [Submodule.Quotient.eq]
      exact mem_coinvariantsKer _ g⁻¹ (a ⊗ₜ Finsupp.single g 1) _ (by
        simp only [tprod_apply, TensorProduct.map_tmul, ofMulAction_single, smul_eq_mul,
          mul_left_inv])
  right_inv := fun x => by
    simp only [tensor2Inv, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
      TensorProduct.mk_apply, Submodule.mkQ_apply, tensor2Hom_apply, inv_one, map_one,
      LinearMap.one_apply, one_smul]
#check finsuppTensorFinsupp
def ugh (α : Type*) : ((ρ.finsupp α).tprod τ).iso ((ρ.tprod τ).finsupp α) :=
iso.mk' _ _ (LinearEquiv.symm _) _
variable {α : Type*}

#check @tensor2Obj k G _ _ A (α →₀ G →₀ k) _ _ Finsupp.addCommGroup (Finsupp.module α (G →₀ k)) ρ (free k G α)


-- what the hell
def ermmmmmmm (α : Type*) : @tensor2Obj _ _ _ _ _ _ _ _ Finsupp.addCommGroup _ ρ (free k G α)
    ≃ₗ[k] α →₀ A := sorry

end Representation
namespace groupHomology

variable {k G : Type u} [CommRing k] [Group G]
open MonoidalCategory

abbrev coinvariantsObj (A : Rep k G) := A.ρ.coinvariants

abbrev coinvariantsMap {A B : Rep k G} (f : A ⟶ B) :
    coinvariantsObj A →ₗ[k] coinvariantsObj B :=
  Representation.coinvariantsMap ⟨f.hom, f.comm⟩

variable (k G)

@[simps] def coinvariants : Rep k G ⥤ ModuleCat k where
  obj := fun A => ModuleCat.of k (coinvariantsObj A)
  map := fun f => ModuleCat.ofHom (coinvariantsMap f)
  map_id := fun X => by
    ext x
    refine Quotient.inductionOn' x (fun y => rfl)
  map_comp := fun f g => by
    ext x
    refine Quotient.inductionOn' x (fun y => rfl)

instance : (coinvariants k G).Additive where
  map_add := fun {_ _ _ _} => LinearMap.ext fun x => Quotient.inductionOn' x (fun _ => rfl)

def coinvariantsAdjunction : coinvariants k G ⊣ Rep.trivialFunctor k G :=
Adjunction.mkOfHomEquiv <| {
  homEquiv := fun A B => (A.ρ.coinvariantsHomEquiv B).trans
    (Rep.homLEquiv A (Rep.trivial k G B)).toEquiv.symm
  homEquiv_naturality_left_symm := fun f g => Submodule.linearMap_qext _ rfl }

instance : IsLeftAdjoint (coinvariants k G) where
  right := Rep.trivialFunctor k G
  adj := coinvariantsAdjunction k G
#check ModuleCat.free
instance : Limits.PreservesColimitsOfSize.{u, u} (coinvariants k G) :=
  (coinvariantsAdjunction k G).leftAdjointPreservesColimits

def ermmm (A : Rep k G) : (coinvariants k G).obj (A ⊗ Rep.leftRegular k G) ≅ A.V :=
  A.ρ.tensor2Iso.toModuleIso

open MonoidalCategory
set_option profiler true

def ok : Rep k G ⥤ Rep k G ⥤ ModuleCat k :=
{ obj := fun A => MonoidalCategory.tensorLeft A ⋙ coinvariants k G
  map := fun f => {
    app := fun A => coinvariantsMap (f ⊗ 𝟙 A)
    naturality := fun A B g => (Representation.tensor2Map ⟨f.hom, f.comm⟩ ⟨g.hom, g.comm⟩).symm }
  map_id := fun A => NatTrans.ext _ _ <| by
    ext B : 1
    dsimp only
    rw [MonoidalCategory.tensor_id]
    exact (coinvariants k G).map_id _
  map_comp := fun f g => NatTrans.ext _ _ <| by
    ext B : 1
    dsimp only
    rw [MonoidalCategory.comp_tensor_id]
    exact (coinvariants k G).map_comp _ _ }

instance (A : Rep k G) : ((ok k G).obj A).Additive := by
  unfold ok
  infer_instance

def Tor (n : ℕ) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj X := Functor.leftDerived ((ok k G).obj X) n
  map f := NatTrans.leftDerived ((ok k G).map f) n

end groupHomology
#exit

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
#align inhomogeneous_cochains.d inhomogeneousCochains.d

set_option profiler true
variable [Group G] (n) (A : Rep k G)

@[nolint checkType] theorem d_eq :
    d n A =
      (freeLiftEquiv (Fin n → G) A).toModuleIso.inv ≫
        (linearYonedaObjBarResolution A).d n (n + 1) ≫
          (freeLiftEquiv (Fin (n + 1) → G) A).toModuleIso.hom := by
  ext f g
  simp only [ChainComplex.of_x, ChainComplex.linearYonedaObj_d, barResolution.d_def,
    Function.comp_apply, freeLiftEquiv_apply]
  show _ = ((freeLiftEquiv _ _).symm f).hom _
  rw [d_single, map_add, map_sum, freeLiftEquiv_symm_apply, one_smul]
  conv =>
    · enter [2, 2, 2, x]
      rw [freeLiftEquiv_symm_apply, map_one]

end inhomogeneousCochains

namespace groupCohomology

variable [Group G] (n) (A : Rep k G)

open inhomogeneousCochains

/-- Given a `k`-linear `G`-representation `A`, this is the complex of inhomogeneous cochains
$$0 \to \mathrm{Fun}(G^0, A) \to \mathrm{Fun}(G^1, A) \to \mathrm{Fun}(G^2, A) \to \dots$$
which calculates the group cohomology of `A`. -/
noncomputable abbrev inhomogeneousCochains : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k ((Fin n → G) → A))
    (fun n => inhomogeneousCochains.d n A) fun n => by
    simp only [d_eq, d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, (linearYonedaObjBarResolution A).d_comp_d] }

@[simp]
theorem inhomogeneousCochains.d_def (n : ℕ) :
    (inhomogeneousCochains A).d n (n + 1) = inhomogeneousCochains.d n A :=
  CochainComplex.of_d _ _ _ _

set_option profiler true

def ForFuckSake : inhomogeneousCochains A ≅ linearYonedaObjBarResolution A := by
  refine' HomologicalComplex.Hom.isoOfComponents _ _
  · intro i
    apply (Rep.freeLiftEquiv (Fin i → G) A).toModuleIso.symm
  rintro i j (h : i + 1 = j)
  subst h
  simp only [Iso.symm_hom, inhomogeneousCochains.d_def, d_eq, Category.assoc]
  slice_rhs 2 4 => { rw [Iso.hom_inv_id, Category.comp_id] }

/-- Given a `k`-linear `G`-representation `A`, the complex of inhomogeneous cochains is isomorphic
to `Hom(P, A)`, where `P` is the standard resolution of `k` as a trivial `G`-representation. -/
def inhomogeneousCochainsIso : inhomogeneousCochains A ≅ linearYonedaObjResolution A :=
  ForFuckSake A ≪≫ ((ChainComplex.linearYoneda (R := k) A).mapIso (Rep.barResolutionIso k G).symm).unop

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
#align group_cohomology groupCohomology

/-- The natural map from `n`-cocycles to `n`th group cohomology for a `k`-linear
`G`-representation `A`. -/
abbrev groupCohomologyπ [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology A n :=
  (inhomogeneousCochains A).homologyπ n

/-- The `n`th group cohomology of a `k`-linear `G`-representation `A` is isomorphic to
`Extⁿ(k, A)` (taken in `Rep k G`), where `k` is a trivial `k`-linear `G`-representation. -/
def groupCohomologyIsoExt [Group G] (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj A :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousCochainsIso A)).hom n ≪≫
    (extIso k G A n).symm
set_option linter.uppercaseLean3 false in
#align group_cohomology_iso_Ext groupCohomologyIsoExt
