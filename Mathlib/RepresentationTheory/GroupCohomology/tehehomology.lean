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

noncomputable section

universe u
section
variable (R A B α : Type*) [CommRing R] [AddCommGroup A] [AddCommGroup B]
  [Module R A] [Module R B]
open TensorProduct

def finsuppTensorLeft :
    (α →₀ A) ⊗[R] B ≃ₗ[R] α →₀ A ⊗[R] B :=
  TensorProduct.congr (LinearEquiv.refl _ _)
    (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm ≪≫ₗ
  finsuppTensorFinsupp R A B α Unit ≪≫ₗ
  Finsupp.domLCongr (Equiv.prodUnique α Unit)

def finsuppTensorRight :
    A ⊗[R] (α →₀ B) ≃ₗ[R] α →₀ A ⊗[R] B :=
  TensorProduct.congr (Finsupp.LinearEquiv.finsuppUnique _ _ _).symm
    (LinearEquiv.refl _ _) ≪≫ₗ
  finsuppTensorFinsupp R A B Unit α ≪≫ₗ
  Finsupp.domLCongr (Equiv.uniqueProd α Unit)

variable {R A B α}
open Finsupp
@[simp] lemma finsuppTensorLeft_tmul_single
    (a : α) (x : A) (y : B) :
    finsuppTensorLeft R A B α (Finsupp.single a x ⊗ₜ y) =
      Finsupp.single a (x ⊗ₜ y) := by
    simp only [finsuppTensorLeft, LinearEquiv.trans_apply, congr_tmul, LinearEquiv.refl_apply,
      LinearEquiv.finsuppUnique_symm_apply, PUnit.default_eq_unit, finsuppTensorFinsupp_single,
      domLCongr_apply, domCongr_apply, equivMapDomain_single, Equiv.coe_prodUnique]

@[simp] lemma finsuppTensorLeft_symm_single_tmul
    (a : α) (x : A) (y : B) :
    (finsuppTensorLeft R A B α).symm (Finsupp.single a (x ⊗ₜ y)) =
      Finsupp.single a x ⊗ₜ y := by
  simp only [finsuppTensorLeft, LinearEquiv.trans_symm, domLCongr_symm, LinearEquiv.trans_apply,
    domLCongr_apply, domCongr_apply, equivMapDomain_single, Equiv.prodUnique_symm_apply,
    PUnit.default_eq_unit, finsuppTensorFinsupp_symm_single, congr_symm_tmul, LinearEquiv.refl_symm,
    LinearEquiv.refl_apply, LinearEquiv.symm_symm, LinearEquiv.finsuppUnique_apply, single_eq_same]

@[simp] lemma finsuppTensorRight_tmul_single
    (a : α) (x : A) (y : B) :
    finsuppTensorRight R A B α (x ⊗ₜ Finsupp.single a y) =
      Finsupp.single a (x ⊗ₜ y) := by
    simp only [finsuppTensorRight, LinearEquiv.trans_apply, congr_tmul,
      LinearEquiv.finsuppUnique_symm_apply, PUnit.default_eq_unit, LinearEquiv.refl_apply,
      finsuppTensorFinsupp_single, domLCongr_apply, domCongr_apply, equivMapDomain_single,
      Equiv.coe_uniqueProd]

@[simp] lemma finsuppTensorRight_symm_single_tmul
    (a : α) (x : A) (y : B) :
    (finsuppTensorRight R A B α).symm (Finsupp.single a (x ⊗ₜ y)) =
      x ⊗ₜ Finsupp.single a y := by
  simp only [finsuppTensorRight, LinearEquiv.trans_symm, domLCongr_symm, LinearEquiv.trans_apply,
    domLCongr_apply, domCongr_apply, equivMapDomain_single, Equiv.uniqueProd_symm_apply,
    PUnit.default_eq_unit, finsuppTensorFinsupp_symm_single, congr_symm_tmul, LinearEquiv.symm_symm,
    LinearEquiv.finsuppUnique_apply, single_eq_same, LinearEquiv.refl_symm, LinearEquiv.refl_apply]
end

open CategoryTheory CategoryTheory.Limits

namespace Representation

variable {k G : Type*} [CommRing k] [Group G] {A B C D : Type*}
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
  (ρ : Representation k G A) (τ : Representation k G B)
  (η : Representation k G C) (ν : Representation k G D) {n : ℕ}
  (α : Type*)

def finsuppTprodLeft :
    ((ρ.finsupp α).tprod τ).iso ((ρ.tprod τ).finsupp α) :=
  iso.mk' _ _ (finsuppTensorLeft k A B α) fun g => by
    ext a x y : 4
    simp only [tprod_apply, finsupp_apply, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.lsingle_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      TensorProduct.curry_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      TensorProduct.map_tmul, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index,
      finsuppTensorLeft_tmul_single]

def finsuppTprodRight :
    (ρ.tprod (τ.finsupp α)).iso ((ρ.tprod τ).finsupp α) :=
  iso.mk' _ _ (finsuppTensorRight k A B α) fun g => by
    ext a x y : 4
    simp only [tprod_apply, finsupp_apply, TensorProduct.AlgebraTensorModule.curry_apply,
      LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, TensorProduct.curry_apply,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, TensorProduct.map_tmul, Finsupp.coe_lsum,
      map_zero, Finsupp.sum_single_index, finsuppTensorRight_tmul_single]

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

def coinvariantsLift (f : A →ₗ[k] B) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
    ρ.coinvariants →ₗ[k] B :=
  Submodule.liftQ _ f <| Submodule.span_le.2 fun x ⟨⟨g, y⟩, hy⟩ => by
    simpa only [← hy, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, LinearMap.coe_comp,
      Function.comp_apply] using LinearMap.ext_iff.1 (h g) y

@[simp] theorem coinvariantsLift_mkQ (f : A →ₗ[k] B) {h : ∀ (x : G), f ∘ₗ ρ x = f} :
  coinvariantsLift ρ f h ∘ₗ (coinvariantsKer ρ).mkQ = f := rfl

def coinvariantsLift' (f : ρ.hom (Representation.trivial k (G := G) (V := B))) :
    ρ.coinvariants →ₗ[k] B :=
  coinvariantsLift _ f.hom f.comm

variable {ρ τ}

def coinvariantsMap (f : ρ.hom τ) :
    ρ.coinvariants →ₗ[k] τ.coinvariants :=
  coinvariantsLift _ (Submodule.mkQ _ ∘ₗ f.hom) fun g => LinearMap.ext fun x => by
    simp only [LinearMap.coe_comp, Function.comp_apply, hom.comm_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq, mem_coinvariantsKer _ g (f.hom x) _ rfl]

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

@[simp] def coinvariantsToFinsupp (α : Type*) :
  (ρ.finsupp α).coinvariants →ₗ[k] α →₀ ρ.coinvariants :=
(coinvariantsLift _ (Finsupp.mapRange.linearMap (Submodule.mkQ _)) <| fun g => by
  ext i x j
  simp only [finsupp_apply, LinearMap.coe_comp, Finsupp.coe_lsum, Function.comp_apply,
    Finsupp.lsingle_apply, map_zero, Finsupp.sum_single_index, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_single, Submodule.mkQ_apply, (Submodule.Quotient.eq _).2
    (mem_coinvariantsKer _ g _ _ rfl)])

@[simp] def finsuppToCoinvariants (α : Type*) :
    (α →₀ ρ.coinvariants) →ₗ[k] (ρ.finsupp α).coinvariants :=
  Finsupp.lsum (R := k) k fun a => coinvariantsMap (ρ.lsingle a)

@[simps] def coinvariantsFinsuppLEquiv (α : Type*) :
    (ρ.finsupp α).coinvariants ≃ₗ[k] α →₀ ρ.coinvariants where
      toFun := coinvariantsToFinsupp ρ α
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := finsuppToCoinvariants ρ α
      left_inv := fun x => by
        show (finsuppToCoinvariants ρ α ∘ₗ _) x = LinearMap.id (R := k) x
        refine' LinearMap.ext_iff.1 (Submodule.linearMap_qext _ _) x
        ext a x
        simp only [finsuppToCoinvariants, coinvariantsMap, coinvariantsLift, lsingle_hom,
          coinvariantsToFinsupp, LinearMap.coe_comp, Finsupp.coe_lsum, LinearMap.coe_mk,
          AddHom.coe_mk, Function.comp_apply, Finsupp.lsingle_apply, Submodule.mkQ_apply,
          Submodule.liftQ_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
          map_zero, Finsupp.sum_single_index, LinearMap.id_comp]
      right_inv := fun x => by
        show (coinvariantsToFinsupp ρ α ∘ₗ _) x = LinearMap.id (R := k) x
        refine' LinearMap.ext_iff.1 _ x
        ext i x j
        simp only [coinvariantsToFinsupp, coinvariantsLift, finsuppToCoinvariants, coinvariantsMap,
          lsingle_hom, LinearMap.coe_comp, Finsupp.coe_lsum, Function.comp_apply,
          Submodule.mkQ_apply, Finsupp.lsingle_apply, map_zero, Finsupp.sum_single_index,
          Submodule.liftQ_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
          LinearMap.id_comp]

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
    ∘ₗ (TensorProduct.comm _ _ _).toLinearMap) fun g => TensorProduct.ext <| by
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

@[simp] lemma tensor2Inv_apply (x : A) :
    tensor2Inv ρ x = Submodule.Quotient.mk (x ⊗ₜ Finsupp.single (1 : G) (1 : k)) := rfl

@[simps] def tensor2Iso : (tensor2Obj ρ (ofMulAction k G G)) ≃ₗ[k] A where
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

variable (α : Type*)

open TensorProduct

-- ??!!
instance whatTheFuck2 : AddCommGroup (A ⊗[k] (G →₀ k)) := by infer_instance
instance whatTheFuck : AddCommGroup (A ⊗[k] (α →₀ (G →₀ k))) :=
@TensorProduct.addCommGroup k _ A (α →₀ (G →₀ k)) _ _ _ _

def coinvariantsTprodFreeToFinsupp :
    (ρ.tprod (Representation.free k G α)).coinvariants →ₗ[k] (α →₀ A) :=
  (coinvariantsFinsuppLEquiv _ α ≪≫ₗ Finsupp.lcongr (Equiv.refl α)
    (tensor2Iso ρ)).toLinearMap ∘ₗ coinvariantsMap (finsuppTprodRight ρ
      (Representation.ofMulAction k G G) α).tohom

@[simp] lemma coinvariantsTprodFreeToFinsupp_apply (x : A) (i : α) (g : G) (r : k) :
    coinvariantsTprodFreeToFinsupp ρ α (Submodule.Quotient.mk
      (x ⊗ₜ Finsupp.single i (Finsupp.single g r)))
      = Finsupp.single i (r • ρ g⁻¹ x) := by
  simp only [coinvariantsTprodFreeToFinsupp, coinvariantsMap, coinvariantsLift, finsuppTprodRight,
    iso.mk', LinearEquiv.invFun_eq_symm, LinearEquiv.mk_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, Submodule.liftQ_apply, finsuppTensorRight_tmul_single,
    Submodule.mkQ_apply, LinearEquiv.trans_apply, coinvariantsFinsuppLEquiv_apply,
    coinvariantsToFinsupp, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Finsupp.lcongr_single, Equiv.refl_apply, tensor2Iso_apply, tensor2Hom_apply]

def finsuppToCoinvariantsTprodFree :
    (α →₀ A) →ₗ[k] (ρ.tprod (Representation.free k G α)).coinvariants :=
  coinvariantsMap (iso.symm _ _ (finsuppTprodRight ρ
    (Representation.ofMulAction k G G) α)).tohom ∘ₗ
      (coinvariantsFinsuppLEquiv _ α ≪≫ₗ Finsupp.lcongr (Equiv.refl α)
        (tensor2Iso ρ)).symm.toLinearMap

@[simp] lemma finsuppToCoinvariantsTprodFree_apply (i : α) (x : A) :
    finsuppToCoinvariantsTprodFree ρ α (Finsupp.single i x)
      = Submodule.Quotient.mk (x ⊗ₜ Finsupp.single i (Finsupp.single (1 : G) (1 : k))) := by
  simp only [finsuppToCoinvariantsTprodFree, coinvariantsMap, coinvariantsLift, finsuppTprodRight,
    iso.mk', LinearEquiv.invFun_eq_symm, LinearEquiv.mk_coe, iso.symm_hom, LinearEquiv.trans_symm,
    Finsupp.lcongr_symm, Equiv.refl_symm, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.trans_apply, Finsupp.lcongr_single, Equiv.refl_apply,
    tensor2Iso_symm_apply, tensor2Inv_apply, coinvariantsFinsuppLEquiv_symm_apply,
    finsuppToCoinvariants, lsingle_hom, Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index,
    Submodule.liftQ_apply, Finsupp.lsingle_apply, Submodule.mkQ_apply,
    finsuppTensorRight_symm_single_tmul]

@[simps] def coinvariantsTprodFreeLEquiv :
    (ρ.tprod (Representation.free k G α)).coinvariants ≃ₗ[k] (α →₀ A) where
      toFun := coinvariantsTprodFreeToFinsupp ρ α
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := finsuppToCoinvariantsTprodFree ρ α
      left_inv := fun x => by
        show (finsuppToCoinvariantsTprodFree ρ α ∘ₗ _) x = LinearMap.id (R := k) x
        refine' LinearMap.ext_iff.1 (Submodule.linearMap_qext _ <| TensorProduct.ext <|
          LinearMap.ext fun a => _) x
        ext i g
        simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
          LinearMap.compr₂_apply, mk_apply, LinearMap.coe_mk, AddHom.coe_mk, Submodule.mkQ_apply,
          coinvariantsTprodFreeToFinsupp_apply, one_smul, finsuppToCoinvariantsTprodFree_apply,
          LinearMap.id_comp, Submodule.Quotient.eq]
        refine' mem_coinvariantsKer (ρ.tprod (free k G α)) g⁻¹ (a ⊗ₜ[k] Finsupp.single i
          (Finsupp.single g 1)) _ (by simp only [tprod_apply, map_tmul, free_ρ_single_single,
            mul_left_inv])
      right_inv := fun x => by
        show (coinvariantsTprodFreeToFinsupp ρ α ∘ₗ _) x = LinearMap.id (R := k) x
        refine' LinearMap.ext_iff.1 _ x
        ext i a
        simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
          finsuppToCoinvariantsTprodFree_apply, coinvariantsTprodFreeToFinsupp_apply, inv_one, _root_.map_one,
          LinearMap.one_apply, one_smul, LinearMap.id_comp]

def d (n : ℕ) : ((Fin (n + 1) → G) →₀ A) →ₗ[k] (Fin n → G) →₀ A :=
  Finsupp.lsum (R := k) k fun g => Finsupp.lsingle (fun i => g i.succ) ∘ₗ ρ (g 0)⁻¹
    + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : ℕ) + 1) • Finsupp.lsingle (Fin.contractNth j (· * ·) g)

end Representation
namespace Rep
variable {k G : Type u} [CommRing k] [Group G]
open MonoidalCategory

def finsuppTensorLeft (α : Type u) (A B : Rep k G) :
    A.finsupp.obj α ⊗ B ≅ (A ⊗ B).finsupp.obj α :=
Rep.mkIso (A.ρ.finsuppTprodLeft B.ρ α).toLinearEquiv
  (A.ρ.finsuppTprodLeft B.ρ α).tohom.comm

def finsuppTensorRight (α : Type u) (A B : Rep k G) :
    A ⊗ B.finsupp.obj α ≅ (A ⊗ B).finsupp.obj α :=
Rep.mkIso (A.ρ.finsuppTprodRight B.ρ α).toLinearEquiv
  (A.ρ.finsuppTprodRight B.ρ α).tohom.comm

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

instance : Limits.PreservesColimitsOfSize.{u, u} (coinvariants k G) :=
  (coinvariantsAdjunction k G).leftAdjointPreservesColimits

variable {k G}

def coinvariantsFinsuppIso (A : Rep k G) (α : Type u) :
  (coinvariants k G).obj ((Rep.finsupp A).obj α)
    ≅ ModuleCat.of k (α →₀ (coinvariants k G).obj A) :=
  (A.ρ.coinvariantsFinsuppLEquiv α).toModuleIso

def coinvariantsTensorLeftRegular (A : Rep k G) :
    (coinvariants k G).obj (A ⊗ Rep.leftRegular k G) ≅ A.V :=
  A.ρ.tensor2Iso.toModuleIso

open MonoidalCategory

def coinvariantsTensorFreeIso (A : Rep k G) (α : Type u) :
    (coinvariants k G).obj (A ⊗ (Rep.free k G).obj α)
      ≅ ModuleCat.of k (α →₀ A) :=
  (A.ρ.coinvariantsTprodFreeLEquiv α).toModuleIso

variable (k G)

@[simps] def tensorG : Rep k G ⥤ Rep k G ⥤ ModuleCat k :=
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

instance (A : Rep k G) : ((tensorG k G).obj A).Additive := by
  unfold tensorG
  infer_instance

def Tor (n : ℕ) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj X := Functor.leftDerived ((tensorG k G).obj X) n
  map f := NatTrans.leftDerived ((tensorG k G).map f) n

variable {k G}
variable (A : Rep k G)

def tensorGChainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] :
  ChainComplex (Rep k G) α ⥤ ChainComplex (ModuleCat k) α :=
Functor.mapHomologicalComplex ((tensorG k G).obj A) _

def torIso (B : Rep k G) (P : ProjectiveResolution B) (n : ℕ) :
    ((Tor k G n).obj A).obj B ≅ ((tensorGChainComplex A ℕ).obj P.complex).homology n :=
  ProjectiveResolution.isoLeftDerivedObj P ((tensorG k G).obj A) n

def tensorGBarResolution := (tensorGChainComplex A ℕ).obj (Rep.barResolution k G)

def tensorGStdResolution := (tensorGChainComplex A ℕ).obj (groupCohomology.resolution k G)

@[nolint checkType] theorem d_eq (n : ℕ) :
    A.ρ.d n =
      (coinvariantsTensorFreeIso A (Fin (n + 1) → G)).inv ≫
        (tensorGBarResolution A).d (n + 1) n ≫
          (coinvariantsTensorFreeIso A (Fin n → G)).hom := by
  ext g a : 2
  simp only [ModuleCat.comp_def, LinearMap.comp_apply,
    coinvariantsTensorFreeIso, LinearEquiv.toModuleIso_inv,
    LinearEquiv.toModuleIso_hom]
  show _ = A.ρ.coinvariantsTprodFreeToFinsupp (Fin n → G) ((tensorGBarResolution A).d _ _
    (A.ρ.finsuppToCoinvariantsTprodFree _ _))
  simp only [Finsupp.lsingle_apply, Representation.finsuppToCoinvariantsTprodFree_apply]
  simp only [tensorGBarResolution, tensorGChainComplex, tensorG_obj, Functor.mapHomologicalComplex_obj_X,
    ChainComplex.of_x, Functor.comp_obj, tensorLeft_obj, Monoidal.transportStruct_tensorObj,
    Equivalence.symm_functor, Action.functorCategoryEquivalence_inverse, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, coinvariants_obj,
    Functor.mapHomologicalComplex_obj_d, barResolution.d_def, Functor.comp_map, tensorLeft_map,
    Monoidal.transportStruct_tensorHom, CategoryTheory.Functor.map_id, coinvariants_map,
    coinvariantsMap, Representation.coinvariantsMap, Representation.coinvariantsLift,
    Action.FunctorCategoryEquivalence.inverse_map_hom, Monoidal.tensorHom_app,
    Action.FunctorCategoryEquivalence.functor_obj_obj, NatTrans.id_app,
    Action.FunctorCategoryEquivalence.functor_map_app, ModuleCat.ofHom_apply, Submodule.liftQ_apply,
    LinearMap.coe_comp, Function.comp_apply]
  erw [ModuleCat.MonoidalCategory.hom_apply]
  rw [Rep.d_single]
  rw [TensorProduct.tmul_add]
  rw [map_add]
  rw [TensorProduct.tmul_sum]
  rw [map_sum]
  simp only [Submodule.mkQ_apply]
  rw [map_add, map_sum,
    A.ρ.coinvariantsTprodFreeToFinsupp_apply, one_smul, ModuleCat.id_apply]
  conv =>
    · enter [2, 2, 2, x]
      rw [A.ρ.coinvariantsTprodFreeToFinsupp_apply, inv_one, map_one]
  rw [Representation.d]
  simp only [Finsupp.coe_lsum, map_zero, Finsupp.sum_single_index, LinearMap.add_apply,
    LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearMap.coeFn_sum,
    Finset.sum_apply, LinearMap.smul_apply, Finsupp.smul_single, LinearMap.one_apply]

-- needs a ModuleCat.ofHom and in d_eq.
noncomputable abbrev inhomogeneousChains :
    ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k ((Fin n → G) →₀ A))
    (fun n => A.ρ.d n) fun n => by
    simp only [d_eq, d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, (tensorGBarResolution A).d_comp_d] }

@[simp]
theorem inhomogeneousChains.d_def (n : ℕ) :
    (inhomogeneousChains A).d (n + 1) n = A.ρ.d n :=
  ChainComplex.of_d _ _ _ _

set_option profiler true

def inhomogeneousChainsIsoTensorGBar  :
    inhomogeneousChains A ≅ tensorGBarResolution A := by
  refine' HomologicalComplex.Hom.isoOfComponents _ _
  · intro i
    apply (coinvariantsTensorFreeIso A (Fin i → G)).symm
  rintro i j (h : j + 1 = i)
  subst h
  simp only [Iso.symm_hom, inhomogeneousChains.d_def, d_eq, Category.assoc]
  slice_rhs 2 4 => { rw [Iso.hom_inv_id, Category.comp_id] }

def inhomogeneousChainsIsoTensorGStd  : inhomogeneousChains A ≅ tensorGStdResolution A :=
  inhomogeneousChainsIsoTensorGBar A ≪≫ (tensorGChainComplex A ℕ).mapIso (Rep.barResolutionIso k G)

abbrev cycles (n : ℕ) : ModuleCat k := (inhomogeneousChains A).cycles n

abbrev iCycles (n : ℕ) : cycles A n ⟶ ModuleCat.of k ((Fin n → G) →₀ A) :=
  (inhomogeneousChains A).iCycles n

abbrev toCycles (i j : ℕ) : ModuleCat.of k ((Fin i → G) →₀ A) ⟶ cycles A j :=
  (inhomogeneousChains A).toCycles i j

def groupHomology (n : ℕ) : ModuleCat k :=
  (inhomogeneousChains A).homology n

abbrev groupHomologyπ (n : ℕ) :
    cycles A n ⟶ groupHomology A n :=
  (inhomogeneousChains A).homologyπ n

def groupHomologyIsoTor [Group G] (A : Rep k G) (n : ℕ) :
    groupHomology A n ≅ ((Tor k G n).obj A).obj (Rep.trivial k G k) :=
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsIsoTensorGStd A)).hom n ≪≫
    (torIso A (Rep.trivial k G k) (groupCohomology.projectiveResolution k G) n).symm
