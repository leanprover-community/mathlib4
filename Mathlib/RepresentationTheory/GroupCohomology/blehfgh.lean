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

theorem Submodule.Quotient.mk_sum {ι : Type*} (S : Submodule R A)
    (s : Finset ι) (f : ι → A) :
    Submodule.Quotient.mk (p := S) (s.sum f) = s.sum (fun i => Submodule.Quotient.mk (f i)) :=
  map_sum (Submodule.mkQ S) _ _

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Rep

variable {k G : Type u} [CommRing k] [Group G] (A B C : Rep k G) {n : ℕ} (α : Type u)

def finsuppTensorLeft [DecidableEq α] :
    A.finsupp α ⊗ B ≅ (A ⊗ B).finsupp α :=
  mkIso' (TensorProduct.finsuppLeft k A B α) fun g =>
    TensorProduct.ext <| Finsupp.lhom_ext fun a b => by
    ext (x : B)
    simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, coe_def, tensor_ρ]
    simp [coe_tensor, tensor_ρ', TensorProduct.finsuppLeft_apply_tmul]

variable {A B}

@[simp]
theorem finsuppTensorLeft_hom_apply_tmul [DecidableEq α] (x : α →₀ A) (y : B) :
    hom (finsuppTensorLeft A B α).hom (x ⊗ₜ y) = x.sum fun i a => Finsupp.single i (a ⊗ₜ y) :=
  TensorProduct.finsuppLeft_apply_tmul _ _

@[simp]
theorem finsuppTensorLeft_inv_apply_single [DecidableEq α] (a : α) (x : A) (y : B) :
    hom (finsuppTensorLeft A B α).inv (Finsupp.single a (x ⊗ₜ y)) = Finsupp.single a x ⊗ₜ y :=
  TensorProduct.finsuppLeft_symm_apply_single _ _ _

variable (A B)

def finsuppTensorRight [DecidableEq α] :
    A ⊗ B.finsupp α ≅ (A ⊗ B).finsupp α :=
  mkIso' (TensorProduct.finsuppRight k A B α) fun g =>
    TensorProduct.ext <| LinearMap.ext fun x => Finsupp.lhom_ext fun a b => by
    simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, coe_def, tensor_ρ]
    simp [coe_tensor, tensor_ρ', TensorProduct.finsuppRight_apply_tmul]

variable {A B}

@[simp]
theorem finsuppTensorRight_hom_apply_tmul [DecidableEq α] (x : A) (y : α →₀ B) :
    hom (finsuppTensorRight A B α).hom (x ⊗ₜ y) = y.sum fun i b => Finsupp.single i (x ⊗ₜ b) :=
  TensorProduct.finsuppRight_apply_tmul _ _

@[simp]
theorem finsuppTensorRight_inv_apply_single [DecidableEq α] (a : α) (x : A) (y : B) :
    hom (finsuppTensorRight A B α).inv (Finsupp.single a (x ⊗ₜ y)) = x ⊗ₜ Finsupp.single a y :=
  TensorProduct.finsuppRight_symm_apply_single _ _ _

end Rep
namespace Representation

variable {k G V W : Type*} [CommRing k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    [AddCommGroup W] [Module k W] (τ : Representation k G W)

def inv : Representation k Gᵐᵒᵖ V :=
  ρ.comp (MulEquiv.inv' G).symm.toMonoidHom

@[simp] lemma inv_apply (g : Gᵐᵒᵖ) (x : V) :
  ρ.inv g x = ρ g.unop⁻¹ x := rfl

abbrev coinvariantsKer := Submodule.span k (Set.range <| fun (x : G × V) => ρ x.1 x.2 - x.2)

lemma mem_coinvariantsKer (g : G) (x a : V) (h : ρ g x - x = a) : a ∈ coinvariantsKer ρ :=
Submodule.subset_span ⟨(g, x), h⟩

abbrev coinvariants := V ⧸ coinvariantsKer ρ

def coinvariantsLift (f : V →ₗ[k] W) (h : ∀ (x : G), f ∘ₗ ρ x = f) :
    ρ.coinvariants →ₗ[k] W :=
  Submodule.liftQ _ f <| Submodule.span_le.2 fun x ⟨⟨g, y⟩, hy⟩ => by
    simpa only [← hy, SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero, LinearMap.coe_comp,
      Function.comp_apply] using LinearMap.ext_iff.1 (h g) y

@[simp] theorem coinvariantsLift_mkQ (f : V →ₗ[k] W) {h : ∀ (x : G), f ∘ₗ ρ x = f} :
  coinvariantsLift ρ f h ∘ₗ (coinvariantsKer ρ).mkQ = f := rfl

@[simp]
theorem coinvariantsLift_apply (f : V →ₗ[k] W) {h : ∀ (x : G), f ∘ₗ ρ x = f} (x : V) :
  coinvariantsLift ρ f h (Submodule.Quotient.mk x) = f x := rfl
end Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G] {A B C D : Rep k G} {n : ℕ} (α : Type u)
  {V : Type u} [AddCommGroup V] [Module k V]
open Representation
def coinvariantsLift (f : A ⟶ (Rep.trivial k G V)) :
    coinvariants A.ρ →ₗ[k] V :=
  Representation.coinvariantsLift _ (hom f) f.comm

def coinvariantsMap (f : A ⟶ B) :
    coinvariants A.ρ →ₗ[k] coinvariants B.ρ :=
  Representation.coinvariantsLift _ (Submodule.mkQ _ ∘ₗ hom f) fun g => LinearMap.ext fun x => by
    simpa [hom_comm_apply'', Submodule.Quotient.eq]
    using mem_coinvariantsKer B.ρ g (hom f x) _ rfl

@[simp] theorem coinvariantsMap_mkQ (f : A ⟶ B) :
  coinvariantsMap f ∘ₗ (coinvariantsKer A.ρ).mkQ = (coinvariantsKer B.ρ).mkQ ∘ₗ hom f := rfl

@[simp]
theorem coinvariantsMap_apply (f : A ⟶ B) (x : A) :
  coinvariantsMap f (Submodule.Quotient.mk x) = Submodule.Quotient.mk (hom f x) := rfl

variable (α : Type u)
variable (A B)

@[simps]
def coinvariantsHomEquiv :
    (coinvariants A.ρ →ₗ[k] B) ≃ (A ⟶ trivial k G B) where
  toFun := fun f => {
    hom := f ∘ₗ (coinvariantsKer A.ρ).mkQ
    comm := fun g => by
      ext x
      exact congr(f $((Submodule.Quotient.eq <| coinvariantsKer A.ρ).2
        (mem_coinvariantsKer _ g x _ rfl))) }
  invFun := fun f => coinvariantsLift f
  left_inv := fun x => Submodule.linearMap_qext _ rfl
  right_inv := fun x => Action.Hom.ext rfl

@[simp] def coinvariantsToFinsupp :
    coinvariants (A.finsupp α).ρ →ₗ[k] α →₀ coinvariants A.ρ :=
(Representation.coinvariantsLift _ (Finsupp.mapRange.linearMap (Submodule.mkQ _)) <| fun g =>
  Finsupp.lhom_ext fun i x => by
  simp [Finsupp.mapRange.linearMap, ← (Submodule.Quotient.eq _).2
    (mem_coinvariantsKer A.ρ g x _ rfl), finsupp])

@[simp] def finsuppToCoinvariants :
    (α →₀ coinvariants A.ρ) →ₗ[k] coinvariants (A.finsupp α).ρ :=
  Finsupp.lsum (R := k) k fun a => coinvariantsMap (lsingle A a)

@[simps]
def coinvariantsFinsuppLEquiv :
    coinvariants (A.finsupp α).ρ ≃ₗ[k] α →₀ coinvariants A.ρ where
  toFun := coinvariantsToFinsupp A α
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := finsuppToCoinvariants A α
  left_inv := fun x => by
    show (finsuppToCoinvariants A α ∘ₗ _) x = LinearMap.id (R := k) x
    refine LinearMap.ext_iff.1 (Submodule.linearMap_qext _ <| Finsupp.lhom_ext fun a x => ?_) x
    have := coinvariantsMap_apply (A.lsingle a) x
    simp_all
  right_inv := fun x => by
    show (coinvariantsToFinsupp A α ∘ₗ _) x = LinearMap.id (R := k) x
    refine LinearMap.ext_iff.1 (Finsupp.lhom_ext fun a x => Quotient.inductionOn'
      (x : coinvariants A.ρ) fun y => ?_) x
    simp [coinvariantsMap, Submodule.Quotient.mk''_eq_mk]

variable {A B}

lemma coinvariants_whisker_comm (f : A ⟶ B) (g : C ⟶ D) :
    coinvariantsMap (B ◁ g) ∘ₗ coinvariantsMap (f ▷ C)
      = coinvariantsMap (f ▷ D)
        ∘ₗ coinvariantsMap (A ◁ g) :=
  Submodule.linearMap_qext _ <| TensorProduct.ext' fun _ _ => by rfl

variable (A)

def coinvariantsTensorHom : coinvariants (A ⊗ leftRegular k G).ρ →ₗ[k] A :=
  Representation.coinvariantsLift _ (TensorProduct.lift (Finsupp.linearCombination _
    (fun g => A.ρ g⁻¹)) ∘ₗ (TensorProduct.comm _ _ _).toLinearMap) fun g => TensorProduct.ext <|
      LinearMap.ext fun (x : A) => Finsupp.lhom_ext fun a y => by
    simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, coe_def, tensor_ρ]
    simp [coe_tensor, tensor_ρ', TensorProduct.finsuppLeft_apply_tmul]

variable {A}

@[simp] lemma coinvariantsTensorHom_apply (x : A) (g : G) (r : k) :
    coinvariantsTensorHom A (Submodule.Quotient.mk (p := coinvariantsKer _)
      (x ⊗ₜ Finsupp.single g r)) = r • A.ρ g⁻¹ x :=
  congr($(Finsupp.linearCombination_single k (v := fun g => A.ρ g⁻¹) r g) x)

variable (A)

def toCoinvariantsTensor : A →ₗ[k] coinvariants (A ⊗ leftRegular k G).ρ :=
  Submodule.mkQ _ ∘ₗ (TensorProduct.mk k A (G →₀ k)).flip (Finsupp.single 1 1)

variable {A}

@[simp] lemma toCoinvariantsTensor_apply (x : A) :
    toCoinvariantsTensor A x = Submodule.Quotient.mk (x ⊗ₜ Finsupp.single (1 : G) (1 : k)) := rfl

variable (A)

@[simps]
def coinvariantsTensorLEquiv : (coinvariants (A ⊗ leftRegular k G).ρ) ≃ₗ[k] A where
  toFun := coinvariantsTensorHom A
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := toCoinvariantsTensor A
  left_inv := LinearMap.congr_fun (f := (toCoinvariantsTensor A) ∘ₗ coinvariantsTensorHom A)
    (g := LinearMap.id) <|
    Submodule.linearMap_qext _ <| TensorProduct.ext <|
      LinearMap.ext fun (a : A) => Finsupp.lhom_ext fun g r => (Submodule.Quotient.eq _).2 <| by
      apply mem_coinvariantsKer (A.ρ.tprod (Representation.leftRegular k G)) g⁻¹
        (a ⊗ₜ[k] Finsupp.single g r)
      have := coinvariantsTensorHom_apply a g r
      simp_all [coe_tensor, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
  right_inv := fun x => by simp [coe_def, coe_tensor, toCoinvariantsTensor,
    coinvariantsTensorHom]

variable (α : Type u) [DecidableEq α]

open TensorProduct

def coinvariantsTensorFreeToFinsupp :
    coinvariants (A ⊗ (Rep.free k G α)).ρ →ₗ[k] (α →₀ A) :=
  (coinvariantsFinsuppLEquiv _ α ≪≫ₗ Finsupp.lcongr (Equiv.refl α)
    (coinvariantsTensorLEquiv A)).toLinearMap ∘ₗ coinvariantsMap (finsuppTensorRight A
      (leftRegular k G) α).hom

variable {A α}

@[simp] lemma coinvariantsTensorFreeToFinsupp_apply (x : A) (i : α) (g : G) (r : k) :
    coinvariantsTensorFreeToFinsupp A α (Submodule.Quotient.mk
      (x ⊗ₜ Finsupp.single i (Finsupp.single g r)))
      = Finsupp.single i (r • A.ρ g⁻¹ x) := by
  have h := finsuppTensorRight_hom_apply_tmul (B := leftRegular k G)
    α x (Finsupp.single i (Finsupp.single g r))
  have h' := coinvariantsTensorHom_apply x g r
  simp_all [coinvariantsTensorFreeToFinsupp, coinvariantsMap,
    coinvariantsFinsuppLEquiv, Finsupp.mapRange.linearMap, coinvariantsTensorLEquiv]

variable (A α)

def finsuppToCoinvariantsTensorFree :
    (α →₀ A) →ₗ[k] coinvariants (A ⊗ (Rep.free k G α)).ρ :=
  coinvariantsMap ((finsuppTensorRight A (leftRegular k G) α)).inv ∘ₗ
    (coinvariantsFinsuppLEquiv _ α ≪≫ₗ Finsupp.lcongr (Equiv.refl α)
      (coinvariantsTensorLEquiv A)).symm.toLinearMap

variable {A α}

@[simp] lemma finsuppToCoinvariantsTensorFree_apply (i : α) (x : A) :
    finsuppToCoinvariantsTensorFree A α (Finsupp.single i x)
      = Submodule.Quotient.mk (x ⊗ₜ Finsupp.single i (Finsupp.single (1 : G) (1 : k))) := by
  simpa [finsuppToCoinvariantsTensorFree, coinvariantsMap, coinvariantsFinsuppLEquiv]
    using congr(Submodule.Quotient.mk $(finsuppTensorRight_inv_apply_single (A := A)
      (B := leftRegular k G) α i x (Finsupp.single 1 1)))

variable (A α)

open Finsupp
@[simps] def coinvariantsTensorFreeLEquiv :
    coinvariants (A ⊗ Rep.free k G α).ρ ≃ₗ[k] (α →₀ A) where
      toFun := coinvariantsTensorFreeToFinsupp A α
      map_add' := map_add _
      map_smul' := map_smul _
      invFun := finsuppToCoinvariantsTensorFree A α
      left_inv := fun x => by
        show (finsuppToCoinvariantsTensorFree A α ∘ₗ _) x = LinearMap.id (R := k) x
        refine LinearMap.ext_iff.1 (Submodule.linearMap_qext _ <| TensorProduct.ext <|
          LinearMap.ext fun (a : A) => lhom_ext' fun i => lhom_ext fun g r => ?_) x
        simp only [LinearMap.coe_comp,
          Function.comp_apply, lsingle_apply, LinearMap.compr₂_apply, mk_apply, LinearMap.coe_mk,
          AddHom.coe_mk, Submodule.mkQ_apply, coinvariantsTensorFreeToFinsupp_apply a i g r,
          finsuppToCoinvariantsTensorFree_apply, LinearMap.id_comp, Submodule.Quotient.eq]
        refine mem_coinvariantsKer (A ⊗ Rep.free k G α).ρ g⁻¹ (a ⊗ₜ[k] single i (single g r)) _
          (sub_left_inj.2 ?_)
        rw [tensor_ρ]
        simp [coe_tensor, TensorProduct.smul_tmul]
      right_inv := fun x => by
        show (coinvariantsTensorFreeToFinsupp A α ∘ₗ _) x = LinearMap.id (R := k) x
        refine LinearMap.ext_iff.1 (Finsupp.lhom_ext fun i a => ?_) x
        simp [coinvariantsTensorFreeToFinsupp_apply a i 1 1]

def d (n : ℕ) : ((Fin (n + 1) → G) →₀ A) →ₗ[k] (Fin n → G) →₀ A :=
  Finsupp.lsum (R := k) k fun g => Finsupp.lsingle (fun i => g i.succ) ∘ₗ A.ρ (g 0)⁻¹
    + Finset.univ.sum fun j : Fin (n + 1) =>
      (-1 : k) ^ ((j : ℕ) + 1) • Finsupp.lsingle (Fin.contractNth j (· * ·) g)

theorem d_apply (n : ℕ) (x : (Fin (n + 1) → G) →₀ A) :
    A.d n x = x.sum fun g a => Finsupp.single (fun i => g i.succ) (A.ρ (g 0)⁻¹ a)
      + Finset.univ.sum fun j : Fin (n + 1) =>
        (-1 : k) ^ ((j : ℕ) + 1) • Finsupp.single (Fin.contractNth j (· * ·) g) a := by
  ext
  simp [d]

variable (k G)

@[simps] def coinvariants : Rep k G ⥤ ModuleCat k where
  obj := fun A => ModuleCat.of k (Representation.coinvariants A.ρ)
  map := fun f => coinvariantsMap f
  map_id := fun X => by
    ext x
    refine Quotient.inductionOn' x (fun y => rfl)
  map_comp := fun f g => by
    ext x
    refine Quotient.inductionOn' x (fun y => rfl)

instance : (coinvariants k G).Additive where
  map_add := fun {_ _ _ _} => LinearMap.ext fun x => Quotient.inductionOn' x (fun _ => rfl)

variable {k G}

abbrev coinvariantsFinsuppIso (A : Rep k G) (α : Type u) :
    (coinvariants k G).obj (A.finsupp α) ≅ ModuleCat.of k (α →₀ (coinvariants k G).obj A) :=
  (coinvariantsFinsuppLEquiv A α).toModuleIso

abbrev coinvariantsTensorLeftRegular (A : Rep k G) :
    (coinvariants k G).obj (A ⊗ Rep.leftRegular k G) ≅ A.V :=
  A.coinvariantsTensorLEquiv.toModuleIso

open MonoidalCategory

abbrev coinvariantsTensorFreeIso (A : Rep k G) (α : Type u) [DecidableEq α] :
    (coinvariants k G).obj (A ⊗ Rep.free k G α)
      ≅ ModuleCat.of k (α →₀ A) :=
  (A.coinvariantsTensorFreeLEquiv α).toModuleIso

variable (k G)

@[simps] def tensor : Rep k G ⥤ Rep k G ⥤ ModuleCat k :=
{ obj := fun A => MonoidalCategory.tensorLeft A ⋙ coinvariants k G
  map := fun f => {
    app := fun A => coinvariantsMap (f ⊗ 𝟙 A)
    naturality := fun A B g => (coinvariants_whisker_comm f g).symm }
  map_id := fun A => NatTrans.ext <| by
    ext B : 1
    dsimp only
    rw [MonoidalCategory.tensor_id]
    exact (coinvariants k G).map_id _
  map_comp := fun f g => NatTrans.ext <| by
    ext B : 1
    dsimp only
    rw [MonoidalCategory.comp_tensor_id]
    exact (coinvariants k G).map_comp _ _ }

instance (A : Rep k G) : ((tensor k G).obj A).Additive := by
  unfold tensor
  infer_instance

def Tor (n : ℕ) : Rep k G ⥤ Rep k G ⥤ ModuleCat k where
  obj X := Functor.leftDerived ((tensor k G).obj X) n
  map f := NatTrans.leftDerived ((tensor k G).map f) n

variable {k G}
variable (A : Rep k G)

def tensorChainComplex (α : Type*) [AddRightCancelSemigroup α] [One α] :
  ChainComplex (Rep k G) α ⥤ ChainComplex (ModuleCat k) α :=
Functor.mapHomologicalComplex ((tensor k G).obj A) _

def torIso (B : Rep k G) (P : ProjectiveResolution B) (n : ℕ) :
    ((Tor k G n).obj A).obj B ≅ ((tensorChainComplex A ℕ).obj P.complex).homology n :=
  ProjectiveResolution.isoLeftDerivedObj P ((tensor k G).obj A) n

def tensorBarResolution := (tensorChainComplex A ℕ).obj (groupHomology.barResolution k G)

def tensorStdResolution := (tensorChainComplex A ℕ).obj (groupCohomology.resolution k G)

open groupHomology
theorem d_eq [DecidableEq G] :
    A.d n = (coinvariantsTensorFreeIso A (Fin (n + 1) → G)).inv ≫
      (tensorBarResolution A).d (n + 1) n ≫ (coinvariantsTensorFreeIso A (Fin n → G)).hom := by
  ext g a : 2
  show _ = A.coinvariantsTensorFreeToFinsupp (Fin n → G) ((tensorBarResolution A).d _ _
    (A.finsuppToCoinvariantsTensorFree _ _))
  simp only [Finsupp.lsingle_apply, finsuppToCoinvariantsTensorFree_apply, tensorBarResolution,
    tensorChainComplex, Functor.mapHomologicalComplex_obj_X, ChainComplex.of_x,
    Functor.mapHomologicalComplex_obj_d, barResolution.d_def]
  show _ = A.coinvariantsTensorFreeToFinsupp (Fin n → G)
    (Submodule.Quotient.mk (a ⊗ₜ[k] hom (groupHomology.d k G n) (single _ _)))
  have := d_single (k := k) g
  simp_all [TensorProduct.tmul_add, TensorProduct.tmul_sum, Submodule.Quotient.mk_sum, d,
    coinvariantsTensorFreeToFinsupp_apply (α := Fin n → G) a]

noncomputable abbrev inhomogeneousChains [DecidableEq G] :
    ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of k ((Fin n → G) →₀ A))
    (fun n => A.d n) fun n => by
    simp only [d_eq]
    slice_lhs 3 4 => { rw [Iso.hom_inv_id] }
    slice_lhs 2 4 => { rw [Category.id_comp, (tensorBarResolution A).d_comp_d] }
    simp

@[simp]
theorem inhomogeneousChains.d_def [DecidableEq G] (n : ℕ) :
    (inhomogeneousChains A).d (n + 1) n = A.d n :=
  ChainComplex.of_d _ _ _ _

def inhomogeneousChainsIsotensorBar [DecidableEq G] :
    inhomogeneousChains A ≅ tensorBarResolution A := by
  refine HomologicalComplex.Hom.isoOfComponents ?_ ?_
  · intro i
    apply (coinvariantsTensorFreeIso A (Fin i → G)).symm
  rintro i j (h : j + 1 = i)
  subst h
  simp only [Iso.symm_hom, inhomogeneousChains.d_def, d_eq, Category.assoc]
  slice_rhs 2 4 => { rw [Iso.hom_inv_id, Category.comp_id] }

variable [DecidableEq G]

def inhomogeneousChainsIsotensorStd  : inhomogeneousChains A ≅ tensorStdResolution A :=
  inhomogeneousChainsIsotensorBar A ≪≫ (tensorChainComplex A ℕ).mapIso (barResolutionIso k G)

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
  isoOfQuasiIsoAt (HomotopyEquiv.ofIso (inhomogeneousChainsIsotensorStd A)).hom n ≪≫
    (torIso A (Rep.trivial k G k) (groupCohomology.projectiveResolution k G) n).symm
