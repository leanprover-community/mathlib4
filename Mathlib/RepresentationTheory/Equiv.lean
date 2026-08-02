/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Intertwining

/-!
## Main purpose

This file is a preliminary file for the `Iso`s in `Rep`, we build all the isomorphisms from
representation level to avoid abusing defeq.

TODO (Edison) : refactor `Rep` into a two-field structure (bundled `Representation`) and rebuild
all the `Iso`s in `Rep` using the equivs in this file.

-/

@[expose] public section

open scoped MonoidAlgebra

universe u u' v v' w w'

variable {k : Type u} [Semiring k] {G : Type v} [Monoid G] {V : Type v'} [AddCommMonoid V]
  [Module k V] {W : Type w'} [AddCommMonoid W] [Module k W] (H : Type w) [Subsingleton H]
  [MulOneClass H] [MulAction G H]

namespace Representation

noncomputable section

variable (k G) in
/-- If there exists `G`-action on a trivial monoid `H` then the induced representation
  on `k[H]` is equivalent to the trivial representation. -/
def ofMulActionSubsingletonEquivTrivial : (ofMulAction k G H).Equiv (trivial k G k) :=
  .mk (MonoidAlgebra.uniqueLinearEquiv k H) fun g ↦ by ext a; simp [Subsingleton.elim (g • a) a]

@[simp]
lemma ofMulActionSubsingletonEquivTrivial_apply (f : k[H]) :
    (ofMulActionSubsingletonEquivTrivial k G H).toIntertwiningMap.toLinearMap f = f.coeff 1 := rfl

@[simp]
lemma ofMulActionSubsingletonEquivTrivial_symm_apply (r : k) :
    (ofMulActionSubsingletonEquivTrivial k G H).symm.toIntertwiningMap.toLinearMap r =
      .single 1 r := rfl

variable (k G) in
/-- The equivalence of representations between `(Fin 1 → G) →₀ k` and `G →₀ k`. -/
def diagonalOneEquivLeftRegular : (diagonal k G 1).Equiv (leftRegular k G) :=
  .mk (MonoidAlgebra.mapDomainLinearEquiv _ _ <| .funUnique _ _) fun g ↦ by ext; simp

@[simp]
lemma diagonalOneEquivLeftRegular_apply_single (f : Fin 1 → G) (r : k) :
    (diagonalOneEquivLeftRegular k G) (.single f r) = .single (f 0) r := by
  simp [diagonalOneEquivLeftRegular]

@[simp]
lemma diagonalOneEquivLeftRegular_symm_apply_single (g : G) (r : k) :
    (diagonalOneEquivLeftRegular k G).symm (.single g r) = .single (uniqueElim g) r := by
  simp [diagonalOneEquivLeftRegular]

section comm

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] (σ : Representation k G V)
  (ρ : Representation k G W)

section finsupp

open Finsupp

/-- Every `f : α → V` can induce an intertwining map between `(α →₀ k[G])` and `V`. -/
@[simps! toLinearMap]
def freeLift {α : Type w'} (f : α → V) : (free k G α).IntertwiningMap σ where
  toLinearMap := linearCombination k (fun x => σ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (MonoidAlgebra.coeffLinearEquiv _).toLinearMap
  isIntertwining' g := by ext; simp

@[simp]
lemma freeLift_single_single {α : Type w'} (i : α) (g : G) (r : k) (f : α → V) :
    freeLift σ f (Finsupp.single i (.single g r)) = r • σ g (f i) := by
  simp [freeLift]

open IntertwiningMap

/-- Equiv between the intertwining map module `(α →₀ G →₀ k) → V` and the function space `α → V`. -/
@[simps]
def freeLiftLEquiv (α : Type w') : ((free k G α).IntertwiningMap σ) ≃ₗ[k] (α → V) where
  toFun f i := f (single i (.single 1 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := freeLift σ
  left_inv f := by ext; simp [← f.isIntertwining]
  right_inv f := by simp [← toLinearMap_apply]

/-- Equiv between representations induced by linear equiv between `(α →₀ V) ⊗[k] W` and
  `α →₀ (V ⊗[k] W)`. -/
def finsuppTensorLeft (α : Type w') [DecidableEq α] :
    ((σ.finsupp α).tprod ρ).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppLeft _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppLeft_apply_tmul]

lemma finsuppTensorLeft_apply_tmul {α : Type w'} [DecidableEq α] (f : α →₀ V) (w : W) :
    finsuppTensorLeft σ ρ α (f ⊗ₜ w) = f.sum fun i v ↦ Finsupp.single i (v ⊗ₜ w) := by
  simp [finsuppTensorLeft, TensorProduct.finsuppLeft_apply_tmul]

@[simp]
lemma finsuppTensorLeft_apply_tmul_apply {α : Type w'} [DecidableEq α] (f : α →₀ V) (w : W)
    (i : α) : finsuppTensorLeft σ ρ α (f ⊗ₜ w) i = f i ⊗ₜ w := by
  simp +contextual [finsuppTensorLeft_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]
lemma finsuppTensorLeft_symm_apply_single {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W) :
    (finsuppTensorLeft σ ρ α).symm (Finsupp.single i (v ⊗ₜ w)) = Finsupp.single i v ⊗ₜ w := by
  simp [finsuppTensorLeft]

/-- Equiv between representations induced by linear equiv between `V ⊗[k] (α →₀ W)` and
  `α →₀ (V ⊗[k] W)`. -/
def finsuppTensorRight (α : Type w') [DecidableEq α] :
    (σ.tprod (ρ.finsupp α)).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppRight _ _ _ _ _) fun g ↦ by
    ext; simp [TensorProduct.finsuppRight_apply_tmul]

lemma finsuppTensorRight_apply_tmul {α : Type w'} [DecidableEq α] (v : V) (f : α →₀ W) :
    finsuppTensorRight σ ρ α (v ⊗ₜ f) = f.sum fun i w ↦ Finsupp.single i (v ⊗ₜ w) := by
  simp [finsuppTensorRight, TensorProduct.finsuppRight_apply_tmul]

@[simp]
lemma finsuppTensorRight_apply_tmul_apply {α : Type w'} [DecidableEq α] (v : V) (f : α →₀ W)
    (i : α) : finsuppTensorRight σ ρ α (v ⊗ₜ f) i = v ⊗ₜ f i := by
  simp +contextual [finsuppTensorRight_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]
lemma finsuppTensorRight_symm_apply_single {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W) :
    (finsuppTensorRight σ ρ α).symm (Finsupp.single i (v ⊗ₜ w)) = v ⊗ₜ Finsupp.single i w := by
  simp [finsuppTensorRight]

/-- Equiv between representations induced by linear equiv between `(G →₀ k) ⊗[k] (α →₀ k)` and
  `α →₀ G →₀ k`. -/
def leftRegularTensorTrivialIsoFree (α : Type w') :
    ((leftRegular k G).tprod (trivial k G k[α])).Equiv (free k G α) :=
  .mk (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv _) (MonoidAlgebra.coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ curryLinearEquiv k
      ≪≫ₗ Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv _).symm) fun g ↦ by ext; simp

@[simp]
lemma leftRegularTensorTrivialIsoFree_apply_single_tmul_single {α : Type w'} (g : G) (i : α)
    (r s : k) : leftRegularTensorTrivialIsoFree α (.single g r ⊗ₜ .single i s) =
      .single i (.single g (r * s)) := by
  simp [leftRegularTensorTrivialIsoFree]

@[simp]
lemma leftRegularTensorTrivialIsoFree_symm_apply_single_single {α : Type w'} (i : α) (g : G)
    (r : k) :
    (leftRegularTensorTrivialIsoFree α).symm (.single i (.single g r)) =
      .single g 1 ⊗ₜ .single i r := by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

end finsupp

/-- The linear equiv between the hom module `k[G] ⟶ᵍ V` and `V` itself. -/
@[simps!]
def leftRegularMapEquiv : (leftRegular k G).IntertwiningMap σ ≃ₗ[k] V where
  toFun f := (Finsupp.llift V k k G).symm
    (f.toLinearMap ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap) (1 : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Finsupp.llift _ _ k _ (fun g ↦ σ g v) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv _).toLinearMap, fun g ↦ by ext g'; simp⟩
  left_inv x := by ext; simp [← x.isIntertwining]
  right_inv v := by simp

set_option backward.isDefEq.respectTransparency false in
lemma leftRegularMapEquiv_symm_single (g : G) (v : V) :
    ((leftRegularMapEquiv σ).symm v) (.single g 1) = σ g v := by
  simp

end comm

end

end Representation
