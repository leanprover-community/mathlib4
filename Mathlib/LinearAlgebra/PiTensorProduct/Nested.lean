/-
Copyright (c) 2025 Davood H. H. Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood H.H. Tehrani, David Gross
-/

module

public import Mathlib.LinearAlgebra.PiTensorProduct

/-!

# Nested PiTensorProducts

Let `β : ι → Type*` be a family of types. We related nested tensor products

 `⨂ i, ⨂ b : β i, s i b`

to tensors "with double indices", i.e. those indexed by dependent sums

 `⨂ j : (Σ i, β i), s j.fst j.snd`.

## Main definitions

* `tprodTprodHom` is the natural homomorphism from a nested tensor product to
tensors with double indicies.

* `tprodFiniteTprodEquiv` is an equivalence between the two types, assuming `[Finite ι]`.

-/

open PiTensorProduct
open scoped TensorProduct

@[expose] public section

namespace PiTensorProduct

variable {ι : Type*} {R : Type*}
variable [CommSemiring R]

section tprodTprodHom

variable {β : ι → Type*}
variable {s : (i : ι) → (i : β i) → Type*}
variable [∀ i, ∀ b, AddCommMonoid (s i b)] [∀ i, ∀ b, Module R (s i b)]
variable [DecidableEq ι] [∀ i : ι, DecidableEq (β i)]

/-- The homomorphism sending pure tensors indexed by a sigma type to totally pure
tensors in a nested `PiTensorProduct`. -/
def tprodTprodHom : (⨂[R] j : (Σ k, β k), s j.1 j.2) →ₗ[R] (⨂[R] k, ⨂[R] i, s k i) :=
  lift (MultilinearMap.compMultilinearMap (tprod R) (fun _ ↦ tprod R))

theorem tprodTprodHom_tprod (f : (j : (Σ i, β i)) → s j.1 j.2) :
    tprodTprodHom (⨂ₜ[R] j, f j) = ⨂ₜ[R] i, ⨂ₜ[R] b : β i, f ⟨i, b⟩ := by
  simp only [tprodTprodHom, lift.tprod, MultilinearMap.compMultilinearMap_apply]
  unfold Sigma.curry
  simp

end tprodTprodHom

section TprodFinTrodEquiv

variable {n : Nat} {β : Fin n → Type*}
variable {s : (k : Fin n) → (i : β k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

/-
## RFCs

### Minor `tprod` equivalences

In `tprodFinTprodEquiv`, we combine six equivalences. These requires some care
to unpack in the first `simp` lemma below. Alternatively, one could introduce
these intermediate equivalences

  `(⨂ i : Fin n, s i) ⊗ (⨂ i : Fin m, s i) ≃ₗ[R] ⨂ i : Fin (n + m), s i`
  `(⨂ i : Fin n, s i) ⊗ s i₀ ≃ₗ[R] ⨂ i : Fin (n + 1), s i`

and prove `simp` lemmas for those.

Trade-offs for the alternative approach:
* Pro -- Slightly more transparent proof; More Truths for Mathlib
* Con -- Proliferation of fairly minor equivalences.

What's the preferred way of handling this?

If #2, one could collect equivalences in a PiTensorProduct/Equiv.lean.


### General equivalences

`sigmaFinSuccEquiv` is not particular to `PiTensorProduct`s. Should it go elsewhere?

Logic/Equiv/Fin/Basic.lean?
Logic/Equiv/Basic.lean? (one doesn't currently import any `Fin` files)
-/

/-- Split off last summand of a dependent sum over `Fin n.succ` -/
def sigmaFinSuccEquiv {n : ℕ} {f : Fin n.succ → Type*} :
  (Σ k : Fin n.succ, f k) ≃ (Σ k : Fin n, f k.castSucc) ⊕ f (Fin.last n) := {
    toFun x := if h : x.1 = Fin.last n then .inr (h ▸ x.2) else
      .inl ⟨⟨x.1, Fin.lt_last_iff_ne_last.mpr h⟩, x.2⟩
    invFun := Sum.rec (fun y ↦ ⟨y.1.castSucc, y.2⟩) (⟨Fin.last n, ·⟩)
    left_inv _ := by aesop
    right_inv _ := by aesop
  }

/-- A nested `PiTensorProduct` with outer index of type `Fin n` is equivalent to
a single `PiTensorProduct` over a sigma type. -/
def tprodFinTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, β k), s j.1 j.2) := by
  induction n with
  | zero => exact (isEmptyEquiv _) ≪≫ₗ (isEmptyEquiv _).symm
  | succ m ih => exact
    -- Write index as sum; split off last summand as binary TP:
    (reindex R _ finSumFinEquiv.symm) ≪≫ₗ (tmulEquivDep R _).symm ≪≫ₗ
    -- Use `ih` on lhs; remove outer PiTP on rhs, thereby exposing inner PiTP:
    (TensorProduct.congr ih (subsingletonEquiv ↑0)) ≪≫ₗ
    -- Convert to single PiTP:
    (tmulEquivDep R (fun j ↦ s (sigmaFinSuccEquiv.symm j).1 (sigmaFinSuccEquiv.symm j).2)) ≪≫ₗ
    (reindex R (fun j ↦ s j.fst j.snd) sigmaFinSuccEquiv).symm

open LinearEquiv in
@[simp]
theorem tprodFinTprodEquiv_tprod (f : (k : Fin n) → (i : β k) → s k i) :
    tprodFinTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, β k), f j.1 j.2 := by
  induction n with
  | zero =>
    simp only [tprodFinTprodEquiv, Nat.rec_zero, trans_apply,
      symm_apply_eq, isEmptyEquiv_apply_tprod]
  | succ m ih =>
    simp only [tprodFinTprodEquiv, Equiv.symm_symm, finSumFinEquiv_apply_left, trans_apply]
    -- Strategy: Repeatedly move equivalences around to obtain the form
    -- `(complex terms) = aSingleEquiv tprod`, then simp away `aSingleEquiv`.
    rw [symm_apply_eq, reindex_tprod, ←eq_symm_apply]
    conv_rhs => apply tmulEquivDep_symm_apply
    rw [←eq_symm_apply, ←eq_symm_apply]
    conv_lhs => apply reindex_tprod
    rw [←symm_apply_eq]
    conv_lhs => apply tmulEquivDep_symm_apply
    simp only [eq_symm_apply, finSumFinEquiv_apply_left,
      TensorProduct.congr_tmul, subsingletonEquiv_apply_tprod]
    --
    exact (congr_arg (· ⊗ₜ[R] (⨂ₜ[R] i : β (Fin.last m), f (Fin.last m) i))
      (ih (fun k i ↦ f k.castSucc i)))

@[simp]
theorem tprodFinTprodEquiv_symm_tprod (f : (j : (Σ k, β k)) → s j.1 j.2) :
    tprodFinTprodEquiv.symm (⨂ₜ[R] j : (Σ k, β k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, Sigma.curry f k i) :=
  by simp [LinearEquiv.symm_apply_eq, Sigma.curry]

end TprodFinTrodEquiv

section tprodFiniteTprodEquiv

variable {ι : Type*} [Finite ι]
variable {β : ι → Type*} {s : (k : ι) → (i : β k) → Type*}
variable [∀ k, ∀ i, AddCommMonoid (s k i)] [∀ k, ∀ i, Module R (s k i)]

/-- A nested `PiTensorProduct` with finite outer index type is equivalent to
a single `PiTensorProduct` over a sigma type. -/
noncomputable def tprodFiniteTprodEquiv :
    (⨂[R] k, ⨂[R] i, s k i) ≃ₗ[R] (⨂[R] j : (Σ k, β k), s j.1 j.2) :=
  let e := Classical.choice (Finite.exists_equiv_fin ι).choose_spec
  let f := (Equiv.sigmaCongrLeft e.symm).symm
  reindex R _ e ≪≫ₗ tprodFinTprodEquiv ≪≫ₗ (reindex R (fun i ↦ s i.fst i.snd) f).symm

@[simp]
theorem tprodFiniteTprodEquiv_tprod (f : (k : ι) → (i : β k) → s k i) :
    tprodFiniteTprodEquiv (⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⨂ₜ[R] j : (Σ k, β k), f j.fst j.snd := by
  simp only [tprodFiniteTprodEquiv, Equiv.symm_symm, LinearEquiv.trans_apply,
    reindex_tprod, Equiv.sigmaCongrLeft_apply, tprodFinTprodEquiv_tprod, LinearEquiv.symm_apply_eq]
  conv_rhs => apply reindex_tprod
  simp

@[simp]
theorem tprodFiniteTprodEquiv_symm_tprod (f : (j : (Σ k, β k)) → s j.1 j.2) :
    tprodFiniteTprodEquiv.symm (⨂ₜ[R] j : (Σ k, β k), f j) = (⨂ₜ[R] k, ⨂ₜ[R] i, f ⟨k, i⟩) := by
  simp [LinearEquiv.symm_apply_eq]

/-- The totally pure tensors (i.e. products of product tensors) span a nested tensor
product, if the outer index type is finite. -/
theorem span_tprodFiniteTprod_eq_top :
    Submodule.span R
      (Set.range fun f : (k : ι) → (i : β k) → s k i ↦ ⨂ₜ[R] k, ⨂ₜ[R] i, f k i) = ⊤ := by
  rw [eq_top_iff, ←tprodFiniteTprodEquiv.symm.range, LinearMap.range_eq_map,
    ←span_tprod_eq_top, ←Submodule.span_image, LinearEquiv.coe_coe]
  gcongr
  intro f
  simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and, tprodFiniteTprodEquiv_symm_tprod]
  intro ⟨y, hy⟩
  use (fun j k ↦ y ⟨j, k⟩)

end tprodFiniteTprodEquiv

end PiTensorProduct
