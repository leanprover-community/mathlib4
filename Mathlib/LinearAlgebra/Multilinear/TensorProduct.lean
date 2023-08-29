/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.TensorProduct

#align_import linear_algebra.multilinear.tensor_product from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

/-!
# Constructions relating multilinear maps and tensor products.
-/


namespace MultilinearMap

section DomCoprod

open TensorProduct

variable {R ι₁ ι₂ ι₃ ι₄ : Type*}

variable [CommSemiring R]

variable {N₁ : Type*} [AddCommMonoid N₁] [Module R N₁]

variable {N₂ : Type*} [AddCommMonoid N₂] [Module R N₂]

variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- Given two multilinear maps `(ι₁ → N) → N₁` and `(ι₂ → N) → N₂`, this produces the map
`(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂` by taking the coproduct of the domain and the tensor product
of the codomain.

This can be thought of as combining `Equiv.sumArrowEquivProdArrow.symm` with
`TensorProduct.map`, noting that the two operations can't be separated as the intermediate result
is not a `MultilinearMap`.

While this can be generalized to work for dependent `Π i : ι₁, N'₁ i` instead of `ι₁ → N`, doing so
introduces `Sum.elim N'₁ N'₂` types in the result which are difficult to work with and not defeq
to the simple case defined here. See [this zulip thread](
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/Instances.20on.20.60sum.2Eelim.20A.20B.20i.60/near/218484619).
-/
@[simps apply]
def domCoprod (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) :
    MultilinearMap R (fun _ : Sum ι₁ ι₂ => N) (N₁ ⊗[R] N₂) where
  toFun v := (a fun i => v (Sum.inl i)) ⊗ₜ b fun i => v (Sum.inr i)
  map_add' _ i p q := by
    letI := (@Sum.inl_injective ι₁ ι₂).decidableEq
    -- ⊢ (fun v => (↑a fun i => v (Sum.inl i)) ⊗ₜ[R] ↑b fun i => v (Sum.inr i)) (Func …
    letI := (@Sum.inr_injective ι₁ ι₂).decidableEq
    -- ⊢ (fun v => (↑a fun i => v (Sum.inl i)) ⊗ₜ[R] ↑b fun i => v (Sum.inr i)) (Func …
    cases i <;> simp [TensorProduct.add_tmul, TensorProduct.tmul_add]
    -- ⊢ (fun v => (↑a fun i => v (Sum.inl i)) ⊗ₜ[R] ↑b fun i => v (Sum.inr i)) (Func …
                -- 🎉 no goals
                -- 🎉 no goals
  map_smul' _ i c p := by
    letI := (@Sum.inl_injective ι₁ ι₂).decidableEq
    -- ⊢ (fun v => (↑a fun i => v (Sum.inl i)) ⊗ₜ[R] ↑b fun i => v (Sum.inr i)) (Func …
    letI := (@Sum.inr_injective ι₁ ι₂).decidableEq
    -- ⊢ (fun v => (↑a fun i => v (Sum.inl i)) ⊗ₜ[R] ↑b fun i => v (Sum.inr i)) (Func …
    cases i <;> simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    -- ⊢ (fun v => (↑a fun i => v (Sum.inl i)) ⊗ₜ[R] ↑b fun i => v (Sum.inr i)) (Func …
                -- 🎉 no goals
                -- 🎉 no goals
#align multilinear_map.dom_coprod MultilinearMap.domCoprod

/-- A more bundled version of `MultilinearMap.domCoprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def domCoprod' :
    MultilinearMap R (fun _ : ι₁ => N) N₁ ⊗[R] MultilinearMap R (fun _ : ι₂ => N) N₂ →ₗ[R]
      MultilinearMap R (fun _ : Sum ι₁ ι₂ => N) (N₁ ⊗[R] N₂) :=
  TensorProduct.lift <|
    LinearMap.mk₂ R domCoprod
      (fun m₁ m₂ n => by
        ext
        -- ⊢ ↑(domCoprod (m₁ + m₂) n) x✝ = ↑(domCoprod m₁ n + domCoprod m₂ n) x✝
        simp only [domCoprod_apply, TensorProduct.add_tmul, add_apply])
        -- 🎉 no goals
      (fun c m n => by
        ext
        -- ⊢ ↑(domCoprod (c • m) n) x✝ = ↑(c • domCoprod m n) x✝
        simp only [domCoprod_apply, TensorProduct.smul_tmul', smul_apply])
        -- 🎉 no goals
      (fun m n₁ n₂ => by
        ext
        -- ⊢ ↑(domCoprod m (n₁ + n₂)) x✝ = ↑(domCoprod m n₁ + domCoprod m n₂) x✝
        simp only [domCoprod_apply, TensorProduct.tmul_add, add_apply])
        -- 🎉 no goals
      fun c m n => by
      ext
      -- ⊢ ↑(domCoprod m (c • n)) x✝ = ↑(c • domCoprod m n) x✝
      simp only [domCoprod_apply, TensorProduct.tmul_smul, smul_apply]
      -- 🎉 no goals
#align multilinear_map.dom_coprod' MultilinearMap.domCoprod'

@[simp]
theorem domCoprod'_apply (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) : domCoprod' (a ⊗ₜ[R] b) = domCoprod a b :=
  rfl
#align multilinear_map.dom_coprod'_apply MultilinearMap.domCoprod'_apply

/-- When passed an `Equiv.sumCongr`, `MultilinearMap.domDomCongr` distributes over
`MultilinearMap.domCoprod`. -/
theorem domCoprod_domDomCongr_sumCongr (a : MultilinearMap R (fun _ : ι₁ => N) N₁)
    (b : MultilinearMap R (fun _ : ι₂ => N) N₂) (σa : ι₁ ≃ ι₃) (σb : ι₂ ≃ ι₄) :
    (a.domCoprod b).domDomCongr (σa.sumCongr σb) =
      (a.domDomCongr σa).domCoprod (b.domDomCongr σb) :=
  rfl
#align multilinear_map.dom_coprod_dom_dom_congr_sum_congr MultilinearMap.domCoprod_domDomCongr_sumCongr

end DomCoprod

end MultilinearMap
