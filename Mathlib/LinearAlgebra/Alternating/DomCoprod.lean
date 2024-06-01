/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.TensorProduct
import Mathlib.GroupTheory.GroupAction.Quotient
/-!
# Exterior product of alternating maps

In this file we define `AlternatingMap.domCoprod`
to be the exterior product of two alternating maps,
taking values in the tensor product of the codomains of the original maps.
-/

#align_import linear_algebra.alternating from "leanprover-community/mathlib"@"0c1d80f5a86b36c1db32e021e8d19ae7809d5b79"

suppress_compilation

open TensorProduct

variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]
variable {R' : Type*} {Mᵢ N₁ N₂ : Type*} [CommSemiring R'] [AddCommGroup N₁] [Module R' N₁]
  [AddCommGroup N₂] [Module R' N₂] [AddCommMonoid Mᵢ] [Module R' Mᵢ]

namespace Equiv.Perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β  -/
abbrev ModSumCongr (α β : Type*) :=
  _ ⧸ (Equiv.Perm.sumCongrHom α β).range
#align equiv.perm.mod_sum_congr Equiv.Perm.ModSumCongr

#align equiv.perm.mod_sum_congr.swap_smul_involutive Equiv.swap_smul_involutive

end Equiv.Perm

namespace AlternatingMap

open Equiv

variable [DecidableEq ιa] [DecidableEq ιb]

/-- summand used in `AlternatingMap.domCoprod` -/
def domCoprod.summand (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)
    (σ : Perm.ModSumCongr ιa ιb) : MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗[R'] N₂) :=
  Quotient.liftOn' σ
    (fun σ =>
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr σ)
    fun σ₁ σ₂ H => by
    rw [QuotientGroup.leftRel_apply] at H
    obtain ⟨⟨sl, sr⟩, h⟩ := H
    ext v
    simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
      coe_multilinearMap, MultilinearMap.smul_apply]
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm
    have : Equiv.Perm.sign (σ₁ * Perm.sumCongrHom _ _ (sl, sr))
      = Equiv.Perm.sign σ₁ * (Equiv.Perm.sign sl * Equiv.Perm.sign sr) := by simp
    rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff, ← TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    simp only [Sum.map_inr, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl,
      Function.comp_apply, Perm.coe_mul]
    -- Porting note (#10691): was `rw`.
    erw [← a.map_congr_perm fun i => v (σ₁ _), ← b.map_congr_perm fun i => v (σ₁ _)]
#align alternating_map.dom_coprod.summand AlternatingMap.domCoprod.summand

theorem domCoprod.summand_mk'' (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)
    (σ : Equiv.Perm (Sum ιa ιb)) :
    domCoprod.summand a b (Quotient.mk'' σ) =
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr
          σ :=
  rfl
#align alternating_map.dom_coprod.summand_mk' AlternatingMap.domCoprod.summand_mk''

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
theorem domCoprod.summand_add_swap_smul_eq_zero (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ}
    {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    domCoprod.summand a b σ v + domCoprod.summand a b (swap i j • σ) v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul, Perm.sign_mul, Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul, Units.val_neg,
    MultilinearMap.smul_apply, MultilinearMap.neg_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply]
  convert add_right_neg (G := N₁ ⊗[R'] N₂) _ using 6 <;>
    · ext k
      rw [Equiv.apply_swap_eq_self hv]
#align alternating_map.dom_coprod.summand_add_swap_smul_eq_zero AlternatingMap.domCoprod.summand_add_swap_smul_eq_zero

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
theorem domCoprod.summand_eq_zero_of_smul_invariant (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : Sum ιa ιb → Mᵢ}
    {i j : Sum ιa ιb} (hv : v i = v j) (hij : i ≠ j) :
    swap i j • σ = σ → domCoprod.summand a b σ v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MultilinearMap.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  cases' hi : σ⁻¹ i with val val <;> cases' hj : σ⁻¹ j with val_1 val_1 <;>
    rw [Perm.inv_eq_iff_eq] at hi hj <;> substs hi hj <;> revert val val_1
  -- Porting note: `on_goal` is not available in `case _ | _ =>`, so the proof gets tedious.
  -- the term pairs with and cancels another term
  case inl.inr =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inl i')
    dsimp only at hσ
    rw [smul_eq_mul, ← mul_swap_eq_swap_mul, mul_inv_rev, swap_inv, inv_mul_cancel_right] at hσ
    simp at hσ
  case inr.inl =>
    intro i' j' _ _ hσ
    obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
    replace hσ := Equiv.congr_fun hσ (Sum.inr i')
    dsimp only at hσ
    rw [smul_eq_mul, ← mul_swap_eq_swap_mul, mul_inv_rev, swap_inv, inv_mul_cancel_right] at hσ
    simp at hσ
  -- the term does not pair but is zero
  case inr.inr =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := N₁ ⊗[R'] N₂) _
    convert TensorProduct.tmul_zero (R := R') (M := N₁) N₂ _
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inl.inl =>
    intro i' j' hv hij _
    convert smul_zero (M := ℤˣ) (A := N₁ ⊗[R'] N₂) _
    convert TensorProduct.zero_tmul (R := R') N₁ (N := N₂) _
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
#align alternating_map.dom_coprod.summand_eq_zero_of_smul_invariant AlternatingMap.domCoprod.summand_eq_zero_of_smul_invariant

/-- Like `MultilinearMap.domCoprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = Fin n` and `ιb = Fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `Sum`

The specialized version can be obtained by combining this definition with `finSumFinEquiv` and
`LinearMap.mul'`.
-/
@[simps]
def domCoprod (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    Mᵢ [⋀^ιa ⊕ ιb]→ₗ[R'] (N₁ ⊗[R'] N₂) :=
  { ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ with
    toFun := fun v => (⇑(∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ)) v
    map_eq_zero_of_eq' := fun v i j hv hij => by
      dsimp only
      rw [MultilinearMap.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => domCoprod.summand_add_swap_smul_eq_zero a b σ hv hij)
          (fun σ _ => mt <| domCoprod.summand_eq_zero_of_smul_invariant a b σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }
#align alternating_map.dom_coprod AlternatingMap.domCoprod
#align alternating_map.dom_coprod_apply AlternatingMap.domCoprod_apply

theorem domCoprod_coe (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) =
      ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ :=
  MultilinearMap.ext fun _ => rfl
#align alternating_map.dom_coprod_coe AlternatingMap.domCoprod_coe

/-- A more bundled version of `AlternatingMap.domCoprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def domCoprod' :
    (Mᵢ [⋀^ιa]→ₗ[R'] N₁) ⊗[R'] (Mᵢ [⋀^ιb]→ₗ[R'] N₂) →ₗ[R']
      (Mᵢ [⋀^ιa ⊕ ιb]→ₗ[R'] (N₁ ⊗[R'] N₂)) :=
  TensorProduct.lift <| by
    refine
      LinearMap.mk₂ R' domCoprod (fun m₁ m₂ n => ?_) (fun c m n => ?_) (fun m n₁ n₂ => ?_)
        fun c m n => ?_ <;>
    · ext
      simp only [domCoprod_apply, add_apply, smul_apply, ← Finset.sum_add_distrib,
        Finset.smul_sum, MultilinearMap.sum_apply, domCoprod.summand]
      congr
      ext σ
      refine Quotient.inductionOn' σ fun σ => ?_
      simp only [Quotient.liftOn'_mk'', coe_add, coe_smul, MultilinearMap.smul_apply,
        ← MultilinearMap.domCoprod'_apply]
      simp only [TensorProduct.add_tmul, ← TensorProduct.smul_tmul', TensorProduct.tmul_add,
        TensorProduct.tmul_smul, LinearMap.map_add, LinearMap.map_smul]
      first | rw [← smul_add] | rw [smul_comm]
      rfl
#align alternating_map.dom_coprod' AlternatingMap.domCoprod'

@[simp]
theorem domCoprod'_apply (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    domCoprod' (a ⊗ₜ[R'] b) = domCoprod a b :=
  rfl
#align alternating_map.dom_coprod'_apply AlternatingMap.domCoprod'_apply

end AlternatingMap

open Equiv

/-- A helper lemma for `MultilinearMap.domCoprod_alternization`. -/
theorem MultilinearMap.domCoprod_alternization_coe [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.domCoprod (MultilinearMap.alternatization a)
      (MultilinearMap.alternatization b) =
      ∑ σa : Perm ιa, ∑ σb : Perm ιb,
        Equiv.Perm.sign σa • Equiv.Perm.sign σb •
          MultilinearMap.domCoprod (a.domDomCongr σa) (b.domDomCongr σb) := by
  simp_rw [← MultilinearMap.domCoprod'_apply, MultilinearMap.alternatization_coe]
  simp_rw [TensorProduct.sum_tmul, TensorProduct.tmul_sum, _root_.map_sum,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  rfl
#align multilinear_map.dom_coprod_alternization_coe MultilinearMap.domCoprod_alternization_coe

open AlternatingMap

/-- Computing the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` is the same
as computing the `AlternatingMap.domCoprod` of the `MultilinearMap.alternatization`s.
-/
theorem MultilinearMap.domCoprod_alternization [DecidableEq ιa] [DecidableEq ιb]
    (a : MultilinearMap R' (fun _ : ιa => Mᵢ) N₁) (b : MultilinearMap R' (fun _ : ιb => Mᵢ) N₂) :
    MultilinearMap.alternatization (MultilinearMap.domCoprod a b) =
      a.alternatization.domCoprod (MultilinearMap.alternatization b) := by
  apply coe_multilinearMap_injective
  rw [domCoprod_coe, MultilinearMap.alternatization_coe,
    Finset.sum_partition (QuotientGroup.leftRel (Perm.sumCongrHom ιa ιb).range)]
  congr 1
  ext1 σ
  refine Quotient.inductionOn' σ fun σ => ?_
  -- unfold the quotient mess left by `Finset.sum_partition`
  -- Porting note: Was `conv in .. => ..`.
  erw
    [@Finset.filter_congr _ _ (fun a => @Quotient.decidableEq _ _
      (QuotientGroup.leftRelDecidable (MonoidHom.range (Perm.sumCongrHom ιa ιb)))
      (Quotient.mk (QuotientGroup.leftRel (MonoidHom.range (Perm.sumCongrHom ιa ιb))) a)
      (Quotient.mk'' σ)) _ (s := Finset.univ)
    fun x _ => QuotientGroup.eq' (s := MonoidHom.range (Perm.sumCongrHom ιa ιb)) (a := x) (b := σ)]
  -- eliminate a multiplication
  rw [← Finset.map_univ_equiv (Equiv.mulLeft σ), Finset.filter_map, Finset.sum_map]
  simp_rw [Equiv.coe_toEmbedding, Equiv.coe_mulLeft, (· ∘ ·), mul_inv_rev, inv_mul_cancel_right,
    Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
    Finset.sum_image (Perm.sumCongrHom_injective.injOn _)]
  -- now we're ready to clean up the RHS, pulling out the summation
  rw [domCoprod.summand_mk'', MultilinearMap.domCoprod_alternization_coe, ← Finset.sum_product',
    Finset.univ_product_univ, ← MultilinearMap.domDomCongrEquiv_apply, _root_.map_sum,
    Finset.smul_sum]
  congr 1
  ext1 ⟨al, ar⟩
  dsimp only
  -- pull out the pair of smuls on the RHS, by rewriting to `_ →ₗ[ℤ] _` and back
  rw [← AddEquiv.coe_toAddMonoidHom, ← AddMonoidHom.coe_toIntLinearMap, LinearMap.map_smul_of_tower,
    LinearMap.map_smul_of_tower, AddMonoidHom.coe_toIntLinearMap, AddEquiv.coe_toAddMonoidHom,
    MultilinearMap.domDomCongrEquiv_apply]
  -- pick up the pieces
  rw [MultilinearMap.domDomCongr_mul, Perm.sign_mul, Perm.sumCongrHom_apply,
    MultilinearMap.domCoprod_domDomCongr_sumCongr, Perm.sign_sumCongr, mul_smul, mul_smul]
#align multilinear_map.dom_coprod_alternization MultilinearMap.domCoprod_alternization

/-- Taking the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` of two
`AlternatingMap`s gives a scaled version of the `AlternatingMap.coprod` of those maps.
-/
theorem MultilinearMap.domCoprod_alternization_eq [DecidableEq ιa] [DecidableEq ιb]
    (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    MultilinearMap.alternatization
      (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : Sum ιa ιb => Mᵢ) (N₁ ⊗ N₂)) =
      ((Fintype.card ιa).factorial * (Fintype.card ιb).factorial) • a.domCoprod b := by
  rw [MultilinearMap.domCoprod_alternization, coe_alternatization, coe_alternatization, mul_smul,
    ← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod',
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod']
#align multilinear_map.dom_coprod_alternization_eq MultilinearMap.domCoprod_alternization_eq
