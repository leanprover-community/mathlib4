/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.TensorProduct

/-!
# Exterior product of alternating maps

In this file we define `AlternatingMap.domCoprod`
to be the exterior product of two alternating maps,
taking values in the tensor product of the codomains of the original maps.
-/

open TensorProduct

variable {ιa ιb : Type*} [Fintype ιa] [Fintype ιb]
variable {R' : Type*} {Mᵢ N₁ N₂ : Type*} [CommSemiring R'] [AddCommGroup N₁] [Module R' N₁]
  [AddCommGroup N₂] [Module R' N₂] [AddCommMonoid Mᵢ] [Module R' Mᵢ]

namespace Equiv.Perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β -/
abbrev ModSumCongr (α β : Type*) :=
  _ ⧸ (Equiv.Perm.sumCongrHom α β).range

end Equiv.Perm

namespace AlternatingMap

open Equiv

variable [DecidableEq ιa] [DecidableEq ιb]

/-- summand used in `AlternatingMap.domCoprod` -/
def domCoprod.summand (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)
    (σ : Perm.ModSumCongr ιa ιb) : MultilinearMap R' (fun _ : ιa ⊕ ιb => Mᵢ) (N₁ ⊗[R'] N₂) :=
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
      TensorProduct.smul_tmul', a.map_congr_perm _ sl, b.map_congr_perm _ sr]
    simp only [Sum.map_inr, Perm.sumCongrHom_apply, Perm.sumCongr_apply, Sum.map_inl,
      Function.comp_def, Perm.coe_mul]

theorem domCoprod.summand_mk'' (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂)
    (σ : Equiv.Perm (ιa ⊕ ιb)) :
    domCoprod.summand a b (Quotient.mk'' σ) =
      Equiv.Perm.sign σ •
        (MultilinearMap.domCoprod ↑a ↑b : MultilinearMap R' (fun _ => Mᵢ) (N₁ ⊗ N₂)).domDomCongr
          σ :=
  rfl

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
theorem domCoprod.summand_add_swap_smul_eq_zero (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ}
    {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
    domCoprod.summand a b σ v + domCoprod.summand a b (swap i j • σ) v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MulAction.Quotient.smul_mk,
    domCoprod.summand]
  rw [smul_eq_mul, Perm.sign_mul, Perm.sign_swap hij]
  simp only [one_mul, neg_mul, Function.comp_apply, Units.neg_smul, Perm.coe_mul,
    MultilinearMap.smul_apply, MultilinearMap.neg_apply, MultilinearMap.domDomCongr_apply,
    MultilinearMap.domCoprod_apply]
  convert add_neg_cancel (G := N₁ ⊗[R'] N₂) _ using 6 <;>
    · ext k
      rw [Equiv.apply_swap_eq_self hv]

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
theorem domCoprod.summand_eq_zero_of_smul_invariant (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁)
    (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) (σ : Perm.ModSumCongr ιa ιb) {v : ιa ⊕ ιb → Mᵢ}
    {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
    swap i j • σ = σ → domCoprod.summand a b σ v = 0 := by
  refine Quotient.inductionOn' σ fun σ => ?_
  dsimp only [Quotient.liftOn'_mk'', Quotient.map'_mk'', MultilinearMap.smul_apply,
    MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, domCoprod.summand]
  intro hσ
  obtain ⟨⟨sl, sr⟩, hσ⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact' hσ)
  rcases hi : σ⁻¹ i with i' | i' <;> rcases hj : σ⁻¹ j with j' | j' <;>
    rw [Perm.inv_eq_iff_eq] at hi hj <;> substs hi hj
  -- the term pairs with and cancels another term
  case inl.inr => simpa using Equiv.congr_fun hσ (Sum.inl i')
  case inr.inl => simpa using Equiv.congr_fun hσ (Sum.inr i')
  -- the term does not pair but is zero
  case inl.inl =>
    suffices (a fun i ↦ v (σ (Sum.inl i))) = 0 by simp_all
    exact AlternatingMap.map_eq_zero_of_eq _ _ hv fun hij' => hij (hij' ▸ rfl)
  case inr.inr =>
    suffices (b fun i ↦ v (σ (Sum.inr i))) = 0 by simp_all
    exact b.map_eq_zero_of_eq _ hv fun hij' => hij (hij' ▸ rfl)

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
      rw [MultilinearMap.sum_apply]
      exact
        Finset.sum_involution (fun σ _ => Equiv.swap i j • σ)
          (fun σ _ => domCoprod.summand_add_swap_smul_eq_zero a b σ hv hij)
          (fun σ _ => mt <| domCoprod.summand_eq_zero_of_smul_invariant a b σ hv hij)
          (fun σ _ => Finset.mem_univ _) fun σ _ =>
          Equiv.swap_smul_involutive i j σ }

theorem domCoprod_coe (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    (↑(a.domCoprod b) : MultilinearMap R' (fun _ => Mᵢ) _) =
      ∑ σ : Perm.ModSumCongr ιa ιb, domCoprod.summand a b σ :=
  MultilinearMap.ext fun _ => rfl

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

@[simp]
theorem domCoprod'_apply (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    domCoprod' (a ⊗ₜ[R'] b) = domCoprod a b :=
  rfl

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

open AlternatingMap

open Perm in
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
  induction σ using Quotient.inductionOn' with
  | h σ =>
  set f := sumCongrHom ιa ιb
  calc
    ∑ τ ∈ _, sign τ • domDomCongr τ (a.domCoprod b) =
        ∑ τ ∈ {τ | τ⁻¹ * σ ∈ f.range}, sign τ • domDomCongr τ (a.domCoprod b) := by
      simp [QuotientGroup.leftRel_apply, f]
    _ = ∑ τ ∈ {τ | τ⁻¹ ∈ f.range}, sign (σ * τ) • domDomCongr (σ * τ) (a.domCoprod b) := by
      conv_lhs => rw [← Finset.map_univ_equiv (Equiv.mulLeft σ), Finset.filter_map, Finset.sum_map]
      simp [Function.comp_def, -MonoidHom.mem_range]
    _ = ∑ τ, sign (σ * f τ) • domDomCongr (σ * f τ) (a.domCoprod b) := by
      simp_rw [f, Subgroup.inv_mem_iff, MonoidHom.mem_range, Finset.univ_filter_exists,
        Finset.sum_image sumCongrHom_injective.injOn]
    _ = ∑ τ : Perm ιa × Perm ιb,
         sign σ • (domDomCongrEquiv σ) (sign τ.1 • sign τ.2 •
           (domDomCongr τ.1 a).domCoprod (domDomCongr τ.2 b)) := by
      simp [f, domDomCongr_mul, domCoprod_domDomCongr_sumCongr, mul_smul]
    _ = domCoprod.summand (alternatization a) (alternatization b) (Quotient.mk'' σ) := by
      simp [domCoprod.summand_mk'', domCoprod_alternization_coe, ← domDomCongrEquiv_apply,
        Finset.smul_sum, ← Finset.sum_product']

/-- Taking the `MultilinearMap.alternatization` of the `MultilinearMap.domCoprod` of two
`AlternatingMap`s gives a scaled version of the `AlternatingMap.coprod` of those maps.
-/
theorem MultilinearMap.domCoprod_alternization_eq [DecidableEq ιa] [DecidableEq ιb]
    (a : Mᵢ [⋀^ιa]→ₗ[R'] N₁) (b : Mᵢ [⋀^ιb]→ₗ[R'] N₂) :
    MultilinearMap.alternatization
      (MultilinearMap.domCoprod a b : MultilinearMap R' (fun _ : ιa ⊕ ιb => Mᵢ) (N₁ ⊗ N₂)) =
      ((Fintype.card ιa).factorial * (Fintype.card ιb).factorial) • a.domCoprod b := by
  rw [MultilinearMap.domCoprod_alternization, coe_alternatization, coe_alternatization, mul_smul,
    ← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply,
    ← TensorProduct.smul_tmul', TensorProduct.tmul_smul,
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod',
    LinearMap.map_smul_of_tower AlternatingMap.domCoprod']
