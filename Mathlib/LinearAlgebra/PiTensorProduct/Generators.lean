/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Data.SubtypeNeLift
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map

import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Generators of multiple tensor products

Given a finite family of `R`-modules `M i`, if we have, for each `i`,
a family of generators of the module `M i`, then the tensor products
of these elements generate `⨂[R] i, M i`.

In `LinearAlgebra.PiTensorProduct.Finite`, we deduce that if the modules `M i`
are finitely generated, then so is `⨂[R] i, M i`.

-/

@[expose] public section

open TensorProduct

namespace PiTensorProduct

variable (R : Type*)

section equivPiTensorComplSingletonTensor

variable {ι : Type*} [DecidableEq ι] (M : ι → Type*)
  [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- The linear equivalence between `⨂[R] i, M i` and the tensor product of
the pi tensor product indexed by the complement of `{i₀}` and `M i₀`. -/
noncomputable def equivPiTensorComplSingletonTensor (i₀ : ι) :
    (⨂[R] i, M i) ≃ₗ[R] ((⨂[R] (i : ({i₀}ᶜ : Set ι)), M i) ⊗[R] M i₀) :=
  (reindex R (s := M) (Equiv.subtypeNeSumPUnit.{0} i₀).symm).trans
    ((tmulEquivDep R (fun i ↦ M (Equiv.subtypeNeSumPUnit i₀ i))).symm.trans
      (LinearEquiv.lTensor _ (subsingletonEquiv Unit.unit)))

variable (i₀ : ι)

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/14624:

We had to use the `instanceSearchTypes` backward compatibility flag to make an instance search
succeed. Concretely, the following instance cannot be synthesized:
`AddCommMonoid (⨂[R] (i₁ : { i // ¬i = i₀ }), M ↑i₁)`
The companion searches `Module R (⨂[R] (i₁ : { i // ¬i = i₀ }), M ↑i₁)` and the two `PUnit`-indexed
variants fail in the same way. They are needed by the `rw [dsimp% …]` below, after `Equiv.symm_symm`
has rewritten the index type to `{ i // ¬i = i₀ }` while the instance arguments in the term stay
phrased through the equivalence.

The failure happens while applying `@PiTensorProduct.instAddCommMonoid`: assigning one of its
instance-implicit-argument metavariables is rejected because the metavariable's type and the type of
the assigned value do not match at `.instances` transparency. The metavariable's expected type is
`(i : { i // ¬i = i₀ }) → AddCommMonoid (M ↑i)`, whereas the assigned value
`fun i ↦ inst✝ ((Equiv.subtypeNeSumPUnit i₀) (Sum.inl i))` has type
`(i : { i // i ≠ i₀ }) → AddCommMonoid (M ((Equiv.subtypeNeSumPUnit i₀) (Sum.inl i)))`. The
comparison bottoms out at `i.1 =?= (Equiv.subtypeNeSumPUnit i₀).1 (Sum.inl i)`, i.e. at actually
computing the equivalence on `Sum.inl i`. Lean falls back to synthesize an instance of the correct
type, which succeeds, but it returns `fun i ↦ inst✝ ↑i`, which is again not defeq to the assigned
value, for the same reason. The `respectTransparency false` backward-compatibility flag blocks Lean
from bumping to implicit, so the comparison happens at `.instances` again.

Validated, but perhaps too invasive, fix: Make all of the following definitions implicit-reducible:

```
  Equiv.trans
  Equiv.optionSubtype
  Equiv.optionEquivSumPUnit
  Equiv.refl
  Set.singleton
  Option.casesOn'
  Equiv.optionSubtypeNe
  Sum.elim
```

Then both backward compatibility options can go: first `respectTransparency false`, then
`instanceSearchTypes false`.
-/
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma equivPiTensorComplSingletonTensor_tprod (i₀ : ι) (m : ∀ i, M i) :
    equivPiTensorComplSingletonTensor R M i₀ (⨂ₜ[R] i, m i) =
      (⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) ⊗ₜ m i₀:= by
  dsimp [equivPiTensorComplSingletonTensor]
  have : (reindex R M (Equiv.subtypeNeSumPUnit.{0} i₀).symm) (⨂ₜ[R] (i : ι), m i) =
      ⨂ₜ[R] j, m ((Equiv.subtypeNeSumPUnit.{0} i₀) j) := by
    simp_rw [reindex_tprod (R := R) (s := M), Equiv.symm_symm]
  rw [dsimp% this, dsimp% tmulEquivDep_symm_apply R
    (fun i ↦ M ((Equiv.subtypeNeSumPUnit.{0} i₀) i))]
  exact (LinearEquiv.lTensor_tmul _ _ _ _).trans (by congr; simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
lemma equivPiTensorComplSingletonTensor_symm_tmul (i₀ : ι)
    (m : ∀ (i : ((Set.singleton i₀)ᶜ : Set ι)), M i) (x : M i₀) :
    (equivPiTensorComplSingletonTensor R M i₀).symm
      ((⨂ₜ[R] (j : ((Set.singleton i₀)ᶜ : Set ι)), m j) ⊗ₜ x) =
    (⨂ₜ[R] i, Function.subtypeNeLift i₀ m x i) := by
  apply (equivPiTensorComplSingletonTensor R M i₀).injective
  simp only [LinearEquiv.apply_symm_apply, equivPiTensorComplSingletonTensor_tprod,
    Function.subtypeNeLift_self]
  congr
  ext ⟨i, hi⟩
  rw [Function.subtypeNeLift_of_neq _ _ _ _ hi]
  rfl

end equivPiTensorComplSingletonTensor

variable {R} {ι : Type*} [Finite ι] {M : ι → Type*} {N : Type*} {γ : ι → Type*}

section AddCommMonoid

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module R N] {g : ⦃i : ι⦄ → (j : γ i) → M i}

lemma submodule_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤) :
    Submodule.span R (Set.range (fun j : ((i : ι) → γ i) ↦
      ⨂ₜ[R] (i : ι), g (j i))) = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  simp_rw [eq_top_iff, ← span_tprod_eq_top, Submodule.span_le, Set.subset_def, SetLike.mem_coe]
  simp_rw [Submodule.eq_top_iff', Finsupp.mem_span_range_iff_exists_finsupp] at hg
  rintro _ ⟨m, rfl⟩
  choose c hc using fun i ↦ hg i (m i)
  simp_rw [← funext hc, Finsupp.sum, MultilinearMap.map_sum_finset, MultilinearMap.map_smul_univ]
  exact sum_mem fun r _ ↦ Submodule.smul_mem _ _ (Submodule.mem_span_of_mem (Set.mem_range_self r))

lemma ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : (⨂[R] i, M i) →ₗ[R] N}
    (h : ∀ (j : (i : ι) → γ i),
      φ (tprod R (fun i ↦ g (j i))) = φ' (tprod R (fun i ↦ g (j i)))) :
    φ = φ' :=
  LinearMap.ext_on_range (submodule_span_eq_top hg) h

lemma _root_.MultilinearMap.ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : MultilinearMap R M N}
    (h : ∀ (j : (i : ι) → γ i), φ (fun i ↦ g (j i)) = φ' (fun i ↦ g (j i))) :
    φ = φ' := by
  suffices lift φ = lift φ' by
    ext m
    simpa using congr($this (tprod _ m))
  exact PiTensorProduct.ext_of_span_eq_top hg (fun j ↦ by simpa using h j)

end AddCommMonoid

end PiTensorProduct
