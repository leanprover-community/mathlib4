/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-! # Pointwise instances on `Submodule`s

This file provides:

* `Submodule.pointwiseNeg`

and the actions

* `Submodule.pointwiseDistribMulAction`
* `Submodule.pointwiseMulActionWithZero`

which matches the action of `Set.mulActionSet`.

This file also provides:
* `Submodule.pointwiseSetSMulSubmodule`: for `R`-module `M`, a `s : Set R` can act on
  `N : Submodule R M` by defining `s • N` to be the smallest submodule containing all `a • n`
  where `a ∈ s` and `n ∈ N`.

These actions are available in the `Pointwise` locale.

## Implementation notes

For an `R`-module `M`, the action of a subset of `R` acting on a submodule of `M` introduced in
section `set_acting_on_submodules` does not have a counterpart in the files
`Mathlib/Algebra/Group/Submonoid/Pointwise.lean` and
`Mathlib/Algebra/GroupWithZero/Submonoid/Pointwise.lean`.

Other than section `set_acting_on_submodules`, most of the lemmas in this file are direct copies of
lemmas from the file `Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.
-/

@[expose] public section

assert_not_exists Ideal

variable {α : Type*} {R : Type*} {M : Type*}

open Pointwise

namespace Submodule

variable [Semiring R] [AddCommGroup M] [Module R M]

/-!
### Sets acting on Submodules

Let `R` be a (semi)ring and `M` an `R`-module. Let `S` be a monoid which acts on `M` distributively,
then subsets of `S` can act on submodules of `M`.
For subset `s ⊆ S` and submodule `N ≤ M`, we define `s • N` to be the smallest submodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.

#### Results
For arbitrary monoids `S` acting distributively on `M`, there is an induction principle for `s • N`:
To prove `P` holds for all `s • N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smul_inductionOn` where
`x : M` and `hx : x ∈ s • N`

When we consider subset of `R` acting on `M`
- `Submodule.pointwiseSetDistribMulAction` : the action described above is distributive.
- `Submodule.mem_set_smul` : `x ∈ s • N` iff `x` can be written as `r₀ n₀ + ... + rₖ nₖ` where
  `rᵢ ∈ s` and `nᵢ ∈ N`.
- `Submodule.coe_span_smul`: `s • N` is the same as `⟨s⟩ • N` where `⟨s⟩` is the ideal spanned
  by `s`.


#### Notes
- If we assume the addition on subsets of `R` is the `⊔` and subtraction `⊓` i.e. use `SetSemiring`,
  then this action actually gives a module structure on submodules of `M` over subsets of `R`.
- If we generalize so that `r • N` makes sense for all `r : S`, then `Submodule.singleton_set_smul`
  and `Submodule.singleton_set_smul` can be generalized as well.
-/

section DistribMulAction

variable {S : Type*} [Monoid S]
variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

-- Implementation note: if `N` is both an `R`-submodule and `S`-submodule and `SMulCommClass R S M`,
-- this lemma is also true for any `s : Set S`.
lemma set_smul_eq_map [SMulCommClass R R N] :
    sR • N =
    Submodule.map
      (N.subtype.comp (Finsupp.lsum R <| DistribSMul.toLinearMap _ _))
      (Finsupp.supported N R sR) := by
  classical
  apply set_smul_eq_of_le
  · intro r n hr hn
    exact ⟨Finsupp.single r ⟨n, hn⟩, Finsupp.single_mem_supported _ _ hr, by simp⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    simp only [LinearMap.coe_comp, coe_subtype, Finsupp.coe_lsum, Finsupp.sum, Function.comp_apply]
    rw [AddSubmonoid.coe_finset_sum]
    refine Submodule.sum_mem (p := sR • N) (t := c.support) ?_ _ ⟨sR • N, ?_⟩
    · rintro r hr
      rw [mem_set_smul_def, Submodule.mem_sInf]
      rintro p hp
      exact hp (hc hr) (c r).2
    · ext x : 1
      simp only [Set.mem_iInter, SetLike.mem_coe]
      fconstructor
      · refine fun h ↦ h fun r n hr hn ↦ ?_
        rw [mem_set_smul_def, mem_sInf]
        exact fun p hp ↦ hp hr hn
      · simp_all

lemma mem_set_smul (x : M) [SMulCommClass R R N] :
    x ∈ sR • N ↔ ∃ (c : R →₀ N), (c.support : Set R) ⊆ sR ∧ x = c.sum fun r m ↦ r • m := by
  fconstructor
  · intro h
    rw [set_smul_eq_map] at h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨c, hc, rfl⟩
  · rw [mem_set_smul_def, Submodule.mem_sInf]
    rintro ⟨c, hc1, rfl⟩ p hp
    rw [Finsupp.sum, AddSubmonoid.coe_finset_sum]
    exact Submodule.sum_mem _ fun r hr ↦ hp (hc1 hr) (c _).2

-- Note that this can't be generalized to `Set S`, because even though `SMulCommClass R R M` implies
-- `SMulComm R R N` for all `R`-submodules `N`, `SMulCommClass R S N` for all `R`-submodules `N`
-- does not make sense. If we just focus on `R`-submodules that are also `S`-submodule, then this
-- should be true.
/-- A subset of a ring `R` has a multiplicative action on submodules of a module over `R`. -/
@[instance_reducible]
protected noncomputable def pointwiseSetMulAction [SMulCommClass R R M] :
    MulAction (Set R) (Submodule R M) where
  one_smul x := show {(1 : R)} • x = x from SetLike.ext fun m =>
    (mem_singleton_set_smul _ _ _).trans ⟨by rintro ⟨_, h, rfl⟩; rwa [one_smul],
      fun h => ⟨m, h, (one_smul _ _).symm⟩⟩
  mul_smul s t x := le_antisymm
    (set_smul_le _ _ _ <| by rintro _ _ ⟨_, _, _, _, rfl⟩ _; rw [mul_smul]; aesop)
    (set_smul_le _ _ _ fun r m hr hm ↦ by
      have : SMulCommClass R R x := ⟨fun r s m => Subtype.ext <| smul_comm _ _ _⟩
      obtain ⟨c, hc1, rfl⟩ := mem_set_smul _ _ _ |>.mp hm
      rw [Finsupp.sum, AddSubmonoid.coe_finset_sum]
      simp only [SetLike.val_smul, Finset.smul_sum, smul_smul]
      exact Submodule.sum_mem _ fun r' hr' ↦
        mem_set_smul_of_mem_mem (Set.mul_mem_mul hr (hc1 hr')) (c _).2)

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetMulAction

-- This cannot be generalized to `Set S` because `MulAction` can't be generalized already.
/-- In a ring, sets acts on submodules. -/
@[instance_reducible]
protected noncomputable def pointwiseSetDistribMulAction [SMulCommClass R R M] :
    DistribMulAction (Set R) (Submodule R M) where
  smul_zero s := set_smul_bot s
  smul_add s x y := le_antisymm
    (set_smul_le _ _ _ <| by
      rintro r m hr hm
      rw [add_eq_sup, Submodule.mem_sup] at hm
      obtain ⟨a, ha, b, hb, rfl⟩ := hm
      rw [smul_add, add_eq_sup, Submodule.mem_sup]
      exact ⟨r • a, mem_set_smul_of_mem_mem (mem1 := hr) (mem2 := ha),
        r • b, mem_set_smul_of_mem_mem (mem1 := hr) (mem2 := hb), rfl⟩)
    (sup_le_iff.mpr ⟨smul_mono_right _ le_sup_left, smul_mono_right _ le_sup_right⟩)

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetDistribMulAction

end DistribMulAction

end Submodule
