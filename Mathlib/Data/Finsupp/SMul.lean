/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Regular.SMul
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Declarations about scalar multiplication on `Finsupp`

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/


noncomputable section

open Finset Function

variable {α β M N G R : Type*}

namespace Finsupp

section

variable [Zero M] [MonoidWithZero R] [MulActionWithZero R M]

@[simp]
theorem single_smul (a b : α) (f : α → M) (r : R) : single a r b • f a = single a (r • f b) b := by
  by_cases h : a = b <;> simp [h]

end

section

variable [Monoid G] [MulAction G α] [AddCommMonoid M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
def comapSMul : SMul G (α →₀ M) where smul g := mapDomain (g • ·)

attribute [local instance] comapSMul

theorem comapSMul_def (g : G) (f : α →₀ M) : g • f = mapDomain (g • ·) f :=
  rfl

@[simp]
theorem comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  mapDomain_single

/-- `Finsupp.comapSMul` is multiplicative -/
def comapMulAction : MulAction G (α →₀ M) where
  one_smul f := by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def, comapSMul_def, comapSMul_def, ← comp_smul_left, mapDomain_comp]

attribute [local instance] comapMulAction

/-- `Finsupp.comapSMul` is distributive -/
def comapDistribMulAction : DistribMulAction G (α →₀ M) where
  smul_zero g := by
    ext a
    simp only [comapSMul_def]
    simp
  smul_add g f f' := by
    ext
    simp only [comapSMul_def]
    simp [mapDomain_add]

end

section

variable [Group G] [MulAction G α] [AddCommMonoid M]

attribute [local instance] comapSMul comapMulAction comapDistribMulAction

/-- When `G` is a group, `Finsupp.comapSMul` acts by precomposition with the action of `g⁻¹`.
-/
@[simp]
theorem comapSMul_apply (g : G) (f : α →₀ M) (a : α) : (g • f) a = f (g⁻¹ • a) := by
  conv_lhs => rw [← smul_inv_smul g a]
  exact mapDomain_apply (MulAction.injective g) _ (g⁻¹ • a)

end

section

/-!
Throughout this section, some `Monoid` and `Semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

theorem _root_.IsSMulRegular.finsupp [Zero M] [SMulZeroClass R M] {k : R}
    (hk : IsSMulRegular M k) : IsSMulRegular (α →₀ M) k :=
  fun _ _ h => ext fun i => hk (DFunLike.congr_fun h i)

instance faithfulSMul [Nonempty α] [Zero M] [SMulZeroClass R M] [FaithfulSMul R M] :
    FaithfulSMul R (α →₀ M) where
  eq_of_smul_eq_smul h :=
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by simpa using DFunLike.congr_fun (h (single a m)) a

variable (α M)

instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (α →₀ M) :=
  { Finsupp.distribSMul _ _ with
    one_smul := fun x => ext fun y => one_smul R (x y)
    mul_smul := fun r s x => ext fun y => mul_smul r s (x y) }

instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α →₀ M) :=
  { toDistribMulAction := Finsupp.distribMulAction α M
    zero_smul := fun _ => ext fun _ => zero_smul _ _
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _ }

variable {α M}

@[simp]
theorem support_smul_eq [Zero R] [Zero M] [SMulWithZero R M] [NoZeroSMulDivisors R M] {b : R}
    (hb : b ≠ 0) {g : α →₀ M} : (b • g).support = g.support :=
  Finset.ext fun a => by simp [Finsupp.smul_apply, hb]

section

variable {p : α → Prop} [DecidablePred p]

@[simp]
theorem filter_smul [Zero M] [SMulZeroClass R M] {b : R} {v : α →₀ M} :
    (b • v).filter p = b • v.filter p :=
  DFunLike.coe_injective <| by
    simp only [filter_eq_indicator, coe_smul]
    exact Set.indicator_const_smul { x | p x } b v

end

theorem mapDomain_smul [AddCommMonoid M] [DistribSMul R M] {f : α → β} (b : R)
    (v : α →₀ M) : mapDomain f (b • v) = b • mapDomain f v :=
  mapDomain_mapRange _ _ _ _ (smul_add b)

theorem smul_single' {_ : Semiring R} (c : R) (a : α) (b : R) :
    c • Finsupp.single a b = Finsupp.single a (c * b) := by simp

theorem smul_single_one [MulZeroOneClass R] (a : α) (b : R) :
    b • single a (1 : R) = single a b := by
  rw [smul_single, smul_eq_mul, mul_one]

theorem comapDomain_smul [Zero M] [SMulZeroClass R M] {f : α → β} (r : R)
    (v : β →₀ M) (hfv : Set.InjOn f (f ⁻¹' ↑v.support))
    (hfrv : Set.InjOn f (f ⁻¹' ↑(r • v).support) :=
      hfv.mono <| Set.preimage_mono <| Finset.coe_subset.mpr support_smul) :
    comapDomain f (r • v) hfrv = r • comapDomain f v hfv := by
  ext
  rfl

/-- A version of `Finsupp.comapDomain_smul` that's easier to use. -/
theorem comapDomain_smul_of_injective [Zero M] [SMulZeroClass R M] {f : α → β}
    (hf : Function.Injective f) (r : R) (v : β →₀ M) :
    comapDomain f (r • v) hf.injOn = r • comapDomain f v hf.injOn :=
  comapDomain_smul _ _ _ _

end

theorem sum_smul_index [MulZeroClass R] [AddCommMonoid M] {g : α →₀ R} {b : R} {h : α → R → M}
    (h0 : ∀ i, h i 0 = 0) : (b • g).sum h = g.sum fun i a => h i (b * a) :=
  Finsupp.sum_mapRange_index h0

theorem sum_smul_index' [Zero M] [SMulZeroClass R M] [AddCommMonoid N] {g : α →₀ M} {b : R}
    {h : α → M → N} (h0 : ∀ i, h i 0 = 0) : (b • g).sum h = g.sum fun i c => h i (b • c) :=
  Finsupp.sum_mapRange_index h0

/-- A version of `Finsupp.sum_smul_index'` for bundled additive maps. -/
theorem sum_smul_index_addMonoidHom [AddZeroClass M] [AddCommMonoid N] [SMulZeroClass R M]
    {g : α →₀ M} {b : R} {h : α → M →+ N} :
    ((b • g).sum fun a => h a) = g.sum fun i c => h i (b • c) :=
  sum_mapRange_index fun i => (h i).map_zero

instance noZeroSMulDivisors [Zero R] [Zero M] [SMulZeroClass R M] {ι : Type*}
    [NoZeroSMulDivisors R M] : NoZeroSMulDivisors R (ι →₀ M) :=
  ⟨fun h => or_iff_not_imp_left.mpr fun hc => Finsupp.ext fun i =>
    (eq_zero_or_eq_zero_of_smul_eq_zero (DFunLike.ext_iff.mp h i)).resolve_left hc⟩

section DistribMulActionSemiHom
variable [Monoid R] [AddMonoid M] [AddMonoid N] [DistribMulAction R M] [DistribMulAction R N]

/-- `Finsupp.single` as a `DistribMulActionSemiHom`.

See also `Finsupp.lsingle` for the version as a linear map. -/
def DistribMulActionHom.single (a : α) : M →+[R] α →₀ M :=
  { singleAddHom a with
    map_smul' := fun k m => by simp }

theorem distribMulActionHom_ext {f g : (α →₀ M) →+[R] N}
    (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) : f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addHom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem distribMulActionHom_ext' {f g : (α →₀ M) →+[R] N}
    (h : ∀ a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

end DistribMulActionSemiHom

end Finsupp
