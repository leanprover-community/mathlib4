/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Nicolò Cavalleri

! This file was ported from Lean 3 source module topology.continuous_function.algebra
! leanprover-community/mathlib commit efe03a53241aaa777c1016a7a0e71dd3b92a4313
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Pi
import Mathbin.Algebra.Periodic
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.Star.StarAlgHom
import Mathbin.Tactic.FieldSimp
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Star
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.ContinuousFunction.Ordered
import Mathbin.Topology.UniformSpace.CompactConvergence

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over the type `continuous_map α β`
(denoted `C(α, β)`) of **bundled** continuous maps from `α` to `β`. For example, `C(α, β)`
is a group when `β` is a group, a ring when `β` is a ring, etc.

For each type of algebraic structure, we also define an appropriate subobject of `α → β`
with carrier `{ f : α → β | continuous f }`. For example, when `β` is a group, a subgroup
`continuous_subgroup α β` of `α → β` is constructed with carrier `{ f : α → β | continuous f }`.

Note that, rather than using the derived algebraic structures on these subobjects
(for example, when `β` is a group, the derived group structure on `continuous_subgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/


attribute [local elab_without_expected_type] Continuous.comp

namespace ContinuousFunctions

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {f g : { f : α → β | Continuous f }}

instance : CoeFun { f : α → β | Continuous f } fun _ => α → β :=
  ⟨Subtype.val⟩

end ContinuousFunctions

namespace ContinuousMap

variable {α : Type _} {β : Type _} {γ : Type _}

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

-- ### "mul" and "add"
@[to_additive]
instance hasMul [Mul β] [ContinuousMul β] : Mul C(α, β) :=
  ⟨fun f g => ⟨f * g, continuous_mul.comp (f.Continuous.prod_mk g.Continuous : _)⟩⟩
#align continuous_map.has_mul ContinuousMap.hasMul
#align continuous_map.has_add ContinuousMap.hasAdd

@[simp, norm_cast, to_additive]
theorem coe_mul [Mul β] [ContinuousMul β] (f g : C(α, β)) : ⇑(f * g) = f * g :=
  rfl
#align continuous_map.coe_mul ContinuousMap.coe_mul
#align continuous_map.coe_add ContinuousMap.coe_add

@[simp, to_additive]
theorem mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = f x * g x :=
  rfl
#align continuous_map.mul_apply ContinuousMap.mul_apply
#align continuous_map.add_apply ContinuousMap.add_apply

@[simp, to_additive]
theorem mul_comp [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
    (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
  rfl
#align continuous_map.mul_comp ContinuousMap.mul_comp
#align continuous_map.add_comp ContinuousMap.add_comp

-- ### "one"
@[to_additive]
instance [One β] : One C(α, β) :=
  ⟨const α 1⟩

@[simp, norm_cast, to_additive]
theorem coe_one [One β] : ⇑(1 : C(α, β)) = 1 :=
  rfl
#align continuous_map.coe_one ContinuousMap.coe_one
#align continuous_map.coe_zero ContinuousMap.coe_zero

@[simp, to_additive]
theorem one_apply [One β] (x : α) : (1 : C(α, β)) x = 1 :=
  rfl
#align continuous_map.one_apply ContinuousMap.one_apply
#align continuous_map.zero_apply ContinuousMap.zero_apply

@[simp, to_additive]
theorem one_comp [One γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1 :=
  rfl
#align continuous_map.one_comp ContinuousMap.one_comp
#align continuous_map.zero_comp ContinuousMap.zero_comp

-- ### "nat_cast"
instance [NatCast β] : NatCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
theorem coe_nat_cast [NatCast β] (n : ℕ) : ((n : C(α, β)) : α → β) = n :=
  rfl
#align continuous_map.coe_nat_cast ContinuousMap.coe_nat_cast

@[simp]
theorem nat_cast_apply [NatCast β] (n : ℕ) (x : α) : (n : C(α, β)) x = n :=
  rfl
#align continuous_map.nat_cast_apply ContinuousMap.nat_cast_apply

-- ### "int_cast"
instance [IntCast β] : IntCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
theorem coe_int_cast [IntCast β] (n : ℤ) : ((n : C(α, β)) : α → β) = n :=
  rfl
#align continuous_map.coe_int_cast ContinuousMap.coe_int_cast

@[simp]
theorem int_cast_apply [IntCast β] (n : ℤ) (x : α) : (n : C(α, β)) x = n :=
  rfl
#align continuous_map.int_cast_apply ContinuousMap.int_cast_apply

-- ### "nsmul" and "pow"
instance hasNsmul [AddMonoid β] [ContinuousAdd β] : SMul ℕ C(α, β) :=
  ⟨fun n f => ⟨n • f, f.Continuous.nsmul n⟩⟩
#align continuous_map.has_nsmul ContinuousMap.hasNsmul

@[to_additive]
instance hasPow [Monoid β] [ContinuousMul β] : Pow C(α, β) ℕ :=
  ⟨fun f n => ⟨f ^ n, f.Continuous.pow n⟩⟩
#align continuous_map.has_pow ContinuousMap.hasPow
#align continuous_map.has_nsmul ContinuousMap.hasNsmul

@[norm_cast, to_additive]
theorem coe_pow [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) : ⇑(f ^ n) = f ^ n :=
  rfl
#align continuous_map.coe_pow ContinuousMap.coe_pow
#align continuous_map.coe_nsmul ContinuousMap.coe_nsmul

@[to_additive]
theorem pow_apply [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) (x : α) :
    (f ^ n) x = f x ^ n :=
  rfl
#align continuous_map.pow_apply ContinuousMap.pow_apply
#align continuous_map.nsmul_apply ContinuousMap.nsmul_apply

-- don't make auto-generated `coe_nsmul` and `nsmul_apply` simp, as the linter complains they're
-- redundant WRT `coe_smul`
attribute [simp] coe_pow pow_apply

@[to_additive]
theorem pow_comp [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : ℕ) (g : C(α, β)) :
    (f ^ n).comp g = f.comp g ^ n :=
  rfl
#align continuous_map.pow_comp ContinuousMap.pow_comp
#align continuous_map.nsmul_comp ContinuousMap.nsmul_comp

-- don't make `nsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] pow_comp

-- ### "inv" and "neg"
@[to_additive]
instance [Group β] [TopologicalGroup β] : Inv C(α, β) where inv f := ⟨f⁻¹, f.Continuous.inv⟩

@[simp, norm_cast, to_additive]
theorem coe_inv [Group β] [TopologicalGroup β] (f : C(α, β)) : ⇑f⁻¹ = f⁻¹ :=
  rfl
#align continuous_map.coe_inv ContinuousMap.coe_inv
#align continuous_map.coe_neg ContinuousMap.coe_neg

@[simp, to_additive]
theorem inv_apply [Group β] [TopologicalGroup β] (f : C(α, β)) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align continuous_map.inv_apply ContinuousMap.inv_apply
#align continuous_map.neg_apply ContinuousMap.neg_apply

@[simp, to_additive]
theorem inv_comp [Group γ] [TopologicalGroup γ] (f : C(β, γ)) (g : C(α, β)) :
    f⁻¹.comp g = (f.comp g)⁻¹ :=
  rfl
#align continuous_map.inv_comp ContinuousMap.inv_comp
#align continuous_map.neg_comp ContinuousMap.neg_comp

-- ### "div" and "sub"
@[to_additive]
instance [Div β] [ContinuousDiv β] : Div C(α, β)
    where div f g := ⟨f / g, f.Continuous.div' g.Continuous⟩

@[simp, norm_cast, to_additive]
theorem coe_div [Div β] [ContinuousDiv β] (f g : C(α, β)) : ⇑(f / g) = f / g :=
  rfl
#align continuous_map.coe_div ContinuousMap.coe_div
#align continuous_map.coe_sub ContinuousMap.coe_sub

@[simp, to_additive]
theorem div_apply [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α) : (f / g) x = f x / g x :=
  rfl
#align continuous_map.div_apply ContinuousMap.div_apply
#align continuous_map.sub_apply ContinuousMap.sub_apply

@[simp, to_additive]
theorem div_comp [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β)) :
    (f / g).comp h = f.comp h / g.comp h :=
  rfl
#align continuous_map.div_comp ContinuousMap.div_comp
#align continuous_map.sub_comp ContinuousMap.sub_comp

-- ### "zpow" and "zsmul"
instance hasZsmul [AddGroup β] [TopologicalAddGroup β] : SMul ℤ C(α, β)
    where smul z f := ⟨z • f, f.Continuous.zsmul z⟩
#align continuous_map.has_zsmul ContinuousMap.hasZsmul

@[to_additive]
instance hasZpow [Group β] [TopologicalGroup β] : Pow C(α, β) ℤ
    where pow f z := ⟨f ^ z, f.Continuous.zpow z⟩
#align continuous_map.has_zpow ContinuousMap.hasZpow
#align continuous_map.has_zsmul ContinuousMap.hasZsmul

@[norm_cast, to_additive]
theorem coe_zpow [Group β] [TopologicalGroup β] (f : C(α, β)) (z : ℤ) : ⇑(f ^ z) = f ^ z :=
  rfl
#align continuous_map.coe_zpow ContinuousMap.coe_zpow
#align continuous_map.coe_zsmul ContinuousMap.coe_zsmul

@[to_additive]
theorem zpow_apply [Group β] [TopologicalGroup β] (f : C(α, β)) (z : ℤ) (x : α) :
    (f ^ z) x = f x ^ z :=
  rfl
#align continuous_map.zpow_apply ContinuousMap.zpow_apply
#align continuous_map.zsmul_apply ContinuousMap.zsmul_apply

-- don't make auto-generated `coe_zsmul` and `zsmul_apply` simp as the linter complains they're
-- redundant WRT `coe_smul`
attribute [simp] coe_zpow zpow_apply

@[to_additive]
theorem zpow_comp [Group γ] [TopologicalGroup γ] (f : C(β, γ)) (z : ℤ) (g : C(α, β)) :
    (f ^ z).comp g = f.comp g ^ z :=
  rfl
#align continuous_map.zpow_comp ContinuousMap.zpow_comp
#align continuous_map.zsmul_comp ContinuousMap.zsmul_comp

-- don't make `zsmul_comp` simp as the linter complains it's redundant WRT `smul_comp`
attribute [simp] zpow_comp

end ContinuousMap

section GroupStructure

/-!
### Group stucture

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/


section Subtype

/-- The `submonoid` of continuous maps `α → β`. -/
@[to_additive "The `add_submonoid` of continuous maps `α → β`. "]
def continuousSubmonoid (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β]
    [MulOneClass β] [ContinuousMul β] : Submonoid (α → β)
    where
  carrier := { f : α → β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' f g fc gc := fc.mul gc
#align continuous_submonoid continuousSubmonoid
#align continuous_add_submonoid continuousAddSubmonoid

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive "The `add_subgroup` of continuous maps `α → β`. "]
def continuousSubgroup (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] [Group β]
    [TopologicalGroup β] : Subgroup (α → β) :=
  { continuousSubmonoid α β with inv_mem' := fun f fc => Continuous.inv fc }
#align continuous_subgroup continuousSubgroup
#align continuous_add_subgroup continuousAddSubgroup

end Subtype

namespace ContinuousMap

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]

@[to_additive]
instance [Semigroup β] [ContinuousMul β] : Semigroup C(α, β) :=
  coe_injective.Semigroup _ coe_mul

@[to_additive]
instance [CommSemigroup β] [ContinuousMul β] : CommSemigroup C(α, β) :=
  coe_injective.CommSemigroup _ coe_mul

@[to_additive]
instance [MulOneClass β] [ContinuousMul β] : MulOneClass C(α, β) :=
  coe_injective.MulOneClass _ coe_one coe_mul

instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C(α, β) :=
  coe_injective.MulZeroClass _ coe_zero coe_mul

instance [SemigroupWithZero β] [ContinuousMul β] : SemigroupWithZero C(α, β) :=
  coe_injective.SemigroupWithZero _ coe_zero coe_mul

@[to_additive]
instance [Monoid β] [ContinuousMul β] : Monoid C(α, β) :=
  coe_injective.Monoid _ coe_one coe_mul coe_pow

instance [MonoidWithZero β] [ContinuousMul β] : MonoidWithZero C(α, β) :=
  coe_injective.MonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [CommMonoid β] [ContinuousMul β] : CommMonoid C(α, β) :=
  coe_injective.CommMonoid _ coe_one coe_mul coe_pow

instance [CommMonoidWithZero β] [ContinuousMul β] : CommMonoidWithZero C(α, β) :=
  coe_injective.CommMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [LocallyCompactSpace α] [Mul β] [ContinuousMul β] : ContinuousMul C(α, β) :=
  ⟨by
    refine' continuous_of_continuous_uncurry _ _
    have h1 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.fst x.snd :=
      continuous_eval'.comp (continuous_fst.prod_map continuous_id)
    have h2 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.snd x.snd :=
      continuous_eval'.comp (continuous_snd.prod_map continuous_id)
    exact h1.mul h2⟩

/-- Coercion to a function as an `monoid_hom`. Similar to `monoid_hom.coe_fn`. -/
@[to_additive "Coercion to a function as an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn`.",
  simps]
def coeFnMonoidHom [Monoid β] [ContinuousMul β] : C(α, β) →* α → β
    where
  toFun := coeFn
  map_one' := coe_one
  map_mul' := coe_mul
#align continuous_map.coe_fn_monoid_hom ContinuousMap.coeFnMonoidHom
#align continuous_map.coe_fn_add_monoid_hom ContinuousMap.coeFnAddMonoidHom

variable (α)

/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`monoid_hom`. Similar to `monoid_hom.comp_left`. -/
@[to_additive
      "Composition on the left by a (continuous) homomorphism of topological `add_monoid`s,\nas an `add_monoid_hom`. Similar to `add_monoid_hom.comp_left`.",
  simps]
protected def MonoidHom.compLeftContinuous {γ : Type _} [Monoid β] [ContinuousMul β]
    [TopologicalSpace γ] [Monoid γ] [ContinuousMul γ] (g : β →* γ) (hg : Continuous g) :
    C(α, β) →* C(α, γ) where
  toFun f := (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun x => g.map_one
  map_mul' f₁ f₂ := ext fun x => g.map_mul _ _
#align monoid_hom.comp_left_continuous MonoidHom.compLeftContinuous
#align add_monoid_hom.comp_left_continuous AddMonoidHom.compLeftContinuous

variable {α}

/-- Composition on the right as a `monoid_hom`. Similar to `monoid_hom.comp_hom'`. -/
@[to_additive
      "Composition on the right as an `add_monoid_hom`. Similar to\n`add_monoid_hom.comp_hom'`.",
  simps]
def compMonoidHom' {γ : Type _} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
    (g : C(α, β)) : C(β, γ) →* C(α, γ)
    where
  toFun f := f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g
#align continuous_map.comp_monoid_hom' ContinuousMap.compMonoidHom'
#align continuous_map.comp_add_monoid_hom' ContinuousMap.compAddMonoidHom'

open BigOperators

@[simp, to_additive]
theorem coe_prod [CommMonoid β] [ContinuousMul β] {ι : Type _} (s : Finset ι) (f : ι → C(α, β)) :
    ⇑(∏ i in s, f i) = ∏ i in s, (f i : α → β) :=
  (coeFnMonoidHom : C(α, β) →* _).map_prod f s
#align continuous_map.coe_prod ContinuousMap.coe_prod
#align continuous_map.coe_sum ContinuousMap.coe_sum

@[to_additive]
theorem prod_apply [CommMonoid β] [ContinuousMul β] {ι : Type _} (s : Finset ι) (f : ι → C(α, β))
    (a : α) : (∏ i in s, f i) a = ∏ i in s, f i a := by simp
#align continuous_map.prod_apply ContinuousMap.prod_apply
#align continuous_map.sum_apply ContinuousMap.sum_apply

@[to_additive]
instance [Group β] [TopologicalGroup β] : Group C(α, β) :=
  coe_injective.Group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance [CommGroup β] [TopologicalGroup β] : CommGroup C(α, β) :=
  coe_injective.CommGroup _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance [CommGroup β] [TopologicalGroup β] : TopologicalGroup C(α, β)
    where
  continuous_mul := by
    letI : UniformSpace β := TopologicalGroup.toUniformSpace β
    have : UniformGroup β := comm_topologicalGroup_is_uniform
    rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt, tendsto_iff_forall_compact_tendsto_uniformly_on, nhds_prod_eq]
    exact fun K hK =>
      uniform_continuous_mul.comp_tendsto_uniformly_on
        ((tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK).Prod
          (tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK))
  continuous_inv := by
    letI : UniformSpace β := TopologicalGroup.toUniformSpace β
    have : UniformGroup β := comm_topologicalGroup_is_uniform
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, tendsto_iff_forall_compact_tendsto_uniformly_on]
    exact fun K hK =>
      uniform_continuous_inv.comp_tendsto_uniformly_on
        (tendsto_iff_forall_compact_tendsto_uniformly_on.mp Filter.tendsto_id K hK)

-- TODO: rewrite the next three lemmas for products and deduce sum case via `to_additive`, once
-- definition of `tprod` is in place
/-- If `α` is locally compact, and an infinite sum of functions in `C(α, β)`
converges to `g` (for the compact-open topology), then the pointwise sum converges to `g x` for
all `x ∈ α`. -/
theorem hasSum_apply {γ : Type _} [LocallyCompactSpace α] [AddCommMonoid β] [ContinuousAdd β]
    {f : γ → C(α, β)} {g : C(α, β)} (hf : HasSum f g) (x : α) : HasSum (fun i : γ => f i x) (g x) :=
  by
  let evₓ : AddMonoidHom C(α, β) β := (Pi.evalAddMonoidHom _ x).comp coe_fn_add_monoid_hom
  exact hf.map evₓ (ContinuousMap.continuous_eval_const' x)
#align continuous_map.has_sum_apply ContinuousMap.hasSum_apply

theorem summable_apply [LocallyCompactSpace α] [AddCommMonoid β] [ContinuousAdd β] {γ : Type _}
    {f : γ → C(α, β)} (hf : Summable f) (x : α) : Summable fun i : γ => f i x :=
  (hasSum_apply hf.HasSum x).Summable
#align continuous_map.summable_apply ContinuousMap.summable_apply

theorem tsum_apply [LocallyCompactSpace α] [T2Space β] [AddCommMonoid β] [ContinuousAdd β]
    {γ : Type _} {f : γ → C(α, β)} (hf : Summable f) (x : α) :
    (∑' i : γ, f i x) = (∑' i : γ, f i) x :=
  (hasSum_apply hf.HasSum x).tsum_eq
#align continuous_map.tsum_apply ContinuousMap.tsum_apply

end ContinuousMap

end GroupStructure

section RingStructure

/-!
### Ring stucture

In this section we show that continuous functions valued in a topological semiring `R` inherit
the structure of a ring.
-/


section Subtype

/-- The subsemiring of continuous maps `α → β`. -/
def continuousSubsemiring (α : Type _) (R : Type _) [TopologicalSpace α] [TopologicalSpace R]
    [NonAssocSemiring R] [TopologicalSemiring R] : Subsemiring (α → R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }
#align continuous_subsemiring continuousSubsemiring

/-- The subring of continuous maps `α → β`. -/
def continuousSubring (α : Type _) (R : Type _) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
    [TopologicalRing R] : Subring (α → R) :=
  { continuousSubsemiring α R, continuousAddSubgroup α R with }
#align continuous_subring continuousSubring

end Subtype

namespace ContinuousMap

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocSemiring β] [TopologicalSemiring β] : NonUnitalNonAssocSemiring C(α, β) :=
  coe_injective.NonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalSemiring β]
    [TopologicalSemiring β] : NonUnitalSemiring C(α, β) :=
  coe_injective.NonUnitalSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [AddMonoidWithOne β]
    [ContinuousAdd β] : AddMonoidWithOne C(α, β) :=
  coe_injective.AddMonoidWithOne _ coe_zero coe_one coe_add coe_nsmul coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonAssocSemiring β]
    [TopologicalSemiring β] : NonAssocSemiring C(α, β) :=
  coe_injective.NonAssocSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [TopologicalSemiring β] : Semiring C(α, β) :=
  coe_injective.Semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocRing β] [TopologicalRing β] : NonUnitalNonAssocRing C(α, β) :=
  coe_injective.NonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalRing β]
    [TopologicalRing β] : NonUnitalRing C(α, β) :=
  coe_injective.NonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonAssocRing β]
    [TopologicalRing β] : NonAssocRing C(α, β) :=
  coe_injective.NonAssocRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_nat_cast coe_int_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Ring β]
    [TopologicalRing β] : Ring C(α, β) :=
  coe_injective.Ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
    coe_nat_cast coe_int_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalCommSemiring β] [TopologicalSemiring β] : NonUnitalCommSemiring C(α, β) :=
  coe_injective.NonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommSemiring β]
    [TopologicalSemiring β] : CommSemiring C(α, β) :=
  coe_injective.CommSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_nat_cast

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalCommRing β]
    [TopologicalRing β] : NonUnitalCommRing C(α, β) :=
  coe_injective.NonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CommRing β]
    [TopologicalRing β] : CommRing C(α, β) :=
  coe_injective.CommRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_pow coe_nat_cast coe_int_cast

/-- Composition on the left by a (continuous) homomorphism of topological semirings, as a
`ring_hom`.  Similar to `ring_hom.comp_left`. -/
@[simps]
protected def RingHom.compLeftContinuous (α : Type _) {β : Type _} {γ : Type _} [TopologicalSpace α]
    [TopologicalSpace β] [Semiring β] [TopologicalSemiring β] [TopologicalSpace γ] [Semiring γ]
    [TopologicalSemiring γ] (g : β →+* γ) (hg : Continuous g) : C(α, β) →+* C(α, γ) :=
  { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }
#align ring_hom.comp_left_continuous RingHom.compLeftContinuous

/-- Coercion to a function as a `ring_hom`. -/
@[simps]
def coeFnRingHom {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [TopologicalSemiring β] : C(α, β) →+* α → β :=
  { (coeFnMonoidHom : C(α, β) →* _), (coeFnAddMonoidHom : C(α, β) →+ _) with toFun := coeFn }
#align continuous_map.coe_fn_ring_hom ContinuousMap.coeFnRingHom

end ContinuousMap

end RingStructure

attribute [local ext] Subtype.eq

section ModuleStructure

/-!
### Semiodule stucture

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/


section Subtype

variable (α : Type _) [TopologicalSpace α]

variable (R : Type _) [Semiring R]

variable (M : Type _) [TopologicalSpace M] [AddCommGroup M]

variable [Module R M] [ContinuousConstSMul R M] [TopologicalAddGroup M]

/-- The `R`-submodule of continuous maps `α → M`. -/
def continuousSubmodule : Submodule R (α → M) :=
  {
    continuousAddSubgroup α
      M with
    carrier := { f : α → M | Continuous f }
    smul_mem' := fun c f hf => hf.const_smul c }
#align continuous_submodule continuousSubmodule

end Subtype

namespace ContinuousMap

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {R R₁ : Type _} {M : Type _}
  [TopologicalSpace M] {M₂ : Type _} [TopologicalSpace M₂]

@[to_additive ContinuousMap.hasVadd]
instance [SMul R M] [ContinuousConstSMul R M] : SMul R C(α, M) :=
  ⟨fun r f => ⟨r • f, f.Continuous.const_smul r⟩⟩

@[to_additive]
instance [LocallyCompactSpace α] [SMul R M] [ContinuousConstSMul R M] :
    ContinuousConstSMul R C(α, M) :=
  ⟨fun γ => continuous_of_continuous_uncurry _ (continuous_eval'.const_smul γ)⟩

@[to_additive]
instance [LocallyCompactSpace α] [TopologicalSpace R] [SMul R M] [ContinuousSMul R M] :
    ContinuousSMul R C(α, M) :=
  ⟨by
    refine' continuous_of_continuous_uncurry _ _
    have h : Continuous fun x : (R × C(α, M)) × α => x.fst.snd x.snd :=
      continuous_eval'.comp (continuous_snd.prod_map continuous_id)
    exact (continuous_fst.comp continuous_fst).smul h⟩

@[simp, norm_cast, to_additive]
theorem coe_smul [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) : ⇑(c • f) = c • f :=
  rfl
#align continuous_map.coe_smul ContinuousMap.coe_smul
#align continuous_map.coe_vadd ContinuousMap.coe_vadd

@[to_additive]
theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
    (c • f) a = c • f a :=
  rfl
#align continuous_map.smul_apply ContinuousMap.smul_apply
#align continuous_map.vadd_apply ContinuousMap.vadd_apply

@[simp, to_additive]
theorem smul_comp [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
    (r • f).comp g = r • f.comp g :=
  rfl
#align continuous_map.smul_comp ContinuousMap.smul_comp
#align continuous_map.vadd_comp ContinuousMap.vadd_comp

@[to_additive]
instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M]
    [SMulCommClass R R₁ M] : SMulCommClass R R₁ C(α, M)
    where smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M] [SMul R R₁]
    [IsScalarTower R R₁ M] : IsScalarTower R R₁ C(α, M)
    where smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousConstSMul R M] [IsCentralScalar R M] :
    IsCentralScalar R C(α, M) where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

instance [Monoid R] [MulAction R M] [ContinuousConstSMul R M] : MulAction R C(α, M) :=
  Function.Injective.mulAction _ coe_injective coe_smul

instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [ContinuousAdd M]
    [ContinuousConstSMul R M] : DistribMulAction R C(α, M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂]

variable [ContinuousAdd M] [Module R M] [ContinuousConstSMul R M]

variable [ContinuousAdd M₂] [Module R M₂] [ContinuousConstSMul R M₂]

instance module : Module R C(α, M) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective coe_smul
#align continuous_map.module ContinuousMap.module

variable (R)

/-- Composition on the left by a continuous linear map, as a `linear_map`.
Similar to `linear_map.comp_left`. -/
@[simps]
protected def ContinuousLinearMap.compLeftContinuous (α : Type _) [TopologicalSpace α]
    (g : M →L[R] M₂) : C(α, M) →ₗ[R] C(α, M₂) :=
  { g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.Continuous with
    map_smul' := fun c f => ext fun x => g.map_smul' c _ }
#align continuous_linear_map.comp_left_continuous ContinuousLinearMap.compLeftContinuous

/-- Coercion to a function as a `linear_map`. -/
@[simps]
def coeFnLinearMap : C(α, M) →ₗ[R] α → M :=
  { (coeFnAddMonoidHom : C(α, M) →+ _) with
    toFun := coeFn
    map_smul' := coe_smul }
#align continuous_map.coe_fn_linear_map ContinuousMap.coeFnLinearMap

end ContinuousMap

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `has_continuous_smul` and a `topological_semiring`.-/


section Subtype

variable {α : Type _} [TopologicalSpace α] {R : Type _} [CommSemiring R] {A : Type _}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [TopologicalSemiring A]

/-- The `R`-subalgebra of continuous maps `α → A`. -/
def continuousSubalgebra : Subalgebra R (α → A) :=
  {
    continuousSubsemiring α
      A with
    carrier := { f : α → A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun x : α => algebraMap R A r) }
#align continuous_subalgebra continuousSubalgebra

end Subtype

section ContinuousMap

variable {α : Type _} [TopologicalSpace α] {R : Type _} [CommSemiring R] {A : Type _}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [TopologicalSemiring A] {A₂ : Type _}
  [TopologicalSpace A₂] [Semiring A₂] [Algebra R A₂] [TopologicalSemiring A₂]

/-- Continuous constant functions as a `ring_hom`. -/
def ContinuousMap.c : R →+* C(α, A)
    where
  toFun := fun c : R => ⟨fun x : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext x <;> exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext x <;> exact (algebraMap R A).map_mul _ _
  map_zero' := by ext x <;> exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext x <;> exact (algebraMap R A).map_add _ _
#align continuous_map.C ContinuousMap.c

@[simp]
theorem ContinuousMap.c_apply (r : R) (a : α) : ContinuousMap.c r a = algebraMap R A r :=
  rfl
#align continuous_map.C_apply ContinuousMap.c_apply

instance ContinuousMap.algebra : Algebra R C(α, A)
    where
  toRingHom := ContinuousMap.c
  commutes' c f := by ext x <;> exact Algebra.commutes' _ _
  smul_def' c f := by ext x <;> exact Algebra.smul_def' _ _
#align continuous_map.algebra ContinuousMap.algebra

variable (R)

/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`alg_hom`. Similar to `alg_hom.comp_left`. -/
@[simps]
protected def AlgHom.compLeftContinuous {α : Type _} [TopologicalSpace α] (g : A →ₐ[R] A₂)
    (hg : Continuous g) : C(α, A) →ₐ[R] C(α, A₂) :=
  { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun c => ContinuousMap.ext fun _ => g.commutes' _ }
#align alg_hom.comp_left_continuous AlgHom.compLeftContinuous

variable (A)

/-- Precomposition of functions into a normed ring by a continuous map is an algebra homomorphism.
-/
@[simps]
def ContinuousMap.compRightAlgHom {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    (f : C(α, β)) : C(β, A) →ₐ[R] C(α, A)
    where
  toFun g := g.comp f
  map_zero' := by
    ext
    rfl
  map_add' g₁ g₂ := by
    ext
    rfl
  map_one' := by
    ext
    rfl
  map_mul' g₁ g₂ := by
    ext
    rfl
  commutes' r := by
    ext
    rfl
#align continuous_map.comp_right_alg_hom ContinuousMap.compRightAlgHom

variable {A}

/-- Coercion to a function as an `alg_hom`. -/
@[simps]
def ContinuousMap.coeFnAlgHom : C(α, A) →ₐ[R] α → A :=
  {
    (ContinuousMap.coeFnRingHom :
      C(α, A) →+* _) with
    toFun := coeFn
    commutes' := fun r => rfl }
#align continuous_map.coe_fn_alg_hom ContinuousMap.coeFnAlgHom

variable {R}

/-- A version of `separates_points` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbrev Subalgebra.SeparatesPoints (s : Subalgebra R C(α, A)) : Prop :=
  Set.SeparatesPoints ((fun f : C(α, A) => (f : α → A)) '' (s : Set C(α, A)))
#align subalgebra.separates_points Subalgebra.SeparatesPoints

theorem Subalgebra.separatesPoints_monotone :
    Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints := fun s s' r h x y n =>
  by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩
#align subalgebra.separates_points_monotone Subalgebra.separatesPoints_monotone

@[simp]
theorem algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A) k a = k • 1 :=
  by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl
#align algebra_map_apply algebraMap_apply

variable {𝕜 : Type _} [TopologicalSpace 𝕜]

/-- A set of continuous maps "separates points strongly"
if for each pair of distinct points there is a function with specified values on them.

We give a slightly unusual formulation, where the specified values are given by some
function `v`, and we ask `f x = v x ∧ f y = v y`. This avoids needing a hypothesis `x ≠ y`.

In fact, this definition would work perfectly well for a set of non-continuous functions,
but as the only current use case is in the Stone-Weierstrass theorem,
writing it this way avoids having to deal with casts inside the set.
(This may need to change if we do Stone-Weierstrass on non-compact spaces,
where the functions would be continuous functions vanishing at infinity.)
-/
def Set.SeparatesPointsStrongly (s : Set C(α, 𝕜)) : Prop :=
  ∀ (v : α → 𝕜) (x y : α), ∃ f : s, (f x : 𝕜) = v x ∧ f y = v y
#align set.separates_points_strongly Set.SeparatesPointsStrongly

variable [Field 𝕜] [TopologicalRing 𝕜]

/-- Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
theorem Subalgebra.SeparatesPoints.strongly {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints) :
    (s : Set C(α, 𝕜)).SeparatesPointsStrongly := fun v x y =>
  by
  by_cases n : x = y
  · subst n
    use (v x • 1 : C(α, 𝕜))
    · apply s.smul_mem
      apply s.one_mem
    · simp [coeFn_coe_base']
  obtain ⟨f, ⟨f, ⟨m, rfl⟩⟩, w⟩ := h n
  replace w : f x - f y ≠ 0 := sub_ne_zero_of_ne w
  let a := v x
  let b := v y
  let f' := ((b - a) * (f x - f y)⁻¹) • (ContinuousMap.c (f x) - f) + ContinuousMap.c a
  refine' ⟨⟨f', _⟩, _, _⟩
  · simp only [f', SetLike.mem_coe, Subalgebra.mem_toSubmodule]
    -- TODO should there be a tactic for this?
    -- We could add an attribute `@[subobject_mem]`, and a tactic
    -- ``def subobject_mem := `[solve_by_elim with subobject_mem { max_depth := 10 }]``
    solve_by_elim (config := { max_depth := 6 }) [Subalgebra.add_mem, Subalgebra.smul_mem,
      Subalgebra.sub_mem, Subalgebra.algebraMap_mem]
  · simp [f', coeFn_coe_base']
  · simp [f', coeFn_coe_base', inv_mul_cancel_right₀ w]
#align subalgebra.separates_points.strongly Subalgebra.SeparatesPoints.strongly

end ContinuousMap

instance ContinuousMap.subsingleton_subalgebra (α : Type _) [TopologicalSpace α] (R : Type _)
    [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R] [Subsingleton α] :
    Subsingleton (Subalgebra R C(α, R)) := by
  fconstructor
  intro s₁ s₂
  by_cases n : Nonempty α
  · obtain ⟨x⟩ := n
    ext f
    have h : f = algebraMap R C(α, R) (f x) := by
      ext x'
      simp only [mul_one, Algebra.id.smul_eq_mul, algebraMap_apply]
      congr
    rw [h]
    simp only [Subalgebra.algebraMap_mem]
  · ext f
    have h : f = 0 := by
      ext x'
      exact False.elim (n ⟨x'⟩)
    subst h
    simp only [Subalgebra.zero_mem]
#align continuous_map.subsingleton_subalgebra ContinuousMap.subsingleton_subalgebra

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `R`. -/


namespace ContinuousMap

instance hasSmul' {α : Type _} [TopologicalSpace α] {R : Type _} [Semiring R] [TopologicalSpace R]
    {M : Type _} [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousSMul R M] :
    SMul C(α, R) C(α, M) :=
  ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩
#align continuous_map.has_smul' ContinuousMap.hasSmul'

instance module' {α : Type _} [TopologicalSpace α] (R : Type _) [Semiring R] [TopologicalSpace R]
    [TopologicalSemiring R] (M : Type _) [TopologicalSpace M] [AddCommMonoid M] [ContinuousAdd M]
    [Module R M] [ContinuousSMul R M] : Module C(α, R) C(α, M)
    where
  smul := (· • ·)
  smul_add c f g := by ext x <;> exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x <;> exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x <;> exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x <;> exact one_smul R (f x)
  zero_smul f := by ext x <;> exact zero_smul _ _
  smul_zero r := by ext x <;> exact smul_zero _
#align continuous_map.module' ContinuousMap.module'

end ContinuousMap

end ModuleOverContinuousFunctions

/-!
We now provide formulas for `f ⊓ g` and `f ⊔ g`, where `f g : C(α, β)`,
in terms of `continuous_map.abs`.
-/


section

variable {R : Type _} [LinearOrderedField R]

-- TODO:
-- This lemma (and the next) could go all the way back in `algebra.order.field`,
-- except that it is tedious to prove without tactics.
-- Rather than stranding it at some intermediate location,
-- it's here, immediately prior to the point of use.
theorem min_eq_half_add_sub_abs_sub {x y : R} : min x y = 2⁻¹ * (x + y - |x - y|) := by
  cases' le_total x y with h h <;> field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two] <;> abel
#align min_eq_half_add_sub_abs_sub min_eq_half_add_sub_abs_sub

theorem max_eq_half_add_add_abs_sub {x y : R} : max x y = 2⁻¹ * (x + y + |x - y|) := by
  cases' le_total x y with h h <;> field_simp [h, abs_of_nonneg, abs_of_nonpos, mul_two] <;> abel
#align max_eq_half_add_add_abs_sub max_eq_half_add_add_abs_sub

end

namespace ContinuousMap

section Lattice

variable {α : Type _} [TopologicalSpace α]

variable {β : Type _} [LinearOrderedField β] [TopologicalSpace β] [OrderTopology β]
  [TopologicalRing β]

theorem inf_eq (f g : C(α, β)) : f ⊓ g = (2⁻¹ : β) • (f + g - |f - g|) :=
  ext fun x => by simpa using min_eq_half_add_sub_abs_sub
#align continuous_map.inf_eq ContinuousMap.inf_eq

-- Not sure why this is grosser than `inf_eq`:
theorem sup_eq (f g : C(α, β)) : f ⊔ g = (2⁻¹ : β) • (f + g + |f - g|) :=
  ext fun x => by simpa [mul_add] using @max_eq_half_add_add_abs_sub _ _ (f x) (g x)
#align continuous_map.sup_eq ContinuousMap.sup_eq

end Lattice

/-!
### Star structure

If `β` has a continuous star operation, we put a star structure on `C(α, β)` by using the
star operation pointwise.

If `β` is a ⋆-ring, then `C(α, β)` inherits a ⋆-ring structure.

If `β` is a ⋆-ring and a ⋆-module over `R`, then the space of continuous functions from `α` to `β`
is a ⋆-module over `R`.

-/


section StarStructure

variable {R α β : Type _}

variable [TopologicalSpace α] [TopologicalSpace β]

section Star

variable [Star β] [ContinuousStar β]

instance : Star C(α, β) where unit f := starContinuousMap.comp f

@[simp]
theorem coe_star (f : C(α, β)) : ⇑(star f) = star f :=
  rfl
#align continuous_map.coe_star ContinuousMap.coe_star

@[simp]
theorem star_apply (f : C(α, β)) (x : α) : star f x = star (f x) :=
  rfl
#align continuous_map.star_apply ContinuousMap.star_apply

end Star

instance [InvolutiveStar β] [ContinuousStar β] : InvolutiveStar C(α, β)
    where star_involutive f := ext fun x => star_star _

instance [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [ContinuousStar β] :
    StarAddMonoid C(α, β) where star_add f g := ext fun x => star_add _ _

instance [Semigroup β] [ContinuousMul β] [StarSemigroup β] [ContinuousStar β] :
    StarSemigroup C(α, β) where star_mul f g := ext fun x => star_mul _ _

instance [NonUnitalSemiring β] [TopologicalSemiring β] [StarRing β] [ContinuousStar β] :
    StarRing C(α, β) :=
  { ContinuousMap.starAddMonoid with }

instance [Star R] [Star β] [SMul R β] [StarModule R β] [ContinuousStar β]
    [ContinuousConstSMul R β] : StarModule R C(α, β)
    where star_smul k f := ext fun x => star_smul _ _

end StarStructure

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (𝕜 : Type _) [CommSemiring 𝕜]

variable (A : Type _) [TopologicalSpace A] [Semiring A] [TopologicalSemiring A] [StarRing A]

variable [ContinuousStar A] [Algebra 𝕜 A]

/-- The functorial map taking `f : C(X, Y)` to `C(Y, A) →⋆ₐ[𝕜] C(X, A)` given by pre-composition
with the continuous function `f`. See `continuous_map.comp_monoid_hom'` and
`continuous_map.comp_add_monoid_hom'`, `continuous_map.comp_right_alg_hom` for bundlings of
pre-composition into a `monoid_hom`, an `add_monoid_hom` and an `alg_hom`, respectively, under
suitable assumptions on `A`. -/
@[simps]
def compStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A)
    where
  toFun g := g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp _
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
#align continuous_map.comp_star_alg_hom' ContinuousMap.compStarAlgHom'

/-- `continuous_map.comp_star_alg_hom'` sends the identity continuous map to the identity
`star_alg_hom` -/
theorem compStarAlgHom'_id : compStarAlgHom' 𝕜 A (ContinuousMap.id X) = StarAlgHom.id 𝕜 C(X, A) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
#align continuous_map.comp_star_alg_hom'_id ContinuousMap.compStarAlgHom'_id

/-- `continuous_map.comp_star_alg_hom` is functorial. -/
theorem compStarAlgHom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compStarAlgHom' 𝕜 A (g.comp f) = (compStarAlgHom' 𝕜 A f).comp (compStarAlgHom' 𝕜 A g) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
#align continuous_map.comp_star_alg_hom'_comp ContinuousMap.compStarAlgHom'_comp

section Periodicity

/-! ### Summing translates of a function -/


/-- Summing the translates of `f` by `ℤ • p` gives a map which is periodic with period `p`.
(This is true without any convergence conditions, since if the sum doesn't converge it is taken to
be the zero map, which is periodic.) -/
theorem periodic_tsum_comp_add_zsmul [LocallyCompactSpace X] [AddCommGroup X]
    [TopologicalAddGroup X] [AddCommMonoid Y] [ContinuousAdd Y] [T2Space Y] (f : C(X, Y)) (p : X) :
    Function.Periodic (⇑(∑' n : ℤ, f.comp (ContinuousMap.addRight (n • p)))) p :=
  by
  intro x
  by_cases h : Summable fun n : ℤ => f.comp (ContinuousMap.addRight (n • p))
  · convert congr_arg (fun f : C(X, Y) => f x) ((Equiv.addRight (1 : ℤ)).tsum_eq _) using 1
    simp_rw [← tsum_apply h, ← tsum_apply ((Equiv.addRight (1 : ℤ)).summable_iff.mpr h),
      Equiv.coe_addRight, comp_apply, coe_add_right, add_one_zsmul, add_comm (_ • p) p, ← add_assoc]
  · rw [tsum_eq_zero_of_not_summable h]
    simp only [coe_zero, Pi.zero_apply]
#align continuous_map.periodic_tsum_comp_add_zsmul ContinuousMap.periodic_tsum_comp_add_zsmul

end Periodicity

end ContinuousMap

namespace Homeomorph

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y]

variable (𝕜 : Type _) [CommSemiring 𝕜]

variable (A : Type _) [TopologicalSpace A] [Semiring A] [TopologicalSemiring A] [StarRing A]

variable [ContinuousStar A] [Algebra 𝕜 A]

/-- `continuous_map.comp_star_alg_hom'` as a `star_alg_equiv` when the continuous map `f` is
actually a homeomorphism. -/
@[simps]
def compStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
  {
    f.toContinuousMap.compStarAlgHom' 𝕜
      A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        to_continuous_map_comp_symm, ContinuousMap.comp_id]
    right_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        symm_comp_to_continuous_map, ContinuousMap.comp_id]
    map_smul' := fun k a => map_smul (f.toContinuousMap.compStarAlgHom' 𝕜 A) k a }
#align homeomorph.comp_star_alg_equiv' Homeomorph.compStarAlgEquiv'

end Homeomorph

