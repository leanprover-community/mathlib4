/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Nicolò Cavalleri
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Algebraic structures over continuous functions

In this file we define instances of algebraic structures over the type `ContinuousMap α β`
(denoted `C(α, β)`) of **bundled** continuous maps from `α` to `β`. For example, `C(α, β)`
is a group when `β` is a group, a ring when `β` is a ring, etc.

For each type of algebraic structure, we also define an appropriate subobject of `α → β`
with carrier `{ f : α → β | Continuous f }`. For example, when `β` is a group, a subgroup
`continuousSubgroup α β` of `α → β` is constructed with carrier `{ f : α → β | Continuous f }`.

Note that, rather than using the derived algebraic structures on these subobjects
(for example, when `β` is a group, the derived group structure on `continuousSubgroup α β`),
one should use `C(α, β)` with the appropriate instance of the structure.
-/

assert_not_exists StoneCech

--attribute [elab_without_expected_type] Continuous.comp

namespace ContinuousFunctions

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {f g : { f : α → β | Continuous f }}

instance : CoeFun { f : α → β | Continuous f } fun _ => α → β :=
  ⟨Subtype.val⟩

end ContinuousFunctions

namespace ContinuousMap

variable {α : Type*} {β : Type*} {γ : Type*}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-! ### `mul` and `add` -/

@[to_additive]
instance instMul [Mul β] [ContinuousMul β] : Mul C(α, β) :=
  ⟨fun f g => ⟨f * g, continuous_mul.comp (f.continuous.prodMk g.continuous :)⟩⟩

@[to_additive (attr := norm_cast, simp)]
theorem coe_mul [Mul β] [ContinuousMul β] (f g : C(α, β)) : ⇑(f * g) = f * g :=
  rfl

@[to_additive (attr := simp)]
theorem mul_apply [Mul β] [ContinuousMul β] (f g : C(α, β)) (x : α) : (f * g) x = f x * g x :=
  rfl

@[to_additive (attr := simp)]
theorem mul_comp [Mul γ] [ContinuousMul γ] (f₁ f₂ : C(β, γ)) (g : C(α, β)) :
    (f₁ * f₂).comp g = f₁.comp g * f₂.comp g :=
  rfl

/-! ### `one` -/

@[to_additive]
instance [One β] : One C(α, β) :=
  ⟨const α 1⟩

@[to_additive (attr := norm_cast, simp)]
theorem coe_one [One β] : ⇑(1 : C(α, β)) = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem one_apply [One β] (x : α) : (1 : C(α, β)) x = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem one_comp [One γ] (g : C(α, β)) : (1 : C(β, γ)).comp g = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem comp_one [One β] (g : C(β, γ)) : g.comp (1 : C(α, β)) = const α (g 1) := rfl

@[to_additive (attr := simp)]
theorem const_one [One β] : const α (1 : β) = 1 := rfl

/-! ### `Nat.cast` -/

instance [NatCast β] : NatCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
theorem coe_natCast [NatCast β] (n : ℕ) : ((n : C(α, β)) : α → β) = n :=
  rfl

@[simp]
theorem natCast_apply [NatCast β] (n : ℕ) (x : α) : (n : C(α, β)) x = n :=
  rfl

/-! ### `Int.cast` -/

instance [IntCast β] : IntCast C(α, β) :=
  ⟨fun n => ContinuousMap.const _ n⟩

@[simp, norm_cast]
theorem coe_intCast [IntCast β] (n : ℤ) : ((n : C(α, β)) : α → β) = n :=
  rfl

@[simp]
theorem intCast_apply [IntCast β] (n : ℤ) (x : α) : (n : C(α, β)) x = n :=
  rfl

/-! ### `nsmul` and `pow` -/

instance instNSMul [AddMonoid β] [ContinuousAdd β] : SMul ℕ C(α, β) :=
  ⟨fun n f => ⟨n • ⇑f, f.continuous.nsmul n⟩⟩

@[to_additive existing]
instance instPow [Monoid β] [ContinuousMul β] : Pow C(α, β) ℕ :=
  ⟨fun f n => ⟨(⇑f) ^ n, f.continuous.pow n⟩⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
theorem coe_pow [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) : ⇑(f ^ n) = (⇑f) ^ n :=
  rfl

@[to_additive (attr := norm_cast)]
theorem pow_apply [Monoid β] [ContinuousMul β] (f : C(α, β)) (n : ℕ) (x : α) :
    (f ^ n) x = f x ^ n :=
  rfl

-- Don't make auto-generated `coe_nsmul` and `nsmul_apply` simp, as the linter complains they're
-- redundant w.r.t. `coe_smul`
attribute [simp] coe_pow pow_apply

@[to_additive]
theorem pow_comp [Monoid γ] [ContinuousMul γ] (f : C(β, γ)) (n : ℕ) (g : C(α, β)) :
    (f ^ n).comp g = f.comp g ^ n :=
  rfl

-- Don't make `nsmul_comp` simp as the linter complains it's redundant w.r.t. `smul_comp`
attribute [simp] pow_comp

/-! ### `inv` and `neg` -/

@[to_additive]
instance [Inv β] [ContinuousInv β] : Inv C(α, β) where inv f := ⟨f⁻¹, f.continuous.inv⟩

@[to_additive (attr := simp)]
theorem coe_inv [Inv β] [ContinuousInv β] (f : C(α, β)) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_apply [Inv β] [ContinuousInv β] (f : C(α, β)) (x : α) : f⁻¹ x = (f x)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
theorem inv_comp [Inv γ] [ContinuousInv γ] (f : C(β, γ)) (g : C(α, β)) :
    f⁻¹.comp g = (f.comp g)⁻¹ :=
  rfl

/-! ### `div` and `sub` -/

@[to_additive]
instance [Div β] [ContinuousDiv β] : Div C(α, β) where
  div f g := ⟨f / g, f.continuous.div' g.continuous⟩

@[to_additive (attr := norm_cast, simp)]
theorem coe_div [Div β] [ContinuousDiv β] (f g : C(α, β)) : ⇑(f / g) = f / g :=
  rfl

@[to_additive (attr := simp)]
theorem div_apply [Div β] [ContinuousDiv β] (f g : C(α, β)) (x : α) : (f / g) x = f x / g x :=
  rfl

@[to_additive (attr := simp)]
theorem div_comp [Div γ] [ContinuousDiv γ] (f g : C(β, γ)) (h : C(α, β)) :
    (f / g).comp h = f.comp h / g.comp h :=
  rfl

/-! ### `zpow` and `zsmul` -/

instance instZSMul [AddGroup β] [IsTopologicalAddGroup β] : SMul ℤ C(α, β) where
  smul z f := ⟨z • ⇑f, f.continuous.zsmul z⟩

@[to_additive existing]
instance instZPow [Group β] [IsTopologicalGroup β] : Pow C(α, β) ℤ where
  pow f z := ⟨(⇑f) ^ z, f.continuous.zpow z⟩

@[to_additive (attr := norm_cast) (reorder := 7 8)]
theorem coe_zpow [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : ℤ) : ⇑(f ^ z) = (⇑f) ^ z :=
  rfl

@[to_additive]
theorem zpow_apply [Group β] [IsTopologicalGroup β] (f : C(α, β)) (z : ℤ) (x : α) :
    (f ^ z) x = f x ^ z :=
  rfl

-- Don't make auto-generated `coe_zsmul` and `zsmul_apply` simp as the linter complains they're
-- redundant w.r.t. `coe_smul`
attribute [simp] coe_zpow zpow_apply

@[to_additive]
theorem zpow_comp [Group γ] [IsTopologicalGroup γ] (f : C(β, γ)) (z : ℤ) (g : C(α, β)) :
    (f ^ z).comp g = f.comp g ^ z :=
  rfl

-- Don't make `zsmul_comp` simp as the linter complains it's redundant w.r.t. `smul_comp`
attribute [simp] zpow_comp

end ContinuousMap

section GroupStructure

/-!
### Group structure

In this section we show that continuous functions valued in a topological group inherit
the structure of a group.
-/


section Subtype

/-- The `Submonoid` of continuous maps `α → β`. -/
@[to_additive /-- The `AddSubmonoid` of continuous maps `α → β`. -/]
def continuousSubmonoid (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β]
    [MulOneClass β] [ContinuousMul β] : Submonoid (α → β) where
  carrier := { f : α → β | Continuous f }
  one_mem' := @continuous_const _ _ _ _ 1
  mul_mem' fc gc := fc.mul gc

/-- The subgroup of continuous maps `α → β`. -/
@[to_additive /-- The `AddSubgroup` of continuous maps `α → β`. -/]
def continuousSubgroup (α : Type*) (β : Type*) [TopologicalSpace α] [TopologicalSpace β] [Group β]
    [IsTopologicalGroup β] : Subgroup (α → β) :=
  { continuousSubmonoid α β with inv_mem' := fun fc => Continuous.inv fc }

end Subtype

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

@[to_additive]
instance [Semigroup β] [ContinuousMul β] : Semigroup C(α, β) :=
  coe_injective.semigroup _ coe_mul

@[to_additive]
instance [CommSemigroup β] [ContinuousMul β] : CommSemigroup C(α, β) :=
  coe_injective.commSemigroup _ coe_mul

@[to_additive]
instance [MulOneClass β] [ContinuousMul β] : MulOneClass C(α, β) :=
  coe_injective.mulOneClass _ coe_one coe_mul

instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C(α, β) :=
  coe_injective.mulZeroClass _ coe_zero coe_mul

instance [SemigroupWithZero β] [ContinuousMul β] : SemigroupWithZero C(α, β) :=
  coe_injective.semigroupWithZero _ coe_zero coe_mul

@[to_additive]
instance [Monoid β] [ContinuousMul β] : Monoid C(α, β) :=
  coe_injective.monoid _ coe_one coe_mul coe_pow

instance [MonoidWithZero β] [ContinuousMul β] : MonoidWithZero C(α, β) :=
  coe_injective.monoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [CommMonoid β] [ContinuousMul β] : CommMonoid C(α, β) :=
  coe_injective.commMonoid _ coe_one coe_mul coe_pow

instance [CommMonoidWithZero β] [ContinuousMul β] : CommMonoidWithZero C(α, β) :=
  coe_injective.commMonoidWithZero _ coe_zero coe_one coe_mul coe_pow

@[to_additive]
instance [LocallyCompactSpace α] [Mul β] [ContinuousMul β] : ContinuousMul C(α, β) :=
  ⟨by
    refine continuous_of_continuous_uncurry _ ?_
    have h1 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.fst x.snd :=
      continuous_eval.comp (continuous_fst.prodMap continuous_id)
    have h2 : Continuous fun x : (C(α, β) × C(α, β)) × α => x.fst.snd x.snd :=
      continuous_eval.comp (continuous_snd.prodMap continuous_id)
    exact h1.mul h2⟩

/-- Coercion to a function as a `MonoidHom`. Similar to `MonoidHom.coeFn`. -/
@[to_additive (attr := simps)
  /-- Coercion to a function as an `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`. -/]
def coeFnMonoidHom [Monoid β] [ContinuousMul β] : C(α, β) →* α → β where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

variable (α) in
/-- Composition on the left by a (continuous) homomorphism of topological monoids, as a
`MonoidHom`. Similar to `MonoidHom.compLeft`. -/
@[to_additive (attr := simps)
/-- Composition on the left by a (continuous) homomorphism of topological `AddMonoid`s, as an
`AddMonoidHom`. Similar to `AddMonoidHom.comp_left`. -/]
protected def _root_.MonoidHom.compLeftContinuous {γ : Type*} [Monoid β] [ContinuousMul β]
    [TopologicalSpace γ] [Monoid γ] [ContinuousMul γ] (g : β →* γ) (hg : Continuous g) :
    C(α, β) →* C(α, γ) where
  toFun f := (⟨g, hg⟩ : C(β, γ)).comp f
  map_one' := ext fun _ => g.map_one
  map_mul' _ _ := ext fun _ => g.map_mul _ _

/-- Composition on the right as a `MonoidHom`. Similar to `MonoidHom.compHom'`. -/
@[to_additive (attr := simps)
      /-- Composition on the right as an `AddMonoidHom`. Similar to `AddMonoidHom.compHom'`. -/]
def compMonoidHom' {γ : Type*} [TopologicalSpace γ] [MulOneClass γ] [ContinuousMul γ]
    (g : C(α, β)) : C(β, γ) →* C(α, γ) where
  toFun f := f.comp g
  map_one' := one_comp g
  map_mul' f₁ f₂ := mul_comp f₁ f₂ g

@[to_additive (attr := simp)]
theorem coe_prod [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι → C(α, β)) :
    ⇑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : α → β) :=
  map_prod coeFnMonoidHom f s

@[to_additive]
theorem prod_apply [CommMonoid β] [ContinuousMul β] {ι : Type*} (s : Finset ι) (f : ι → C(α, β))
    (a : α) : (∏ i ∈ s, f i) a = ∏ i ∈ s, f i a := by simp

@[to_additive]
instance [Group β] [IsTopologicalGroup β] : Group C(α, β) :=
  coe_injective.group _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance instCommGroupContinuousMap [CommGroup β] [IsTopologicalGroup β] : CommGroup C(α, β) :=
  coe_injective.commGroup _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

@[to_additive]
instance [CommGroup β] [IsTopologicalGroup β] : IsTopologicalGroup C(α, β) where
  continuous_mul := by
    letI : UniformSpace β := IsTopologicalGroup.toUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    rintro ⟨f, g⟩
    rw [ContinuousAt, tendsto_iff_forall_isCompact_tendstoUniformlyOn, nhds_prod_eq]
    exact fun K hK =>
      uniformContinuous_mul.comp_tendstoUniformlyOn
        ((tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK).prodMk
          (tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK))
  continuous_inv := by
    letI : UniformSpace β := IsTopologicalGroup.toUniformSpace β
    have : IsUniformGroup β := isUniformGroup_of_commGroup
    rw [continuous_iff_continuousAt]
    intro f
    rw [ContinuousAt, tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    exact fun K hK =>
      uniformContinuous_inv.comp_tendstoUniformlyOn
        (tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp Filter.tendsto_id K hK)

/-- If an infinite product of functions in `C(α, β)` converges to `g`
(for the compact-open topology), then the pointwise product converges to `g x` for all `x ∈ α`. -/
@[to_additive
  /-- If an infinite sum of functions in `C(α, β)` converges to `g` (for the compact-open topology),
then the pointwise sum converges to `g x` for all `x ∈ α`. -/]
theorem hasProd_apply {γ : Type*} [CommMonoid β] [ContinuousMul β]
    {f : γ → C(α, β)} {g : C(α, β)} (hf : HasProd f g) (x : α) :
    HasProd (fun i : γ => f i x) (g x) := by
  let ev : C(α, β) →* β := (Pi.evalMonoidHom _ x).comp coeFnMonoidHom
  exact hf.map ev (continuous_eval_const x)

@[to_additive]
theorem multipliable_apply [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ → C(α, β)}
    (hf : Multipliable f) (x : α) : Multipliable fun i : γ => f i x :=
  (hasProd_apply hf.hasProd x).multipliable

@[to_additive]
theorem tprod_apply [T2Space β] [CommMonoid β] [ContinuousMul β] {γ : Type*} {f : γ → C(α, β)}
    (hf : Multipliable f) (x : α) :
    ∏' i : γ, f i x = (∏' i : γ, f i) x :=
  (hasProd_apply hf.hasProd x).tprod_eq

end ContinuousMap

end GroupStructure

section RingStructure

/-!
### Ring structure

In this section we show that continuous functions valued in a topological semiring `R` inherit
the structure of a ring.
-/


section Subtype

/-- The subsemiring of continuous maps `α → β`. -/
def continuousSubsemiring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R]
    [NonAssocSemiring R] [IsTopologicalSemiring R] : Subsemiring (α → R) :=
  { continuousAddSubmonoid α R, continuousSubmonoid α R with }

/-- The subring of continuous maps `α → β`. -/
def continuousSubring (α : Type*) (R : Type*) [TopologicalSpace α] [TopologicalSpace R] [Ring R]
    [IsTopologicalRing R] : Subring (α → R) :=
  { continuousAddSubgroup α R, continuousSubsemiring α R with }

end Subtype

namespace ContinuousMap

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] : NonUnitalNonAssocSemiring C(α, β) :=
  coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalSemiring β]
    [IsTopologicalSemiring β] : NonUnitalSemiring C(α, β) :=
  coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [AddMonoidWithOne β]
    [ContinuousAdd β] : AddMonoidWithOne C(α, β) :=
  coe_injective.addMonoidWithOne _ coe_zero coe_one coe_add coe_nsmul coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonAssocSemiring β]
    [IsTopologicalSemiring β] : NonAssocSemiring C(α, β) :=
  coe_injective.nonAssocSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [IsTopologicalSemiring β] : Semiring C(α, β) :=
  coe_injective.semiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalNonAssocRing β] [IsTopologicalRing β] : NonUnitalNonAssocRing C(α, β) :=
  coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalRing β]
    [IsTopologicalRing β] : NonUnitalRing C(α, β) :=
  coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonAssocRing β]
    [IsTopologicalRing β] : NonAssocRing C(α, β) :=
  coe_injective.nonAssocRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_natCast coe_intCast

instance instRing {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Ring β]
    [IsTopologicalRing β] : Ring C(α, β) :=
  coe_injective.ring _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul coe_pow
    coe_natCast coe_intCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [NonUnitalCommSemiring β] [IsTopologicalSemiring β] : NonUnitalCommSemiring C(α, β) :=
  coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul coe_nsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CommSemiring β]
    [IsTopologicalSemiring β] : CommSemiring C(α, β) :=
  coe_injective.commSemiring _ coe_zero coe_one coe_add coe_mul coe_nsmul coe_pow coe_natCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [NonUnitalCommRing β]
    [IsTopologicalRing β] : NonUnitalCommRing C(α, β) :=
  coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CommRing β]
    [IsTopologicalRing β] : CommRing C(α, β) :=
  coe_injective.commRing _ coe_zero coe_one coe_add coe_mul coe_neg coe_sub coe_nsmul coe_zsmul
    coe_pow coe_natCast coe_intCast

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [LocallyCompactSpace α]
    [NonUnitalSemiring β] [IsTopologicalSemiring β] : IsTopologicalSemiring C(α, β) where

instance {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [LocallyCompactSpace α]
    [NonUnitalRing β] [IsTopologicalRing β] : IsTopologicalRing C(α, β) where

/-- Composition on the left by a (continuous) homomorphism of topological semirings, as a
`RingHom`.  Similar to `RingHom.compLeft`. -/
@[simps!]
protected def _root_.RingHom.compLeftContinuous (α : Type*) {β : Type*} {γ : Type*}
    [TopologicalSpace α]
    [TopologicalSpace β] [Semiring β] [IsTopologicalSemiring β] [TopologicalSpace γ] [Semiring γ]
    [IsTopologicalSemiring γ] (g : β →+* γ) (hg : Continuous g) : C(α, β) →+* C(α, γ) :=
  { g.toMonoidHom.compLeftContinuous α hg, g.toAddMonoidHom.compLeftContinuous α hg with }

/-- Coercion to a function as a `RingHom`. -/
@[simps!]
def coeFnRingHom {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Semiring β]
    [IsTopologicalSemiring β] : C(α, β) →+* α → β :=
  { (coeFnMonoidHom : C(α, β) →* _),
    (coeFnAddMonoidHom : C(α, β) →+ _) with }

end ContinuousMap

end RingStructure

attribute [local ext] Subtype.eq

section ModuleStructure

/-!
### Module structure

In this section we show that continuous functions valued in a topological module `M` over a
topological semiring `R` inherit the structure of a module.
-/


section Subtype

variable (α : Type*) [TopologicalSpace α]
variable (R : Type*) [Semiring R]
variable (M : Type*) [TopologicalSpace M] [AddCommGroup M]
variable [Module R M] [ContinuousConstSMul R M] [IsTopologicalAddGroup M]

/-- The `R`-submodule of continuous maps `α → M`. -/
def continuousSubmodule : Submodule R (α → M) :=
  { continuousAddSubgroup α M with
    carrier := { f : α → M | Continuous f }
    smul_mem' := fun c _ hf => hf.const_smul c }

end Subtype

namespace ContinuousMap

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {R R₁ : Type*} {M : Type*}
  [TopologicalSpace M] {M₂ : Type*} [TopologicalSpace M₂]

@[to_additive]
instance instSMul [SMul R M] [ContinuousConstSMul R M] : SMul R C(α, M) :=
  ⟨fun r f => ⟨r • ⇑f, f.continuous.const_smul r⟩⟩

@[to_additive]
instance [SMul R M] [ContinuousConstSMul R M] : ContinuousConstSMul R C(α, M) where
  continuous_const_smul r := continuous_postcomp ⟨_, continuous_const_smul r⟩

@[to_additive]
instance [TopologicalSpace R] [SMul R M] [ContinuousSMul R M] :
    ContinuousSMul R C(α, M) :=
  ⟨(continuous_postcomp ⟨_, continuous_smul⟩).comp continuous_prodMk_const⟩

@[to_additive (attr := simp, norm_cast)]
theorem coe_smul [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) : ⇑(c • f) = c • ⇑f :=
  rfl

@[to_additive]
theorem smul_apply [SMul R M] [ContinuousConstSMul R M] (c : R) (f : C(α, M)) (a : α) :
    (c • f) a = c • f a :=
  rfl

@[to_additive (attr := simp)]
theorem smul_comp [SMul R M] [ContinuousConstSMul R M] (r : R) (f : C(β, M)) (g : C(α, β)) :
    (r • f).comp g = r • f.comp g :=
  rfl

@[to_additive]
instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M]
    [SMulCommClass R R₁ M] : SMulCommClass R R₁ C(α, M) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

instance [SMul R M] [ContinuousConstSMul R M] [SMul R₁ M] [ContinuousConstSMul R₁ M] [SMul R R₁]
    [IsScalarTower R R₁ M] : IsScalarTower R R₁ C(α, M) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

instance [SMul R M] [SMul Rᵐᵒᵖ M] [ContinuousConstSMul R M] [IsCentralScalar R M] :
    IsCentralScalar R C(α, M) where op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [IsScalarTower R M M] :
    IsScalarTower R C(α, M) C(α, M) where
  smul_assoc _ _ _ := ext fun _ => smul_mul_assoc ..

instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass R M M] :
    SMulCommClass R C(α, M) C(α, M) where
  smul_comm _ _ _ := ext fun _ => (mul_smul_comm ..).symm

instance [SMul R M] [ContinuousConstSMul R M] [Mul M] [ContinuousMul M] [SMulCommClass M R M] :
    SMulCommClass C(α, M) R C(α, M) where
  smul_comm _ _ _ := ext fun _ => smul_comm (_ : M) ..

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

variable (R)

/-- Composition on the left by a continuous linear map, as a `ContinuousLinearMap`.
Similar to `LinearMap.compLeft`. -/
@[simps]
protected def _root_.ContinuousLinearMap.compLeftContinuous (α : Type*) [TopologicalSpace α]
    (g : M →L[R] M₂) : C(α, M) →L[R] C(α, M₂) where
  __ := g.toLinearMap.toAddMonoidHom.compLeftContinuous α g.continuous
  map_smul' := fun c _ => ext fun _ => g.map_smul' c _
  cont := ContinuousMap.continuous_postcomp _

/-- The constant map `x ↦ y ↦ x` as a `ContinuousLinearMap`. -/
@[simps!]
def _root_.ContinuousLinearMap.const (α : Type*) [TopologicalSpace α] : M →L[R] C(α, M) where
  toFun m := .const α m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_const'

/-- Coercion to a function as a `LinearMap`. -/
@[simps]
def coeFnLinearMap : C(α, M) →ₗ[R] α → M :=
  { (coeFnAddMonoidHom : C(α, M) →+ _) with
    map_smul' := coe_smul }

/-- Evaluation at a point, as a continuous linear map. -/
@[simps apply]
def evalCLM (x : α) : C(α, M) →L[R] M where
  toFun f := f x
  map_add' _ _ := add_apply _ _ x
  map_smul' _ _ := smul_apply _ _ x

end ContinuousMap

end ModuleStructure

section AlgebraStructure

/-!
### Algebra structure

In this section we show that continuous functions valued in a topological algebra `A` over a ring
`R` inherit the structure of an algebra. Note that the hypothesis that `A` is a topological algebra
is obtained by requiring that `A` be both a `ContinuousSMul` and a `IsTopologicalSemiring`. -/


section Subtype

variable {α : Type*} [TopologicalSpace α] {R : Type*} [CommSemiring R] {A : Type*}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [IsTopologicalSemiring A]

/-- The `R`-subalgebra of continuous maps `α → A`. -/
def continuousSubalgebra : Subalgebra R (α → A) :=
  { continuousSubsemiring α A with
    carrier := { f : α → A | Continuous f }
    algebraMap_mem' := fun r => (continuous_const : Continuous fun _ : α => algebraMap R A r) }

end Subtype

section ContinuousMap

variable {α : Type*} [TopologicalSpace α] {R : Type*} [CommSemiring R] {A : Type*}
  [TopologicalSpace A] [Semiring A] [Algebra R A] [IsTopologicalSemiring A] {A₂ : Type*}
  [TopologicalSpace A₂] [Semiring A₂] [Algebra R A₂] [IsTopologicalSemiring A₂]

/-- Continuous constant functions as a `RingHom`. -/
def ContinuousMap.C : R →+* C(α, A) where
  toFun := fun c : R => ⟨fun _ : α => (algebraMap R A) c, continuous_const⟩
  map_one' := by ext _; exact (algebraMap R A).map_one
  map_mul' c₁ c₂ := by ext _; exact (algebraMap R A).map_mul _ _
  map_zero' := by ext _; exact (algebraMap R A).map_zero
  map_add' c₁ c₂ := by ext _; exact (algebraMap R A).map_add _ _

@[simp]
theorem ContinuousMap.C_apply (r : R) (a : α) : ContinuousMap.C r a = algebraMap R A r :=
  rfl

instance ContinuousMap.algebra : Algebra R C(α, A) where
  algebraMap := ContinuousMap.C
  commutes' c f := by ext x; exact Algebra.commutes' _ _
  smul_def' c f := by ext x; exact Algebra.smul_def' _ _

variable (R)

/-- Composition on the left by a (continuous) homomorphism of topological `R`-algebras, as an
`AlgHom`. Similar to `AlgHom.compLeft`. -/
@[simps!]
protected def AlgHom.compLeftContinuous {α : Type*} [TopologicalSpace α] (g : A →ₐ[R] A₂)
    (hg : Continuous g) : C(α, A) →ₐ[R] C(α, A₂) :=
  { g.toRingHom.compLeftContinuous α hg with
    commutes' := fun _ => ContinuousMap.ext fun _ => g.commutes' _ }

variable (A)

/-- Precomposition of functions into a topological semiring by a continuous map is an algebra
homomorphism. -/
@[simps]
def ContinuousMap.compRightAlgHom {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : C(α, β)) : C(β, A) →ₐ[R] C(α, A) where
  toFun g := g.comp f
  map_zero' := ext fun _ ↦ rfl
  map_add'  _ _ := ext fun _ ↦ rfl
  map_one' := ext fun _ ↦ rfl
  map_mul' _ _ := ext fun _ ↦ rfl
  commutes' _ := ext fun _ ↦ rfl

theorem ContinuousMap.compRightAlgHom_continuous {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (f : C(α, β)) : Continuous (compRightAlgHom R A f) :=
  continuous_precomp f

variable {A}

/-- Coercion to a function as an `AlgHom`. -/
@[simps!]
def ContinuousMap.coeFnAlgHom : C(α, A) →ₐ[R] α → A :=
  { (ContinuousMap.coeFnRingHom : C(α, A) →+* _) with
    commutes' := fun _ => rfl }

variable {R}

/-- A version of `Set.SeparatesPoints` for subalgebras of the continuous functions,
used for stating the Stone-Weierstrass theorem.
-/
abbrev Subalgebra.SeparatesPoints (s : Subalgebra R C(α, A)) : Prop :=
  Set.SeparatesPoints ((fun f : C(α, A) => (f : α → A)) '' (s : Set C(α, A)))

theorem Subalgebra.separatesPoints_monotone :
    Monotone fun s : Subalgebra R C(α, A) => s.SeparatesPoints := fun s s' r h x y n => by
  obtain ⟨f, m, w⟩ := h n
  rcases m with ⟨f, ⟨m, rfl⟩⟩
  exact ⟨_, ⟨f, ⟨r m, rfl⟩⟩, w⟩

@[simp]
theorem algebraMap_apply (k : R) (a : α) : algebraMap R C(α, A) k a = k • (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

variable {𝕜 : Type*} [TopologicalSpace 𝕜]
variable (s : Set C(α, 𝕜)) (f : s) (x : α)

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
  ∀ (v : α → 𝕜) (x y : α), ∃ f ∈ s, (f x : 𝕜) = v x ∧ f y = v y

variable [Field 𝕜] [IsTopologicalRing 𝕜]

/-- Working in continuous functions into a topological field,
a subalgebra of functions that separates points also separates points strongly.

By the hypothesis, we can find a function `f` so `f x ≠ f y`.
By an affine transformation in the field we can arrange so that `f x = a` and `f x = b`.
-/
theorem Subalgebra.SeparatesPoints.strongly {s : Subalgebra 𝕜 C(α, 𝕜)} (h : s.SeparatesPoints) :
    (s : Set C(α, 𝕜)).SeparatesPointsStrongly := fun v x y => by
  by_cases n : x = y
  · subst n
    exact ⟨_, (v x • (1 : s) : s).prop, mul_one _, mul_one _⟩
  obtain ⟨_, ⟨f, hf, rfl⟩, hxy⟩ := h n
  replace hxy : f x - f y ≠ 0 := sub_ne_zero_of_ne hxy
  let a := v x
  let b := v y
  let f' : s :=
    ((b - a) * (f x - f y)⁻¹) • (algebraMap _ s (f x) - (⟨f, hf⟩ : s)) + algebraMap _ s a
  refine ⟨f', f'.prop, ?_, ?_⟩
  · simp [a, b, f']
  · simp [a, b, f', inv_mul_cancel_right₀ hxy]

end ContinuousMap

instance ContinuousMap.subsingleton_subalgebra (α : Type*) [TopologicalSpace α] (R : Type*)
    [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [Subsingleton α] :
    Subsingleton (Subalgebra R C(α, R)) :=
  ⟨fun s₁ s₂ => by
    cases isEmpty_or_nonempty α
    · have : Subsingleton C(α, R) := DFunLike.coe_injective.subsingleton
      subsingleton
    · inhabit α
      ext f
      have h : f = algebraMap R C(α, R) (f default) := by
        ext x'
        simp only [mul_one, Algebra.id.smul_eq_mul, algebraMap_apply]
        congr
        simp [eq_iff_true_of_subsingleton]
      rw [h]
      simp only [Subalgebra.algebraMap_mem]⟩

end AlgebraStructure

section ModuleOverContinuousFunctions

/-!
### Structure as module over scalar functions

If `M` is a module over `R`, then we show that the space of continuous functions from `α` to `M`
is naturally a module over the ring of continuous functions from `α` to `R`. -/

namespace ContinuousMap

variable
  {α : Type*} [TopologicalSpace α]
  {R : Type*} [Semiring R] [TopologicalSpace R]
  {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousSMul R M]

instance instSMul' : SMul C(α, R) C(α, M) :=
  ⟨fun f g => ⟨fun x => f x • g x, Continuous.smul f.2 g.2⟩⟩

/-- Coercion to a function for a scalar-valued continuous map multiplying a vector-valued one
(as opposed to `ContinuousMap.coe_smul` which is multiplication by a constant scalar). -/
@[simp] lemma coe_smul' (f : C(α, R)) (g : C(α, M)) :
    ⇑(f • g) = ⇑f • ⇑g :=
  rfl

/-- Evaluation of a scalar-valued continuous map multiplying a vector-valued one
(as opposed to `ContinuousMap.smul_apply` which is multiplication by a constant scalar). -/
-- (this doesn't need to be @[simp] since it can be derived from `coe_smul'` and `Pi.smul_apply'`)
lemma smul_apply' (f : C(α, R)) (g : C(α, M)) (x : α) :
    (f • g) x = f x • g x :=
  rfl

instance module' [IsTopologicalSemiring R] [ContinuousAdd M] :
    Module C(α, R) C(α, M) where
  smul := (· • ·)
  smul_add c f g := by ext x; exact smul_add (c x) (f x) (g x)
  add_smul c₁ c₂ f := by ext x; exact add_smul (c₁ x) (c₂ x) (f x)
  mul_smul c₁ c₂ f := by ext x; exact mul_smul (c₁ x) (c₂ x) (f x)
  one_smul f := by ext x; exact one_smul R (f x)
  zero_smul f := by ext x; exact zero_smul _ _
  smul_zero r := by ext x; exact smul_zero _

end ContinuousMap

end ModuleOverContinuousFunctions

/-! ### Evaluation as a bundled map -/

variable {X : Type*} (S R : Type*) [TopologicalSpace X] [CommSemiring S] [CommSemiring R]
variable [Algebra S R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- Evaluation of continuous maps at a point, bundled as an algebra homomorphism. -/
@[simps]
def ContinuousMap.evalAlgHom (x : X) : C(X, R) →ₐ[S] R where
  toFun f := f x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
