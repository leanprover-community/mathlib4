/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Topology.Algebra.Order.Support
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Compactly supported continuous functions

In this file, we define the type `C_c(α, β)` of compactly supported continuous functions and the
class `CompactlySupportedContinuousMapClass`, and prove basic properties.

## Main definitions and results

This file contains various instances such as `Add`, `Mul`, `SMul F C_c(α, β)` when `F` is a class of
continuous functions.
When `β` has more structures, `C_c(α, β)` inherits such structures as `AddCommGroup`,
`NonUnitalRing` and `StarRing`.

When the domain `α` is compact, `CompactlySupportedContinuousMap.continuousMapEquiv`
gives the identification `C(α, β) ≃ C_c(α, β)`.

-/

@[expose] public section

variable {F α β γ : Type*} [TopologicalSpace α]

/-- `C_c(α, β)` is the type of continuous functions `α → β` with compact support from a topological
space to a topological space with a zero element.

When possible, instead of parametrizing results over `f : C_c(α, β)`,
you should parametrize over `{F : Type*} [CompactlySupportedContinuousMapClass F α β] (f : F)`.

When you extend this structure, make sure to extend `CompactlySupportedContinuousMapClass`. -/
structure CompactlySupportedContinuousMap (α β : Type*) [TopologicalSpace α] [Zero β]
    [TopologicalSpace β] extends ContinuousMap α β where
  /-- The function has compact support . -/
  hasCompactSupport' : HasCompactSupport toFun

@[inherit_doc]
scoped[CompactlySupported] notation (priority := 2000)
  "C_c(" α ", " β ")" => CompactlySupportedContinuousMap α β

@[inherit_doc]
scoped[CompactlySupported] notation α " →C_c " β => CompactlySupportedContinuousMap α β

open CompactlySupported

section

/-- `CompactlySupportedContinuousMapClass F α β` states that `F` is a type of continuous maps with
compact support.

You should also extend this typeclass when you extend `CompactlySupportedContinuousMap`. -/
class CompactlySupportedContinuousMapClass (F : Type*) (α β : outParam <| Type*)
    [TopologicalSpace α] [Zero β] [TopologicalSpace β] [FunLike F α β] : Prop
    extends ContinuousMapClass F α β where
  /-- Each member of the class has compact support. -/
  hasCompactSupport (f : F) : HasCompactSupport f

end

namespace CompactlySupportedContinuousMap

section Basics

variable [TopologicalSpace β] [Zero β]

instance : FunLike C_c(α, β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

protected lemma hasCompactSupport (f : C_c(α, β)) : HasCompactSupport f := f.hasCompactSupport'

instance : CompactlySupportedContinuousMapClass C_c(α, β) α β where
  map_continuous f := f.continuous_toFun
  hasCompactSupport f := f.hasCompactSupport'

@[simp]
theorem coe_toContinuousMap (f : C_c(α, β)) : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
theorem ext {f g : C_c(α, β)} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_mk (f : C(α, β)) (h : HasCompactSupport f) : ⇑(⟨f, h⟩ : C_c(α, β)) = f :=
  rfl

/-- Copy of a `CompactlySupportedContinuousMap` with a new `toFun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : C_c(α, β)) (f' : α → β) (h : f' = f) : C_c(α, β) where
  toFun := f'
  continuous_toFun := by
    rw [h]
    exact f.continuous_toFun
  hasCompactSupport' := by
    simp_rw [h]
    exact f.hasCompactSupport'

@[simp]
theorem coe_copy (f : C_c(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : C_c(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

theorem eq_of_empty [IsEmpty α] (f g : C_c(α, β)) : f = g :=
  ext <| IsEmpty.elim ‹_›

/-- A continuous function on a compact space automatically has compact support. -/
@[simps]
def continuousMapEquiv [CompactSpace α] : C(α, β) ≃ C_c(α, β) where
  toFun f :=
    { toFun := f
      hasCompactSupport' := HasCompactSupport.of_compactSpace f }
  invFun f := f

@[deprecated (since := "2025-10-21")] alias ContinuousMap.liftCompactlySupported :=
    continuousMapEquiv

variable {γ : Type*} [TopologicalSpace γ] [Zero γ]

/-- Composition of a continuous function `f` with compact support with another continuous function
`g` sending `0` to `0` from the left yields another continuous function `g ∘ f` with compact
support.

If `g` doesn't send `0` to `0`, `f.compLeft g` defaults to `0`. -/
noncomputable def compLeft (g : C(β, γ)) (f : C_c(α, β)) : C_c(α, γ) where
  toContinuousMap := by classical exact if g 0 = 0 then g.comp f else 0
  hasCompactSupport' := by
    split_ifs with hg
    · exact f.hasCompactSupport'.comp_left hg
    · exact .zero

lemma toContinuousMap_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) :
    (f.compLeft g).toContinuousMap = g.comp f := if_pos hg

lemma coe_compLeft {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) : f.compLeft g = g ∘ f := by
  simp [compLeft, if_pos hg]

lemma compLeft_apply {g : C(β, γ)} (hg : g 0 = 0) (f : C_c(α, β)) (a : α) :
    f.compLeft g a = g (f a) := by simp [coe_compLeft hg f]

/-- A compactly supported continuous function gives rise to a bounded continuous function. -/
@[simps] def toBoundedContinuousFunction {β : Type*} [PseudoMetricSpace β] [Zero β]
    (f : C_c(α, β)) : BoundedContinuousFunction α β where
  toFun := f
  map_bounded' := by
    have : IsCompact (Set.range f) := f.hasCompactSupport.isCompact_range f.continuous
    rcases Metric.isBounded_iff.1 this.isBounded with ⟨C, hC⟩
    exact ⟨C, by grind⟩

end Basics

/-! ### Algebraic structure

Whenever `β` has the structure of continuous additive monoid and a compatible topological structure,
then `C_c(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C_c(α, β)` will not have a multiplicative identity.
-/

section AlgebraicStructure

variable [TopologicalSpace β] (x : α)

instance [Zero β] : Zero C_c(α, β) where
  zero := { toFun := (0 : C(α, β))
            continuous_toFun := (0 : C(α, β)).2
            hasCompactSupport' := by simp [HasCompactSupport, tsupport] }

instance [Zero β] : Inhabited C_c(α, β) :=
  ⟨0⟩

@[simp]
theorem coe_zero [Zero β] : ⇑(0 : C_c(α, β)) = 0 :=
  rfl

theorem zero_apply [Zero β] : (0 : C_c(α, β)) x = 0 :=
  rfl

instance [MulZeroClass β] [ContinuousMul β] : Mul C_c(α, β) :=
  ⟨fun f g => ⟨f * g, HasCompactSupport.mul_left g.2⟩⟩

@[simp]
theorem coe_mul [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : ⇑(f * g) = f * g :=
  rfl

theorem mul_apply [MulZeroClass β] [ContinuousMul β] (f g : C_c(α, β)) : (f * g) x = f x * g x :=
  rfl

/-- the product of `f : F` assuming `ContinuousMapClass F α γ` and `ContinuousSMul γ β` and
`g : C_c(α, β)` is in `C_c(α, β)` -/
instance [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] : SMul F C_c(α, β) where
  smul f g :=
    ⟨⟨fun x ↦ f x • g x, (map_continuous f).smul (map_continuous g)⟩, g.hasCompactSupport.smul_left⟩

@[simp]
theorem coe_smulc [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c(α, β)) :
    ⇑(f • g) = fun x => f x • g x :=
  rfl

theorem smulc_apply [Zero β] [TopologicalSpace γ] [SMulZeroClass γ β] [ContinuousSMul γ β]
    {F : Type*} [FunLike F α γ] [ContinuousMapClass F α γ] (f : F) (g : C_c(α, β)) (x : α) :
    (f • g) x = f x • g x :=
  rfl

instance [MulZeroClass β] [ContinuousMul β] : MulZeroClass C_c(α, β) := fast_instance%
  DFunLike.coe_injective.mulZeroClass _ coe_zero coe_mul

instance [SemigroupWithZero β] [ContinuousMul β] :
    SemigroupWithZero C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semigroupWithZero _ coe_zero coe_mul

instance [AddZeroClass β] [ContinuousAdd β] : Add C_c(α, β) :=
  ⟨fun f g => ⟨f + g, HasCompactSupport.add f.2 g.2⟩⟩

@[simp]
theorem coe_add [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply [AddZeroClass β] [ContinuousAdd β] (f g : C_c(α, β)) : (f + g) x = f x + g x :=
  rfl

instance [AddZeroClass β] [ContinuousAdd β] : AddZeroClass C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

/-- Coercion to a function as a `AddMonoidHom`. Similar to `AddMonoidHom.coeFn`. -/
def coeFnMonoidHom [AddMonoid β] [ContinuousAdd β] : C_c(α, β) →+ α → β where
  toFun f := f
  map_zero' := coe_zero
  map_add' := coe_add

instance [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] :
    SMul R C_c(α, β) := fast_instance%
  ⟨fun r f => ⟨⟨r • ⇑f, (map_continuous f).const_smul r⟩, HasCompactSupport.smul_left f.2⟩⟩

@[simp, norm_cast]
theorem coe_smul [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
    (f : C_c(α, β)) : ⇑(r • f) = r • ⇑f :=
  rfl

theorem smul_apply [Zero β] {R : Type*} [SMulZeroClass R β] [ContinuousConstSMul R β] (r : R)
    (f : C_c(α, β)) (x : α) : (r • f) x = r • f x :=
  rfl

section AddMonoid

instance [AddMonoid β] [ContinuousAdd β] : AddMonoid C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoid

instance [AddCommMonoid β] [ContinuousAdd β] : AddCommMonoid C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

@[simp]
theorem coe_sum [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι → C_c(α, β)) :
    ⇑(∑ i ∈ s, f i) = ∑ i ∈ s, (f i : α → β) :=
  map_sum coeFnMonoidHom f s

theorem sum_apply [AddCommMonoid β] [ContinuousAdd β] {ι : Type*} (s : Finset ι) (f : ι → C_c(α, β))
    (a : α) : (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by simp

section AddGroup

variable [AddGroup β] [IsTopologicalAddGroup β] (f g : C_c(α, β))

instance : Neg C_c(α, β) where
  neg f := { toFun := -f.1
             continuous_toFun := map_continuous (-f.1)
             hasCompactSupport' := by simpa [HasCompactSupport, tsupport] using f.2 }

@[simp]
theorem coe_neg : ⇑(-f) = -f :=
  rfl

theorem neg_apply : (-f) x = -f x :=
  rfl

instance : Sub C_c(α, β) where
  sub f g := { toFun := f.1 - g.1
               continuous_toFun := map_continuous (f.1 - g.1)
               hasCompactSupport' := by
                 simpa [sub_eq_add_neg] using HasCompactSupport.add f.2 (-g).2 }

@[simp]
theorem coe_sub : ⇑(f - g) = f - g :=
  rfl

theorem sub_apply : (f - g) x = f x - g x :=
  rfl

instance : AddGroup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end AddGroup

instance [AddCommGroup β] [IsTopologicalAddGroup β] : AddCommGroup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ =>
    rfl

instance [Zero β] {R : Type*} [Zero R] [SMulWithZero R β] [SMulWithZero Rᵐᵒᵖ β]
    [ContinuousConstSMul R β] [IsCentralScalar R β] : IsCentralScalar R C_c(α, β) :=
  ⟨fun _ _ => ext fun _ => op_smul_eq_smul _ _⟩

instance [Zero β] {R : Type*} [Zero R] [SMulWithZero R β]
    [ContinuousConstSMul R β] : SMulWithZero R C_c(α, β) := fast_instance%
  Function.Injective.smulWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

instance [Zero β] {R : Type*} [MonoidWithZero R] [MulActionWithZero R β]
    [ContinuousConstSMul R β] : MulActionWithZero R C_c(α, β) := fast_instance%
  Function.Injective.mulActionWithZero ⟨_, coe_zero⟩ DFunLike.coe_injective coe_smul

instance [AddCommMonoid β] [ContinuousAdd β] {R : Type*} [Semiring R] [Module R β]
    [ContinuousConstSMul R β] : Module R C_c(α, β) := fast_instance%
  Function.Injective.module R ⟨⟨_, coe_zero⟩, coe_add⟩ DFunLike.coe_injective coe_smul

instance [NonUnitalNonAssocSemiring β] [IsTopologicalSemiring β] :
    NonUnitalNonAssocSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalSemiring β] [IsTopologicalSemiring β] :
    NonUnitalSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalCommSemiring β] [IsTopologicalSemiring β] :
    NonUnitalCommSemiring C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommSemiring _ coe_zero coe_add coe_mul fun _ _ => rfl

instance [NonUnitalNonAssocRing β] [IsTopologicalRing β] :
    NonUnitalNonAssocRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalNonAssocRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

instance [NonUnitalRing β] [IsTopologicalRing β] : NonUnitalRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalRing _ coe_zero coe_add coe_mul coe_neg coe_sub (fun _ _ => rfl)
    fun _ _ => rfl

instance [NonUnitalCommRing β] [IsTopologicalRing β] :
    NonUnitalCommRing C_c(α, β) := fast_instance%
  DFunLike.coe_injective.nonUnitalCommRing _ coe_zero coe_add coe_mul coe_neg coe_sub
    (fun _ _ => rfl) fun _ _ => rfl

set_option backward.isDefEq.respectTransparency false in
instance {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [IsScalarTower R β β] :
    IsScalarTower R C_c(α, β) C_c(α, β) where
  smul_assoc r f g := by
    ext
    simp only [smul_eq_mul, coe_mul, coe_smul, Pi.mul_apply, Pi.smul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]

set_option backward.isDefEq.respectTransparency false in
instance {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring β]
    [IsTopologicalSemiring β] [Module R β] [ContinuousConstSMul R β] [SMulCommClass R β β] :
    SMulCommClass R C_c(α, β) C_c(α, β) where
  smul_comm r f g := by
    ext
    simp only [smul_eq_mul, coe_smul, coe_mul, Pi.smul_apply, Pi.mul_apply]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

end AlgebraicStructure

section Star

/-! ### Star structure

It is possible to equip `C_c(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`StarAddMonoid` is close enough.

The `StarAddMonoid` class on `C_c(α, β)` is inherited from their counterparts on `α →ᵇ β`.
-/


variable [TopologicalSpace β] [AddMonoid β] [StarAddMonoid β] [ContinuousStar β]

instance : Star C_c(α, β) where
  star f :=
    { toFun := fun x => star (f x)
      continuous_toFun := (map_continuous f).star
      hasCompactSupport' := by
        rw [HasCompactSupport, tsupport]
        have support_star : (Function.support fun (x : α) => star (f x)) = Function.support f := by
          ext x
          simp only [Function.mem_support, ne_eq, star_eq_zero]
        rw [support_star]
        exact f.2 }

@[simp]
theorem coe_star (f : C_c(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl

theorem star_apply (f : C_c(α, β)) (x : α) : (star f) x = star (f x) :=
  rfl

instance [TrivialStar β] : TrivialStar C_c(α, β) where
    star_trivial f := ext fun x => star_trivial (f x)

instance [ContinuousAdd β] : StarAddMonoid C_c(α, β) where
  star_involutive f := ext fun x => star_star (f x)
  star_add f g := ext fun x => star_add (f x) (g x)

end Star

section StarModule

variable {𝕜 : Type*} [Zero 𝕜] [Star 𝕜] [AddMonoid β] [StarAddMonoid β] [TopologicalSpace β]
  [ContinuousStar β] [SMulWithZero 𝕜 β] [ContinuousConstSMul 𝕜 β] [StarModule 𝕜 β]

instance : StarModule 𝕜 C_c(α, β) where
  star_smul k f := ext fun x => star_smul k (f x)

end StarModule

section StarRing

variable [NonUnitalSemiring β] [StarRing β] [TopologicalSpace β] [ContinuousStar β]
  [IsTopologicalSemiring β]

instance : StarRing C_c(α, β) :=
  { CompactlySupportedContinuousMap.instStarAddMonoid with
    star_mul := fun f g => ext fun x => star_mul (f x) (g x) }

end StarRing

section PartialOrder

/-! ### The partial order in `C_c`
When `β` is equipped with a partial order, `C_c(α, β)` is given the pointwise partial order.
-/

variable {β : Type*} [TopologicalSpace β] [Zero β] [PartialOrder β]

instance partialOrder : PartialOrder C_c(α, β) :=
  fast_instance% PartialOrder.lift (⇑) DFunLike.coe_injective

theorem le_def {f g : C_c(α, β)} : f ≤ g ↔ ∀ a, f a ≤ g a := Pi.le_def

theorem lt_def {f g : C_c(α, β)} : f < g ↔ (∀ a, f a ≤ g a) ∧ ∃ a, f a < g a := Pi.lt_def

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup β] [Zero β] [TopologicalSpace β] [ContinuousSup β]

instance instSup : Max C_c(α, β) where max f g :=
  { toFun := f ⊔ g
    continuous_toFun := Continuous.sup f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.sup g.hasCompactSupport }

@[simp, norm_cast] lemma coe_sup (f g : C_c(α, β)) : ⇑(f ⊔ g) = ⇑f ⊔ g := rfl

@[simp] lemma sup_apply (f g : C_c(α, β)) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

instance semilatticeSup : SemilatticeSup C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup

lemma finsetSup'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) (a : α) :
    s.sup' H f a = s.sup' H fun i ↦ f i a :=
  Finset.comp_sup'_eq_sup'_comp H (fun g : C_c(α, β) ↦ g a) fun _ _ ↦ rfl

@[simp, norm_cast]
lemma coe_finsetSup' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) :
    ⇑(s.sup' H f) = s.sup' H fun i ↦ ⇑(f i) := by ext; simp [finsetSup'_apply]

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf β] [Zero β] [TopologicalSpace β] [ContinuousInf β]

instance instInf : Min C_c(α, β) where min f g :=
  { toFun := f ⊓ g
    continuous_toFun := Continuous.inf f.continuous g.continuous
    hasCompactSupport' := f.hasCompactSupport.inf g.hasCompactSupport }

@[simp, norm_cast] lemma coe_inf (f g : C_c(α, β)) : ⇑(f ⊓ g) = ⇑f ⊓ g := rfl

@[simp] lemma inf_apply (f g : C_c(α, β)) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

instance semilatticeInf : SemilatticeInf C_c(α, β) := fast_instance%
  DFunLike.coe_injective.semilatticeInf _ .rfl .rfl coe_inf

lemma finsetInf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) (a : α) :
    s.inf' H f a = s.inf' H fun i ↦ f i a :=
  Finset.comp_inf'_eq_inf'_comp H (fun g : C_c(α, β) ↦ g a) fun _ _ ↦ rfl

@[simp, norm_cast]
lemma coe_finsetInf' {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → C_c(α, β)) :
    ⇑(s.inf' H f) = s.inf' H fun i ↦ ⇑(f i) := by ext; simp [finsetInf'_apply]

end SemilatticeInf

section Lattice

variable [TopologicalSpace β]

instance [Lattice β] [TopologicalLattice β] [Zero β] : Lattice C_c(α, β) where

instance instMulLeftMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulLeftMono β] :
    MulLeftMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => mul_le_mul_right (hg₁₂ x) _⟩

instance instMulRightMono [PartialOrder β] [MulZeroClass β] [ContinuousMul β] [MulRightMono β] :
    MulRightMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => mul_le_mul_left (hg₁₂ x) _⟩

instance instAddLeftMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddLeftMono β] :
    AddLeftMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => add_le_add_right (hg₁₂ x) _⟩

instance instAddRightMono [PartialOrder β] [AddZeroClass β] [ContinuousAdd β] [AddRightMono β] :
    AddRightMono C_c(α, β) :=
  ⟨fun _ _ _ hg₁₂ x => add_le_add_left (hg₁₂ x) _⟩

-- TODO transfer this lattice structure to `BoundedContinuousFunction`

end Lattice

section IsOrderedAddMonoid

variable [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
variable [PartialOrder β] [IsOrderedAddMonoid β]

instance : IsOrderedAddMonoid C_c(α, β) where
  add_le_add_left _ _ hfg c := add_le_add_left hfg c

end IsOrderedAddMonoid

/-! ### `C_c` as a functor

For each `β` with sufficient structure, there is a contravariant functor `C_c(-, β)` from the
category of topological spaces with morphisms given by `CocompactMap`s.
-/


variable {δ : Type*} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

local notation α " →co " β => CocompactMap α β

section

variable [Zero δ]

/-- Composition of a continuous function with compact support with a cocompact map
yields another continuous function with compact support. -/
def comp (f : C_c(γ, δ)) (g : β →co γ) : C_c(β, δ) where
  toContinuousMap := (f : C(γ, δ)).comp g
  hasCompactSupport' := by
    apply IsCompact.of_isClosed_subset (g.isCompact_preimage_of_isClosed f.2 (isClosed_tsupport _))
      (isClosed_tsupport (f ∘ g))
    intro x hx
    rw [tsupport, Set.mem_preimage, _root_.mem_closure_iff]
    intro o ho hgxo
    rw [tsupport, _root_.mem_closure_iff] at hx
    obtain ⟨y, hy⟩ := hx (g ⁻¹' o) (IsOpen.preimage g.1.2 ho) hgxo
    exact ⟨g y, hy⟩

@[simp]
theorem coe_comp_to_continuous_fun (f : C_c(γ, δ)) (g : β →co γ) : ((f.comp g) : β → δ) = f ∘ g :=
  rfl

@[simp]
theorem comp_id (f : C_c(γ, δ)) : f.comp (CocompactMap.id γ) = f :=
  ext fun _ => rfl

@[simp]
theorem comp_assoc (f : C_c(γ, δ)) (g : β →co γ) (h : α →co β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem zero_comp (g : β →co γ) : (0 : C_c(γ, δ)).comp g = 0 :=
  rfl

end

/-- Composition as an additive monoid homomorphism. -/
def compAddMonoidHom [AddMonoid δ] [ContinuousAdd δ] (g : β →co γ) : C_c(γ, δ) →+ C_c(β, δ) where
  toFun f := f.comp g
  map_zero' := zero_comp g
  map_add' _ _ := rfl

/-- Composition as a semigroup homomorphism. -/
def compMulHom [MulZeroClass δ] [ContinuousMul δ] (g : β →co γ) : C_c(γ, δ) →ₙ* C_c(β, δ) where
  toFun f := f.comp g
  map_mul' _ _ := rfl

/-- Composition as a linear map. -/
def compLinearMap [AddCommMonoid δ] [ContinuousAdd δ] {R : Type*} [Semiring R] [Module R δ]
    [ContinuousConstSMul R δ] (g : β →co γ) : C_c(γ, δ) →ₗ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Composition as a non-unital algebra homomorphism. -/
def compNonUnitalAlgHom {R : Type*} [Semiring R] [NonUnitalNonAssocSemiring δ]
    [IsTopologicalSemiring δ] [Module R δ] [ContinuousConstSMul R δ] (g : β →co γ) :
    C_c(γ, δ) →ₙₐ[R] C_c(β, δ) where
  toFun f := f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end CompactlySupportedContinuousMap

namespace CompactlySupportedContinuousMapClass

section Basic

variable [Zero β] [TopologicalSpace β] [FunLike F α β] [CompactlySupportedContinuousMapClass F α β]

instance : CoeTC F (CompactlySupportedContinuousMap α β) :=
  ⟨fun f =>
    { toFun := f
      continuous_toFun := map_continuous f
      hasCompactSupport' := hasCompactSupport f }⟩

/-- A continuous function on a compact space has automatically compact support. This is not an
instance to avoid type class loops. -/
lemma of_compactSpace (G : Type*) [FunLike G α β]
    [ContinuousMapClass G α β] [CompactSpace α] : CompactlySupportedContinuousMapClass G α β where
  map_continuous := map_continuous
  hasCompactSupport := by
    intro f
    exact HasCompactSupport.of_compactSpace f

end Basic

section Uniform

variable [UniformSpace β] [UniformSpace γ] [Zero γ] [FunLike F β γ]
  [CompactlySupportedContinuousMapClass F β γ]

theorem uniformContinuous (f : F) : UniformContinuous (f : β → γ) :=
  (map_continuous f).uniformContinuous_of_tendsto_cocompact
  (HasCompactSupport.is_zero_at_infty (hasCompactSupport f))

end Uniform

section ZeroAtInfty

variable [TopologicalSpace β] [TopologicalSpace γ] [Zero γ]
  [FunLike F β γ] [CompactlySupportedContinuousMapClass F β γ]

instance : ZeroAtInftyContinuousMapClass F β γ where
  zero_at_infty f := HasCompactSupport.is_zero_at_infty (hasCompactSupport f)

end ZeroAtInfty

end CompactlySupportedContinuousMapClass

section NonnegativePart

open NNReal

namespace CompactlySupportedContinuousMap

protected lemma exists_add_of_le {f₁ f₂ : C_c(α, ℝ≥0)} (h : f₁ ≤ f₂) : ∃ (g : C_c(α, ℝ≥0)),
    f₁ + g = f₂ := by
  refine ⟨⟨f₂.1 - f₁.1, ?_⟩, ?_⟩
  · apply (f₁.hasCompactSupport'.union f₂.hasCompactSupport').of_isClosed_subset isClosed_closure
    rw [tsupport, tsupport, ← closure_union]
    apply closure_mono
    intro x hx
    contrapose hx
    simp only [ContinuousMap.toFun_eq_coe, coe_toContinuousMap, Set.mem_union, Function.mem_support,
      ne_eq, not_or, Decidable.not_not, ContinuousMap.coe_sub, Pi.sub_apply] at hx ⊢
    simp [hx.1, hx.2]
  · ext x
    simpa [← NNReal.coe_add] using add_tsub_cancel_of_le (h x)

/-- The nonnegative part of a continuous compactly supported `ℝ`-valued function as a
continuous compactly supported `ℝ≥0`-valued function. -/
noncomputable def nnrealPart (f : C_c(α, ℝ)) : C_c(α, ℝ≥0) where
  toFun := Real.toNNReal.comp f.toFun
  continuous_toFun := Continuous.comp continuous_real_toNNReal f.continuous
  hasCompactSupport' := HasCompactSupport.comp_left f.hasCompactSupport' Real.toNNReal_zero

@[simp]
lemma nnrealPart_apply (f : C_c(α, ℝ)) (x : α) :
    f.nnrealPart x = Real.toNNReal (f x) := rfl

lemma nnrealPart_neg_eq_zero_of_nonneg {f : C_c(α, ℝ)} (hf : 0 ≤ f) : (-f).nnrealPart = 0 := by
  ext x
  simpa using hf x

lemma nnrealPart_smul_pos (f : C_c(α, ℝ)) {a : ℝ} (ha : 0 ≤ a) :
    (a • f).nnrealPart = a.toNNReal • f.nnrealPart := by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, Real.coe_toNNReal', smul_eq_mul,
    NNReal.coe_mul, ha, sup_of_le_left]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [ha, hfx, mul_nonneg]
  · simp [mul_nonpos_iff, ha, hfx]

lemma nnrealPart_smul_neg (f : C_c(α, ℝ)) {a : ℝ} (ha : a ≤ 0) :
    (a • f).nnrealPart = (-a).toNNReal • (-f).nnrealPart := by
  ext x
  simp only [nnrealPart_apply, coe_smul, Pi.smul_apply, smul_eq_mul, Real.coe_toNNReal', coe_neg,
    Pi.neg_apply, NNReal.coe_mul]
  rcases le_total 0 (f x) with hfx | hfx
  · simp [mul_nonpos_iff, ha, hfx]
  · simp [ha, hfx, mul_nonneg_of_nonpos_of_nonpos]

lemma nnrealPart_add_le_add_nnrealPart (f g : C_c(α, ℝ)) :
    (f + g).nnrealPart ≤ f.nnrealPart + g.nnrealPart := by
  intro x
  simpa using Real.toNNReal_add_le

lemma exists_add_nnrealPart_add_eq (f g : C_c(α, ℝ)) : ∃ (h : C_c(α, ℝ≥0)),
    (f + g).nnrealPart + h = f.nnrealPart + g.nnrealPart ∧
    (-f + -g).nnrealPart + h = (-f).nnrealPart + (-g).nnrealPart := by
  obtain ⟨h, hh⟩ := CompactlySupportedContinuousMap.exists_add_of_le
    (nnrealPart_add_le_add_nnrealPart f g)
  use h
  refine ⟨hh, ?_⟩
  ext x
  have hhx := congr(($hh x : ℝ))
  simp only [coe_add, Pi.add_apply, nnrealPart_apply, coe_neg, Pi.neg_apply, NNReal.coe_add,
    Real.coe_toNNReal', ← neg_add, max_neg_zero] at hhx ⊢
  linear_combination hhx

/-- The compactly supported continuous `ℝ≥0`-valued function as a compactly supported `ℝ`-valued
function. -/
noncomputable def toReal (f : C_c(α, ℝ≥0)) : C_c(α, ℝ) :=
  f.compLeft ContinuousMap.coeNNRealReal

@[simp] lemma toReal_apply (f : C_c(α, ℝ≥0)) (x : α) : f.toReal x = f x := compLeft_apply rfl _ _
@[simp] lemma toReal_nonneg {f : C_c(α, ℝ≥0)} : 0 ≤ f.toReal := fun _ ↦ by simp
@[simp] lemma toReal_add (f g : C_c(α, ℝ≥0)) : (f + g).toReal = f.toReal + g.toReal := by ext; simp
@[simp] lemma toReal_smul (r : ℝ≥0) (f : C_c(α, ℝ≥0)) : (r • f).toReal = r • f.toReal := by
  ext; simp [NNReal.smul_def]

@[simp]
lemma nnrealPart_sub_nnrealPart_neg (f : C_c(α, ℝ)) :
    (nnrealPart f).toReal - (nnrealPart (-f)).toReal = f := by ext x; simp

/-- The map `toReal` defined as a `ℝ≥0`-linear map. -/
noncomputable def toRealLinearMap : C_c(α, ℝ≥0) →ₗ[ℝ≥0] C_c(α, ℝ) where
  toFun := toReal
  map_add' f g := by ext x; simp
  map_smul' a f := by ext x; simp

@[simp, norm_cast]
lemma coe_toRealLinearMap : (toRealLinearMap : C_c(α, ℝ≥0) → C_c(α, ℝ)) = toReal := rfl

lemma toRealLinearMap_apply (f : C_c(α, ℝ≥0)) : toRealLinearMap f = f.toReal := rfl

lemma toRealLinearMap_apply_apply (f : C_c(α, ℝ≥0)) (x : α) :
    toRealLinearMap f x = (f x).toReal := by simp

@[simp]
lemma nnrealPart_toReal_eq (f : C_c(α, ℝ≥0)) : nnrealPart (toReal f) = f := by ext x; simp

@[simp]
lemma nnrealPart_neg_toReal_eq (f : C_c(α, ℝ≥0)) : nnrealPart (-toReal f) = 0 := by ext x; simp

section toNNRealLinear

/-- For a positive linear functional `Λ : C_c(α, ℝ) → ℝ`, define a `ℝ≥0`-linear map. -/
noncomputable def toNNRealLinear (Λ : C_c(α, ℝ) →ₚ[ℝ] ℝ) :
    C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := .mk (Λ (toRealLinearMap f)) (Λ.map_nonneg (by simp))
  map_add' f g := by simp; rfl
  map_smul' a f := by simp [NNReal.smul_def]; rfl

@[simp]
lemma toNNRealLinear_apply (Λ : C_c(α, ℝ) →ₚ[ℝ] ℝ) (f : C_c(α, ℝ≥0)) :
    toNNRealLinear Λ f = Λ (toReal f) := rfl

@[simp]
lemma toNNRealLinear_inj (Λ₁ Λ₂ : C_c(α, ℝ) →ₚ[ℝ] ℝ) :
    toNNRealLinear Λ₁ = toNNRealLinear Λ₂ ↔ Λ₁ = Λ₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  ext f
  rw [← nnrealPart_sub_nnrealPart_neg f]
  simp only [LinearMap.ext_iff, NNReal.eq_iff, toNNRealLinear_apply] at h
  simp_rw [map_sub, h]

end toNNRealLinear

section toRealPositiveLinear

/-- For a positive linear functional `Λ : C_c(α, ℝ≥0) → ℝ≥0`, define a positive `ℝ`-linear map. -/
noncomputable def toRealPositiveLinear (Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) : C_c(α, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => Λ (nnrealPart f) - Λ (nnrealPart (- f))
      map_add' f g := by
        simp only [neg_add_rev]
        obtain ⟨h, hh⟩ := exists_add_nnrealPart_add_eq f g
        rw [← add_zero ((Λ (f + g).nnrealPart).toReal - (Λ (-g + -f).nnrealPart).toReal),
          ← sub_self (Λ h).toReal, sub_add_sub_comm, ← NNReal.coe_add, ← NNReal.coe_add,
          ← map_add, ← map_add, hh.1, add_comm (-g) (-f), hh.2]
        simp only [map_add, NNReal.coe_add]
        ring
      map_smul' a f := by
        rcases le_total 0 a with ha | ha
        · rw [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f), nnrealPart_smul_pos f ha,
            nnrealPart_smul_pos (-f) ha]
          simp [sup_of_le_left ha, mul_sub]
        · simp only [RingHom.id_apply, smul_eq_mul, ← (smul_neg a f),
            nnrealPart_smul_neg f ha, nnrealPart_smul_neg (-f) ha, map_smul,
            NNReal.coe_mul, Real.coe_toNNReal', neg_neg, sup_of_le_left (neg_nonneg.mpr ha)]
          ring }
    (fun g hg ↦ by simp [nnrealPart_neg_eq_zero_of_nonneg hg])

lemma toRealPositiveLinear_apply {Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0} (f : C_c(α, ℝ)) :
    toRealPositiveLinear Λ f = Λ (nnrealPart f) - Λ (nnrealPart (-f)) := rfl

@[simp]
lemma eq_toRealPositiveLinear_toReal (Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) (f : C_c(α, ℝ≥0)) :
    toRealPositiveLinear Λ (toReal f) = Λ f := by
  simp [toRealPositiveLinear_apply]

@[simp]
lemma eq_toNNRealLinear_toRealPositiveLinear (Λ : C_c(α, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0) :
    toNNRealLinear (toRealPositiveLinear Λ) = Λ := by
  ext f
  simp

end toRealPositiveLinear

section pullback

variable [R1Space α] [Group α] [TopologicalSpace β] [R1Space β] [Group β] [ContinuousMul β]
  [NormedAddCommGroup γ] {φ : α →* β} (hφ : Topology.IsClosedEmbedding φ)

open scoped Pointwise in
/-- Pull back a continuous compactly supported function `f` on `β` along a closed embedding
`φ : α →* β` to the continuous compactly supported function `a ↦ f (b * φ a)` on `A`. -/
@[to_additive /-- Pull back a continuous compactly supported function `f` on `β` along a closed
embedding `φ : α →+ β` to the continuous compactly supported function `a ↦ f (b + φ a)` on `A`. -/]
noncomputable def pullback_monoidHom (f : CompactlySupportedContinuousMap β γ) (b : β) :
    CompactlySupportedContinuousMap α γ where
  toFun a := f (b * φ a)
  hasCompactSupport' := by
    obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
    refine exists_compact_iff_hasCompactSupport.mp ⟨φ ⁻¹' (b⁻¹ • K),
      hφ.isCompact_preimage (hK.smul b⁻¹), fun x hx ↦ hf _ ?_⟩
    simpa [Set.mem_smul_set_iff_inv_smul_mem] using hx
  continuous_toFun := by fun_prop

@[to_additive]
theorem pullback_monoidHom_def (f : CompactlySupportedContinuousMap β γ) (b : β) (a : α) :
    pullback_monoidHom hφ f b a = f (b * φ a) :=
  rfl

end pullback

end CompactlySupportedContinuousMap

end NonnegativePart
