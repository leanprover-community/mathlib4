/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Mitchell Lee
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Order.Filter.Pointwise
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Theory of topological monoids

In this file we define mixin classes `ContinuousMul` and `ContinuousAdd`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/

@[expose] public section

universe u v

open Set Filter TopologicalSpace Topology
open scoped Topology Pointwise

variable {ι α M N X : Type*} [TopologicalSpace X]

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X → M) :=
  @continuous_const _ _ _ _ 1

namespace MulOpposite

/-- If multiplication is separately continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is separately continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
instance [TopologicalSpace α] [Mul α] [SeparatelyContinuousMul α] :
    SeparatelyContinuousMul αᵐᵒᵖ where
  continuous_mul_const := continuous_op.comp (continuous_unop.const_mul (unop _))
  continuous_const_mul := continuous_op.comp (continuous_unop.mul_const (unop _))

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive /-- If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`. -/]
instance [TopologicalSpace α] [Mul α] [ContinuousMul α] : ContinuousMul αᵐᵒᵖ :=
  ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

end MulOpposite

section SeparatelyContinuousMul

variable [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M]

@[to_additive]
instance : SeparatelyContinuousMul Mᵒᵈ :=
  ‹SeparatelyContinuousMul M›

@[to_additive]
instance : SeparatelyContinuousMul (ULift.{u} M) :=
  ⟨continuous_uliftUp.comp (by fun_prop), continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]
instance SeparatelyContinuousMul.to_continuousSMul : ContinuousConstSMul M M :=
  ⟨fun _ ↦ continuous_const_mul⟩

@[to_additive]
instance SeparatelyContinuousMul.to_continuousSMul_op : ContinuousConstSMul Mᵐᵒᵖ M :=
  ⟨fun _ ↦ continuous_mul_const⟩

end SeparatelyContinuousMul

section ContinuousMul

variable [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive]
instance : ContinuousMul Mᵒᵈ :=
  ‹ContinuousMul M›

@[to_additive]
instance : ContinuousMul (ULift.{u} M) := ⟨continuous_uliftUp.comp (by fun_prop)⟩

@[to_additive]
instance ContinuousMul.to_continuousSMul : ContinuousSMul M M :=
  ⟨continuous_mul⟩

@[to_additive]
instance ContinuousMul.to_continuousSMul_op : ContinuousSMul Mᵐᵒᵖ M :=
  ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) from
    by fun_prop⟩

@[to_additive]
theorem ContinuousMul.induced {α : Type*} {β : Type*} {F : Type*} [FunLike F α β] [Mul α]
    [Mul β] [MulHomClass F α β] [tβ : TopologicalSpace β] [ContinuousMul β] (f : F) :
    @ContinuousMul α (tβ.induced f) _ := by
  let tα := tβ.induced f
  refine ⟨continuous_induced_rng.2 ?_⟩
  simp only [Function.comp_def, map_mul]
  fun_prop

@[deprecated (since := "2026-02-20")] alias continuous_add_left := continuous_const_add
@[deprecated (since := "2026-02-20")] alias continuous_add_right := continuous_add_const
@[to_additive existing, deprecated (since := "2026-02-20")]
alias continuous_mul_left := continuous_const_mul
@[to_additive existing, deprecated (since := "2026-02-20")]
alias continuous_mul_right := continuous_mul_const

@[to_additive]
theorem ContinuousOn.comp_mul_left {f : M → X} {s t : Set M} {c : M} (hf : ContinuousOn f t)
    (hct : Set.MapsTo (fun x : M => c * x) s t) : ContinuousOn (fun x => f (c * x)) s :=
  hf.comp (continuous_const_mul c).continuousOn hct

@[to_additive]
theorem ContinuousOn.comp_mul_right {f : M → X} {s t : Set M} {c : M} (hf : ContinuousOn f t)
    (hct : Set.MapsTo (fun x : M => x * c) s t) : ContinuousOn (fun x => f (x * c)) s :=
  hf.comp (continuous_mul_const c).continuousOn hct

@[to_additive]
theorem tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
  continuous_iff_continuousAt.mp ContinuousMul.continuous_mul (a, b)

@[to_additive]
theorem le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b ≤ 𝓝 (a * b) := by
  rw [← map₂_mul, ← map_uncurry_prod, ← nhds_prod_eq]
  exact continuous_mul.tendsto _

@[to_additive (attr := simp)]
theorem nhds_one_mul_nhds {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm <|
    le_mul_of_one_le_left' <| pure_le_nhds 1

@[to_additive (attr := simp)]
theorem nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 a * 𝓝 1 = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm <|
    le_mul_of_one_le_right' <| pure_le_nhds 1

/-- This lemma exists to ensure that we can still do the simplification `pure_le_nhds_iff`
after simplifying with `pure_one`. -/
@[to_additive (attr := simp) /-- This lemma exists to ensure that we can still do the simplification
`pure_le_nhds_iff` after simplifying with `pure_zero`. -/]
theorem one_le_nhds_iff [T1Space X] [One X] {b : X} : 1 ≤ 𝓝 b ↔ 1 = b :=
  pure_le_nhds_iff

section tendsto_nhds

variable {𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [Mul 𝕜] [TopologicalSpace 𝕜] [SeparatelyContinuousMul 𝕜]
  {l : Filter α} {f : α → 𝕜} {b c : 𝕜} (hb : 0 < b)
include hb

theorem Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
    Tendsto (fun a => b * f a) l (𝓝[>] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

theorem Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
    Tendsto (fun a => b * f a) l (𝓝[<] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

theorem Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[>] c)) :
    Tendsto (fun a => f a * b) l (𝓝[>] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Ioi] at *; gcongr

theorem Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] (h : Tendsto f l (𝓝[<] c)) :
    Tendsto (fun a => f a * b) l (𝓝[<] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ _ => by rw [Set.mem_Iio] at *; gcongr

end tendsto_nhds

@[to_additive]
protected theorem Specializes.mul {a b c d : M} (hab : a ⤳ b) (hcd : c ⤳ d) : (a * c) ⤳ (b * d) :=
  hab.smul hcd

@[to_additive]
protected theorem Inseparable.mul {a b c d : M} (hab : Inseparable a b) (hcd : Inseparable c d) :
    Inseparable (a * c) (b * d) :=
  hab.smul hcd

@[to_additive]
protected theorem Specializes.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    {a b : M} (h : a ⤳ b) (n : ℕ) : (a ^ n) ⤳ (b ^ n) :=
  Nat.recOn n (by simp only [pow_zero, specializes_rfl]) fun _ ihn ↦ by
    simpa only [pow_succ] using ihn.mul h

@[to_additive]
protected theorem Inseparable.pow {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    {a b : M} (h : Inseparable a b) (n : ℕ) : Inseparable (a ^ n) (b ^ n) :=
  (h.specializes.pow n).antisymm (h.specializes'.pow n)

/-- Construct a unit from limits of units and their inverses. -/
@[to_additive (attr := simps)
  /-- Construct an additive unit from limits of additive units and their negatives. -/]
def Filter.Tendsto.units [TopologicalSpace N] [Monoid N] [ContinuousMul N] [T2Space N]
    {f : ι → Nˣ} {r₁ r₂ : N} {l : Filter ι} [l.NeBot] (h₁ : Tendsto (fun x => ↑(f x)) l (𝓝 r₁))
    (h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝 r₂)) : Nˣ where
  val := r₁
  inv := r₂
  val_inv := by
    symm
    simpa using h₁.mul h₂
  inv_val := by
    symm
    simpa using h₂.mul h₁

@[to_additive]
instance Prod.continuousMul [TopologicalSpace N] [Mul N] [ContinuousMul N] :
    ContinuousMul (M × N) :=
  ⟨by apply Continuous.prodMk <;> fun_prop⟩

@[to_additive]
instance Prod.separatelyContinuousMul {M N : Type*}
    [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M]
    [TopologicalSpace N] [Mul N] [SeparatelyContinuousMul N] :
    SeparatelyContinuousMul (M × N) where
  continuous_const_mul {_} := by apply Continuous.prodMk <;> fun_prop
  continuous_mul_const {_} := by apply Continuous.prodMk <;> fun_prop

@[to_additive]
instance Pi.continuousMul {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, ContinuousMul (C i)] : ContinuousMul (∀ i, C i) where
  continuous_mul :=
    continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'

@[to_additive]
instance Pi.separatelyContinuousMul {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, SeparatelyContinuousMul (C i)] : SeparatelyContinuousMul (∀ i, C i) where
  continuous_mul_const {_} := continuous_pi fun i ↦ (continuous_apply i).mul_const _
  continuous_const_mul {_} := continuous_pi fun i ↦ (continuous_apply i).const_mul _

/-- A version of `Pi.continuousMul` for non-dependent functions. It is needed because sometimes
Lean 3 fails to use `Pi.continuousMul` for non-dependent functions. -/
@[to_additive /-- A version of `Pi.continuousAdd` for non-dependent functions. It is needed
because sometimes Lean fails to use `Pi.continuousAdd` for non-dependent functions. -/]
instance Pi.continuousMul' : ContinuousMul (ι → M) :=
  Pi.continuousMul

@[to_additive]
instance (priority := 100) continuousMul_of_discreteTopology [TopologicalSpace N] [Mul N]
    [DiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_discreteTopology⟩

@[to_additive]
instance (priority := 100) continuousMul_of_indiscreteTopology [TopologicalSpace N] [Mul N]
    [IndiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_indiscreteTopology⟩

open Filter

open Function

@[to_additive]
theorem ContinuousMul.of_nhds_one {M : Type u} [Monoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ˢ 𝓝 1) <| 𝓝 1)
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : ContinuousMul M :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    have key : (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) := by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀ * y₀ * x := by
      ext x
      simp [mul_assoc]
    calc
      map (uncurry (· * ·)) (𝓝 (x₀, y₀)) = map (uncurry (· * ·)) (𝓝 x₀ ×ˢ 𝓝 y₀) := by
        rw [nhds_prod_eq]
      _ = map (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) (𝓝 1 ×ˢ 𝓝 1) := by
        unfold uncurry
        rw [hleft x₀, hright y₀, prod_map_map_eq, Filter.map_map, Function.comp_def]
      _ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ˢ 𝓝 1)) := by
        rw [key, ← Filter.map_map]
      _ ≤ map ((fun x : M => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) := map_mono hmul
      _ = 𝓝 (x₀ * y₀) := by
        rw [← Filter.map_map, ← hright, hleft y₀, Filter.map_map, key₂, ← hleft]⟩

@[to_additive]
theorem continuousMul_of_comm_of_nhds_one (M : Type u) [CommMonoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : ContinuousMul M := by
  apply ContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]

end ContinuousMul

section PointwiseLimits

variable (M₁ M₂ : Type*) [TopologicalSpace M₂] [T2Space M₂]

@[to_additive]
theorem isClosed_setOf_map_one [One M₁] [One M₂] : IsClosed { f : M₁ → M₂ | f 1 = 1 } :=
  isClosed_eq (continuous_apply 1) continuous_const

@[to_additive]
theorem isClosed_setOf_map_mul [Mul M₁] [Mul M₂] [ContinuousMul M₂] :
    IsClosed { f : M₁ → M₂ | ∀ x y, f (x * y) = f x * f y } := by
  simp only [setOf_forall]
  exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
    isClosed_eq (continuous_apply _) (by fun_prop)

section Semigroup

variable {M₁ M₂} [Mul M₁] [Mul M₂] [ContinuousMul M₂]
  {F : Type*} [FunLike F M₁ M₂] [MulHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled semigroup homomorphism `M₁ →ₙ* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →ₙ* M₂` (or another type of bundled
homomorphisms that has a `MulHomClass` instance) to `M₁ → M₂`. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Construct a bundled additive semigroup homomorphism `M₁ →ₙ+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →ₙ+ M₂` (or another
type of bundled homomorphisms that has an `AddHomClass` instance) to `M₁ → M₂`. -/]
def mulHomOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (range fun (f : F) (x : M₁) => f x)) : M₁ →ₙ* M₂ where
  toFun := f
  map_mul' := (isClosed_setOf_map_mul M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_mul) hf

/-- Construct a bundled semigroup homomorphism from a pointwise limit of semigroup homomorphisms. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Construct a bundled additive semigroup homomorphism from a pointwise limit of additive
semigroup homomorphisms -/]
def mulHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →ₙ* M₂ :=
  mulHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ => mem_range_self _

variable (M₁ M₂)

@[to_additive]
theorem MulHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →ₙ* M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨mulHomOfMemClosureRangeCoe f hf, rfl⟩

end Semigroup

section Monoid

variable {M₁ M₂} [MulOneClass M₁] [MulOneClass M₂] [ContinuousMul M₂]
  {F : Type*} [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `MonoidHomClass` instance) to `M₁ → M₂`. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another
type of bundled homomorphisms that has an `AddMonoidHomClass` instance) to `M₁ → M₂`. -/]
def monoidHomOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (range fun (f : F) (x : M₁) => f x)) : M₁ →* M₂ where
  toFun := f
  map_one' := (isClosed_setOf_map_one M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOf_map_mul M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_mul) hf

/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive (attr := simps! -fullyApplied)
  /-- Construct a bundled additive monoid homomorphism from a pointwise limit of additive
monoid homomorphisms -/]
def monoidHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →* M₂ :=
  monoidHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| Eventually.of_forall fun _ => mem_range_self _

variable (M₁ M₂)

@[to_additive]
theorem MonoidHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →* M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩

end Monoid

end PointwiseLimits

@[to_additive]
theorem Topology.IsInducing.continuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] [ContinuousMul N] (f : F)
    (hf : IsInducing f) : ContinuousMul M :=
  ⟨(hf.continuousSMul hf.continuous (map_mul f _ _)).1⟩

@[to_additive]
theorem continuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    [TopologicalSpace N] [ContinuousMul N] (f : F) : @ContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.continuousMul f ⟨rfl⟩

@[to_additive]
instance Subsemigroup.continuousMul [TopologicalSpace M] [Semigroup M] [ContinuousMul M]
    (S : Subsemigroup M) : ContinuousMul S :=
  IsInducing.continuousMul ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]
instance Submonoid.continuousMul [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    (S : Submonoid M) : ContinuousMul S :=
  S.toSubsemigroup.continuousMul

open MulOpposite in
@[to_additive]
theorem Topology.IsInducing.separatelyContinuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace M] [TopologicalSpace N] [SeparatelyContinuousMul N]
    (f : F) (hf : IsInducing f) : SeparatelyContinuousMul M where
  continuous_const_mul := (hf.continuousConstSMul f (map_mul f _ _)).1 _
  continuous_mul_const {m} :=
    have := ((opHomeomorph.isInducing.comp hf).comp (opHomeomorph.symm.isInducing)
      |>.continuousConstSMul (fun x ↦ op (f (unop x))) (by simp)).1 (op m)
    continuous_unop.comp <| this.comp continuous_op

@[to_additive]
theorem separatelyContinuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N]
    [MulHomClass F M N] [TopologicalSpace N] [SeparatelyContinuousMul N] (f : F) :
    @SeparatelyContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  IsInducing.separatelyContinuousMul f ⟨rfl⟩

@[to_additive]
instance Subsemigroup.separatelyContinuousMul [TopologicalSpace M] [Semigroup M]
    [SeparatelyContinuousMul M] (S : Subsemigroup M) : SeparatelyContinuousMul S :=
  IsInducing.separatelyContinuousMul
    ({ toFun := (↑), map_mul' := fun _ _ => rfl } : MulHom S M) ⟨rfl⟩

@[to_additive]
instance Submonoid.separatelyContinuousMul [TopologicalSpace M] [Monoid M]
    [SeparatelyContinuousMul M] (S : Submonoid M) : SeparatelyContinuousMul S :=
  S.toSubsemigroup.separatelyContinuousMul
section MulZeroClass

open Filter

variable {α β : Type*}
variable [TopologicalSpace M] [MulZeroClass M] [ContinuousMul M]

theorem exists_mem_nhds_zero_mul_subset
    {K U : Set M} (hK : IsCompact K) (hU : U ∈ 𝓝 0) : ∃ V ∈ 𝓝 0, K * V ⊆ U := by
  refine hK.induction_on ?_ ?_ ?_ ?_
  · exact ⟨univ, by simp⟩
  · rintro s t hst ⟨V, hV, hV'⟩
    exact ⟨V, hV, (mul_subset_mul_right hst).trans hV'⟩
  · rintro s t ⟨V, V_in, hV'⟩ ⟨W, W_in, hW'⟩
    use V ∩ W, inter_mem V_in W_in
    rw [union_mul]
    exact
      union_subset ((mul_subset_mul_left V.inter_subset_left).trans hV')
        ((mul_subset_mul_left V.inter_subset_right).trans hW')
  · intro x hx
    have := tendsto_mul (show U ∈ 𝓝 (x * 0) by simpa using hU)
    rw [nhds_prod_eq, mem_map, mem_prod_iff] at this
    rcases this with ⟨t, ht, s, hs, h⟩
    rw [← image_subset_iff, image_mul_prod] at h
    exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, s, hs, h⟩

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M` which is disjoint from the cocompact filter. Then, the multiplication map
`M × M → M` tends to zero on the filter product `𝓝 0 ×ˢ l`. -/
theorem tendsto_mul_nhds_zero_prod_of_disjoint_cocompact {l : Filter M}
    (hl : Disjoint l (cocompact M)) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) (𝓝 0 ×ˢ l) (𝓝 0) := calc
  map (fun x : M × M ↦ x.1 * x.2) (𝓝 0 ×ˢ l)
  _ ≤ map (fun x : M × M ↦ x.1 * x.2) (𝓝ˢ ({0} ×ˢ Set.univ)) :=
    map_mono <| nhds_prod_le_of_disjoint_cocompact 0 hl
  _ ≤ 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨hx, _⟩ ↦ mul_eq_zero_of_left hx _

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M` which is disjoint from the cocompact filter. Then, the multiplication map
`M × M → M` tends to zero on the filter product `l ×ˢ 𝓝 0`. -/
theorem tendsto_mul_prod_nhds_zero_of_disjoint_cocompact {l : Filter M}
    (hl : Disjoint l (cocompact M)) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) (l ×ˢ 𝓝 0) (𝓝 0) := calc
  map (fun x : M × M ↦ x.1 * x.2) (l ×ˢ 𝓝 0)
  _ ≤ map (fun x : M × M ↦ x.1 * x.2) (𝓝ˢ (Set.univ ×ˢ {0})) :=
    map_mono <| prod_nhds_le_of_disjoint_cocompact 0 hl
  _ ≤ 𝓝 0 := continuous_mul.tendsto_nhdsSet_nhds fun _ ⟨_, hx⟩ ↦ mul_eq_zero_of_right _ hx

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M × M` which is disjoint from the cocompact filter. Then, the multiplication
map `M × M → M` tends to zero on `(𝓝 0).coprod (𝓝 0) ⊓ l`. -/
theorem tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact {l : Filter (M × M)}
    (hl : Disjoint l (cocompact (M × M))) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) ((𝓝 0).coprod (𝓝 0) ⊓ l) (𝓝 0) := by
  have := calc
    (𝓝 0).coprod (𝓝 0) ⊓ l
    _ ≤ (𝓝 0).coprod (𝓝 0) ⊓ map Prod.fst l ×ˢ map Prod.snd l :=
      inf_le_inf_left _ le_prod_map_fst_snd
    _ ≤ 𝓝 0 ×ˢ map Prod.snd l ⊔ map Prod.fst l ×ˢ 𝓝 0 :=
      coprod_inf_prod_le _ _ _ _
  apply (Tendsto.sup _ _).mono_left this
  · apply tendsto_mul_nhds_zero_prod_of_disjoint_cocompact
    exact disjoint_map_cocompact continuous_snd hl
  · apply tendsto_mul_prod_nhds_zero_of_disjoint_cocompact
    exact disjoint_map_cocompact continuous_fst hl

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `l` be a filter on `M × M` which is both disjoint from the cocompact filter and less than or
equal to `(𝓝 0).coprod (𝓝 0)`. Then the multiplication map `M × M → M` tends to zero on `l`. -/
theorem tendsto_mul_nhds_zero_of_disjoint_cocompact {l : Filter (M × M)}
    (hl : Disjoint l (cocompact (M × M))) (h'l : l ≤ (𝓝 0).coprod (𝓝 0)) :
    Tendsto (fun x : M × M ↦ x.1 * x.2) l (𝓝 0) := by
  simpa [inf_eq_right.mpr h'l] using tendsto_mul_coprod_nhds_zero_inf_of_disjoint_cocompact hl

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `f : α → M` and `g : α → M` be functions. If `f` tends to zero on a filter `l`
and the image of `l` under `g` is disjoint from the cocompact filter on `M`, then
`fun x : α ↦ f x * g x` also tends to zero on `l`. -/
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_right {f g : α → M} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (hg : Disjoint (map g l) (cocompact M)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) :=
  tendsto_mul_nhds_zero_prod_of_disjoint_cocompact hg |>.comp (hf.prodMk tendsto_map)

/-- Let `M` be a topological space with a continuous multiplication operation and a `0`.
Let `f : α → M` and `g : α → M` be functions. If `g` tends to zero on a filter `l`
and the image of `l` under `f` is disjoint from the cocompact filter on `M`, then
`fun x : α ↦ f x * g x` also tends to zero on `l`. -/
theorem Tendsto.tendsto_mul_zero_of_disjoint_cocompact_left {f g : α → M} {l : Filter α}
    (hf : Disjoint (map f l) (cocompact M)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) :=
  tendsto_mul_prod_nhds_zero_of_disjoint_cocompact hf |>.comp (tendsto_map.prodMk hg)

/-- If `f : α → M` and `g : β → M` are continuous and both tend to zero on the cocompact filter,
then `fun i : α × β ↦ f i.1 * g i.2` also tends to zero on the cocompact filter. -/
theorem tendsto_mul_cocompact_nhds_zero [TopologicalSpace α] [TopologicalSpace β]
    {f : α → M} {g : β → M} (f_cont : Continuous f) (g_cont : Continuous g)
    (hf : Tendsto f (cocompact α) (𝓝 0)) (hg : Tendsto g (cocompact β) (𝓝 0)) :
    Tendsto (fun i : α × β ↦ f i.1 * g i.2) (cocompact (α × β)) (𝓝 0) := by
  set l : Filter (M × M) := map (Prod.map f g) (cocompact (α × β)) with l_def
  set K : Set (M × M) := (insert 0 (range f)) ×ˢ (insert 0 (range g))
  have K_compact : IsCompact K := .prod (hf.isCompact_insert_range_of_cocompact f_cont)
    (hg.isCompact_insert_range_of_cocompact g_cont)
  have K_mem_l : K ∈ l := eventually_map.mpr <| .of_forall fun ⟨x, y⟩ ↦
    ⟨mem_insert_of_mem _ (mem_range_self _), mem_insert_of_mem _ (mem_range_self _)⟩
  have l_compact : Disjoint l (cocompact (M × M)) := by
    rw [disjoint_cocompact_right]
    exact ⟨K, K_mem_l, K_compact⟩
  have l_le_coprod : l ≤ (𝓝 0).coprod (𝓝 0) := by
    rw [l_def, ← coprod_cocompact]
    exact hf.prodMap_coprod hg
  exact tendsto_mul_nhds_zero_of_disjoint_cocompact l_compact l_le_coprod |>.comp tendsto_map

/-- If `f : α → M` and `g : β → M` both tend to zero on the cofinite filter, then so does
`fun i : α × β ↦ f i.1 * g i.2`. -/
theorem tendsto_mul_cofinite_nhds_zero {f : α → M} {g : β → M}
    (hf : Tendsto f cofinite (𝓝 0)) (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun i : α × β ↦ f i.1 * g i.2) cofinite (𝓝 0) := by
  letI : TopologicalSpace α := ⊥
  haveI : DiscreteTopology α := discreteTopology_bot α
  letI : TopologicalSpace β := ⊥
  haveI : DiscreteTopology β := discreteTopology_bot β
  rw [← cocompact_eq_cofinite] at *
  exact tendsto_mul_cocompact_nhds_zero
    continuous_of_discreteTopology continuous_of_discreteTopology hf hg

end MulZeroClass

section GroupWithZero

lemma GroupWithZero.isOpen_singleton_zero [GroupWithZero M] [TopologicalSpace M]
    [ContinuousMul M] [CompactSpace M] [T1Space M] :
    IsOpen {(0 : M)} := by
  obtain ⟨U, hU, h0U, h1U⟩ := t1Space_iff_exists_open.mp ‹_› zero_ne_one
  obtain ⟨W, hW, hW'⟩ := exists_mem_nhds_zero_mul_subset isCompact_univ (hU.mem_nhds h0U)
  by_cases H : ∃ x ≠ 0, x ∈ W
  · obtain ⟨x, hx, hxW⟩ := H
    cases h1U (hW' (by simpa [hx] using Set.mul_mem_mul (Set.mem_univ x⁻¹) hxW))
  · obtain rfl : W = {0} := subset_antisymm
      (by simpa [not_imp_not] using H) (by simpa using mem_of_mem_nhds hW)
    simpa [isOpen_iff_mem_nhds]

end GroupWithZero

section MulOneClass

variable [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

@[to_additive exists_open_nhds_zero_half]
theorem exists_open_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s := by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s ∈ 𝓝 ((1, 1) : M × M) :=
    tendsto_mul (by simpa only [one_mul] using hs)
  simpa only [prod_subset_iff] using exists_nhds_square this

@[to_additive exists_nhds_zero_half]
theorem exists_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s :=
  let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `V * V ⊆ U`. -/
@[to_additive /-- Given an open neighborhood `U` of `0` there is an open neighborhood `V` of `0`
  such that `V + V ⊆ U`. -/]
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ V * V ⊆ U := by
  simpa only [mul_subset_iff] using exists_open_nhds_one_split hU

@[to_additive]
theorem Filter.HasBasis.mul_self {p : ι → Prop} {s : ι → Set M} (h : (𝓝 1).HasBasis p s) :
    (𝓝 1).HasBasis p fun i => s i * s i := by
  rw [← nhds_mul_nhds_one, ← map₂_mul, ← map_uncurry_prod]
  simpa only [← image_mul_prod] using h.prod_self.map _

end MulOneClass

section ContinuousMul

section Semigroup

variable [TopologicalSpace M] [Semigroup M] [SeparatelyContinuousMul M]

@[to_additive]
theorem Subsemigroup.top_closure_mul_self_subset (s : Subsemigroup M) :
    _root_.closure (s : Set M) * _root_.closure s ⊆ _root_.closure s :=
  image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const
      hx hy fun _ ha _ hb => s.mul_mem ha hb

/-- The (topological-space) closure of a subsemigroup of a space `M` with `ContinuousMul` is
itself a subsemigroup. -/
@[to_additive /-- The (topological-space) closure of an additive submonoid of a space `M` with
`ContinuousAdd` is itself an additive submonoid. -/]
def Subsemigroup.topologicalClosure (s : Subsemigroup M) : Subsemigroup M where
  carrier := _root_.closure (s : Set M)
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]
theorem Subsemigroup.coe_topologicalClosure (s : Subsemigroup M) :
    (s.topologicalClosure : Set M) = _root_.closure (s : Set M) := rfl

@[to_additive]
theorem Subsemigroup.le_topologicalClosure (s : Subsemigroup M) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
theorem Subsemigroup.isClosed_topologicalClosure (s : Subsemigroup M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

@[to_additive]
theorem Subsemigroup.topologicalClosure_minimal (s : Subsemigroup M) {t : Subsemigroup M}
    (h : s ≤ t) (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t := closure_minimal h ht

@[to_additive (attr := gcongr)]
theorem Subsemigroup.topologicalClosure_mono {s t : Subsemigroup M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a subsemigroup of a topological semigroup is commutative, then so is its topological
closure.

See note [reducible non-instances] -/
@[to_additive /-- If a submonoid of an additive topological monoid is commutative, then so is its
topological closure.

See note [reducible non-instances] -/]
abbrev Subsemigroup.commSemigroupTopologicalClosure [T2Space M] (s : Subsemigroup M)
    (hs : ∀ x y : s, x * y = y * x) : CommSemigroup s.topologicalClosure :=
  { MulMemClass.toSemigroup s.topologicalClosure with
    mul_comm :=
      have : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := fun x hx y hy =>
        congr_arg Subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩)
      fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      Subtype.ext <| by
        refine eqOn_closure₂' this ?_ ?_ ?_ ?_ x hx y hy
        all_goals fun_prop }

@[to_additive]
theorem IsCompact.mul [TopologicalSpace N] [Mul N] [ContinuousMul N] {s t : Set N}
    (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul

end Semigroup

variable [TopologicalSpace M] [Monoid M]

section SeparatelyContinuousMul

variable [SeparatelyContinuousMul M]

@[to_additive]
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s ⊆ _root_.closure s :=
  image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂' continuous_const_mul continuous_mul_const hx hy
      fun _ ha _ hb ↦ s.mul_mem ha hb

@[to_additive]
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s = _root_.closure s :=
  Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, hx, 1, _root_.subset_closure s.one_mem, mul_one _⟩

/-- The (topological-space) closure of a submonoid of a space `M` with `ContinuousMul` is
itself a submonoid. -/
@[to_additive /-- The (topological-space) closure of an additive submonoid of a space `M` with
`ContinuousAdd` is itself an additive submonoid. -/]
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M where
  carrier := _root_.closure (s : Set M)
  one_mem' := _root_.subset_closure s.one_mem
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩

@[to_additive]
theorem Submonoid.coe_topologicalClosure (s : Submonoid M) :
    (s.topologicalClosure : Set M) = _root_.closure (s : Set M) := rfl

@[to_additive]
theorem Submonoid.le_topologicalClosure (s : Submonoid M) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

@[to_additive]
theorem Submonoid.isClosed_topologicalClosure (s : Submonoid M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure

@[to_additive]
theorem Submonoid.topologicalClosure_minimal (s : Submonoid M) {t : Submonoid M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t := closure_minimal h ht

@[to_additive (attr := gcongr)]
theorem Submonoid.topologicalClosure_mono {s t : Submonoid M} (h : s ≤ t) :
    s.topologicalClosure ≤ t.topologicalClosure :=
  _root_.closure_mono h

/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive /-- If a submonoid of an additive topological monoid is commutative, then so is its
topological closure.

See note [reducible non-instances]. -/]
abbrev Submonoid.commMonoidTopologicalClosure [T2Space M] (s : Submonoid M)
    (hs : ∀ x y : s, x * y = y * x) : CommMonoid s.topologicalClosure :=
  { s.topologicalClosure.toMonoid, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

/-- Left-multiplication by a left-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) :
    Filter.Tendsto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_const_mul b))
  convert Filter.tendsto_id
  ext x
  simp [← mul_assoc, ha]

/-- Right-multiplication by a right-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) :
    Filter.Tendsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_mul_const b))
  simp only [comp_mul_right, ha, mul_one]
  exact Filter.tendsto_id

end SeparatelyContinuousMul

variable [ContinuousMul M]

@[to_additive exists_nhds_zero_quarter]
theorem exists_nhds_one_split4 {u : Set M} (hu : u ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u := by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)

@[to_additive]
theorem tendsto_list_prod {f : ι → α → M} {x : Filter α} {a : ι → M} :
    ∀ l : List ι,
      (∀ i ∈ l, Tendsto (f i) x (𝓝 (a i))) →
        Tendsto (fun b => (l.map fun c => f c b).prod) x (𝓝 (l.map a).prod)
  | [], _ => by simp [tendsto_const_nhds]
  | f::l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact
      (h f List.mem_cons_self).mul
        (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_mem _ hc))

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀ i ∈ l, Continuous (f i)) :
    Continuous fun a => (l.map fun i => f i a).prod :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x

@[to_additive]
theorem continuousOn_list_prod {f : ι → X → M} (l : List ι) {t : Set X}
    (h : ∀ i ∈ l, ContinuousOn (f i) t) :
    ContinuousOn (fun a => (l.map fun i => f i a).prod) t := by
  intro x hx
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx]
  refine tendsto_list_prod _ fun i hi => ?_
  specialize h i hi x hx
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx] at h
  exact h

@[to_additive (attr := continuity)]
theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n
  | 0 => by simpa using continuous_const
  | k + 1 => by
    simp only [pow_succ']
    exact continuous_id.mul (continuous_pow _)

instance AddMonoid.continuousConstSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousConstSMul ℕ A :=
  ⟨continuous_nsmul⟩

instance AddMonoid.continuousSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousSMul ℕ A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_nsmul⟩

-- We register `Continuous.pow` as a `continuity` lemma with low penalty (so
-- `continuity` will try it before other `continuity` lemmas). This is a
-- workaround for goals of the form `Continuous fun x => x ^ 2`, where
-- `continuity` applies `Continuous.mul` since the goal is defeq to
-- `Continuous fun x => x * x`.
--
-- To properly fix this, we should make sure that `continuity` applies its
-- lemmas with reducible transparency, preventing the unfolding of `^`. But this
-- is quite an invasive change.
@[to_additive (attr := aesop safe -100 (rule_sets := [Continuous]), fun_prop)]
theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous fun b => f b ^ n :=
  (continuous_pow n).comp h

@[to_additive]
theorem continuousOn_pow {s : Set M} (n : ℕ) : ContinuousOn (fun (x : M) => x ^ n) s :=
  (continuous_pow n).continuousOn

@[to_additive]
theorem continuousAt_pow (x : M) (n : ℕ) : ContinuousAt (fun (x : M) => x ^ n) x :=
  (continuous_pow n).continuousAt

@[to_additive]
theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : ℕ) :
    Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuousAt_pow _ _).tendsto.comp hf

@[to_additive]
theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
    (n : ℕ) : ContinuousWithinAt (fun x => f x ^ n) s x :=
  Filter.Tendsto.pow hf n

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) :
    ContinuousAt (fun x => f x ^ n) x :=
  Filter.Tendsto.pow hf n

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun x => f x ^ n) s := fun x hx => (hf x hx).pow n

/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instance applies when `R = A`, or when `[Algebra R A]` is available. -/
@[to_additive /-- If `R` acts on `A` via `A`, then continuous addition implies
continuous affine addition by constants. -/]
instance (priority := 100) IsScalarTower.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [IsScalarTower R A A] [TopologicalSpace A] [SeparatelyContinuousMul A] :
    ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp +singlePass only [← smul_one_mul q (_ : A)]
    fun_prop

/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instance applies when `R = Aᵐᵒᵖ`. -/
@[to_additive /-- If the action of `R` on `A` commutes with left-addition, then
continuous addition implies continuous affine addition by constants.

Notably, this instance applies when `R = Aᵃᵒᵖ`. -/]
instance (priority := 100) SMulCommClass.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [SMulCommClass R A A] [TopologicalSpace A] [SeparatelyContinuousMul A] :
    ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp +singlePass only [← mul_smul_one q (_ : A)]
    fun_prop

end ContinuousMul

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoid α] [ContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `Topology.Algebra.Group`,
because the predicate `ContinuousInv` has not yet been defined. -/
@[to_additive /-- If addition on an additive monoid is continuous, then addition on the additive
units of the monoid, with respect to the induced topology, is continuous.

Negation is also continuous, but we register this in a later file, `Topology.Algebra.Group`, because
the predicate `ContinuousNeg` has not yet been defined. -/]
instance : ContinuousMul αˣ := isInducing_embedProduct.continuousMul (embedProduct α)

end Units

@[to_additive (attr := fun_prop)]
theorem Continuous.units_map [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →* N) (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

section

variable [TopologicalSpace M] [CommMonoid M]

@[to_additive]
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) :
    (S : Set M) ∈ 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem

variable [ContinuousMul M]

@[to_additive]
theorem tendsto_multiset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Multiset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => (s.map fun c => f c b).prod) x (𝓝 (s.map a).prod) := by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l

@[to_additive]
theorem tendsto_finset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => ∏ c ∈ s, f c b) x (𝓝 (∏ c ∈ s, a c)) :=
  tendsto_multiset_prod _

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => (s.map fun i => f i a).prod := by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l

@[to_additive]
theorem continuousOn_multiset_prod {f : ι → X → M} (s : Multiset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => (s.map fun i => f i a).prod) t := by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_finset_prod {f : ι → X → M} (s : Finset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => ∏ i ∈ s, f i a :=
  continuous_multiset_prod _

@[to_additive]
theorem continuousOn_finset_prod {f : ι → X → M} (s : Finset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => ∏ i ∈ s, f i a) t :=
  continuousOn_multiset_prod _

@[to_additive]
theorem eventuallyEq_prod {X M : Type*} [CommMonoid M] {s : Finset ι} {l : Filter X}
    {f g : ι → X → M} (hs : ∀ i ∈ s, f i =ᶠ[l] g i) : ∏ i ∈ s, f i =ᶠ[l] ∏ i ∈ s, g i := by
  replace hs : ∀ᶠ x in l, ∀ i ∈ s, f i x = g i x := by rwa [eventually_all_finset]
  filter_upwards [hs] with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]

open Function

@[to_additive]
theorem LocallyFinite.exists_finset_mulSupport {M : Type*} [One M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport <| f i) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, (mulSupport fun i => f i x) ⊆ I := by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine ⟨hUf.toFinset, mem_of_superset hxU fun y hy i hi => ?_⟩
  rw [hUf.coe_toFinset]
  exact ⟨y, hi, hy⟩

@[to_additive]
theorem finprod_eventually_eq_prod {M : Type*} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport (f i)) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, ∏ᶠ i, f i y = ∏ i ∈ s, f i y :=
  let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun _ hy => finprod_eq_prod_of_mulSupport_subset _ fun _ hi => hy hi⟩

@[to_additive]
theorem continuous_finprod {f : ι → X → M} (hc : ∀ i, Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ i, f i x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine ContinuousAt.congr ?_ (EventuallyEq.symm hs)
  exact tendsto_finset_prod _ fun i _ => (hc i).continuousAt

@[to_additive]
theorem continuous_finprod_cond {f : ι → X → M} {p : ι → Prop} (hc : ∀ i, p i → Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    Continuous fun x => ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)

end

instance [TopologicalSpace M] [Mul M] [ContinuousMul M] : ContinuousAdd (Additive M) where
  continuous_add := @continuous_mul M _ _ _

instance [TopologicalSpace M] [Add M] [ContinuousAdd M] : ContinuousMul (Multiplicative M) where
  continuous_mul := @continuous_add M _ _ _

instance [TopologicalSpace M] [Mul M] [SeparatelyContinuousMul M] :
    SeparatelyContinuousAdd (Additive M) where
  continuous_const_add := @continuous_const_mul M _ _ _
  continuous_add_const := @continuous_mul_const M _ _ _

instance [TopologicalSpace M] [Add M] [SeparatelyContinuousAdd M] :
    SeparatelyContinuousMul (Multiplicative M) where
  continuous_const_mul := @continuous_const_add M _ _ _
  continuous_mul_const := @continuous_add_const M _ _ _

section LatticeOps

variable {ι' : Sort*} [Mul M]

@[to_additive]
theorem continuousMul_sInf {ts : Set (TopologicalSpace M)}
    (h : ∀ t ∈ ts, @ContinuousMul M t _) : @ContinuousMul M (sInf ts) _ :=
  letI := sInf ts
  { continuous_mul :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom₂ ht ht (@ContinuousMul.continuous_mul M t _ (h t ht)) }

@[to_additive]
theorem continuousMul_iInf {ts : ι' → TopologicalSpace M}
    (h' : ∀ i, @ContinuousMul M (ts i) _) : @ContinuousMul M (⨅ i, ts i) _ := by
  rw [← sInf_range]
  exact continuousMul_sInf (Set.forall_mem_range.mpr h')

@[to_additive]
theorem continuousMul_inf {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _)
    (h₂ : @ContinuousMul M t₂ _) : @ContinuousMul M (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousMul_iInf fun b => ?_
  cases b <;> assumption

end LatticeOps

namespace ContinuousMap

variable [Mul X] [SeparatelyContinuousMul X]

/-- The continuous map `fun y => y * x` -/
@[to_additive /-- The continuous map `fun y => y + x` -/]
protected def mulRight (x : X) : C(X, X) :=
  mk _ (continuous_mul_const x)

@[to_additive (attr := simp)]
theorem coe_mulRight (x : X) : ⇑(ContinuousMap.mulRight x) = fun y => y * x :=
  rfl

/-- The continuous map `fun y => x * y` -/
@[to_additive /-- The continuous map `fun y => x + y` -/]
protected def mulLeft (x : X) : C(X, X) :=
  mk _ (continuous_const_mul x)

@[to_additive (attr := simp)]
theorem coe_mulLeft (x : X) : ⇑(ContinuousMap.mulLeft x) = fun y => x * y :=
  rfl

end ContinuousMap
