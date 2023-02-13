/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module topology.algebra.monoid
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Finprod
import Mathbin.Order.Filter.Pointwise
import Mathbin.Topology.Algebra.MulAction
import Mathbin.Algebra.BigOperators.Pi

/-!
# Theory of topological monoids

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/


universe u v

open Classical Set Filter TopologicalSpace

open Classical Topology BigOperators Pointwise

variable {ι α X M N : Type _} [TopologicalSpace X]

@[to_additive]
theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X → M) :=
  @continuous_const _ _ _ _ 1
#align continuous_one continuous_one
#align continuous_zero continuous_zero

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `add_monoid M` and `has_continuous_add M`.

Continuity in only the left/right argument can be stated using
`has_continuous_const_vadd α α`/`has_continuous_const_vadd αᵐᵒᵖ α`. -/
class HasContinuousAdd (M : Type u) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2
#align has_continuous_add HasContinuousAdd

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `monoid M`
and `has_continuous_mul M`.

Continuity in only the left/right argument can be stated using
`has_continuous_const_smul α α`/`has_continuous_const_smul αᵐᵒᵖ α`. -/
@[to_additive]
class HasContinuousMul (M : Type u) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2
#align has_continuous_mul HasContinuousMul
#align has_continuous_add HasContinuousAdd

section HasContinuousMul

variable [TopologicalSpace M] [Mul M] [HasContinuousMul M]

@[to_additive]
instance : HasContinuousMul Mᵒᵈ :=
  ‹HasContinuousMul M›

@[to_additive]
theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 :=
  HasContinuousMul.continuous_mul
#align continuous_mul continuous_mul
#align continuous_add continuous_add

@[to_additive]
instance HasContinuousMul.to_hasContinuousSmul : HasContinuousSmul M M :=
  ⟨continuous_mul⟩
#align has_continuous_mul.to_has_continuous_smul HasContinuousMul.to_hasContinuousSmul
#align has_continuous_add.to_has_continuous_vadd HasContinuousAdd.to_has_continuous_vadd

@[to_additive]
instance HasContinuousMul.to_hasContinuousSmul_op : HasContinuousSmul Mᵐᵒᵖ M :=
  ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) from
      continuous_mul.comp <|
        continuous_swap.comp <| Continuous.prod_map MulOpposite.continuous_unop continuous_id⟩
#align has_continuous_mul.to_has_continuous_smul_op HasContinuousMul.to_hasContinuousSmul_op
#align has_continuous_add.to_has_continuous_vadd_op HasContinuousAdd.to_has_continuous_vadd_op

@[continuity, to_additive]
theorem Continuous.mul {f g : X → M} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x * g x :=
  continuous_mul.comp (hf.prod_mk hg : _)
#align continuous.mul Continuous.mul
#align continuous.add Continuous.add

@[to_additive]
theorem continuous_mul_left (a : M) : Continuous fun b : M => a * b :=
  continuous_const.mul continuous_id
#align continuous_mul_left continuous_mul_left
#align continuous_add_left continuous_add_left

@[to_additive]
theorem continuous_mul_right (a : M) : Continuous fun b : M => b * a :=
  continuous_id.mul continuous_const
#align continuous_mul_right continuous_mul_right
#align continuous_add_right continuous_add_right

@[to_additive]
theorem ContinuousOn.mul {f g : X → M} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x * g x) s :=
  (continuous_mul.comp_continuousOn (hf.Prod hg) : _)
#align continuous_on.mul ContinuousOn.mul
#align continuous_on.add ContinuousOn.add

@[to_additive]
theorem tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
  continuous_iff_continuousAt.mp HasContinuousMul.continuous_mul (a, b)
#align tendsto_mul tendsto_mul
#align tendsto_add tendsto_add

@[to_additive]
theorem Filter.Tendsto.mul {f g : α → M} {x : Filter α} {a b : M} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => f x * g x) x (𝓝 (a * b)) :=
  tendsto_mul.comp (hf.prod_mk_nhds hg)
#align filter.tendsto.mul Filter.Tendsto.mul
#align filter.tendsto.add Filter.Tendsto.add

@[to_additive]
theorem Filter.Tendsto.const_mul (b : M) {c : M} {f : α → M} {l : Filter α}
    (h : Tendsto (fun k : α => f k) l (𝓝 c)) : Tendsto (fun k : α => b * f k) l (𝓝 (b * c)) :=
  tendsto_const_nhds.mul h
#align filter.tendsto.const_mul Filter.Tendsto.const_mul
#align filter.tendsto.const_add Filter.Tendsto.const_add

@[to_additive]
theorem Filter.Tendsto.mul_const (b : M) {c : M} {f : α → M} {l : Filter α}
    (h : Tendsto (fun k : α => f k) l (𝓝 c)) : Tendsto (fun k : α => f k * b) l (𝓝 (c * b)) :=
  h.mul tendsto_const_nhds
#align filter.tendsto.mul_const Filter.Tendsto.mul_const
#align filter.tendsto.add_const Filter.Tendsto.add_const

@[to_additive]
theorem le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b ≤ 𝓝 (a * b) :=
  by
  rw [← map₂_mul, ← map_uncurry_prod, ← nhds_prod_eq]
  exact continuous_mul.tendsto _
#align le_nhds_mul le_nhds_mul
#align le_nhds_add le_nhds_add

@[simp, to_additive]
theorem nhds_one_mul_nhds {M} [MulOneClass M] [TopologicalSpace M] [HasContinuousMul M] (a : M) :
    𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm <|
    le_mul_of_one_le_left' <| pure_le_nhds 1
#align nhds_one_mul_nhds nhds_one_mul_nhds
#align nhds_zero_add_nhds nhds_zero_add_nhds

@[simp, to_additive]
theorem nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpace M] [HasContinuousMul M] (a : M) :
    𝓝 a * 𝓝 1 = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm <|
    le_mul_of_one_le_right' <| pure_le_nhds 1
#align nhds_mul_nhds_one nhds_mul_nhds_one
#align nhds_add_nhds_zero nhds_add_nhds_zero

section tendsto_nhds

variable {𝕜 : Type _} [Preorder 𝕜] [Zero 𝕜] [Mul 𝕜] [TopologicalSpace 𝕜] [HasContinuousMul 𝕜]
  {l : Filter α} {f : α → 𝕜} {b c : 𝕜} (hb : 0 < b)

theorem Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] [PosMulReflectLT 𝕜]
    (h : Tendsto f l (𝓝[>] c)) : Tendsto (fun a => b * f a) l (𝓝[>] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_left hb).mpr
#align filter.tendsto_nhds_within_Ioi.const_mul Filter.TendstoNhdsWithinIoi.const_mul

theorem Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] [PosMulReflectLT 𝕜]
    (h : Tendsto f l (𝓝[<] c)) : Tendsto (fun a => b * f a) l (𝓝[<] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_left hb).mpr
#align filter.tendsto_nhds_within_Iio.const_mul Filter.TendstoNhdsWithinIio.const_mul

theorem Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] [MulPosReflectLT 𝕜]
    (h : Tendsto f l (𝓝[>] c)) : Tendsto (fun a => f a * b) l (𝓝[>] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_right hb).mpr
#align filter.tendsto_nhds_within_Ioi.mul_const Filter.TendstoNhdsWithinIoi.mul_const

theorem Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] [MulPosReflectLT 𝕜]
    (h : Tendsto f l (𝓝[<] c)) : Tendsto (fun a => f a * b) l (𝓝[<] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun j => (mul_lt_mul_right hb).mpr
#align filter.tendsto_nhds_within_Iio.mul_const Filter.TendstoNhdsWithinIio.mul_const

end tendsto_nhds

/-- Construct a unit from limits of units and their inverses. -/
@[to_additive Filter.Tendsto.addUnits
      "Construct an additive unit from limits of additive units\nand their negatives.",
  simps]
def Filter.Tendsto.units [TopologicalSpace N] [Monoid N] [HasContinuousMul N] [T2Space N]
    {f : ι → Nˣ} {r₁ r₂ : N} {l : Filter ι} [l.ne_bot] (h₁ : Tendsto (fun x => ↑(f x)) l (𝓝 r₁))
    (h₂ : Tendsto (fun x => ↑(f x)⁻¹) l (𝓝 r₂)) : Nˣ
    where
  val := r₁
  inv := r₂
  val_inv := by
    symm
    simpa using h₁.mul h₂
  inv_val := by
    symm
    simpa using h₂.mul h₁
#align filter.tendsto.units Filter.Tendsto.units
#align filter.tendsto.add_units Filter.Tendsto.addUnits

@[to_additive]
theorem ContinuousAt.mul {f g : X → M} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x * g x) x :=
  hf.mul hg
#align continuous_at.mul ContinuousAt.mul
#align continuous_at.add ContinuousAt.add

@[to_additive]
theorem ContinuousWithinAt.mul {f g : X → M} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (fun x => f x * g x) s x :=
  hf.mul hg
#align continuous_within_at.mul ContinuousWithinAt.mul
#align continuous_within_at.add ContinuousWithinAt.add

@[to_additive]
instance [TopologicalSpace N] [Mul N] [HasContinuousMul N] : HasContinuousMul (M × N) :=
  ⟨(continuous_fst.fst'.mul continuous_fst.snd').prod_mk
      (continuous_snd.fst'.mul continuous_snd.snd')⟩

@[to_additive]
instance Pi.hasContinuousMul {C : ι → Type _} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, HasContinuousMul (C i)] : HasContinuousMul (∀ i, C i)
    where continuous_mul :=
    continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'
#align pi.has_continuous_mul Pi.hasContinuousMul
#align pi.has_continuous_add Pi.has_continuous_add

/-- A version of `pi.has_continuous_mul` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_mul` for non-dependent functions. -/
@[to_additive
      "A version of `pi.has_continuous_add` for non-dependent functions. It is needed\nbecause sometimes Lean fails to use `pi.has_continuous_add` for non-dependent functions."]
instance Pi.has_continuous_mul' : HasContinuousMul (ι → M) :=
  Pi.hasContinuousMul
#align pi.has_continuous_mul' Pi.has_continuous_mul'
#align pi.has_continuous_add' Pi.has_continuous_add'

@[to_additive]
instance (priority := 100) hasContinuousMul_of_discreteTopology [TopologicalSpace N] [Mul N]
    [DiscreteTopology N] : HasContinuousMul N :=
  ⟨continuous_of_discreteTopology⟩
#align has_continuous_mul_of_discrete_topology hasContinuousMul_of_discreteTopology
#align has_continuous_add_of_discrete_topology has_continuous_add_of_discreteTopology

open Filter

open Function

@[to_additive]
theorem HasContinuousMul.of_nhds_one {M : Type u} [Monoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) <| 𝓝 1)
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1))
    (hright : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x * x₀) (𝓝 1)) : HasContinuousMul M :=
  ⟨by
    rw [continuous_iff_continuousAt]
    rintro ⟨x₀, y₀⟩
    have key :
      (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) =
        ((fun x => x₀ * x) ∘ fun x => x * y₀) ∘ uncurry (· * ·) :=
      by
      ext p
      simp [uncurry, mul_assoc]
    have key₂ : ((fun x => x₀ * x) ∘ fun x => y₀ * x) = fun x => x₀ * y₀ * x :=
      by
      ext x
      simp
    calc
      map (uncurry (· * ·)) (𝓝 (x₀, y₀)) = map (uncurry (· * ·)) (𝓝 x₀ ×ᶠ 𝓝 y₀) := by
        rw [nhds_prod_eq]
      _ = map (fun p : M × M => x₀ * p.1 * (p.2 * y₀)) (𝓝 1 ×ᶠ 𝓝 1) := by
        rw [uncurry, hleft x₀, hright y₀, prod_map_map_eq, Filter.map_map]
      _ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ᶠ 𝓝 1)) := by
        rw [key, ← Filter.map_map]
      _ ≤ map ((fun x : M => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) := map_mono hmul
      _ = 𝓝 (x₀ * y₀) := by rw [← Filter.map_map, ← hright, hleft y₀, Filter.map_map, key₂, ← hleft]
      ⟩
#align has_continuous_mul.of_nhds_one HasContinuousMul.of_nhds_one
#align has_continuous_add.of_nhds_zero HasContinuousAdd.of_nhds_zero

@[to_additive]
theorem hasContinuousMul_of_comm_of_nhds_one (M : Type u) [CommMonoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : HasContinuousMul M :=
  by
  apply HasContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]
#align has_continuous_mul_of_comm_of_nhds_one hasContinuousMul_of_comm_of_nhds_one
#align has_continuous_add_of_comm_of_nhds_zero has_continuous_add_of_comm_of_nhds_zero

end HasContinuousMul

section PointwiseLimits

variable (M₁ M₂ : Type _) [TopologicalSpace M₂] [T2Space M₂]

@[to_additive]
theorem isClosed_setOf_map_one [One M₁] [One M₂] : IsClosed { f : M₁ → M₂ | f 1 = 1 } :=
  isClosed_eq (continuous_apply 1) continuous_const
#align is_closed_set_of_map_one isClosed_setOf_map_one
#align is_closed_set_of_map_zero isClosed_setOf_map_zero

@[to_additive]
theorem isClosed_setOf_map_mul [Mul M₁] [Mul M₂] [HasContinuousMul M₂] :
    IsClosed { f : M₁ → M₂ | ∀ x y, f (x * y) = f x * f y } :=
  by
  simp only [set_of_forall]
  exact
    isClosed_interᵢ fun x =>
      isClosed_interᵢ fun y =>
        isClosed_eq (continuous_apply _) ((continuous_apply _).mul (continuous_apply _))
#align is_closed_set_of_map_mul isClosed_setOf_map_mul
#align is_closed_set_of_map_add isClosed_setOf_map_add

variable {M₁ M₂} [MulOneClass M₁] [MulOneClass M₂] [HasContinuousMul M₂] {F : Type _}
  [MonoidHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `monoid_hom_class` instance) to `M₁ → M₂`. -/
@[to_additive
      "Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`\nand a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another\ntype of bundled homomorphisms that has a `add_monoid_hom_class` instance) to `M₁ → M₂`.",
  simps (config := { fullyApplied := false })]
def monoidHomOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (range fun (f : F) (x : M₁) => f x)) : M₁ →* M₂
    where
  toFun := f
  map_one' := (isClosed_setOf_map_one M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOf_map_mul M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_mul) hf
#align monoid_hom_of_mem_closure_range_coe monoidHomOfMemClosureRangeCoe
#align add_monoid_hom_of_mem_closure_range_coe addMonoidHomOfMemClosureRangeCoe

/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive
      "Construct a bundled additive monoid homomorphism from a pointwise limit of additive\nmonoid homomorphisms",
  simps (config := { fullyApplied := false })]
def monoidHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.ne_bot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →* M₂ :=
  monoidHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| eventually_of_forall fun a => mem_range_self _
#align monoid_hom_of_tendsto monoidHomOfTendsto
#align add_monoid_hom_of_tendsto addMonoidHomOfTendsto

variable (M₁ M₂)

@[to_additive]
theorem MonoidHom.isClosed_range_coe : IsClosed (range (coeFn : (M₁ →* M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩
#align monoid_hom.is_closed_range_coe MonoidHom.isClosed_range_coe
#align add_monoid_hom.is_closed_range_coe AddMonoidHom.isClosed_range_coe

end PointwiseLimits

@[to_additive]
theorem Inducing.hasContinuousMul {M N F : Type _} [Mul M] [Mul N] [MulHomClass F M N]
    [TopologicalSpace M] [TopologicalSpace N] [HasContinuousMul N] (f : F) (hf : Inducing f) :
    HasContinuousMul M :=
  ⟨hf.continuous_iff.2 <| by
      simpa only [(· ∘ ·), map_mul f] using hf.continuous.fst'.mul hf.continuous.snd'⟩
#align inducing.has_continuous_mul Inducing.hasContinuousMul
#align inducing.has_continuous_add Inducing.has_continuous_add

@[to_additive]
theorem hasContinuousMul_induced {M N F : Type _} [Mul M] [Mul N] [MulHomClass F M N]
    [TopologicalSpace N] [HasContinuousMul N] (f : F) : @HasContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  Inducing.hasContinuousMul f ⟨rfl⟩
#align has_continuous_mul_induced hasContinuousMul_induced
#align has_continuous_add_induced has_continuous_add_induced

@[to_additive]
instance Subsemigroup.hasContinuousMul [TopologicalSpace M] [Semigroup M] [HasContinuousMul M]
    (S : Subsemigroup M) : HasContinuousMul S :=
  Inducing.hasContinuousMul (⟨coe, fun _ _ => rfl⟩ : MulHom S M) ⟨rfl⟩
#align subsemigroup.has_continuous_mul Subsemigroup.hasContinuousMul
#align add_subsemigroup.has_continuous_add AddSubsemigroup.has_continuous_add

@[to_additive]
instance Submonoid.hasContinuousMul [TopologicalSpace M] [Monoid M] [HasContinuousMul M]
    (S : Submonoid M) : HasContinuousMul S :=
  S.toSubsemigroup.HasContinuousMul
#align submonoid.has_continuous_mul Submonoid.hasContinuousMul
#align add_submonoid.has_continuous_add AddSubmonoid.has_continuous_add

section HasContinuousMul

variable [TopologicalSpace M] [Monoid M] [HasContinuousMul M]

@[to_additive]
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
    closure (s : Set M) * closure s ⊆ closure s :=
  image2_subset_iff.2 fun x hx y hy =>
    map_mem_closure₂ continuous_mul hx hy fun a ha b hb => s.mul_mem ha hb
#align submonoid.top_closure_mul_self_subset Submonoid.top_closure_mul_self_subset
#align add_submonoid.top_closure_add_self_subset AddSubmonoid.top_closure_add_self_subset

@[to_additive]
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
    closure (s : Set M) * closure s = closure s :=
  Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, 1, hx, subset_closure s.one_mem, mul_one _⟩
#align submonoid.top_closure_mul_self_eq Submonoid.top_closure_mul_self_eq
#align add_submonoid.top_closure_add_self_eq AddSubmonoid.top_closure_add_self_eq

/-- The (topological-space) closure of a submonoid of a space `M` with `has_continuous_mul` is
itself a submonoid. -/
@[to_additive
      "The (topological-space) closure of an additive submonoid of a space `M` with\n`has_continuous_add` is itself an additive submonoid."]
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M
    where
  carrier := closure (s : Set M)
  one_mem' := subset_closure s.one_mem
  mul_mem' a b ha hb := s.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩
#align submonoid.topological_closure Submonoid.topologicalClosure
#align add_submonoid.topological_closure AddSubmonoid.topologicalClosure

@[to_additive]
theorem Submonoid.le_topologicalClosure (s : Submonoid M) : s ≤ s.topologicalClosure :=
  subset_closure
#align submonoid.le_topological_closure Submonoid.le_topologicalClosure
#align add_submonoid.le_topological_closure AddSubmonoid.le_topologicalClosure

@[to_additive]
theorem Submonoid.isClosed_topologicalClosure (s : Submonoid M) :
    IsClosed (s.topologicalClosure : Set M) := by convert isClosed_closure
#align submonoid.is_closed_topological_closure Submonoid.isClosed_topologicalClosure
#align add_submonoid.is_closed_topological_closure AddSubmonoid.isClosed_topologicalClosure

@[to_additive]
theorem Submonoid.topologicalClosure_minimal (s : Submonoid M) {t : Submonoid M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht
#align submonoid.topological_closure_minimal Submonoid.topologicalClosure_minimal
#align add_submonoid.topological_closure_minimal AddSubmonoid.topologicalClosure_minimal

/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive
      "If a submonoid of an additive topological monoid is commutative, then so is its\ntopological closure."]
def Submonoid.commMonoidTopologicalClosure [T2Space M] (s : Submonoid M)
    (hs : ∀ x y : s, x * y = y * x) : CommMonoid s.topologicalClosure :=
  { s.topologicalClosure.toMonoid with
    mul_comm :=
      have : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := fun x hx y hy =>
        congr_arg Subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩)
      fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      Subtype.ext <|
        eqOn_closure₂ this continuous_mul (continuous_snd.mul continuous_fst) x hx y hy }
#align submonoid.comm_monoid_topological_closure Submonoid.commMonoidTopologicalClosure
#align add_submonoid.add_comm_monoid_topological_closure AddSubmonoid.addCommMonoidTopologicalClosure

@[to_additive exists_open_nhds_zero_half]
theorem exists_open_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s :=
  by
  have : (fun a : M × M => a.1 * a.2) ⁻¹' s ∈ 𝓝 ((1, 1) : M × M) :=
    tendsto_mul (by simpa only [one_mul] using hs)
  simpa only [prod_subset_iff] using exists_nhds_square this
#align exists_open_nhds_one_split exists_open_nhds_one_split
#align exists_open_nhds_zero_half exists_open_nhds_zero_half

@[to_additive exists_nhds_zero_half]
theorem exists_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s :=
  let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
  ⟨V, IsOpen.mem_nhds Vo V1, hV⟩
#align exists_nhds_one_split exists_nhds_one_split
#align exists_nhds_zero_half exists_nhds_zero_half

@[to_additive exists_nhds_zero_quarter]
theorem exists_nhds_one_split4 {u : Set M} (hu : u ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
  by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)
#align exists_nhds_one_split4 exists_nhds_one_split4
#align exists_nhds_zero_quarter exists_nhds_zero_quarter

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
@[to_additive
      "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`\n  such that `V + V ⊆ U`."]
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ V * V ⊆ U :=
  by
  rcases exists_open_nhds_one_split hU with ⟨V, Vo, V1, hV⟩
  use V, Vo, V1
  rintro _ ⟨x, y, hx, hy, rfl⟩
  exact hV _ hx _ hy
#align exists_open_nhds_one_mul_subset exists_open_nhds_one_mul_subset
#align exists_open_nhds_zero_add_subset exists_open_nhds_zero_add_subset

@[to_additive]
theorem IsCompact.mul {s t : Set M} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t) :=
  by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul
#align is_compact.mul IsCompact.mul
#align is_compact.add IsCompact.add

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem tendsto_list_prod {f : ι → α → M} {x : Filter α} {a : ι → M} :
    ∀ l : List ι,
      (∀ i ∈ l, Tendsto (f i) x (𝓝 (a i))) →
        Tendsto (fun b => (l.map fun c => f c b).Prod) x (𝓝 (l.map a).Prod)
  | [], _ => by simp [tendsto_const_nhds]
  | f::l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact
      (h f (List.mem_cons_self _ _)).mul
        (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_mem _ hc))
#align tendsto_list_prod tendsto_list_prod
#align tendsto_list_sum tendsto_list_sum

@[to_additive]
theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀ i ∈ l, Continuous (f i)) :
    Continuous fun a => (l.map fun i => f i a).Prod :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x
#align continuous_list_prod continuous_list_prod
#align continuous_list_sum continuous_list_sum

@[to_additive]
theorem continuousOn_list_prod {f : ι → X → M} (l : List ι) {t : Set X}
    (h : ∀ i ∈ l, ContinuousOn (f i) t) : ContinuousOn (fun a => (l.map fun i => f i a).Prod) t :=
  by
  intro x hx
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx]
  refine' tendsto_list_prod _ fun i hi => _
  specialize h i hi x hx
  rw [continuousWithinAt_iff_continuousAt_restrict _ hx] at h
  exact h
#align continuous_on_list_prod continuousOn_list_prod
#align continuous_on_list_sum continuousOn_list_sum

@[continuity, to_additive]
theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n
  | 0 => by simpa using continuous_const
  | k + 1 => by
    simp only [pow_succ]
    exact continuous_id.mul (continuous_pow _)
#align continuous_pow continuous_pow
#align continuous_nsmul continuous_nsmul

instance AddMonoid.continuousConstSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [HasContinuousAdd A] : ContinuousConstSMul ℕ A :=
  ⟨continuous_nsmul⟩
#align add_monoid.has_continuous_const_smul_nat AddMonoid.continuousConstSMul_nat

instance AddMonoid.hasContinuousSmul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [HasContinuousAdd A] : HasContinuousSmul ℕ A :=
  ⟨continuous_uncurry_of_discreteTopology continuous_nsmul⟩
#align add_monoid.has_continuous_smul_nat AddMonoid.hasContinuousSmul_nat

@[continuity, to_additive Continuous.nsmul]
theorem Continuous.pow {f : X → M} (h : Continuous f) (n : ℕ) : Continuous fun b => f b ^ n :=
  (continuous_pow n).comp h
#align continuous.pow Continuous.pow
#align continuous.nsmul Continuous.nsmul

@[to_additive]
theorem continuousOn_pow {s : Set M} (n : ℕ) : ContinuousOn (fun x => x ^ n) s :=
  (continuous_pow n).ContinuousOn
#align continuous_on_pow continuousOn_pow
#align continuous_on_nsmul continuousOn_nsmul

@[to_additive]
theorem continuousAt_pow (x : M) (n : ℕ) : ContinuousAt (fun x => x ^ n) x :=
  (continuous_pow n).ContinuousAt
#align continuous_at_pow continuousAt_pow
#align continuous_at_nsmul continuousAt_nsmul

@[to_additive Filter.Tendsto.nsmul]
theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : ℕ) :
    Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuousAt_pow _ _).Tendsto.comp hf
#align filter.tendsto.pow Filter.Tendsto.pow
#align filter.tendsto.nsmul Filter.Tendsto.nsmul

@[to_additive ContinuousWithinAt.nsmul]
theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
    (n : ℕ) : ContinuousWithinAt (fun x => f x ^ n) s x :=
  hf.pow n
#align continuous_within_at.pow ContinuousWithinAt.pow
#align continuous_within_at.nsmul ContinuousWithinAt.nsmul

@[to_additive ContinuousAt.nsmul]
theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) :
    ContinuousAt (fun x => f x ^ n) x :=
  hf.pow n
#align continuous_at.pow ContinuousAt.pow
#align continuous_at.nsmul ContinuousAt.nsmul

@[to_additive ContinuousOn.nsmul]
theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun x => f x ^ n) s := fun x hx => (hf x hx).pow n
#align continuous_on.pow ContinuousOn.pow
#align continuous_on.nsmul ContinuousOn.nsmul

/-- Left-multiplication by a left-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) :
    Filter.Tendsto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M) :=
  by
  refine' Filter.Tendsto.of_tendsto_comp _ (Filter.comap_cocompact_le (continuous_mul_left b))
  convert Filter.tendsto_id
  ext x
  simp [ha]
#align filter.tendsto_cocompact_mul_left Filter.tendsto_cocompact_mul_left

/-- Right-multiplication by a right-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) :
    Filter.Tendsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M) :=
  by
  refine' Filter.Tendsto.of_tendsto_comp _ (Filter.comap_cocompact_le (continuous_mul_right b))
  convert Filter.tendsto_id
  ext x
  simp [ha]
#align filter.tendsto_cocompact_mul_right Filter.tendsto_cocompact_mul_right

/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instances applies when `R = A`, or when `[algebra R A]` is available. -/
@[to_additive
      "If `R` acts on `A` via `A`, then continuous addition implies\ncontinuous affine addition by constants."]
instance (priority := 100) IsScalarTower.continuousConstSMul {R A : Type _} [Monoid A] [SMul R A]
    [IsScalarTower R A A] [TopologicalSpace A] [HasContinuousMul A] : ContinuousConstSMul R A
    where continuous_const_smul q :=
    by
    simp (config := { singlePass := true }) only [← smul_one_mul q (_ : A)]
    exact continuous_const.mul continuous_id
#align is_scalar_tower.has_continuous_const_smul IsScalarTower.continuousConstSMul
#align vadd_assoc_class.has_continuous_const_vadd VAddAssocClass.has_continuous_const_vadd

/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instances applies when `R = Aᵐᵒᵖ` -/
@[to_additive
      "If the action of `R` on `A` commutes with left-addition, then\ncontinuous addition implies continuous affine addition by constants.\n\nNotably, this instances applies when `R = Aᵃᵒᵖ`. "]
instance (priority := 100) SMulCommClass.continuousConstSMul {R A : Type _} [Monoid A] [SMul R A]
    [SMulCommClass R A A] [TopologicalSpace A] [HasContinuousMul A] : ContinuousConstSMul R A
    where continuous_const_smul q :=
    by
    simp (config := { singlePass := true }) only [← mul_smul_one q (_ : A)]
    exact continuous_id.mul continuous_const
#align smul_comm_class.has_continuous_const_smul SMulCommClass.continuousConstSMul
#align vadd_comm_class.has_continuous_const_vadd VAddCommClass.has_continuous_const_vadd

end HasContinuousMul

namespace MulOpposite

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [TopologicalSpace α] [Mul α] [HasContinuousMul α] : HasContinuousMul αᵐᵒᵖ :=
  ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoid α] [HasContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `topology.algebra.group`,
because the predicate `has_continuous_inv` has not yet been defined. -/
@[to_additive
      "If addition on an additive monoid is continuous, then addition on the additive units\nof the monoid, with respect to the induced topology, is continuous.\n\nNegation is also continuous, but we register this in a later file, `topology.algebra.group`, because\nthe predicate `has_continuous_neg` has not yet been defined."]
instance : HasContinuousMul αˣ :=
  inducing_embedProduct.HasContinuousMul (embedProduct α)

end Units

@[to_additive]
theorem Continuous.units_map [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →* N) (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩
#align continuous.units_map Continuous.units_map
#align continuous.add_units_map Continuous.add_units_map

section

variable [TopologicalSpace M] [CommMonoid M]

@[to_additive]
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) :
    (S : Set M) ∈ 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem
#align submonoid.mem_nhds_one Submonoid.mem_nhds_one
#align add_submonoid.mem_nhds_zero AddSubmonoid.mem_nhds_zero

variable [HasContinuousMul M]

@[to_additive]
theorem tendsto_multiset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Multiset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => (s.map fun c => f c b).Prod) x (𝓝 (s.map a).Prod) :=
  by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l
#align tendsto_multiset_prod tendsto_multiset_prod
#align tendsto_multiset_sum tendsto_multiset_sum

@[to_additive]
theorem tendsto_finset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
  tendsto_multiset_prod _
#align tendsto_finset_prod tendsto_finset_prod
#align tendsto_finset_sum tendsto_finset_sum

@[continuity, to_additive]
theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => (s.map fun i => f i a).Prod :=
  by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l
#align continuous_multiset_prod continuous_multiset_prod
#align continuous_multiset_sum continuous_multiset_sum

@[to_additive]
theorem continuousOn_multiset_prod {f : ι → X → M} (s : Multiset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => (s.map fun i => f i a).Prod) t :=
  by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l
#align continuous_on_multiset_prod continuousOn_multiset_prod
#align continuous_on_multiset_sum continuousOn_multiset_sum

@[continuity, to_additive]
theorem continuous_finset_prod {f : ι → X → M} (s : Finset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => ∏ i in s, f i a :=
  continuous_multiset_prod _
#align continuous_finset_prod continuous_finset_prod
#align continuous_finset_sum continuous_finset_sum

@[to_additive]
theorem continuousOn_finset_prod {f : ι → X → M} (s : Finset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => ∏ i in s, f i a) t :=
  continuousOn_multiset_prod _
#align continuous_on_finset_prod continuousOn_finset_prod
#align continuous_on_finset_sum continuousOn_finset_sum

@[to_additive]
theorem eventuallyEq_prod {X M : Type _} [CommMonoid M] {s : Finset ι} {l : Filter X}
    {f g : ι → X → M} (hs : ∀ i ∈ s, f i =ᶠ[l] g i) : (∏ i in s, f i) =ᶠ[l] ∏ i in s, g i :=
  by
  replace hs : ∀ᶠ x in l, ∀ i ∈ s, f i x = g i x
  · rwa [eventually_all_finset]
  filter_upwards [hs]with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]
#align eventually_eq_prod eventuallyEq_prod
#align eventually_eq_sum eventuallyEq_sum

open Function

@[to_additive]
theorem LocallyFinite.exists_finset_mulSupport {M : Type _} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport <| f i) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, (mulSupport fun i => f i x) ⊆ I :=
  by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine' ⟨hUf.to_finset, mem_of_superset hxU fun y hy i hi => _⟩
  rw [hUf.coe_to_finset]
  exact ⟨y, hi, hy⟩
#align locally_finite.exists_finset_mul_support LocallyFinite.exists_finset_mulSupport
#align locally_finite.exists_finset_support LocallyFinite.exists_finset_support

@[to_additive]
theorem finprod_eventually_eq_prod {M : Type _} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport (f i)) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, (∏ᶠ i, f i y) = ∏ i in s, f i y :=
  let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun y hy => finprod_eq_prod_of_mulSupport_subset _ fun i hi => hy hi⟩
#align finprod_eventually_eq_prod finprod_eventually_eq_prod
#align finsum_eventually_eq_sum finsum_eventually_eq_sum

@[to_additive]
theorem continuous_finprod {f : ι → X → M} (hc : ∀ i, Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ i, f i x :=
  by
  refine' continuous_iff_continuousAt.2 fun x => _
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine' ContinuousAt.congr _ (eventually_eq.symm hs)
  exact tendsto_finset_prod _ fun i hi => (hc i).ContinuousAt
#align continuous_finprod continuous_finprod
#align continuous_finsum continuous_finsum

@[to_additive]
theorem continuous_finprod_cond {f : ι → X → M} {p : ι → Prop} (hc : ∀ i, p i → Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ (i) (hi : p i), f i x :=
  by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)
#align continuous_finprod_cond continuous_finprod_cond
#align continuous_finsum_cond continuous_finsum_cond

end

instance [TopologicalSpace M] [Mul M] [HasContinuousMul M] : HasContinuousAdd (Additive M)
    where continuous_add := @continuous_mul M _ _ _

instance [TopologicalSpace M] [Add M] [HasContinuousAdd M] : HasContinuousMul (Multiplicative M)
    where continuous_mul := @continuous_add M _ _ _

section LatticeOps

variable {ι' : Sort _} [Mul M]

@[to_additive]
theorem hasContinuousMul_infₛ {ts : Set (TopologicalSpace M)}
    (h : ∀ t ∈ ts, @HasContinuousMul M t _) : @HasContinuousMul M (infₛ ts) _ :=
  {
    continuous_mul :=
      continuous_infₛ_rng.2 fun t ht =>
        continuous_infₛ_dom₂ ht ht (@HasContinuousMul.continuous_mul M t _ (h t ht)) }
#align has_continuous_mul_Inf hasContinuousMul_infₛ
#align has_continuous_add_Inf has_continuous_add_infₛ

@[to_additive]
theorem hasContinuousMul_infᵢ {ts : ι' → TopologicalSpace M}
    (h' : ∀ i, @HasContinuousMul M (ts i) _) : @HasContinuousMul M (⨅ i, ts i) _ :=
  by
  rw [← infₛ_range]
  exact hasContinuousMul_infₛ (set.forall_range_iff.mpr h')
#align has_continuous_mul_infi hasContinuousMul_infᵢ
#align has_continuous_add_infi has_continuous_add_infᵢ

@[to_additive]
theorem hasContinuousMul_inf {t₁ t₂ : TopologicalSpace M} (h₁ : @HasContinuousMul M t₁ _)
    (h₂ : @HasContinuousMul M t₂ _) : @HasContinuousMul M (t₁ ⊓ t₂) _ :=
  by
  rw [inf_eq_infᵢ]
  refine' hasContinuousMul_infᵢ fun b => _
  cases b <;> assumption
#align has_continuous_mul_inf hasContinuousMul_inf
#align has_continuous_add_inf has_continuous_add_inf

end LatticeOps

