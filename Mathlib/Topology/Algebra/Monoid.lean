/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.Filter.Pointwise
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Algebra.Group.ULift

#align_import topology.algebra.monoid from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Theory of topological monoids

In this file we define mixin classes `ContinuousMul` and `ContinuousAdd`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/


universe u v

open scoped Classical
open Set Filter TopologicalSpace

open scoped Classical
open Topology Pointwise

variable {ι α M N X : Type*} [TopologicalSpace X]

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_one [TopologicalSpace M] [One M] : Continuous (1 : X → M) :=
  @continuous_const _ _ _ _ 1
#align continuous_one continuous_one
#align continuous_zero continuous_zero

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `AddMonoid M` and `ContinuousAdd M`.

Continuity in only the left/right argument can be stated using
`ContinuousConstVAdd α α`/`ContinuousConstVAdd αᵐᵒᵖ α`. -/
class ContinuousAdd (M : Type u) [TopologicalSpace M] [Add M] : Prop where
  continuous_add : Continuous fun p : M × M => p.1 + p.2
#align has_continuous_add ContinuousAdd

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `Monoid M`
and `ContinuousMul M`.

Continuity in only the left/right argument can be stated using
`ContinuousConstSMul α α`/`ContinuousConstSMul αᵐᵒᵖ α`. -/
@[to_additive]
class ContinuousMul (M : Type u) [TopologicalSpace M] [Mul M] : Prop where
  continuous_mul : Continuous fun p : M × M => p.1 * p.2
#align has_continuous_mul ContinuousMul

section ContinuousMul

variable [TopologicalSpace M] [Mul M] [ContinuousMul M]

@[to_additive]
instance : ContinuousMul Mᵒᵈ :=
  ‹ContinuousMul M›

@[to_additive (attr := continuity)]
theorem continuous_mul : Continuous fun p : M × M => p.1 * p.2 :=
  ContinuousMul.continuous_mul
#align continuous_mul continuous_mul
#align continuous_add continuous_add

@[to_additive]
instance : ContinuousMul (ULift.{u} M) := by
  constructor
  apply continuous_uLift_up.comp
  exact continuous_mul.comp₂ (continuous_uLift_down.comp continuous_fst)
    (continuous_uLift_down.comp continuous_snd)

@[to_additive]
instance ContinuousMul.to_continuousSMul : ContinuousSMul M M :=
  ⟨continuous_mul⟩
#align has_continuous_mul.to_has_continuous_smul ContinuousMul.to_continuousSMul
#align has_continuous_add.to_has_continuous_vadd ContinuousAdd.to_continuousVAdd

@[to_additive]
instance ContinuousMul.to_continuousSMul_op : ContinuousSMul Mᵐᵒᵖ M :=
  ⟨show Continuous ((fun p : M × M => p.1 * p.2) ∘ Prod.swap ∘ Prod.map MulOpposite.unop id) from
      continuous_mul.comp <|
        continuous_swap.comp <| Continuous.prod_map MulOpposite.continuous_unop continuous_id⟩
#align has_continuous_mul.to_has_continuous_smul_op ContinuousMul.to_continuousSMul_op
#align has_continuous_add.to_has_continuous_vadd_op ContinuousAdd.to_continuousVAdd_op

@[to_additive (attr := continuity, fun_prop)]
theorem Continuous.mul {f g : X → M} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => f x * g x :=
  continuous_mul.comp (hf.prod_mk hg : _)
#align continuous.mul Continuous.mul
#align continuous.add Continuous.add

@[to_additive (attr := continuity)]
theorem continuous_mul_left (a : M) : Continuous fun b : M => a * b :=
  continuous_const.mul continuous_id
#align continuous_mul_left continuous_mul_left
#align continuous_add_left continuous_add_left

@[to_additive (attr := continuity)]
theorem continuous_mul_right (a : M) : Continuous fun b : M => b * a :=
  continuous_id.mul continuous_const
#align continuous_mul_right continuous_mul_right
#align continuous_add_right continuous_add_right

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.mul {f g : X → M} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x * g x) s :=
  (continuous_mul.comp_continuousOn (hf.prod hg) : _)
#align continuous_on.mul ContinuousOn.mul
#align continuous_on.add ContinuousOn.add

@[to_additive]
theorem tendsto_mul {a b : M} : Tendsto (fun p : M × M => p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
  continuous_iff_continuousAt.mp ContinuousMul.continuous_mul (a, b)
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
theorem le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b ≤ 𝓝 (a * b) := by
  rw [← map₂_mul, ← map_uncurry_prod, ← nhds_prod_eq]
  exact continuous_mul.tendsto _
#align le_nhds_mul le_nhds_mul
#align le_nhds_add le_nhds_add

@[to_additive (attr := simp)]
theorem nhds_one_mul_nhds {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (one_mul a)).antisymm <|
    le_mul_of_one_le_left' <| pure_le_nhds 1
#align nhds_one_mul_nhds nhds_one_mul_nhds
#align nhds_zero_add_nhds nhds_zero_add_nhds

@[to_additive (attr := simp)]
theorem nhds_mul_nhds_one {M} [MulOneClass M] [TopologicalSpace M] [ContinuousMul M] (a : M) :
    𝓝 a * 𝓝 1 = 𝓝 a :=
  ((le_nhds_mul _ _).trans_eq <| congr_arg _ (mul_one a)).antisymm <|
    le_mul_of_one_le_right' <| pure_le_nhds 1
#align nhds_mul_nhds_one nhds_mul_nhds_one
#align nhds_add_nhds_zero nhds_add_nhds_zero

section tendsto_nhds

variable {𝕜 : Type*} [Preorder 𝕜] [Zero 𝕜] [Mul 𝕜] [TopologicalSpace 𝕜] [ContinuousMul 𝕜]
  {l : Filter α} {f : α → 𝕜} {b c : 𝕜} (hb : 0 < b)

theorem Filter.TendstoNhdsWithinIoi.const_mul [PosMulStrictMono 𝕜] [PosMulReflectLT 𝕜]
    (h : Tendsto f l (𝓝[>] c)) : Tendsto (fun a => b * f a) l (𝓝[>] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ => (mul_lt_mul_left hb).mpr
#align filter.tendsto_nhds_within_Ioi.const_mul Filter.TendstoNhdsWithinIoi.const_mul

theorem Filter.TendstoNhdsWithinIio.const_mul [PosMulStrictMono 𝕜] [PosMulReflectLT 𝕜]
    (h : Tendsto f l (𝓝[<] c)) : Tendsto (fun a => b * f a) l (𝓝[<] (b * c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).const_mul b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ => (mul_lt_mul_left hb).mpr
#align filter.tendsto_nhds_within_Iio.const_mul Filter.TendstoNhdsWithinIio.const_mul

theorem Filter.TendstoNhdsWithinIoi.mul_const [MulPosStrictMono 𝕜] [MulPosReflectLT 𝕜]
    (h : Tendsto f l (𝓝[>] c)) : Tendsto (fun a => f a * b) l (𝓝[>] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ => (mul_lt_mul_right hb).mpr
#align filter.tendsto_nhds_within_Ioi.mul_const Filter.TendstoNhdsWithinIoi.mul_const

theorem Filter.TendstoNhdsWithinIio.mul_const [MulPosStrictMono 𝕜] [MulPosReflectLT 𝕜]
    (h : Tendsto f l (𝓝[<] c)) : Tendsto (fun a => f a * b) l (𝓝[<] (c * b)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_nhds_of_tendsto_nhdsWithin h).mul_const b) <|
    (tendsto_nhdsWithin_iff.mp h).2.mono fun _ => (mul_lt_mul_right hb).mpr
#align filter.tendsto_nhds_within_Iio.mul_const Filter.TendstoNhdsWithinIio.mul_const

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
  "Construct an additive unit from limits of additive units and their negatives."]
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
#align filter.tendsto.units Filter.Tendsto.units
#align filter.tendsto.add_units Filter.Tendsto.addUnits

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.mul {f g : X → M} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => f x * g x) x :=
  Filter.Tendsto.mul hf hg
#align continuous_at.mul ContinuousAt.mul
#align continuous_at.add ContinuousAt.add

@[to_additive]
theorem ContinuousWithinAt.mul {f g : X → M} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x)
    (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (fun x => f x * g x) s x :=
  Filter.Tendsto.mul hf hg
#align continuous_within_at.mul ContinuousWithinAt.mul
#align continuous_within_at.add ContinuousWithinAt.add

@[to_additive]
instance Prod.continuousMul [TopologicalSpace N] [Mul N] [ContinuousMul N] :
    ContinuousMul (M × N) :=
  ⟨(continuous_fst.fst'.mul continuous_fst.snd').prod_mk
      (continuous_snd.fst'.mul continuous_snd.snd')⟩

@[to_additive]
instance Pi.continuousMul {C : ι → Type*} [∀ i, TopologicalSpace (C i)] [∀ i, Mul (C i)]
    [∀ i, ContinuousMul (C i)] : ContinuousMul (∀ i, C i) where
  continuous_mul :=
    continuous_pi fun i => (continuous_apply i).fst'.mul (continuous_apply i).snd'
#align pi.has_continuous_mul Pi.continuousMul
#align pi.has_continuous_add Pi.continuousAdd

/-- A version of `Pi.continuousMul` for non-dependent functions. It is needed because sometimes
Lean 3 fails to use `Pi.continuousMul` for non-dependent functions. -/
@[to_additive "A version of `Pi.continuousAdd` for non-dependent functions. It is needed
because sometimes Lean fails to use `Pi.continuousAdd` for non-dependent functions."]
instance Pi.continuousMul' : ContinuousMul (ι → M) :=
  Pi.continuousMul
#align pi.has_continuous_mul' Pi.continuousMul'
#align pi.has_continuous_add' Pi.continuousAdd'

@[to_additive]
instance (priority := 100) continuousMul_of_discreteTopology [TopologicalSpace N] [Mul N]
    [DiscreteTopology N] : ContinuousMul N :=
  ⟨continuous_of_discreteTopology⟩
#align has_continuous_mul_of_discrete_topology continuousMul_of_discreteTopology
#align has_continuous_add_of_discrete_topology continuousAdd_of_discreteTopology

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
        -- Porting note: `rw` was able to prove this
        -- Now it fails with `failed to rewrite using equation theorems for 'Function.uncurry'`
        -- and `failed to rewrite using equation theorems for 'Function.comp'`.
        -- Removing those two lemmas, the `rw` would succeed, but then needs a `rfl`.
        simp (config := { unfoldPartialApp := true }) only [uncurry]
        simp_rw [hleft x₀, hright y₀, prod_map_map_eq, Filter.map_map, Function.comp_def]
      _ = map ((fun x => x₀ * x) ∘ fun x => x * y₀) (map (uncurry (· * ·)) (𝓝 1 ×ˢ 𝓝 1)) := by
        rw [key, ← Filter.map_map]
      _ ≤ map ((fun x : M => x₀ * x) ∘ fun x => x * y₀) (𝓝 1) := map_mono hmul
      _ = 𝓝 (x₀ * y₀) := by
        rw [← Filter.map_map, ← hright, hleft y₀, Filter.map_map, key₂, ← hleft]⟩
#align has_continuous_mul.of_nhds_one ContinuousMul.of_nhds_one
#align has_continuous_add.of_nhds_zero ContinuousAdd.of_nhds_zero

@[to_additive]
theorem continuousMul_of_comm_of_nhds_one (M : Type u) [CommMonoid M] [TopologicalSpace M]
    (hmul : Tendsto (uncurry ((· * ·) : M → M → M)) (𝓝 1 ×ˢ 𝓝 1) (𝓝 1))
    (hleft : ∀ x₀ : M, 𝓝 x₀ = map (fun x => x₀ * x) (𝓝 1)) : ContinuousMul M := by
  apply ContinuousMul.of_nhds_one hmul hleft
  intro x₀
  simp_rw [mul_comm, hleft x₀]
#align has_continuous_mul_of_comm_of_nhds_one continuousMul_of_comm_of_nhds_one
#align has_continuous_add_of_comm_of_nhds_zero continuousAdd_of_comm_of_nhds_zero

end ContinuousMul

section PointwiseLimits

variable (M₁ M₂ : Type*) [TopologicalSpace M₂] [T2Space M₂]

@[to_additive]
theorem isClosed_setOf_map_one [One M₁] [One M₂] : IsClosed { f : M₁ → M₂ | f 1 = 1 } :=
  isClosed_eq (continuous_apply 1) continuous_const
#align is_closed_set_of_map_one isClosed_setOf_map_one
#align is_closed_set_of_map_zero isClosed_setOf_map_zero

@[to_additive]
theorem isClosed_setOf_map_mul [Mul M₁] [Mul M₂] [ContinuousMul M₂] :
    IsClosed { f : M₁ → M₂ | ∀ x y, f (x * y) = f x * f y } := by
  simp only [setOf_forall]
  exact
    isClosed_iInter fun x =>
      isClosed_iInter fun y =>
        isClosed_eq (continuous_apply _)
          -- Porting note: proof was:
          -- `((continuous_apply _).mul (continuous_apply _))`
          (by continuity)
#align is_closed_set_of_map_mul isClosed_setOf_map_mul
#align is_closed_set_of_map_add isClosed_setOf_map_add

-- Porting note: split variables command over two lines, can't change explicitness at the same time
-- as declaring new variables.
variable {M₁ M₂}
variable [MulOneClass M₁] [MulOneClass M₂] [ContinuousMul M₂]
  {F : Type*} [FunLike F M₁ M₂] [MonoidHomClass F M₁ M₂] {l : Filter α}

/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `MonoidHomClass` instance) to `M₁ → M₂`. -/
@[to_additive (attr := simps (config := .asFn))
  "Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another
type of bundled homomorphisms that has an `AddMonoidHomClass` instance) to `M₁ → M₂`."]
def monoidHomOfMemClosureRangeCoe (f : M₁ → M₂)
    (hf : f ∈ closure (range fun (f : F) (x : M₁) => f x)) : M₁ →* M₂ where
  toFun := f
  map_one' := (isClosed_setOf_map_one M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_one) hf
  map_mul' := (isClosed_setOf_map_mul M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_mul) hf
#align monoid_hom_of_mem_closure_range_coe monoidHomOfMemClosureRangeCoe
#align add_monoid_hom_of_mem_closure_range_coe addMonoidHomOfMemClosureRangeCoe

/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive (attr := simps! (config := .asFn))
  "Construct a bundled additive monoid homomorphism from a pointwise limit of additive
monoid homomorphisms"]
def monoidHomOfTendsto (f : M₁ → M₂) (g : α → F) [l.NeBot]
    (h : Tendsto (fun a x => g a x) l (𝓝 f)) : M₁ →* M₂ :=
  monoidHomOfMemClosureRangeCoe f <|
    mem_closure_of_tendsto h <| eventually_of_forall fun _ => mem_range_self _
#align monoid_hom_of_tendsto monoidHomOfTendsto
#align add_monoid_hom_of_tendsto addMonoidHomOfTendsto

variable (M₁ M₂)

@[to_additive]
theorem MonoidHom.isClosed_range_coe : IsClosed (Set.range ((↑) : (M₁ →* M₂) → M₁ → M₂)) :=
  isClosed_of_closure_subset fun f hf => ⟨monoidHomOfMemClosureRangeCoe f hf, rfl⟩
#align monoid_hom.is_closed_range_coe MonoidHom.isClosed_range_coe
#align add_monoid_hom.is_closed_range_coe AddMonoidHom.isClosed_range_coe

end PointwiseLimits

@[to_additive]
theorem Inducing.continuousMul {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    [TopologicalSpace M] [TopologicalSpace N] [ContinuousMul N] (f : F) (hf : Inducing f) :
    ContinuousMul M :=
  ⟨(hf.continuousSMul hf.continuous (map_mul f _ _)).1⟩
#align inducing.has_continuous_mul Inducing.continuousMul
#align inducing.has_continuous_add Inducing.continuousAdd

@[to_additive]
theorem continuousMul_induced {M N F : Type*} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    [TopologicalSpace N] [ContinuousMul N] (f : F) : @ContinuousMul M (induced f ‹_›) _ :=
  letI := induced f ‹_›
  Inducing.continuousMul f ⟨rfl⟩
#align has_continuous_mul_induced continuousMul_induced
#align has_continuous_add_induced continuousAdd_induced

@[to_additive]
instance Subsemigroup.continuousMul [TopologicalSpace M] [Semigroup M] [ContinuousMul M]
    (S : Subsemigroup M) : ContinuousMul S :=
  Inducing.continuousMul ({ toFun := (↑), map_mul' := fun _ _ => rfl} : MulHom S M) ⟨rfl⟩
#align subsemigroup.has_continuous_mul Subsemigroup.continuousMul
#align add_subsemigroup.has_continuous_add AddSubsemigroup.continuousAdd

@[to_additive]
instance Submonoid.continuousMul [TopologicalSpace M] [Monoid M] [ContinuousMul M]
    (S : Submonoid M) : ContinuousMul S :=
  S.toSubsemigroup.continuousMul
#align submonoid.has_continuous_mul Submonoid.continuousMul
#align add_submonoid.has_continuous_add AddSubmonoid.continuousAdd

section MulZeroClass

open Filter

variable {α β : Type*}
variable [TopologicalSpace M] [MulZeroClass M] [ContinuousMul M]
variable {f : α → M} {g : β → M}

/-- If `f : α → M` and `g : β → M` are continuous and both tend to zero on the cocompact filter,
then `fun (i : α × β) ↦ (f i.1) * (g i.2)` also tends to zero on the cocompact filter. -/
theorem tendsto_mul_cocompact_nhds_zero [TopologicalSpace α] [TopologicalSpace β]
    (f_cont : Continuous f) (g_cont : Continuous g)
    (hf : Tendsto f (cocompact α) (𝓝 0)) (hg : Tendsto g (cocompact β) (𝓝 0)) :
    Tendsto (fun (i : α × β) ↦ (f i.1) * (g i.2)) (cocompact (α × β)) (𝓝 0) := by
  -- We use the notation `⊤` for `Set.univ` in this proof.
  have h'f : Disjoint (map f ⊤) (cocompact M) := by
    apply (disjoint_cocompact_right _).mpr
    use insert 0 (range f), by simp, Tendsto.isCompact_insert_range_of_cocompact hf f_cont
  have h'g : Disjoint (map g ⊤) (cocompact M) := by
    apply (disjoint_cocompact_right _).mpr
    use insert 0 (range g), by simp, Tendsto.isCompact_insert_range_of_cocompact hg g_cont
  have h₁ : Tendsto (Prod.map f g) ((cocompact α) ×ˢ ⊤) (𝓝ˢ ({0} ×ˢ ⊤)) := calc
    map (Prod.map f g) ((cocompact α) ×ˢ ⊤)
    _ = map f (cocompact α) ×ˢ map g ⊤ := (prod_map_map_eq' _ _ _ _).symm
    _ ≤ 𝓝 0 ×ˢ map g ⊤                := prod_mono_left _ hf
    _ = 𝓝ˢ {0} ×ˢ map g ⊤             := congrArg (· ×ˢ map g ⊤) nhdsSet_singleton.symm
    _ ≤ 𝓝ˢ ({0} ×ˢ ⊤)                 :=
      nhdsSet_prod_le_of_disjoint_cocompact isCompact_singleton h'g
  have h₂ : Tendsto (Prod.map f g) (⊤ ×ˢ (cocompact β)) (𝓝ˢ (⊤ ×ˢ {0})) := calc
    map (Prod.map f g) (⊤ ×ˢ (cocompact β))
    _ = map f ⊤ ×ˢ map g (cocompact β) := (prod_map_map_eq' _ _ _ _).symm
    _ ≤ map f ⊤ ×ˢ 𝓝 0                := prod_mono_right _ hg
    _ = map f ⊤ ×ˢ 𝓝ˢ {0}             := congrArg (map f ⊤ ×ˢ ·) nhdsSet_singleton.symm
    _ ≤ 𝓝ˢ (⊤ ×ˢ {0})                 :=
      prod_nhdsSet_le_of_disjoint_cocompact isCompact_singleton h'f
  have h₃ : Tendsto (Prod.map f g) (cocompact (α × β)) (𝓝ˢ ({0} ×ˢ ⊤ ∪ ⊤ ×ˢ {0})) := by
    convert h₁.sup_sup h₂
    · exact coprod_cocompact.symm.trans (coprod_eq_prod_top_sup_top_prod _ _)
    · exact nhdsSet_union _ _
  have h₄ : MapsTo (fun (p : M × M) ↦ p.1 * p.2) ({0} ×ˢ ⊤ ∪ ⊤ ×ˢ {0}) {0} := by
    rintro ⟨x, y⟩ (⟨rfl, _⟩ | ⟨_, rfl⟩)
    · exact zero_mul y
    · exact mul_zero x
  have h₅ : Tendsto (fun (p : M × M) ↦ p.1 * p.2) (𝓝ˢ ({0} ×ˢ ⊤ ∪ ⊤ ×ˢ {0})) (𝓝 0) := by
    rw [← nhdsSet_singleton]
    exact continuous_mul.tendsto_nhdsSet h₄
  exact h₅.comp h₃

/-- If `f : α → M` and `g : β → M` both tend to zero on the cofinite filter, then so does
`fun (i : α × β) ↦ (f i.1) * (g i.2)`. -/
theorem tendsto_mul_cofinite_nhds_zero (hf : Tendsto f cofinite (𝓝 0))
    (hg : Tendsto g cofinite (𝓝 0)) :
    Tendsto (fun (i : α × β) ↦ (f i.1) * (g i.2)) cofinite (𝓝 0) := by
  letI : TopologicalSpace α := ⊥
  haveI : DiscreteTopology α := discreteTopology_bot α
  letI : TopologicalSpace β := ⊥
  haveI : DiscreteTopology β := discreteTopology_bot β
  rw [← cocompact_eq_cofinite] at *
  exact tendsto_mul_cocompact_nhds_zero
    continuous_of_discreteTopology continuous_of_discreteTopology hf hg

end MulZeroClass

section MulOneClass

variable [TopologicalSpace M] [MulOneClass M] [ContinuousMul M]

@[to_additive exists_open_nhds_zero_half]
theorem exists_open_nhds_one_split {s : Set M} (hs : s ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ ∀ v ∈ V, ∀ w ∈ V, v * w ∈ s := by
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

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `V * V ⊆ U`. -/
@[to_additive "Given an open neighborhood `U` of `0` there is an open neighborhood `V` of `0`
  such that `V + V ⊆ U`."]
theorem exists_open_nhds_one_mul_subset {U : Set M} (hU : U ∈ 𝓝 (1 : M)) :
    ∃ V : Set M, IsOpen V ∧ (1 : M) ∈ V ∧ V * V ⊆ U := by
  simpa only [mul_subset_iff] using exists_open_nhds_one_split hU
#align exists_open_nhds_one_mul_subset exists_open_nhds_one_mul_subset
#align exists_open_nhds_zero_add_subset exists_open_nhds_zero_add_subset

end MulOneClass

section ContinuousMul

variable [TopologicalSpace M] [Monoid M] [ContinuousMul M]

@[to_additive]
theorem Submonoid.top_closure_mul_self_subset (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s ⊆ _root_.closure s :=
  image2_subset_iff.2 fun _ hx _ hy =>
    map_mem_closure₂ continuous_mul hx hy fun _ ha _ hb => s.mul_mem ha hb
#align submonoid.top_closure_mul_self_subset Submonoid.top_closure_mul_self_subset
#align add_submonoid.top_closure_add_self_subset AddSubmonoid.top_closure_add_self_subset

@[to_additive]
theorem Submonoid.top_closure_mul_self_eq (s : Submonoid M) :
    _root_.closure (s : Set M) * _root_.closure s = _root_.closure s :=
  Subset.antisymm s.top_closure_mul_self_subset fun x hx =>
    ⟨x, hx, 1, _root_.subset_closure s.one_mem, mul_one _⟩
#align submonoid.top_closure_mul_self_eq Submonoid.top_closure_mul_self_eq
#align add_submonoid.top_closure_add_self_eq AddSubmonoid.top_closure_add_self_eq

/-- The (topological-space) closure of a submonoid of a space `M` with `ContinuousMul` is
itself a submonoid. -/
@[to_additive "The (topological-space) closure of an additive submonoid of a space `M` with
`ContinuousAdd` is itself an additive submonoid."]
def Submonoid.topologicalClosure (s : Submonoid M) : Submonoid M where
  carrier := _root_.closure (s : Set M)
  one_mem' := _root_.subset_closure s.one_mem
  mul_mem' ha hb := s.top_closure_mul_self_subset ⟨_, ha, _, hb, rfl⟩
#align submonoid.topological_closure Submonoid.topologicalClosure
#align add_submonoid.topological_closure AddSubmonoid.topologicalClosure

@[to_additive]
theorem Submonoid.coe_topologicalClosure (s : Submonoid M) :
    (s.topologicalClosure : Set M) = _root_.closure (s : Set M) := rfl

@[to_additive]
theorem Submonoid.le_topologicalClosure (s : Submonoid M) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
#align submonoid.le_topological_closure Submonoid.le_topologicalClosure
#align add_submonoid.le_topological_closure AddSubmonoid.le_topologicalClosure

@[to_additive]
theorem Submonoid.isClosed_topologicalClosure (s : Submonoid M) :
    IsClosed (s.topologicalClosure : Set M) := isClosed_closure
#align submonoid.is_closed_topological_closure Submonoid.isClosed_topologicalClosure
#align add_submonoid.is_closed_topological_closure AddSubmonoid.isClosed_topologicalClosure

@[to_additive]
theorem Submonoid.topologicalClosure_minimal (s : Submonoid M) {t : Submonoid M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t := closure_minimal h ht
#align submonoid.topological_closure_minimal Submonoid.topologicalClosure_minimal
#align add_submonoid.topological_closure_minimal AddSubmonoid.topologicalClosure_minimal

/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive "If a submonoid of an additive topological monoid is commutative, then so is its
topological closure."]
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

@[to_additive exists_nhds_zero_quarter]
theorem exists_nhds_one_split4 {u : Set M} (hu : u ∈ 𝓝 (1 : M)) :
    ∃ V ∈ 𝓝 (1 : M), ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u := by
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩
  use V, V1
  intro v w s t v_in w_in s_in t_in
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)
#align exists_nhds_one_split4 exists_nhds_one_split4
#align exists_nhds_zero_quarter exists_nhds_zero_quarter

@[to_additive]
theorem IsCompact.mul {s t : Set M} (hs : IsCompact s) (ht : IsCompact t) : IsCompact (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).image continuous_mul
#align is_compact.mul IsCompact.mul
#align is_compact.add IsCompact.add

@[to_additive]
theorem tendsto_list_prod {f : ι → α → M} {x : Filter α} {a : ι → M} :
    ∀ l : List ι,
      (∀ i ∈ l, Tendsto (f i) x (𝓝 (a i))) →
        Tendsto (fun b => (l.map fun c => f c b).prod) x (𝓝 (l.map a).prod)
  | [], _ => by simp [tendsto_const_nhds]
  | f::l, h => by
    simp only [List.map_cons, List.prod_cons]
    exact
      (h f (List.mem_cons_self _ _)).mul
        (tendsto_list_prod l fun c hc => h c (List.mem_cons_of_mem _ hc))
#align tendsto_list_prod tendsto_list_prod
#align tendsto_list_sum tendsto_list_sum

@[to_additive (attr := continuity)]
theorem continuous_list_prod {f : ι → X → M} (l : List ι) (h : ∀ i ∈ l, Continuous (f i)) :
    Continuous fun a => (l.map fun i => f i a).prod :=
  continuous_iff_continuousAt.2 fun x =>
    tendsto_list_prod l fun c hc => continuous_iff_continuousAt.1 (h c hc) x
#align continuous_list_prod continuous_list_prod
#align continuous_list_sum continuous_list_sum

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
#align continuous_on_list_prod continuousOn_list_prod
#align continuous_on_list_sum continuousOn_list_sum

@[to_additive (attr := continuity)]
theorem continuous_pow : ∀ n : ℕ, Continuous fun a : M => a ^ n
  | 0 => by simpa using continuous_const
  | k + 1 => by
    simp only [pow_succ']
    exact continuous_id.mul (continuous_pow _)
#align continuous_pow continuous_pow
#align continuous_nsmul continuous_nsmul

instance AddMonoid.continuousConstSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousConstSMul ℕ A :=
  ⟨continuous_nsmul⟩
#align add_monoid.has_continuous_const_smul_nat AddMonoid.continuousConstSMul_nat

instance AddMonoid.continuousSMul_nat {A} [AddMonoid A] [TopologicalSpace A]
    [ContinuousAdd A] : ContinuousSMul ℕ A :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_nsmul⟩
#align add_monoid.has_continuous_smul_nat AddMonoid.continuousSMul_nat

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
#align continuous.pow Continuous.pow
#align continuous.nsmul Continuous.nsmul

@[to_additive]
theorem continuousOn_pow {s : Set M} (n : ℕ) : ContinuousOn (fun (x : M) => x ^ n) s :=
  (continuous_pow n).continuousOn
#align continuous_on_pow continuousOn_pow
#align continuous_on_nsmul continuousOn_nsmul

@[to_additive]
theorem continuousAt_pow (x : M) (n : ℕ) : ContinuousAt (fun (x : M) => x ^ n) x :=
  (continuous_pow n).continuousAt
#align continuous_at_pow continuousAt_pow
#align continuous_at_nsmul continuousAt_nsmul

@[to_additive]
theorem Filter.Tendsto.pow {l : Filter α} {f : α → M} {x : M} (hf : Tendsto f l (𝓝 x)) (n : ℕ) :
    Tendsto (fun x => f x ^ n) l (𝓝 (x ^ n)) :=
  (continuousAt_pow _ _).tendsto.comp hf
#align filter.tendsto.pow Filter.Tendsto.pow
#align filter.tendsto.nsmul Filter.Tendsto.nsmul

@[to_additive]
theorem ContinuousWithinAt.pow {f : X → M} {x : X} {s : Set X} (hf : ContinuousWithinAt f s x)
    (n : ℕ) : ContinuousWithinAt (fun x => f x ^ n) s x :=
  Filter.Tendsto.pow hf n
#align continuous_within_at.pow ContinuousWithinAt.pow
#align continuous_within_at.nsmul ContinuousWithinAt.nsmul

@[to_additive (attr := fun_prop)]
theorem ContinuousAt.pow {f : X → M} {x : X} (hf : ContinuousAt f x) (n : ℕ) :
    ContinuousAt (fun x => f x ^ n) x :=
  Filter.Tendsto.pow hf n
#align continuous_at.pow ContinuousAt.pow
#align continuous_at.nsmul ContinuousAt.nsmul

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.pow {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (fun x => f x ^ n) s := fun x hx => (hf x hx).pow n
#align continuous_on.pow ContinuousOn.pow
#align continuous_on.nsmul ContinuousOn.nsmul

/-- Left-multiplication by a left-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) :
    Filter.Tendsto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_mul_left b))
  convert Filter.tendsto_id
  ext x
  simp [← mul_assoc, ha]
#align filter.tendsto_cocompact_mul_left Filter.tendsto_cocompact_mul_left

/-- Right-multiplication by a right-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) :
    Filter.Tendsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M) := by
  refine Filter.Tendsto.of_tendsto_comp ?_ (Filter.comap_cocompact_le (continuous_mul_right b))
  simp only [comp_mul_right, ha, mul_one]
  exact Filter.tendsto_id
  -- Porting note: changed proof
#align filter.tendsto_cocompact_mul_right Filter.tendsto_cocompact_mul_right

/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instances applies when `R = A`, or when `[Algebra R A]` is available. -/
@[to_additive "If `R` acts on `A` via `A`, then continuous addition implies
continuous affine addition by constants."]
instance (priority := 100) IsScalarTower.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [IsScalarTower R A A] [TopologicalSpace A] [ContinuousMul A] : ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp (config := { singlePass := true }) only [← smul_one_mul q (_ : A)]
    exact continuous_const.mul continuous_id
#align is_scalar_tower.has_continuous_const_smul IsScalarTower.continuousConstSMul
#align vadd_assoc_class.has_continuous_const_vadd VAddAssocClass.continuousConstVAdd

/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instances applies when `R = Aᵐᵒᵖ`. -/
@[to_additive "If the action of `R` on `A` commutes with left-addition, then
continuous addition implies continuous affine addition by constants.

Notably, this instances applies when `R = Aᵃᵒᵖ`."]
instance (priority := 100) SMulCommClass.continuousConstSMul {R A : Type*} [Monoid A] [SMul R A]
    [SMulCommClass R A A] [TopologicalSpace A] [ContinuousMul A] : ContinuousConstSMul R A where
  continuous_const_smul q := by
    simp (config := { singlePass := true }) only [← mul_smul_one q (_ : A)]
    exact continuous_id.mul continuous_const
#align smul_comm_class.has_continuous_const_smul SMulCommClass.continuousConstSMul
#align vadd_comm_class.has_continuous_const_vadd VAddCommClass.continuousConstVAdd

end ContinuousMul

namespace MulOpposite

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [TopologicalSpace α] [Mul α] [ContinuousMul α] : ContinuousMul αᵐᵒᵖ :=
  ⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

end MulOpposite

namespace Units

open MulOpposite

variable [TopologicalSpace α] [Monoid α] [ContinuousMul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `Topology.Algebra.Group`,
because the predicate `ContinuousInv` has not yet been defined. -/
@[to_additive "If addition on an additive monoid is continuous, then addition on the additive units
of the monoid, with respect to the induced topology, is continuous.

Negation is also continuous, but we register this in a later file, `Topology.Algebra.Group`, because
the predicate `ContinuousNeg` has not yet been defined."]
instance : ContinuousMul αˣ :=
  inducing_embedProduct.continuousMul (embedProduct α)

end Units

@[to_additive]
theorem Continuous.units_map [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →* N) (hf : Continuous f) : Continuous (Units.map f) :=
  Units.continuous_iff.2 ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩
#align continuous.units_map Continuous.units_map
#align continuous.add_units_map Continuous.addUnits_map

section

variable [TopologicalSpace M] [CommMonoid M]

@[to_additive]
theorem Submonoid.mem_nhds_one (S : Submonoid M) (oS : IsOpen (S : Set M)) :
    (S : Set M) ∈ 𝓝 (1 : M) :=
  IsOpen.mem_nhds oS S.one_mem
#align submonoid.mem_nhds_one Submonoid.mem_nhds_one
#align add_submonoid.mem_nhds_zero AddSubmonoid.mem_nhds_zero

variable [ContinuousMul M]

@[to_additive]
theorem tendsto_multiset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Multiset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => (s.map fun c => f c b).prod) x (𝓝 (s.map a).prod) := by
  rcases s with ⟨l⟩
  simpa using tendsto_list_prod l
#align tendsto_multiset_prod tendsto_multiset_prod
#align tendsto_multiset_sum tendsto_multiset_sum

@[to_additive]
theorem tendsto_finset_prod {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι) :
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
      Tendsto (fun b => ∏ c ∈ s, f c b) x (𝓝 (∏ c ∈ s, a c)) :=
  tendsto_multiset_prod _
#align tendsto_finset_prod tendsto_finset_prod
#align tendsto_finset_sum tendsto_finset_sum

@[to_additive (attr := continuity)]
theorem continuous_multiset_prod {f : ι → X → M} (s : Multiset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => (s.map fun i => f i a).prod := by
  rcases s with ⟨l⟩
  simpa using continuous_list_prod l
#align continuous_multiset_prod continuous_multiset_prod
#align continuous_multiset_sum continuous_multiset_sum

@[to_additive]
theorem continuousOn_multiset_prod {f : ι → X → M} (s : Multiset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => (s.map fun i => f i a).prod) t := by
  rcases s with ⟨l⟩
  simpa using continuousOn_list_prod l
#align continuous_on_multiset_prod continuousOn_multiset_prod
#align continuous_on_multiset_sum continuousOn_multiset_sum

@[to_additive (attr := continuity, fun_prop)]
theorem continuous_finset_prod {f : ι → X → M} (s : Finset ι) :
    (∀ i ∈ s, Continuous (f i)) → Continuous fun a => ∏ i ∈ s, f i a :=
  continuous_multiset_prod _
#align continuous_finset_prod continuous_finset_prod
#align continuous_finset_sum continuous_finset_sum

@[to_additive]
theorem continuousOn_finset_prod {f : ι → X → M} (s : Finset ι) {t : Set X} :
    (∀ i ∈ s, ContinuousOn (f i) t) → ContinuousOn (fun a => ∏ i ∈ s, f i a) t :=
  continuousOn_multiset_prod _
#align continuous_on_finset_prod continuousOn_finset_prod
#align continuous_on_finset_sum continuousOn_finset_sum

@[to_additive]
theorem eventuallyEq_prod {X M : Type*} [CommMonoid M] {s : Finset ι} {l : Filter X}
    {f g : ι → X → M} (hs : ∀ i ∈ s, f i =ᶠ[l] g i) : ∏ i ∈ s, f i =ᶠ[l] ∏ i ∈ s, g i := by
  replace hs : ∀ᶠ x in l, ∀ i ∈ s, f i x = g i x := by rwa [eventually_all_finset]
  filter_upwards [hs] with x hx
  simp only [Finset.prod_apply, Finset.prod_congr rfl hx]
#align eventually_eq_prod eventuallyEq_prod
#align eventually_eq_sum eventuallyEq_sum

open Function

@[to_additive]
theorem LocallyFinite.exists_finset_mulSupport {M : Type*} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport <| f i) (x₀ : X) :
    ∃ I : Finset ι, ∀ᶠ x in 𝓝 x₀, (mulSupport fun i => f i x) ⊆ I := by
  rcases hf x₀ with ⟨U, hxU, hUf⟩
  refine ⟨hUf.toFinset, mem_of_superset hxU fun y hy i hi => ?_⟩
  rw [hUf.coe_toFinset]
  exact ⟨y, hi, hy⟩
#align locally_finite.exists_finset_mul_support LocallyFinite.exists_finset_mulSupport
#align locally_finite.exists_finset_support LocallyFinite.exists_finset_support

@[to_additive]
theorem finprod_eventually_eq_prod {M : Type*} [CommMonoid M] {f : ι → X → M}
    (hf : LocallyFinite fun i => mulSupport (f i)) (x : X) :
    ∃ s : Finset ι, ∀ᶠ y in 𝓝 x, ∏ᶠ i, f i y = ∏ i ∈ s, f i y :=
  let ⟨I, hI⟩ := hf.exists_finset_mulSupport x
  ⟨I, hI.mono fun _ hy => finprod_eq_prod_of_mulSupport_subset _ fun _ hi => hy hi⟩
#align finprod_eventually_eq_prod finprod_eventually_eq_prod
#align finsum_eventually_eq_sum finsum_eventually_eq_sum

@[to_additive]
theorem continuous_finprod {f : ι → X → M} (hc : ∀ i, Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) : Continuous fun x => ∏ᶠ i, f i x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩
  refine ContinuousAt.congr ?_ (EventuallyEq.symm hs)
  exact tendsto_finset_prod _ fun i _ => (hc i).continuousAt
#align continuous_finprod continuous_finprod
#align continuous_finsum continuous_finsum

@[to_additive]
theorem continuous_finprod_cond {f : ι → X → M} {p : ι → Prop} (hc : ∀ i, p i → Continuous (f i))
    (hf : LocallyFinite fun i => mulSupport (f i)) :
    Continuous fun x => ∏ᶠ (i) (_ : p i), f i x := by
  simp only [← finprod_subtype_eq_finprod_cond]
  exact continuous_finprod (fun i => hc i i.2) (hf.comp_injective Subtype.coe_injective)
#align continuous_finprod_cond continuous_finprod_cond
#align continuous_finsum_cond continuous_finsum_cond

end

instance [TopologicalSpace M] [Mul M] [ContinuousMul M] : ContinuousAdd (Additive M) where
  continuous_add := @continuous_mul M _ _ _

instance [TopologicalSpace M] [Add M] [ContinuousAdd M] : ContinuousMul (Multiplicative M) where
  continuous_mul := @continuous_add M _ _ _

section LatticeOps

variable {ι' : Sort*} [Mul M]

@[to_additive]
theorem continuousMul_sInf {ts : Set (TopologicalSpace M)}
    (h : ∀ t ∈ ts, @ContinuousMul M t _) : @ContinuousMul M (sInf ts) _ :=
  letI := sInf ts
  { continuous_mul :=
      continuous_sInf_rng.2 fun t ht =>
        continuous_sInf_dom₂ ht ht (@ContinuousMul.continuous_mul M t _ (h t ht)) }
#align has_continuous_mul_Inf continuousMul_sInf
#align has_continuous_add_Inf continuousAdd_sInf

@[to_additive]
theorem continuousMul_iInf {ts : ι' → TopologicalSpace M}
    (h' : ∀ i, @ContinuousMul M (ts i) _) : @ContinuousMul M (⨅ i, ts i) _ := by
  rw [← sInf_range]
  exact continuousMul_sInf (Set.forall_mem_range.mpr h')
#align has_continuous_mul_infi continuousMul_iInf
#align has_continuous_add_infi continuousAdd_iInf

@[to_additive]
theorem continuousMul_inf {t₁ t₂ : TopologicalSpace M} (h₁ : @ContinuousMul M t₁ _)
    (h₂ : @ContinuousMul M t₂ _) : @ContinuousMul M (t₁ ⊓ t₂) _ := by
  rw [inf_eq_iInf]
  refine continuousMul_iInf fun b => ?_
  cases b <;> assumption
#align has_continuous_mul_inf continuousMul_inf
#align has_continuous_add_inf continuousAdd_inf

end LatticeOps

namespace ContinuousMap

variable [Mul X] [ContinuousMul X]

/-- The continuous map `fun y => y * x` -/
@[to_additive "The continuous map `fun y => y + x`"]
protected def mulRight (x : X) : C(X, X) :=
  mk _ (continuous_mul_right x)
#align continuous_map.mul_right ContinuousMap.mulRight
#align continuous_map.add_right ContinuousMap.addRight

@[to_additive (attr := simp)]
theorem coe_mulRight (x : X) : ⇑(ContinuousMap.mulRight x) = fun y => y * x :=
  rfl
#align continuous_map.coe_mul_right ContinuousMap.coe_mulRight
#align continuous_map.coe_add_right ContinuousMap.coe_addRight

/-- The continuous map `fun y => x * y` -/
@[to_additive "The continuous map `fun y => x + y`"]
protected def mulLeft (x : X) : C(X, X) :=
  mk _ (continuous_mul_left x)
#align continuous_map.mul_left ContinuousMap.mulLeft
#align continuous_map.add_left ContinuousMap.addLeft

@[to_additive (attr := simp)]
theorem coe_mulLeft (x : X) : ⇑(ContinuousMap.mulLeft x) = fun y => x * y :=
  rfl
#align continuous_map.coe_mul_left ContinuousMap.coe_mulLeft
#align continuous_map.coe_add_left ContinuousMap.coe_addLeft

end ContinuousMap
