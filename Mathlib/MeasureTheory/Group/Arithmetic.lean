/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module measure_theory.group.arithmetic
! leanprover-community/mathlib commit a75898643b2d774cced9ae7c0b28c21663b99666
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.AeMeasurable

/-!
# Typeclasses for measurability of operations

In this file we define classes `has_measurable_mul` etc and prove dot-style lemmas
(`measurable.mul`, `ae_measurable.mul` etc). For binary operations we define two typeclasses:

- `has_measurable_mul` says that both left and right multiplication are measurable;
- `has_measurable_mul₂` says that `λ p : α × α, p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_mul₂`
etc require `α` to have a second countable topology.

We define separate classes for `has_measurable_div`/`has_measurable_sub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `has_continuous_mul` to `has_measurable_mul` see file
`measure_theory.borel_space`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operations) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## Todo

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `has_measurable_pow` to `has_measurable_smul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `measurable_smul`.)
-/


universe u v

open BigOperators Pointwise MeasureTheory

open MeasureTheory

/-!
### Binary operations: `(+)`, `(*)`, `(-)`, `(/)`
-/


/-- We say that a type `has_measurable_add` if `((+) c)` and `(+ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (+)` see `has_measurable_add₂`. -/
class HasMeasurableAdd (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable ((· + ·) c)
  measurable_add_const : ∀ c : M, Measurable (· + c)
#align has_measurable_add HasMeasurableAdd

export HasMeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type `has_measurable_add` if `uncurry (+)` is a measurable functions.
For a typeclass assuming measurability of `((+) c)` and `(+ c)` see `has_measurable_add`. -/
class HasMeasurableAdd₂ (M : Type _) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2
#align has_measurable_add₂ HasMeasurableAdd₂

export HasMeasurableAdd₂ (measurable_add)

export HasMeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type `has_measurable_mul` if `((*) c)` and `(* c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `has_measurable_mul₂`. -/
@[to_additive]
class HasMeasurableMul (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable ((· * ·) c)
  measurable_mul_const : ∀ c : M, Measurable (· * c)
#align has_measurable_mul HasMeasurableMul
#align has_measurable_add HasMeasurableAdd

export HasMeasurableMul (measurable_const_mul measurable_mul_const)

/-- We say that a type `has_measurable_mul` if `uncurry (*)` is a measurable functions.
For a typeclass assuming measurability of `((*) c)` and `(* c)` see `has_measurable_mul`. -/
@[to_additive HasMeasurableAdd₂]
class HasMeasurableMul₂ (M : Type _) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2
#align has_measurable_mul₂ HasMeasurableMul₂
#align has_measurable_add₂ HasMeasurableAdd₂

export HasMeasurableMul₂ (measurable_mul)

section Mul

variable {M α : Type _} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α} {f g : α → M}
  {μ : Measure α}

include m

@[measurability, to_additive]
theorem Measurable.const_mul [HasMeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf
#align measurable.const_mul Measurable.const_mul
#align measurable.const_add Measurable.const_add

@[measurability, to_additive]
theorem AEMeasurable.const_mul [HasMeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c * f x) μ :=
  (HasMeasurableMul.measurable_const_mul c).comp_aemeasurable hf
#align ae_measurable.const_mul AEMeasurable.const_mul
#align ae_measurable.const_add AEMeasurable.const_add

@[measurability, to_additive]
theorem Measurable.mul_const [HasMeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf
#align measurable.mul_const Measurable.mul_const
#align measurable.add_const Measurable.add_const

@[measurability, to_additive]
theorem AEMeasurable.mul_const [HasMeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_aemeasurable hf
#align ae_measurable.mul_const AEMeasurable.mul_const
#align ae_measurable.add_const AEMeasurable.add_const

@[measurability, to_additive]
theorem Measurable.mul' [HasMeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f * g) :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul' Measurable.mul'
#align measurable.add' Measurable.add'

@[measurability, to_additive]
theorem Measurable.mul [HasMeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul Measurable.mul
#align measurable.add Measurable.add

@[measurability, to_additive]
theorem AEMeasurable.mul' [HasMeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f * g) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul' AEMeasurable.mul'
#align ae_measurable.add' AEMeasurable.add'

@[measurability, to_additive]
theorem AEMeasurable.mul [HasMeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a * g a) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul AEMeasurable.mul
#align ae_measurable.add AEMeasurable.add

omit m

@[to_additive]
instance (priority := 100) HasMeasurableMul₂.to_hasMeasurableMul [HasMeasurableMul₂ M] :
    HasMeasurableMul M :=
  ⟨fun c => measurable_const.mul measurable_id, fun c => measurable_id.mul measurable_const⟩
#align has_measurable_mul₂.to_has_measurable_mul HasMeasurableMul₂.to_hasMeasurableMul
#align has_measurable_add₂.to_has_measurable_add HasMeasurableAdd₂.to_has_measurable_add

@[to_additive]
instance Pi.hasMeasurableMul {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableMul (α i)] : HasMeasurableMul (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun g =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩
#align pi.has_measurable_mul Pi.hasMeasurableMul
#align pi.has_measurable_add Pi.has_measurable_add

@[to_additive Pi.has_measurable_add₂]
instance Pi.hasMeasurableMul₂ {ι : Type _} {α : ι → Type _} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableMul₂ (α i)] : HasMeasurableMul₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurable_fst.eval.mul measurable_snd.eval⟩
#align pi.has_measurable_mul₂ Pi.hasMeasurableMul₂
#align pi.has_measurable_add₂ Pi.has_measurable_add₂

attribute [measurability]
  Measurable.add' Measurable.add AEMeasurable.add AEMeasurable.add' Measurable.const_add AEMeasurable.const_add Measurable.add_const AEMeasurable.add_const

end Mul

/-- A version of `measurable_div_const` that assumes `has_measurable_mul` instead of
  `has_measurable_div`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive
      " A version of `measurable_sub_const` that assumes `has_measurable_add` instead of\n  `has_measurable_sub`. This can be nice to avoid unnecessary type-class assumptions. "]
theorem measurable_div_const' {G : Type _} [DivInvMonoid G] [MeasurableSpace G] [HasMeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]
#align measurable_div_const' measurable_div_const'
#align measurable_sub_const' measurable_sub_const'

/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class HasMeasurablePow (β γ : Type _) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2
#align has_measurable_pow HasMeasurablePow

export HasMeasurablePow (measurable_pow)

/-- `monoid.has_pow` is measurable. -/
instance Monoid.hasMeasurablePow (M : Type _) [Monoid M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurablePow M ℕ :=
  ⟨measurable_from_prod_countable fun n =>
      by
      induction' n with n ih
      · simp only [pow_zero, ← Pi.one_def, measurable_one]
      · simp only [pow_succ]
        exact measurable_id.mul ih⟩
#align monoid.has_measurable_pow Monoid.hasMeasurablePow

section Pow

variable {β γ α : Type _} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [HasMeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}

include m

@[measurability]
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prod_mk hg)
#align measurable.pow Measurable.pow

@[measurability]
theorem AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.pow AEMeasurable.pow

@[measurability]
theorem Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const
#align measurable.pow_const Measurable.pow_const

@[measurability]
theorem AEMeasurable.pow_const (hf : AEMeasurable f μ) (c : γ) :
    AEMeasurable (fun x => f x ^ c) μ :=
  hf.pow aemeasurable_const
#align ae_measurable.pow_const AEMeasurable.pow_const

@[measurability]
theorem Measurable.const_pow (hg : Measurable g) (c : β) : Measurable fun x => c ^ g x :=
  measurable_const.pow hg
#align measurable.const_pow Measurable.const_pow

@[measurability]
theorem AEMeasurable.const_pow (hg : AEMeasurable g μ) (c : β) :
    AEMeasurable (fun x => c ^ g x) μ :=
  aemeasurable_const.pow hg
#align ae_measurable.const_pow AEMeasurable.const_pow

omit m

end Pow

/-- We say that a type `has_measurable_sub` if `(λ x, c - x)` and `(λ x, x - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `has_measurable_sub₂`. -/
class HasMeasurableSub (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : ∀ c : G, Measurable fun x => c - x
  measurable_sub_const : ∀ c : G, Measurable fun x => x - c
#align has_measurable_sub HasMeasurableSub

export HasMeasurableSub (measurable_const_sub measurable_sub_const)

/-- We say that a type `has_measurable_sub` if `uncurry (-)` is a measurable functions.
For a typeclass assuming measurability of `((-) c)` and `(- c)` see `has_measurable_sub`. -/
class HasMeasurableSub₂ (G : Type _) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2
#align has_measurable_sub₂ HasMeasurableSub₂

export HasMeasurableSub₂ (measurable_sub)

/-- We say that a type `has_measurable_div` if `((/) c)` and `(/ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (/)` see `has_measurable_div₂`. -/
@[to_additive]
class HasMeasurableDiv (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_const_div : ∀ c : G₀, Measurable ((· / ·) c)
  measurable_div_const : ∀ c : G₀, Measurable (· / c)
#align has_measurable_div HasMeasurableDiv
#align has_measurable_sub HasMeasurableSub

export HasMeasurableDiv (measurable_const_div measurable_div_const)

/-- We say that a type `has_measurable_div` if `uncurry (/)` is a measurable functions.
For a typeclass assuming measurability of `((/) c)` and `(/ c)` see `has_measurable_div`. -/
@[to_additive HasMeasurableSub₂]
class HasMeasurableDiv₂ (G₀ : Type _) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2
#align has_measurable_div₂ HasMeasurableDiv₂
#align has_measurable_sub₂ HasMeasurableSub₂

export HasMeasurableDiv₂ (measurable_div)

section Div

variable {G α : Type _} [MeasurableSpace G] [Div G] {m : MeasurableSpace α} {f g : α → G}
  {μ : Measure α}

include m

@[measurability, to_additive]
theorem Measurable.const_div [HasMeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (HasMeasurableDiv.measurable_const_div c).comp hf
#align measurable.const_div Measurable.const_div
#align measurable.const_sub Measurable.const_sub

@[measurability, to_additive]
theorem AEMeasurable.const_div [HasMeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => c / f x) μ :=
  (HasMeasurableDiv.measurable_const_div c).comp_aemeasurable hf
#align ae_measurable.const_div AEMeasurable.const_div
#align ae_measurable.const_sub AEMeasurable.const_sub

@[measurability, to_additive]
theorem Measurable.div_const [HasMeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (HasMeasurableDiv.measurable_div_const c).comp hf
#align measurable.div_const Measurable.div_const
#align measurable.sub_const Measurable.sub_const

@[measurability, to_additive]
theorem AEMeasurable.div_const [HasMeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => f x / c) μ :=
  (HasMeasurableDiv.measurable_div_const c).comp_aemeasurable hf
#align ae_measurable.div_const AEMeasurable.div_const
#align ae_measurable.sub_const AEMeasurable.sub_const

@[measurability, to_additive]
theorem Measurable.div' [HasMeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div' Measurable.div'
#align measurable.sub' Measurable.sub'

@[measurability, to_additive]
theorem Measurable.div [HasMeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a / g a :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div Measurable.div
#align measurable.sub Measurable.sub

@[measurability, to_additive]
theorem AEMeasurable.div' [HasMeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f / g) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div' AEMeasurable.div'
#align ae_measurable.sub' AEMeasurable.sub'

@[measurability, to_additive]
theorem AEMeasurable.div [HasMeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a / g a) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div AEMeasurable.div
#align ae_measurable.sub AEMeasurable.sub

attribute [measurability]
  Measurable.sub Measurable.sub' AEMeasurable.sub AEMeasurable.sub' Measurable.const_sub AEMeasurable.const_sub Measurable.sub_const AEMeasurable.sub_const

omit m

@[to_additive]
instance (priority := 100) HasMeasurableDiv₂.to_hasMeasurableDiv [HasMeasurableDiv₂ G] :
    HasMeasurableDiv G :=
  ⟨fun c => measurable_const.div measurable_id, fun c => measurable_id.div measurable_const⟩
#align has_measurable_div₂.to_has_measurable_div HasMeasurableDiv₂.to_hasMeasurableDiv
#align has_measurable_sub₂.to_has_measurable_sub HasMeasurableSub₂.to_has_measurable_sub

@[to_additive]
instance Pi.hasMeasurableDiv {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableDiv (α i)] : HasMeasurableDiv (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun g =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩
#align pi.has_measurable_div Pi.hasMeasurableDiv
#align pi.has_measurable_sub Pi.has_measurable_sub

@[to_additive Pi.has_measurable_sub₂]
instance Pi.hasMeasurableDiv₂ {ι : Type _} {α : ι → Type _} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableDiv₂ (α i)] : HasMeasurableDiv₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => measurable_fst.eval.div measurable_snd.eval⟩
#align pi.has_measurable_div₂ Pi.hasMeasurableDiv₂
#align pi.has_measurable_sub₂ Pi.has_measurable_sub₂

@[measurability]
theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [MeasurableSpace E] [AddGroup E]
    [MeasurableSingletonClass E] [HasMeasurableSub₂ E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } :=
  by
  suffices h_set_eq : { x : α | f x = g x } = { x | (f - g) x = (0 : E) }
  · rw [h_set_eq]
    exact (hf.sub hg) measurableSet_eq
  ext
  simp_rw [Set.mem_setOf_eq, Pi.sub_apply, sub_eq_zero]
#align measurable_set_eq_fun measurableSet_eq_fun

theorem nullMeasurableSet_eq_fun {E} [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E]
    [HasMeasurableSub₂ E] {f g : α → E} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ :=
  by
  apply (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk).NullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk]with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]
#align null_measurable_set_eq_fun nullMeasurableSet_eq_fun

theorem measurableSet_eq_fun_of_countable {m : MeasurableSpace α} {E} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } :=
  by
  have : { x | f x = g x } = ⋃ j, { x | f x = j } ∩ { x | g x = j } :=
    by
    ext1 x
    simp only [Set.mem_setOf_eq, Set.mem_unionᵢ, Set.mem_inter_iff, exists_eq_right']
  rw [this]
  refine' MeasurableSet.unionᵢ fun j => MeasurableSet.inter _ _
  · exact hf (measurable_set_singleton j)
  · exact hg (measurable_set_singleton j)
#align measurable_set_eq_fun_of_countable measurableSet_eq_fun_of_countable

theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [HasMeasurableSub₂ E]
    (hm : m ≤ m0) {f g : α → E} (hf : measurable[m] f) (hg : measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᶠ[@Measure.ae α m (μ.trim hm)] g :=
  by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurable_set_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurableSet_eq_fun α m E _ _ _ _ _ _ hf hg)
#align ae_eq_trim_of_measurable ae_eq_trim_of_measurable

end Div

/-- We say that a type `has_measurable_neg` if `x ↦ -x` is a measurable function. -/
class HasMeasurableNeg (G : Type _) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G → G)
#align has_measurable_neg HasMeasurableNeg

/-- We say that a type `has_measurable_inv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class HasMeasurableInv (G : Type _) [Inv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (Inv.inv : G → G)
#align has_measurable_inv HasMeasurableInv
#align has_measurable_neg HasMeasurableNeg

export HasMeasurableInv (measurable_inv)

export HasMeasurableNeg (measurable_neg)

@[to_additive]
instance (priority := 100) hasMeasurableDiv_of_mul_inv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [HasMeasurableMul G] [HasMeasurableInv G] : HasMeasurableDiv G
    where
  measurable_const_div c := by
    convert measurable_inv.const_mul c
    ext1
    apply div_eq_mul_inv
  measurable_div_const c := by
    convert measurable_id.mul_const c⁻¹
    ext1
    apply div_eq_mul_inv
#align has_measurable_div_of_mul_inv hasMeasurableDiv_of_mul_inv
#align has_measurable_sub_of_add_neg has_measurable_sub_of_add_neg

section Inv

variable {G α : Type _} [Inv G] [MeasurableSpace G] [HasMeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}

include m

@[measurability, to_additive]
theorem Measurable.inv (hf : Measurable f) : Measurable fun x => (f x)⁻¹ :=
  measurable_inv.comp hf
#align measurable.inv Measurable.inv
#align measurable.neg Measurable.neg

@[measurability, to_additive]
theorem AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurable (fun x => (f x)⁻¹) μ :=
  measurable_inv.comp_aemeasurable hf
#align ae_measurable.inv AEMeasurable.inv
#align ae_measurable.neg AEMeasurable.neg

attribute [measurability] Measurable.neg AEMeasurable.neg

@[simp, to_additive]
theorem measurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [HasMeasurableInv G]
    {f : α → G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff measurable_inv_iff
#align measurable_neg_iff measurable_neg_iff

@[simp, to_additive]
theorem aEMeasurable_inv_iff {G : Type _} [Group G] [MeasurableSpace G] [HasMeasurableInv G]
    {f : α → G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff aEMeasurable_inv_iff
#align ae_measurable_neg_iff aEMeasurable_neg_iff

@[simp]
theorem measurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀]
    [HasMeasurableInv G₀] {f : α → G₀} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff₀ measurable_inv_iff₀

@[simp]
theorem aEMeasurable_inv_iff₀ {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀]
    [HasMeasurableInv G₀] {f : α → G₀} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff₀ aEMeasurable_inv_iff₀

omit m

@[to_additive]
instance Pi.hasMeasurableInv {ι : Type _} {α : ι → Type _} [∀ i, Inv (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableInv (α i)] : HasMeasurableInv (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩
#align pi.has_measurable_inv Pi.hasMeasurableInv
#align pi.has_measurable_neg Pi.has_measurable_neg

@[to_additive]
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurable_inv hs
#align measurable_set.inv MeasurableSet.inv
#align measurable_set.neg MeasurableSet.neg

end Inv

/-- `div_inv_monoid.has_pow` is measurable. -/
instance DivInvMonoid.hasMeasurableZpow (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
    [HasMeasurableMul₂ G] [HasMeasurableInv G] : HasMeasurablePow G ℤ :=
  ⟨measurable_from_prod_countable fun n => by
      cases' n with n n
      · simp_rw [zpow_ofNat]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩
#align div_inv_monoid.has_measurable_zpow DivInvMonoid.hasMeasurableZpow

@[to_additive]
instance (priority := 100) hasMeasurableDiv₂_of_mul_inv (G : Type _) [MeasurableSpace G]
    [DivInvMonoid G] [HasMeasurableMul₂ G] [HasMeasurableInv G] : HasMeasurableDiv₂ G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩
#align has_measurable_div₂_of_mul_inv hasMeasurableDiv₂_of_mul_inv
#align has_measurable_div₂_of_add_neg hasMeasurableDiv₂_of_add_neg

/-- We say that the action of `M` on `α` `has_measurable_vadd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd (M α : Type _) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurable_const_vadd : ∀ c : M, Measurable ((· +ᵥ ·) c : α → α)
  measurable_vadd_const : ∀ x : α, Measurable fun c : M => c +ᵥ x
#align has_measurable_vadd HasMeasurableVadd

/-- We say that the action of `M` on `α` `has_measurable_smul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class HasMeasurableSmul (M α : Type _) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurable_const_smul : ∀ c : M, Measurable ((· • ·) c : α → α)
  measurable_smul_const : ∀ x : α, Measurable fun c : M => c • x
#align has_measurable_smul HasMeasurableSmul
#align has_measurable_vadd HasMeasurableVadd

/-- We say that the action of `M` on `α` `has_measurable_vadd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class HasMeasurableVadd₂ (M α : Type _) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)
#align has_measurable_vadd₂ HasMeasurableVadd₂

/-- We say that the action of `M` on `α` `has_measurable_smul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive HasMeasurableVadd₂]
class HasMeasurableSmul₂ (M α : Type _) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] :
  Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α → α)
#align has_measurable_smul₂ HasMeasurableSmul₂
#align has_measurable_vadd₂ HasMeasurableVadd₂

export HasMeasurableSmul (measurable_const_smul measurable_smul_const)

export HasMeasurableSmul₂ (measurable_smul)

export HasMeasurableVadd (measurable_const_vadd measurable_vadd_const)

export HasMeasurableVadd₂ (measurable_vadd)

@[to_additive]
instance hasMeasurableSmul_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul M] :
    HasMeasurableSmul M M :=
  ⟨measurable_id.const_mul, measurable_id.mul_const⟩
#align has_measurable_smul_of_mul hasMeasurableSmul_of_mul
#align has_measurable_vadd_of_add has_measurable_vadd_of_add

@[to_additive]
instance hasMeasurableSmul₂_of_mul (M : Type _) [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] :
    HasMeasurableSmul₂ M M :=
  ⟨measurable_mul⟩
#align has_measurable_smul₂_of_mul hasMeasurableSmul₂_of_mul
#align has_measurable_smul₂_of_add hasMeasurableSmul₂_of_add

@[to_additive]
instance Submonoid.hasMeasurableSmul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [HasMeasurableSmul M α] (s : Submonoid M) : HasMeasurableSmul s α :=
  ⟨fun c => by simpa only using measurable_const_smul (c : M), fun x =>
    (measurable_smul_const x : Measurable fun c : M => c • x).comp measurable_subtype_coe⟩
#align submonoid.has_measurable_smul Submonoid.hasMeasurableSmul
#align add_submonoid.has_measurable_vadd AddSubmonoid.has_measurable_vadd

@[to_additive]
instance Subgroup.hasMeasurableSmul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [HasMeasurableSmul G α] (s : Subgroup G) : HasMeasurableSmul s α :=
  s.toSubmonoid.HasMeasurableSmul
#align subgroup.has_measurable_smul Subgroup.hasMeasurableSmul
#align add_subgroup.has_measurable_vadd AddSubgroup.has_measurable_vadd

section Smul

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [SMul M β] {m : MeasurableSpace α}
  {f : α → M} {g : α → β}

include m

@[measurability, to_additive]
theorem Measurable.smul [HasMeasurableSmul₂ M β] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurable_smul.comp (hf.prod_mk hg)
#align measurable.smul Measurable.smul
#align measurable.vadd Measurable.vadd

@[measurability, to_additive]
theorem AEMeasurable.smul [HasMeasurableSmul₂ M β] {μ : Measure α} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun x => f x • g x) μ :=
  HasMeasurableSmul₂.measurable_smul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.smul AEMeasurable.smul
#align ae_measurable.vadd AEMeasurable.vadd

omit m

@[to_additive]
instance (priority := 100) HasMeasurableSmul₂.to_hasMeasurableSmul [HasMeasurableSmul₂ M β] :
    HasMeasurableSmul M β :=
  ⟨fun c => measurable_const.smul measurable_id, fun y => measurable_id.smul measurable_const⟩
#align has_measurable_smul₂.to_has_measurable_smul HasMeasurableSmul₂.to_hasMeasurableSmul
#align has_measurable_vadd₂.to_has_measurable_vadd HasMeasurableVadd₂.to_has_measurable_vadd

include m

variable [HasMeasurableSmul M β] {μ : Measure α}

@[measurability, to_additive]
theorem Measurable.smul_const (hf : Measurable f) (y : β) : Measurable fun x => f x • y :=
  (HasMeasurableSmul.measurable_smul_const y).comp hf
#align measurable.smul_const Measurable.smul_const
#align measurable.vadd_const Measurable.vadd_const

@[measurability, to_additive]
theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : β) :
    AEMeasurable (fun x => f x • y) μ :=
  (HasMeasurableSmul.measurable_smul_const y).comp_aemeasurable hf
#align ae_measurable.smul_const AEMeasurable.smul_const
#align ae_measurable.vadd_const AEMeasurable.vadd_const

@[measurability, to_additive]
theorem Measurable.const_smul' (hg : Measurable g) (c : M) : Measurable fun x => c • g x :=
  (HasMeasurableSmul.measurable_const_smul c).comp hg
#align measurable.const_smul' Measurable.const_smul'
#align measurable.const_vadd' Measurable.const_vadd'

@[measurability, to_additive]
theorem Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  hg.const_smul' c
#align measurable.const_smul Measurable.const_smul
#align measurable.const_vadd Measurable.const_vadd

@[measurability, to_additive]
theorem AEMeasurable.const_smul' (hg : AEMeasurable g μ) (c : M) :
    AEMeasurable (fun x => c • g x) μ :=
  (HasMeasurableSmul.measurable_const_smul c).comp_aemeasurable hg
#align ae_measurable.const_smul' AEMeasurable.const_smul'
#align ae_measurable.const_vadd' AEMeasurable.const_vadd'

@[measurability, to_additive]
theorem AEMeasurable.const_smul (hf : AEMeasurable g μ) (c : M) : AEMeasurable (c • g) μ :=
  hf.const_smul' c
#align ae_measurable.const_smul AEMeasurable.const_smul
#align ae_measurable.const_vadd AEMeasurable.const_vadd

omit m

@[to_additive]
instance Pi.hasMeasurableSmul {ι : Type _} {α : ι → Type _} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, HasMeasurableSmul M (α i)] :
    HasMeasurableSmul M (∀ i, α i) :=
  ⟨fun g => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_smul _, fun g =>
    measurable_pi_iff.mpr fun i => measurable_smul_const _⟩
#align pi.has_measurable_smul Pi.hasMeasurableSmul
#align pi.has_measurable_vadd Pi.has_measurable_vadd

/-- `add_monoid.has_smul_nat` is measurable. -/
instance AddMonoid.has_measurable_smul_nat₂ (M : Type _) [AddMonoid M] [MeasurableSpace M]
    [HasMeasurableAdd₂ M] : HasMeasurableSmul₂ ℕ M :=
  ⟨by
    suffices Measurable fun p : M × ℕ => p.2 • p.1 by apply this.comp measurable_swap
    refine' measurable_from_prod_countable fun n => _
    induction' n with n ih
    · simp only [zero_smul, ← Pi.zero_def, measurable_zero]
    · simp only [succ_nsmul]
      exact measurable_id.add ih⟩
#align add_monoid.has_measurable_smul_nat₂ AddMonoid.has_measurable_smul_nat₂

/-- `sub_neg_monoid.has_smul_int` is measurable. -/
instance SubNegMonoid.has_measurable_smul_int₂ (M : Type _) [SubNegMonoid M] [MeasurableSpace M]
    [HasMeasurableAdd₂ M] [HasMeasurableNeg M] : HasMeasurableSmul₂ ℤ M :=
  ⟨by
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by apply this.comp measurable_swap
    refine' measurable_from_prod_countable fun n => _
    induction' n with n n ih
    · simp only [ofNat_zsmul]
      exact measurable_const_smul _
    · simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩
#align sub_neg_monoid.has_measurable_smul_int₂ SubNegMonoid.has_measurable_smul_int₂

end Smul

section MulAction

variable {M β α : Type _} [MeasurableSpace M] [MeasurableSpace β] [Monoid M] [MulAction M β]
  [HasMeasurableSmul M β] [MeasurableSpace α] {f : α → β} {μ : Measure α}

variable {G : Type _} [Group G] [MeasurableSpace G] [MulAction G β] [HasMeasurableSmul G β]

@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align measurable_const_smul_iff measurable_const_smul_iff
#align measurable_const_vadd_iff measurable_const_vadd_iff

@[to_additive]
theorem aEMeasurable_const_smul_iff (c : G) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align ae_measurable_const_smul_iff aEMeasurable_const_smul_iff
#align ae_measurable_const_vadd_iff aEMeasurable_const_vadd_iff

@[to_additive]
instance : MeasurableSpace Mˣ :=
  MeasurableSpace.comap (coe : Mˣ → M) ‹_›

@[to_additive]
instance Units.hasMeasurableSmul : HasMeasurableSmul Mˣ β
    where
  measurable_const_smul c := (measurable_const_smul (c : M) : _)
  measurable_smul_const x :=
    (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap
#align units.has_measurable_smul Units.hasMeasurableSmul
#align add_units.has_measurable_vadd AddUnits.has_measurable_vadd

@[to_additive]
theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u
#align is_unit.measurable_const_smul_iff IsUnit.measurable_const_smul_iff
#align is_add_unit.measurable_const_vadd_iff IsAddUnit.measurable_const_vadd_iff

@[to_additive]
theorem IsUnit.aEMeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aEMeasurable_const_smul_iff u
#align is_unit.ae_measurable_const_smul_iff IsUnit.aEMeasurable_const_smul_iff
#align is_add_unit.ae_measurable_const_vadd_iff IsAddUnit.aEMeasurable_const_vadd_iff

variable {G₀ : Type _} [GroupWithZero G₀] [MeasurableSpace G₀] [MulAction G₀ β]
  [HasMeasurableSmul G₀ β]

theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff
#align measurable_const_smul_iff₀ measurable_const_smul_iff₀

theorem aEMeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  (IsUnit.mk0 c hc).aEMeasurable_const_smul_iff
#align ae_measurable_const_smul_iff₀ aEMeasurable_const_smul_iff₀

end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

@[to_additive]
instance {α : Type _} [h : MeasurableSpace α] : MeasurableSpace αᵐᵒᵖ :=
  MeasurableSpace.map op h

@[to_additive]
theorem measurable_mul_op {α : Type _} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun s =>
  id
#align measurable_mul_op measurable_mul_op
#align measurable_add_op measurable_add_op

@[to_additive]
theorem measurable_mul_unop {α : Type _} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) :=
  fun s => id
#align measurable_mul_unop measurable_mul_unop
#align measurable_add_unop measurable_add_unop

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul M] : HasMeasurableMul Mᵐᵒᵖ :=
  ⟨fun c => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun c =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]
instance {M : Type _} [Mul M] [MeasurableSpace M] [HasMeasurableMul₂ M] : HasMeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance HasMeasurableSmul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] [HasMeasurableSmul M α] : HasMeasurableSmul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c =>
      show Measurable fun x => op c • x by
        simpa only [op_smul_eq_smul] using measurable_const_smul c,
    fun x =>
    show Measurable fun c => op (unop c) • x by
      simpa only [op_smul_eq_smul] using (measurable_smul_const x).comp measurable_mul_unop⟩
#align has_measurable_smul.op HasMeasurableSmul.op

/-- If a scalar is central, then its right action is measurable when its left action is. -/
instance HasMeasurableSmul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [HasMeasurableSmul₂ M α] : HasMeasurableSmul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2
      by
      simp_rw [op_smul_eq_smul]
      refine' (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩
#align has_measurable_smul₂.op HasMeasurableSmul₂.op

@[to_additive]
instance hasMeasurableSmul_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M]
    [HasMeasurableMul M] : HasMeasurableSmul Mᵐᵒᵖ M :=
  ⟨fun c => measurable_mul_const (unop c), fun x => measurable_mul_unop.const_mul x⟩
#align has_measurable_smul_opposite_of_mul hasMeasurableSmul_opposite_of_mul
#align has_measurable_vadd_opposite_of_add has_measurable_vadd_opposite_of_add

@[to_additive]
instance hasMeasurableSmul₂_opposite_of_mul {M : Type _} [Mul M] [MeasurableSpace M]
    [HasMeasurableMul₂ M] : HasMeasurableSmul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩
#align has_measurable_smul₂_opposite_of_mul hasMeasurableSmul₂_opposite_of_mul
#align has_measurable_smul₂_opposite_of_add hasMeasurableSmul₂_opposite_of_add

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type _} [Monoid M] [MeasurableSpace M] [HasMeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

include m

@[measurability, to_additive]
theorem List.measurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) : Measurable l.Prod :=
  by
  induction' l with f l ihl; · exact measurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.measurable_prod' List.measurable_prod'
#align list.measurable_sum' List.measurable_sum'

@[measurability, to_additive]
theorem List.aEMeasurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.Prod μ := by
  induction' l with f l ihl; · exact aEMeasurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.ae_measurable_prod' List.aEMeasurable_prod'
#align list.ae_measurable_sum' List.aEMeasurable_sum'

@[measurability, to_additive]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod' hl
#align list.measurable_prod List.measurable_prod
#align list.measurable_sum List.measurable_sum

@[measurability, to_additive]
theorem List.aEMeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.ae_measurable_prod' hl
#align list.ae_measurable_prod List.aEMeasurable_prod
#align list.ae_measurable_sum List.aEMeasurable_sum

omit m

end Monoid

section CommMonoid

variable {M ι α : Type _} [CommMonoid M] [MeasurableSpace M] [HasMeasurableMul₂ M]
  {m : MeasurableSpace α} {μ : Measure α} {f : ι → α → M}

include m

@[measurability, to_additive]
theorem Multiset.measurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.Prod := by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod' (by simpa using hl)
#align multiset.measurable_prod' Multiset.measurable_prod'
#align multiset.measurable_sum' Multiset.measurable_sum'

@[measurability, to_additive]
theorem Multiset.aEMeasurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.Prod μ := by
  rcases l with ⟨l⟩
  simpa using l.ae_measurable_prod' (by simpa using hl)
#align multiset.ae_measurable_prod' Multiset.aEMeasurable_prod'
#align multiset.ae_measurable_sum' Multiset.aEMeasurable_sum'

@[measurability, to_additive]
theorem Multiset.measurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).Prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod' hs
#align multiset.measurable_prod Multiset.measurable_prod
#align multiset.measurable_sum Multiset.measurable_sum

@[measurability, to_additive]
theorem Multiset.aEMeasurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α → M => f x).Prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.ae_measurable_prod' hs
#align multiset.ae_measurable_prod Multiset.aEMeasurable_prod
#align multiset.ae_measurable_sum Multiset.aEMeasurable_sum

@[measurability, to_additive]
theorem Finset.measurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf
#align finset.measurable_prod' Finset.measurable_prod'
#align finset.measurable_sum' Finset.measurable_sum'

@[measurability, to_additive]
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a => ∏ i in s, f i a := by
  simpa only [← Finset.prod_apply] using s.measurable_prod' hf
#align finset.measurable_prod Finset.measurable_prod
#align finset.measurable_sum Finset.measurable_sum

@[measurability, to_additive]
theorem Finset.aEMeasurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (∏ i in s, f i) μ :=
  Multiset.aEMeasurable_prod' _ fun g hg =>
    let ⟨i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi
#align finset.ae_measurable_prod' Finset.aEMeasurable_prod'
#align finset.ae_measurable_sum' Finset.aEMeasurable_sum'

@[measurability, to_additive]
theorem Finset.aEMeasurable_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∏ i in s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.ae_measurable_prod' hf
#align finset.ae_measurable_prod Finset.aEMeasurable_prod
#align finset.ae_measurable_sum Finset.aEMeasurable_sum

omit m

end CommMonoid

