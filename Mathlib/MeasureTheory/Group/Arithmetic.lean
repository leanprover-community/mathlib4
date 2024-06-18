/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable

#align_import measure_theory.group.arithmetic from "leanprover-community/mathlib"@"a75898643b2d774cced9ae7c0b28c21663b99666"

/-!
# Typeclasses for measurability of operations

In this file we define classes `MeasurableMul` etc and prove dot-style lemmas
(`Measurable.mul`, `AEMeasurable.mul` etc). For binary operations we define two typeclasses:

- `MeasurableMul` says that both left and right multiplication are measurable;
- `MeasurableMul₂` says that `fun p : α × α => p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `MeasurableMul₂`
etc require `α` to have a second countable topology.

We define separate classes for `MeasurableDiv`/`MeasurableSub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `ContinuousMul` to `MeasurableMul` see file
`MeasureTheory.BorelSpace`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operations) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## Todo

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `MeasurablePow` to `MeasurableSMul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `MeasurableSMul`.)
-/

open MeasureTheory
open scoped Pointwise

universe u v
variable {α : Type*}

/-!
### Binary operations: `(· + ·)`, `(· * ·)`, `(· - ·)`, `(· / ·)`
-/


/-- We say that a type has `MeasurableAdd` if `(· + c)` and `(· + c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· + ·)` see `MeasurableAdd₂`. -/
class MeasurableAdd (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_const_add : ∀ c : M, Measurable (c + ·)
  measurable_add_const : ∀ c : M, Measurable (· + c)
#align has_measurable_add MeasurableAdd
#align has_measurable_add.measurable_const_add MeasurableAdd.measurable_const_add
#align has_measurable_add.measurable_add_const MeasurableAdd.measurable_add_const

export MeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type has `MeasurableAdd₂` if `uncurry (· + ·)` is a measurable functions.
For a typeclass assuming measurability of `(c + ·)` and `(· + c)` see `MeasurableAdd`. -/
class MeasurableAdd₂ (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2
#align has_measurable_add₂ MeasurableAdd₂

export MeasurableAdd₂ (measurable_add)

/-- We say that a type has `MeasurableMul` if `(c * ·)` and `(· * c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `MeasurableMul₂`. -/
@[to_additive]
class MeasurableMul (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable (c * ·)
  measurable_mul_const : ∀ c : M, Measurable (· * c)
#align has_measurable_mul MeasurableMul
#align has_measurable_mul.measurable_const_mul MeasurableMul.measurable_const_mul
#align has_measurable_mul.measurable_mul_const MeasurableMul.measurable_mul_const

export MeasurableMul (measurable_const_mul measurable_mul_const)

/-- We say that a type has `MeasurableMul₂` if `uncurry (· * ·)` is a measurable functions.
For a typeclass assuming measurability of `(c * ·)` and `(· * c)` see `MeasurableMul`. -/
@[to_additive MeasurableAdd₂]
class MeasurableMul₂ (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2
#align has_measurable_mul₂ MeasurableMul₂
#align has_measurable_mul₂.measurable_mul MeasurableMul₂.measurable_mul

export MeasurableMul₂ (measurable_mul)

section Mul

variable {M α : Type*} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α} {f g : α → M}
  {μ : Measure α}

@[to_additive (attr := measurability)]
theorem Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf
#align measurable.const_mul Measurable.const_mul
#align measurable.const_add Measurable.const_add

@[to_additive (attr := measurability)]
theorem AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c * f x) μ :=
  (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf
#align ae_measurable.const_mul AEMeasurable.const_mul
#align ae_measurable.const_add AEMeasurable.const_add

@[to_additive (attr := measurability)]
theorem Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf
#align measurable.mul_const Measurable.mul_const
#align measurable.add_const Measurable.add_const

@[to_additive (attr := measurability)]
theorem AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_aemeasurable hf
#align ae_measurable.mul_const AEMeasurable.mul_const
#align ae_measurable.add_const AEMeasurable.add_const

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.mul' [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f * g) :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul' Measurable.mul'
#align measurable.add' Measurable.add'

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a :=
  measurable_mul.comp (hf.prod_mk hg)
#align measurable.mul Measurable.mul
#align measurable.add Measurable.add

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.mul' [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f * g) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul' AEMeasurable.mul'
#align ae_measurable.add' AEMeasurable.add'

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a * g a) μ :=
  measurable_mul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.mul AEMeasurable.mul
#align ae_measurable.add AEMeasurable.add

@[to_additive]
instance (priority := 100) MeasurableMul₂.toMeasurableMul [MeasurableMul₂ M] :
    MeasurableMul M :=
  ⟨fun _ => measurable_const.mul measurable_id, fun _ => measurable_id.mul measurable_const⟩
#align has_measurable_mul₂.to_has_measurable_mul MeasurableMul₂.toMeasurableMul
#align has_measurable_add₂.to_has_measurable_add MeasurableAdd₂.toMeasurableAdd

@[to_additive]
instance Pi.measurableMul {ι : Type*} {α : ι → Type*} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul (α i)] : MeasurableMul (∀ i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩
#align pi.has_measurable_mul Pi.measurableMul
#align pi.has_measurable_add Pi.measurableAdd

@[to_additive Pi.measurableAdd₂]
instance Pi.measurableMul₂ {ι : Type*} {α : ι → Type*} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul₂ (α i)] : MeasurableMul₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.mul measurable_snd.eval⟩
#align pi.has_measurable_mul₂ Pi.measurableMul₂
#align pi.has_measurable_add₂ Pi.measurableAdd₂

end Mul

/-- A version of `measurable_div_const` that assumes `MeasurableMul` instead of
  `MeasurableDiv`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive " A version of `measurable_sub_const` that assumes `MeasurableAdd` instead of
  `MeasurableSub`. This can be nice to avoid unnecessary type-class assumptions. "]
theorem measurable_div_const' {G : Type*} [DivInvMonoid G] [MeasurableSpace G] [MeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]
#align measurable_div_const' measurable_div_const'
#align measurable_sub_const' measurable_sub_const'

/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class MeasurablePow (β γ : Type*) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] : Prop where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2
#align has_measurable_pow MeasurablePow

export MeasurablePow (measurable_pow)

/-- `Monoid.Pow` is measurable. -/
instance Monoid.measurablePow (M : Type*) [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurablePow M ℕ :=
  ⟨measurable_from_prod_countable fun n => by
      induction' n with n ih
      · simp only [Nat.zero_eq, pow_zero, ← Pi.one_def, measurable_one]
      · simp only [pow_succ]
        exact ih.mul measurable_id⟩
#align monoid.has_measurable_pow Monoid.measurablePow

section Pow

variable {β γ α : Type*} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [MeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}

@[aesop safe 20 apply (rule_sets := [Measurable])]
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prod_mk hg)
#align measurable.pow Measurable.pow

@[aesop safe 20 apply (rule_sets := [Measurable])]
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

end Pow

/-- We say that a type has `MeasurableSub` if `(c - ·)` and `(· - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `MeasurableSub₂`. -/
class MeasurableSub (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : ∀ c : G, Measurable (c - ·)
  measurable_sub_const : ∀ c : G, Measurable (· - c)
#align has_measurable_sub MeasurableSub
#align has_measurable_sub.measurable_const_sub MeasurableSub.measurable_const_sub
#align has_measurable_sub.measurable_sub_const MeasurableSub.measurable_sub_const

export MeasurableSub (measurable_const_sub measurable_sub_const)

/-- We say that a type has `MeasurableSub₂` if `uncurry (· - ·)` is a measurable functions.
For a typeclass assuming measurability of `(c - ·)` and `(· - c)` see `MeasurableSub`. -/
class MeasurableSub₂ (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2
#align has_measurable_sub₂ MeasurableSub₂
#align has_measurable_sub₂.measurable_sub MeasurableSub₂.measurable_sub

export MeasurableSub₂ (measurable_sub)

/-- We say that a type has `MeasurableDiv` if `(c / ·)` and `(· / c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· / ·)` see `MeasurableDiv₂`. -/
@[to_additive]
class MeasurableDiv (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_const_div : ∀ c : G₀, Measurable (c / ·)
  measurable_div_const : ∀ c : G₀, Measurable (· / c)
#align has_measurable_div MeasurableDiv
#align has_measurable_div.measurable_const_div MeasurableDiv.measurable_div_const
#align has_measurable_div.measurable_div_const MeasurableDiv.measurable_div_const

export MeasurableDiv (measurable_const_div measurable_div_const)

/-- We say that a type has `MeasurableDiv₂` if `uncurry (· / ·)` is a measurable functions.
For a typeclass assuming measurability of `(c / ·)` and `(· / c)` see `MeasurableDiv`. -/
@[to_additive MeasurableSub₂]
class MeasurableDiv₂ (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2
#align has_measurable_div₂ MeasurableDiv₂
#align has_measurable_div₂.measurable_div MeasurableDiv₂.measurable_div

export MeasurableDiv₂ (measurable_div)

section Div

variable {G α : Type*} [MeasurableSpace G] [Div G] {m : MeasurableSpace α} {f g : α → G}
  {μ : Measure α}

@[to_additive (attr := measurability)]
theorem Measurable.const_div [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (MeasurableDiv.measurable_const_div c).comp hf
#align measurable.const_div Measurable.const_div
#align measurable.const_sub Measurable.const_sub

@[to_additive (attr := measurability)]
theorem AEMeasurable.const_div [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => c / f x) μ :=
  (MeasurableDiv.measurable_const_div c).comp_aemeasurable hf
#align ae_measurable.const_div AEMeasurable.const_div
#align ae_measurable.const_sub AEMeasurable.const_sub

@[to_additive (attr := measurability)]
theorem Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (MeasurableDiv.measurable_div_const c).comp hf
#align measurable.div_const Measurable.div_const
#align measurable.sub_const Measurable.sub_const

@[to_additive (attr := measurability)]
theorem AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => f x / c) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf
#align ae_measurable.div_const AEMeasurable.div_const
#align ae_measurable.sub_const AEMeasurable.sub_const

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.div' [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable (f / g) :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div' Measurable.div'
#align measurable.sub' Measurable.sub'

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a / g a :=
  measurable_div.comp (hf.prod_mk hg)
#align measurable.div Measurable.div
#align measurable.sub Measurable.sub

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.div' [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f / g) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div' AEMeasurable.div'
#align ae_measurable.sub' AEMeasurable.sub'

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.div [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a / g a) μ :=
  measurable_div.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.div AEMeasurable.div
#align ae_measurable.sub AEMeasurable.sub

@[to_additive]
instance (priority := 100) MeasurableDiv₂.toMeasurableDiv [MeasurableDiv₂ G] :
    MeasurableDiv G :=
  ⟨fun _ => measurable_const.div measurable_id, fun _ => measurable_id.div measurable_const⟩
#align has_measurable_div₂.to_has_measurable_div MeasurableDiv₂.toMeasurableDiv
#align has_measurable_sub₂.to_has_measurable_sub MeasurableSub₂.toMeasurableSub

@[to_additive]
instance Pi.measurableDiv {ι : Type*} {α : ι → Type*} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv (α i)] : MeasurableDiv (∀ i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩
#align pi.has_measurable_div Pi.measurableDiv
#align pi.has_measurable_sub Pi.measurableSub

@[to_additive Pi.measurableSub₂]
instance Pi.measurableDiv₂ {ι : Type*} {α : ι → Type*} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv₂ (α i)] : MeasurableDiv₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.div measurable_snd.eval⟩
#align pi.has_measurable_div₂ Pi.measurableDiv₂
#align pi.has_measurable_sub₂ Pi.measurableSub₂

@[measurability]
theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [MeasurableSpace E] [AddGroup E]
    [MeasurableSingletonClass E] [MeasurableSub₂ E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } := by
  suffices h_set_eq : { x : α | f x = g x } = { x | (f - g) x = (0 : E) } by
    rw [h_set_eq]
    exact (hf.sub hg) measurableSet_eq
  ext
  simp_rw [Set.mem_setOf_eq, Pi.sub_apply, sub_eq_zero]
#align measurable_set_eq_fun measurableSet_eq_fun

@[measurability]
lemma measurableSet_eq_fun' {β : Type*} [CanonicallyOrderedAddCommMonoid β] [Sub β] [OrderedSub β]
    {_ : MeasurableSpace β} [MeasurableSub₂ β] [MeasurableSingletonClass β]
    {f g : α → β} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x | f x = g x} := by
  have : {a | f a = g a} = {a | (f - g) a = 0} ∩ {a | (g - f) a = 0} := by
    ext
    simp only [Set.mem_setOf_eq, Pi.sub_apply, tsub_eq_zero_iff_le, Set.mem_inter_iff]
    exact ⟨fun h ↦ ⟨h.le, h.symm.le⟩, fun h ↦ le_antisymm h.1 h.2⟩
  rw [this]
  exact ((hf.sub hg) (measurableSet_singleton 0)).inter ((hg.sub hf) (measurableSet_singleton 0))

theorem nullMeasurableSet_eq_fun {E} [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E]
    [MeasurableSub₂ E] {f g : α → E} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    NullMeasurableSet { x | f x = g x } μ := by
  apply (measurableSet_eq_fun hf.measurable_mk hg.measurable_mk).nullMeasurableSet.congr
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk] with x hfx hgx
  change (hf.mk f x = hg.mk g x) = (f x = g x)
  simp only [hfx, hgx]
#align null_measurable_set_eq_fun nullMeasurableSet_eq_fun

theorem measurableSet_eq_fun_of_countable {m : MeasurableSpace α} {E} [MeasurableSpace E]
    [MeasurableSingletonClass E] [Countable E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } := by
  have : { x | f x = g x } = ⋃ j, { x | f x = j } ∩ { x | g x = j } := by
    ext1 x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_eq_right']
  rw [this]
  refine MeasurableSet.iUnion fun j => MeasurableSet.inter ?_ ?_
  · exact hf (measurableSet_singleton j)
  · exact hg (measurableSet_singleton j)
#align measurable_set_eq_fun_of_countable measurableSet_eq_fun_of_countable

theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [MeasurableSub₂ E]
    (hm : m ≤ m0) {f g : α → E} (hf : Measurable[m] f) (hg : Measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.trim hm] g := by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurableSet_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurableSet_eq_fun α m E _ _ _ _ _ _ hf hg)
#align ae_eq_trim_of_measurable ae_eq_trim_of_measurable

end Div

/-- We say that a type has `MeasurableNeg` if `x ↦ -x` is a measurable function. -/
class MeasurableNeg (G : Type*) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G → G)
#align has_measurable_neg MeasurableNeg
#align has_measurable_neg.measurable_neg MeasurableNeg.measurable_neg

/-- We say that a type has `MeasurableInv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class MeasurableInv (G : Type*) [Inv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (Inv.inv : G → G)
#align has_measurable_inv MeasurableInv
#align has_measurable_inv.measurable_inv MeasurableInv.measurable_inv

export MeasurableInv (measurable_inv)

export MeasurableNeg (measurable_neg)

@[to_additive]
instance (priority := 100) measurableDiv_of_mul_inv (G : Type*) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul G] [MeasurableInv G] : MeasurableDiv G where
  measurable_const_div c := by
    convert measurable_inv.const_mul c using 1
    ext1
    apply div_eq_mul_inv
  measurable_div_const c := by
    convert measurable_id.mul_const c⁻¹ using 1
    ext1
    apply div_eq_mul_inv
#align has_measurable_div_of_mul_inv measurableDiv_of_mul_inv
#align has_measurable_sub_of_add_neg measurableSub_of_add_neg

section Inv

variable {G α : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}

@[to_additive (attr := measurability)]
theorem Measurable.inv (hf : Measurable f) : Measurable fun x => (f x)⁻¹ :=
  measurable_inv.comp hf
#align measurable.inv Measurable.inv
#align measurable.neg Measurable.neg

@[to_additive (attr := measurability)]
theorem AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurable (fun x => (f x)⁻¹) μ :=
  measurable_inv.comp_aemeasurable hf
#align ae_measurable.inv AEMeasurable.inv
#align ae_measurable.neg AEMeasurable.neg

@[to_additive (attr := simp)]
theorem measurable_inv_iff {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff measurable_inv_iff
#align measurable_neg_iff measurable_neg_iff

@[to_additive (attr := simp)]
theorem aemeasurable_inv_iff {G : Type*} [Group G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff aemeasurable_inv_iff
#align ae_measurable_neg_iff aemeasurable_neg_iff

@[simp]
theorem measurable_inv_iff₀ {G₀ : Type*} [GroupWithZero G₀] [MeasurableSpace G₀]
    [MeasurableInv G₀] {f : α → G₀} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align measurable_inv_iff₀ measurable_inv_iff₀

@[simp]
theorem aemeasurable_inv_iff₀ {G₀ : Type*} [GroupWithZero G₀] [MeasurableSpace G₀]
    [MeasurableInv G₀] {f : α → G₀} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩
#align ae_measurable_inv_iff₀ aemeasurable_inv_iff₀

@[to_additive]
instance Pi.measurableInv {ι : Type*} {α : ι → Type*} [∀ i, Inv (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableInv (α i)] : MeasurableInv (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩
#align pi.has_measurable_inv Pi.measurableInv
#align pi.has_measurable_neg Pi.measurableNeg

@[to_additive]
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurable_inv hs
#align measurable_set.inv MeasurableSet.inv
#align measurable_set.neg MeasurableSet.neg

@[to_additive]
theorem measurableEmbedding_inv [InvolutiveInv α] [MeasurableInv α] :
    MeasurableEmbedding (Inv.inv (α := α)) :=
  ⟨inv_injective, measurable_inv, fun s hs ↦ s.image_inv ▸ hs.inv⟩

end Inv

@[to_additive]
theorem Measurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {f g : α → G} (hf : Measurable f) :
    Measurable (f * g) ↔ Measurable g :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
theorem AEMeasurable.mul_iff_right {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α → G} (hf : AEMeasurable f μ) :
    AEMeasurable (f * g) μ ↔ AEMeasurable g μ :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive]
theorem Measurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {f g : α → G} (hf : Measurable f) :
    Measurable (g * f) ↔ Measurable g :=
  mul_comm g f ▸ Measurable.mul_iff_right hf

@[to_additive]
theorem AEMeasurable.mul_iff_left {G : Type*} [MeasurableSpace G] [MeasurableSpace α] [CommGroup G]
    [MeasurableMul₂ G] [MeasurableInv G] {μ : Measure α} {f g : α → G} (hf : AEMeasurable f μ) :
    AEMeasurable (g * f) μ ↔ AEMeasurable g μ :=
  mul_comm g f ▸ AEMeasurable.mul_iff_right hf

/-- `DivInvMonoid.Pow` is measurable. -/
instance DivInvMonoid.measurableZPow (G : Type u) [DivInvMonoid G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] : MeasurablePow G ℤ :=
  ⟨measurable_from_prod_countable fun n => by
      cases' n with n n
      · simp_rw [Int.ofNat_eq_coe, zpow_natCast]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩
#align div_inv_monoid.has_measurable_zpow DivInvMonoid.measurableZPow

@[to_additive]
instance (priority := 100) measurableDiv₂_of_mul_inv (G : Type*) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G] : MeasurableDiv₂ G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩
#align has_measurable_div₂_of_mul_inv measurableDiv₂_of_mul_inv
#align has_measurable_div₂_of_add_neg measurableDiv₂_of_add_neg

-- See note [lower instance priority]
instance (priority := 100) MeasurableDiv.toMeasurableInv [MeasurableSpace α] [Group α]
    [MeasurableDiv α] : MeasurableInv α where
  measurable_inv := by simpa using measurable_const_div (1 : α)

/-- We say that the action of `M` on `α` has `MeasurableVAdd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class MeasurableVAdd (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_const_vadd : ∀ c : M, Measurable (c +ᵥ · : α → α)
  measurable_vadd_const : ∀ x : α, Measurable (· +ᵥ x : M → α)
#align has_measurable_vadd MeasurableVAdd
#align has_measurable_vadd.measurable_const_vadd MeasurableVAdd.measurable_const_vadd
#align has_measurable_vadd.measurable_vadd_const MeasurableVAdd.measurable_vadd_const

/-- We say that the action of `M` on `α` has `MeasurableSMul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class MeasurableSMul (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_const_smul : ∀ c : M, Measurable (c • · : α → α)
  measurable_smul_const : ∀ x : α, Measurable (· • x : M → α)
#align has_measurable_smul MeasurableSMul
#align has_measurable_smul.measurable_const_smul MeasurableSMul.measurable_const_smul
#align has_measurable_smul.measurable_smul_const MeasurableSMul.measurable_smul_const

/-- We say that the action of `M` on `α` has `MeasurableVAdd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class MeasurableVAdd₂ (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)
#align has_measurable_vadd₂ MeasurableVAdd₂
#align has_measurable_vadd₂.measurable_vadd MeasurableVAdd₂.measurable_vadd

/-- We say that the action of `M` on `α` has `Measurable_SMul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive MeasurableVAdd₂]
class MeasurableSMul₂ (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α → α)
#align has_measurable_smul₂ MeasurableSMul₂
#align has_measurable_smul₂.measurable_smul MeasurableSMul₂.measurable_smul

export MeasurableSMul (measurable_const_smul measurable_smul_const)

export MeasurableSMul₂ (measurable_smul)

export MeasurableVAdd (measurable_const_vadd measurable_vadd_const)

export MeasurableVAdd₂ (measurable_vadd)

@[to_additive]
instance measurableSMul_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul M] :
    MeasurableSMul M M :=
  ⟨measurable_id.const_mul, measurable_id.mul_const⟩
#align has_measurable_smul_of_mul measurableSMul_of_mul
#align has_measurable_vadd_of_add measurableVAdd_of_add

@[to_additive]
instance measurableSMul₂_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurableSMul₂ M M :=
  ⟨measurable_mul⟩
#align has_measurable_smul₂_of_mul measurableSMul₂_of_mul
#align has_measurable_smul₂_of_add measurableSMul₂_of_add

@[to_additive]
instance Submonoid.measurableSMul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [MeasurableSMul M α] (s : Submonoid M) : MeasurableSMul s α :=
  ⟨fun c => by simpa only using measurable_const_smul (c : M), fun x =>
    (measurable_smul_const x : Measurable fun c : M => c • x).comp measurable_subtype_coe⟩
#align submonoid.has_measurable_smul Submonoid.measurableSMul
#align add_submonoid.has_measurable_vadd AddSubmonoid.measurableVAdd

@[to_additive]
instance Subgroup.measurableSMul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [MeasurableSMul G α] (s : Subgroup G) : MeasurableSMul s α :=
  s.toSubmonoid.measurableSMul
#align subgroup.has_measurable_smul Subgroup.measurableSMul
#align add_subgroup.has_measurable_vadd AddSubgroup.measurableVAdd

section SMul

variable {M β α : Type*} [MeasurableSpace M] [MeasurableSpace β] [_root_.SMul M β]
  {m : MeasurableSpace α} {f : α → M} {g : α → β}

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.smul [MeasurableSMul₂ M β] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurable_smul.comp (hf.prod_mk hg)
#align measurable.smul Measurable.smul
#align measurable.vadd Measurable.vadd

@[to_additive (attr := aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.smul [MeasurableSMul₂ M β] {μ : Measure α} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun x => f x • g x) μ :=
  MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prod_mk hg)
#align ae_measurable.smul AEMeasurable.smul
#align ae_measurable.vadd AEMeasurable.vadd

@[to_additive]
instance (priority := 100) MeasurableSMul₂.toMeasurableSMul [MeasurableSMul₂ M β] :
    MeasurableSMul M β :=
  ⟨fun _ => measurable_const.smul measurable_id, fun _ => measurable_id.smul measurable_const⟩
#align has_measurable_smul₂.to_has_measurable_smul MeasurableSMul₂.toMeasurableSMul
#align has_measurable_vadd₂.to_has_measurable_vadd MeasurableVAdd₂.toMeasurableVAdd

variable [MeasurableSMul M β] {μ : Measure α}

@[to_additive (attr := measurability)]
theorem Measurable.smul_const (hf : Measurable f) (y : β) : Measurable fun x => f x • y :=
  (MeasurableSMul.measurable_smul_const y).comp hf
#align measurable.smul_const Measurable.smul_const
#align measurable.vadd_const Measurable.vadd_const

@[to_additive (attr := measurability)]
theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : β) :
    AEMeasurable (fun x => f x • y) μ :=
  (MeasurableSMul.measurable_smul_const y).comp_aemeasurable hf
#align ae_measurable.smul_const AEMeasurable.smul_const
#align ae_measurable.vadd_const AEMeasurable.vadd_const

@[to_additive (attr := measurability)]
theorem Measurable.const_smul' (hg : Measurable g) (c : M) : Measurable fun x => c • g x :=
  (MeasurableSMul.measurable_const_smul c).comp hg
#align measurable.const_smul' Measurable.const_smul'
#align measurable.const_vadd' Measurable.const_vadd'

@[to_additive (attr := measurability)]
theorem Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  hg.const_smul' c
#align measurable.const_smul Measurable.const_smul
#align measurable.const_vadd Measurable.const_vadd

@[to_additive (attr := measurability)]
theorem AEMeasurable.const_smul' (hg : AEMeasurable g μ) (c : M) :
    AEMeasurable (fun x => c • g x) μ :=
  (MeasurableSMul.measurable_const_smul c).comp_aemeasurable hg
#align ae_measurable.const_smul' AEMeasurable.const_smul'
#align ae_measurable.const_vadd' AEMeasurable.const_vadd'

@[to_additive (attr := measurability)]
theorem AEMeasurable.const_smul (hf : AEMeasurable g μ) (c : M) : AEMeasurable (c • g) μ :=
  hf.const_smul' c
#align ae_measurable.const_smul AEMeasurable.const_smul
#align ae_measurable.const_vadd AEMeasurable.const_vadd

@[to_additive]
instance Pi.measurableSMul {ι : Type*} {α : ι → Type*} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSMul M (α i)] :
    MeasurableSMul M (∀ i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_smul _, fun _ =>
    measurable_pi_iff.mpr fun _ => measurable_smul_const _⟩
#align pi.has_measurable_smul Pi.measurableSMul
#align pi.has_measurable_vadd Pi.measurableVAdd

/-- `AddMonoid.SMul` is measurable. -/
instance AddMonoid.measurableSMul_nat₂ (M : Type*) [AddMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] : MeasurableSMul₂ ℕ M :=
  ⟨by
    suffices Measurable fun p : M × ℕ => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable fun n => ?_
    induction' n with n ih
    · simp only [Nat.zero_eq, zero_smul, ← Pi.zero_def, measurable_zero]
    · simp only [succ_nsmul]
      exact ih.add measurable_id⟩
#align add_monoid.has_measurable_smul_nat₂ AddMonoid.measurableSMul_nat₂

/-- `SubNegMonoid.SMulInt` is measurable. -/
instance SubNegMonoid.measurableSMul_int₂ (M : Type*) [SubNegMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] [MeasurableNeg M] : MeasurableSMul₂ ℤ M :=
  ⟨by
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable fun n => ?_
    induction' n with n n ih
    · simp only [Int.ofNat_eq_coe, natCast_zsmul]
      exact measurable_const_smul _
    · simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩
#align sub_neg_monoid.has_measurable_smul_int₂ SubNegMonoid.measurableSMul_int₂

end SMul

section MulAction

variable {M β α : Type*} [MeasurableSpace M] [MeasurableSpace β] [Monoid M] [MulAction M β]
  [MeasurableSMul M β] [MeasurableSpace α] {f : α → β} {μ : Measure α}

variable {G : Type*} [Group G] [MeasurableSpace G] [MulAction G β] [MeasurableSMul G β]

@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align measurable_const_smul_iff measurable_const_smul_iff
#align measurable_const_vadd_iff measurable_const_vadd_iff

@[to_additive]
theorem aemeasurable_const_smul_iff (c : G) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, fun h => h.const_smul c⟩
#align ae_measurable_const_smul_iff aemeasurable_const_smul_iff
#align ae_measurable_const_vadd_iff aemeasurable_const_vadd_iff

@[to_additive]
instance Units.instMeasurableSpace : MeasurableSpace Mˣ := MeasurableSpace.comap ((↑) : Mˣ → M) ‹_›
#align units.measurable_space Units.instMeasurableSpace
#align add_units.measurable_space AddUnits.instMeasurableSpace

@[to_additive]
instance Units.measurableSMul : MeasurableSMul Mˣ β where
  measurable_const_smul c := (measurable_const_smul (c : M) : _)
  measurable_smul_const x :=
    (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap
#align units.has_measurable_smul Units.measurableSMul
#align add_units.has_measurable_vadd AddUnits.measurableVAdd

@[to_additive]
nonrec theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u
#align is_unit.measurable_const_smul_iff IsUnit.measurable_const_smul_iff
#align is_add_unit.measurable_const_vadd_iff IsAddUnit.measurable_const_vadd_iff

@[to_additive]
nonrec theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u
#align is_unit.ae_measurable_const_smul_iff IsUnit.aemeasurable_const_smul_iff
#align is_add_unit.ae_measurable_const_vadd_iff IsAddUnit.aemeasurable_const_vadd_iff

variable {G₀ : Type*} [GroupWithZero G₀] [MeasurableSpace G₀] [MulAction G₀ β]
  [MeasurableSMul G₀ β]

theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff
#align measurable_const_smul_iff₀ measurable_const_smul_iff₀

theorem aemeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  (IsUnit.mk0 c hc).aemeasurable_const_smul_iff
#align ae_measurable_const_smul_iff₀ aemeasurable_const_smul_iff₀

end MulAction

/-!
### Opposite monoid
-/


section Opposite

open MulOpposite

@[to_additive]
instance MulOpposite.instMeasurableSpace {α : Type*} [h : MeasurableSpace α] :
    MeasurableSpace αᵐᵒᵖ :=
  MeasurableSpace.map op h
#align mul_opposite.measurable_space MulOpposite.instMeasurableSpace
#align add_opposite.measurable_space AddOpposite.instMeasurableSpace

@[to_additive]
theorem measurable_mul_op {α : Type*} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun _ =>
  id
#align measurable_mul_op measurable_mul_op
#align measurable_add_op measurable_add_op

@[to_additive]
theorem measurable_mul_unop {α : Type*} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) :=
  fun _ => id
#align measurable_mul_unop measurable_mul_unop
#align measurable_add_unop measurable_add_unop

@[to_additive]
instance MulOpposite.instMeasurableMul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableMul Mᵐᵒᵖ :=
  ⟨fun _ => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun _ =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩
#align mul_opposite.has_measurable_mul MulOpposite.instMeasurableMul
#align add_opposite.has_measurable_add AddOpposite.instMeasurableAdd

@[to_additive]
instance MulOpposite.instMeasurableMul₂ {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩
#align mul_opposite.has_measurable_mul₂ MulOpposite.instMeasurableMul₂
#align add_opposite.has_measurable_mul₂ AddOpposite.instMeasurableMul₂

/-- If a scalar is central, then its right action is measurable when its left action is. -/
nonrec instance MeasurableSMul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul M α] : MeasurableSMul Mᵐᵒᵖ α :=
  ⟨MulOpposite.rec' fun c =>
      show Measurable fun x => op c • x by
        simpa only [op_smul_eq_smul] using measurable_const_smul c,
    fun x =>
    show Measurable fun c => op (unop c) • x by
      simpa only [op_smul_eq_smul] using (measurable_smul_const x).comp measurable_mul_unop⟩
#align has_measurable_smul.op MeasurableSMul.op

/-- If a scalar is central, then its right action is measurable when its left action is. -/
nonrec instance MeasurableSMul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul₂ M α] : MeasurableSMul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2 by
      simp_rw [op_smul_eq_smul]
      exact (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩
#align has_measurable_smul₂.op MeasurableSMul₂.op

@[to_additive]
instance measurableSMul_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableSMul Mᵐᵒᵖ M :=
  ⟨fun c => measurable_mul_const (unop c), fun x => measurable_mul_unop.const_mul x⟩
#align has_measurable_smul_opposite_of_mul measurableSMul_opposite_of_mul
#align has_measurable_vadd_opposite_of_add measurableVAdd_opposite_of_add

@[to_additive]
instance measurableSMul₂_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableSMul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩
#align has_measurable_smul₂_opposite_of_mul measurableSMul₂_opposite_of_mul
#align has_measurable_smul₂_opposite_of_add measurableSMul₂_opposite_of_add

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

@[to_additive (attr := measurability)]
theorem List.measurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  induction' l with f l ihl; · exact measurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.measurable_prod' List.measurable_prod'
#align list.measurable_sum' List.measurable_sum'

@[to_additive (attr := measurability)]
theorem List.aemeasurable_prod' (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  induction' l with f l ihl; · exact aemeasurable_one
  rw [List.forall_mem_cons] at hl
  rw [List.prod_cons]
  exact hl.1.mul (ihl hl.2)
#align list.ae_measurable_prod' List.aemeasurable_prod'
#align list.ae_measurable_sum' List.aemeasurable_sum'

@[to_additive (attr := measurability)]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod' hl
#align list.measurable_prod List.measurable_prod
#align list.measurable_sum List.measurable_sum

@[to_additive (attr := measurability)]
theorem List.aemeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aemeasurable_prod' hl
#align list.ae_measurable_prod List.aemeasurable_prod
#align list.ae_measurable_sum List.aemeasurable_sum

end Monoid

section CommMonoid

variable {M ι α : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {μ : Measure α} {f : ι → α → M}

@[to_additive (attr := measurability)]
theorem Multiset.measurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod' (by simpa using hl)
#align multiset.measurable_prod' Multiset.measurable_prod'
#align multiset.measurable_sum' Multiset.measurable_sum'

@[to_additive (attr := measurability)]
theorem Multiset.aemeasurable_prod' (l : Multiset (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aemeasurable_prod' (by simpa using hl)
#align multiset.ae_measurable_prod' Multiset.aemeasurable_prod'
#align multiset.ae_measurable_sum' Multiset.aemeasurable_sum'

@[to_additive (attr := measurability)]
theorem Multiset.measurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod' hs
#align multiset.measurable_prod Multiset.measurable_prod
#align multiset.measurable_sum Multiset.measurable_sum

@[to_additive (attr := measurability)]
theorem Multiset.aemeasurable_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aemeasurable_prod' hs
#align multiset.ae_measurable_prod Multiset.aemeasurable_prod
#align multiset.ae_measurable_sum Multiset.aemeasurable_sum

@[to_additive (attr := measurability)]
theorem Finset.measurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∏ i ∈ s, f i) :=
  Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf
#align finset.measurable_prod' Finset.measurable_prod'
#align finset.measurable_sum' Finset.measurable_sum'

@[to_additive (attr := measurability)]
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a => ∏ i ∈ s, f i a := by
  simpa only [← Finset.prod_apply] using s.measurable_prod' hf
#align finset.measurable_prod Finset.measurable_prod
#align finset.measurable_sum Finset.measurable_sum

@[to_additive (attr := measurability)]
theorem Finset.aemeasurable_prod' (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (∏ i ∈ s, f i) μ :=
  Multiset.aemeasurable_prod' _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi
#align finset.ae_measurable_prod' Finset.aemeasurable_prod'
#align finset.ae_measurable_sum' Finset.aemeasurable_sum'

@[to_additive (attr := measurability)]
theorem Finset.aemeasurable_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∏ i ∈ s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aemeasurable_prod' hf
#align finset.ae_measurable_prod Finset.aemeasurable_prod
#align finset.ae_measurable_sum Finset.aemeasurable_sum

end CommMonoid

variable [MeasurableSpace α] [Mul α] [Div α] [Inv α]

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul [DiscreteMeasurableSpace α] :
    MeasurableMul α where
  measurable_const_mul _ := measurable_discrete _
  measurable_mul_const _ := measurable_discrete _

@[to_additive DiscreteMeasurableSpace.toMeasurableAdd₂] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableMul₂ α := ⟨measurable_discrete _⟩

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableInv [DiscreteMeasurableSpace α] :
    MeasurableInv α := ⟨measurable_discrete _⟩

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv [DiscreteMeasurableSpace α] :
    MeasurableDiv α where
  measurable_const_div _ := measurable_discrete _
  measurable_div_const _ := measurable_discrete _

@[to_additive DiscreteMeasurableSpace.toMeasurableSub₂] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableDiv₂ α := ⟨measurable_discrete _⟩
