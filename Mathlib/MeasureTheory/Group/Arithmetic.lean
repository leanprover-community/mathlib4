/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Measure.AEMeasurable

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

## TODO

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

export MeasurableAdd (measurable_const_add measurable_add_const)

/-- We say that a type has `MeasurableAdd₂` if `uncurry (· + ·)` is a measurable functions.
For a typeclass assuming measurability of `(c + ·)` and `(· + c)` see `MeasurableAdd`. -/
class MeasurableAdd₂ (M : Type*) [MeasurableSpace M] [Add M] : Prop where
  measurable_add : Measurable fun p : M × M => p.1 + p.2

export MeasurableAdd₂ (measurable_add)

/-- We say that a type has `MeasurableMul` if `(c * ·)` and `(· * c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `MeasurableMul₂`. -/
@[to_additive]
class MeasurableMul (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_const_mul : ∀ c : M, Measurable (c * ·)
  measurable_mul_const : ∀ c : M, Measurable (· * c)

export MeasurableMul (measurable_const_mul measurable_mul_const)

/-- We say that a type has `MeasurableMul₂` if `uncurry (· * ·)` is a measurable functions.
For a typeclass assuming measurability of `(c * ·)` and `(· * c)` see `MeasurableMul`. -/
@[to_additive MeasurableAdd₂]
class MeasurableMul₂ (M : Type*) [MeasurableSpace M] [Mul M] : Prop where
  measurable_mul : Measurable fun p : M × M => p.1 * p.2

export MeasurableMul₂ (measurable_mul)

section Mul

variable {M α β : Type*} [MeasurableSpace M] [Mul M] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α → M} {μ : Measure α}

@[to_additive (attr := fun_prop, measurability)]
theorem Measurable.const_mul [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => c * f x :=
  (measurable_const_mul c).comp hf

@[to_additive (attr := fun_prop, measurability)]
theorem AEMeasurable.const_mul [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => c * f x) μ :=
  (MeasurableMul.measurable_const_mul c).comp_aemeasurable hf

@[to_additive (attr := fun_prop, measurability)]
theorem Measurable.mul_const [MeasurableMul M] (hf : Measurable f) (c : M) :
    Measurable fun x => f x * c :=
  (measurable_mul_const c).comp hf

@[to_additive (attr := fun_prop, measurability)]
theorem AEMeasurable.mul_const [MeasurableMul M] (hf : AEMeasurable f μ) (c : M) :
    AEMeasurable (fun x => f x * c) μ :=
  (measurable_mul_const c).comp_aemeasurable hf

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a * g a :=
  measurable_mul.comp (hf.prodMk hg)

/-- Compositional version of `Measurable.mul` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))
/-- Compositional version of `Measurable.add` for use by `fun_prop`. -/]
lemma Measurable.mul' [MeasurableMul₂ M] {f g : α → β → M} {h : α → β} (hf : Measurable ↿f)
    (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a ↦ (f a * g a) (h a) := by
  simp; fun_prop

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.mul' [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f * g) μ :=
  measurable_mul.comp_aemeasurable (hf.prodMk hg)

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.mul [MeasurableMul₂ M] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a * g a) μ :=
  measurable_mul.comp_aemeasurable (hf.prodMk hg)

@[to_additive]
instance (priority := 100) MeasurableMul₂.toMeasurableMul [MeasurableMul₂ M] :
    MeasurableMul M :=
  ⟨fun _ => measurable_const.mul measurable_id, fun _ => measurable_id.mul measurable_const⟩

@[to_additive]
instance Pi.measurableMul {ι : Type*} {α : ι → Type*} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul (α i)] : MeasurableMul (∀ i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_mul _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).mul_const _⟩

@[to_additive Pi.measurableAdd₂]
instance Pi.measurableMul₂ {ι : Type*} {α : ι → Type*} [∀ i, Mul (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableMul₂ (α i)] : MeasurableMul₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.mul measurable_snd.eval⟩

end Mul

/-- A version of `measurable_div_const` that assumes `MeasurableMul` instead of
  `MeasurableDiv`. This can be nice to avoid unnecessary type-class assumptions. -/
@[to_additive /-- A version of `measurable_sub_const` that assumes `MeasurableAdd` instead of
  `MeasurableSub`. This can be nice to avoid unnecessary type-class assumptions. -/]
theorem measurable_div_const' {G : Type*} [DivInvMonoid G] [MeasurableSpace G] [MeasurableMul G]
    (g : G) : Measurable fun h => h / g := by simp_rw [div_eq_mul_inv, measurable_mul_const]

/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class MeasurablePow (β γ : Type*) [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] : Prop where
  measurable_pow : Measurable fun p : β × γ => p.1 ^ p.2

export MeasurablePow (measurable_pow)

/-- `Monoid.Pow` is measurable. -/
instance Monoid.measurablePow (M : Type*) [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurablePow M ℕ :=
  ⟨measurable_from_prod_countable fun n => by
      induction n with
      | zero => simp only [pow_zero, ← Pi.one_def, measurable_one]
      | succ n ih =>
        simp only [pow_succ]
        exact ih.mul measurable_id⟩

section Pow

variable {β γ α : Type*} [MeasurableSpace β] [MeasurableSpace γ] [Pow β γ] [MeasurablePow β γ]
  {m : MeasurableSpace α} {μ : Measure α} {f : α → β} {g : α → γ}

@[aesop safe 20 apply (rule_sets := [Measurable]), fun_prop]
theorem Measurable.pow (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x ^ g x :=
  measurable_pow.comp (hf.prodMk hg)

@[aesop safe 20 apply (rule_sets := [Measurable]), fun_prop]
theorem AEMeasurable.pow (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => f x ^ g x) μ :=
  measurable_pow.comp_aemeasurable (hf.prodMk hg)

@[fun_prop, measurability]
theorem Measurable.pow_const (hf : Measurable f) (c : γ) : Measurable fun x => f x ^ c :=
  hf.pow measurable_const

@[fun_prop, measurability]
theorem AEMeasurable.pow_const (hf : AEMeasurable f μ) (c : γ) :
    AEMeasurable (fun x => f x ^ c) μ :=
  hf.pow aemeasurable_const

@[fun_prop, measurability]
theorem Measurable.const_pow (hg : Measurable g) (c : β) : Measurable fun x => c ^ g x :=
  measurable_const.pow hg

@[fun_prop, measurability]
theorem AEMeasurable.const_pow (hg : AEMeasurable g μ) (c : β) :
    AEMeasurable (fun x => c ^ g x) μ :=
  aemeasurable_const.pow hg

end Pow

/-- We say that a type has `MeasurableSub` if `(c - ·)` and `(· - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `MeasurableSub₂`. -/
class MeasurableSub (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_const_sub : ∀ c : G, Measurable (c - ·)
  measurable_sub_const : ∀ c : G, Measurable (· - c)

export MeasurableSub (measurable_const_sub measurable_sub_const)

/-- We say that a type has `MeasurableSub₂` if `uncurry (· - ·)` is a measurable functions.
For a typeclass assuming measurability of `(c - ·)` and `(· - c)` see `MeasurableSub`. -/
class MeasurableSub₂ (G : Type*) [MeasurableSpace G] [Sub G] : Prop where
  measurable_sub : Measurable fun p : G × G => p.1 - p.2

export MeasurableSub₂ (measurable_sub)

/-- We say that a type has `MeasurableDiv` if `(c / ·)` and `(· / c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (· / ·)` see `MeasurableDiv₂`. -/
@[to_additive]
class MeasurableDiv (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_const_div : ∀ c : G₀, Measurable (c / ·)
  measurable_div_const : ∀ c : G₀, Measurable (· / c)

export MeasurableDiv (measurable_const_div measurable_div_const)

/-- We say that a type has `MeasurableDiv₂` if `uncurry (· / ·)` is a measurable functions.
For a typeclass assuming measurability of `(c / ·)` and `(· / c)` see `MeasurableDiv`. -/
@[to_additive MeasurableSub₂]
class MeasurableDiv₂ (G₀ : Type*) [MeasurableSpace G₀] [Div G₀] : Prop where
  measurable_div : Measurable fun p : G₀ × G₀ => p.1 / p.2

export MeasurableDiv₂ (measurable_div)

section Div

variable {G α β : Type*} [MeasurableSpace G] [Div G] {m : MeasurableSpace α}
  {mβ : MeasurableSpace β} {f g : α → G} {μ : Measure α}

@[to_additive (attr := fun_prop, measurability)]
theorem Measurable.const_div [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => c / f x :=
  (MeasurableDiv.measurable_const_div c).comp hf

@[to_additive (attr := fun_prop, measurability)]
theorem AEMeasurable.const_div [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => c / f x) μ :=
  (MeasurableDiv.measurable_const_div c).comp_aemeasurable hf

@[to_additive (attr := fun_prop, measurability)]
theorem Measurable.div_const [MeasurableDiv G] (hf : Measurable f) (c : G) :
    Measurable fun x => f x / c :=
  (MeasurableDiv.measurable_div_const c).comp hf

@[to_additive (attr := fun_prop, measurability)]
theorem AEMeasurable.div_const [MeasurableDiv G] (hf : AEMeasurable f μ) (c : G) :
    AEMeasurable (fun x => f x / c) μ :=
  (MeasurableDiv.measurable_div_const c).comp_aemeasurable hf

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.div [MeasurableDiv₂ G] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => f a / g a :=
  measurable_div.comp (hf.prodMk hg)

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
lemma Measurable.div' [MeasurableDiv₂ G] {f g : α → β → G} {h : α → β} (hf : Measurable ↿f)
    (hg : Measurable ↿g) (hh : Measurable h) : Measurable fun a ↦ (f a / g a) (h a) := by
  simp; fun_prop

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.div' [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (f / g) μ :=
  measurable_div.comp_aemeasurable (hf.prodMk hg)

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.div [MeasurableDiv₂ G] (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => f a / g a) μ :=
  measurable_div.comp_aemeasurable (hf.prodMk hg)

@[to_additive]
instance (priority := 100) MeasurableDiv₂.toMeasurableDiv [MeasurableDiv₂ G] :
    MeasurableDiv G :=
  ⟨fun _ => measurable_const.div measurable_id, fun _ => measurable_id.div measurable_const⟩

@[to_additive]
instance Pi.measurableDiv {ι : Type*} {α : ι → Type*} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv (α i)] : MeasurableDiv (∀ i, α i) :=
  ⟨fun _ => measurable_pi_iff.mpr fun i => (measurable_pi_apply i).const_div _, fun _ =>
    measurable_pi_iff.mpr fun i => (measurable_pi_apply i).div_const _⟩

@[to_additive Pi.measurableSub₂]
instance Pi.measurableDiv₂ {ι : Type*} {α : ι → Type*} [∀ i, Div (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableDiv₂ (α i)] : MeasurableDiv₂ (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun _ => measurable_fst.eval.div measurable_snd.eval⟩

@[measurability]
theorem measurableSet_eq_fun {m : MeasurableSpace α} {E} [MeasurableSpace E] [AddGroup E]
    [MeasurableSingletonClass E] [MeasurableSub₂ E] {f g : α → E} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { x | f x = g x } := by
  suffices h_set_eq : { x : α | f x = g x } = { x | (f - g) x = (0 : E) } by
    rw [h_set_eq]
    exact (hf.sub hg) measurableSet_eq
  ext
  simp_rw [Set.mem_setOf_eq, Pi.sub_apply, sub_eq_zero]

@[measurability]
lemma measurableSet_eq_fun' {β : Type*} [AddCommMonoid β] [PartialOrder β]
    [CanonicallyOrderedAdd β] [Sub β] [OrderedSub β]
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

theorem ae_eq_trim_of_measurable {α E} {m m0 : MeasurableSpace α} {μ : Measure α}
    [MeasurableSpace E] [AddGroup E] [MeasurableSingletonClass E] [MeasurableSub₂ E]
    (hm : m ≤ m0) {f g : α → E} (hf : Measurable[m] f) (hg : Measurable[m] g) (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.trim hm] g := by
  rwa [Filter.EventuallyEq, ae_iff, trim_measurableSet_eq hm _]
  exact @MeasurableSet.compl α _ m (@measurableSet_eq_fun α m E _ _ _ _ _ _ hf hg)

end Div

/-- We say that a type has `MeasurableNeg` if `x ↦ -x` is a measurable function. -/
class MeasurableNeg (G : Type*) [Neg G] [MeasurableSpace G] : Prop where
  measurable_neg : Measurable (Neg.neg : G → G)

/-- We say that a type has `MeasurableInv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class MeasurableInv (G : Type*) [Inv G] [MeasurableSpace G] : Prop where
  measurable_inv : Measurable (Inv.inv : G → G)

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

section Inv

variable {G α : Type*} [Inv G] [MeasurableSpace G] [MeasurableInv G] {m : MeasurableSpace α}
  {f : α → G} {μ : Measure α}

@[to_additive (attr := fun_prop, measurability)]
theorem Measurable.inv (hf : Measurable f) : Measurable fun x => (f x)⁻¹ :=
  measurable_inv.comp hf

@[to_additive (attr := fun_prop, measurability)]
theorem AEMeasurable.inv (hf : AEMeasurable f μ) : AEMeasurable (fun x => (f x)⁻¹) μ :=
  measurable_inv.comp_aemeasurable hf

@[to_additive (attr := simp)]
theorem measurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : (Measurable fun x => (f x)⁻¹) ↔ Measurable f :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩

@[to_additive (attr := simp)]
theorem aemeasurable_inv_iff {G : Type*} [InvolutiveInv G] [MeasurableSpace G] [MeasurableInv G]
    {f : α → G} : AEMeasurable (fun x => (f x)⁻¹) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [inv_inv] using h.inv, fun h => h.inv⟩

@[deprecated (since := "2025-04-09")]
alias measurable_inv_iff₀ := measurable_inv_iff

@[deprecated (since := "2025-04-09")]
alias aemeasurable_inv_iff₀ := aemeasurable_inv_iff

@[to_additive]
instance Pi.measurableInv {ι : Type*} {α : ι → Type*} [∀ i, Inv (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableInv (α i)] : MeasurableInv (∀ i, α i) :=
  ⟨measurable_pi_iff.mpr fun i => (measurable_pi_apply i).inv⟩

@[to_additive]
theorem MeasurableSet.inv {s : Set G} (hs : MeasurableSet s) : MeasurableSet s⁻¹ :=
  measurable_inv hs

@[to_additive]
theorem measurableEmbedding_inv [InvolutiveInv α] [MeasurableInv α] :
    MeasurableEmbedding (Inv.inv (α := α)) :=
  ⟨inv_injective, measurable_inv, fun s hs ↦ s.image_inv_eq_inv ▸ hs.inv⟩

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
      rcases n with n | n
      · simp_rw [Int.ofNat_eq_coe, zpow_natCast]
        exact measurable_id.pow_const _
      · simp_rw [zpow_negSucc]
        exact (measurable_id.pow_const (n + 1)).inv⟩

@[to_additive]
instance (priority := 100) measurableDiv₂_of_mul_inv (G : Type*) [MeasurableSpace G]
    [DivInvMonoid G] [MeasurableMul₂ G] [MeasurableInv G] : MeasurableDiv₂ G :=
  ⟨by
    simp only [div_eq_mul_inv]
    exact measurable_fst.mul measurable_snd.inv⟩

-- See note [lower instance priority]
instance (priority := 100) MeasurableDiv.toMeasurableInv [MeasurableSpace α] [Group α]
    [MeasurableDiv α] : MeasurableInv α where
  measurable_inv := by simpa using measurable_const_div (1 : α)

/-- We say that the action of `M` on `α` has `MeasurableConstVAdd` if for each `c` the map
`x ↦ c +ᵥ x` is a measurable function. -/
class MeasurableConstVAdd (M α : Type*) [VAdd M α] [MeasurableSpace α] : Prop where
  measurable_const_vadd : ∀ c : M, Measurable (c +ᵥ · : α → α)

/-- We say that the action of `M` on `α` has `MeasurableConstSMul` if for each `c` the map
`x ↦ c • x` is a measurable function. -/
@[to_additive]
class MeasurableConstSMul (M α : Type*) [SMul M α] [MeasurableSpace α] : Prop where
  measurable_const_smul : ∀ c : M, Measurable (c • · : α → α)

/-- We say that the action of `M` on `α` has `MeasurableVAdd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class MeasurableVAdd (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α]
    extends MeasurableConstVAdd M α where
  measurable_vadd_const : ∀ x : α, Measurable (· +ᵥ x : M → α)

/-- We say that the action of `M` on `α` has `MeasurableSMul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class MeasurableSMul (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α]
    extends MeasurableConstSMul M α where
  measurable_smul_const : ∀ x : α, Measurable (· • x : M → α)

/-- We say that the action of `M` on `α` has `MeasurableVAdd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class MeasurableVAdd₂ (M α : Type*) [VAdd M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_vadd : Measurable (Function.uncurry (· +ᵥ ·) : M × α → α)

/-- We say that the action of `M` on `α` has `Measurable_SMul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive MeasurableVAdd₂]
class MeasurableSMul₂ (M α : Type*) [SMul M α] [MeasurableSpace M] [MeasurableSpace α] :
    Prop where
  measurable_smul : Measurable (Function.uncurry (· • ·) : M × α → α)

export MeasurableConstVAdd (measurable_const_vadd)
export MeasurableConstSMul (measurable_const_smul)
export MeasurableVAdd (measurable_vadd_const)
export MeasurableSMul (measurable_smul_const)
export MeasurableSMul₂ (measurable_smul)
export MeasurableVAdd₂ (measurable_vadd)

@[to_additive]
instance measurableSMul_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul M] :
    MeasurableSMul M M where
  measurable_const_smul := measurable_id.const_mul
  measurable_smul_const := measurable_id.mul_const

@[to_additive]
instance measurableSMul₂_of_mul (M : Type*) [Mul M] [MeasurableSpace M] [MeasurableMul₂ M] :
    MeasurableSMul₂ M M :=
  ⟨measurable_mul⟩

@[to_additive]
instance Submonoid.instMeasurableConstSMul {M α} [MeasurableSpace α] [Monoid M] [MulAction M α]
    [MeasurableConstSMul M α] (s : Submonoid M) : MeasurableConstSMul s α where
  measurable_const_smul c := by simpa only using measurable_const_smul (c : M)

@[to_additive]
instance Submonoid.instMeasurableSMul {M α} [MeasurableSpace M] [MeasurableSpace α] [Monoid M]
    [MulAction M α] [MeasurableSMul M α] (s : Submonoid M) : MeasurableSMul s α where
  measurable_smul_const x := (measurable_smul_const (M := M) x).comp measurable_subtype_coe

@[to_additive]
instance Subgroup.instMeasurableConstSMul {G α} [MeasurableSpace α] [Group G] [MulAction G α]
    [MeasurableConstSMul G α] (s : Subgroup G) : MeasurableConstSMul s α :=
  s.toSubmonoid.instMeasurableConstSMul

@[to_additive]
instance Subgroup.instMeasurableSMul {G α} [MeasurableSpace G] [MeasurableSpace α] [Group G]
    [MulAction G α] [MeasurableSMul G α] (s : Subgroup G) : MeasurableSMul s α :=
  s.toSubmonoid.instMeasurableSMul

section SMul
variable {M X α β : Type*} [MeasurableSpace X] [SMul M X]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : α → M} {g : α → X}

section MeasurableConstSMul
variable [MeasurableConstSMul M X]

@[to_additive (attr := fun_prop, measurability)]
lemma Measurable.const_smul (hg : Measurable g) (c : M) : Measurable (c • g) :=
  (measurable_const_smul c).comp hg

/-- Compositional version of `Measurable.const_smul` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Measurable.const_vadd` for use by `fun_prop`. -/]
lemma Measurable.fun_const_smul {g : α → β → X} {h : α → β} (hg : Measurable ↿g) (hh : Measurable h)
    (c : M) : Measurable fun a ↦ (c • g a) (h a) :=
  (hg.comp <| measurable_id.prodMk hh).const_smul _

@[deprecated (since := "2025-04-23")] alias Measurable.const_smul' := Measurable.fun_const_smul

@[to_additive (attr := fun_prop, measurability)]
lemma AEMeasurable.fun_const_smul (hg : AEMeasurable g μ) (c : M) : AEMeasurable (c • g ·) μ :=
  (measurable_const_smul c).comp_aemeasurable hg

@[deprecated (since := "2025-04-23")] alias AEMeasurable.const_smul' := AEMeasurable.fun_const_smul

@[to_additive (attr := fun_prop, measurability)]
lemma AEMeasurable.const_smul (hf : AEMeasurable g μ) (c : M) : AEMeasurable (c • g) μ :=
  hf.fun_const_smul c

@[to_additive]
instance Pi.instMeasurableConstSMul {ι : Type*} {α : ι → Type*} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableConstSMul M (α i)] :
    MeasurableConstSMul M (∀ i, α i) where
  measurable_const_smul _ := measurable_pi_iff.2 fun i ↦ (measurable_pi_apply i).const_smul _

/-- If a scalar is central, then its right action is measurable when its left action is. -/
@[to_additive]
nonrec instance MulOpposite.instMeasurableConstSMul [SMul M α] [SMul Mᵐᵒᵖ α] [IsCentralScalar M α]
    [MeasurableConstSMul M α] : MeasurableConstSMul Mᵐᵒᵖ α where
  measurable_const_smul := by simpa using measurable_const_smul

end MeasurableConstSMul

variable [MeasurableSpace M]

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem Measurable.smul [MeasurableSMul₂ M X] (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => f x • g x :=
  measurable_smul.comp (hf.prodMk hg)

/-- Compositional version of `Measurable.smul` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Measurable.vadd` for use by `fun_prop`. -/]
lemma Measurable.smul' [MeasurableSMul₂ M X] {f : α → β → M} {g : α → β → X} {h : α → β}
    (hf : Measurable ↿f) (hg : Measurable ↿g) (hh : Measurable h) :
    Measurable fun a ↦ (f a • g a) (h a) := by simp; fun_prop

@[to_additive (attr := fun_prop, aesop safe 20 apply (rule_sets := [Measurable]))]
theorem AEMeasurable.smul [MeasurableSMul₂ M X] {μ : Measure α} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun x => f x • g x) μ :=
  MeasurableSMul₂.measurable_smul.comp_aemeasurable (hf.prodMk hg)

@[to_additive]
instance (priority := 100) MeasurableSMul₂.toMeasurableSMul [MeasurableSMul₂ M X] :
    MeasurableSMul M X where
  measurable_const_smul _ := measurable_const.smul measurable_id
  measurable_smul_const _ := measurable_id.smul measurable_const

variable [MeasurableSMul M X]

@[to_additive (attr := fun_prop, measurability)]
theorem Measurable.smul_const (hf : Measurable f) (y : X) : Measurable fun x => f x • y :=
  (MeasurableSMul.measurable_smul_const y).comp hf

@[to_additive (attr := fun_prop, measurability)]
theorem AEMeasurable.smul_const (hf : AEMeasurable f μ) (y : X) :
    AEMeasurable (fun x => f x • y) μ :=
  (MeasurableSMul.measurable_smul_const y).comp_aemeasurable hf

@[to_additive]
instance Pi.measurableSMul {ι : Type*} {α : ι → Type*} [∀ i, SMul M (α i)]
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSMul M (α i)] :
    MeasurableSMul M (∀ i, α i) where
  measurable_smul_const _ := measurable_pi_iff.2 fun _ ↦ measurable_smul_const _

/-- `AddMonoid.SMul` is measurable. -/
instance AddMonoid.measurableSMul_nat₂ (M : Type*) [AddMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] : MeasurableSMul₂ ℕ M :=
  ⟨by
    suffices Measurable fun p : M × ℕ => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable fun n => ?_
    induction n with
    | zero => simp only [zero_smul, ← Pi.zero_def, measurable_zero]
    | succ n ih =>
      simp only [succ_nsmul]
      exact ih.add measurable_id⟩

/-- `SubNegMonoid.SMulInt` is measurable. -/
instance SubNegMonoid.measurableSMul_int₂ (M : Type*) [SubNegMonoid M] [MeasurableSpace M]
    [MeasurableAdd₂ M] [MeasurableNeg M] : MeasurableSMul₂ ℤ M :=
  ⟨by
    suffices Measurable fun p : M × ℤ => p.2 • p.1 by apply this.comp measurable_swap
    refine measurable_from_prod_countable fun n => ?_
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_coe, natCast_zsmul]
      exact measurable_const_smul _
    | negSucc n =>
      simp only [negSucc_zsmul]
      exact (measurable_const_smul _).neg⟩

end SMul

section IterateMulAct

variable {α : Type*} {_ : MeasurableSpace α} {f : α → α}

@[to_additive]
theorem Measurable.measurableSMul₂_iterateMulAct (h : Measurable f) :
    MeasurableSMul₂ (IterateMulAct f) α where
  measurable_smul :=
    suffices Measurable fun p : α × IterateMulAct f ↦ f^[p.2.val] p.1 from this.comp measurable_swap
    measurable_from_prod_countable fun n ↦ h.iterate n.val

@[to_additive (attr := simp)]
theorem measurableSMul_iterateMulAct : MeasurableSMul (IterateMulAct f) α ↔ Measurable f :=
  ⟨fun _ ↦ measurable_const_smul (IterateMulAct.mk (f := f) 1), fun h ↦
    have := h.measurableSMul₂_iterateMulAct; inferInstance⟩

@[to_additive (attr := simp)]
theorem measurableSMul₂_iterateMulAct : MeasurableSMul₂ (IterateMulAct f) α ↔ Measurable f :=
  ⟨fun _ ↦ measurableSMul_iterateMulAct.mp inferInstance,
    Measurable.measurableSMul₂_iterateMulAct⟩

end IterateMulAct

section MulAction
variable {G G₀ M β α : Type*} [MeasurableSpace β] [MeasurableSpace α] {f : α → β} {μ : Measure α}

section Group
variable {G : Type*} [Group G] [MulAction G β] [MeasurableConstSMul G β]

@[to_additive]
theorem measurable_const_smul_iff (c : G) : (Measurable fun x => c • f x) ↔ Measurable f :=
  ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

@[to_additive]
theorem aemeasurable_const_smul_iff (c : G) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa [inv_smul_smul, Pi.smul_def] using h.const_smul c⁻¹, fun h => h.const_smul c⟩

end Group

section Monoid
variable [Monoid M] [MulAction M β]

section MeasurableConstSMul
variable [MeasurableConstSMul M β]

@[to_additive]
instance Units.instMeasurableConstSMul : MeasurableConstSMul Mˣ β where
  measurable_const_smul c := measurable_const_smul (c : M)

@[to_additive]
nonrec theorem IsUnit.measurable_const_smul_iff {c : M} (hc : IsUnit c) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ measurable_const_smul_iff u

@[to_additive]
nonrec theorem IsUnit.aemeasurable_const_smul_iff {c : M} (hc : IsUnit c) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  let ⟨u, hu⟩ := hc
  hu ▸ aemeasurable_const_smul_iff u

end MeasurableConstSMul

section MeasurableSMul
variable [MeasurableSpace M] [MeasurableSMul M β]

@[to_additive]
instance Units.instMeasurableSpace : MeasurableSpace Mˣ := .comap Units.val ‹_›

@[to_additive]
instance Units.measurableSMul : MeasurableSMul Mˣ β where
  measurable_smul_const x :=
    (measurable_smul_const x : Measurable fun c : M => c • x).comp MeasurableSpace.le_map_comap

end MeasurableSMul
end Monoid

section GroupWithZero
variable [GroupWithZero G₀] [MeasurableSpace G₀] [MulAction G₀ β] [MeasurableSMul G₀ β]

theorem measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    (Measurable fun x => c • f x) ↔ Measurable f :=
  (IsUnit.mk0 c hc).measurable_const_smul_iff

theorem aemeasurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
    AEMeasurable (fun x => c • f x) μ ↔ AEMeasurable f μ :=
  (IsUnit.mk0 c hc).aemeasurable_const_smul_iff

end GroupWithZero
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

@[to_additive]
theorem measurable_mul_op {α : Type*} [MeasurableSpace α] : Measurable (op : α → αᵐᵒᵖ) := fun _ =>
  id

@[to_additive]
theorem measurable_mul_unop {α : Type*} [MeasurableSpace α] : Measurable (unop : αᵐᵒᵖ → α) :=
  fun _ => id

@[to_additive]
instance MulOpposite.instMeasurableMul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableMul Mᵐᵒᵖ :=
  ⟨fun _ => measurable_mul_op.comp (measurable_mul_unop.mul_const _), fun _ =>
    measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]
instance MulOpposite.instMeasurableMul₂ {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableMul₂ Mᵐᵒᵖ :=
  ⟨measurable_mul_op.comp
      ((measurable_mul_unop.comp measurable_snd).mul (measurable_mul_unop.comp measurable_fst))⟩

/-- If a scalar is central, then its right action is measurable when its left action is. -/
@[to_additive]
nonrec instance MeasurableSMul.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul M α] : MeasurableSMul Mᵐᵒᵖ α where
  measurable_smul_const x :=
    show Measurable fun c => op (unop c) • x by
      simpa only [op_smul_eq_smul] using (measurable_smul_const x).comp measurable_mul_unop

/-- If a scalar is central, then its right action is measurable when its left action is. -/
nonrec instance MeasurableSMul₂.op {M α} [MeasurableSpace M] [MeasurableSpace α] [SMul M α]
    [SMul Mᵐᵒᵖ α] [IsCentralScalar M α] [MeasurableSMul₂ M α] : MeasurableSMul₂ Mᵐᵒᵖ α :=
  ⟨show Measurable fun x : Mᵐᵒᵖ × α => op (unop x.1) • x.2 by
      simp_rw [op_smul_eq_smul]
      exact (measurable_mul_unop.comp measurable_fst).smul measurable_snd⟩

@[to_additive]
instance measurableSMul_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul M] : MeasurableSMul Mᵐᵒᵖ M where
  measurable_const_smul c := measurable_mul_const (unop c)
  measurable_smul_const x := measurable_mul_unop.const_mul x

@[to_additive]
instance measurableSMul₂_opposite_of_mul {M : Type*} [Mul M] [MeasurableSpace M]
    [MeasurableMul₂ M] : MeasurableSMul₂ Mᵐᵒᵖ M :=
  ⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

end Opposite

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M α : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M] {m : MeasurableSpace α}
  {μ : Measure α}

@[to_additive (attr := measurability, fun_prop)]
theorem List.measurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  induction l with
  | nil => exact measurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[deprecated (since := "2025-05-30")]
alias List.measurable_sum' := List.measurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias List.measurable_prod' := List.measurable_prod

@[to_additive (attr := measurability, fun_prop)]
theorem List.aemeasurable_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  induction l with
  | nil => exact aemeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[deprecated (since := "2025-05-30")]
alias List.aemeasurable_sum' := List.aemeasurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias List.aemeasurable_prod' := List.aemeasurable_prod

@[to_additive (attr := measurability, fun_prop)]
theorem List.measurable_fun_prod (l : List (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable fun x => (l.map fun f : α → M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.measurable_prod hl

@[to_additive (attr := measurability, fun_prop)]
theorem List.aemeasurable_fun_prod (l : List (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable (fun x => (l.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.list_prod_apply] using l.aemeasurable_prod hl

end Monoid

section CommMonoid

variable {M ι α β : Type*} [CommMonoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {m : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α} {f : ι → α → M}

@[to_additive (attr := measurability, fun_prop)]
theorem Multiset.measurable_prod (l : Multiset (α → M)) (hl : ∀ f ∈ l, Measurable f) :
    Measurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.measurable_prod (by simpa using hl)

@[deprecated (since := "2025-05-30")]
alias Multiset.measurable_sum' := Multiset.measurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias Multiset.measurable_prod' := Multiset.measurable_prod

@[to_additive (attr := measurability, fun_prop)]
theorem Multiset.aemeasurable_prod (l : Multiset (α → M)) (hl : ∀ f ∈ l, AEMeasurable f μ) :
    AEMeasurable l.prod μ := by
  rcases l with ⟨l⟩
  simpa using l.aemeasurable_prod (by simpa using hl)

@[deprecated (since := "2025-05-30")]
alias Multiset.aemeasurable_sum' := Multiset.aemeasurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias Multiset.aemeasurable_prod' := Multiset.aemeasurable_prod

@[to_additive (attr := measurability, fun_prop)]
theorem Multiset.measurable_fun_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, Measurable f) :
    Measurable fun x => (s.map fun f : α → M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.measurable_prod hs

@[to_additive (attr := measurability, fun_prop)]
theorem Multiset.aemeasurable_fun_prod (s : Multiset (α → M)) (hs : ∀ f ∈ s, AEMeasurable f μ) :
    AEMeasurable (fun x => (s.map fun f : α → M => f x).prod) μ := by
  simpa only [← Pi.multiset_prod_apply] using s.aemeasurable_prod hs

@[to_additive (attr := measurability, fun_prop)]
theorem Finset.measurable_fun_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a ↦ ∏ i ∈ s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

@[to_additive (attr := measurability, fun_prop)]
theorem Finset.measurable_prod (s : Finset ι) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun a ↦ ∏ i ∈ s, f i a := by
  simp_rw [← Finset.prod_apply]
  exact Finset.prod_induction _ _ (fun _ _ => Measurable.mul) (@measurable_one M _ _ _ _) hf

/-- Compositional version of `Finset.measurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := measurability, fun_prop)
/-- Compositional version of `Finset.measurable_sum` for use by `fun_prop`. -/]
lemma Finset.measurable_prod_apply {f : ι → α → β → M} {g : α → β} {s : Finset ι}
    (hf : ∀ i ∈ s, Measurable ↿(f i)) (hg : Measurable g) :
    Measurable fun a ↦ (∏ i ∈ s, f i a) (g a) := by simp; fun_prop (discharger := assumption)

@[deprecated (since := "2025-05-30")]
alias Finset.measurable_sum' := Finset.measurable_sum_apply
@[to_additive existing, deprecated (since := "2025-05-30")]
alias Finset.measurable_prod' := Finset.measurable_prod_apply

@[to_additive (attr := measurability, fun_prop)]
theorem Finset.aemeasurable_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (∏ i ∈ s, f i) μ :=
  Multiset.aemeasurable_prod _ fun _g hg =>
    let ⟨_i, hi, hg⟩ := Multiset.mem_map.1 hg
    hg ▸ hf _ hi

@[deprecated (since := "2025-05-30")]
alias Finset.aemeasurable_sum' := Finset.aemeasurable_sum
@[to_additive existing, deprecated (since := "2025-05-30")]
alias Finset.aemeasurable_prod' := Finset.aemeasurable_prod

@[to_additive (attr := measurability, fun_prop)]
theorem Finset.aemeasurable_fun_prod (s : Finset ι) (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun a => ∏ i ∈ s, f i a) μ := by
  simpa only [← Finset.prod_apply] using s.aemeasurable_prod hf

end CommMonoid

variable [MeasurableSpace α] [Mul α] [Div α] [Inv α]

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul [DiscreteMeasurableSpace α] :
    MeasurableMul α where
  measurable_const_mul _ := .of_discrete
  measurable_mul_const _ := .of_discrete

@[to_additive DiscreteMeasurableSpace.toMeasurableAdd₂] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableMul₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableMul₂ α := ⟨.of_discrete⟩

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableInv [DiscreteMeasurableSpace α] :
    MeasurableInv α := ⟨.of_discrete⟩

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv [DiscreteMeasurableSpace α] :
    MeasurableDiv α where
  measurable_const_div _ := .of_discrete
  measurable_div_const _ := .of_discrete

@[to_additive DiscreteMeasurableSpace.toMeasurableSub₂] -- See note [lower instance priority]
instance (priority := 100) DiscreteMeasurableSpace.toMeasurableDiv₂
    [DiscreteMeasurableSpace (α × α)] : MeasurableDiv₂ α := ⟨.of_discrete⟩
