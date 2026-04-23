/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Metrizable.Real

/-!

# Almost everywhere equal functions

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `Mathlib/MeasureTheory/Function/L1Space/AEEqFun.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` is a measurable space, `β` is a topological
  space, and `μ` is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`.
  In comments, `[f]` is also used to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.

## Main statements

* The linear structure of `L⁰` :
  Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
  `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
  of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

  See `mk_add_mk`, `neg_mk`, `mk_sub`, `smul_mk`,
  `coeFn_add`, `coeFn_neg`, `coeFn_sub`, `coeFn_smul`

* The order structure of `L⁰` :
  `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
  And `α →ₘ β` inherits the preorder and partial order of `β`.

  TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
  linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.cast`:      To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.toFun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `AEEqFun.mk`:  To construct an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`:        Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `compMeasurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`:       Use `comp₂ g f₁ f₂` to get `[fun a ↦ g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

@[expose] public section

-- Guard against import creep
assert_not_exists InnerProductSpace

noncomputable section

open Topology Set Filter TopologicalSpace ENNReal EMetric MeasureTheory Function

variable {α β γ δ : Type*} [MeasurableSpace α] {μ ν : Measure α}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]
variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
@[implicit_reducible]
def Measure.aeEqSetoid (μ : Measure α) : Setoid { f : α → β // AEStronglyMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun {f} => ae_eq_refl f.val, fun {_ _} => ae_eq_symm,
    fun {_ _ _} => ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
they differ on a set of measure `0`. -/
def AEEqFun (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid β)

variable {α β}

@[inherit_doc MeasureTheory.AEEqFun]
notation:25 α " →ₘ[" μ "] " β => AEEqFun α β μ

end MeasurableSpace

variable [TopologicalSpace δ]

namespace AEEqFun

section
variable [TopologicalSpace β]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type*} [TopologicalSpace β] (f : α → β) (hf : AEStronglyMeasurable f μ) : α →ₘ[μ] β :=
  Quotient.mk'' ⟨f, hf⟩

open scoped Classical in
/-- Coercion from a space of equivalence classes of almost everywhere strongly measurable
functions to functions. We ensure that if `f` has a constant representative,
then we choose that one. -/
@[coe]
def cast (f : α →ₘ[μ] β) : α → β :=
  if h : ∃ (b : β), f = mk (const α b) aestronglyMeasurable_const then
    const α <| Classical.choose h else
    AEStronglyMeasurable.mk _ (Quotient.out f : { f : α → β // AEStronglyMeasurable f μ }).2

/-- A measurable representative of an `AEEqFun` [f] -/
instance instCoeFun : CoeFun (α →ₘ[μ] β) fun _ => α → β := ⟨cast⟩

@[fun_prop]
protected theorem stronglyMeasurable (f : α →ₘ[μ] β) : StronglyMeasurable f := by
  simp only [cast]
  split_ifs with h
  · exact stronglyMeasurable_const
  · apply AEStronglyMeasurable.stronglyMeasurable_mk

@[fun_prop]
protected theorem aestronglyMeasurable (f : α →ₘ[μ] β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]
protected theorem measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : Measurable f :=
  f.stronglyMeasurable.measurable

@[fun_prop]
protected theorem aemeasurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : AEMeasurable f μ :=
  f.measurable.aemeasurable

@[simp]
theorem quot_mk_eq_mk (f : α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
  rfl

@[simp]
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotient.eq''

@[simp]
theorem mk_coeFn (f : α →ₘ[μ] β) : mk f f.aestronglyMeasurable = f := by
  conv_lhs => simp only [cast]
  split_ifs with h
  · exact Classical.choose_spec h |>.symm
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk, mk_eq_mk]
  exact (AEStronglyMeasurable.ae_eq_mk _).symm

@[ext]
theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]

theorem coeFn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f := by
  rw [← mk_eq_mk (hf := AEEqFun.aestronglyMeasurable ..) (hg := hf), mk_coeFn]

@[elab_as_elim]
theorem induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H

@[elab_as_elim]
theorem induction_on₂ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf

@[elab_as_elim]
theorem induction_on₃ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    {α'' β'' : Type*} [MeasurableSpace α''] [TopologicalSpace β''] {μ'' : Measure α''}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
    {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf

end

/-!
### Composition of an a.e. equal function with a (quasi-)measure-preserving function
-/

section compQuasiMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β} {f : α → β}

open MeasureTheory.Measure (QuasiMeasurePreserving)

/-- Composition of an almost everywhere equal function and a quasi-measure-preserving function.

See also `AEEqFun.compMeasurePreserving`. -/
def compQuasiMeasurePreserving (g : β →ₘ[ν] γ) (f : α → β) (hf : QuasiMeasurePreserving f μ ν) :
    α →ₘ[μ] γ :=
  Quotient.liftOn' g (fun g ↦ mk (g ∘ f) <| g.2.comp_quasiMeasurePreserving hf) fun _ _ h ↦
    mk_eq_mk.2 <| h.comp_tendsto hf.tendsto_ae

@[simp]
theorem compQuasiMeasurePreserving_mk {g : β → γ} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) :
    (mk g hg).compQuasiMeasurePreserving f hf = mk (g ∘ f) (hg.comp_quasiMeasurePreserving hf) :=
  rfl

theorem compQuasiMeasurePreserving_eq_mk (g : β →ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) :
    g.compQuasiMeasurePreserving f hf =
      mk (g ∘ f) (g.aestronglyMeasurable.comp_quasiMeasurePreserving hf) := by
  rw [← compQuasiMeasurePreserving_mk g.aestronglyMeasurable hf, mk_coeFn]

theorem coeFn_compQuasiMeasurePreserving (g : β →ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) :
    g.compQuasiMeasurePreserving f hf =ᵐ[μ] g ∘ f := by
  rw [compQuasiMeasurePreserving_eq_mk]
  apply coeFn_mk

theorem compQuasiMeasurePreserving_congr (g : β →ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν)
    {f' : α → β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compQuasiMeasurePreserving g f hf = compQuasiMeasurePreserving g f' (hf.congr hf' h) := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving, h]

@[simp]
theorem compQuasiMeasurePreserving_id (g : β →ₘ[ν] γ) :
    compQuasiMeasurePreserving g id (.id ν) = g := by
  ext
  exact coeFn_compQuasiMeasurePreserving _ _

theorem compQuasiMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ →ₘ[ξ] δ) {f : β → γ} (hf : QuasiMeasurePreserving f ν ξ) {f' : α → β}
    (hf' : QuasiMeasurePreserving f' μ ν) :
    compQuasiMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compQuasiMeasurePreserving (compQuasiMeasurePreserving g f hf) f' hf' := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving,
    coeFn_compQuasiMeasurePreserving, comp_assoc]

theorem compQuasiMeasurePreserving_iterate (g : α →ₘ[μ] γ) {f : α → α}
    (hf : QuasiMeasurePreserving f μ μ) (n : ℕ) :
    (compQuasiMeasurePreserving · f hf)^[n] g =
    compQuasiMeasurePreserving g (f^[n]) (hf.iterate n) := by
  induction n with
  | zero => simp
  | succ n hind =>
    nth_rewrite 1 [add_comm]
    simp [iterate_add, hind, ← compQuasiMeasurePreserving_comp]

end compQuasiMeasurePreserving

section compMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β}
  {f : α → β} {g : β → γ}

/-- Composition of an almost everywhere equal function and a quasi-measure-preserving function.

This is an important special case of `AEEqFun.compQuasiMeasurePreserving`. We use a separate
definition so that lemmas that need `f` to be measure preserving can be `@[simp]` lemmas. -/
def compMeasurePreserving (g : β →ₘ[ν] γ) (f : α → β) (hf : MeasurePreserving f μ ν) : α →ₘ[μ] γ :=
  g.compQuasiMeasurePreserving f hf.quasiMeasurePreserving

@[simp]
theorem compMeasurePreserving_mk (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    (mk g hg).compMeasurePreserving f hf =
      mk (g ∘ f) (hg.comp_quasiMeasurePreserving hf.quasiMeasurePreserving) :=
  rfl

theorem compMeasurePreserving_eq_mk (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    g.compMeasurePreserving f hf =
      mk (g ∘ f) (g.aestronglyMeasurable.comp_quasiMeasurePreserving hf.quasiMeasurePreserving) :=
  g.compQuasiMeasurePreserving_eq_mk _

theorem coeFn_compMeasurePreserving (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    g.compMeasurePreserving f hf =ᵐ[μ] g ∘ f :=
  g.coeFn_compQuasiMeasurePreserving _

theorem compMeasurePreserving_congr (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν)
    {f' : α → β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compMeasurePreserving g f hf = compMeasurePreserving g f' (hf.congr hf' h) :=
  compQuasiMeasurePreserving_congr _ _ hf' h

@[simp]
theorem compMeasurePreserving_id (g : β →ₘ[ν] γ) :
    compMeasurePreserving g id (.id ν) = g :=
  compQuasiMeasurePreserving_id _

theorem compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ →ₘ[ξ] δ) {f : β → γ} (hf : MeasurePreserving f ν ξ) {f' : α → β}
    (hf' : MeasurePreserving f' μ ν) :
    compMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compMeasurePreserving (compMeasurePreserving g f hf) f' hf' :=
  compQuasiMeasurePreserving_comp _ _ _

theorem compMeasurePreserving_iterate (g : α →ₘ[μ] γ) {f : α → α}
    (hf : MeasurePreserving f μ μ) (n : ℕ) :
    (compMeasurePreserving · f hf)^[n] g = compMeasurePreserving g (f^[n]) (hf.iterate n) :=
  compQuasiMeasurePreserving_iterate _ _ _

end compMeasurePreserving

variable [TopologicalSpace β] [TopologicalSpace γ]

/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
`[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f (fun f => mk (g ∘ (f : α → β)) (hg.comp_aestronglyMeasurable f.2))
    fun _ _ H => mk_eq_mk.2 <| H.fun_comp g

@[simp]
theorem comp_mk (g : β → γ) (hg : Continuous g) (f : α → β) (hf) :
    comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestronglyMeasurable hf) :=
  rfl

@[simp]
theorem comp_id (f : α →ₘ[μ] β) : comp id (continuous_id) f = f := by
  rcases f; rfl

@[simp]
theorem comp_comp (g : γ → δ) (g' : β → γ) (hg : Continuous g) (hg' : Continuous g')
    (f : α →ₘ[μ] β) : comp g hg (comp g' hg' f) = comp (g ∘ g') (hg.comp hg') f := by
  rcases f; rfl

theorem comp_eq_mk (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable f.aestronglyMeasurable) := by
  rw [← comp_mk g hg f f.aestronglyMeasurable, mk_coeFn]

theorem coeFn_comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f := by
  rw [comp_eq_mk]
  apply coeFn_mk

theorem comp_compQuasiMeasurePreserving
    {β : Type*} [MeasurableSpace β] {ν} (g : γ → δ) (hg : Continuous g)
    (f : β →ₘ[ν] γ) {φ : α → β} (hφ : Measure.QuasiMeasurePreserving φ μ ν) :
    (comp g hg f).compQuasiMeasurePreserving φ hφ =
      comp g hg (f.compQuasiMeasurePreserving φ hφ) := by
  rcases f; rfl

section CompMeasurable

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [MeasurableSpace γ]
  [PseudoMetrizableSpace γ] [OpensMeasurableSpace γ] [SecondCountableTopology γ]

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
`[g ∘ f] : α →ₘ γ`. This requires that `γ` has a second countable topology. -/
def compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f
    (fun f' => mk (g ∘ (f' : α → β)) (hg.comp_aemeasurable f'.2.aemeasurable).aestronglyMeasurable)
    fun _ _ H => mk_eq_mk.2 <| H.fun_comp g

@[simp]
theorem compMeasurable_mk (g : β → γ) (hg : Measurable g) (f : α → β)
    (hf : AEStronglyMeasurable f μ) :
    compMeasurable g hg (mk f hf : α →ₘ[μ] β) =
      mk (g ∘ f) (hg.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable :=
  rfl

theorem compMeasurable_eq_mk (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =
    mk (g ∘ f) (hg.comp_aemeasurable f.aemeasurable).aestronglyMeasurable := by
  rw [← compMeasurable_mk g hg f f.aestronglyMeasurable, mk_coeFn]

theorem coeFn_compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =ᵐ[μ] g ∘ f := by
  rw [compMeasurable_eq_mk]
  apply coeFn_mk

end CompMeasurable

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prodMk g.2))
    fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 <| Hf.prodMk Hg

@[simp]
theorem pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
    (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prodMk hg) :=
  rfl

theorem pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
    f.pair g =
      mk (fun x => (f x, g x)) (f.aestronglyMeasurable.prodMk g.aestronglyMeasurable) := by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyMeasurable, g.aestronglyMeasurable]

theorem coeFn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) := by
  rw [pair_eq_mk]
  apply coeFn_mk

/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
`[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    α →ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)

@[simp]
theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_aestronglyMeasurable (hf₁.prodMk hf₂)) :=
  rfl

theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl

theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = mk (fun a => g (f₁ a) (f₂ a))
      (hg.comp_aestronglyMeasurable (f₁.aestronglyMeasurable.prodMk f₂.aestronglyMeasurable)) := by
  rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; rfl

theorem coeFn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂_eq_mk]
  apply coeFn_mk

section

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
  [MeasurableSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] [SecondCountableTopologyEither β γ]
  [MeasurableSpace δ] [PseudoMetrizableSpace δ] [OpensMeasurableSpace δ] [SecondCountableTopology δ]

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
`[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₘ γ`. This requires `δ` to have second-countable topology. -/
def comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
  compMeasurable _ hg (f₁.pair f₂)

@[simp]
theorem comp₂Measurable_mk_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α → β)
    (f₂ : α → γ) (hf₁ hf₂) :
    comp₂Measurable g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (hf₁.aemeasurable.prodMk hf₂.aemeasurable)).aestronglyMeasurable :=
  rfl

theorem comp₂Measurable_eq_pair (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ = compMeasurable _ hg (f₁.pair f₂) :=
  rfl

theorem comp₂Measurable_eq_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (f₁.aemeasurable.prodMk f₂.aemeasurable)).aestronglyMeasurable := by
  rw [comp₂Measurable_eq_pair, pair_eq_mk, compMeasurable_mk]; rfl

theorem coeFn_comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂Measurable_eq_mk]
  apply coeFn_mk

end

/-- Interpret `f : α →ₘ[μ] β` as a germ at `ae μ` forgetting that `f` is almost everywhere
strongly measurable. -/
def toGerm (f : α →ₘ[μ] β) : Germ (ae μ) β :=
  Quotient.liftOn' f (fun f => ((f : α → β) : Germ (ae μ) β)) fun _ _ H => Germ.coe_eq.2 H

@[simp]
theorem mk_toGerm (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).toGerm = f :=
  rfl

theorem toGerm_eq (f : α →ₘ[μ] β) : f.toGerm = (f : α → β) := by
  rw [← mk_toGerm f f.aestronglyMeasurable, mk_coeFn]

theorem toGerm_injective : Injective (toGerm : (α →ₘ[μ] β) → Germ (ae μ) β) := fun f g H =>
  ext <| Germ.coe_eq.1 <| by rwa [← toGerm_eq, ← toGerm_eq]

@[simp]
theorem compQuasiMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α → β} {ν}
    (g : β →ₘ[ν] γ) (hf : Measure.QuasiMeasurePreserving f μ ν) :
    (g.compQuasiMeasurePreserving f hf).toGerm = g.toGerm.compTendsto f hf.tendsto_ae := by
  rcases g; rfl

@[simp]
theorem compMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α → β} {ν}
    (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    (g.compMeasurePreserving f hf).toGerm =
      g.toGerm.compTendsto f hf.quasiMeasurePreserving.tendsto_ae :=
  compQuasiMeasurePreserving_toGerm _ _

theorem comp_toGerm (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    (comp g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp

theorem compMeasurable_toGerm [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    (compMeasurable g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp

theorem comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

theorem comp₂Measurable_toGerm [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopologyEither β γ]
    [MeasurableSpace γ] [BorelSpace γ] [PseudoMetrizableSpace δ] [SecondCountableTopology δ]
    [MeasurableSpace δ] [OpensMeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂Measurable g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
for almost all `a` -/
def LiftPred (p : β → Prop) (f : α →ₘ[μ] β) : Prop :=
  f.toGerm.LiftPred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
`(f a, g a)` for almost all `a` -/
def LiftRel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm

theorem liftRel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
    LiftRel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl

theorem liftRel_iff_coeFn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
    LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) := by
  rw [← liftRel_mk_mk (hf := f.aestronglyMeasurable) (hg := g.aestronglyMeasurable),
    mk_coeFn, mk_coeFn]

section Order

instance instPreorder [Preorder β] : Preorder (α →ₘ[μ] β) :=
  Preorder.lift toGerm

@[simp]
theorem mk_le_mk [Preorder β] {f g : α → β} (hf hg) : (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
  Iff.rfl

@[simp, norm_cast]
theorem coeFn_le [Preorder β] {f g : α →ₘ[μ] β} : (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
  liftRel_iff_coeFn.symm

instance instPartialOrder [PartialOrder β] : PartialOrder (α →ₘ[μ] β) :=
  PartialOrder.lift toGerm toGerm_injective

section Lattice

section Sup

variable [SemilatticeSup β] [ContinuousSup β]

instance instSup : Max (α →ₘ[μ] β) where max f g := AEEqFun.comp₂ (· ⊔ ·) continuous_sup f g

theorem coeFn_sup (f g : α →ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x :=
  coeFn_comp₂ _ _ _ _

protected theorem le_sup_left (f g : α →ₘ[μ] β) : f ≤ f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_left

protected theorem le_sup_right (f g : α →ₘ[μ] β) : g ≤ f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_right

protected theorem sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_sup f g] with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag

end Sup

section Inf

variable [SemilatticeInf β] [ContinuousInf β]

instance instInf : Min (α →ₘ[μ] β) where min f g := AEEqFun.comp₂ (· ⊓ ·) continuous_inf f g

theorem coeFn_inf (f g : α →ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x :=
  coeFn_comp₂ _ _ _ _

protected theorem inf_le_left (f g : α →ₘ[μ] β) : f ⊓ g ≤ f := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_left

protected theorem inf_le_right (f g : α →ₘ[μ] β) : f ⊓ g ≤ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_right

protected theorem le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_inf f g] with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag

end Inf

instance instLattice [Lattice β] [TopologicalLattice β] : Lattice (α →ₘ[μ] β) :=
  { AEEqFun.instPartialOrder with
    sup := max
    le_sup_left := AEEqFun.le_sup_left
    le_sup_right := AEEqFun.le_sup_right
    sup_le := AEEqFun.sup_le
    inf := min
    inf_le_left := AEEqFun.inf_le_left
    inf_le_right := AEEqFun.inf_le_right
    le_inf := AEEqFun.le_inf }

end Lattice

end Order

variable (α)

/-- The equivalence class of a constant function: `[fun _ : α => b]`, based on the equivalence
relation of being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β :=
  mk (fun _ : α ↦ b) aestronglyMeasurable_const

theorem coeFn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coeFn_mk _ _

/-- If the measure is nonzero, we can strengthen `coeFn_const` to get an equality. -/
@[simp]
theorem coeFn_const_eq [NeZero μ] (b : β) (x : α) : (const α b : α →ₘ[μ] β) x = b := by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  have := Classical.choose_spec h
  set b' := Classical.choose h
  simp_rw [const, mk_eq_mk, EventuallyEq, ← const_def, eventually_const] at this
  rw [Function.const, this]

variable {α}

instance instInhabited [Inhabited β] : Inhabited (α →ₘ[μ] β) :=
  ⟨const α default⟩

@[to_additive]
instance instOne [One β] : One (α →ₘ[μ] β) :=
  ⟨const α 1⟩

@[to_additive]
theorem one_def [One β] : (1 : α →ₘ[μ] β) = mk (fun _ : α => 1) aestronglyMeasurable_const :=
  rfl

@[to_additive]
theorem coeFn_one [One β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 :=
  coeFn_const ..

@[to_additive (attr := simp)]
theorem coeFn_one_eq [NeZero μ] [One β] {x : α} : (1 : α →ₘ[μ] β) x = 1 :=
  coeFn_const_eq ..

@[to_additive (attr := simp)]
theorem one_toGerm [One β] : (1 : α →ₘ[μ] β).toGerm = 1 :=
  rfl

-- Note we set up the scalar actions before the `Monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section SMul

variable {𝕜 𝕜' : Type*}
variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]
variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]

instance instSMul : SMul 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩

@[simp]
theorem smul_mk (c : 𝕜) (f : α → γ) (hf : AEStronglyMeasurable f μ) :
    c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl

theorem coeFn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  coeFn_comp _ _ _

theorem smul_toGerm (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _

instance instSMulCommClass [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩

instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩

instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

end SMul

section Mul

variable [Mul γ] [ContinuousMul γ]

@[to_additive]
instance instMul : Mul (α →ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩

@[to_additive (attr := simp)]
theorem mk_mul_mk (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    (mk f hf : α →ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl

@[to_additive]
theorem coeFn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coeFn_comp₂ _ _ _ _

@[to_additive (attr := simp)]
theorem mul_toGerm (f g : α →ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _

end Mul

instance instAddMonoid [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

instance instAddCommMonoid [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

section Monoid

variable [Monoid γ] [ContinuousMul γ]

instance instPowNat : Pow (α →ₘ[μ] γ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]
theorem mk_pow (f : α → γ) (hf) (n : ℕ) :
    (mk f hf : α →ₘ[μ] γ) ^ n =
      mk (f ^ n) ((_root_.continuous_pow n).comp_aestronglyMeasurable hf) :=
  rfl

theorem coeFn_pow (f : α →ₘ[μ] γ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
theorem pow_toGerm (f : α →ₘ[μ] γ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

@[to_additive existing]
instance instMonoid : Monoid (α →ₘ[μ] γ) :=
  toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm

/-- `AEEqFun.toGerm` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `AEEqFun.toGerm` as an `AddMonoidHom`. -/]
def toGermMonoidHom : (α →ₘ[μ] γ) →* (ae μ).Germ γ where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm

end Monoid

@[to_additive existing]
instance instCommMonoid [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm

section Group

variable [Group γ] [IsTopologicalGroup γ]

section Inv

@[to_additive]
instance instInv : Inv (α →ₘ[μ] γ) :=
  ⟨comp Inv.inv continuous_inv⟩

@[to_additive (attr := simp)]
theorem inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl

@[to_additive]
theorem coeFn_inv (f : α →ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coeFn_comp _ _ _

@[to_additive]
theorem inv_toGerm (f : α →ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _

end Inv

section Div

@[to_additive]
instance instDiv : Div (α →ₘ[μ] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩

@[to_additive (attr := simp)]
theorem mk_div (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (f / g) (hf.div hg) = (mk f hf : α →ₘ[μ] γ) / mk g hg :=
  rfl

@[to_additive]
theorem coeFn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coeFn_comp₂ _ _ _ _

@[to_additive]
theorem div_toGerm (f g : α →ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _

end Div

section ZPow

instance instPowInt : Pow (α →ₘ[μ] γ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩

@[simp]
theorem mk_zpow (f : α → γ) (hf) (n : ℤ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_aestronglyMeasurable hf) :=
  rfl

theorem coeFn_zpow (f : α →ₘ[μ] γ) (n : ℤ) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
theorem zpow_toGerm (f : α →ₘ[μ] γ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

end ZPow

end Group

instance instAddGroup [AddGroup γ] [IsTopologicalAddGroup γ] : AddGroup (α →ₘ[μ] γ) :=
  toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

instance instAddCommGroup [AddCommGroup γ] [IsTopologicalAddGroup γ] : AddCommGroup (α →ₘ[μ] γ) :=
  { add_comm := add_comm }

@[to_additive existing]
instance instGroup [Group γ] [IsTopologicalGroup γ] : Group (α →ₘ[μ] γ) :=
  toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive existing]
instance instCommGroup [CommGroup γ] [IsTopologicalGroup γ] : CommGroup (α →ₘ[μ] γ) :=
  { mul_comm := mul_comm }

section Module

variable {𝕜 : Type*}

instance instMulAction [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    MulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.mulAction toGerm smul_toGerm

instance instDistribMulAction [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.distribMulAction (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) fun c : 𝕜 =>
    smul_toGerm c

instance instModule [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : Module 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.module 𝕜 (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) smul_toGerm

end Module

open ENNReal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
  Quotient.liftOn' f (fun f => ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) fun _ _ => lintegral_congr_ae

@[simp]
theorem lintegral_mk (f : α → ℝ≥0∞) (hf) : (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl

theorem lintegral_coeFn (f : α →ₘ[μ] ℝ≥0∞) : ∫⁻ a, f a ∂μ = f.lintegral := by
  rw [← lintegral_mk (hf := f.aestronglyMeasurable), mk_coeFn]

@[simp]
nonrec theorem lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 :=
  lintegral_zero

@[simp]
theorem lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
  induction_on f fun _f hf => (lintegral_eq_zero_iff' hf.aemeasurable).trans mk_eq_mk.symm

theorem lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  induction_on₂ f g fun f hf g _ => by simp [lintegral_add_left' hf.aemeasurable]

theorem lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
  induction_on₂ f g fun _f _ _g _ hfg => lintegral_mono_ae hfg

section Abs

theorem coeFn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroup β]
    [IsTopologicalAddGroup β] (f : α →ₘ[μ] β) : ⇑|f| =ᵐ[μ] fun x => |f x| := by
  simp_rw [abs]
  filter_upwards [AEEqFun.coeFn_sup f (-f), AEEqFun.coeFn_neg f] with x hx_sup hx_neg
  rw [hx_sup, hx_neg, Pi.neg_apply]

end Abs

section Star

variable {R : Type*} [TopologicalSpace R]

instance [Star R] [ContinuousStar R] : Star (α →ₘ[μ] R) where
  star f := (AEEqFun.comp _ continuous_star f)

lemma coeFn_star [Star R] [ContinuousStar R] (f : α →ₘ[μ] R) : ↑(star f) =ᵐ[μ] (star f : α → R) :=
  coeFn_comp _ (continuous_star) f

instance [InvolutiveStar R] [ContinuousStar R] : InvolutiveStar (α →ₘ[μ] R) where
  star_involutive f := comp_comp _ _ _ _ f |>.trans <| by simp [star_involutive.comp_self]

instance [Star R] [TrivialStar R] [ContinuousStar R] : TrivialStar (α →ₘ[μ] R) where
  star_trivial f := show comp _ _ f = f by simp [funext star_trivial, ← Function.id_def]

end Star

section PosPart

variable [LinearOrder γ] [OrderClosedTopology γ] [Zero γ]

/-- Positive part of an `AEEqFun`. -/
def posPart (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
  comp (fun x => max x 0) (by fun_prop) f

@[simp]
theorem posPart_mk (f : α → γ) (hf) :
    posPart (mk f hf : α →ₘ[μ] γ) = mk (fun x ↦ max (f x) 0) (by fun_prop) :=
  rfl

theorem coeFn_posPart (f : α →ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  coeFn_comp _ _ _

end PosPart

section AELimit

/-- The ae-limit is ae-unique. -/
theorem tendsto_ae_unique {ι : Type*} [T2Space β]
    {g h : α → β} {f : ι → α → β} {l : Filter ι} [l.NeBot]
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (g ω)))
    (hh : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (h ω))) : g =ᵐ[μ] h := by
  filter_upwards [hg, hh] with ω hg1 hh1 using tendsto_nhds_unique hg1 hh1

end AELimit

end AEEqFun

end MeasureTheory

namespace ContinuousMap

open MeasureTheory

variable [TopologicalSpace α] [BorelSpace α] (μ)
variable [TopologicalSpace β] [SecondCountableTopologyEither α β] [PseudoMetrizableSpace β]

/-- The equivalence class of `μ`-almost-everywhere measurable functions associated to a continuous
map. -/
def toAEEqFun (f : C(α, β)) : α →ₘ[μ] β :=
  AEEqFun.mk f f.continuous.aestronglyMeasurable

theorem coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqFun μ =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _

variable [Group β] [IsTopologicalGroup β]

/-- The `MulHom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive /-- The `AddHom` from the group of continuous maps from `α` to `β` to the group of
equivalence classes of `μ`-almost-everywhere measurable functions. -/]
def toAEEqFunMulHom : C(α, β) →* α →ₘ[μ] β where
  toFun := ContinuousMap.toAEEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AEEqFun.mk_mul_mk _ _ f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable

variable {𝕜 : Type*} [Semiring 𝕜]
variable [TopologicalSpace γ] [PseudoMetrizableSpace γ] [AddCommGroup γ] [Module 𝕜 γ]
  [IsTopologicalAddGroup γ] [ContinuousConstSMul 𝕜 γ] [SecondCountableTopologyEither α γ]

/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
def toAEEqFunLinearMap : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
  { toAEEqFunAddHom μ with
    map_smul' := fun c f => AEEqFun.smul_mk c f f.continuous.aestronglyMeasurable }

end ContinuousMap
