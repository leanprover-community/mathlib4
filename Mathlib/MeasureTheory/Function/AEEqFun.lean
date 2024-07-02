/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Order.Filter.Germ
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

#align_import measure_theory.function.ae_eq_fun from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!

# Almost everywhere equal functions

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `L1Space.lean` for `L¹` space.

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

    See `mk_add_mk`,  `neg_mk`,     `mk_sub_mk`,  `smul_mk`,
        `add_toFun`, `neg_toFun`, `sub_toFun`, `smul_toFun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.toFun`      : To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.toFun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `comp_measurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`        : Use `comp₂ g f₁ f₂` to get `[fun a ↦ g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

noncomputable section

open scoped Classical
open ENNReal Topology

open Set Filter TopologicalSpace ENNReal EMetric MeasureTheory Function

variable {α β γ δ : Type*} [MeasurableSpace α] {μ ν : Measure α}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]
variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
def Measure.aeEqSetoid (μ : Measure α) : Setoid { f : α → β // AEStronglyMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun {f} => ae_eq_refl f.val, fun {_ _} => ae_eq_symm,
    fun {_ _ _} => ae_eq_trans⟩
#align measure_theory.measure.ae_eq_setoid MeasureTheory.Measure.aeEqSetoid

variable (α)

/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
    strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
    they differ on a set of measure `0`.  -/
def AEEqFun (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid β)
#align measure_theory.ae_eq_fun MeasureTheory.AEEqFun

variable {α β}

@[inherit_doc MeasureTheory.AEEqFun]
notation:25 α " →ₘ[" μ "] " β => AEEqFun α β μ

end MeasurableSpace

namespace AEEqFun

variable [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
    on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type*} [TopologicalSpace β] (f : α → β) (hf : AEStronglyMeasurable f μ) : α →ₘ[μ] β :=
  Quotient.mk'' ⟨f, hf⟩
#align measure_theory.ae_eq_fun.mk MeasureTheory.AEEqFun.mk

/-- Auxiliary condition used in the cast function. -/
def cast.Cond (f : α →ₘ[μ] β) : Prop :=
  ∃ (g : α → β) (hg : StronglyMeasurable g),
    f = mk g hg.aestronglyMeasurable ∧ g ∈ range (Function.const α)

/-- Coercion from a space of equivalence classes of almost everywhere strongly measurable
functions to functions. -/
@[coe]
def cast (f : α →ₘ[μ] β) : α → β :=
  if h : cast.Cond f then Classical.choose h else
    AEStronglyMeasurable.mk _ (Quotient.out' f : { f : α → β // AEStronglyMeasurable f μ }).2

/-- A measurable representative of an `AEEqFun` [f] -/
instance instCoeFun : CoeFun (α →ₘ[μ] β) fun _ => α → β := ⟨cast⟩
#align measure_theory.ae_eq_fun.has_coe_to_fun MeasureTheory.AEEqFun.instCoeFun

protected theorem stronglyMeasurable (f : α →ₘ[μ] β) : StronglyMeasurable f := by
  simp only [cast]
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · apply AEStronglyMeasurable.stronglyMeasurable_mk
#align measure_theory.ae_eq_fun.strongly_measurable MeasureTheory.AEEqFun.stronglyMeasurable

protected theorem aestronglyMeasurable (f : α →ₘ[μ] β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable
#align measure_theory.ae_eq_fun.ae_strongly_measurable MeasureTheory.AEEqFun.aestronglyMeasurable

protected theorem measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : Measurable f :=
  f.stronglyMeasurable.measurable
#align measure_theory.ae_eq_fun.measurable MeasureTheory.AEEqFun.measurable

protected theorem aemeasurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : AEMeasurable f μ :=
  f.measurable.aemeasurable
#align measure_theory.ae_eq_fun.ae_measurable MeasureTheory.AEEqFun.aemeasurable

@[simp]
theorem quot_mk_eq_mk (f : α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
  rfl
#align measure_theory.ae_eq_fun.quot_mk_eq_mk MeasureTheory.AEEqFun.quot_mk_eq_mk

@[simp]
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotient.eq''
#align measure_theory.ae_eq_fun.mk_eq_mk MeasureTheory.AEEqFun.mk_eq_mk

@[simp]
theorem mk_coeFn (f : α →ₘ[μ] β) : mk f f.aestronglyMeasurable = f := by
  conv_lhs => simp only [cast]
  split_ifs with h
  · exact Classical.choose_spec h |>.2.1.symm
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk, mk_eq_mk]
  exact (AEStronglyMeasurable.ae_eq_mk _).symm
#align measure_theory.ae_eq_fun.mk_coe_fn MeasureTheory.AEEqFun.mk_coeFn

@[ext]
theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]
#align measure_theory.ae_eq_fun.ext MeasureTheory.AEEqFun.ext

theorem ext_iff {f g : α →ₘ[μ] β} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h => by rw [h], fun h => ext h⟩
#align measure_theory.ae_eq_fun.ext_iff MeasureTheory.AEEqFun.ext_iff

theorem coeFn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f := by
  rw [← mk_eq_mk, mk_coeFn]
#align measure_theory.ae_eq_fun.coe_fn_mk MeasureTheory.AEEqFun.coeFn_mk

@[elab_as_elim]
theorem induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H
#align measure_theory.ae_eq_fun.induction_on MeasureTheory.AEEqFun.induction_on

@[elab_as_elim]
theorem induction_on₂ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf
#align measure_theory.ae_eq_fun.induction_on₂ MeasureTheory.AEEqFun.induction_on₂

@[elab_as_elim]
theorem induction_on₃ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    {α'' β'' : Type*} [MeasurableSpace α''] [TopologicalSpace β''] {μ'' : Measure α''}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
    {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf
#align measure_theory.ae_eq_fun.induction_on₃ MeasureTheory.AEEqFun.induction_on₃

/-!
### Composition of an a.e. equal function with a (quasi) measure preserving function
-/

section compQuasiMeasurePreserving

variable [MeasurableSpace β] {ν : MeasureTheory.Measure β} {f : α → β}

open MeasureTheory.Measure (QuasiMeasurePreserving)

/-- Composition of an almost everywhere equal function and a quasi measure preserving function.

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

end compQuasiMeasurePreserving

section compMeasurePreserving

variable [MeasurableSpace β] {ν : MeasureTheory.Measure β} {f : α → β} {g : β → γ}

/-- Composition of an almost everywhere equal function and a quasi measure preserving function.

This is an important special case of `AEEqFun.compQuasiMeasurePreserving`. We use a separate
definition so that lemmas that need `f` to be measure preserving can be `@[simp]` lemmas.  -/
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

end compMeasurePreserving

/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f (fun f => mk (g ∘ (f : α → β)) (hg.comp_aestronglyMeasurable f.2))
    fun _ _ H => mk_eq_mk.2 <| H.fun_comp g
#align measure_theory.ae_eq_fun.comp MeasureTheory.AEEqFun.comp

@[simp]
theorem comp_mk (g : β → γ) (hg : Continuous g) (f : α → β) (hf) :
    comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.comp_mk MeasureTheory.AEEqFun.comp_mk

theorem comp_eq_mk (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable f.aestronglyMeasurable) := by
  rw [← comp_mk g hg f f.aestronglyMeasurable, mk_coeFn]
#align measure_theory.ae_eq_fun.comp_eq_mk MeasureTheory.AEEqFun.comp_eq_mk

theorem coeFn_comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f := by
  rw [comp_eq_mk]
  apply coeFn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp MeasureTheory.AEEqFun.coeFn_comp

theorem comp_compQuasiMeasurePreserving [MeasurableSpace β] {ν} (g : γ → δ) (hg : Continuous g)
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
#align measure_theory.ae_eq_fun.comp_measurable MeasureTheory.AEEqFun.compMeasurable

@[simp]
theorem compMeasurable_mk (g : β → γ) (hg : Measurable g) (f : α → β)
    (hf : AEStronglyMeasurable f μ) :
    compMeasurable g hg (mk f hf : α →ₘ[μ] β) =
      mk (g ∘ f) (hg.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable :=
  rfl
#align measure_theory.ae_eq_fun.comp_measurable_mk MeasureTheory.AEEqFun.compMeasurable_mk

theorem compMeasurable_eq_mk (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =
    mk (g ∘ f) (hg.comp_aemeasurable f.aemeasurable).aestronglyMeasurable := by
  rw [← compMeasurable_mk g hg f f.aestronglyMeasurable, mk_coeFn]
#align measure_theory.ae_eq_fun.comp_measurable_eq_mk MeasureTheory.AEEqFun.compMeasurable_eq_mk

theorem coeFn_compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =ᵐ[μ] g ∘ f := by
  rw [compMeasurable_eq_mk]
  apply coeFn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp_measurable MeasureTheory.AEEqFun.coeFn_compMeasurable

end CompMeasurable

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prod_mk g.2))
    fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 <| Hf.prod_mk Hg
#align measure_theory.ae_eq_fun.pair MeasureTheory.AEEqFun.pair

@[simp]
theorem pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
    (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prod_mk hg) :=
  rfl
#align measure_theory.ae_eq_fun.pair_mk_mk MeasureTheory.AEEqFun.pair_mk_mk

theorem pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
    f.pair g =
      mk (fun x => (f x, g x)) (f.aestronglyMeasurable.prod_mk g.aestronglyMeasurable) := by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyMeasurable, g.aestronglyMeasurable]
#align measure_theory.ae_eq_fun.pair_eq_mk MeasureTheory.AEEqFun.pair_eq_mk

theorem coeFn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) := by
  rw [pair_eq_mk]
  apply coeFn_mk
#align measure_theory.ae_eq_fun.coe_fn_pair MeasureTheory.AEEqFun.coeFn_pair

/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[fun a => g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    α →ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)
#align measure_theory.ae_eq_fun.comp₂ MeasureTheory.AEEqFun.comp₂

@[simp]
theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_aestronglyMeasurable (hf₁.prod_mk hf₂)) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_mk_mk MeasureTheory.AEEqFun.comp₂_mk_mk

theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_eq_pair MeasureTheory.AEEqFun.comp₂_eq_pair

theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = mk (fun a => g (f₁ a) (f₂ a))
      (hg.comp_aestronglyMeasurable (f₁.aestronglyMeasurable.prod_mk f₂.aestronglyMeasurable)) := by
  rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; rfl
#align measure_theory.ae_eq_fun.comp₂_eq_mk MeasureTheory.AEEqFun.comp₂_eq_mk

theorem coeFn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂_eq_mk]
  apply coeFn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp₂ MeasureTheory.AEEqFun.coeFn_comp₂

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
#align measure_theory.ae_eq_fun.comp₂_measurable MeasureTheory.AEEqFun.comp₂Measurable

@[simp]
theorem comp₂Measurable_mk_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α → β)
    (f₂ : α → γ) (hf₁ hf₂) :
    comp₂Measurable g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (hf₁.aemeasurable.prod_mk hf₂.aemeasurable)).aestronglyMeasurable :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_mk_mk MeasureTheory.AEEqFun.comp₂Measurable_mk_mk

theorem comp₂Measurable_eq_pair (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ = compMeasurable _ hg (f₁.pair f₂) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_eq_pair MeasureTheory.AEEqFun.comp₂Measurable_eq_pair

theorem comp₂Measurable_eq_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (f₁.aemeasurable.prod_mk f₂.aemeasurable)).aestronglyMeasurable := by
  rw [comp₂Measurable_eq_pair, pair_eq_mk, compMeasurable_mk]; rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_eq_mk MeasureTheory.AEEqFun.comp₂Measurable_eq_mk

theorem coeFn_comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂Measurable_eq_mk]
  apply coeFn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp₂_measurable MeasureTheory.AEEqFun.coeFn_comp₂Measurable

end

/-- Interpret `f : α →ₘ[μ] β` as a germ at `ae μ` forgetting that `f` is almost everywhere
    strongly measurable. -/
def toGerm (f : α →ₘ[μ] β) : Germ (ae μ) β :=
  Quotient.liftOn' f (fun f => ((f : α → β) : Germ (ae μ) β)) fun _ _ H => Germ.coe_eq.2 H
#align measure_theory.ae_eq_fun.to_germ MeasureTheory.AEEqFun.toGerm

@[simp]
theorem mk_toGerm (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).toGerm = f :=
  rfl
#align measure_theory.ae_eq_fun.mk_to_germ MeasureTheory.AEEqFun.mk_toGerm

theorem toGerm_eq (f : α →ₘ[μ] β) : f.toGerm = (f : α → β) := by rw [← mk_toGerm, mk_coeFn]
#align measure_theory.ae_eq_fun.to_germ_eq MeasureTheory.AEEqFun.toGerm_eq

theorem toGerm_injective : Injective (toGerm : (α →ₘ[μ] β) → Germ (ae μ) β) := fun f g H =>
  ext <| Germ.coe_eq.1 <| by rwa [← toGerm_eq, ← toGerm_eq]
#align measure_theory.ae_eq_fun.to_germ_injective MeasureTheory.AEEqFun.toGerm_injective

@[simp]
theorem compQuasiMeasurePreserving_toGerm [MeasurableSpace β] {f : α → β} {ν}
    (g : β →ₘ[ν] γ) (hf : Measure.QuasiMeasurePreserving f μ ν) :
    (g.compQuasiMeasurePreserving f hf).toGerm = g.toGerm.compTendsto f hf.tendsto_ae := by
  rcases g; rfl

@[simp]
theorem compMeasurePreserving_toGerm [MeasurableSpace β] {f : α → β} {ν}
    (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    (g.compMeasurePreserving f hf).toGerm =
      g.toGerm.compTendsto f hf.quasiMeasurePreserving.tendsto_ae :=
  compQuasiMeasurePreserving_toGerm _ _

theorem comp_toGerm (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    (comp g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp
#align measure_theory.ae_eq_fun.comp_to_germ MeasureTheory.AEEqFun.comp_toGerm

theorem compMeasurable_toGerm [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    (compMeasurable g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp
#align measure_theory.ae_eq_fun.comp_measurable_to_germ MeasureTheory.AEEqFun.compMeasurable_toGerm

theorem comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp
#align measure_theory.ae_eq_fun.comp₂_to_germ MeasureTheory.AEEqFun.comp₂_toGerm

theorem comp₂Measurable_toGerm [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopologyEither β γ]
    [MeasurableSpace γ] [BorelSpace γ] [PseudoMetrizableSpace δ] [SecondCountableTopology δ]
    [MeasurableSpace δ] [OpensMeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂Measurable g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp
#align measure_theory.ae_eq_fun.comp₂_measurable_to_germ MeasureTheory.AEEqFun.comp₂Measurable_toGerm

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def LiftPred (p : β → Prop) (f : α →ₘ[μ] β) : Prop :=
  f.toGerm.LiftPred p
#align measure_theory.ae_eq_fun.lift_pred MeasureTheory.AEEqFun.LiftPred

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def LiftRel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm
#align measure_theory.ae_eq_fun.lift_rel MeasureTheory.AEEqFun.LiftRel

theorem liftRel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
    LiftRel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl
#align measure_theory.ae_eq_fun.lift_rel_mk_mk MeasureTheory.AEEqFun.liftRel_mk_mk

theorem liftRel_iff_coeFn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
    LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) := by rw [← liftRel_mk_mk, mk_coeFn, mk_coeFn]
#align measure_theory.ae_eq_fun.lift_rel_iff_coe_fn MeasureTheory.AEEqFun.liftRel_iff_coeFn

section Order

instance instPreorder [Preorder β] : Preorder (α →ₘ[μ] β) :=
  Preorder.lift toGerm
#align measure_theory.ae_eq_fun.preorder MeasureTheory.AEEqFun.instPreorder

@[simp]
theorem mk_le_mk [Preorder β] {f g : α → β} (hf hg) : (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
  Iff.rfl
#align measure_theory.ae_eq_fun.mk_le_mk MeasureTheory.AEEqFun.mk_le_mk

@[simp, norm_cast]
theorem coeFn_le [Preorder β] {f g : α →ₘ[μ] β} : (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
  liftRel_iff_coeFn.symm
#align measure_theory.ae_eq_fun.coe_fn_le MeasureTheory.AEEqFun.coeFn_le

instance instPartialOrder [PartialOrder β] : PartialOrder (α →ₘ[μ] β) :=
  PartialOrder.lift toGerm toGerm_injective
#align measure_theory.ae_eq_fun.partial_order MeasureTheory.AEEqFun.instPartialOrder

section Lattice

section Sup

variable [SemilatticeSup β] [ContinuousSup β]

instance instSup : Sup (α →ₘ[μ] β) where sup f g := AEEqFun.comp₂ (· ⊔ ·) continuous_sup f g
#align measure_theory.ae_eq_fun.has_sup MeasureTheory.AEEqFun.instSup

theorem coeFn_sup (f g : α →ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_sup MeasureTheory.AEEqFun.coeFn_sup

protected theorem le_sup_left (f g : α →ₘ[μ] β) : f ≤ f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_left
#align measure_theory.ae_eq_fun.le_sup_left MeasureTheory.AEEqFun.le_sup_left

protected theorem le_sup_right (f g : α →ₘ[μ] β) : g ≤ f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_right
#align measure_theory.ae_eq_fun.le_sup_right MeasureTheory.AEEqFun.le_sup_right

protected theorem sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_sup f g] with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag
#align measure_theory.ae_eq_fun.sup_le MeasureTheory.AEEqFun.sup_le

end Sup

section Inf

variable [SemilatticeInf β] [ContinuousInf β]

instance instInf : Inf (α →ₘ[μ] β) where inf f g := AEEqFun.comp₂ (· ⊓ ·) continuous_inf f g
#align measure_theory.ae_eq_fun.has_inf MeasureTheory.AEEqFun.instInf

theorem coeFn_inf (f g : α →ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_inf MeasureTheory.AEEqFun.coeFn_inf

protected theorem inf_le_left (f g : α →ₘ[μ] β) : f ⊓ g ≤ f := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_left
#align measure_theory.ae_eq_fun.inf_le_left MeasureTheory.AEEqFun.inf_le_left

protected theorem inf_le_right (f g : α →ₘ[μ] β) : f ⊓ g ≤ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_right
#align measure_theory.ae_eq_fun.inf_le_right MeasureTheory.AEEqFun.inf_le_right

protected theorem le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_inf f g] with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag
#align measure_theory.ae_eq_fun.le_inf MeasureTheory.AEEqFun.le_inf

end Inf

instance instLattice [Lattice β] [TopologicalLattice β] : Lattice (α →ₘ[μ] β) :=
  { AEEqFun.instPartialOrder with
    sup := Sup.sup
    le_sup_left := AEEqFun.le_sup_left
    le_sup_right := AEEqFun.le_sup_right
    sup_le := AEEqFun.sup_le
    inf := Inf.inf
    inf_le_left := AEEqFun.inf_le_left
    inf_le_right := AEEqFun.inf_le_right
    le_inf := AEEqFun.le_inf }
#align measure_theory.ae_eq_fun.lattice MeasureTheory.AEEqFun.instLattice

end Lattice

end Order

variable (α)

/-- The equivalence class of a constant function: `[fun _ : α => b]`, based on the equivalence
relation of being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β :=
  mk (fun _ : α ↦ b) aestronglyMeasurable_const
#align measure_theory.ae_eq_fun.const MeasureTheory.AEEqFun.const

theorem coeFn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coeFn_mk _ _
#align measure_theory.ae_eq_fun.coe_fn_const MeasureTheory.AEEqFun.coeFn_const

/-- If the measure is nonzero, we can strengthen `coeFn_const` to get an equality. -/
theorem coeFn_const_eq [NeZero μ] (b : β) (x : α) : (const α b : α →ₘ[μ] β) x = b := by
  simp only [cast]
  have h : cast.Cond (const α b : α →ₘ[μ] β) :=
    ⟨(fun _ : α ↦ b), stronglyMeasurable_const, rfl, ⟨b, rfl⟩⟩
  rw [dif_pos h]
  obtain ⟨hf, h2f, c', h3f⟩ := Classical.choose_spec h
  nth_rw 1 [const] at h2f
  rw [mk_eq_mk, ← h3f, EventuallyEq, ← const_def] at h2f
  simp only [eventually_const] at h2f
  rw [← h3f, h2f, Function.const]

variable {α}

instance instInhabited [Inhabited β] : Inhabited (α →ₘ[μ] β) :=
  ⟨const α default⟩
#align measure_theory.ae_eq_fun.inhabited MeasureTheory.AEEqFun.instInhabited

@[to_additive]
instance instOne [One β] : One (α →ₘ[μ] β) :=
  ⟨const α 1⟩
#align measure_theory.ae_eq_fun.has_one MeasureTheory.AEEqFun.instOne
#align measure_theory.ae_eq_fun.has_zero MeasureTheory.AEEqFun.instZero

@[to_additive]
theorem one_def [One β] : (1 : α →ₘ[μ] β) = mk (fun _ : α => 1) aestronglyMeasurable_const :=
  rfl
#align measure_theory.ae_eq_fun.one_def MeasureTheory.AEEqFun.one_def
#align measure_theory.ae_eq_fun.zero_def MeasureTheory.AEEqFun.zero_def

@[to_additive]
theorem coeFn_one [One β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 :=
  coeFn_const ..
#align measure_theory.ae_eq_fun.coe_fn_one MeasureTheory.AEEqFun.coeFn_one
#align measure_theory.ae_eq_fun.coe_fn_zero MeasureTheory.AEEqFun.coeFn_zero

@[to_additive (attr := simp)]
theorem coeFn_one_eq [NeZero μ] [One β] {x : α} : (1 : α →ₘ[μ] β) x = 1 :=
  coeFn_const_eq ..

@[to_additive (attr := simp)]
theorem one_toGerm [One β] : (1 : α →ₘ[μ] β).toGerm = 1 :=
  rfl
#align measure_theory.ae_eq_fun.one_to_germ MeasureTheory.AEEqFun.one_toGerm
#align measure_theory.ae_eq_fun.zero_to_germ MeasureTheory.AEEqFun.zero_toGerm

-- Note we set up the scalar actions before the `Monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section SMul

variable {𝕜 𝕜' : Type*}
variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]
variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]

instance instSMul : SMul 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩
#align measure_theory.ae_eq_fun.has_smul MeasureTheory.AEEqFun.instSMul

@[simp]
theorem smul_mk (c : 𝕜) (f : α → γ) (hf : AEStronglyMeasurable f μ) :
    c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl
#align measure_theory.ae_eq_fun.smul_mk MeasureTheory.AEEqFun.smul_mk

theorem coeFn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_smul MeasureTheory.AEEqFun.coeFn_smul

theorem smul_toGerm (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.smul_to_germ MeasureTheory.AEEqFun.smul_toGerm

instance instSMulCommClass [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩
#align measure_theory.ae_eq_fun.smul_comm_class MeasureTheory.AEEqFun.instSMulCommClass

instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩
#align measure_theory.ae_eq_fun.is_scalar_tower MeasureTheory.AEEqFun.instIsScalarTower

instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩
#align measure_theory.ae_eq_fun.is_central_scalar MeasureTheory.AEEqFun.instIsCentralScalar

end SMul

section Mul

variable [Mul γ] [ContinuousMul γ]

@[to_additive]
instance instMul : Mul (α →ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩
#align measure_theory.ae_eq_fun.has_mul MeasureTheory.AEEqFun.instMul
#align measure_theory.ae_eq_fun.has_add MeasureTheory.AEEqFun.instAdd

@[to_additive (attr := simp)]
theorem mk_mul_mk (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    (mk f hf : α →ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl
#align measure_theory.ae_eq_fun.mk_mul_mk MeasureTheory.AEEqFun.mk_mul_mk
#align measure_theory.ae_eq_fun.mk_add_mk MeasureTheory.AEEqFun.mk_add_mk

@[to_additive]
theorem coeFn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_mul MeasureTheory.AEEqFun.coeFn_mul
#align measure_theory.ae_eq_fun.coe_fn_add MeasureTheory.AEEqFun.coeFn_add

@[to_additive (attr := simp)]
theorem mul_toGerm (f g : α →ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _
#align measure_theory.ae_eq_fun.mul_to_germ MeasureTheory.AEEqFun.mul_toGerm
#align measure_theory.ae_eq_fun.add_to_germ MeasureTheory.AEEqFun.add_toGerm

end Mul

instance instAddMonoid [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _
#align measure_theory.ae_eq_fun.add_monoid MeasureTheory.AEEqFun.instAddMonoid

instance instAddCommMonoid [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _
#align measure_theory.ae_eq_fun.add_comm_monoid MeasureTheory.AEEqFun.instAddCommMonoid

section Monoid

variable [Monoid γ] [ContinuousMul γ]

instance instPowNat : Pow (α →ₘ[μ] γ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩
#align measure_theory.ae_eq_fun.nat.has_pow MeasureTheory.AEEqFun.instPowNat

@[simp]
theorem mk_pow (f : α → γ) (hf) (n : ℕ) :
    (mk f hf : α →ₘ[μ] γ) ^ n =
      mk (f ^ n) ((_root_.continuous_pow n).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.mk_pow MeasureTheory.AEEqFun.mk_pow

theorem coeFn_pow (f : α →ₘ[μ] γ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_pow MeasureTheory.AEEqFun.coeFn_pow

@[simp]
theorem pow_toGerm (f : α →ₘ[μ] γ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.pow_to_germ MeasureTheory.AEEqFun.pow_toGerm

@[to_additive existing]
instance instMonoid : Monoid (α →ₘ[μ] γ) :=
  toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm
#align measure_theory.ae_eq_fun.monoid MeasureTheory.AEEqFun.instMonoid

/-- `AEEqFun.toGerm` as a `MonoidHom`. -/
@[to_additive (attr := simps) "`AEEqFun.toGerm` as an `AddMonoidHom`."]
def toGermMonoidHom : (α →ₘ[μ] γ) →* (ae μ).Germ γ where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm
#align measure_theory.ae_eq_fun.to_germ_monoid_hom MeasureTheory.AEEqFun.toGermMonoidHom
#align measure_theory.ae_eq_fun.to_germ_monoid_hom_apply MeasureTheory.AEEqFun.toGermMonoidHom_apply
#align measure_theory.ae_eq_fun.to_germ_add_monoid_hom MeasureTheory.AEEqFun.toGermAddMonoidHom
#align measure_theory.ae_eq_fun.to_germ_add_monoid_hom_apply MeasureTheory.AEEqFun.toGermAddMonoidHom_apply

end Monoid

@[to_additive existing]
instance instCommMonoid [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm
#align measure_theory.ae_eq_fun.comm_monoid MeasureTheory.AEEqFun.instCommMonoid

section Group

variable [Group γ] [TopologicalGroup γ]

section Inv

@[to_additive]
instance instInv : Inv (α →ₘ[μ] γ) :=
  ⟨comp Inv.inv continuous_inv⟩
#align measure_theory.ae_eq_fun.has_inv MeasureTheory.AEEqFun.instInv
#align measure_theory.ae_eq_fun.has_neg MeasureTheory.AEEqFun.instNeg

@[to_additive (attr := simp)]
theorem inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl
#align measure_theory.ae_eq_fun.inv_mk MeasureTheory.AEEqFun.inv_mk
#align measure_theory.ae_eq_fun.neg_mk MeasureTheory.AEEqFun.neg_mk

@[to_additive]
theorem coeFn_inv (f : α →ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_inv MeasureTheory.AEEqFun.coeFn_inv
#align measure_theory.ae_eq_fun.coe_fn_neg MeasureTheory.AEEqFun.coeFn_neg

@[to_additive]
theorem inv_toGerm (f : α →ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.inv_to_germ MeasureTheory.AEEqFun.inv_toGerm
#align measure_theory.ae_eq_fun.neg_to_germ MeasureTheory.AEEqFun.neg_toGerm

end Inv

section Div

@[to_additive]
instance instDiv : Div (α →ₘ[μ] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩
#align measure_theory.ae_eq_fun.has_div MeasureTheory.AEEqFun.instDiv
#align measure_theory.ae_eq_fun.has_sub MeasureTheory.AEEqFun.instSub

@[to_additive (attr := simp, nolint simpNF)] -- Porting note: LHS does not simplify.
theorem mk_div (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (f / g) (hf.div hg) = (mk f hf : α →ₘ[μ] γ) / mk g hg :=
  rfl
#align measure_theory.ae_eq_fun.mk_div MeasureTheory.AEEqFun.mk_div
#align measure_theory.ae_eq_fun.mk_sub MeasureTheory.AEEqFun.mk_sub

@[to_additive]
theorem coeFn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_div MeasureTheory.AEEqFun.coeFn_div
#align measure_theory.ae_eq_fun.coe_fn_sub MeasureTheory.AEEqFun.coeFn_sub

@[to_additive]
theorem div_toGerm (f g : α →ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _
#align measure_theory.ae_eq_fun.div_to_germ MeasureTheory.AEEqFun.div_toGerm
#align measure_theory.ae_eq_fun.sub_to_germ MeasureTheory.AEEqFun.sub_toGerm

end Div

section ZPow

instance instPowInt : Pow (α →ₘ[μ] γ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩
#align measure_theory.ae_eq_fun.has_int_pow MeasureTheory.AEEqFun.instPowInt

@[simp]
theorem mk_zpow (f : α → γ) (hf) (n : ℤ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.mk_zpow MeasureTheory.AEEqFun.mk_zpow

theorem coeFn_zpow (f : α →ₘ[μ] γ) (n : ℤ) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_zpow MeasureTheory.AEEqFun.coeFn_zpow

@[simp]
theorem zpow_toGerm (f : α →ₘ[μ] γ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.zpow_to_germ MeasureTheory.AEEqFun.zpow_toGerm

end ZPow

end Group

instance instAddGroup [AddGroup γ] [TopologicalAddGroup γ] : AddGroup (α →ₘ[μ] γ) :=
  toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _
#align measure_theory.ae_eq_fun.add_group MeasureTheory.AEEqFun.instAddGroup

instance instAddCommGroup [AddCommGroup γ] [TopologicalAddGroup γ] : AddCommGroup (α →ₘ[μ] γ) :=
  { add_comm := add_comm }
#align measure_theory.ae_eq_fun.add_comm_group MeasureTheory.AEEqFun.instAddCommGroup

@[to_additive existing]
instance instGroup [Group γ] [TopologicalGroup γ] : Group (α →ₘ[μ] γ) :=
  toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm
#align measure_theory.ae_eq_fun.group MeasureTheory.AEEqFun.instGroup

@[to_additive existing]
instance instCommGroup [CommGroup γ] [TopologicalGroup γ] : CommGroup (α →ₘ[μ] γ) :=
  { mul_comm := mul_comm }
#align measure_theory.ae_eq_fun.comm_group MeasureTheory.AEEqFun.instCommGroup

section Module

variable {𝕜 : Type*}

instance instMulAction [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    MulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.mulAction toGerm smul_toGerm
#align measure_theory.ae_eq_fun.mul_action MeasureTheory.AEEqFun.instMulAction

instance instDistribMulAction [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.distribMulAction (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) fun c : 𝕜 =>
    smul_toGerm c
#align measure_theory.ae_eq_fun.distrib_mul_action MeasureTheory.AEEqFun.instDistribMulAction

instance instModule [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : Module 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.module 𝕜 (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) smul_toGerm
#align measure_theory.ae_eq_fun.module MeasureTheory.AEEqFun.instModule

end Module

open ENNReal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
  Quotient.liftOn' f (fun f => ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) fun _ _ => lintegral_congr_ae
#align measure_theory.ae_eq_fun.lintegral MeasureTheory.AEEqFun.lintegral

@[simp]
theorem lintegral_mk (f : α → ℝ≥0∞) (hf) : (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl
#align measure_theory.ae_eq_fun.lintegral_mk MeasureTheory.AEEqFun.lintegral_mk

theorem lintegral_coeFn (f : α →ₘ[μ] ℝ≥0∞) : ∫⁻ a, f a ∂μ = f.lintegral := by
  rw [← lintegral_mk, mk_coeFn]
#align measure_theory.ae_eq_fun.lintegral_coe_fn MeasureTheory.AEEqFun.lintegral_coeFn

@[simp]
nonrec theorem lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 :=
  lintegral_zero
#align measure_theory.ae_eq_fun.lintegral_zero MeasureTheory.AEEqFun.lintegral_zero

@[simp]
theorem lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
  induction_on f fun _f hf => (lintegral_eq_zero_iff' hf.aemeasurable).trans mk_eq_mk.symm
#align measure_theory.ae_eq_fun.lintegral_eq_zero_iff MeasureTheory.AEEqFun.lintegral_eq_zero_iff

theorem lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  induction_on₂ f g fun f hf g _ => by simp [lintegral_add_left' hf.aemeasurable]
#align measure_theory.ae_eq_fun.lintegral_add MeasureTheory.AEEqFun.lintegral_add

theorem lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
  induction_on₂ f g fun _f _ _g _ hfg => lintegral_mono_ae hfg
#align measure_theory.ae_eq_fun.lintegral_mono MeasureTheory.AEEqFun.lintegral_mono

section Abs

theorem coeFn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroup β]
    [TopologicalAddGroup β] (f : α →ₘ[μ] β) : ⇑|f| =ᵐ[μ] fun x => |f x| := by
  simp_rw [abs]
  filter_upwards [AEEqFun.coeFn_sup f (-f), AEEqFun.coeFn_neg f] with x hx_sup hx_neg
  rw [hx_sup, hx_neg, Pi.neg_apply]
#align measure_theory.ae_eq_fun.coe_fn_abs MeasureTheory.AEEqFun.coeFn_abs

end Abs

section PosPart

variable [LinearOrder γ] [OrderClosedTopology γ] [Zero γ]

/-- Positive part of an `AEEqFun`. -/
def posPart (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
  comp (fun x => max x 0) (continuous_id.max continuous_const) f
#align measure_theory.ae_eq_fun.pos_part MeasureTheory.AEEqFun.posPart

@[simp]
theorem posPart_mk (f : α → γ) (hf) :
    posPart (mk f hf : α →ₘ[μ] γ) =
      mk (fun x => max (f x) 0)
        ((continuous_id.max continuous_const).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.pos_part_mk MeasureTheory.AEEqFun.posPart_mk

theorem coeFn_posPart (f : α →ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_pos_part MeasureTheory.AEEqFun.coeFn_posPart

end PosPart

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
#align continuous_map.to_ae_eq_fun ContinuousMap.toAEEqFun

theorem coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqFun μ =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _
#align continuous_map.coe_fn_to_ae_eq_fun ContinuousMap.coeFn_toAEEqFun

variable [Group β] [TopologicalGroup β]

/-- The `MulHom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive "The `AddHom` from the group of continuous maps from `α` to `β` to the group of
equivalence classes of `μ`-almost-everywhere measurable functions."]
def toAEEqFunMulHom : C(α, β) →* α →ₘ[μ] β where
  toFun := ContinuousMap.toAEEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AEEqFun.mk_mul_mk _ _ f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable
#align continuous_map.to_ae_eq_fun_mul_hom ContinuousMap.toAEEqFunMulHom
#align continuous_map.to_ae_eq_fun_add_hom ContinuousMap.toAEEqFunAddHom

variable {𝕜 : Type*} [Semiring 𝕜]
variable [TopologicalSpace γ] [PseudoMetrizableSpace γ] [AddCommGroup γ] [Module 𝕜 γ]
  [TopologicalAddGroup γ] [ContinuousConstSMul 𝕜 γ] [SecondCountableTopologyEither α γ]

/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
def toAEEqFunLinearMap : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
  { toAEEqFunAddHom μ with
    map_smul' := fun c f => AEEqFun.smul_mk c f f.continuous.aestronglyMeasurable }
#align continuous_map.to_ae_eq_fun_linear_map ContinuousMap.toAEEqFunLinearMap

end ContinuousMap

-- Guard against import creep
assert_not_exists InnerProductSpace
