/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou

! This file was ported from Lean 3 source module measure_theory.function.ae_eq_fun
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Integral.Lebesgue
import Mathbin.Order.Filter.Germ
import Mathbin.Topology.ContinuousFunction.Algebra
import Mathbin.MeasureTheory.Function.StronglyMeasurable.Basic

/-!

# Almost everywhere equal functions

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `l1_space.lean` for `L¹` space.

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
        `add_to_fun`, `neg_to_fun`, `sub_to_fun`, `smul_to_fun`

* The order structure of `L⁰` :
    `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
    And `α →ₘ β` inherits the preorder and partial order of `β`.

    TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
    linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.to_fun`     : To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.to_fun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `ae_eq_fun.mk` : To constructs an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`         : Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `comp_measurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`        : Use `comp₂ g f₁ f₂ to get `[λ a, g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/


noncomputable section

open Classical ENNReal Topology

open Set Filter TopologicalSpace ENNReal Emetric MeasureTheory Function

variable {α β γ δ : Type _} [MeasurableSpace α] {μ ν : Measure α}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]

variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
def Measure.aeEqSetoid (μ : Measure α) : Setoid { f : α → β // AEStronglyMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun f => ae_eq_refl f, fun f g => ae_eq_symm, fun f g h =>
    ae_eq_trans⟩
#align measure_theory.measure.ae_eq_setoid MeasureTheory.Measure.aeEqSetoid

variable (α)

/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
    strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
    they differ on a set of measure `0`.  -/
def AeEqFun (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid β)
#align measure_theory.ae_eq_fun MeasureTheory.AeEqFun

variable {α β}

-- mathport name: «expr →ₘ[ ] »
notation:25 α " →ₘ[" μ "] " β => AeEqFun α β μ

end MeasurableSpace

namespace AeEqFun

variable [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
    on the equivalence relation of being almost everywhere equal. -/
def mk {β : Type _} [TopologicalSpace β] (f : α → β) (hf : AEStronglyMeasurable f μ) : α →ₘ[μ] β :=
  Quotient.mk'' ⟨f, hf⟩
#align measure_theory.ae_eq_fun.mk MeasureTheory.AeEqFun.mk

/-- A measurable representative of an `ae_eq_fun` [f] -/
instance : CoeFun (α →ₘ[μ] β) fun _ => α → β :=
  ⟨fun f =>
    AEStronglyMeasurable.mk _ (Quotient.out' f : { f : α → β // AEStronglyMeasurable f μ }).2⟩

protected theorem stronglyMeasurable (f : α →ₘ[μ] β) : StronglyMeasurable f :=
  AEStronglyMeasurable.stronglyMeasurable_mk _
#align measure_theory.ae_eq_fun.strongly_measurable MeasureTheory.AeEqFun.stronglyMeasurable

protected theorem aEStronglyMeasurable (f : α →ₘ[μ] β) : AEStronglyMeasurable f μ :=
  f.StronglyMeasurable.AEStronglyMeasurable
#align measure_theory.ae_eq_fun.ae_strongly_measurable MeasureTheory.AeEqFun.aEStronglyMeasurable

protected theorem measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : Measurable f :=
  AEStronglyMeasurable.measurable_mk _
#align measure_theory.ae_eq_fun.measurable MeasureTheory.AeEqFun.measurable

protected theorem aEMeasurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : AEMeasurable f μ :=
  f.Measurable.AEMeasurable
#align measure_theory.ae_eq_fun.ae_measurable MeasureTheory.AeEqFun.aEMeasurable

@[simp]
theorem quot_mk_eq_mk (f : α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
  rfl
#align measure_theory.ae_eq_fun.quot_mk_eq_mk MeasureTheory.AeEqFun.quot_mk_eq_mk

@[simp]
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotient.eq''
#align measure_theory.ae_eq_fun.mk_eq_mk MeasureTheory.AeEqFun.mk_eq_mk

@[simp]
theorem mk_coeFn (f : α →ₘ[μ] β) : mk f f.AEStronglyMeasurable = f :=
  by
  conv_rhs => rw [← Quotient.out_eq' f]
  set g : { f : α → β // ae_strongly_measurable f μ } := Quotient.out' f with hg
  have : g = ⟨g.1, g.2⟩ := Subtype.eq rfl
  rw [this, ← mk, mk_eq_mk]
  exact (ae_strongly_measurable.ae_eq_mk _).symm
#align measure_theory.ae_eq_fun.mk_coe_fn MeasureTheory.AeEqFun.mk_coeFn

@[ext]
theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coe_fn, ← g.mk_coe_fn, mk_eq_mk]
#align measure_theory.ae_eq_fun.ext MeasureTheory.AeEqFun.ext

theorem ext_iff {f g : α →ₘ[μ] β} : f = g ↔ f =ᵐ[μ] g :=
  ⟨fun h => by rw [h], fun h => ext h⟩
#align measure_theory.ae_eq_fun.ext_iff MeasureTheory.AeEqFun.ext_iff

theorem coeFn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f :=
  by
  apply (ae_strongly_measurable.ae_eq_mk _).symm.trans
  exact @Quotient.mk_out' _ (μ.ae_eq_setoid β) (⟨f, hf⟩ : { f // ae_strongly_measurable f μ })
#align measure_theory.ae_eq_fun.coe_fn_mk MeasureTheory.AeEqFun.coeFn_mk

@[elab_as_elim]
theorem induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H
#align measure_theory.ae_eq_fun.induction_on MeasureTheory.AeEqFun.induction_on

@[elab_as_elim]
theorem induction_on₂ {α' β' : Type _} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf
#align measure_theory.ae_eq_fun.induction_on₂ MeasureTheory.AeEqFun.induction_on₂

@[elab_as_elim]
theorem induction_on₃ {α' β' : Type _} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    {α'' β'' : Type _} [MeasurableSpace α''] [TopologicalSpace β''] {μ'' : Measure α''}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
    {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf
#align measure_theory.ae_eq_fun.induction_on₃ MeasureTheory.AeEqFun.induction_on₃

/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. -/
def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f (fun f => mk (g ∘ (f : α → β)) (hg.comp_aestronglyMeasurable f.2))
    fun f f' H => mk_eq_mk.2 <| H.fun_comp g
#align measure_theory.ae_eq_fun.comp MeasureTheory.AeEqFun.comp

@[simp]
theorem comp_mk (g : β → γ) (hg : Continuous g) (f : α → β) (hf) :
    comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.comp_mk MeasureTheory.AeEqFun.comp_mk

theorem comp_eq_mk (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable f.AEStronglyMeasurable) := by
  rw [← comp_mk g hg f f.ae_strongly_measurable, mk_coe_fn]
#align measure_theory.ae_eq_fun.comp_eq_mk MeasureTheory.AeEqFun.comp_eq_mk

theorem coeFn_comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f :=
  by
  rw [comp_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp MeasureTheory.AeEqFun.coeFn_comp

section CompMeasurable

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [MeasurableSpace γ]
  [PseudoMetrizableSpace γ] [OpensMeasurableSpace γ] [SecondCountableTopology γ]

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
    return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
    `[g ∘ f] : α →ₘ γ`. This requires that `γ` has a second countable topology. -/
def compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f
    (fun f' => mk (g ∘ (f' : α → β)) (hg.comp_aemeasurable f'.2.AEMeasurable).AEStronglyMeasurable)
    fun f f' H => mk_eq_mk.2 <| H.fun_comp g
#align measure_theory.ae_eq_fun.comp_measurable MeasureTheory.AeEqFun.compMeasurable

@[simp]
theorem compMeasurable_mk (g : β → γ) (hg : Measurable g) (f : α → β)
    (hf : AEStronglyMeasurable f μ) :
    compMeasurable g hg (mk f hf : α →ₘ[μ] β) =
      mk (g ∘ f) (hg.comp_aemeasurable hf.AEMeasurable).AEStronglyMeasurable :=
  rfl
#align measure_theory.ae_eq_fun.comp_measurable_mk MeasureTheory.AeEqFun.compMeasurable_mk

theorem compMeasurable_eq_mk (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f = mk (g ∘ f) (hg.comp_aemeasurable f.AEMeasurable).AEStronglyMeasurable :=
  by rw [← comp_measurable_mk g hg f f.ae_strongly_measurable, mk_coe_fn]
#align measure_theory.ae_eq_fun.comp_measurable_eq_mk MeasureTheory.AeEqFun.compMeasurable_eq_mk

theorem coeFn_compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =ᵐ[μ] g ∘ f :=
  by
  rw [comp_measurable_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp_measurable MeasureTheory.AeEqFun.coeFn_compMeasurable

end CompMeasurable

/-- The class of `x ↦ (f x, g x)`. -/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prod_mk g.2))
    fun f g f' g' Hf Hg => mk_eq_mk.2 <| Hf.prod_mk Hg
#align measure_theory.ae_eq_fun.pair MeasureTheory.AeEqFun.pair

@[simp]
theorem pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
    (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prod_mk hg) :=
  rfl
#align measure_theory.ae_eq_fun.pair_mk_mk MeasureTheory.AeEqFun.pair_mk_mk

theorem pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
    f.pair g = mk (fun x => (f x, g x)) (f.AEStronglyMeasurable.prod_mk g.AEStronglyMeasurable) :=
  by simp only [← pair_mk_mk, mk_coe_fn]
#align measure_theory.ae_eq_fun.pair_eq_mk MeasureTheory.AeEqFun.pair_eq_mk

theorem coeFn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) :=
  by
  rw [pair_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_pair MeasureTheory.AeEqFun.coeFn_pair

/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ` -/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    α →ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)
#align measure_theory.ae_eq_fun.comp₂ MeasureTheory.AeEqFun.comp₂

@[simp]
theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_aestronglyMeasurable (hf₁.prod_mk hf₂)) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_mk_mk MeasureTheory.AeEqFun.comp₂_mk_mk

theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_eq_pair MeasureTheory.AeEqFun.comp₂_eq_pair

theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) :
    comp₂ g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aestronglyMeasurable (f₁.AEStronglyMeasurable.prod_mk f₂.AEStronglyMeasurable)) :=
  by rw [comp₂_eq_pair, pair_eq_mk, comp_mk] <;> rfl
#align measure_theory.ae_eq_fun.comp₂_eq_mk MeasureTheory.AeEqFun.comp₂_eq_mk

theorem coeFn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) :=
  by
  rw [comp₂_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp₂ MeasureTheory.AeEqFun.coeFn_comp₂

section

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [SecondCountableTopology β]
  [MeasurableSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]
  [MeasurableSpace δ] [PseudoMetrizableSpace δ] [OpensMeasurableSpace δ] [SecondCountableTopology δ]

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
    `[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
    `λ a, g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
    `[λ a, g (f₁ a) (f₂ a)] : α →ₘ γ`. This requires `δ` to have second-countable topology. -/
def comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
  compMeasurable _ hg (f₁.pair f₂)
#align measure_theory.ae_eq_fun.comp₂_measurable MeasureTheory.AeEqFun.comp₂Measurable

@[simp]
theorem comp₂Measurable_mk_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α → β)
    (f₂ : α → γ) (hf₁ hf₂) :
    comp₂Measurable g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (hf₁.AEMeasurable.prod_mk hf₂.AEMeasurable)).AEStronglyMeasurable :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_mk_mk MeasureTheory.AeEqFun.comp₂Measurable_mk_mk

theorem comp₂Measurable_eq_pair (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ = compMeasurable _ hg (f₁.pair f₂) :=
  rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_eq_pair MeasureTheory.AeEqFun.comp₂Measurable_eq_pair

theorem comp₂Measurable_eq_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (f₁.AEMeasurable.prod_mk f₂.AEMeasurable)).AEStronglyMeasurable :=
  by rw [comp₂_measurable_eq_pair, pair_eq_mk, comp_measurable_mk] <;> rfl
#align measure_theory.ae_eq_fun.comp₂_measurable_eq_mk MeasureTheory.AeEqFun.comp₂Measurable_eq_mk

theorem coeFn_comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) :=
  by
  rw [comp₂_measurable_eq_mk]
  apply coe_fn_mk
#align measure_theory.ae_eq_fun.coe_fn_comp₂_measurable MeasureTheory.AeEqFun.coeFn_comp₂Measurable

end

/-- Interpret `f : α →ₘ[μ] β` as a germ at `μ.ae` forgetting that `f` is almost everywhere
    strongly measurable. -/
def toGerm (f : α →ₘ[μ] β) : Germ μ.ae β :=
  Quotient.liftOn' f (fun f => ((f : α → β) : Germ μ.ae β)) fun f g H => Germ.coe_eq.2 H
#align measure_theory.ae_eq_fun.to_germ MeasureTheory.AeEqFun.toGerm

@[simp]
theorem mk_toGerm (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).toGerm = f :=
  rfl
#align measure_theory.ae_eq_fun.mk_to_germ MeasureTheory.AeEqFun.mk_toGerm

theorem toGerm_eq (f : α →ₘ[μ] β) : f.toGerm = (f : α → β) := by rw [← mk_to_germ, mk_coe_fn]
#align measure_theory.ae_eq_fun.to_germ_eq MeasureTheory.AeEqFun.toGerm_eq

theorem toGerm_injective : Injective (toGerm : (α →ₘ[μ] β) → Germ μ.ae β) := fun f g H =>
  ext <| Germ.coe_eq.1 <| by rwa [← to_germ_eq, ← to_germ_eq]
#align measure_theory.ae_eq_fun.to_germ_injective MeasureTheory.AeEqFun.toGerm_injective

theorem comp_toGerm (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    (comp g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f hf => by simp
#align measure_theory.ae_eq_fun.comp_to_germ MeasureTheory.AeEqFun.comp_toGerm

theorem compMeasurable_toGerm [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    (compMeasurable g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f hf => by simp
#align measure_theory.ae_eq_fun.comp_measurable_to_germ MeasureTheory.AeEqFun.compMeasurable_toGerm

theorem comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.zipWith g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ hf₁ f₂ hf₂ => by simp
#align measure_theory.ae_eq_fun.comp₂_to_germ MeasureTheory.AeEqFun.comp₂_toGerm

theorem comp₂Measurable_toGerm [PseudoMetrizableSpace β] [SecondCountableTopology β]
    [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace γ] [SecondCountableTopology γ]
    [MeasurableSpace γ] [BorelSpace γ] [PseudoMetrizableSpace δ] [SecondCountableTopology δ]
    [MeasurableSpace δ] [OpensMeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂Measurable g hg f₁ f₂).toGerm = f₁.toGerm.zipWith g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ hf₁ f₂ hf₂ => by simp
#align measure_theory.ae_eq_fun.comp₂_measurable_to_germ MeasureTheory.AeEqFun.comp₂Measurable_toGerm

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
    for almost all `a` -/
def LiftPred (p : β → Prop) (f : α →ₘ[μ] β) : Prop :=
  f.toGerm.LiftPred p
#align measure_theory.ae_eq_fun.lift_pred MeasureTheory.AeEqFun.LiftPred

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
    `(f a, g a)` for almost all `a` -/
def LiftRel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm
#align measure_theory.ae_eq_fun.lift_rel MeasureTheory.AeEqFun.LiftRel

theorem liftRel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
    LiftRel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl
#align measure_theory.ae_eq_fun.lift_rel_mk_mk MeasureTheory.AeEqFun.liftRel_mk_mk

theorem liftRel_iff_coeFn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
    LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) := by rw [← lift_rel_mk_mk, mk_coe_fn, mk_coe_fn]
#align measure_theory.ae_eq_fun.lift_rel_iff_coe_fn MeasureTheory.AeEqFun.liftRel_iff_coeFn

section Order

instance [Preorder β] : Preorder (α →ₘ[μ] β) :=
  Preorder.lift toGerm

@[simp]
theorem mk_le_mk [Preorder β] {f g : α → β} (hf hg) : (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
  Iff.rfl
#align measure_theory.ae_eq_fun.mk_le_mk MeasureTheory.AeEqFun.mk_le_mk

@[simp, norm_cast]
theorem coeFn_le [Preorder β] {f g : α →ₘ[μ] β} : (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
  liftRel_iff_coeFn.symm
#align measure_theory.ae_eq_fun.coe_fn_le MeasureTheory.AeEqFun.coeFn_le

instance [PartialOrder β] : PartialOrder (α →ₘ[μ] β) :=
  PartialOrder.lift toGerm toGerm_injective

section Lattice

section Sup

variable [SemilatticeSup β] [ContinuousSup β]

instance : Sup (α →ₘ[μ] β) where sup f g := AeEqFun.comp₂ (· ⊔ ·) continuous_sup f g

theorem coeFn_sup (f g : α →ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_sup MeasureTheory.AeEqFun.coeFn_sup

protected theorem le_sup_left (f g : α →ₘ[μ] β) : f ≤ f ⊔ g :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g]with _ ha
  rw [ha]
  exact le_sup_left
#align measure_theory.ae_eq_fun.le_sup_left MeasureTheory.AeEqFun.le_sup_left

protected theorem le_sup_right (f g : α →ₘ[μ] β) : g ≤ f ⊔ g :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_sup f g]with _ ha
  rw [ha]
  exact le_sup_right
#align measure_theory.ae_eq_fun.le_sup_right MeasureTheory.AeEqFun.le_sup_right

protected theorem sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' :=
  by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_sup f g]with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag
#align measure_theory.ae_eq_fun.sup_le MeasureTheory.AeEqFun.sup_le

end Sup

section Inf

variable [SemilatticeInf β] [ContinuousInf β]

instance : Inf (α →ₘ[μ] β) where inf f g := AeEqFun.comp₂ (· ⊓ ·) continuous_inf f g

theorem coeFn_inf (f g : α →ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_inf MeasureTheory.AeEqFun.coeFn_inf

protected theorem inf_le_left (f g : α →ₘ[μ] β) : f ⊓ g ≤ f :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g]with _ ha
  rw [ha]
  exact inf_le_left
#align measure_theory.ae_eq_fun.inf_le_left MeasureTheory.AeEqFun.inf_le_left

protected theorem inf_le_right (f g : α →ₘ[μ] β) : f ⊓ g ≤ g :=
  by
  rw [← coe_fn_le]
  filter_upwards [coe_fn_inf f g]with _ ha
  rw [ha]
  exact inf_le_right
#align measure_theory.ae_eq_fun.inf_le_right MeasureTheory.AeEqFun.inf_le_right

protected theorem le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g :=
  by
  rw [← coe_fn_le] at hf hg⊢
  filter_upwards [hf, hg, coe_fn_inf f g]with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag
#align measure_theory.ae_eq_fun.le_inf MeasureTheory.AeEqFun.le_inf

end Inf

instance [Lattice β] [TopologicalLattice β] : Lattice (α →ₘ[μ] β) :=
  { AeEqFun.partialOrder with
    sup := Sup.sup
    le_sup_left := AeEqFun.le_sup_left
    le_sup_right := AeEqFun.le_sup_right
    sup_le := AeEqFun.sup_le
    inf := Inf.inf
    inf_le_left := AeEqFun.inf_le_left
    inf_le_right := AeEqFun.inf_le_right
    le_inf := AeEqFun.le_inf }

end Lattice

end Order

variable (α)

/-- The equivalence class of a constant function: `[λ a:α, b]`, based on the equivalence relation of
    being almost everywhere equal -/
def const (b : β) : α →ₘ[μ] β :=
  mk (fun a : α => b) aestronglyMeasurable_const
#align measure_theory.ae_eq_fun.const MeasureTheory.AeEqFun.const

theorem coeFn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coeFn_mk _ _
#align measure_theory.ae_eq_fun.coe_fn_const MeasureTheory.AeEqFun.coeFn_const

variable {α}

instance [Inhabited β] : Inhabited (α →ₘ[μ] β) :=
  ⟨const α default⟩

@[to_additive]
instance [One β] : One (α →ₘ[μ] β) :=
  ⟨const α 1⟩

@[to_additive]
theorem one_def [One β] : (1 : α →ₘ[μ] β) = mk (fun a : α => 1) aestronglyMeasurable_const :=
  rfl
#align measure_theory.ae_eq_fun.one_def MeasureTheory.AeEqFun.one_def
#align measure_theory.ae_eq_fun.zero_def MeasureTheory.AeEqFun.zero_def

@[to_additive]
theorem coeFn_one [One β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 :=
  coeFn_const _ _
#align measure_theory.ae_eq_fun.coe_fn_one MeasureTheory.AeEqFun.coeFn_one
#align measure_theory.ae_eq_fun.coe_fn_zero MeasureTheory.AeEqFun.coeFn_zero

@[simp, to_additive]
theorem one_toGerm [One β] : (1 : α →ₘ[μ] β).toGerm = 1 :=
  rfl
#align measure_theory.ae_eq_fun.one_to_germ MeasureTheory.AeEqFun.one_toGerm
#align measure_theory.ae_eq_fun.zero_to_germ MeasureTheory.AeEqFun.zero_toGerm

-- Note we set up the scalar actions before the `monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section SMul

variable {𝕜 𝕜' : Type _}

variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]

variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]

instance : SMul 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun c f => comp ((· • ·) c) (continuous_id.const_smul c) f⟩

@[simp]
theorem smul_mk (c : 𝕜) (f : α → γ) (hf : AEStronglyMeasurable f μ) :
    c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl
#align measure_theory.ae_eq_fun.smul_mk MeasureTheory.AeEqFun.smul_mk

theorem coeFn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • f :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_smul MeasureTheory.AeEqFun.coeFn_smul

theorem smul_toGerm (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.smul_to_germ MeasureTheory.AeEqFun.smul_toGerm

instance [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩

instance [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩

instance [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

end SMul

section Mul

variable [Mul γ] [ContinuousMul γ]

@[to_additive]
instance : Mul (α →ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩

@[simp, to_additive]
theorem mk_mul_mk (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    (mk f hf : α →ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl
#align measure_theory.ae_eq_fun.mk_mul_mk MeasureTheory.AeEqFun.mk_mul_mk
#align measure_theory.ae_eq_fun.mk_add_mk MeasureTheory.AeEqFun.mk_add_mk

@[to_additive]
theorem coeFn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_mul MeasureTheory.AeEqFun.coeFn_mul
#align measure_theory.ae_eq_fun.coe_fn_add MeasureTheory.AeEqFun.coeFn_add

@[simp, to_additive]
theorem mul_toGerm (f g : α →ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _
#align measure_theory.ae_eq_fun.mul_to_germ MeasureTheory.AeEqFun.mul_toGerm
#align measure_theory.ae_eq_fun.add_to_germ MeasureTheory.AeEqFun.add_toGerm

end Mul

instance [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.AddMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

instance [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.AddCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

section Monoid

variable [Monoid γ] [ContinuousMul γ]

instance : Pow (α →ₘ[μ] γ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]
theorem mk_pow (f : α → γ) (hf) (n : ℕ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_pow n).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.mk_pow MeasureTheory.AeEqFun.mk_pow

theorem coeFn_pow (f : α →ₘ[μ] γ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_pow MeasureTheory.AeEqFun.coeFn_pow

@[simp]
theorem pow_toGerm (f : α →ₘ[μ] γ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.pow_to_germ MeasureTheory.AeEqFun.pow_toGerm

@[to_additive]
instance : Monoid (α →ₘ[μ] γ) :=
  toGerm_injective.Monoid toGerm one_toGerm mul_toGerm pow_toGerm

/-- `ae_eq_fun.to_germ` as a `monoid_hom`. -/
@[to_additive "`ae_eq_fun.to_germ` as an `add_monoid_hom`.", simps]
def toGermMonoidHom : (α →ₘ[μ] γ) →* μ.ae.Germ γ
    where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm
#align measure_theory.ae_eq_fun.to_germ_monoid_hom MeasureTheory.AeEqFun.toGermMonoidHom
#align measure_theory.ae_eq_fun.to_germ_add_monoid_hom MeasureTheory.AeEqFun.toGermAddMonoidHom

end Monoid

@[to_additive]
instance [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.CommMonoid toGerm one_toGerm mul_toGerm pow_toGerm

section Group

variable [Group γ] [TopologicalGroup γ]

section Inv

@[to_additive]
instance : Inv (α →ₘ[μ] γ) :=
  ⟨comp Inv.inv continuous_inv⟩

@[simp, to_additive]
theorem inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl
#align measure_theory.ae_eq_fun.inv_mk MeasureTheory.AeEqFun.inv_mk
#align measure_theory.ae_eq_fun.neg_mk MeasureTheory.AeEqFun.neg_mk

@[to_additive]
theorem coeFn_inv (f : α →ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_inv MeasureTheory.AeEqFun.coeFn_inv
#align measure_theory.ae_eq_fun.coe_fn_neg MeasureTheory.AeEqFun.coeFn_neg

@[to_additive]
theorem inv_toGerm (f : α →ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.inv_to_germ MeasureTheory.AeEqFun.inv_toGerm
#align measure_theory.ae_eq_fun.neg_to_germ MeasureTheory.AeEqFun.neg_toGerm

end Inv

section Div

@[to_additive]
instance : Div (α →ₘ[μ] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩

@[simp, to_additive]
theorem mk_div (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (f / g) (hf.div hg) = (mk f hf : α →ₘ[μ] γ) / mk g hg :=
  rfl
#align measure_theory.ae_eq_fun.mk_div MeasureTheory.AeEqFun.mk_div
#align measure_theory.ae_eq_fun.mk_sub MeasureTheory.AeEqFun.mk_sub

@[to_additive]
theorem coeFn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coeFn_comp₂ _ _ _ _
#align measure_theory.ae_eq_fun.coe_fn_div MeasureTheory.AeEqFun.coeFn_div
#align measure_theory.ae_eq_fun.coe_fn_sub MeasureTheory.AeEqFun.coeFn_sub

@[to_additive]
theorem div_toGerm (f g : α →ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _
#align measure_theory.ae_eq_fun.div_to_germ MeasureTheory.AeEqFun.div_toGerm
#align measure_theory.ae_eq_fun.sub_to_germ MeasureTheory.AeEqFun.sub_toGerm

end Div

section Zpow

instance hasIntPow : Pow (α →ₘ[μ] γ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩
#align measure_theory.ae_eq_fun.has_int_pow MeasureTheory.AeEqFun.hasIntPow

@[simp]
theorem mk_zpow (f : α → γ) (hf) (n : ℤ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.mk_zpow MeasureTheory.AeEqFun.mk_zpow

theorem coeFn_zpow (f : α →ₘ[μ] γ) (n : ℤ) : ⇑(f ^ n) =ᵐ[μ] f ^ n :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_zpow MeasureTheory.AeEqFun.coeFn_zpow

@[simp]
theorem zpow_toGerm (f : α →ₘ[μ] γ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _
#align measure_theory.ae_eq_fun.zpow_to_germ MeasureTheory.AeEqFun.zpow_toGerm

end Zpow

end Group

instance [AddGroup γ] [TopologicalAddGroup γ] : AddGroup (α →ₘ[μ] γ) :=
  toGerm_injective.AddGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

instance [AddCommGroup γ] [TopologicalAddGroup γ] : AddCommGroup (α →ₘ[μ] γ) :=
  toGerm_injective.AddCommGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _

@[to_additive]
instance [Group γ] [TopologicalGroup γ] : Group (α →ₘ[μ] γ) :=
  toGerm_injective.Group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive]
instance [CommGroup γ] [TopologicalGroup γ] : CommGroup (α →ₘ[μ] γ) :=
  toGerm_injective.CommGroup _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

section Module

variable {𝕜 : Type _}

instance [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] : MulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.MulAction toGerm smul_toGerm

instance [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.DistribMulAction (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) fun c : 𝕜 =>
    smul_toGerm c

instance [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    Module 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.Module 𝕜 (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) smul_toGerm

end Module

open ENNReal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
  Quotient.liftOn' f (fun f => ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) fun f g => lintegral_congr_ae
#align measure_theory.ae_eq_fun.lintegral MeasureTheory.AeEqFun.lintegral

@[simp]
theorem lintegral_mk (f : α → ℝ≥0∞) (hf) : (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl
#align measure_theory.ae_eq_fun.lintegral_mk MeasureTheory.AeEqFun.lintegral_mk

theorem lintegral_coeFn (f : α →ₘ[μ] ℝ≥0∞) : (∫⁻ a, f a ∂μ) = f.lintegral := by
  rw [← lintegral_mk, mk_coe_fn]
#align measure_theory.ae_eq_fun.lintegral_coe_fn MeasureTheory.AeEqFun.lintegral_coeFn

@[simp]
theorem lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 :=
  lintegral_zero
#align measure_theory.ae_eq_fun.lintegral_zero MeasureTheory.AeEqFun.lintegral_zero

@[simp]
theorem lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
  induction_on f fun f hf => (lintegral_eq_zero_iff' hf.AEMeasurable).trans mk_eq_mk.symm
#align measure_theory.ae_eq_fun.lintegral_eq_zero_iff MeasureTheory.AeEqFun.lintegral_eq_zero_iff

theorem lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  induction_on₂ f g fun f hf g hg => by simp [lintegral_add_left' hf.ae_measurable]
#align measure_theory.ae_eq_fun.lintegral_add MeasureTheory.AeEqFun.lintegral_add

theorem lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
  induction_on₂ f g fun f hf g hg hfg => lintegral_mono_ae hfg
#align measure_theory.ae_eq_fun.lintegral_mono MeasureTheory.AeEqFun.lintegral_mono

section Abs

theorem coeFn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroup β]
    [TopologicalAddGroup β] (f : α →ₘ[μ] β) : ⇑(|f|) =ᵐ[μ] fun x => |f x| :=
  by
  simp_rw [abs_eq_sup_neg]
  filter_upwards [ae_eq_fun.coe_fn_sup f (-f), ae_eq_fun.coe_fn_neg f]with x hx_sup hx_neg
  rw [hx_sup, hx_neg, Pi.neg_apply]
#align measure_theory.ae_eq_fun.coe_fn_abs MeasureTheory.AeEqFun.coeFn_abs

end Abs

section PosPart

variable [LinearOrder γ] [OrderClosedTopology γ] [Zero γ]

/-- Positive part of an `ae_eq_fun`. -/
def posPart (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
  comp (fun x => max x 0) (continuous_id.max continuous_const) f
#align measure_theory.ae_eq_fun.pos_part MeasureTheory.AeEqFun.posPart

@[simp]
theorem posPart_mk (f : α → γ) (hf) :
    posPart (mk f hf : α →ₘ[μ] γ) =
      mk (fun x => max (f x) 0)
        ((continuous_id.max continuous_const).comp_aestronglyMeasurable hf) :=
  rfl
#align measure_theory.ae_eq_fun.pos_part_mk MeasureTheory.AeEqFun.posPart_mk

theorem coeFn_posPart (f : α →ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  coeFn_comp _ _ _
#align measure_theory.ae_eq_fun.coe_fn_pos_part MeasureTheory.AeEqFun.coeFn_posPart

end PosPart

end AeEqFun

end MeasureTheory

namespace ContinuousMap

open MeasureTheory

variable [TopologicalSpace α] [BorelSpace α] (μ)

variable [TopologicalSpace β] [SecondCountableTopologyEither α β] [PseudoMetrizableSpace β]

/-- The equivalence class of `μ`-almost-everywhere measurable functions associated to a continuous
map. -/
def toAeEqFun (f : C(α, β)) : α →ₘ[μ] β :=
  AeEqFun.mk f f.Continuous.AEStronglyMeasurable
#align continuous_map.to_ae_eq_fun ContinuousMap.toAeEqFun

theorem coeFn_toAeEqFun (f : C(α, β)) : f.toAeEqFun μ =ᵐ[μ] f :=
  AeEqFun.coeFn_mk f _
#align continuous_map.coe_fn_to_ae_eq_fun ContinuousMap.coeFn_toAeEqFun

variable [Group β] [TopologicalGroup β]

/-- The `mul_hom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive
      "The `add_hom` from the group of continuous maps from `α` to `β` to the group of\nequivalence classes of `μ`-almost-everywhere measurable functions."]
def toAeEqFunMulHom : C(α, β) →* α →ₘ[μ] β
    where
  toFun := ContinuousMap.toAeEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AeEqFun.mk_mul_mk _ _ f.Continuous.AEStronglyMeasurable g.Continuous.AEStronglyMeasurable
#align continuous_map.to_ae_eq_fun_mul_hom ContinuousMap.toAeEqFunMulHom
#align continuous_map.to_ae_eq_fun_add_hom ContinuousMap.toAeEqFunAddHom

variable {𝕜 : Type _} [Semiring 𝕜]

variable [TopologicalSpace γ] [PseudoMetrizableSpace γ] [AddCommGroup γ] [Module 𝕜 γ]
  [TopologicalAddGroup γ] [ContinuousConstSMul 𝕜 γ] [SecondCountableTopologyEither α γ]

/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
def toAeEqFunLinearMap : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
  { toAeEqFunAddHom μ with
    map_smul' := fun c f => AeEqFun.smul_mk c f f.Continuous.AEStronglyMeasurable }
#align continuous_map.to_ae_eq_fun_linear_map ContinuousMap.toAeEqFunLinearMap

end ContinuousMap

-- Guard against import creep
assert_not_exists inner_product_space

