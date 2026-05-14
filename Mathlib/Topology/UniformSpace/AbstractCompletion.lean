/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.UniformSpace.Equiv
public import Mathlib.Topology.Continuous
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Abstract theory of Hausdorff completions of uniform spaces

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induces the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion; it only studies consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `Topology/UniformSpace/CompareReals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `UniformSpace/Completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `UniformSpace/UniformSpaceCat` for the category packaging.

## Implementation notes

A tiny technical advantage of using a characteristic predicate such as the properties listed in
`AbstractCompletion` instead of stating the universal property is that the universal property
derived from the predicate is more universe polymorphic.

## References

We don't know any traditional text discussing this. Real world mathematics simply silently
identify the results of any two constructions that lead to something one could reasonably
call a completion.

## Tags

uniform spaces, completion, universal property
-/

@[expose] public section


noncomputable section

open Filter Set Function

/-- A completion of `α` is the data of a complete separated uniform space
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
@[pp_with_univ]
structure AbstractCompletion.{v, u} (α : Type u) [UniformSpace α] where
  /-- The underlying space of the completion. -/
  space : Type v
  /-- A map from a space to its completion. -/
  coe : α → space
  /-- The completion carries a uniform structure. -/
  uniformStruct : UniformSpace space
  /-- The completion is complete. -/
  complete : CompleteSpace space
  /-- The completion is a T₀ space. -/
  separation : T0Space space
  /-- The map into the completion is uniform-inducing. -/
  isUniformInducing : IsUniformInducing coe
  /-- The map into the completion has dense range. -/
  dense : DenseRange coe

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

namespace AbstractCompletion

universe uα vα vα' uβ vβ uγ vγ

variable {α : Type uα} [UniformSpace α] (pkg : AbstractCompletion.{vα} α)

local notation "hatα" => pkg.space

local notation "ι" => pkg.coe

/-- If `α` is complete, then it is an abstract completion of itself. -/
def ofComplete [T0Space α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance .id denseRange_id

theorem closure_range : closure (range ι) = univ :=
  pkg.dense.closure_range

theorem isDenseInducing : IsDenseInducing ι :=
  ⟨pkg.isUniformInducing.isInducing, pkg.dense⟩

theorem uniformContinuous_coe : UniformContinuous ι :=
  IsUniformInducing.uniformContinuous pkg.isUniformInducing

theorem continuous_coe : Continuous ι :=
  pkg.uniformContinuous_coe.continuous

@[elab_as_elim]
theorem induction_on {p : hatα → Prop} (a : hatα) (hp : IsClosed { a | p a }) (ih : ∀ a, p (ι a)) :
    p a :=
  isClosed_property pkg.dense hp ih a

variable {β : Type uβ}

protected theorem funext [TopologicalSpace β] [T2Space β] {f g : hatα → β} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a, f (ι a) = g (ι a)) : f = g :=
  funext fun a => pkg.induction_on a (isClosed_eq hf hg) h

variable [UniformSpace β]

section Extend

/-- Extension of maps to completions -/
protected def extend (f : α → β) : hatα → β :=
  open scoped Classical in
  if UniformContinuous f then pkg.isDenseInducing.extend f else fun x => f (pkg.dense.some x)

variable {f : α → β}

theorem extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.isDenseInducing.extend f :=
  if_pos hf

theorem inseparable_extend_coe (hf : UniformContinuous f) (x : α) :
    Inseparable (pkg.extend f (ι x)) (f x) := by
  rw [extend_def _ hf]
  exact pkg.isDenseInducing.inseparable_extend hf.continuous.continuousAt

theorem extend_coe [T2Space β] (hf : UniformContinuous f) (a : α) : (pkg.extend f) (ι a) = f a := by
  rw [pkg.extend_def hf]
  exact pkg.isDenseInducing.extend_eq hf.continuous a

variable [CompleteSpace β]

theorem uniformContinuous_extend : UniformContinuous (pkg.extend f) := by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniformContinuous_uniformly_extend pkg.isUniformInducing pkg.dense hf
  · unfold AbstractCompletion.extend
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr 1

theorem continuous_extend : Continuous (pkg.extend f) :=
  pkg.uniformContinuous_extend.continuous

lemma isUniformInducing_extend (h : IsUniformInducing f) :
    IsUniformInducing (pkg.extend f) := by
  rw [extend_def _ h.uniformContinuous]
  exact pkg.isDenseInducing.isUniformInducing_extend pkg.isUniformInducing h

variable [T0Space β]

theorem extend_unique (hf : UniformContinuous f) {g : hatα → β} (hg : UniformContinuous g)
    (h : ∀ a : α, f a = g (ι a)) : pkg.extend f = g := by
  apply pkg.funext pkg.continuous_extend hg.continuous
  simpa only [pkg.extend_coe hf] using h

@[simp]
theorem extend_comp_coe {f : hatα → β} (hf : UniformContinuous f) : pkg.extend (f ∘ ι) = f :=
  funext fun x =>
    pkg.induction_on x (isClosed_eq pkg.continuous_extend hf.continuous) fun y =>
      pkg.extend_coe (hf.comp <| pkg.uniformContinuous_coe) y

end Extend

section MapSec

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

/-- Lifting maps to completions -/
protected def map (f : α → β) : hatα → hatβ :=
  pkg.extend (ι' ∘ f)

local notation "map" => pkg.map pkg'

variable (f : α → β)

theorem uniformContinuous_map : UniformContinuous (map f) :=
  pkg.uniformContinuous_extend

@[continuity]
theorem continuous_map : Continuous (map f) :=
  pkg.continuous_extend

variable {f}

@[simp]
theorem map_coe (hf : UniformContinuous f) (a : α) : map f (ι a) = ι' (f a) :=
  pkg.extend_coe (pkg'.uniformContinuous_coe.comp hf) a

theorem map_unique {f : α → β} {g : hatα → hatβ} (hg : UniformContinuous g)
    (h : ∀ a, ι' (f a) = g (ι a)) : map f = g :=
  pkg.funext (pkg.continuous_map _ _) hg.continuous <| by
    intro a
    change pkg.extend (ι' ∘ f) _ = _
    simp_rw [Function.comp_def, h, ← comp_apply (f := g)]
    rw [pkg.extend_coe (hg.comp pkg.uniformContinuous_coe)]

@[simp]
theorem map_id : pkg.map pkg id = id :=
  pkg.map_unique pkg uniformContinuous_id fun _ => rfl

variable {γ : Type uγ} [UniformSpace γ]

theorem extend_map [CompleteSpace γ] [T0Space γ] {f : β → γ} {g : α → β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    pkg'.extend f ∘ map g = pkg.extend (f ∘ g) :=
  pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend
    fun a => by
    rw [pkg.extend_coe (hf.comp hg), comp_apply, pkg.map_coe pkg' hg, pkg'.extend_coe hf]
    rfl

variable (pkg'' : AbstractCompletion.{vγ} γ)

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f) :=
  pkg.extend_map pkg' (pkg''.uniformContinuous_coe.comp hg) hf

/-- The uniform isomorphism between two completions of isomorphic uniform spaces. -/
def mapEquiv (e : α ≃ᵤ β) : hatα ≃ᵤ hatβ where
  toFun := pkg.map pkg' e
  invFun := pkg'.map pkg e.symm
  uniformContinuous_toFun := uniformContinuous_map ..
  uniformContinuous_invFun := uniformContinuous_map ..
  left_inv := Function.leftInverse_iff_comp.2 <| by
    simp [map_comp _ _ _ e.symm.uniformContinuous e.uniformContinuous]
  right_inv := Function.rightInverse_iff_comp.2 <| by
    simp [map_comp _ _ _ e.uniformContinuous e.symm.uniformContinuous]

@[simp]
theorem mapEquiv_symm (e : α ≃ᵤ β) :
    (pkg.mapEquiv pkg' e).symm = pkg'.mapEquiv pkg e.symm := rfl

@[simp]
theorem mapEquiv_coe (e : α ≃ᵤ β) (a : α) : pkg.mapEquiv pkg' e (ι a) = ι' (e a) :=
  pkg.map_coe pkg' e.uniformContinuous _

end MapSec

section Compare

-- We can now compare two completion packages for the same uniform space
variable (pkg' : AbstractCompletion.{vα'} α)

/-- The comparison map between two completions of the same uniform space. -/
def compare : pkg.space → pkg'.space :=
  pkg.extend pkg'.coe

theorem uniformContinuous_compare : UniformContinuous (pkg.compare pkg') :=
  pkg.uniformContinuous_extend

theorem compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a :=
  pkg.extend_coe pkg'.uniformContinuous_coe a

theorem inverse_compare : pkg.compare pkg' ∘ pkg'.compare pkg = id := by
  have uc := pkg.uniformContinuous_compare pkg'
  have uc' := pkg'.uniformContinuous_compare pkg
  apply pkg'.funext (uc.comp uc').continuous continuous_id
  intro a
  rw [comp_apply, pkg'.compare_coe pkg, pkg.compare_coe pkg']
  rfl

/-- The uniform bijection between two completions of the same uniform space. -/
def compareEquiv : pkg.space ≃ᵤ pkg'.space where
  toFun := pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniformContinuous_toFun := uniformContinuous_compare _ _
  uniformContinuous_invFun := uniformContinuous_compare _ _

theorem uniformContinuous_compareEquiv : UniformContinuous (pkg.compareEquiv pkg') :=
  pkg.uniformContinuous_compare pkg'

theorem uniformContinuous_compareEquiv_symm : UniformContinuous (pkg.compareEquiv pkg').symm :=
  pkg'.uniformContinuous_compare pkg


open scoped Topology

/-Let `f : α → γ` be a continuous function between a uniform space `α` and a regular topological
space `γ`, and let `pkg, pkg'` be two abstract completions of `α`. Then
if for every point `a : pkg` the filter `f.map (coe⁻¹ (𝓝 a))` obtained by pushing forward with `f`
the preimage in `α` of `𝓝 a` tends to `𝓝 (f.extend a : β)`, then the comparison map
between `pkg` and `pkg'` composed with the extension of `f` to `pkg`` coincides with the
extension of `f` to `pkg'`. The situation is described in the following diagram, where the
two diagonal arrows are the extensions of `f` to the two different completions `pkg` and `pkg'`;
the statement of `compare_comp_eq_compare` is the commutativity of the right triangle.

```
`α^`=`pkg` ≅ `α^'`=`pkg'`   *here `≅` is `compare`*
  ∧     \        /
  |      \      /
  |       \    /
  |        V  ∨
 α ---f---> γ
```
-/
theorem compare_comp_eq_compare (γ : Type uγ) [TopologicalSpace γ]
    [T3Space γ] {f : α → γ} (cont_f : Continuous f) :
    letI := pkg.uniformStruct.toTopologicalSpace
    letI := pkg'.uniformStruct.toTopologicalSpace
    (∀ a : pkg.space,
      Filter.Tendsto f (Filter.comap pkg.coe (𝓝 a)) (𝓝 ((pkg.isDenseInducing.extend f) a))) →
      pkg.isDenseInducing.extend f ∘ pkg'.compare pkg = pkg'.isDenseInducing.extend f := by
  let _ := pkg'.uniformStruct
  let _ := pkg.uniformStruct
  intro h
  have (x : α) : (pkg.isDenseInducing.extend f ∘ pkg'.compare pkg) (pkg'.coe x) = f x := by
    simp only [Function.comp_apply, compare_coe, IsDenseInducing.extend_eq _ cont_f]
  apply (IsDenseInducing.extend_unique (AbstractCompletion.isDenseInducing _) this
    (Continuous.comp _ (uniformContinuous_compare pkg' pkg).continuous)).symm
  apply IsDenseInducing.continuous_extend
  exact fun a ↦ ⟨(pkg.isDenseInducing.extend f) a, h a⟩

end Compare

section Prod

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

/-- Products of completions -/
protected def prod : AbstractCompletion (α × β) where
  space := hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := IsUniformInducing.prod pkg.isUniformInducing pkg'.isUniformInducing
  dense := pkg.dense.prodMap pkg'.dense

end Prod

section Extension₂

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

variable {γ : Type uγ} [UniformSpace γ]

open Function

/-- Extend two variable map to completions. -/
protected def extend₂ (f : α → β → γ) : hatα → hatβ → γ :=
  curry <| (pkg.prod pkg').extend (uncurry f)

section T0Space

variable [T0Space γ] {f : α → β → γ}

theorem extension₂_coe_coe (hf : UniformContinuous <| uncurry f) (a : α) (b : β) :
    pkg.extend₂ pkg' f (ι a) (ι' b) = f a b :=
  show (pkg.prod pkg').extend (uncurry f) ((pkg.prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.prod pkg').extend_coe hf _

end T0Space

variable {f : α → β → γ}
variable [CompleteSpace γ] (f)

theorem uniformContinuous_extension₂ : UniformContinuous₂ (pkg.extend₂ pkg' f) := by
  rw [uniformContinuous₂_def, AbstractCompletion.extend₂, uncurry_curry]
  apply uniformContinuous_extend

end Extension₂

section Map₂

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

variable {γ : Type uγ} [UniformSpace γ] (pkg'' : AbstractCompletion.{vγ} γ)

local notation "hatγ" => pkg''.space

local notation "ι''" => pkg''.coe

local notation f " ∘₂ " g => bicompr f g

/-- Lift two variable maps to completions. -/
protected def map₂ (f : α → β → γ) : hatα → hatβ → hatγ :=
  pkg.extend₂ pkg' (pkg''.coe ∘₂ f)

theorem uniformContinuous_map₂ (f : α → β → γ) : UniformContinuous₂ (pkg.map₂ pkg' pkg'' f) :=
  AbstractCompletion.uniformContinuous_extension₂ pkg pkg' _

theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α → β → γ} {a : δ → hatα} {b : δ → hatβ}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => pkg.map₂ pkg' pkg'' f (a d) (b d) :=
  (pkg.uniformContinuous_map₂ pkg' pkg'' f).continuous.comp₂ ha hb

theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    pkg.map₂ pkg' pkg'' f (ι a) (ι' b) = ι'' (f a b) :=
  pkg.extension₂_coe_coe (f := pkg''.coe ∘₂ f) pkg' (pkg''.uniformContinuous_coe.comp hf) a b

end Map₂

end AbstractCompletion
