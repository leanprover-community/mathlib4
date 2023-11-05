/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.UniformSpace.Equiv

#align_import topology.uniform_space.abstract_completion from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Abstract theory of Hausdorff completions of uniform spaces

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induce the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion, it only study consequences of their existence.
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


noncomputable section

attribute [local instance] Classical.propDecidable

open Filter Set Function

universe u

/-- A completion of `α` is the data of a complete separated uniform space (from the same universe)
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
structure AbstractCompletion (α : Type u) [UniformSpace α] where
  /-- The underlying space of the completion. -/
  space : Type u
  /-- A map from a space to its completion. -/
  coe : α → space
  /-- The completion carries a uniform structure. -/
  uniformStruct : UniformSpace space
  /-- The completion is complete. -/
  complete : CompleteSpace space
  /-- The completion is a separated space. -/
  separation : SeparatedSpace space
  /-- The map into the completion is uniform-inducing. -/
  uniformInducing : UniformInducing coe
  /-- The map into the completion has dense range. -/
  dense : DenseRange coe

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

namespace AbstractCompletion

variable {α : Type*} [UniformSpace α] (pkg : AbstractCompletion α)

local notation "hatα" => pkg.space

local notation "ι" => pkg.coe

/-- If `α` is complete, then it is an abstract completion of itself. -/
def ofComplete [SeparatedSpace α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance uniformInducing_id denseRange_id

theorem closure_range : closure (range ι) = univ :=
  pkg.dense.closure_range

theorem denseInducing : DenseInducing ι :=
  ⟨pkg.uniformInducing.inducing, pkg.dense⟩

theorem uniformContinuous_coe : UniformContinuous ι :=
  UniformInducing.uniformContinuous pkg.uniformInducing

theorem continuous_coe : Continuous ι :=
  pkg.uniformContinuous_coe.continuous

@[elab_as_elim]
theorem induction_on {p : hatα → Prop} (a : hatα) (hp : IsClosed { a | p a }) (ih : ∀ a, p (ι a)) :
    p a :=
  isClosed_property pkg.dense hp ih a

variable {β : Type*}

protected theorem funext [TopologicalSpace β] [T2Space β] {f g : hatα → β} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a, f (ι a) = g (ι a)) : f = g :=
  funext fun a => pkg.induction_on a (isClosed_eq hf hg) h

variable [UniformSpace β]

section Extend

/-- Extension of maps to completions -/
protected def extend (f : α → β) : hatα → β :=
  if UniformContinuous f then pkg.denseInducing.extend f else fun x => f (pkg.dense.some x)

variable {f : α → β}

theorem extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.denseInducing.extend f :=
  if_pos hf

theorem extend_coe [T2Space β] (hf : UniformContinuous f) (a : α) : (pkg.extend f) (ι a) = f a := by
  rw [pkg.extend_def hf]
  exact pkg.denseInducing.extend_eq hf.continuous a

variable [CompleteSpace β]

theorem uniformContinuous_extend : UniformContinuous (pkg.extend f) := by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniformContinuous_uniformly_extend pkg.uniformInducing pkg.dense hf
  · change UniformContinuous (ite _ _ _)
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr 1

theorem continuous_extend : Continuous (pkg.extend f) :=
  pkg.uniformContinuous_extend.continuous

variable [SeparatedSpace β]

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

variable (pkg' : AbstractCompletion β)

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
    simp only [(· ∘ ·), h, ←comp_apply (f := g)]
    rw [pkg.extend_coe (hg.comp pkg.uniformContinuous_coe)]

@[simp]
theorem map_id : pkg.map pkg id = id :=
  pkg.map_unique pkg uniformContinuous_id fun _ => rfl

variable {γ : Type*} [UniformSpace γ]

theorem extend_map [CompleteSpace γ] [SeparatedSpace γ] {f : β → γ} {g : α → β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    pkg'.extend f ∘ map g = pkg.extend (f ∘ g) :=
  pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend
    fun a => by
    rw [pkg.extend_coe (hf.comp hg), comp_apply, pkg.map_coe pkg' hg, pkg'.extend_coe hf]
    rfl

variable (pkg'' : AbstractCompletion γ)

theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f) :=
  pkg.extend_map pkg' (pkg''.uniformContinuous_coe.comp hg) hf

end MapSec

section Compare

-- We can now compare two completion packages for the same uniform space
variable (pkg' : AbstractCompletion α)

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
def compareEquiv : pkg.space ≃ᵤ pkg'.space
    where
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

end Compare

section Prod

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

/-- Products of completions -/
protected def prod : AbstractCompletion (α × β)
    where
  space := hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  uniformInducing := UniformInducing.prod pkg.uniformInducing pkg'.uniformInducing
  dense := DenseRange.prod_map pkg.dense pkg'.dense

end Prod

section Extension₂

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

variable {γ : Type*} [UniformSpace γ]

open Function

/-- Extend two variable map to completions. -/
protected def extend₂ (f : α → β → γ) : hatα → hatβ → γ :=
  curry <| (pkg.prod pkg').extend (uncurry f)

section SeparatedSpace

variable [SeparatedSpace γ] {f : α → β → γ}

theorem extension₂_coe_coe (hf : UniformContinuous <| uncurry f) (a : α) (b : β) :
    pkg.extend₂ pkg' f (ι a) (ι' b) = f a b :=
  show (pkg.prod pkg').extend (uncurry f) ((pkg.prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.prod pkg').extend_coe hf _

end SeparatedSpace

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

variable {γ : Type*} [UniformSpace γ] (pkg'' : AbstractCompletion γ)

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
  ((pkg.uniformContinuous_map₂ pkg' pkg'' f).continuous.comp (Continuous.prod_mk ha hb) : _)

theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    pkg.map₂ pkg' pkg'' f (ι a) (ι' b) = ι'' (f a b) :=
  pkg.extension₂_coe_coe (f := pkg''.coe ∘₂ f) pkg' (pkg''.uniformContinuous_coe.comp hf) a b

end Map₂

end AbstractCompletion
