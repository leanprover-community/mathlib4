/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # Bilipschitz equivalence

A common pattern in Mathlib is to replace the topology, uniformity and bornology on a type
synonym with those of the underlying type.

The most common way to do this is to activate a local instance for something which puts a
`PseudoMetricSpace` structure on the type synonym, prove that this metric is bilipschitz equivalent
to the metric on the underlying type, and then use this to show that the uniformities and
bornologies agree, which can then be used with `PseudoMetricSpace.replaceUniformity` or
`PseudoMetricSpace.replaceBornology`.

With the tooling outside this file, this can be a bit cumbersome, especially when it occurs
repeatedly, and moreover it can lend itself to abuse of the definitional equality inherent in the
type synonym. In this file, we make this pattern more convenient by providing lemmas which take
directly the conditions that the map is bilipschitz, and then prove the relevant equalities.
Moreover, because there are no type synonyms here, it is necessary to phrase these equalities in
terms of the induced uniformity and bornology, which means users will need to do the same if they
choose to use these convenience lemmas. This encourages good hygiene in the development of type
synonyms.
-/

open NNReal

section Uniformity

open Uniformity

variable {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
variable {K₁ K₂ : ℝ≥0} {f : α → β}

/-- If `f : α → β` is bilipschitz, then the pullback of the uniformity on `β` through `f` agrees
with the uniformity on `α`.

This can be used to provide the replacement equality when applying
`PseudoMetricSpace.replaceUniformity`, which can be useful when following the forgetful inheritance
pattern when creating type synonyms.

Important Note: if `α` is some synonym of a type `β` (at default transparency), and `f : α ≃ β` is
some bilipschitz equivalence, then instead of writing:
```
instance : UniformSpace α := inferInstanceAs (UniformSpace β)
```
Users should instead write something like:
```
instance : UniformSpace α := (inferInstance : UniformSpace β).comap f
```
in order to avoid abuse of the definitional equality `α := β`. -/
lemma uniformity_eq_of_bilipschitz (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) :
    𝓤[(inferInstance : UniformSpace β).comap f] = 𝓤 α :=
  hf₁.isUniformInducing hf₂.uniformContinuous |>.comap_uniformity

end Uniformity

section Bornology

open Bornology Filter

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
variable {K₁ K₂ : ℝ≥0} {f : α → β}

/-- If `f : α → β` is bilipschitz, then the pullback of the bornology on `β` through `f` agrees
with the bornology on `α`. -/
lemma bornology_eq_of_bilipschitz (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f) :
    @cobounded _ (induced f) = cobounded α :=
  le_antisymm hf₂.comap_cobounded_le hf₁.tendsto_cobounded.le_comap


/-- If `f : α → β` is bilipschitz, then the pullback of the bornology on `β` through `f` agrees
with the bornology on `α`.

This can be used to provide the replacement equality when applying
`PseudoMetricSpace.replaceBornology`, which can be useful when following the forgetful inheritance
pattern when creating type synonyms.

Important Note: if `α` is some synonym of a type `β` (at default transparency), and `f : α ≃ β` is
some bilipschitz equivalence, then instead of writing:
```
instance : Bornology α := inferInstanceAs (Bornology β)
```
Users should instead write something like:
```
instance : Bornology α := Bornology.induced (f : α → β)
```
in order to avoid abuse of the definitional equality `α := β`. -/
lemma isBounded_iff_of_bilipschitz (hf₁ : AntilipschitzWith K₁ f) (hf₂ : LipschitzWith K₂ f)
    (s : Set α) : @IsBounded _ (induced f) s ↔ Bornology.IsBounded s :=
  Filter.ext_iff.1 (bornology_eq_of_bilipschitz hf₁ hf₂) (sᶜ)

end Bornology
