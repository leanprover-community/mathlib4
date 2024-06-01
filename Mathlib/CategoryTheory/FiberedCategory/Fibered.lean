/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be (pre)fibered.

## Main definitions
- `IsPreFibered p` expresses that `p` gives `𝒳` the structure of a prefibered category over `𝒮`,
as in SGA VI.6.1
- `IsFibered p` expresses `𝒳` is fibered over `𝒮` via a functor `p : 𝒳 ⥤ 𝒮`, as in SGA VI.6.1.
This means that it is prefibered, and that the composition of any two cartesian morphisms is
cartesian.

In the literature one often sees the notion of a fibered category defined as the existence of
strongly cartesian morphisms lying over any given morphism in the base. This is equivalent to the
notion above, and we give an alternate constructor `IsFibered.of_has_pullbacks'` for constructing
a fibered category this way.


## Implementation

The constructor of `IsPreFibered` is called `has_pullbacks'`. The reason for the prime is that when
wanting to apply this condition, it is recommended to instead use the lemma `has_pullbacks`
(without the prime), which is more applicable with respect to non-definitional equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)

-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Definition of a prefibered category.
See SGA 1 VI.6.1. -/
class Functor.IsPreFibered (p : 𝒳 ⥤ 𝒮) : Prop where
  has_pullbacks' {a : 𝒳} {R : 𝒮} (f : R ⟶ p.obj a) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ

protected lemma IsPreFibered.has_pullbacks {p : 𝒳 ⥤ 𝒮} [p.IsPreFibered] {a : 𝒳} {R S : 𝒮}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : 𝒳) (φ : b ⟶ a), IsCartesian p f φ := by
  subst ha; exact IsPreFibered.has_pullbacks' f

/-- Definition of a fibered category.

See SGA 1 VI.6.1. -/
class Functor.IsFibered (p : 𝒳 ⥤ 𝒮) extends IsPreFibered p : Prop where
  comp {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ)

instance (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S T : 𝒮} (f : R ⟶ S) (g : S ⟶ T) {a b c : 𝒳} (φ : a ⟶ b)
    (ψ : b ⟶ c) [IsCartesian p f φ] [IsCartesian p g ψ] : IsCartesian p (f ≫ g) (φ ≫ ψ) :=
  IsFibered.comp f g φ ψ

namespace IsPreFibered

open IsCartesian


variable {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S)

/-- Given a prefibered category `p : 𝒳 ⥤ 𝒫`, and a diagram
```
           a
           -
           |
           v
  R --f--> S
```
`pullbackObj` is defined as the domain `R ×_S a` of some cartesian arrow lying over
`f`, which exists by the fibered category structure on `p`. -/
noncomputable def pullbackObj {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮}
    {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : 𝒳 :=
  Classical.choose (IsPreFibered.has_pullbacks ha f)

/-- Given a fibered category `p : 𝒳 ⥤ 𝒫`, and a diagram
```
          a
          -
          |
          v
R --f--> S
```
we get a map `R ×_S b ⟶ a` -/
noncomputable def pullbackMap {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮}
    {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : pullbackObj ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (IsPreFibered.has_pullbacks ha f))

instance pullbackMap.IsCartesian {p : 𝒳 ⥤ 𝒮} [IsPreFibered p] {R S : 𝒮}
    {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : IsCartesian p f (pullbackMap ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreFibered.has_pullbacks ha f))

lemma pullbackObj_proj : p.obj (pullbackObj ha f) = R :=
  domain_eq p f (pullbackMap ha f)

end IsPreFibered

namespace IsFibered

open IsCartesian IsPreFibered

instance isStronglyCartesian_of_isCartesian (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {R S : 𝒮} (f : R ⟶ S)
    {a b : 𝒳} (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ := by
  apply IsStronglyCartesian.mk
  intro a' g φ' hφ'
  -- Let `ψ` be a cartesian arrow lying over `g`
  let ψ := pullbackMap (domain_eq p f φ) g
  --have : IsCartesian p (g ≫ f) (ψ ≫ φ) := inferInstance
  -- Let `τ : a' ⟶ ..` be the map induced by the universal property of `ψ ≫ φ`
  let τ := inducedMap p (g ≫ f) (ψ ≫ φ) φ'
  use τ ≫ ψ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  -- TODO: order of values (+ make type-class instance?)
  apply comp_lift_id_left p (p.obj a') τ g ψ
  rw [assoc, inducedMap_comp] -- TODO: comp simp lemma?
  intro π ⟨hπ, hπ_comp⟩
  -- Let `τ'` be the map induced from `π` and the universal property of `ψ`
  rw [← inducedMap_comp p g ψ π]
  congr 1
  apply inducedMap_unique
  rw [← assoc, inducedMap_comp]
  exact hπ_comp

lemma isStronglyCartesian_of_has_pullbacks' (p : 𝒳 ⥤ 𝒮) (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
    ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) {R S : 𝒮} (f : R ⟶ S) {a b : 𝒳}
      (φ : a ⟶ b) [p.IsCartesian f φ] : p.IsStronglyCartesian f φ := by
  apply IsStronglyCartesian.mk
  intro c g φ' hφ'
  subst_hom_lift p f φ; clear a b R S
  -- Let `ψ` be a cartesian arrow lying over `g`
  obtain ⟨a', ψ, hψ⟩ := h _ _ (p.map φ)
  -- Let `τ' : c ⟶ a'` be the map induced by the universal property of `ψ`
  let τ' := IsStronglyCartesian.inducedMap p (p.map φ) ψ (f':= g ≫ p.map φ) rfl φ'
  -- Let `τ : a' ⟶ a` be the map induced by the universal property of `φ`
  let Φ := naturalIso p (p.map φ) φ ψ
  --let τ := inducedMap p (p.map φ) φ ψ
  use τ' ≫ Φ.hom
  refine ⟨⟨?_, ?_⟩, ?_⟩
  -- TODO: order of values (+ make type-class instance?)
  have : p.IsHomLift (𝟙 (p.obj a)) Φ.hom := by simp only [naturalIso_hom, Φ]; infer_instance
  apply comp_lift_id_right p g τ' (p.obj a) Φ.hom
  simp only [naturalIso_hom, assoc, inducedMap_comp, Φ]
  rw [IsStronglyCartesian.inducedMap_comp] -- TODO: comp simp lemma?
  intro π ⟨hπ, hπ_comp⟩
  rw [← Iso.comp_inv_eq]
  have : p.IsHomLift g (π ≫ Φ.inv) := by
    simp only [naturalIso_inv, Φ]
    apply comp_lift_id_right p g π (p.obj a)
  apply IsStronglyCartesian.inducedMap_unique p
  simp [Φ, hπ_comp]


lemma of_has_pullbacks' {p : 𝒳 ⥤ 𝒮} (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
    ∃ (b : 𝒳) (φ : b ⟶ a), IsStronglyCartesian p f φ) : IsFibered p where
  toIsPreFibered := by
    apply IsPreFibered.mk
    intro a R f
    obtain ⟨b, φ, hφ⟩ := h a R f
    refine ⟨b, φ, inferInstance⟩
  comp := by
    intro R S T f g a b c φ ψ _ _
    have : p.IsStronglyCartesian f φ := by apply isStronglyCartesian_of_has_pullbacks' p h
    have : p.IsStronglyCartesian g ψ := by apply isStronglyCartesian_of_has_pullbacks' p h
    infer_instance

/-- Given a diagram
```
                  a
                  -
                  |
                  v
T --g--> R --f--> S
```
we have an isomorphism `T ×_S a ≅ T ×_R (R ×_S a)` -/
noncomputable def pullbackPullbackIso {p : 𝒳 ⥤ 𝒮} [IsFibered p]
    {R S T : 𝒮}  {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
      pullbackObj ha (g ≫ f) ≅ pullbackObj (pullbackObj_proj ha f) g :=
  naturalIso p (g ≫ f) (pullbackMap (pullbackObj_proj ha f) g ≫ pullbackMap ha f)
    (pullbackMap ha (g ≫ f))

end IsFibered

end CategoryTheory
