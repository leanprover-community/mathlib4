/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Cartesian morphisms

This file defines Cartesian resp. strongly Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted to `Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCartesian p f φ` expresses that `φ` is a Cartesian morphism lying over `f` with respect to `p` in
the sense of SGA 1 VI 5.1. This means that for any morphism `φ' : a' ⟶ b` lying over `f` there is
a unique morphism `τ : a' ⟶ a` lying over `𝟙 R`, such that `φ' = τ ≫ φ`.

`IsStronglyCartesian p f φ` expresses that `φ` is a strongly Cartesian morphism lying over `f` with
respect to `p`, see <https://stacks.math.columbia.edu/tag/02XK>.

## Implementation

The constructor of `IsStronglyCartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

## References
* [A. Grothendieck, M. Raynaud, *SGA 1*](https://arxiv.org/abs/math/0206203)
* [Stacks: Fibred Categories](https://stacks.math.columbia.edu/tag/02XJ)
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is Cartesian if for all
morphisms `φ' : a' ⟶ b`, also lying over `f`, there exists a unique morphism `χ : a' ⟶ a` lifting
`𝟙 R` such that `φ' = χ ≫ φ`.

See SGA 1 VI 5.1. -/
class IsCartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'
attribute [instance] IsCartesian.toIsHomLift

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly Cartesian if for
all morphisms `φ' : a' ⟶ b` and all diagrams of the form
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ'` lifts `g ≫ f`, there exists a lift `χ` of `g` such that `φ' = χ ≫ φ`. -/
@[stacks 02XK]
class IsStronglyCartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property' {a' : 𝒳} (g : p.obj a' ⟶ R) (φ' : a' ⟶ b) [IsHomLift p (g ≫ f) φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'
attribute [instance] IsStronglyCartesian.toIsHomLift

end

namespace IsCartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCartesian p f φ]

section

variable {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']

/-- Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a' ⟶ b` which also lifts `f`, then `IsCartesian.map f φ φ'` is the morphism `a' ⟶ a` lifting
`𝟙 R` obtained from the universal property of `φ`. -/
protected noncomputable def map : a' ⟶ a :=
  Classical.choose <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ'

instance map_isHomLift : IsHomLift p (𝟙 R) (IsCartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]
lemma fac : IsCartesian.map p f φ φ' ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

/-- Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a' ⟶ b` which also lifts `f`. Then any morphism `ψ : a' ⟶ a` lifting `𝟙 R` such that
`g ≫ ψ = φ'` must equal the map induced from the universal property of `φ`. -/
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') :
    ψ = IsCartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

end

/-- Given a Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and two morphisms
`ψ ψ' : a' ⟶ a` such that `ψ ≫ φ = ψ' ≫ φ`. Then we must have `ψ = ψ'`. -/
protected lemma ext (φ : a ⟶ b) [IsCartesian p f φ] {a' : 𝒳} (ψ ψ' : a' ⟶ a)
    [IsHomLift p (𝟙 R) ψ] [IsHomLift p (𝟙 R) ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (ψ ≫ φ) ψ rfl, map_uniq p f φ (ψ ≫ φ) ψ' h.symm]

@[simp]
lemma map_self : IsCartesian.map p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ (ψ ≫ φ'.inv)
    refine ⟨⟨inferInstance, by simp only [fac_assoc, assoc, Iso.inv_hom_id, comp_id]⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    rw [Iso.eq_comp_inv]
    simp only [assoc, hτ₂]

/-- The canonical isomorphism between the domains of two Cartesian arrows
lying over the same object. -/
@[simps]
noncomputable def domainUniqueUpToIso {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] : a' ≅ a where
  hom := IsCartesian.map p f φ φ'
  inv := IsCartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply IsCartesian.ext p (p.map φ') φ'
    simp only [assoc, fac, id_comp]
  inv_hom_id := by
    subst_hom_lift p f φ
    apply IsCartesian.ext p (p.map φ) φ
    simp only [assoc, fac, id_comp]

instance domainUniqueUpToIso_inv_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').hom :=
  domainUniqueUpToIso_hom p f φ φ' ▸ IsCartesian.map_isHomLift p f φ φ'

instance domainUniqueUpToIso_hom_isHomLift {a' : 𝒳} (φ' : a' ⟶ b) [IsCartesian p f φ'] :
    IsHomLift p (𝟙 R) (domainUniqueUpToIso p f φ φ').inv :=
  domainUniqueUpToIso_inv p f φ φ' ▸ IsCartesian.map_isHomLift p f φ' φ

/-- Precomposing a Cartesian morphism with an isomorphism lifting the identity is Cartesian. -/
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCartesian.map p f φ ψ ≫ φ'.inv
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_comp_inv]
    apply map_uniq
    simp only [assoc, hτ₂]

end IsCartesian

namespace IsStronglyCartesian

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCartesian p f φ]

/-- The universal property of a strongly Cartesian morphism.

This lemma is more flexible with respect to non-definitional equalities than the field
`universal_property'` of `IsStronglyCartesian`. -/
lemma universal_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (g ≫ f) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCartesian.universal_property' f

instance isCartesian_of_isStronglyCartesian [p.IsStronglyCartesian f φ] : p.IsCartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 R) f (by simp) φ'

section

variable {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f) (φ' : a' ⟶ b)
  [IsHomLift p f' φ']

/-- Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and a morphism `φ' : a' ⟶ b`. Then `map` is the map `a' ⟶ a`
lying over `g` obtained from the universal property of `φ`. -/
noncomputable def map : a' ⟶ a :=
  Classical.choose <| universal_property p f φ _ _ hf' φ'

instance map_isHomLift : IsHomLift p g (map p f φ hf' φ') :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[reassoc (attr := simp)]
lemma fac : (map p f φ hf' φ') ≫ φ = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

/-- Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and morphisms `φ' : a' ⟶ b`, `ψ : a' ⟶ a` such that
`ψ ≫ φ = φ'`. Then `ψ` is the map induced by the universal property. -/
lemma map_uniq (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') : ψ = map p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

end

/-- Given a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that `φ` is strongly Cartesian, and morphisms `ψ ψ' : a' ⟶ a` such that
`g ≫ ψ = φ' = g ≫ ψ'`. Then we have that `ψ = ψ'`. -/
protected lemma ext (φ : a ⟶ b) [IsStronglyCartesian p f φ] {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R)
    {ψ ψ' : a' ⟶ a} [IsHomLift p g ψ] [IsHomLift p g ψ'] (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' := by
  rw [map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ rfl, map_uniq p f φ (g := g) rfl (ψ ≫ φ) ψ' h.symm]

@[simp]
lemma map_self : map p f φ (id_comp f).symm φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [id_comp]

/-- When its possible to compare the two, the composition of two `IsStronglyCartesian.map` will also
be given by a `IsStronglyCartesian.map`. In other words, given diagrams
```
a''         a'        a --φ--> b
|           |         |        |
v           v         v        v
R'' --g'--> R' --g--> R --f--> S
```
and
```
a' --φ'--> b
|          |
v          v
R' --f'--> S
```
and
```
a'' --φ''--> b
|            |
v            v
R'' --f''--> S
```
such that `φ` and `φ'` are strongly Cartesian morphisms, and such that `f' = g ≫ f` and
`f'' = g' ≫ f'`. Then composing the induced map from `a'' ⟶ a'` with the induced map from
`a' ⟶ a` gives the induced map from `a'' ⟶ a`. -/
@[reassoc (attr := simp)]
lemma map_comp_map {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R}
    {g' : R'' ⟶ R'} (H : f' = g ≫ f) (H' : f'' = g' ≫ f') (φ' : a' ⟶ b) (φ'' : a'' ⟶ b)
    [IsStronglyCartesian p f' φ'] [IsHomLift p f'' φ''] :
    map p f' φ' H' φ'' ≫ map p f φ H φ' =
      map p f φ (show f'' = (g' ≫ g) ≫ f by rwa [assoc, ← H]) φ'' := by
  apply map_uniq p f φ
  simp only [assoc, fac]

end

section

variable {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}

/-- Given two strongly Cartesian morphisms `φ`, `ψ` as follows
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then the composite `φ ≫ ψ` is also strongly Cartesian. -/
instance comp [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ] :
    IsStronglyCartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro a' h τ hτ
    use map p f φ (f' := h ≫ f) rfl (map p g ψ (assoc h f g).symm τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [← assoc, fac, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [assoc, hπ'₂]

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that `φ ≫ ψ` and `ψ` are strongly Cartesian, then so is `φ`. -/
protected lemma of_comp [IsStronglyCartesian p g ψ] [IsStronglyCartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p f φ] : IsStronglyCartesian p f φ where
  universal_property' := by
    intro a' h τ hτ
    have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp p (h ≫ f) _ τ ψ
    /- We get a morphism `π : a' ⟶ a` such that `π ≫ φ ≫ ψ = τ ≫ ψ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := h ≫ f ≫ g) rfl (τ ≫ ψ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /- The fact that `π ≫ φ = τ` follows from `π ≫ φ ≫ ψ = τ ≫ ψ` and the universal property of
    `ψ`. -/
    · apply IsStronglyCartesian.ext p g ψ (h ≫ f) (by simp)
    -- Finally, the uniqueness of `π` comes from the universal property of `φ ≫ ψ`.
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      simp [hπ'₂.symm]

end

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S)

instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCartesian p f φ.hom where
  universal_property' := by
    intro a' g τ hτ
    use τ ≫ φ.inv
    refine ⟨?_, by cat_disch⟩
    simpa using (IsHomLift.comp p (g ≫ f) (isoOfIsoLift p f φ).inv τ φ.inv)

instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCartesian p f φ :=
  @IsStronglyCartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

/-- A strongly Cartesian morphism lying over an isomorphism is an isomorphism. -/
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCartesian p f φ] [IsIso f] : IsIso φ := by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ` be the morphism induced by applying universal property to `𝟙 b` lying over `f⁻¹ ≫ f`.
  let φ' := map p (p.map φ) φ (IsIso.inv_hom_id (p.map φ)).symm (𝟙 b)
  use φ'
  -- `φ' ≫ φ = 𝟙 b` follows immediately from the universal property.
  have inv_hom : φ' ≫ φ = 𝟙 b := fac p (p.map φ) φ _ (𝟙 b)
  refine ⟨?_, inv_hom⟩
  -- We will now show that `φ ≫ φ' = 𝟙 a` by showing that `(φ ≫ φ') ≫ φ = 𝟙 a ≫ φ`.
  have h₁ : IsHomLift p (𝟙 (p.obj a)) (φ ≫ φ') := by
    rw [← IsIso.hom_inv_id (p.map φ)]
    apply IsHomLift.comp
  apply IsStronglyCartesian.ext p (p.map φ) φ (𝟙 (p.obj a))
  simp only [assoc, inv_hom, comp_id, id_comp]

end

section

variable {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}

/-- The canonical isomorphism between the domains of two strongly Cartesian morphisms lying over
isomorphic objects. -/
@[simps]
noncomputable def domainIsoOfBaseIso (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] : a' ≅ a where
  hom := map p f φ h φ'
  inv :=
    haveI : p.IsHomLift ((fun x ↦ g.inv ≫ x) (g.hom ≫ f)) φ := by
      simpa using IsCartesian.toIsHomLift
    map p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

instance domainUniqueUpToIso_inv_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.hom (domainIsoOfBaseIso p h φ φ').hom :=
  domainIsoOfBaseIso_hom p h φ φ' ▸ IsStronglyCartesian.map_isHomLift p f φ h φ'

instance domainUniqueUpToIso_hom_isHomLift (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    [IsStronglyCartesian p f φ] [IsStronglyCartesian p f' φ'] :
    IsHomLift p g.inv (domainIsoOfBaseIso p h φ φ').inv := by
  haveI : p.IsHomLift ((fun x ↦ g.inv ≫ x) (g.hom ≫ f)) φ := by
    simpa using IsCartesian.toIsHomLift
  simpa using IsStronglyCartesian.map_isHomLift p f' φ' (congrArg (g.inv ≫ ·) h.symm) φ

end

end IsStronglyCartesian

end CategoryTheory.Functor
