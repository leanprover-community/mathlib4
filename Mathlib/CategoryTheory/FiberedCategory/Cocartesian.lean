/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.HomLift
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.StacksAttribute
import Mathlib.Util.CompileInductive

/-!
# Co-Cartesian morphisms

This file defines co-Cartesian resp. strongly co-Cartesian morphisms with respect to a functor
`p : 𝒳 ⥤ 𝒮`.

This file has been adapted from `Mathlib/CategoryTheory/FiberedCategory/Cartesian.lean`,
please try to change them in sync.

## Main definitions

`IsCocartesian p f φ` expresses that `φ` is a co-Cartesian morphism lying over `f : R ⟶ S` with
respect to `p`. This means that for any morphism `φ' : a ⟶ b'` lying over `f` there
is a unique morphism `τ : b ⟶ b'` lying over `𝟙 S`, such that `φ' = φ ≫ τ`.

`IsStronglyCocartesian p f φ` expresses that `φ` is a strongly co-Cartesian morphism lying over `f`
with respect to `p`.

## Implementation

The constructor of `IsStronglyCocartesian` has been named `universal_property'`, and is mainly
intended to be used for constructing instances of this class. To use the universal property, we
generally recommended to use the lemma `IsStronglyCocartesian.universal_property` instead. The
difference between the two is that the latter is more flexible with respect to non-definitional
equalities.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is co-Cartesian if for all
morphisms `φ' : a ⟶ b'`, also lying over `f`, there exists a unique morphism `χ : b ⟶ b'` lifting
`𝟙 S` such that `φ' = φ ≫ χ`. -/
class IsCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property {b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ'] :
      ∃! χ : b ⟶ b', IsHomLift p (𝟙 S) χ ∧ φ ≫ χ = φ'

attribute [instance] IsCocartesian.toIsHomLift
/-- A morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is strongly co-Cartesian if for
all morphisms `φ' : a ⟶ b'` and all diagrams of the form
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ'` lifts `f ≫ g`, there exists a lift `χ` of `g` such that `φ' = χ ≫ φ`. -/
@[stacks 02XK]
class IsStronglyCocartesian : Prop where
  [toIsHomLift : IsHomLift p f φ]
  universal_property' {b' : 𝒳} (g : S ⟶ p.obj b') (φ' : a ⟶ b') [IsHomLift p (f ≫ g) φ'] :
      ∃! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ'
attribute [instance] IsStronglyCocartesian.toIsHomLift

end

namespace IsCocartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCocartesian p f φ]

section

variable {b' : 𝒳} (φ' : a ⟶ b') [IsHomLift p f φ']

/-- Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a ⟶ b'` which also lifts `f`, then `IsCocartesian.map f φ φ'` is the morphism `b ⟶ b'` lying
over `𝟙 S` obtained from the universal property of `φ`. -/
protected noncomputable def map : b ⟶ b' :=
  Classical.choose <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ'

instance map_isHomLift : IsHomLift p (𝟙 S) (IsCocartesian.map p f φ φ') :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.1

@[reassoc (attr := simp)]
lemma fac : φ ≫ IsCocartesian.map p f φ φ' = φ' :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').1.2

/-- Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and another morphism
`φ' : a ⟶ b'` which also lifts `f`. Then any morphism `ψ : b ⟶ b'` lifting `𝟙 S` such that
`g ≫ ψ = φ'` must equal the map induced by the universal property of `φ`. -/
lemma map_uniq (ψ : b ⟶ b') [IsHomLift p (𝟙 S) ψ] (hψ : φ ≫ ψ = φ') :
    ψ = IsCocartesian.map p f φ φ' :=
  (Classical.choose_spec <| IsCocartesian.universal_property (p := p) (f := f) (φ := φ) φ').2
    ψ ⟨inferInstance, hψ⟩

end

/-- Given a co-Cartesian morphism `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, and two morphisms
`ψ ψ' : b ⟶ b'` lifting `𝟙 S` such that `φ ≫ ψ = φ ≫ ψ'`. Then we must have `ψ = ψ'`. -/
protected lemma ext (φ : a ⟶ b) [IsCocartesian p f φ] {b' : 𝒳} (ψ ψ' : b ⟶ b')
    [IsHomLift p (𝟙 S) ψ] [IsHomLift p (𝟙 S) ψ'] (h : φ ≫ ψ = φ ≫ ψ') : ψ = ψ' := by
  rw [map_uniq p f φ (φ ≫ ψ) ψ rfl, map_uniq p f φ (φ ≫ ψ) ψ' h.symm]

@[simp]
lemma map_self : IsCocartesian.map p f φ φ = 𝟙 b := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

/-- The canonical isomorphism between the codomains of two co-Cartesian morphisms
lying over the same object. -/
noncomputable def codomainUniqueUpToIso {b' : 𝒳} (φ' : a ⟶ b') [IsCocartesian p f φ'] :
    b ≅ b' where
  hom := IsCocartesian.map p f φ φ'
  inv := IsCocartesian.map p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ
    apply IsCocartesian.ext p (p.map φ) φ
    simp only [fac_assoc, fac, comp_id]
  inv_hom_id := by
    subst_hom_lift p f φ'
    apply IsCocartesian.ext p (p.map φ') φ'
    simp only [fac_assoc, fac, comp_id]

/-- Postcomposing a co-Cartesian morphism with an isomorphism lifting the identity is
co-Cartesian. -/
instance of_comp_iso {b' : 𝒳} (φ' : b ≅ b') [IsHomLift p (𝟙 S) φ'.hom] :
    IsCocartesian p f (φ ≫ φ'.hom) where
  universal_property := by
    intro c ψ hψ
    use φ'.inv ≫ IsCocartesian.map p f φ ψ
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    rw [Iso.eq_inv_comp]
    apply map_uniq
    exact ((assoc φ _ _) ▸ hτ₂)

/-- Precomposing a co-Cartesian morphism with an isomorphism lifting the identity is
co-Cartesian. -/
instance of_iso_comp {a' : 𝒳} (φ' : a' ≅ a) [IsHomLift p (𝟙 R) φ'.hom] :
    IsCocartesian p f (φ'.hom ≫ φ) where
  universal_property := by
    intro c ψ hψ
    use IsCocartesian.map p f φ (φ'.inv ≫ ψ)
    refine ⟨⟨inferInstance, by simp⟩, ?_⟩
    rintro τ ⟨hτ₁, hτ₂⟩
    apply map_uniq
    simp only [Iso.eq_inv_comp, ← assoc, hτ₂]

end IsCocartesian

namespace IsStronglyCocartesian

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCocartesian p f φ]

/-- The universal property of a strongly co-Cartesian morphism.

This lemma is more flexible with respect to non-definitional equalities than the field
`universal_property'` of `IsStronglyCocartesian`. -/
lemma universal_property {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g)
    (φ' : a ⟶ b') [IsHomLift p f' φ'] : ∃! χ : b ⟶ b', IsHomLift p g χ ∧ φ ≫ χ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (f ≫ g) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCocartesian.universal_property' f

instance isCocartesian_of_isStronglyCocartesian : p.IsCocartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 S) f (comp_id f).symm φ'

section

variable {S' : 𝒮} {b' : 𝒳} {g : S ⟶ S'} {f' : R ⟶ S'} (hf' : f' = f ≫ g) (φ' : a ⟶ b')
  [IsHomLift p f' φ']

/-- Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and a morphism `φ' : a ⟶ b'`. Then `map` is the map
`b ⟶ b'` lying over `g` obtained from the universal property of `φ`. -/
noncomputable def map : b ⟶ b' :=
  Classical.choose <| universal_property p f φ _ _ hf' φ'

instance map_isHomLift : IsHomLift p g (map p f φ hf' φ') :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[reassoc (attr := simp)]
lemma fac : φ ≫ (map p f φ hf' φ') = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2


/-- Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and morphisms `φ' : a ⟶ b'`, `ψ : b ⟶ b'` such that
`g ≫ ψ = φ'`. Then `ψ` is the map induced by the universal property. -/
lemma map_uniq (ψ : b ⟶ b') [IsHomLift p g ψ] (hψ : φ ≫ ψ = φ') : ψ = map p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

end

/-- Given a diagram
```
a --φ--> b        b'
|        |        |
v        v        v
R --f--> S --g--> S'
```
such that `φ` is strongly co-Cartesian, and morphisms `ψ ψ' : b ⟶ b'` such that
`g ≫ ψ = φ' = g ≫ ψ'`. Then we have that `ψ = ψ'`. -/
protected lemma ext (φ : a ⟶ b) [IsStronglyCocartesian p f φ] {S' : 𝒮} {b' : 𝒳} (g : S ⟶ S')
    {ψ ψ' : b ⟶ b'} [IsHomLift p g ψ] [IsHomLift p g ψ'] (h : φ ≫ ψ = φ ≫ ψ') : ψ = ψ' := by
  rw [map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ rfl, map_uniq p f φ (g := g) rfl (φ ≫ ψ) ψ' h.symm]

@[simp]
lemma map_self : map p f φ (comp_id f).symm φ = 𝟙 b := by
  subst_hom_lift p f φ; symm
  apply map_uniq
  simp only [comp_id]

/-- When its possible to compare the two, the composition of two `IsStronglyCocartesian.map` will
also be given by a `IsStronglyCocartesian.map`. In other words, given diagrams
```
a --φ--> b        b'         b''
|        |        |          |
v        v        v          v
R --f--> S --g--> S' --g'--> S'
```
and
```
a --φ'--> b'
|         |
v         v
R --f'--> S'

```
and
```
a --φ''--> b''
|          |
v          v
R --f''--> S''
```
such that `φ` and `φ'` are strongly co-Cartesian morphisms, and such that `f' = f ≫ g` and
`f'' = f' ≫ g'`. Then composing the induced map from `b ⟶ b'` with the induced map from
`b' ⟶ b''` gives the induced map from `b ⟶ b''`. -/
@[reassoc (attr := simp)]
lemma map_comp_map {S' S'' : 𝒮} {b' b'' : 𝒳} {f' : R ⟶ S'} {f'' : R ⟶ S''} {g : S ⟶ S'}
    {g' : S' ⟶ S''} (H : f' = f ≫ g) (H' : f'' = f' ≫ g') (φ' : a ⟶ b') (φ'' : a ⟶ b'')
    [IsStronglyCocartesian p f' φ'] [IsHomLift p f'' φ''] :
    map p f φ H φ' ≫ map p f' φ' H' φ'' =
      map p f φ (show f'' = f ≫ (g ≫ g') by rwa [← assoc, ← H]) φ'' := by
  apply map_uniq p f φ
  simp only [fac_assoc, fac]

end

section

variable {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b} {ψ : b ⟶ c}

/-- Given two strongly co-Cartesian morphisms `φ`, `ψ` as follows
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then the composite `φ ≫ ψ` is also strongly co-Cartesian. -/
instance comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p g ψ] :
    IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro c' h τ hτ
    use map p g ψ (f' := g ≫ h) rfl <| map p f φ (assoc f g h) τ
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · simp only [assoc, fac]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      apply map_uniq
      simp only [← hπ'₂, assoc]

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that `φ ≫ ψ` and `φ` are strongly co-Cartesian, then so is `ψ`. -/
protected lemma of_comp [IsStronglyCocartesian p f φ] [IsStronglyCocartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p g ψ] : IsStronglyCocartesian p g ψ where
  universal_property' := by
    intro c' h τ hτ
    /- We get a morphism `π : c ⟶ c'` such that `(φ ≫ ψ) ≫ π = φ ≫ τ` from the universal property
    of `φ ≫ ψ`. This will be the morphism induced by `φ`. -/
    use map p (f ≫ g) (φ ≫ ψ) (f' := f ≫ g ≫ h) (assoc f g h).symm (φ ≫ τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    /- The fact that `ψ ≫ π = τ` follows from `φ ≫ ψ ≫ π = φ ≫ τ` and the universal property of
    `φ`. -/
    · apply IsStronglyCocartesian.ext p f φ (g ≫ h) <| by simp only [← assoc, fac]
    -- Finally, uniqueness of `π` comes from the universal property of `φ ≫ ψ`.
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply map_uniq
      simp [hπ'₂.symm]

end

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S)

instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCocartesian p f φ.hom where
  universal_property' := by
    intro b' g τ hτ
    use φ.inv ≫ τ
    refine ⟨?_, by cat_disch⟩
    simpa [← assoc] using (IsHomLift.comp p (isoOfIsoLift p f φ).inv (f ≫ g) φ.inv τ)

instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCocartesian p f φ :=
  @IsStronglyCocartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

/-- A strongly co-Cartesian arrow lying over an isomorphism is an isomorphism. -/
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCocartesian p f φ] [IsIso f] : IsIso φ := by
  subst_hom_lift p f φ; clear a b R S
  -- Let `φ'` be the morphism induced by applying universal property to `𝟙 a` lying over `f ≫ f⁻¹`.
  let φ' := map p (p.map φ) φ (IsIso.hom_inv_id (p.map φ)).symm (𝟙 a)
  use φ'
  -- `φ ≫ φ' = 𝟙 a` follows immediately from the universal property.
  have inv_hom : φ ≫ φ' = 𝟙 a := fac p (p.map φ) φ _ (𝟙 a)
  refine ⟨inv_hom, ?_⟩
  -- We will now show that `φ' ≫ φ = 𝟙 b` by showing that `φ ≫ (φ' ≫ φ) = φ ≫ 𝟙 b`.
  have h₁ : IsHomLift p (𝟙 (p.obj b)) (φ' ≫ φ) := by
    rw [← IsIso.inv_hom_id (p.map φ)]
    apply IsHomLift.comp
  apply IsStronglyCocartesian.ext p (p.map φ) φ (𝟙 (p.obj b))
  simp only [← assoc, inv_hom, comp_id, id_comp]

end

/-- The canonical isomorphism between the codomains of two strongly co-Cartesian arrows lying over
isomorphic objects. -/
noncomputable def codomainIsoOfBaseIso {R S S' : 𝒮} {a b b' : 𝒳} {f : R ⟶ S} {f' : R ⟶ S'}
    {g : S ≅ S'} (h : f' = f ≫ g.hom) (φ : a ⟶ b) (φ' : a ⟶ b') [IsStronglyCocartesian p f φ]
    [IsStronglyCocartesian p f' φ'] : b ≅ b' where
  hom := map p f φ h φ'
  inv := @map _ _ _ _ p _ _ _ _ f' φ' _ _ _ _ _ (congrArg (· ≫ g.inv) h.symm) φ
    (by simp only [assoc, Iso.hom_inv_id, comp_id]; infer_instance)

end IsStronglyCocartesian

end CategoryTheory.Functor
