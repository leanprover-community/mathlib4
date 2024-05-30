/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Cartesian morphisms

This file defines cartesian resp. strongly cartesian morphisms with respect to a functor
`p : 𝒳 ⟶ 𝒮`.

## Main definitions

- `IsCartesian p f φ` expresses that `φ` is a cartesian arrow lying over `f` with respect to `p`.
This structure extends `IsHomLift p f φ`.

`IsStronglyCartesian p f φ` expresses that `φ` is a cartesian arrow lying over `f` with respect to
`p`. This structure also extends `IsHomLift p f φ`.

## Implementation

The standard constructor of `IsStronglyCartesian` has both been renamed to `.mk'`, and we
have provided an alternate constructor `IsStronglyCartesian.mk`. The difference between the two
is that `IsStronglyCartesian.mk` peforms some substitutions of superfluous variables for the user.
It is recommended to use these instead to minimize the amount of equalities that needs to be carried
around in the construction.

## References
SGA 1
Stacks project

-/

/-
TODO:
- (after) fix mk' documentation in file docstring
- Fix variables in two remaining lemmas
- Fix docstrings
- clean up proofs
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

namespace CategoryTheory

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮)

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)

/-- The proposition that a morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is a
cartesian morphism. See SGA 1 VI 5.1. -/
class Functor.IsCartesian extends IsHomLift p f φ : Prop where
  universal_property {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p (𝟙 R) χ ∧ χ ≫ φ = φ'

/-- The proposition that a morphism `φ : a ⟶ b` in `𝒳` lying over `f : R ⟶ S` in `𝒮` is a
strongly cartesian morphism.

See <https://stacks.math.columbia.edu/tag/02XK> -/
class Functor.IsStronglyCartesian extends IsHomLift p f φ : Prop where
  universal_property' {a' : 𝒳} (g : p.obj a' ⟶ R) (φ' : a' ⟶ b) [IsHomLift p (g ≫ f) φ'] :
      ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ'

end

namespace IsCartesian

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsCartesian p f φ]

section

variable {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ']

/-- Given a cartesian arrow `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, a morphism `φ' : a' ⟶ b`
lifting `𝟙 R`, then `inducedMap f φ φ'` is the morphism `a' ⟶ a` obtained from the universal
property of `φ`. -/
noncomputable def inducedMap : a' ⟶ a :=
  Classical.choose <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ'

instance inducedMap_isHomLift : IsHomLift p (𝟙 R) (inducedMap p f φ φ') :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.1

@[simp]
lemma inducedMap_comp : (inducedMap p f φ φ') ≫ φ = φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').1.2

/-- Given a cartesian arrow `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, a morphism `φ' : a' ⟶ b`
lifting `𝟙 R`, and a morphism `ψ : a' ⟶ a` such that `g ≫ ψ = φ'`. Then `ψ` is the map induced
by the universal property of `φ`. -/
lemma inducedMap_unique (ψ : a' ⟶ a) [IsHomLift p (𝟙 R) ψ] (hψ : ψ ≫ φ = φ') :
    ψ = inducedMap p f φ φ' :=
  (Classical.choose_spec <| IsCartesian.universal_property (p:=p) (f:=f) (φ:=φ) φ').2
    ψ ⟨inferInstance, hψ⟩

/-- Given a cartesian arrow `φ : a ⟶ b` lying over `f : R ⟶ S` in `𝒳`, a morphism `φ' : a' ⟶ b`
lifting `𝟙 R`, and two morphisms `ψ ψ' : a' ⟶ a` such that `g ≫ ψ = φ' = g ≫ ψ'`. Then we must
have `ψ = ψ'`. -/
protected lemma uniqueness {ψ ψ' : a' ⟶ a} [IsHomLift p (𝟙 R) ψ] [IsHomLift p (𝟙 R) ψ']
    (hcomp : ψ ≫ φ = φ') (hcomp' : ψ' ≫ φ = φ') : ψ = ψ' := by
  rw [inducedMap_unique p f φ φ' ψ hcomp, inducedMap_unique p f φ φ' ψ' hcomp']

end

@[simp]
lemma inducedMap_self_eq_id : inducedMap p f φ φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply inducedMap_unique
  simp only [id_comp]

/-- The canonical isomorphism between the domains of two cartesian arrows
lying over the same object. -/
@[simps]
noncomputable def naturalIso {a' : 𝒳} (φ' : a' ⟶ b) [IsHomLift p f φ'] [IsCartesian p f φ'] :
    a' ≅ a where
  hom := inducedMap p f φ φ'
  inv := inducedMap p f φ' φ
  hom_inv_id := by
    subst_hom_lift p f φ'
    apply IsCartesian.uniqueness p (p.map φ') φ' φ' (by simp) (id_comp _)
  inv_hom_id := by
    subst_hom_lift p f φ
    apply IsCartesian.uniqueness p (p.map φ) φ φ (by simp) (id_comp _)

end IsCartesian

namespace IsStronglyCartesian

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) [IsStronglyCartesian p f φ]

lemma universal_property {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (f' : R' ⟶ S) (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ' := by
  subst_hom_lift p f' φ'; clear a b R S
  have : p.IsHomLift (g ≫ f) φ' := (hf' ▸ inferInstance)
  apply IsStronglyCartesian.universal_property' f

instance isCartesian_of_isStronglyCartesian [p.IsStronglyCartesian f φ] : p.IsCartesian f φ where
  universal_property := fun φ' => universal_property p f φ (𝟙 R) f (by simp) φ'

-- TODO: section here

/-- Given a cartesian morphism `φ`, a diagram
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
and an arrow `φ' : a' ⟶ b`, then `inducedMap` is the map `a' ⟶ a` obtained from the
universal property of `φ`. -/
noncomputable def inducedMap {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : a' ⟶ a :=
  Classical.choose <| universal_property p f φ _ _ hf' φ'

instance inducedMap_isHomLift {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : IsHomLift p g (inducedMap p f φ hf' φ') :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.1

@[simp]
lemma inducedMap_comp {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] : (inducedMap p f φ hf' φ') ≫ φ = φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').1.2

/-- Given a cartesian arrow `φ : a ⟶ b` in `𝒳` and a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
Then for any arrow `φ' : a' ⟶ b`, and `ψ : a' ⟶ a` such that `g ≫ ψ = φ'`.
Then `ψ` is the map induced by the universal property. -/
lemma inducedMap_unique {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] (ψ : a' ⟶ a) [IsHomLift p g ψ] (hψ : ψ ≫ φ = φ') :
    ψ = inducedMap p f φ hf' φ' :=
  (Classical.choose_spec <| universal_property p f φ _ _ hf' φ').2 ψ ⟨inferInstance, hψ⟩

/-- Given a cartesian arrow `φ : a ⟶ b` in `𝒳` and a diagram: TODO COMMENTS
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
with `φ` a cartesian arrow. Then for any arrow `φ' : a' ⟶ b`, any two arrows `ψ ψ' : a' ⟶ a` such
that `g ≫ ψ = φ' = g ≫ ψ'`. Then `ψ = ψ'`. -/
protected lemma uniqueness {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    (φ' : a' ⟶ b) [IsHomLift p f' φ'] {ψ ψ' : a' ⟶ a} [IsHomLift p g ψ]
    [IsHomLift p g ψ'] (hcomp : ψ ≫ φ = φ') (hcomp' : ψ' ≫ φ = φ') : ψ = ψ' := by
  rw [inducedMap_unique p f φ hf' φ' ψ hcomp, inducedMap_unique p f φ hf' φ' ψ' hcomp']

@[simp]
lemma inducedMap_self_eq_id : inducedMap p f φ (id_comp f).symm φ = 𝟙 a := by
  subst_hom_lift p f φ; symm
  apply inducedMap_unique
  simp only [id_comp]

/- The composition of two induced maps is also an induced map.
Given a diagrams
```
a''         a'        a --φ--> b          a' --φ'--> b          a'' --φ''--> b
|           |         |        |    and   |          |    and   |            |
v           v         v        v          v          v          v            v
R'' --g'--> R' --g--> R --f--> S          R' --f'--> S          R'' --f''--> S
```
such that `φ` and `φ'` are cartesian arrows. Composing the induced map from `a'' ⟶ a'` with the
induced map from `a' ⟶ a` gives the induced map from `a'' ⟶ a`. -/
-- TODO: fix assumptions here... Why are these compositions necessary? g, h are not mentioned...
@[simp]
lemma inducedMap_inducedMap {R' R'' : 𝒮} {a' a'' : 𝒳} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R}
    {g' : R'' ⟶ R'} (H : f' = g ≫ f) (H' : f'' = g' ≫ f') (φ' : a' ⟶ b) (φ'' : a'' ⟶ b)
    [IsStronglyCartesian p f' φ'] [IsHomLift p f'' φ''] :
    inducedMap p f' φ' H' φ'' ≫ inducedMap p f φ H φ' =
      inducedMap p f φ (show f'' = (g' ≫ g) ≫ f by rwa [assoc, ← H]) φ'' := by
  apply inducedMap_unique p f φ
  simp only [assoc, inducedMap_comp]

/-- Given two cartesian arrows `φ`, `ψ` as follows
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then the composite `φ ≫ ψ` is also cartesian. -/
-- TODO: fix assumptions here...
instance comp {T : 𝒮} {c : 𝒳} (f : R ⟶ S) (g : S ⟶ T) (φ : a ⟶ b)
    (ψ : b ⟶ c) [IsStronglyCartesian p f φ] [IsStronglyCartesian p g ψ] :
      IsStronglyCartesian p (f ≫ g) (φ ≫ ψ) where
  universal_property' := by
    intro a' h τ hτ
    -- TODO: can simplify this line??
    use inducedMap p f φ (rfl (a := h ≫ f)) (inducedMap p g ψ (assoc h f g).symm τ)
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [← assoc, inducedMap_comp, inducedMap_comp]
    · intro π' ⟨hπ'₁, hπ'₂⟩
      apply inducedMap_unique
      apply inducedMap_unique
      simp only [assoc, hπ'₂]

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that the composite `φ ≫ ψ` and `ψ` are cartesian, then so is `φ`. -/
-- TODO: fix assumptions here...
protected lemma of_comp {R S T : 𝒮} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T}
    {φ : a ⟶ b} {ψ : b ⟶ c} [IsStronglyCartesian p g ψ] [IsStronglyCartesian p (f ≫ g) (φ ≫ ψ)]
    [IsHomLift p f φ] : IsStronglyCartesian p f φ where
  universal_property' := by
    -- Fix a morphism `τ : a' ⟶ b` and a morphism `h : p(a') ⟶ R` such that `τ` lifts `h ≫ f`
    intro a' h τ hτ
    have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp p (h ≫ f) _ τ ψ
    -- We get a morphism `π : a' ⟶ a` from the universal property of `φ ≫ ψ`
    use inducedMap p (f ≫ g) (φ ≫ ψ) (f' := h ≫ f ≫ g) rfl (τ ≫ ψ)
    refine ⟨⟨inferInstance, ?_⟩,?_⟩
    -- The fact that `π ≫ φ = τ` follows from `π ≫ φ ≫ ψ = τ ≫ ψ` and the universal property of `ψ`
    · apply IsStronglyCartesian.uniqueness p g ψ (g := h ≫ f) rfl (τ ≫ ψ) (by simp) rfl
    -- Finally, uniqueness of `π` comes from the universal property of `φ ≫ ψ`
    intro π' ⟨hπ'₁, hπ'₂⟩
    apply inducedMap_unique
    simp [hπ'₂.symm]

end

section

variable {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S)

instance of_iso (φ : a ≅ b) [IsHomLift p f φ.hom] : IsStronglyCartesian p f φ.hom where
  universal_property' := by
    intro a' g τ hτ
    use τ ≫ φ.inv
    refine ⟨?_, by aesop_cat⟩
    simpa using (IsHomLift.comp p (g ≫ f) (isoOfIsoLift p f φ).inv τ φ.inv)

instance of_isIso (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsStronglyCartesian p f φ :=
  @IsStronglyCartesian.of_iso _ _ _ _ p _ _ _ _ f (asIso φ) (by aesop)

/-- A cartesian arrow lying over an isomorphism is an isomorphism. -/
lemma isIso_of_base_isIso (φ : a ⟶ b) [IsStronglyCartesian p f φ] (hf : IsIso f) : IsIso φ := by
  -- The inverse will be given by applying the universal property to the arrows f⁻¹ : S ⟶ R and 𝟙 b
  subst_hom_lift p f φ; clear a b R S
  let φ' := inducedMap p (p.map φ) φ (IsIso.inv_hom_id (p.map φ)).symm (𝟙 b)
  use φ'
  -- `φ' ≫ φ = 𝟙 b` follows immediately from the universal property
  have inv_hom : φ' ≫ φ = 𝟙 b := inducedMap_comp p (p.map φ) φ _ (𝟙 b)
  refine ⟨?_, inv_hom⟩
  -- We now show that `φ ≫ φ' = 𝟙 a` by applying the universal property of `φ` to the equality
  -- `φ ≫ φ' ≫ φ = φ ≫ 𝟙 b = 𝟙 a ≫ φ`
  have h₁ : IsHomLift p (𝟙 (p.obj a)) (φ  ≫ φ') := by
    rw [← IsIso.hom_inv_id (p.map φ)]
    apply IsHomLift.comp
  have h₂ : IsHomLift p (p.map φ) (φ ≫ φ' ≫ φ) := by
    simpa using IsHomLift.comp p (𝟙 (p.obj a)) (p.map φ) (φ ≫ φ') φ
  apply IsStronglyCartesian.uniqueness p _ φ (id_comp (p.map φ)).symm (φ ≫ φ' ≫ φ)
  · apply Category.assoc
  · simp only [inv_hom, id_comp, comp_id]

end

/-- The canonical isomorphism between the domains of two cartesian arrows lying over
isomorphic objects. -/
noncomputable def isoOfBaseIso {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S}
  {g : R' ≅ R} (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b) [IsStronglyCartesian p f φ]
    [IsStronglyCartesian p f' φ'] : a' ≅ a where
  hom := inducedMap p f φ h φ'
  inv := @inducedMap _ _ _ _ p _ _ _ _ f' φ' _ _ _ _ _ (congrArg (g.inv ≫ ·) h.symm) φ
    (by simp; infer_instance)

end IsStronglyCartesian

end CategoryTheory
