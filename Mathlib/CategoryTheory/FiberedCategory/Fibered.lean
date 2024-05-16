/-
Copyright (c) 2024 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Calle Sönne
-/

import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!

# Fibered categories

This file defines what it means for a functor `p : 𝒳 ⥤ 𝒮` to be fibered`.

## Main definitions

- `IsPullback p f φ` expresses that `φ` is furthermore a pullback of `f` along `p`. This structure
extends `IsHomLift p f φ`.
- `IsFibered p` expresses that `p` gives `𝒳` the structure of a fibered category over `𝒮`, i.e.
that for every morphism `f : S ⟶ R` in `𝒮` and every object `b` in `𝒳` with `p(b)=R` there is a
pullback `φ : a ⟶ b`  of `f`.

## Implementation
The standard constructors of `IsPullback` and `IsFibered` have both been renamed to `.mk'`. We have
provided alternate lemmas `IsPullback.mk` and `IsFibered.mk` for constructing instances of these
structures, and it is recommended to use these instead to minimize the amount of equalities that
needs to be carried around in the construction.

The reason for this is the following:
Just like `IsHomLift p f φ`, we have phrased `IsPullback p f φ` in a way to make its usage as
flexible  as possible with respect to non-definitional equalities of domains / codomains.
In particular, given a lift
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
(by which we mean an object of `IsHomLift p f φ`). We say that it is a pullback if for all arrows
`g : R' ⟶ R`, and all lifts
```
  a' --φ'--> b
  -          -
  |          |
  v          v
  R' --f'--> S
```
such that `f' = g ≫ f`, there is a unique induced map .... (TODO)
This definition gives us some flexibility in that it allows us to take `f'` to be non-definitionally
equal to `g ≫ f`, and `p(a')` to be non-definitionally equal to `R'`.

Similarly, `IsFibered p` is phrased as saying that for every `f : R ⟶ S`, and every `a` such that
`p(a)=S`, there is a pullback `φ` lying over `f`. The alternate constructor `IsFibered.mk` only
requires us to construct this pullback for every `a` and every `f : R ⟶ p(a)`.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Functor Category IsHomLift

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- The proposition that a lift
```
  a --φ--> b
  -        -
  |        |
  v        v
  R --f--> S
```
is a pullback.
-/
structure IsPullback (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) extends
    IsHomLift p f φ : Prop where mk' ::
  (UniversalProperty {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S}
    (_ : f' = g ≫ f) {φ' : a' ⟶ b} (_ : IsHomLift p f' φ') :
      ∃! χ : a' ⟶ a, IsHomLift p g χ ∧ χ ≫ φ = φ')

/-- Definition of a Fibered category. -/
class IsFibered (p : 𝒳 ⥤ 𝒮) : Prop where mk' ::
  (has_pullbacks {a : 𝒳} {R S : 𝒮} (_ : p.obj a = S) (f : R ⟶ S) :
    ∃ (b : 𝒳) (φ : b ⟶ a), IsPullback p f φ)

protected lemma IsPullback.mk {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : b ⟶ a}
    (hφ : IsHomLift p f φ) (h : ∀ (a' : 𝒳) (g : p.obj a' ⟶ R) (φ' : a' ⟶ a),
      IsHomLift p (g ≫ f) φ' → ∃! χ : a' ⟶ b, IsHomLift p g χ ∧ χ ≫ φ = φ') :
        IsPullback p f φ where
  toIsHomLift := hφ
  UniversalProperty := by
    intro R' a' g f' hf' φ' hφ'
    have := hφ'.ObjLiftDomain.symm
    subst this
    subst hf'
    apply h a' g φ' hφ'

protected lemma IsFibered.mk {p : 𝒳 ⥤ 𝒮} (h : ∀ (a : 𝒳) (R : 𝒮) (f : R ⟶ p.obj a),
    ∃ (b : 𝒳) (φ : b ⟶ a), IsPullback p f φ) : IsFibered p where
  has_pullbacks := @fun a R S ha f => by subst ha; apply h a R f

namespace IsPullback

/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
such that φ is a pullback, and an arrow φ' : a' ⟶ b,
the induced map is the map a' ⟶ a obtained from the
universal property of φ. -/
noncomputable def InducedMap {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') : a' ⟶ a :=
  Classical.choose $ hφ.UniversalProperty hf' hφ'

lemma InducedMap_IsHomLift {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') : IsHomLift p g (InducedMap hφ hf' hφ') :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).1.1

@[simp]
lemma InducedMap_Diagram {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') : (InducedMap hφ hf' hφ') ≫ φ = φ' :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).1.2

/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
with φ a pullback. Then for any arrow φ' : a' ⟶ b, and ψ : a' ⟶ a such that
g ≫ ψ = φ'. Then ψ equals the induced pullback map. -/
lemma InducedMap_unique {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') {ψ : a' ⟶ a} (hψ : IsHomLift p g ψ)
    (hcomp : ψ ≫ φ = φ') : ψ = InducedMap hφ hf' hφ' :=
  (Classical.choose_spec (hφ.UniversalProperty hf' hφ')).2 ψ ⟨hψ, hcomp⟩

-- TODO: API to deal with the f' = g ≫ f stuff...?
/-- Given a diagram:
```
a'        a --φ--> b
|         |        |
v         v        v
R' --g--> R --f--> S
```
with φ a pullback. Then for any arrow φ' : a' ⟶ b, any two arrows ψ ψ' : a' ⟶ a such that
g ≫ ψ = φ' = g ≫ ψ'. Then ψ = ψ'. -/
protected lemma uniqueness {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback p f φ) {R' : 𝒮} {a' : 𝒳} {g : R' ⟶ R} {f' : R' ⟶ S} (hf' : f' = g ≫ f)
    {φ' : a' ⟶ b} (hφ' : IsHomLift p f' φ') {ψ ψ' : a' ⟶ a} (hψ : IsHomLift p g ψ)
    (hψ' : IsHomLift p g ψ') (hcomp : ψ ≫ φ = φ') (hcomp' : ψ' ≫ φ = φ') : ψ = ψ' := by
  rw [InducedMap_unique hφ hf' hφ' hψ hcomp, InducedMap_unique hφ hf' hφ' hψ' hcomp']

@[simp]
lemma InducedMap_self_eq_id {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback p f φ) : InducedMap hφ (id_comp f).symm hφ.toIsHomLift = 𝟙 a:=
  (InducedMap_unique hφ (id_comp f).symm hφ.toIsHomLift (IsHomLift.id hφ.ObjLiftDomain)
    (id_comp _)).symm

/- The composition of two induced maps is also an induced map...
TODO MAYBE A SLIGHTLY DIFFERENT VERSION OF THIS... (look into where its applied)

Given a diagram:
```
a''         a'        a --φ--> b
|           |         |        |
v           v         v        v
R'' --h'--> R' --h--> R --f--> S
``` -/
@[simp]
lemma InducedMap_comp {p : 𝒳 ⥤ 𝒮} {R R' R'' S: 𝒮} {a a' a'' b : 𝒳}
    {f : R ⟶ S} {f' : R' ⟶ S} {f'' : R'' ⟶ S} {g : R' ⟶ R} {h : R'' ⟶ R'}
    (H : f' = g ≫ f) (H' : f'' = h ≫ f') {φ : a ⟶ b} {φ' : a' ⟶ b} {φ'' : a'' ⟶ b}
    (hφ : IsPullback p f φ) (hφ' : IsPullback p f' φ') (hφ'' : IsHomLift p f'' φ'') :
    InducedMap hφ' H' hφ'' ≫ InducedMap hφ H hφ'.toIsHomLift
      = InducedMap hφ (show f'' = (h ≫ g) ≫ f by rwa [assoc, ← H]) hφ'' := by
  apply InducedMap_unique
  · apply IsHomLift.comp
    apply InducedMap_IsHomLift
    apply InducedMap_IsHomLift
  · simp only [assoc, InducedMap_Diagram]

/-- Given two pullback squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
Then also the composite φ ≫ ψ is a pullback square. -/
protected lemma comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c: 𝒳} {f : R ⟶ S} {g : S ⟶ T} {φ : a ⟶ b}
    {ψ : b ⟶ c} (hφ : IsPullback p f φ) (hψ : IsPullback p g ψ) :
      IsPullback p (f ≫ g) (φ ≫ ψ) := by
  apply IsPullback.mk
  · apply IsHomLift.comp hφ.toIsHomLift hψ.toIsHomLift
  · intro a' h τ hτ
    use InducedMap hφ rfl (InducedMap_IsHomLift hψ rfl ((assoc h f g).symm ▸ hτ))
    refine ⟨⟨InducedMap_IsHomLift hφ rfl _, ?_⟩, ?_⟩
    · rw [← assoc, (InducedMap_Diagram hφ rfl _), (InducedMap_Diagram hψ rfl _)]
    · intro π' hπ'
      -- TODO: maybe this can be golfed with new uniqueness lemma
      apply InducedMap_unique hφ _ _ hπ'.1
      apply InducedMap_unique hψ _ _ (IsHomLift.comp hπ'.1 hφ.toIsHomLift)
      simp only [assoc, hπ'.2]

/-- Given two commutative squares
```
a --φ--> b --ψ--> c
|        |        |
v        v        v
R --f--> S --g--> T
```
such that the composite φ ≫ ψ and ψ are pullbacks, then so is φ. -/
protected lemma of_comp {p : 𝒳 ⥤ 𝒮} {R S T : 𝒮} {a b c: 𝒳} {f : R ⟶ S} {g : S ⟶ T}
    {φ : a ⟶ b} {ψ : b ⟶ c} (hψ : IsPullback p g ψ) (hcomp : IsPullback p (f ≫ g) (φ ≫ ψ))
    (hφ : IsHomLift p f φ) : IsPullback p f φ := by
  apply IsPullback.mk hφ
  -- Fix a morphism τ : a' ⟶ b and a morphism h : p(a') ⟶ R such that τ lifts h ≫ f
  intro a' h τ hτ
  have h₁ : IsHomLift p (h ≫ f ≫ g) (τ ≫ ψ) := by simpa using IsHomLift.comp hτ hψ.toIsHomLift
  -- We get a morphism π : a' ⟶ a from the universal property of φ ≫ ψ
  use InducedMap hcomp rfl h₁
  refine ⟨⟨InducedMap_IsHomLift hcomp rfl h₁, ?_⟩,?_⟩
  -- The fact that π ≫ φ = τ follows from π ≫ φ ≫ ψ = τ ≫ ψ and the universal property of ψ
  · apply IsPullback.uniqueness hψ rfl (by rwa [assoc]) _ hτ _ rfl
    · apply IsHomLift.comp (InducedMap_IsHomLift hcomp rfl h₁) hφ
    · rw [assoc, (InducedMap_Diagram hcomp rfl h₁)]
  -- Finally, uniqueness of π comes from the universal property of φ ≫ ψ
  intro π' hπ'
  apply InducedMap_unique _ _ _ hπ'.1 (by rw [← hπ'.2, assoc])

lemma of_iso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ≅ b} (hφ : IsHomLift p f φ.hom) :
    IsPullback p f φ.hom := by
  apply IsPullback.mk hφ
  intro a' g τ hτ
  use τ ≫ φ.inv
  refine ⟨?_, by aesop_cat⟩
  simpa using IsHomLift.comp hτ <| IsHomLift.inv_lift_inv' hφ

lemma of_isIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳}
    {f : R ⟶ S} {φ : a ⟶ b} (hφ : IsHomLift p f φ) [IsIso φ] : IsPullback p f φ :=
  IsPullback.of_iso (φ := asIso φ) hφ

/- eqToHom interactions. LEAVE THESE OUT OF FIRST PR! -/

-- TODO: eqToHom is a pullback over eqToHom (should be only one lemma! Should assume IsHomLift!)

lemma eqToHom_codomain {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hba : b = a) {S : 𝒮} (hS : p.obj a = S) :
    IsPullback p (𝟙 S) (eqToHom hba) :=
  of_isIso (eqToHom_codomain_lift_id hba hS)

lemma eqToHom_domain {p : 𝒳 ⥤ 𝒮} {a b : 𝒳} (hba : b = a) {S : 𝒮} (hS : p.obj b = S) :
    IsPullback p (𝟙 S) (eqToHom hba) :=
  of_isIso (eqToHom_domain_lift_id hba hS)

lemma eqToHom_comp {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsPullback p f φ) (hc : c = b) : IsPullback p f (eqToHom hc ≫ φ) :=
  id_comp f ▸ IsPullback.comp (eqToHom_codomain hc hφ.ObjLiftDomain) hφ

lemma comp_eqToHom {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b c : 𝒳} {f : R ⟶ S}
    {φ : b ⟶ a} (hφ : IsPullback p f φ) (hc : a = c) : IsPullback p f (φ ≫ eqToHom hc) :=
  comp_id f ▸ IsPullback.comp hφ (eqToHom_domain hc hφ.ObjLiftCodomain)

/-- A pullback over an isomorphism is an isomorphism. -/
lemma isIso_of_base_isIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    (hφ : IsPullback p f φ) (hf : IsIso f) : IsIso φ := by
  -- The inverse will be given by applying the universal property to f⁻¹ : S ⟶ R and 𝟙 b
  let φ' := InducedMap hφ (IsIso.inv_hom_id f).symm (IsHomLift.id hφ.ObjLiftCodomain)
  use φ'
  -- φ' ≫ φ = 𝟙 b follows immediately from the universal property
  have inv_hom : φ' ≫ φ = 𝟙 b := InducedMap_Diagram hφ (IsIso.inv_hom_id f).symm
    (IsHomLift.id hφ.ObjLiftCodomain)
  refine ⟨?_, inv_hom⟩
  have h₁ : IsHomLift p (𝟙 R) (φ  ≫ φ') := by
    rw [← IsIso.hom_inv_id f]
    apply IsHomLift.comp hφ.toIsHomLift
    apply InducedMap_IsHomLift
  have h₂ : IsHomLift p f (φ ≫ φ' ≫ φ) := by simpa using IsHomLift.comp h₁ hφ.toIsHomLift
  -- φ ≫ φ' = 𝟙 a follows from TODO
  apply IsPullback.uniqueness hφ (id_comp f).symm h₂ h₁ (IsHomLift.id hφ.ObjLiftDomain)
  · apply Category.assoc
  · simp only [inv_hom, id_comp, comp_id]

/-- The canonical isomorphism between two pullbacks lying over isomorphic objects. -/
noncomputable def IsPullbackIso_of_base_Iso {p : 𝒳 ⥤ 𝒮}
  {R R' S : 𝒮} {a a' b : 𝒳} {f : R ⟶ S} {f' : R' ⟶ S} {g : R' ≅ R}
  (H : f' = g.hom ≫ f) {φ : a ⟶ b} {φ' : a' ⟶ b}
  (hφ : IsPullback p f φ) (hφ' : IsPullback p f' φ') : a' ≅ a where
    hom := InducedMap hφ H hφ'.toIsHomLift
    inv := InducedMap hφ' (congrArg (g.inv ≫ ·) H.symm) (by simpa using hφ.toIsHomLift)

/-- The canonical isomorphism between the domains of two pullbacks lying over the same object. -/
noncomputable def IsPullbackIso {p : 𝒳 ⥤ 𝒮} {R S : 𝒮} {a' a b : 𝒳} {f : R ⟶ S} {φ : a ⟶ b}
    {φ' : a' ⟶ b} (hφ : IsPullback p f φ) (hφ' : IsPullback p f φ') : a' ≅ a :=
  IsPullbackIso_of_base_Iso (show f = (Iso.refl R).hom ≫ f by simp) hφ hφ'

end IsPullback

namespace IsFibered

open IsPullback

/-- Given a Fibered category p : 𝒳 ⥤ 𝒫, and a diagram
```
           a
           -
           |
           v
  R --f--> S
```
we have a pullback `R ×_S a` -/
noncomputable def PullbackObj {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p) {R S : 𝒮}
    {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : 𝒳 :=
  Classical.choose (hp.1 ha f)

/-- Given a Fibered category p : 𝒳 ⥤ 𝒫, and a diagram
```
          a
          -
          |
          v
R --f--> S
```
we get a map R ×_S b ⟶ a -/
noncomputable def PullbackMap {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p) {R S : 𝒮}
    {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : PullbackObj hp ha f ⟶ a :=
  Classical.choose (Classical.choose_spec (hp.1 ha f))

lemma PullbackMap.IsPullback {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p) {R S : 𝒮}
    {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : IsPullback p f (PullbackMap hp ha f) :=
  Classical.choose_spec (Classical.choose_spec (hp.1 ha f))

lemma PullbackObj_proj {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
    {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) : p.obj (PullbackObj hp ha f) = R :=
  (PullbackMap.IsPullback hp ha f).ObjLiftDomain

/-- Given a diagram
```
                  a
                  -
                  |
                  v
T --g--> R --f--> S
```
we have an isomorphism T ×_S a ≅ T ×_R (R ×_S a) -/
noncomputable def PullbackPullbackIso {p : 𝒳 ⥤ 𝒮} (hp : IsFibered p)
    {R S T : 𝒮}  {a : 𝒳} (ha : p.obj a = S) (f : R ⟶ S) (g : T ⟶ R) :
      PullbackObj hp ha (g ≫ f) ≅ PullbackObj hp (PullbackObj_proj hp ha f) g :=
  IsPullbackIso (IsPullback.comp (PullbackMap.IsPullback hp (PullbackObj_proj hp ha f) g)
    (PullbackMap.IsPullback hp ha f))
      (PullbackMap.IsPullback hp ha (g ≫ f))

end IsFibered
