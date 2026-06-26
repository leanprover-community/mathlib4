/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Preadditive.Comma
public import Mathlib.CategoryTheory.Quotient.Preadditive
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Weak limits

If `F : J ⥤ C` is a functor and `c : Cone F`, we say that `c` is a weak limit of `F` if
every cone over `F` admits a (not necessarily unique) morphism to `c`. In other words, a
weak limit satisfies the same "versal property" as a limit, without the uniqueness
condition. In particular, weak limits are not unique, and they are not functorial.

We set up some API for weak limits, mostly copied from that for limits, prove that any
limit cone is a weak limit cone, and that, if a limit exists, then it is a retract of any
weak limit (see `Retract.ofIsLimit`).

We then specialize to weak equalizers, weak kernels and weak pullbacks, and give some API
for those shapes, again inspired from the non-weak case. We prove that a category with weak
equalizers and pullbacks has weak pullbacks, and that a preadditive category has weak equalizers
if and only if it has weak kernels.

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {J : Type*} [Category* J] {K : Type*} [Category* K] {C : Type*}
    [Category* C] {F : Functor J C} {D : Type*} [Category* D] {G : Functor K D}

namespace Limits

structure IsWeakLimit (t : Cone F) where
  /-- There is a morphism from any cone point to `t.pt` -/
  lift : ∀ s : Cone F, s.pt ⟶ t.pt
  /-- The map makes the triangle with the two natural transformations commute -/
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j := by cat_disch

attribute [reassoc (attr := simp)] IsWeakLimit.fac

/--
If `F` has a limit, then it is a retract of any weak limit of `F`.
-/
def _root_.Retract.ofIsLimit {t t' : Cone F} (l : IsLimit t) (l' : IsWeakLimit t') :
    Retract t.pt t'.pt where
      i := l'.lift t
      r := l.lift t'
      retract := l.hom_ext (fun _ ↦ by rw [assoc, id_comp, l.fac t', l'.fac t])

/--
If `c : Cone F` is a limit, then it is a weak limit.
-/
def IsWeakLimit_of_isLimit {t : Cone F} (l : IsLimit t) : IsWeakLimit t where
  lift := l.lift
  fac := l.fac

/-- `WeakLimitCone F` contains a cone over `F` together with the information that it is
a weak limit. -/
structure WeakLimitCone (F : J ⥤ C) where
  /-- The cone itself -/
  cone : Cone F
  /-- The proof that is the limit cone -/
  isWeakLimit : IsWeakLimit cone

/--
Any limit cone defines a weak limit cone with the same underlying cone over `F` and the same
lifts.
-/
def WeakLimitCone_of_limitCone {F : J ⥤ C} (c : LimitCone F) : WeakLimitCone F where
  cone := c.cone
  isWeakLimit := IsWeakLimit_of_isLimit c.isLimit

/-- `HasWeakLimit F` represents the mere existence of a weak limit for `F`. -/
class HasWeakLimit (F : J ⥤ C) : Prop where mk' ::
  /-- There is some weak limit cone for `F` -/
  exists_weakLimit : Nonempty (WeakLimitCone F)

/--
If `F` has a limit, then it has a weak limit.
-/
lemma HasWeakLimit_of_hasLimit (F : J ⥤ C) [HasLimit F] : HasWeakLimit F where
  exists_weakLimit := Nonempty.intro (WeakLimitCone_of_limitCone (getLimitCone F))

theorem HasWeakLimit.mk {F : J ⥤ C} (d : WeakLimitCone F) : HasWeakLimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `WeakLimitCone F` from `HasWeakLimit F`. -/
def getWeakLimitCone (F : J ⥤ C) [HasWeakLimit F] : WeakLimitCone F :=
  Classical.choice <| HasWeakLimit.exists_weakLimit

variable (J C) in
/-- `C` has weak limits of shape `J` if there exists a weak limit for every functor
`F : J ⥤ C`. -/
class HasWeakLimitsOfShape : Prop where
  /-- All functors `F : J ⥤ C` from `J` have weak limits -/
  has_weakLimit : ∀ F : J ⥤ C, HasWeakLimit F := by infer_instance

instance (priority := 100) hasWeakLimitOfHasWeakLimitsOfShape
    [HasWeakLimitsOfShape J C] (F : J ⥤ C) : HasWeakLimit F :=
  HasWeakLimitsOfShape.has_weakLimit F

instance (priority := 100) hasWeakLimitsOfShapeOfHasLimitsOfShape {J : Type*} [Category* J]
    [HasLimitsOfShape J C] : HasWeakLimitsOfShape J C where
      has_weakLimit F := HasWeakLimit_of_hasLimit F

-- Interface to the `HasWeakLimit` class.
/-- An arbitrary choice of weak limit cone for a functor. -/
def weakLimit.cone (F : J ⥤ C) [HasWeakLimit F] : Cone F :=
  (getWeakLimitCone F).cone

/-- An arbitrary choice of weak limit object of a functor. -/
def weakLimit (F : J ⥤ C) [HasWeakLimit F] :=
  (weakLimit.cone F).pt

/-- The projection from the weak limit object to a value of the functor. -/
def weakLimit.π (F : J ⥤ C) [HasWeakLimit F] (j : J) : weakLimit F ⟶ F.obj j :=
  (weakLimit.cone F).π.app j

@[reassoc]
theorem weakLimit.π_comp_eqToHom (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (hj : j = j') :
    weakLimit.π F j ≫ eqToHom (by subst hj; rfl) = weakLimit.π F j' := by
  subst hj
  simp

@[simp]
theorem weakLimit.cone_x {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).pt = weakLimit F := rfl

@[simp]
theorem weakLimit.cone_π {F : J ⥤ C} [HasWeakLimit F] :
    (weakLimit.cone F).π.app = weakLimit.π _ := rfl

@[reassoc (attr := simp)]
theorem weakLimit.w (F : J ⥤ C) [HasWeakLimit F] {j j' : J} (f : j ⟶ j') :
    weakLimit.π F j ≫ F.map f = weakLimit.π F j' :=
  (weakLimit.cone F).w f

/-- Evidence that the arbitrary choice of cone provided by `weakLimit.cone F`
is a weak limit cone. -/
def weakLimit.isWeakLimit (F : J ⥤ C) [HasWeakLimit F] :
    IsWeakLimit (weakLimit.cone F) :=
  (getWeakLimitCone F).isWeakLimit

/-- A morphism from the cone point of any other cone to the weak limit object. -/
def weakLimit.lift (F : J ⥤ C) [HasWeakLimit F] (c : Cone F) :
    c.pt ⟶ weakLimit F :=
  (weakLimit.isWeakLimit F).lift c

@[simp]
theorem weakLimit.isWeakLimit_lift {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) :
    (weakLimit.isWeakLimit F).lift c = weakLimit.lift F c :=
  rfl

@[reassoc (attr := simp)]
theorem weakLimit.lift_π {F : J ⥤ C} [HasWeakLimit F] (c : Cone F) (j : J) :
    weakLimit.lift F c ≫ weakLimit.π F j = c.π.app j :=
  IsWeakLimit.fac _ c j

namespace IsWeakLimit

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
def ofIsoWeakLimit {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) : IsWeakLimit t where
  lift s := P.lift s ≫ i.hom.hom
  fac s j := by simp

theorem ofIsoWeakLimit_lift {r t : Cone F} (P : IsWeakLimit r) (i : r ≅ t) (s) :
    (P.ofIsoWeakLimit i).lift s = P.lift s ≫ i.hom.hom :=
  rfl

/-- The versal morphism from any other cone to a weak limit cone. -/
def liftConeMorphism {t : Cone F} (h : IsWeakLimit t) (s : Cone F) : s ⟶ t where hom := h.lift s

/-- Given a right adjoint functor between categories of cones,
the image of a weak limit cone is a weak limit cone.
-/
def ofRightAdjoint {left : Cone F ⥤ Cone G} {right : Cone G ⥤ Cone F}
    (adj : left ⊣ right) {c : Cone G} (t : IsWeakLimit c) : IsWeakLimit (right.obj c) where
      lift s := (adj.homEquiv s c (t.liftConeMorphism _)).hom
      fac s j := by simp

end IsWeakLimit

/-- If a functor `F` has a weak limit, so does any naturally isomorphic functor.
-/
theorem hasWeakLimit_of_iso {F G : J ⥤ C} [HasWeakLimit F] (α : F ≅ G) : HasWeakLimit G :=
  HasWeakLimit.mk
    { cone := (Cone.postcompose α.hom).obj (weakLimit.cone F)
      isWeakLimit := {
        lift s := (weakLimit.isWeakLimit F).lift ((Cone.postcompose α.inv).obj s)
        fac s j := by
          simp only [Cone.postcompose_obj_π, weakLimit.cone_x, NatTrans.comp_app, weakLimit.cone_π]
          refine (weakLimit.lift_π_assoc ((Cone.postcompose α.inv).obj s) j (α.hom.app j)).trans ?_
          simp only [Cone.postcompose_obj_π, NatTrans.comp_app]
          change (_ ≫ _) ≫ _ = _
          rw [assoc, Iso.inv_hom_id_app, comp_id]}
      }

theorem hasWeakLimit_iff_of_iso {F G : J ⥤ C} (α : F ≅ G) : HasWeakLimit F ↔ HasWeakLimit G :=
  ⟨fun _ ↦ hasWeakLimit_of_iso α, fun _ ↦ hasWeakLimit_of_iso α.symm⟩

section WeakEqualizer

variable {X Y : C} (f g : X ⟶ Y)

/-- Two parallel morphisms `f` and `g` have a weak equalizer if the diagram `parallelPair f g`
has a weak limit. -/
abbrev HasWeakEqualizer :=
  HasWeakLimit (parallelPair f g)

variable [HasWeakEqualizer f g]

/-- If a weak equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
saying `weakEqualizer f g`. -/
noncomputable abbrev weakEqualizer : C :=
  weakLimit (parallelPair f g)

/-- If a weak equalizer of `f` and `g` exists, we can access the morphism
`weakEqualizer f g ⟶ X` by saying `weakEqualizer.ι f g`. -/
noncomputable abbrev weakEqualizer.ι : weakEqualizer f g ⟶ X :=
  weakLimit.π (parallelPair f g) WalkingParallelPair.zero

/-- A weak equalizer cone for a parallel pair `f` and `g` -/
noncomputable abbrev weakEqualizer.fork : Fork f g :=
  weakLimit.cone (parallelPair f g)

@[simp]
theorem weakEqualizer.fork_ι : (weakEqualizer.fork f g).ι = weakEqualizer.ι f g :=
  rfl

@[simp]
theorem weakEqualizer.fork_π_app_zero :
    (weakEqualizer.fork f g).π.app WalkingParallelPair.zero = weakEqualizer.ι f g :=
  rfl

@[reassoc]
theorem weakEqualizer.condition : weakEqualizer.ι f g ≫ f = weakEqualizer.ι f g ≫ g :=
  Fork.condition <| weakLimit.cone <| parallelPair f g

set_option backward.defeqAttrib.useBackward true in
/-- The weak equalizer built from `weakEqualizer.ι f g` is weakly limiting. -/
def weakEqualizerIsWeakEqualizer : IsWeakLimit (Fork.ofι (weakEqualizer.ι f g)
    (weakEqualizer.condition f g)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

variable {f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the weak equalizer of
`f` and `g` via `weakEqualizer.lift : W ⟶ weakEqualizer f g`. -/
noncomputable abbrev weakEqualizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ weakEqualizer f g :=
  weakLimit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]
theorem weakEqualizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    weakEqualizer.lift k h ≫ weakEqualizer.ι f g = k :=
  weakLimit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakEqualizer f g` satisfying `l ≫ weakEqualizer.ι f g = k`. -/
def weakEqualizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ weakEqualizer f g // l ≫ weakEqualizer.ι f g = k } :=
  ⟨weakEqualizer.lift k h, weakEqualizer.lift_ι _ _⟩

variable (C)

/-- A category `HasWeakEqualizers` if it has all weak limits of shape `WalkingParallelPair`,
i.e. if it has a weak equalizer for every parallel pair of morphisms. -/
abbrev HasWeakEqualizers :=
  HasWeakLimitsOfShape WalkingParallelPair C

/-- A category with equalizers has weak equalizers. -/
instance (priority := 100) HasWeakEqualizersOfHasEqualizers [HasEqualizers C] :
    HasWeakEqualizers C where

/-- If `C` has all weak limits of diagrams `parallelPair f g`, then it has all weak equalizers -/
theorem hasWeakEqualizers_of_hasWeakLimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasWeakLimit (parallelPair f g)] : HasWeakEqualizers C :=
  { has_weakLimit := fun F => hasWeakLimit_of_iso (diagramIsoParallelPair F).symm }

variable {C}

/-- This is a slightly more convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[simps]
def Fork.IsWeakLimit.mk (t : Fork f g) (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s) : IsWeakLimit t :=
  { lift
    fac := fun s j =>
      WalkingParallelPair.casesOn j (fac s) <| by
        simp [← Category.assoc, fac]}

/-- This is another convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
def Fork.IsWeakLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : ∀ s : Fork f g, { l // l ≫ t.ι = s.ι}) :
    IsWeakLimit t :=
  Fork.IsWeakLimit.mk t (fun s => (create s).1) (fun s => (create s).2)

end WeakEqualizer

section WeakKernel

variable [HasZeroMorphisms C]

/-- A morphism `f` has a weak kernel if the functor `ParallelPair f 0` has a weak limit. -/
abbrev HasWeakKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasWeakLimit (parallelPair f 0)

/-- If a morphism `f` has a kernel, then it has a weak kernel. -/
lemma HasWeakKernelOfHasKernel {X Y : C} (f : X ⟶ Y) [HasKernel f] : HasWeakKernel f :=
  HasWeakLimit_of_hasLimit _

variable (C) in
/-- `HasWeakKernels` represents the existence of weak kernels for every morphism. -/
class HasWeakKernels : Prop where
  has_weakLimit : ∀ {X Y : C} (f : X ⟶ Y), HasWeakKernel f := by infer_instance

attribute [instance 100] HasWeakKernels.has_weakLimit

/-- If a category has kernels, then it has weak kernels. -/
instance (priority := 100) HasWeakKernelsOfHasKernels [HasKernels C] :
    HasWeakKernels C where
      has_weakLimit _ := HasWeakKernelOfHasKernel _

section

variable {X Y : C} (f : X ⟶ Y) [HasWeakKernel f]

/-- The weak kernel of a morphism. -/
abbrev weakKernel : C :=
  weakEqualizer f 0

/-- The map from `weakKernel f` into the source of `f`. -/
abbrev weakKernel.ι : weakKernel f ⟶ X :=
  weakEqualizer.ι f 0

@[simp]
theorem weakEqualizer_as_weakKernel : weakEqualizer.ι f 0 = weakKernel.ι f := rfl

@[reassoc (attr := simp)]
theorem weakKernel.condition : weakKernel.ι f ≫ f = 0 :=
  KernelFork.condition _

set_option backward.defeqAttrib.useBackward true in
/-- The weak kernel built from `weakKernel.ι f` is weakly limiting. -/
def weakKernelIsWeakKernel :
    IsWeakLimit (Fork.ofι (weakKernel.ι f) ((weakKernel.condition f).trans comp_zero.symm)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through
`weakKernel.ι f` via `weakKernel.lift : W ⟶ weakKernel f`. -/
abbrev weakKernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ weakKernel f :=
  (weakKernelIsWeakKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
theorem weakKernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    weakKernel.lift f k h ≫ weakKernel.ι f = k :=
  (weakKernelIsWeakKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ weakKernel f`
such that `l ≫ weakKernel.ι f = k`. -/
def weakKernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) :
    { l : W ⟶ weakKernel f // l ≫ weakKernel.ι f = k } :=
  ⟨weakKernel.lift f k h, weakKernel.lift_ι _ _ _⟩

end

end WeakKernel

section WeakPullback

variable {W X Y Z : C}

/-- Two morphisms `f : X ⟶ Z` and `g : Y ⟶ Z` have a weak pullback if the diagram
`cospan f g` has a weak limit. -/
abbrev HasWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :=
  HasWeakLimit (cospan f g)

/-- `weakPullback f g` computes the weak pullback of a pair of morphisms
with the same target. -/
abbrev weakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :=
  weakLimit (cospan f g)

/-- The cone associated to the weak pullback of `f` and `g` -/
abbrev weakPullback.cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakPullback f g] : PullbackCone f g :=
  weakLimit.cone (cospan f g)

/-- The first projection of the weak pullback of `f` and `g`. -/
abbrev weakPullback.fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ X :=
  weakLimit.π (cospan f g) WalkingCospan.left

/-- The second projection of the weak pullback of `f` and `g`. -/
abbrev weakPullback.snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    weakPullback f g ⟶ Y :=
  weakLimit.π (cospan f g) WalkingCospan.right

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`weakPullback.lift : W ⟶ weakPullback f g`. -/
abbrev weakPullback.lift {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) : W ⟶ weakPullback f g :=
  weakLimit.lift _ (PullbackCone.mk h k w)

set_option backward.isDefEq.respectTransparency false in
lemma weakPullback.exists_lift {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g := by cat_disch) :
    ∃ (l : W ⟶ weakPullback f g),
    l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k :=
  ⟨weakPullback.lift h k, by simp⟩

/-- The cone associated to a weak pullback is a weak limit cone. -/
abbrev weakPullback.isWeakLimit {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (weakPullback.cone f g) :=
  weakLimit.isWeakLimit (cospan f g)

@[simp]
theorem WeakPullbackCone.fst_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.fst (weakLimit.cone (cospan f g)) = weakPullback.fst f g := rfl

@[simp]
theorem WeakPullbackCone.snd_limit_cone {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasWeakLimit (cospan f g)] :
    PullbackCone.snd (weakLimit.cone (cospan f g)) = weakPullback.snd f g := rfl

@[reassoc]
theorem weakPullback.lift_fst {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.fst f g = h :=
  weakLimit.lift_π _ _

@[reassoc]
theorem weakPullback.lift_snd {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasWeakPullback f g] (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
    weakPullback.lift h k w ≫ weakPullback.snd f g = k :=
  weakLimit.lift_π _ _

/-- A pair of morphisms `h : W ⟶ X` and `k : W ⟶ Y` satisfying `h ≫ f = k ≫ g` induces a morphism
`l : W ⟶ weakPullback f g` such that `l ≫ weakPullback.fst = h` and `l ≫ weakPullback.snd = k`. -/
def weakPullback.lift' {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g]
    (h : W ⟶ X) (k : W ⟶ Y) (w : h ≫ f = k ≫ g) :
      { l : W ⟶ weakPullback f g //
      l ≫ weakPullback.fst f g = h ∧ l ≫ weakPullback.snd f g = k } :=
  ⟨weakPullback.lift h k w, weakPullback.lift_fst _ _ _, weakPullback.lift_snd _ _ _⟩

@[reassoc]
theorem weakPullback.condition {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasWeakPullback f g] :
    weakPullback.fst f g ≫ f = weakPullback.snd f g ≫ g :=
  PullbackCone.condition _

/-- Given such a diagram, then there is a natural morphism from the weak pullback of
`W ⟶ S` and `X ⟶ S` to the weak pullback of `Y ⟶ T` and `Z ⟶ T`.

```
W ⟶ Y
  ↘   ↘
  S ⟶ T
  ↗   ↗
X ⟶ Z
```
-/
abbrev weakPullback.map {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [HasWeakPullback f₁ f₂]
    (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [HasWeakPullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
    (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) :
    weakPullback f₁ f₂ ⟶ weakPullback g₁ g₂ :=
  weakPullback.lift (weakPullback.fst f₁ f₂ ≫ i₁) (weakPullback.snd f₁ f₂ ≫ i₂)
    (by simp only [Category.assoc, ← eq₁, ← eq₂, weakPullback.condition_assoc])

/-- A morphism from the weak pullback of `W ⟶ S` and `X ⟶ S` to the weak pullback of
`Y ⟶ T` and `Z ⟶ T` given `S ⟶ T`. -/
abbrev weakPullback.mapDesc {X Y S T : C} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [HasWeakPullback f g]
    [HasWeakPullback (f ≫ i) (g ≫ i)] : weakPullback f g ⟶ weakPullback (f ≫ i) (g ≫ i) :=
  weakPullback.map f g (f ≫ i) (g ≫ i) (𝟙 _) (𝟙 _) i (Category.id_comp _).symm
  (Category.id_comp _).symm

/-- The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone that is a
weak limit, is also a weak limit. -/
def PullbackCone.mkSelfIsWeakLimit {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {t : PullbackCone f g}
    (ht : IsWeakLimit t) : IsWeakLimit (PullbackCone.mk t.fst t.snd t.condition) :=
  IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

/-- The weak pullback cone built from the weak pullback projections is a weak pullback. -/
def weakPullbackIsWeakPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasWeakPullback f g] :
    IsWeakLimit (PullbackCone.mk (weakPullback.fst f g) (weakPullback.snd f g)
    weakPullback.condition) :=
  PullbackCone.mkSelfIsWeakLimit <| weakPullback.isWeakLimit f g

namespace PullbackCone

variable {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- This is a slightly more convenient method to verify that a pullback cone is a weak limit cone.
It only asks for a proof of facts that carry any mathematical content -/
def isWeakLimitAux (t : PullbackCone f g) (lift : ∀ s : PullbackCone f g, s.pt ⟶ t.pt)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ t.fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ t.snd = s.snd) : IsWeakLimit t :=
  { lift
    fac := fun s j => Option.casesOn j (by
        rw [← s.w WalkingCospan.Hom.inl, ← t.w WalkingCospan.Hom.inl, ← Category.assoc]
        congr
        exact fac_left s)
      fun j' => WalkingPair.casesOn j' (fac_left s) (fac_right s)}

/-- This is another convenient method to verify that a pullback cone is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
def isWeakLimitAux' (t : PullbackCone f g)
    (create :
      ∀ s : PullbackCone f g,
        { l //
          l ≫ t.fst = s.fst ∧
            l ≫ t.snd = s.snd}) :
    Limits.IsWeakLimit t :=
  PullbackCone.isWeakLimitAux t (fun s => (create s).1)
    (fun s => (create s).2.1) (fun s => (create s).2.2)

/-- This is a more convenient formulation to show that a `PullbackCone` constructed using
`PullbackCone.mk` is a weak limit cone.
-/
def IsWeakLimit.mk {W : C} {fst : W ⟶ X} {snd : W ⟶ Y} (eq : fst ≫ f = snd ≫ g)
    (lift : ∀ s : PullbackCone f g, s.pt ⟶ W)
    (fac_left : ∀ s : PullbackCone f g, lift s ≫ fst = s.fst)
    (fac_right : ∀ s : PullbackCone f g, lift s ≫ snd = s.snd) :
    IsWeakLimit (PullbackCone.mk fst snd eq) :=
  isWeakLimitAux _ lift fac_left fac_right

/-- If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we get `l : W ⟶ t.pt`, which satisfies `l ≫ fst t = h`
and `l ≫ snd t = k`, see `IsWeakLimit.lift_fst` and `IsWeakLimit.lift_snd`. -/
def IsWeakLimit.lift {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) : W ⟶ t.pt :=
  ht.lift <| PullbackCone.mk _ _ w

@[reassoc (attr := simp)]
lemma IsWeakLimit.lift_fst {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.fst t = h :=
  ht.fac _ _

@[reassoc (attr := simp)]
lemma IsWeakLimit.lift_snd {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X)
    (k : W ⟶ Y) (w : h ≫ f = k ≫ g) : IsWeakLimit.lift ht h k w ≫ PullbackCone.snd t = k :=
  ht.fac _ _

/-- If `t` is a weak limit pullback cone over `f` and `g` and `h : W ⟶ X` and `k : W ⟶ Y` are such
that `h ≫ f = k ≫ g`, then we have `l : W ⟶ t.pt` satisfying `l ≫ fst t = h` and `l ≫ snd t = k`.
-/
def IsWeakLimit.lift' {t : PullbackCone f g} (ht : IsWeakLimit t) {W : C} (h : W ⟶ X) (k : W ⟶ Y)
    (w : h ≫ f = k ≫ g) :
    { l : W ⟶ t.pt // l ≫ PullbackCone.fst t = h ∧ l ≫ PullbackCone.snd t = k } :=
  ⟨IsWeakLimit.lift ht h k w, by simp⟩

/-- The pullback cone reconstructed using `PullbackCone.mk` from a pullback cone that is a
weak limit, is also a weak limit. -/
def mkSelfIsLimit {t : PullbackCone f g} (ht : IsWeakLimit t) :
    IsWeakLimit (PullbackCone.mk t.fst t.snd t.condition) :=
  IsWeakLimit.ofIsoWeakLimit ht (PullbackCone.eta t)

end PullbackCone

variable (C)

/-- A category `HasPullbacks` if it has all weak limits of shape `WalkingCospan`, i.e. if it
has a weak pullback for every pair of morphisms with the same codomain. -/
abbrev HasWeakPullbacks :=
  HasWeakLimitsOfShape WalkingCospan C

instance (priority := 100) HasWeakPullbacksOfHasPullbacks [HasPullbacks C] :
    HasWeakPullbacks C where

variable (f : X ⟶ Z) (g : Y ⟶ Z)

set_option backward.isDefEq.respectTransparency false in
/-- If the product `X ⨯ Y` and the weak equalizer of `π₁ ≫ f` and `π₂ ≫ g` exist, then the
weak pullback of `f` and `g` exists: it is given by composing the equalizer with the projections. -/
theorem hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair [HasLimit (pair X Y)]
    [HasWeakLimit (parallelPair (prod.fst ≫ f) (prod.snd ≫ g))] : HasWeakLimit (cospan f g) :=
  let π₁ : X ⨯ Y ⟶ X := prod.fst
  let π₂ : X ⨯ Y ⟶ Y := prod.snd
  let e := weakEqualizer.ι (π₁ ≫ f) (π₂ ≫ g)
  HasWeakLimit.mk
    { cone :=
        PullbackCone.mk (e ≫ π₁) (e ≫ π₂) <| by
          rw [Category.assoc, weakEqualizer.condition]
          simp [e]
      isWeakLimit :=
        PullbackCone.IsWeakLimit.mk _ (fun s => weakEqualizer.lift
          (prod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)) <| by
            rw [← Category.assoc, limit.lift_π, ← Category.assoc, limit.lift_π]
            exact PullbackCone.condition _)
          (by simp [π₁, e]) (by simp [π₂, e])}

section

attribute [local instance] hasWeakLimit_cospan_of_hasLimit_pair_of_hasWeakLimit_parallelPair

/-- If a category has all binary products and all weak equalizers, then it also has all
weak pullbacks. As usual, this is not an instance, since there may be a more direct way to
construct weak pullbacks. -/
theorem hasWeakPullbacks_of_hasBinaryProducts_of_hasWeakKernels
    [HasBinaryProducts C] [HasWeakEqualizers C] : HasWeakPullbacks C where
      has_weakLimit F := hasWeakLimit_of_iso (diagramIsoCospan F).symm

end

end WeakPullback

end Limits

namespace Preadditive

open Preadditive Limits

variable [Preadditive C] {X Y : C} {f g : X ⟶ Y}

/-- A weak kernel of `f - g` is a weak equalizer of `f` and `g`. -/
def isWeakLimitForkOfKernelFork {c : KernelFork (f - g)} (i : IsWeakLimit c) :
    IsWeakLimit (forkOfKernelFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (kernelForkOfFork s), i.fac _ _⟩

@[simp]
theorem isWeakLimitForkOfKernelFork_lift {c : KernelFork (f - g)} (i : IsWeakLimit c)
    (s : Fork f g) : (isWeakLimitForkOfKernelFork i).lift s = i.lift (kernelForkOfFork s) :=
  rfl

/-- A weak equalizer of `f` and `g` is a weak kernel of `f - g`. -/
def isWeakLimitKernelForkOfFork {c : Fork f g} (i : IsWeakLimit c) :
    IsWeakLimit (kernelForkOfFork c) :=
  Fork.IsWeakLimit.mk' _ fun s => ⟨i.lift (forkOfKernelFork s), i.fac _ _⟩

variable (f g)

/-- A preadditive category has a weak equalizer for `f` and `g` if it has a weak
kernel for `f - g`. -/
theorem hasWeakEqualizer_of_hasWeakKernel [HasWeakKernel (f - g)] : HasWeakEqualizer f g :=
  HasWeakLimit.mk
    { cone := forkOfKernelFork _
      isWeakLimit := isWeakLimitForkOfKernelFork (weakEqualizerIsWeakEqualizer (f - g) 0) }

/-- A preadditive category has a weak kernel for `f - g` if it has a weak equalizer
for `f` and `g`. -/
theorem hasWeakKernel_of_hasWeakEqualizer [HasWeakEqualizer f g] : HasWeakKernel (f - g) :=
  HasWeakLimit.mk
    { cone := kernelForkOfFork (weakEqualizer.fork f g)
      isWeakLimit := isWeakLimitKernelForkOfFork (weakLimit.isWeakLimit (parallelPair f g)) }

/-- If a preadditive category has all weak kernels, then it also has all weak equalizers. -/
theorem hasWeakEqualizers_of_hasWeakKernels [HasWeakKernels C] : HasWeakEqualizers C :=
  @hasWeakEqualizers_of_hasWeakLimit_parallelPair _ _
  fun {_} {_} f g => hasWeakEqualizer_of_hasWeakKernel f g

end Preadditive
