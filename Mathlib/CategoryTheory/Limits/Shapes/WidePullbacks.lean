/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Wide pullbacks

We define the category `WidePullbackShape`, (resp. `WidePushoutShape`) which is the category
obtained from a discrete category of type `J` by adjoining a terminal (resp. initial) element.
Limits of this shape are wide pullbacks (pushouts).
The convenience method `wideCospan` (`wideSpan`) constructs a functor from this category, hitting
the given morphisms.

We use `WidePullbackShape` to define ordinary pullbacks (pushouts) by using `J := WalkingPair`,
which allows easy proofs of some related lemmas.
Furthermore, wide pullbacks are used to show the existence of limits in the slice category.
Namely, if `C` has wide pullbacks then `C/B` has limits for any object `B` in `C`.

Typeclasses `HasWidePullbacks` and `HasFiniteWidePullbacks` assert the existence of wide
pullbacks and finite wide pullbacks.
-/

@[expose] public section

universe w w' v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Limits

variable (J : Type w)

to_dual_name_hint Init Term

/-- A wide pullback shape for any type `J` can be written simply as `Option J`. -/
@[to_dual (attr := implicit_reducible)
/-- A wide pushout shape for any type `J` can be written simply as `Option J`. -/]
def WidePullbackShape := Option J

@[to_dual]
instance : Inhabited (WidePullbackShape J) where
  default := none

variable {J}

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of arrows for the shape indexing a wide pushout. -/
inductive WidePushoutShape.Hom : WidePushoutShape J → WidePushoutShape J → Type w
  | id : ∀ X, Hom X X
  | init : ∀ j : J, Hom none (some j)
  deriving DecidableEq

namespace WidePullbackShape

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type of arrows for the shape indexing a wide pullback. -/
@[to_dual (reorder := 2 3)]
inductive Hom : WidePullbackShape J → WidePullbackShape J → Type w
  | id : ∀ X, Hom X X
  | term : ∀ j : J, Hom (some j) none
  deriving DecidableEq

attribute [to_dual existing (reorder := motive (1 2), 3 4)] Hom.casesOn
attribute [to_dual existing (reorder := motive (1 2), 5 6)] Hom.rec

-- See https://github.com/leanprover/lean4/issues/10295
attribute [nolint unusedArguments]
  instDecidableEqHom.decEq WidePushoutShape.instDecidableEqHom.decEq

@[to_dual]
instance struct : CategoryStruct (WidePullbackShape J) where
  Hom := Hom
  id j := Hom.id j
  comp f g := by
    cases f
    · exact g
    cases g
    apply Hom.term _

@[to_dual]
instance Hom.inhabited : Inhabited (Hom (none : WidePullbackShape J) none) :=
  ⟨Hom.id (none : WidePullbackShape J)⟩

open Lean Elab Tactic
/- Pointing note: experimenting with manual scoping of aesop tactics. Attempted to define
aesop rule directing on `WidePushoutOut` and it didn't take for some reason -/
/-- An aesop tactic for bulk cases on morphisms in `WidePushoutShape` -/
private meta def evalCasesBash : TacticM Unit := do
  evalTactic
    (← `(tactic| casesm* WidePullbackShape _,
      (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)))

attribute [local aesop safe tactic (rule_sets := [CategoryTheory])] evalCasesBash

@[to_dual]
instance subsingleton_hom : Quiver.IsThin (WidePullbackShape J) := fun _ _ => by
  constructor
  intro a b
  casesm* WidePullbackShape _, (_ : WidePullbackShape _) ⟶ (_ : WidePullbackShape _)
  · rfl
  · rfl
  · rfl

@[to_dual]
instance category : SmallCategory (WidePullbackShape J) :=
  thin_category

@[to_dual (attr := simp)]
theorem hom_id (X : WidePullbackShape J) : Hom.id X = 𝟙 X :=
  rfl

variable {C : Type u} [Category.{v} C]

/-- Construct a functor out of the wide pullback shape given a J-indexed collection of arrows to a
fixed object.
-/
@[to_dual (attr := implicit_reducible, simps)
/-- Construct a functor out of the wide pushout shape given a J-indexed collection of arrows from a
fixed object.
-/]
def wideCospan (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : WidePullbackShape J ⥤ C where
  obj j := Option.casesOn j B objs
  map
    | .id X => 𝟙 _
    | .term j => arrows j

/-- Every diagram is naturally isomorphic (actually, equal) to a `wideCospan` -/
@[to_dual /-- Every diagram is naturally isomorphic (actually, equal) to a `wideSpan` -/]
def diagramIsoWideCospan (F : WidePullbackShape J ⥤ C) :
    F ≅ wideCospan (F.obj none) (fun j => F.obj (some j)) fun j => F.map (Hom.term j) :=
  NatIso.ofComponents fun j => eqToIso <| by cat_disch

/-- Construct a cone over a wide cospan. -/
@[to_dual (attr := implicit_reducible, simps) /-- Construct a cocone over a wide span. -/]
def mkCone {F : WidePullbackShape J ⥤ C} {X : C} (f : X ⟶ F.obj none) (π : ∀ j, X ⟶ F.obj (some j))
    (w : ∀ j, π j ≫ F.map (Hom.term j) = f) : Cone F :=
  { pt := X
    π :=
      { app := fun j =>
          match j with
          | none => f
          | some j => π j
        naturality := fun j j' f => by
          cases j <;> cases j' <;> cases f <;> simp [w] } }

/-- Wide pullback diagrams of equivalent index types are equivalent. -/
@[to_dual /-- Wide pushout diagrams of equivalent index types are equivalent. -/]
def equivalenceOfEquiv (J' : Type w') (h : J ≃ J') :
    WidePullbackShape J ≌ WidePullbackShape J' where
  functor := wideCospan none (fun j => some (h j)) fun j => Hom.term (h j)
  inverse := wideCospan none (fun j => some (h.invFun j)) fun j => Hom.term (h.invFun j)
  unitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun j => by cases j <;> exact eqToIso (by simp))

@[to_dual (attr := simp)]
lemma equivalenceOfEquiv_functor_obj_none {ι ι' : Type*} (e : ι ≃ ι') :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj none = none := rfl

@[to_dual (attr := simp)]
lemma equivalenceOfEquiv_functor_obj_some {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.obj (some i) = some (e i) := rfl

@[to_dual (attr := simp)]
lemma equivalenceOfEquiv_functor_map_term {ι ι' : Type*} (e : ι ≃ ι') (i) :
    (WidePullbackShape.equivalenceOfEquiv _ e).functor.map (.term i) = .term (e i) := rfl

attribute [local instance] uliftCategory in
/-- Lifting universe and morphism levels preserves wide pullback diagrams. -/
@[to_dual /-- Lifting universe and morphism levels preserves wide pushout diagrams. -/]
def uliftEquivalence :
    ULiftHom.{w'} (ULift.{w'} (WidePullbackShape J)) ≌ WidePullbackShape (ULift J) :=
  (ULiftHomULiftCategory.equiv.{w', w', w, w} (WidePullbackShape J)).symm.trans
    (equivalenceOfEquiv _ (Equiv.ulift.{w', w}.symm : J ≃ ULift.{w'} J))

/-- Show two functors out of a wide pullback shape are isomorphic by showing their components are
isomorphic. -/
@[simps!]
def functorExt {ι : Type*} {F G : WidePullbackShape ι ⥤ C}
    (base : F.obj none ≅ G.obj none) (comp : ∀ i, F.obj (some i) ≅ G.obj (some i))
    (w : ∀ i, F.map (.term i) ≫ base.hom = (comp i).hom ≫ G.map (.term i) := by cat_disch) :
    F ≅ G :=
  NatIso.ofComponents
    (fun i ↦ match i with
      | none => base
      | some i => comp i)
    (fun f ↦ by rcases f <;> simp [w])

end WidePullbackShape

variable (C : Type u) [Category.{v} C]

/-- A category `HasWidePullbacks` if it has all limits of shape `WidePullbackShape J`, i.e. if it
has a wide pullback for every collection of morphisms with the same codomain. -/
@[to_dual
/-- A category `HasWidePushouts` if it has all colimits of shape `WidePushoutShape J`, i.e. if it
has a wide pushout for every collection of morphisms with the same domain. -/]
abbrev HasWidePullbacks : Prop :=
  ∀ J : Type w, HasLimitsOfShape (WidePullbackShape J) C

variable {C}

/-- `HasWidePullback B objs arrows` means that `wideCospan B objs arrows` has a limit. -/
@[to_dual
/-- `HasWidePushout B objs arrows` means that `wideSpan B objs arrows` has a colimit. -/]
abbrev HasWidePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B) : Prop :=
  HasLimit (WidePullbackShape.wideCospan B objs arrows)

/-- A choice of wide pullback. -/
@[to_dual /-- A choice of wide pushout. -/]
noncomputable abbrev widePullback (B : C) (objs : J → C) (arrows : ∀ j : J, objs j ⟶ B)
    [HasWidePullback B objs arrows] : C :=
  limit (WidePullbackShape.wideCospan B objs arrows)

namespace widePullback

variable {C : Type u} [Category.{v} C] {B : C} {objs : J → C} (arrows : ∀ j : J, objs j ⟶ B)
variable [HasWidePullback B objs arrows]

/-- The `j`-th projection from the pullback. -/
@[to_dual ι /-- The `j`-th inclusion to the pushout. -/]
noncomputable abbrev π (j : J) : widePullback _ _ arrows ⟶ objs j :=
  limit.π (WidePullbackShape.wideCospan _ _ _) (Option.some j)


/-- The unique map to the base from the pullback. -/
@[to_dual head /-- The unique map from the head to the pushout. -/]
noncomputable abbrev base : widePullback _ _ arrows ⟶ B :=
  limit.π (WidePullbackShape.wideCospan _ _ _) Option.none

@[to_dual (attr := reassoc (attr := simp)) arrow_ι]
theorem π_arrow (j : J) : π arrows j ≫ arrows _ = base arrows := by
  apply limit.w (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.Hom.term j)

variable {arrows} in
/-- Lift a collection of morphisms to a morphism to the pullback. -/
@[to_dual desc /-- Descend a collection of morphisms to a morphism from the pushout. -/]
noncomputable abbrev lift {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j)
    (w : ∀ j, fs j ≫ arrows j = f) : X ⟶ widePullback _ _ arrows :=
  limit.lift (WidePullbackShape.wideCospan _ _ _) (WidePullbackShape.mkCone f fs <| w)

variable {X : C} (f : X ⟶ B) (fs : ∀ j : J, X ⟶ objs j) (w : ∀ j, fs j ≫ arrows j = f)

@[to_dual (attr := reassoc) ι_desc]
theorem lift_π (j : J) : lift f fs w ≫ π arrows j = fs _ := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

@[to_dual (attr := reassoc) head_desc]
theorem lift_base : lift f fs w ≫ base arrows = f := by
  simp only [limit.lift_π, WidePullbackShape.mkCone_π_app]

@[to_dual eq_desc_of_comp_eq]
theorem eq_lift_of_comp_eq (g : X ⟶ widePullback _ _ arrows) :
    (∀ j : J, g ≫ π arrows j = fs j) → g ≫ base arrows = f → g = lift f fs w := by
  intro h1 h2
  apply
    (limit.isLimit (WidePullbackShape.wideCospan B objs arrows)).uniq
      (WidePullbackShape.mkCone f fs <| w)
  rintro (_ | _)
  · apply h2
  · apply h1

@[to_dual hom_eq_desc]
theorem hom_eq_lift (g : X ⟶ widePullback _ _ arrows) :
    g = lift (g ≫ base arrows) (fun j => g ≫ π arrows j) (by simp) := by
  aesop

@[to_dual (attr := ext 1100)]
theorem hom_ext (g1 g2 : X ⟶ widePullback _ _ arrows) : (∀ j : J,
    g1 ≫ π arrows j = g2 ≫ π arrows j) → g1 ≫ base arrows = g2 ≫ base arrows → g1 = g2 := by
  intro h1 h2
  apply limit.hom_ext
  rintro (_ | _)
  · apply h2
  · apply h1

end widePullback

@[to_dual (attr := deprecated (since := "2026-08-15"))]
alias WidePullback := widePullback
@[to_dual (attr := deprecated (since := "2026-08-15")) ι]
alias WidePullback.π := widePullback.π
@[to_dual (attr := deprecated (since := "2026-08-15")) head]
alias WidePullback.base := widePullback.base
@[to_dual (attr := deprecated (since := "2026-08-15")) arrow_ι]
alias WidePullback.π_arrow := widePullback.π_arrow
@[to_dual (attr := deprecated (since := "2026-08-15")) desc]
alias WidePullback.lift := widePullback.lift
@[to_dual (attr := deprecated (since := "2026-08-15")) ι_desc]
alias WidePullback.lift_π := widePullback.lift_π
@[to_dual (attr := deprecated (since := "2026-08-15")) head_desc]
alias WidePullback.lift_base := widePullback.lift_base
@[to_dual (attr := deprecated (since := "2026-08-15")) eq_desc_of_comp_eq]
alias WidePullback.eq_lift_of_comp_eq := widePullback.eq_lift_of_comp_eq
@[to_dual (attr := deprecated (since := "2026-08-15")) hom_eq_desc]
alias WidePullback.hom_eq_lift := widePullback.hom_eq_lift
@[to_dual (attr := deprecated (since := "2026-08-15"))]
alias WidePullback.hom_ext := widePullback.hom_ext

/-- A wide pullback cone is a cone on the wide cospan formed by a family of morphisms. -/
abbrev WidePullbackCone {ι : Type*} {X : C} {Y : ι → C} (f : ∀ i, Y i ⟶ X) :=
  Cone (WidePullbackShape.wideCospan X Y f)

namespace WidePullbackCone

variable {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}

/-- The projection on the components of a wide pullback cone. -/
def π (s : WidePullbackCone f) (i : ι) : s.pt ⟶ Y i :=
  (Cone.π s).app (some i)

/-- The projection to the base of a wide pullback cone. -/
def base (s : WidePullbackCone f) : s.pt ⟶ X :=
  (Cone.π s).app none

@[reassoc (attr := simp)]
lemma condition (s : WidePullbackCone f) (i : ι) : s.π i ≫ f i = s.base := by
  simpa using! ((Cone.π s).naturality (.term i)).symm

/-- Construct a wide pullback cone from the projections. -/
@[simps! pt]
def mk {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) :
    WidePullbackCone f :=
  WidePullbackShape.mkCone b π h

@[simp]
lemma mk_base {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) :
    (WidePullbackCone.mk b π h).base = b := rfl

@[simp]
lemma mk_π {W : C} (b : W ⟶ X) (π : ∀ i, W ⟶ Y i) (h : ∀ i, π i ≫ f i = b) (i : ι) :
    (WidePullbackCone.mk b π h).π i = π i := rfl

/-- Constructor to show a wide pullback cone is limiting. -/
def IsLimit.mk (s : WidePullbackCone f) (lift : ∀ t : WidePullbackCone f, t.pt ⟶ s.pt)
    (facbase : ∀ t, lift t ≫ s.base = t.base) (facπ : ∀ t i, lift t ≫ s.π i = t.π i)
    (uniq : ∀ (t) (m : t.pt ⟶ s.pt), m ≫ s.base = t.base → (∀ i, m ≫ s.π i = t.π i) → m = lift t) :
    IsLimit s where
  lift := lift
  fac t j := by
    cases j
    · exact facbase t
    · exact facπ t _
  uniq t m hm := uniq _ _ (hm none) fun _ ↦ hm (some _)

lemma IsLimit.hom_ext {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} {k l : W ⟶ s.pt} (hbase : k ≫ s.base = l ≫ s.base)
    (hπ : ∀ i, k ≫ s.π i = l ≫ s.π i) :
    k = l := by
  apply hs.hom_ext
  rintro (_ | j)
  · exact hbase
  · exact hπ j

/-- Lift a family of morphisms to a limiting wide pullback cone. -/
def IsLimit.lift {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) :
    W ⟶ s.pt :=
  hs.lift (WidePullbackCone.mk b a w)

@[reassoc (attr := simp)]
lemma IsLimit.lift_base {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) :
    IsLimit.lift hs b a w ≫ s.base = b :=
  hs.fac _ _

@[reassoc (attr := simp)]
lemma IsLimit.lift_π {s : WidePullbackCone f} (hs : IsLimit s)
    {W : C} (b : W ⟶ X) (a : ∀ i, W ⟶ Y i) (w : ∀ i, a i ≫ f i = b) (i : ι) :
    IsLimit.lift hs b a w ≫ s.π i = a i :=
  hs.fac _ _

/-- To show two wide pullback cones are isomorphic, it suffices to give a compatible isomorphism
of their cone points. -/
def ext {ι : Type*}
    {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} {s t : WidePullbackCone f}
    (e : s.pt ≅ t.pt)
    (base : e.hom ≫ t.base = s.base := by cat_disch)
    (π : ∀ i, e.hom ≫ t.π i = s.π i := by cat_disch) :
    s ≅ t :=
  Cone.ext e <| by
    rintro (_ | _)
    · exact base.symm
    · exact (π _).symm

/-- Reindex a wide pullback cone. -/
@[simps! pt]
def reindex {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    WidePullbackCone (fun i ↦ f (e i)) :=
  .mk s.base (fun i ↦ s.π _) (by simp)

@[simp]
lemma reindex_base {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) :
    (s.reindex e).base = s.base := rfl

@[simp]
lemma reindex_π {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X} (s : WidePullbackCone f)
    {ι' : Type*} (e : ι' ≃ ι) (i : ι') :
    (s.reindex e).π i = s.π (e i) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing a pullback cone preserves being limiting. -/
def reindexIsLimitEquiv {ι : Type*} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}
    (s : WidePullbackCone f) {ι' : Type*} (e : ι' ≃ ι) :
    IsLimit (s.reindex e) ≃ IsLimit s :=
  (IsLimit.whiskerEquivalenceEquiv <| WidePullbackShape.equivalenceOfEquiv _ e.symm).trans <|
    IsLimit.equivOfNatIsoOfIso
      (WidePullbackShape.functorExt (Iso.refl X) (fun i ↦ eqToIso (by simp))
        fun i ↦ by simp [← eqToHom_naturality]) _ _
      (WidePullbackCone.ext (Iso.refl _) (by simp [base, reindex, mk])
        (fun i ↦ by
          simp [π, reindex, mk,
            eqToHom_naturality (fun i ↦ (Cone.π s).app (some i)) (e.apply_symm_apply i)]))

end WidePullbackCone

variable (J)

/-- The action on morphisms of the obvious functor
  `WidePullbackShape_op : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
@[to_dual (reorder := X Y)
/-- The action on morphisms of the obvious functor
`widePushoutShapeOp : WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/]
def widePullbackShapeOpMap :
    ∀ X Y : WidePullbackShape J,
      (X ⟶ Y) → ((op X : (WidePushoutShape J)ᵒᵖ) ⟶ (op Y : (WidePushoutShape J)ᵒᵖ))
  | _, _, WidePullbackShape.Hom.id X => Quiver.Hom.op (WidePushoutShape.Hom.id _)
  | _, _, WidePullbackShape.Hom.term _ => Quiver.Hom.op (WidePushoutShape.Hom.init _)

/-- The obvious functor `WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ` -/
@[to_dual (attr := simps)
/-- The obvious functor `WidePushoutShape J ⥤ (WidePullbackShape J)ᵒᵖ` -/]
def widePullbackShapeOp : WidePullbackShape J ⥤ (WidePushoutShape J)ᵒᵖ where
  obj X := op X
  map {X₁} {X₂} := widePullbackShapeOpMap J X₁ X₂

/-- The obvious functor `(WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J` -/
@[to_dual (attr := simps!)
/-- The obvious functor `(WidePushoutShape J)ᵒᵖ ⥤ WidePullbackShape J` -/]
def widePullbackShapeUnop : (WidePullbackShape J)ᵒᵖ ⥤ WidePushoutShape J :=
  (widePullbackShapeOp J).leftOp

/-- The inverse of the unit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
@[to_dual
/-- The inverse of the unit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/]
def widePushoutShapeOpUnop : widePushoutShapeUnop J ⋙ widePullbackShapeOp J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The counit isomorphism of the equivalence
`widePullbackShapeOpEquiv : (WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/
@[to_dual
/-- The counit isomorphism of the equivalence
`widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/]
def widePushoutShapeUnopOp : widePushoutShapeOp J ⋙ widePullbackShapeUnop J ≅ 𝟭 _ :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- The duality equivalence `(WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J` -/
@[to_dual (attr := simps)
/-- The duality equivalence `(WidePullbackShape J)ᵒᵖ ≌ WidePushoutShape J` -/]
def widePushoutShapeOpEquiv : (WidePushoutShape J)ᵒᵖ ≌ WidePullbackShape J where
  functor := widePushoutShapeUnop J
  inverse := widePullbackShapeOp J
  unitIso := (widePushoutShapeOpUnop J).symm
  counitIso := widePullbackShapeUnopOp J

/-- If a category has wide pushouts on a higher universe level it also has wide pushouts
on a lower universe level. -/
@[to_dual
/-- If a category has wide pullbacks on a higher universe level it also has wide pullbacks
on a lower universe level. -/]
theorem hasWidePushouts_shrink [HasWidePushouts.{max w w'} C] : HasWidePushouts.{w} C := fun _ =>
  hasColimitsOfShape_of_equivalence (WidePushoutShape.equivalenceOfEquiv _ Equiv.ulift.{w'})

end CategoryTheory.Limits
