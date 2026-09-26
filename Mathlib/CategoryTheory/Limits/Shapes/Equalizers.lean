/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Equalizers and coequalizers

This file defines (co)equalizers as special cases of (co)limits.

An equalizer is the categorical generalization of the subobject ${a ∈ A | f(a) = g(a)}$ known
from abelian groups or modules. It is a limit cone over the diagram formed by `f` and `g`.

A coequalizer is the dual concept.

## Main definitions

* `WalkingParallelPair` is the indexing category used for (co)equalizer diagrams
* `parallelPair` is a functor from `WalkingParallelPair` to our category `C`.
* a `fork` is a cone over a parallel pair.
  * there is really only one interesting morphism in a fork: the arrow from the vertex of the fork
    to the domain of f and g. It is called `fork.ι`.
* an `equalizer` is now just a `limit (parallelPair f g)`

Each of these has a dual.

## Main statements

* `equalizer.ι_mono` states that every equalizer map is a monomorphism
* `isIso_limit_cone_parallelPair_of_self` states that the identity on the domain of `f` is an
  equalizer of `f` and `f`.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

@[expose] public section

section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v v₂ u u₂

to_dual_name_hint Zero One, Mono Epi

/-- The type of objects for the diagram indexing a (co)equalizer. -/
@[to_dual_do_translate]
inductive WalkingParallelPair : Type
  | zero
  | one
  deriving DecidableEq, Inhabited

attribute [to_dual existing] WalkingParallelPair.zero
attribute [to_dual self (reorder := zero one)] WalkingParallelPair.casesOn WalkingParallelPair.rec

open WalkingParallelPair

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
@[to_dual self (reorder := 1 2)]
inductive WalkingParallelPairHom : WalkingParallelPair → WalkingParallelPair → Type
  | left : WalkingParallelPairHom zero one
  | right : WalkingParallelPairHom zero one
  | id (X : WalkingParallelPair) : WalkingParallelPairHom X X
  deriving DecidableEq

attribute [to_dual self (reorder := motive (1 2), 2 3)] WalkingParallelPairHom.casesOn

/-- Satisfying the inhabited linter -/
instance : Inhabited (WalkingParallelPairHom zero one) where default := WalkingParallelPairHom.left

open WalkingParallelPairHom

/-- Composition of morphisms in the indexing diagram for (co)equalizers. -/
@[to_dual self (reorder := X Z, 4 5)]
def WalkingParallelPairHom.comp {X Y Z : WalkingParallelPair} :
     WalkingParallelPairHom X Y → WalkingParallelPairHom Y Z → WalkingParallelPairHom X Z
  | id _, h => h
  | left, id one => left
  | right, id one => right

@[to_dual id_comp]
theorem WalkingParallelPairHom.comp_id
    {X Y : WalkingParallelPair} (f : WalkingParallelPairHom X Y) : comp f (id Y) = f := by
  cases f <;> rfl

theorem WalkingParallelPairHom.assoc {X Y Z W : WalkingParallelPair}
    (f : WalkingParallelPairHom X Y) (g : WalkingParallelPairHom Y Z)
    (h : WalkingParallelPairHom Z W) : comp (comp f g) h = comp f (comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance walkingParallelPairHomCategory : SmallCategory WalkingParallelPair where
  Hom := WalkingParallelPairHom
  id := id
  comp := comp
  comp_id := comp_id
  id_comp := id_comp
  assoc := assoc

@[simp]
theorem walkingParallelPairHom_id (X : WalkingParallelPair) : WalkingParallelPairHom.id X = 𝟙 X :=
  rfl

/-- The functor `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
@[implicit_reducible]
def walkingParallelPairOp : WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ where
  obj x := op <| match x with | zero => one | one => zero
  map f := by
    cases f <;> apply Quiver.Hom.op
    exacts [left, right, WalkingParallelPairHom.id _]
  map_comp := by rintro _ _ _ (_ | _ | _) g <;> cases g <;> rfl

@[to_dual (attr := simp)]
theorem walkingParallelPairOp_zero : walkingParallelPairOp.obj zero = op one := rfl

@[simp]
theorem walkingParallelPairOp_left :
    dsimp% walkingParallelPairOp.map left = Quiver.Hom.op left := rfl

@[simp]
theorem walkingParallelPairOp_right :
    dsimp% walkingParallelPairOp.map right = Quiver.Hom.op right := rfl

/--
The equivalence `WalkingParallelPair ⥤ WalkingParallelPairᵒᵖ` sending left to left and right to
right.
-/
@[implicit_reducible, simps functor inverse]
def walkingParallelPairOpEquiv : WalkingParallelPair ≌ WalkingParallelPairᵒᵖ where
  functor := walkingParallelPairOp
  inverse := walkingParallelPairOp.leftOp
  unitIso :=
    NatIso.ofComponents (fun j => eqToIso (by cases j <;> rfl))
      (by rintro _ _ (_ | _ | _) <;> simp)
  counitIso :=
    NatIso.ofComponents (fun j => eqToIso (by
            induction j with | _ X
            cases X <;> rfl))
      (fun {i} {j} f => by
      induction i with | _ i
      induction j with | _ j
      let g := f.unop
      have : f = g.op := rfl
      rw [this]
      cases i <;> cases j <;> cases g <;> rfl)
  functor_unitIso_comp := fun j => by cases j <;> rfl

@[to_dual (attr := simp)]
theorem walkingParallelPairOpEquiv_unitIso_zero :
    walkingParallelPairOpEquiv.unitIso.app zero = Iso.refl zero := rfl

@[to_dual (attr := simp)]
theorem walkingParallelPairOpEquiv_counitIso_zero :
    walkingParallelPairOpEquiv.counitIso.app (op zero) = Iso.refl (op zero) := rfl

@[to_dual (attr := simp) walkingParallelPairOpEquiv_unitIso_inv_app_one]
theorem walkingParallelPairOpEquiv_unitIso_hom_app_zero :
    walkingParallelPairOpEquiv.unitIso.hom.app zero = 𝟙 zero := rfl

@[to_dual (attr := simp) walkingParallelPairOpEquiv_unitIso_hom_app_one]
theorem walkingParallelPairOpEquiv_unitIso_inv_app_zero :
    walkingParallelPairOpEquiv.unitIso.inv.app zero = 𝟙 zero := rfl

@[to_dual (attr := simp) walkingParallelPairOpEquiv_counitIso_inv_app_op_one]
theorem walkingParallelPairOpEquiv_counitIso_hom_app_op_zero :
    walkingParallelPairOpEquiv.counitIso.hom.app (op zero) = 𝟙 (op zero) := rfl

@[to_dual (attr := simp) walkingParallelPairOpEquiv_counitIso_hom_app_op_one]
theorem walkingParallelPairOpEquiv_counitIso_inv_app_op_zero :
    walkingParallelPairOpEquiv.counitIso.inv.app (op zero) = 𝟙 (op zero) := rfl

variable {C : Type u}
variable {X Y : C}

namespace parallelPair

/-- Implementation of `parallelPair`, do not use directly. -/
@[instance_reducible]
def parallelPairObj (X Y : C) (x : WalkingParallelPair) : C :=
  match x with
  | zero => X
  | one => Y

@[simp] theorem parallelPairObj_zero : parallelPairObj X Y zero = X := rfl
@[simp] theorem parallelPairObj_one : parallelPairObj X Y one = Y := rfl

variable [Category.{v} C]

/-- Implementation of `parallelPair`, do not use directly. -/
def parallelPairHom (f g : X ⟶ Y) {x y : WalkingParallelPair} (h : x ⟶ y) :
    parallelPairObj X Y x ⟶ parallelPairObj X Y y :=
  match h with
  | .id _ => 𝟙 _
  | .left => f
  | .right => g

@[simp] theorem parallelPairHom_id {f g : X ⟶ Y} {x : WalkingParallelPair} :
  parallelPairHom f g (𝟙 x) = 𝟙 (parallelPairObj X Y x) := (rfl)

@[simp] theorem parallelPairHom_left {f g : X ⟶ Y} :
  parallelPairHom f g .left = f := (rfl)

@[simp] theorem parallelPairHom_right {f g : X ⟶ Y} :
  parallelPairHom f g .right = g := (rfl)

end parallelPair

variable [Category.{v} C]

open parallelPair in
/-- `parallelPair f g` is the diagram in `C` consisting of the two morphisms `f` and `g` with
common domain and codomain. -/
@[implicit_reducible, to_dual self]
def parallelPair (f g : X ⟶ Y) : WalkingParallelPair ⥤ C where
  obj x := parallelPairObj X Y x
  map h := parallelPairHom f g h
  map_comp := by rintro _ _ _ ⟨⟩ ⟨⟩ <;> simp

@[to_dual (attr := simp)]
theorem parallelPair_obj_zero (f g : X ⟶ Y) : (parallelPair f g).obj zero = X := rfl

@[simp, to_dual self]
theorem parallelPair_map_left (f g : X ⟶ Y) : (parallelPair f g).map left = f := rfl

@[simp, to_dual self]
theorem parallelPair_map_right (f g : X ⟶ Y) : (parallelPair f g).map right = g := rfl

@[simp]
theorem parallelPair_functor_obj {F : WalkingParallelPair ⥤ C} (j : WalkingParallelPair) :
    (parallelPair (F.map left) (F.map right)).obj j = F.obj j := by cases j <;> rfl

/-- Every functor indexing a (co)equalizer is naturally isomorphic (actually, equal) to a
`parallelPair` -/
@[simps!]
def diagramIsoParallelPair (F : WalkingParallelPair ⥤ C) :
    F ≅ parallelPair (F.map left) (F.map right) :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> rfl) (by rintro _ _ (_ | _ | _) <;> simp)

/-- Constructor for natural transformations between parallel pairs. -/
@[simps]
def parallelPairHomMk {F G : WalkingParallelPair ⥤ C}
    (p : F.obj zero ⟶ G.obj zero)
    (q : F.obj one ⟶ G.obj one)
    (hl : F.map left ≫ q = p ≫ G.map left := by cat_disch)
    (hr : F.map right ≫ q = p ≫ G.map right := by cat_disch) : F ⟶ G where
  app := by rintro (_ | _); exacts [p, q]
  naturality := by rintro _ _ (_ | _); all_goals cat_disch

/-- Constructor for natural isomorphisms between parallel pairs. -/
@[simps!]
def parallelPairIsoMk {F G : WalkingParallelPair ⥤ C}
    (p : F.obj zero ≅ G.obj zero)
    (q : F.obj one ≅ G.obj one)
    (hl : F.map left ≫ q.hom = p.hom ≫ G.map left := by cat_disch)
    (hr : F.map right ≫ q.hom = p.hom ≫ G.map right := by cat_disch) : F ≅ G :=
  NatIso.ofComponents (by rintro (_ | _); exacts [p, q])
    (by rintro _ _ (_ | _); all_goals cat_disch)

/-- Construct a morphism between parallel pairs. -/
def parallelPairHom {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X') (q : Y ⟶ Y')
    (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') : parallelPair f g ⟶ parallelPair f' g' :=
  parallelPairHomMk p q

/-- Construct a isomorphism between parallel pairs. -/
def parallelPairIso {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ≅ X') (q : Y ≅ Y')
    (wf : f ≫ q.hom = p.hom ≫ f') (wg : g ≫ q.hom = p.hom ≫ g') :
    parallelPair f g ≅ parallelPair f' g' := parallelPairIsoMk p q

@[simp]
theorem parallelPairHom_app_zero {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app zero = p :=
  rfl

@[simp]
theorem parallelPairHom_app_one {X' Y' : C} (f g : X ⟶ Y) (f' g' : X' ⟶ Y') (p : X ⟶ X')
    (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') :
    (parallelPairHom f g f' g' p q wf wg).app one = q :=
  rfl

/-- Construct a natural isomorphism between functors out of the walking parallel pair from
its components. -/
@[simps!, to_dual none]
def parallelPair.ext {F G : WalkingParallelPair ⥤ C} (zero : F.obj zero ≅ G.obj zero)
    (one : F.obj one ≅ G.obj one)
    (left : F.map left ≫ one.hom = zero.hom ≫ G.map left := by cat_disch)
    (right : F.map right ≫ one.hom = zero.hom ≫ G.map right := by cat_disch) : F ≅ G :=
  NatIso.ofComponents
    (by
      rintro ⟨j⟩
      exacts [zero, one])
    (by rintro _ _ ⟨_⟩ <;> simp [left, right])

/-- Construct a natural isomorphism between `parallelPair f g` and `parallelPair f' g'` given
equalities `f = f'` and `g = g'`. -/
@[simps!]
def parallelPair.eqOfHomEq {f g f' g' : X ⟶ Y} (hf : f = f') (hg : g = g') :
    parallelPair f g ≅ parallelPair f' g' :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [hf]) (by simp [hg])

/-- A fork on `f` and `g` is just a `Cone (parallelPair f g)`. -/
@[to_dual /-- A cofork on `f` and `g` is just a `Cocone (parallelPair f g)`. -/]
abbrev Fork (f g : X ⟶ Y) :=
  Cone (parallelPair f g)

variable {f g : X ⟶ Y}

/-- A fork `t` on the parallel pair `f g : X ⟶ Y` consists of two morphisms
`t.π.app zero : t.pt ⟶ X` and `t.π.app one : t.pt ⟶ Y`. Of these,
only the first one is interesting, and we give it the shorter name `Fork.ι t`. -/
@[to_dual
/-- A cofork `t` on the parallelPair `f g : X ⟶ Y` consists of two morphisms
`t.ι.app zero : X ⟶ t.pt` and `t.ι.app one : Y ⟶ t.pt`. Of these, only the second one is
interesting, and we give it the shorter name `Cofork.π t`. -/]
def Fork.ι (t : Fork f g) : t.pt ⟶ X :=
  t.π.app zero

@[to_dual (attr := simp)]
theorem Fork.app_zero_eq_ι (t : Fork f g) : t.π.app zero = t.ι :=
  rfl

@[to_dual (attr := simp) app_zero_eq_comp_π_left]
theorem Fork.app_one_eq_ι_comp_left (s : Fork f g) : s.π.app one = s.ι ≫ f := by
  rw [← s.app_zero_eq_ι, ← s.w left, parallelPair_map_left]

@[to_dual (attr := reassoc) app_zero_eq_comp_π_right]
theorem Fork.app_one_eq_ι_comp_right (s : Fork f g) : s.π.app one = s.ι ≫ g := by
  rw [← s.app_zero_eq_ι, ← s.w right, parallelPair_map_right]

/-- A fork on `f g : X ⟶ Y` is determined by the morphism `ι : P ⟶ X` satisfying `ι ≫ f = ι ≫ g`.
-/
@[to_dual (attr := simps, implicit_reducible)
/-- A cofork on `f g : X ⟶ Y` is determined by the morphism `π : Y ⟶ P` satisfying
`f ≫ π = g ≫ π`. -/]
def Fork.ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : Fork f g where
  pt := P
  π :=
    { app := fun X => by
        cases X
        · exact ι
        · exact ι ≫ f
      naturality := fun {X} {Y} f =>
        by cases X <;> cases Y <;> cases f <;> simp [w] }

@[to_dual (attr := simp)]
theorem Fork.ι_ofι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : (Fork.ofι ι w).ι = ι :=
  rfl

@[to_dual (attr := reassoc)]
theorem Fork.condition (t : Fork f g) : t.ι ≫ f = t.ι ≫ g := by
  rw [← t.app_one_eq_ι_comp_left, ← t.app_one_eq_ι_comp_right]

/-- To check whether two maps are equalized by both maps of a fork, it suffices to check it for the
first map -/
@[to_dual
/-- To check whether two maps are coequalized by both maps of a cofork, it suffices to check it for
the second map -/]
theorem Fork.equalizer_ext (s : Fork f g) {W : C} {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι) :
    ∀ j : WalkingParallelPair, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by
    have : k ≫ ι s ≫ f = l ≫ ι s ≫ f := by
      simp only [← Category.assoc]; exact congrArg (· ≫ f) h
    rw [s.app_one_eq_ι_comp_left, this]

insert_to_dual_translation CategoryTheory.Limits.Fork.IsLimit CategoryTheory.Limits.Cofork.IsColimit

@[to_dual]
theorem Fork.IsLimit.hom_ext {s : Fork f g} (hs : IsLimit s) {W : C} {k l : W ⟶ s.pt}
    (h : k ≫ s.ι = l ≫ s.ι) : k = l :=
  hs.hom_ext <| Fork.equalizer_ext _ h

@[to_dual (attr := reassoc (attr := simp)) π_desc]
theorem Fork.IsLimit.lift_ι {s t : Fork f g} (hs : IsLimit s) : hs.lift t ≫ s.ι = t.ι :=
  hs.fac _ _

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
`k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`. -/
@[to_dual desc
/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
`f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`. -/]
def Fork.IsLimit.lift {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ s.pt :=
  hs.lift (Fork.ofι _ h)

@[to_dual (attr := reassoc (attr := simp)) π_desc']
lemma Fork.IsLimit.lift_ι' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    Fork.IsLimit.lift hs k h ≫ s.ι = k :=
    hs.fac _ _

/-- If `s` is a limit fork over `f` and `g`, then a morphism `k : W ⟶ X` satisfying
`k ≫ f = k ≫ g` induces a morphism `l : W ⟶ s.pt` such that `l ≫ fork.ι s = k`. -/
@[to_dual desc'
/-- If `s` is a colimit cofork over `f` and `g`, then a morphism `k : Y ⟶ W` satisfying
`f ≫ k = g ≫ k` induces a morphism `l : s.pt ⟶ W` such that `cofork.π s ≫ l = k`. -/]
def Fork.IsLimit.lift' {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ s.pt // l ≫ s.ι = k } :=
  ⟨Fork.IsLimit.lift hs k h, by simp⟩

@[to_dual]
lemma Fork.IsLimit.mono {s : Fork f g} (hs : IsLimit s) : Mono s.ι where
  right_cancellation _ _ h := hom_ext hs h

@[to_dual]
theorem Fork.IsLimit.existsUnique {s : Fork f g} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = k ≫ g) : ∃! l : W ⟶ s.pt, l ≫ s.ι = k :=
  ⟨hs.lift <| Fork.ofι _ h, hs.fac _ _, fun _ hm =>
    Fork.IsLimit.hom_ext hs <| hm.symm ▸ (hs.fac (Fork.ofι _ h) WalkingParallelPair.zero).symm⟩

/-- This is a slightly more convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[to_dual (attr := simps)
/-- This is a slightly more convenient method to verify that a cofork is a colimit cocone. It
only asks for a proof of facts that carry any mathematical content -/]
def Fork.IsLimit.mk (t : Fork f g) (lift : ∀ s : Fork f g, s.pt ⟶ t.pt)
    (fac : ∀ s : Fork f g, lift s ≫ t.ι = s.ι)
    (uniq : ∀ (s : Fork f g) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j =>
      WalkingParallelPair.casesOn j (fac s) <| by
        simp [← Category.assoc, fac]
    uniq := fun s m j => by aesop }

/-- This is another convenient method to verify that a fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/
@[to_dual
/-- This is another convenient method to verify that a cofork is a colimit cocone. It
only asks for a proof of facts that carry any mathematical content, and allows access to the
same `s` for all parts. -/]
def Fork.IsLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : ∀ s : Fork f g, { l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l }) : IsLimit t :=
  Fork.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w => (create s).2.2 w

/-- Noncomputably make a limit cone from the existence of unique factorizations. -/
@[no_expose, to_dual
/-- Noncomputably make a colimit cocone from the existence of unique factorizations. -/]
noncomputable def Fork.IsLimit.ofExistsUnique {t : Fork f g}
    (hs : ∀ s : Fork f g, ∃! l : s.pt ⟶ t.pt, l ≫ t.ι = s.ι) : IsLimit t := by
  choose d hd hd' using hs
  exact Fork.IsLimit.mk _ d hd fun s m hm => hd' _ _ hm

/-- Given a limit cone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from `Z` to its point
are in bijection with morphisms `h : Z ⟶ X` such that `h ≫ f = h ≫ g`.
Further, this bijection is natural in `Z`: see `Fork.IsLimit.homIso_natural`.
This is a special case of `IsLimit.homIso'`, often useful to construct adjunctions.
-/
@[to_dual (attr := simps)
/-- Given a colimit cocone for the pair `f g : X ⟶ Y`, for any `Z`, morphisms from the cocone point
to `Z` are in bijection with morphisms `h : Y ⟶ Z` such that `f ≫ h = g ≫ h`.
Further, this bijection is natural in `Z`: see `Cofork.IsColimit.homIso_natural`.
This is a special case of `IsColimit.homIso'`, often useful to construct adjunctions.
-/]
def Fork.IsLimit.homIso {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.pt) ≃ { h : Z ⟶ X // h ≫ f = h ≫ g } where
  toFun k := ⟨k ≫ t.ι, by simp only [Category.assoc, t.condition]⟩
  invFun h := (Fork.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Fork.IsLimit.hom_ext ht (Fork.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Fork.IsLimit.lift' ht _ _).prop

/-- The bijection of `Fork.IsLimit.homIso` is natural in `Z`. -/
@[to_dual /-- The bijection of `Cofork.IsColimit.homIso` is natural in `Z`. -/]
theorem Fork.IsLimit.homIso_natural {X Y : C} {f g : X ⟶ Y} {t : Fork f g} (ht : IsLimit t)
    {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.pt) :
    (Fork.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) = q ≫ (Fork.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _

/-- This is a helper construction that can be useful when verifying that a category has all
equalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)`, and a fork on `F.map left` and `F.map right`,
we get a cone on `F`.

If you're thinking about using this, have a look at `hasEqualizers_of_hasLimit_parallelPair`,
which you may find to be an easier way of achieving your goal. -/
@[to_dual
/-- This is a helper construction that can be useful when verifying that a category has all
coequalizers. Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)`, and a cofork on `F.map left` and `F.map right`,
we get a cocone on `F`.

If you're thinking about using this, have a look at `hasCoequalizers_of_hasColimit_parallelPair`,
which you may find to be an easier way of achieving your goal. -/]
def Cone.ofFork {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) : Cone F where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by simp)
      naturality := by rintro _ _ (_ | _ | _) <;> simp [t.condition] }

@[to_dual (attr := simp)]
theorem Cone.ofFork_π {F : WalkingParallelPair ⥤ C} (t : Fork (F.map left) (F.map right)) (j) :
    (Cone.ofFork t).π.app j = t.π.app j ≫ eqToHom (by simp) := rfl

/-- Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)` and a cone on `F`, we get a fork on
`F.map left` and `F.map right`. -/
@[to_dual
/-- Given `F : WalkingParallelPair ⥤ C`, which is really the same as
`parallelPair (F.map left) (F.map right)` and a cocone on `F`, we get a cofork on
`F.map left` and `F.map right`. -/]
def Fork.ofCone {F : WalkingParallelPair ⥤ C} (t : Cone F) : Fork (F.map left) (F.map right) where
  pt := t.pt
  π := { app := fun X => t.π.app X ≫ eqToHom (by simp)
         naturality := by rintro _ _ (_ | _ | _) <;> simp }

@[to_dual (attr := simp)]
theorem Fork.ofCone_π {F : WalkingParallelPair ⥤ C} (t : Cone F) (j) :
    (Fork.ofCone t).π.app j = t.π.app j ≫ eqToHom (by simp) := rfl

@[to_dual (attr := simp)]
theorem Fork.ι_postcompose {f' g' : X ⟶ Y} {α : parallelPair f g ⟶ parallelPair f' g'}
    {c : Fork f g} : Fork.ι ((Cone.postcompose α).obj c) = c.ι ≫ α.app .zero :=
  rfl

/-- Helper function for constructing morphisms between equalizer forks. -/
@[to_dual (attr := simps)
/-- Helper function for constructing morphisms between coequalizer coforks. -/]
def Fork.mkHom {s t : Fork f g} (k : s.pt ⟶ t.pt) (w : k ≫ t.ι = s.ι) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simp only [Fork.app_one_eq_ι_comp_left, ← Category.assoc]
      congr

@[reassoc (attr := simp)]
theorem Fork.hom_comp_ι {s t : Fork f g} (f : s ⟶ t) : f.hom ≫ t.ι = s.ι := by
  cases s; cases t; cases f; aesop

/-- To construct an isomorphism between forks,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps, to_dual none] -- TODO: use `to_dual_for` instead
def Fork.ext {s t : Fork f g} (i : s.pt ≅ t.pt) (w : i.hom ≫ t.ι = s.ι := by cat_disch) :
    s ≅ t where
  hom := Fork.mkHom i.hom w
  inv := Fork.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

/-- Two forks of the form `ofι` are isomorphic whenever their `ι`'s are equal. -/
@[to_dual CoforkOfπ.ext
/-- Two coforks of the form `ofπ` are isomorphic whenever their `π`'s are equal. -/]
def ForkOfι.ext {P : C} {ι ι' : P ⟶ X} (w : ι ≫ f = ι ≫ g) (w' : ι' ≫ f = ι' ≫ g) (h : ι = ι') :
    Fork.ofι ι w ≅ Fork.ofι ι' w' :=
  Fork.ext (Iso.refl _) (by simp [h])

/-- Every fork is isomorphic to one of the form `Fork.of_ι _ _`. -/
@[to_dual (attr := simps!) /-- Every cofork is isomorphic to one of the form `Cofork.ofπ _ _`. -/]
def Fork.isoForkOfι (c : Fork f g) : c ≅ Fork.ofι c.ι c.condition :=
  Fork.ext (Iso.refl _)

/--
If `f, g : X ⟶ Y` and `f', g : X' ⟶ Y'` pairwise form a commutative square with isomorphisms
`X ≅ X'` and `Y ≅ Y'`, the categories of forks are equivalent.
-/
def Fork.equivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) :
    Fork f g ≌ Fork f' g' :=
  Cone.postcomposeEquivalence <|
    parallelPair.ext e₀ e₁ (by simp [comm₁]) (by simp [comm₂])

@[simp]
lemma Fork.equivOfIsos_functor_obj_ι {X Y : C} {f g : X ⟶ Y}
    {X' Y' : C} {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) (c : Fork f g) :
    ((Fork.equivOfIsos e₀ e₁ comm₁ comm₂).functor.obj c).ι = c.ι ≫ e₀.hom :=
  rfl

@[simp]
lemma Fork.equivOfIsos_inverse_obj_ι {X Y : C} {f g : X ⟶ Y}
    {X' Y' : C} {f' g' : X' ⟶ Y'} (e₀ : X ≅ X') (e₁ : Y ≅ Y')
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch) (c : Fork f' g') :
    ((Fork.equivOfIsos e₀ e₁ comm₁ comm₂).inverse.obj c).ι = c.ι ≫ e₀.inv :=
  rfl

/--
Given two forks with isomorphic components in such a way that the natural diagrams commute, then
one is a limit if and only if the other one is.
-/
def Fork.isLimitEquivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    (c : Fork f g)
    {f' g' : X' ⟶ Y'} (c' : Fork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₀.hom := by cat_disch) :
    IsLimit c ≃ IsLimit c' :=
  let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsLimit.equivOfNatIsoOfIso i c c' (Fork.ext e comm₃)

/--
Given two forks with isomorphic components in such a way that the natural diagrams commute, then if
one is a limit, then the other one is as well.
-/
def Fork.isLimitOfIsos {X' Y' : C} (c : Fork f g) (hc : IsLimit c)
    {f' g' : X' ⟶ Y'} (c' : Fork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e.hom ≫ c'.ι = c.ι ≫ e₀.hom := by cat_disch) : IsLimit c' :=
  (Fork.isLimitEquivOfIsos c c' e₀ e₁ e) hc

@[reassoc (attr := simp)]
theorem Cofork.π_comp_hom {s t : Cofork f g} (f : s ⟶ t) : s.π ≫ f.hom = t.π := by
  cases s; cases t; cases f; aesop

@[deprecated (since := "2026-09-25")] alias Fork.π_comp_hom := Cofork.π_comp_hom

/-- To construct an isomorphism between coforks,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
@[simps]
def Cofork.ext {s t : Cofork f g} (i : s.pt ≅ t.pt) (w : s.π ≫ i.hom = t.π := by cat_disch) :
    s ≅ t where
  hom := Cofork.mkHom i.hom w
  inv := Cofork.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

/--
Given two coforks with isomorphic components in such a way that the natural diagrams commute, then
one is a colimit if and only if the other one is.
-/
def Cofork.isColimitEquivOfIsos {X Y : C} {f g : X ⟶ Y} {X' Y' : C}
    (c : Cofork f g)
    {f' g' : X' ⟶ Y'} (c' : Cofork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e₁.inv ≫ c.π ≫ e.hom = c'.π := by cat_disch) :
    IsColimit c ≃ IsColimit c' :=
  let i : parallelPair f g ≅ parallelPair f' g' := parallelPair.ext e₀ e₁ comm₁.symm comm₂.symm
  IsColimit.equivOfNatIsoOfIso i c c' (Cofork.ext e (by rw [← comm₃, ← Category.assoc]; rfl))

/--
Given two coforks with isomorphic components in such a way that the natural diagrams commute, then
if one is a colimit, then the other one is as well.
-/
def Cofork.isColimitOfIsos {X' Y' : C} (c : Cofork f g) (hc : IsColimit c)
    {f' g' : X' ⟶ Y'} (c' : Cofork f' g')
    (e₀ : X ≅ X') (e₁ : Y ≅ Y') (e : c.pt ≅ c'.pt)
    (comm₁ : e₀.hom ≫ f' = f ≫ e₁.hom := by cat_disch)
    (comm₂ : e₀.hom ≫ g' = g ≫ e₁.hom := by cat_disch)
    (comm₃ : e₁.inv ≫ c.π ≫ e.hom = c'.π := by cat_disch) : IsColimit c' :=
  (Cofork.isColimitEquivOfIsos c c' e₀ e₁ e) hc

variable (f g)

section

/-- Two parallel morphisms `f` and `g` have an equalizer if the diagram `parallelPair f g` has a
limit. -/
@[to_dual
/-- Two parallel morphisms `f` and `g` have a coequalizer if the diagram `parallelPair f g` has a
colimit. -/]
abbrev HasEqualizer :=
  HasLimit (parallelPair f g)

variable [HasEqualizer f g]

/-- If an equalizer of `f` and `g` exists, we can access an arbitrary choice of such by
saying `equalizer f g`. -/
@[to_dual
/-- If a coequalizer of `f` and `g` exists, we can access an arbitrary choice of such by
saying `coequalizer f g`. -/]
noncomputable abbrev equalizer : C :=
  limit (parallelPair f g)

/-- If an equalizer of `f` and `g` exists, we can access the inclusion
`equalizer f g ⟶ X` by saying `equalizer.ι f g`. -/
@[to_dual
/-- If a coequalizer of `f` and `g` exists, we can access the corresponding projection by
saying `coequalizer.π f g`. -/]
noncomputable abbrev equalizer.ι : equalizer f g ⟶ X :=
  limit.π (parallelPair f g) zero

/-- An equalizer cone for a parallel pair `f` and `g` -/
@[to_dual /-- An arbitrary choice of coequalizer cocone for a parallel pair `f` and `g`. -/]
noncomputable abbrev equalizer.fork : Fork f g :=
  limit.cone (parallelPair f g)

@[to_dual (attr := simp)]
theorem equalizer.fork_ι : (equalizer.fork f g).ι = equalizer.ι f g :=
  rfl

@[to_dual (attr := simp)]
theorem equalizer.fork_π_app_zero : (equalizer.fork f g).π.app zero = equalizer.ι f g :=
  rfl

@[to_dual (attr := reassoc)]
theorem equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
  Fork.condition <| limit.cone <| parallelPair f g

/-- The equalizer built from `equalizer.ι f g` is limiting. -/
@[to_dual /-- The cofork built from `coequalizer.π f g` is colimiting. -/]
noncomputable def equalizerIsEqualizer : IsLimit (Fork.ofι (equalizer.ι f g)
    (equalizer.condition f g)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

variable {f g}

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` factors through the equalizer of `f` and `g`
via `equalizer.lift : W ⟶ equalizer f g`. -/
@[to_dual desc
/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` factors through the coequalizer of `f`
and `g` via `coequalizer.desc : coequalizer f g ⟶ W`. -/]
noncomputable abbrev equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
  limit.lift (parallelPair f g) (Fork.ofι k h)

@[to_dual (attr := reassoc) π_desc]
theorem equalizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    equalizer.lift k h ≫ equalizer.ι f g = k :=
  limit.lift_π _ _

/-- A morphism `k : W ⟶ X` satisfying `k ≫ f = k ≫ g` induces a morphism `l : W ⟶ equalizer f g`
satisfying `l ≫ equalizer.ι f g = k`. -/
@[to_dual desc'
/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = g ≫ k` induces a morphism
`l : coequalizer f g ⟶ W` satisfying `coequalizer.π ≫ g = l`. -/]
noncomputable def equalizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ equalizer f g // l ≫ equalizer.ι f g = k } :=
  ⟨equalizer.lift k h, equalizer.lift_ι _ _⟩

/-- Two maps into an equalizer are equal if they are equal when composed with the equalizer map. -/
@[to_dual (attr := ext)
/-- Two maps from a coequalizer are equal if they are equal when composed with the coequalizer
map -/]
theorem equalizer.hom_ext {W : C} {k l : W ⟶ equalizer f g}
    (h : k ≫ equalizer.ι f g = l ≫ equalizer.ι f g) : k = l :=
  Fork.IsLimit.hom_ext (limit.isLimit _) h

@[to_dual]
theorem equalizer.existsUnique {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    ∃! l : W ⟶ equalizer f g, l ≫ equalizer.ι f g = k :=
  Fork.IsLimit.existsUnique (limit.isLimit _) _ h

/-- An equalizer morphism is a monomorphism -/
@[to_dual /-- A coequalizer morphism is an epimorphism -/]
instance equalizer.ι_mono : Mono (equalizer.ι f g) where
  right_cancellation _ _ w := equalizer.hom_ext w

end

section

variable {f g}

/-- The equalizer morphism in any limit cone is a monomorphism. -/
@[to_dual /-- The coequalizer morphism in any colimit cocone is an epimorphism. -/]
theorem mono_of_isLimit_fork {c : Fork f g} (i : IsLimit c) : Mono c.ι :=
  { right_cancellation := fun _ _ w => Fork.IsLimit.hom_ext i w }

end

section

variable {f g}

/-- The identity determines a cone on the equalizer diagram of `f` and `g` if `f = g`. -/
@[to_dual (attr := implicit_reducible)
/-- The identity determines a cocone on the coequalizer diagram of `f` and `g`, if `f = g`. -/]
def idFork (h : f = g) : Fork f g :=
  Fork.ofι (𝟙 X) <| h ▸ rfl

/-- The identity on `X` is an equalizer of `(f, g)`, if `f = g`. -/
@[to_dual /-- The identity on `Y` is a coequalizer of `(f, g)`, where `f = g`. -/]
def isLimitIdFork (h : f = g) : IsLimit (idFork h) :=
  Fork.IsLimit.mk _ Fork.ι (fun _ => Category.comp_id _) fun s m h => by
    convert! h
    exact (Category.comp_id _).symm

/-- Every equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
@[to_dual /-- Every coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/]
theorem isIso_limit_cone_parallelPair_of_eq (h₀ : f = g) {c : Fork f g} (h : IsLimit c) :
    IsIso c.ι :=
  Iso.isIso_hom <| IsLimit.conePointUniqueUpToIso h <| isLimitIdFork h₀

/-- The equalizer of `(f, g)`, where `f = g`, is an isomorphism. -/
@[to_dual /-- The coequalizer of `(f, g)`, where `f = g`, is an isomorphism. -/]
theorem equalizer.ι_of_eq [HasEqualizer f g] (h : f = g) : IsIso (equalizer.ι f g) :=
  isIso_limit_cone_parallelPair_of_eq h <| limit.isLimit _

/-- Every equalizer of `(f, f)` is an isomorphism. -/
@[to_dual /-- Every coequalizer of `(f, f)` is an isomorphism. -/]
theorem isIso_limit_cone_parallelPair_of_self {c : Fork f f} (h : IsLimit c) : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq rfl h

/-- An equalizer that is an epimorphism is an isomorphism. -/
@[to_dual /-- A coequalizer that is a monomorphism is an isomorphism. -/]
theorem isIso_limit_cone_parallelPair_of_epi {c : Fork f g} (h : IsLimit c) [Epi c.ι] : IsIso c.ι :=
  isIso_limit_cone_parallelPair_of_eq ((cancel_epi _).1 (Fork.condition c)) h

@[deprecated (since := "2026-09-25")]
alias isIso_limit_cocone_parallelPair_of_epi := isIso_colimit_cocone_parallelPair_of_mono

/-- Two morphisms are equal if there is a fork whose inclusion is epi. -/
@[to_dual /-- Two morphisms are equal if there is a cofork whose projection is mono. -/]
theorem eq_of_epi_fork_ι (t : Fork f g) [Epi t.ι] : f = g :=
  (cancel_epi t.ι).1 <| Fork.condition t

/-- If the equalizer of two morphisms is an epimorphism, then the two morphisms are equal. -/
@[to_dual
/-- If the coequalizer of two morphisms is a monomorphism, then the two morphisms are equal. -/]
theorem eq_of_epi_equalizer [HasEqualizer f g] [Epi (equalizer.ι f g)] : f = g :=
  (cancel_epi (equalizer.ι f g)).1 <| equalizer.condition _ _

end

@[to_dual]
instance hasEqualizer_of_self : HasEqualizer f f :=
  HasLimit.mk
    { cone := idFork rfl
      isLimit := isLimitIdFork rfl }

/-- The equalizer inclusion for `(f, f)` is an isomorphism. -/
@[to_dual /-- The coequalizer projection for `(f, f)` is an isomorphism. -/]
instance equalizer.ι_of_self : IsIso (equalizer.ι f f) :=
  equalizer.ι_of_eq rfl

/-- The equalizer of a morphism with itself is isomorphic to the source. -/
@[to_dual isoTargetOfSelf
/-- The coequalizer of a morphism with itself is isomorphic to the target. -/]
noncomputable def equalizer.isoSourceOfSelf : equalizer f f ≅ X :=
  asIso (equalizer.ι f f)

@[to_dual (attr := simp) isoTargetOfSelf_inv]
theorem equalizer.isoSourceOfSelf_hom : (equalizer.isoSourceOfSelf f).hom = equalizer.ι f f :=
  rfl

@[to_dual (attr := simp) isoTargetOfSelf_hom]
theorem equalizer.isoSourceOfSelf_inv :
    (equalizer.isoSourceOfSelf f).inv = equalizer.lift (𝟙 X) (by simp) := by
  ext
  simp [equalizer.isoSourceOfSelf]

section

variable {f g : X ⟶ Y} {Z : C} (h : Z ⟶ X)

/--
Given a fork `s` on morphisms `f, g : X ⟶ Y` and a pullback cone `c` on `s.ι : s.pt ⟶ X` and a
morphism `h : Z ⟶ X`, the projection `c.snd : c.pt ⟶ Z` induces a fork on `h ≫ f` and `h ≫ g`.
```
c.pt → Z
|      |
v      v
s.pt → X ⇉ Y
```
-/
@[implicit_reducible]
def precompFork (s : Fork f g) (c : PullbackCone s.ι h) : Fork (h ≫ f) (h ≫ g) :=
  Fork.ofι c.snd <| by
    rw [← c.condition_assoc, ← c.condition_assoc, s.condition]

/--
Any fork on `h ≫ f` and `h ≫ g` lifts to a pullback along `h` of an equalizer of `f` and `g`.
-/
def liftPrecomp {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c)
    (s' : Fork (h ≫ f) (h ≫ g)) :
    s'.pt ⟶ (precompFork h s c).pt :=
  hc.lift <| PullbackCone.mk
    (hs.lift <| Fork.ofι (s'.ι ≫ h) (by simp [s'.condition])) s'.ι

/-- The pullback of an equalizer is an equalizer. -/
def isLimitPrecompFork {s : Fork f g} (hs : IsLimit s) {c : PullbackCone s.ι h} (hc : IsLimit c) :
    IsLimit (precompFork h s c) :=
  Fork.IsLimit.mk _
    (fun s' ↦ liftPrecomp h hs hc s')
    (by simp [liftPrecomp, precompFork])
    (fun s' m h ↦ hc.hom_ext <| by
      apply PullbackCone.equalizer_ext
      · simp only [liftPrecomp, IsLimit.fac, PullbackCone.mk_π_app]
        apply hs.hom_ext
        apply Fork.equalizer_ext
        simp only [Fork.ι_ofι, precompFork] at h
        simp [c.condition, reassoc_of% h]
      · simpa [liftPrecomp] using! h)

lemma hasEqualizer_precomp_of_equalizer {s : Fork f g} (hs : IsLimit s)
    {c : PullbackCone s.ι h} (hc : IsLimit c) :
    HasEqualizer (h ≫ f) (h ≫ g) :=
  HasLimit.mk
    { cone := precompFork h s c
      isLimit := isLimitPrecompFork h hs hc }

instance hasEqualizer_precomp_of_hasEqualizer [HasEqualizer f g] [HasPullback (equalizer.ι f g) h] :
    HasEqualizer (h ≫ f) (h ≫ g) :=
  hasEqualizer_precomp_of_equalizer h
    (equalizerIsEqualizer f g) (pullback.isLimit (equalizer.ι f g) h)

end

section

variable [HasCoequalizer f g] {f g}

theorem coequalizer.π_colimMap_desc {X' Y' Z : C} (f' g' : X' ⟶ Y') [HasCoequalizer f' g']
    (p : X ⟶ X') (q : Y ⟶ Y') (wf : f ≫ q = p ≫ f') (wg : g ≫ q = p ≫ g') (h : Y' ⟶ Z)
    (wh : f' ≫ h = g' ≫ h) :
    coequalizer.π f g ≫ colimMap (parallelPairHom f g f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h := by
  rw [ι_colimMap_assoc, parallelPairHom_app_one, coequalizer.π_desc]

end

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism for the equalizer of `(f, g)`.
This is an isomorphism iff `G` preserves the equalizer of `(f, g)`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Equalizers.lean`
-/
@[to_dual /-- The comparison morphism for the coequalizer of `(f, g)`. -/]
noncomputable def equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    G.obj (equalizer f g) ⟶ equalizer (G.map f) (G.map g) :=
  equalizer.lift (G.map (equalizer.ι _ _))
    (by simp only [← G.map_comp]; rw [equalizer.condition])

@[to_dual (attr := reassoc (attr := simp)) ι_comp_coequalizerComparison]
theorem equalizerComparison_comp_π [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] :
    equalizerComparison f g G ≫ equalizer.ι (G.map f) (G.map g) = G.map (equalizer.ι f g) :=
  equalizer.lift_ι _ _

@[to_dual (attr := reassoc (attr := simp)) coequalizerComparison_map_desc]
theorem map_lift_equalizerComparison [HasEqualizer f g] [HasEqualizer (G.map f) (G.map g)] {Z : C}
    {h : Z ⟶ X} (w : h ≫ f = h ≫ g) :
    G.map (equalizer.lift h w) ≫ equalizerComparison f g G =
      equalizer.lift (G.map h) (by simp only [← G.map_comp, w]) := by
  apply equalizer.hom_ext
  simp [← G.map_comp]

end Comparison

variable (C)

/-- A category `HasEqualizers` if it has all limits of shape `WalkingParallelPair`, i.e. if it has
an equalizer for every parallel pair of morphisms. -/
@[to_dual
/-- A category `HasCoequalizers` if it has all colimits of shape `WalkingParallelPair`, i.e. if it
has a coequalizer for every parallel pair of morphisms. -/]
abbrev HasEqualizers :=
  HasLimitsOfShape WalkingParallelPair C

/-- If `C` has all limits of diagrams `parallelPair f g`, then it has all equalizers -/
@[to_dual
/-- If `C` has all colimits of diagrams `parallelPair f g`, then it has all coequalizers -/]
theorem hasEqualizers_of_hasLimit_parallelPair
    [∀ {X Y : C} {f g : X ⟶ Y}, HasLimit (parallelPair f g)] : HasEqualizers C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelPair F).symm }

section

-- In this section we show that a split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
variable {C} [IsSplitMono f]

/-- A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`.
Here we build the cone, and show in `isSplitMonoEqualizes` that it is a limit cone.
-/
@[to_dual (attr := simps (rhsMd := default))
/-- A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`.
Here we build the cocone, and show in `isSplitEpiCoequalizes` that it is a colimit cocone.
-/]
noncomputable def coneOfIsSplitMono : Fork (𝟙 Y) (retraction f ≫ f) :=
  Fork.ofι f (by simp)

@[to_dual (attr := simp)]
theorem coneOfIsSplitMono_ι : (coneOfIsSplitMono f).ι = f :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A split mono `f` equalizes `(retraction f ≫ f)` and `(𝟙 Y)`. -/
@[to_dual /-- A split epi `f` coequalizes `(f ≫ section_ f)` and `(𝟙 X)`. -/]
noncomputable def isSplitMonoEqualizes {X Y : C} (f : X ⟶ Y) [IsSplitMono f] :
    IsLimit (coneOfIsSplitMono f) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ retraction f, by
      dsimp
      rw [Category.assoc, ← s.condition]
      apply Category.comp_id, fun hm => by simp [← hm]⟩

end

/-- We show that the converse to `isSplitMonoEqualizes` is true:
Whenever `f` equalizes `(r ≫ f)` and `(𝟙 Y)`, then `r` is a retraction of `f`. -/
@[to_dual
/-- We show that the converse to `isSplitEpiEqualizes` is true:
Whenever `f` coequalizes `(f ≫ s)` and `(𝟙 X)`, then `s` is a section of `f`. -/]
def splitMonoOfEqualizer {X Y : C} {f : X ⟶ Y} {r : Y ⟶ X} (hr : f ≫ r ≫ f = f)
    (h : IsLimit (Fork.ofι f (hr.trans (Category.comp_id _).symm : f ≫ r ≫ f = f ≫ 𝟙 Y))) :
    SplitMono f where
  retraction := r
  id := Fork.IsLimit.hom_ext h ((Category.assoc _ _ _).trans <| hr.trans (Category.id_comp _).symm)

variable {C f g}

/-- The fork obtained by postcomposing an equalizer fork with a monomorphism is an equalizer. -/
@[to_dual isCoequalizerEpiComp
/-- The cofork obtained by precomposing a coequalizer cofork with an epimorphism is
a coequalizer. -/]
def isEqualizerCompMono {c : Fork f g} (i : IsLimit c) {Z : C} (h : Y ⟶ Z) [hm : Mono h] :
    have : Fork.ι c ≫ f ≫ h = Fork.ι c ≫ g ≫ h := by
      simp only [← Category.assoc]
      exact congrArg (· ≫ h) c.condition
    IsLimit (Fork.ofι c.ι (by simp [this]) : Fork (f ≫ h) (g ≫ h)) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : Fork f g := Fork.ofι s.ι (by apply hm.right_cancellation; simp [s.condition])
    let l := Fork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

variable (C f g)

@[to_dual hasCoequalizer_epi_comp]
instance hasEqualizer_comp_mono [HasEqualizer f g] {Z : C} (h : Y ⟶ Z) [Mono h] :
    HasEqualizer (f ≫ h) (g ≫ h) :=
  ⟨⟨{   cone := _
        isLimit := isEqualizerCompMono (limit.isLimit _) h }⟩⟩

/-- An equalizer of an idempotent morphism and the identity is split mono. -/
@[to_dual (attr := simps)
/-- A coequalizer of an idempotent morphism and the identity is split epi. -/]
def splitMonoOfIdempotentOfIsLimitFork {X : C} {f : X ⟶ X} (hf : f ≫ f = f) {c : Fork (𝟙 X) f}
    (i : IsLimit c) : SplitMono c.ι where
  retraction := i.lift (Fork.ofι f (by simp [hf]))
  id := by
    let := mono_of_isLimit_fork i
    rw [← cancel_mono_id c.ι, Category.assoc, Fork.IsLimit.lift_ι, Fork.ι_ofι, ← c.condition]
    exact Category.comp_id c.ι

/-- The equalizer of an idempotent morphism and the identity is split mono. -/
@[to_dual /-- The coequalizer of an idempotent morphism and the identity is split epi. -/]
noncomputable def splitMonoOfIdempotentEqualizer {X : C} {f : X ⟶ X} (hf : f ≫ f = f)
    [HasEqualizer (𝟙 X) f] : SplitMono (equalizer.ι (𝟙 X) f) :=
  splitMonoOfIdempotentOfIsLimitFork _ hf (limit.isLimit _)

end CategoryTheory.Limits
