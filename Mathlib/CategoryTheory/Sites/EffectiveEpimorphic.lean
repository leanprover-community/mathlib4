/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic.ApplyFun

/-!

# Effective epimorphisms

We define the notion of effective epimorphic (pre)sieves, morphisms and family of morphisms
and provide some API for relating the three notions.

More precisely, if `f` is a morphism, then `f` is an effective epi if and only if the sieve
it generates is effective epimorphic; see `CategoryTheory.Sieve.effectiveEpimorphic_singleton`.
The analogous statement for a family of morphisms is in the theorem
`CategoryTheory.Sieve.effectiveEpimorphic_family`.

We have defined the notion of effective epi for morphisms and families of morphisms in such a
way that avoids requiring the existence of pullbacks. However, if the relevant pullbacks exist
then these definitions are equivalent, see `effectiveEpiStructOfRegularEpi`,
`regularEpiOfEffectiveEpi`, and `effectiveEpiOfKernelPair`.
See [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
[Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions. Note that
our notion of `EffectiveEpi` is often called "strict epi" in the literature.

## References
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
- [Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions.

## TODO
- Find sufficient conditions on functors to preserve/reflect effective epis.

-/

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

/-- A sieve is effective epimorphic if the associated cocone is a colimit cocone. -/
def Sieve.EffectiveEpimorphic {X : C} (S : Sieve X) : Prop :=
  Nonempty (IsColimit (S : Presieve X).cocone)

/-- A presieve is effective epimorphic if the cocone associated to the sieve it generates
is a colimit cocone. -/
abbrev Presieve.EffectiveEpimorphic {X : C} (S : Presieve X) : Prop :=
  (Sieve.generate S).EffectiveEpimorphic

/--
The sieve of morphisms which factor through a given morphism `f`.
This is equal to `Sieve.generate (Presieve.singleton f)`, but has
more convenient definitional properties.
-/
def Sieve.generateSingleton {X Y : C} (f : Y ⟶ X) : Sieve X where
  arrows Z := { g | ∃ (e : Z ⟶ Y), e ≫ f = g }
  downward_closed := by
    rintro W Z g ⟨e,rfl⟩ q
    exact ⟨q ≫ e, by simp⟩

lemma Sieve.generateSingleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generateSingleton f := by
  ext Z g
  constructor
  · rintro ⟨W,i,p,⟨⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨g,h⟩
    exact ⟨Y,g,f,⟨⟩,h⟩

/--
This structure encodes the data required for a morphism to be an effective epimorphism.
-/
structure EffectiveEpiStruct {X Y : C} (f : Y ⟶ X) where
  desc : ∀ {W : C} (e : Y ⟶ W),
    (∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) → (X ⟶ W)
  fac : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e),
    f ≫ desc e h = e
  uniq : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W), f ≫ m = e → m = desc e h

attribute [nolint docBlame]
  EffectiveEpiStruct.desc
  EffectiveEpiStruct.fac
  EffectiveEpiStruct.uniq

/--
A morphism `f : Y ⟶ X` is an effective epimorphism provided that `f` exhibits `X` as a colimit
of the diagram of all "relations" `R ⇉ Y`.
If `f` has a kernel pair, then this is equivalent to showing that the corresponding cofork is
a colimit.
-/
class EffectiveEpi {X Y : C} (f : Y ⟶ X) : Prop where
  effectiveEpi : Nonempty (EffectiveEpiStruct f)

attribute [nolint docBlame] EffectiveEpi.effectiveEpi

/-- Some chosen `EffectiveEpiStruct` associated to an effective epi. -/
noncomputable
def EffectiveEpi.getStruct {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : EffectiveEpiStruct f :=
  EffectiveEpi.effectiveEpi.some

/-- Descend along an effective epi. -/
noncomputable
def EffectiveEpi.desc {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    X ⟶ W := (EffectiveEpi.getStruct f).desc e h

@[reassoc (attr := simp)]
lemma EffectiveEpi.fac {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    f ≫ EffectiveEpi.desc f e h = e :=
  (EffectiveEpi.getStruct f).fac e h

lemma EffectiveEpi.uniq {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W) (hm : f ≫ m = e) :
    m = EffectiveEpi.desc f e h :=
  (EffectiveEpi.getStruct f).uniq e h _ hm

instance epiOfEffectiveEpi {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : Epi f := by
  constructor
  intro W m₁ m₂ h
  have : m₂ = EffectiveEpi.desc f (f ≫ m₂)
    (fun {Z} g₁ g₂ h => by simp only [← Category.assoc, h]) := EffectiveEpi.uniq _ _ _ _ rfl
  rw [this]
  exact EffectiveEpi.uniq _ _ _ _ h

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
def isColimitOfEffectiveEpiStruct {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStruct f) :
    IsColimit (Sieve.generateSingleton f : Presieve X).cocone :=
  letI D := FullSubcategory fun T : Over X => Sieve.generateSingleton f T.hom
  letI F : D ⥤ _ := (Sieve.generateSingleton f).arrows.diagram
  { desc := fun S => Hf.desc (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
      intro Z g₁ g₂ h
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      let g₁' : Z' ⟶ Y' := Over.homMk g₁
      let g₂' : Z' ⟶ Y' := Over.homMk g₂ (by simp [h])
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      simp only [S.w]
    fac := by
      rintro S ⟨T,g,hT⟩
      dsimp
      nth_rewrite 1 [← hT, Category.assoc, Hf.fac]
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      let g' : x ⟶ y := Over.homMk g
      change F.map g' ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm
      dsimp
      generalize_proofs h1 h2
      apply Hf.uniq _ h2
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
noncomputable
def effectiveEpiStructOfIsColimit {X Y : C} (f : Y ⟶ X)
    (Hf : IsColimit (Sieve.generateSingleton f : Presieve X).cocone) :
    EffectiveEpiStruct f :=
  let aux {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    Cocone (Sieve.generateSingleton f).arrows.diagram :=
    { pt := W
      ι := {
        app := fun ⟨T,hT⟩ => hT.choose ≫ e
        naturality := by
          rintro ⟨A,hA⟩ ⟨B,hB⟩ (q : A ⟶ B)
          dsimp; simp only [← Category.assoc, Category.comp_id]
          apply h
          rw [Category.assoc, hB.choose_spec, hA.choose_spec, Over.w] } }
  { desc := fun {W} e h => Hf.desc (aux e h)
    fac := by
      intro W e h
      dsimp
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      dsimp at this; rw [this]; clear this
      nth_rewrite 2 [← Category.id_comp e]
      apply h
      generalize_proofs hh
      rw [hh.choose_spec, Category.id_comp]
    uniq := by
      intro W e h m hm
      dsimp
      apply Hf.uniq (aux e h)
      rintro ⟨A,g,hA⟩
      dsimp
      nth_rewrite 1 [← hA, Category.assoc, hm]
      apply h
      generalize_proofs hh
      rwa [hh.choose_spec] }

theorem Sieve.effectiveEpimorphic_singleton {X Y : C} (f : Y ⟶ X) :
    (Presieve.singleton f).EffectiveEpimorphic ↔ (EffectiveEpi f) := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateSingleton_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
  · rintro ⟨h⟩
    show Nonempty _
    rw [Sieve.generateSingleton_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h

/--
The sieve of morphisms which factor through a morphism in a given family.
This is equal to `Sieve.generate (Presieve.ofArrows X π)`, but has
more convenient definitional properties.
-/
def Sieve.generateFamily {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    Sieve B where
  arrows Y := { f | ∃ (a : α) (g : Y ⟶ X a), g ≫ π a = f }
  downward_closed := by
    rintro Y₁ Y₂ g₁ ⟨a,q,rfl⟩ e
    exact ⟨a, e ≫ q, by simp⟩

lemma Sieve.generateFamily_eq {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    Sieve.generate (Presieve.ofArrows X π) = Sieve.generateFamily X π := by
  ext Y g
  constructor
  · rintro ⟨W, g, f, ⟨a⟩, rfl⟩
    exact ⟨a, g, rfl⟩
  · rintro ⟨a, g, rfl⟩
    exact ⟨_, g, π a, ⟨a⟩, rfl⟩

/--
This structure encodes the data required for a family of morphisms to be effective epimorphic.
-/
structure EffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) where
  desc : ∀ {W} (e : (a : α) → (X a ⟶ W)),
          (∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) → (B ⟶ W)
  fac : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (a : α), π a ≫ desc e h = e a
  uniq : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (m : B ⟶ W), (∀ (a : α), π a ≫ m = e a) → m = desc e h

attribute [nolint docBlame]
  EffectiveEpiFamilyStruct.desc
  EffectiveEpiFamilyStruct.fac
  EffectiveEpiFamilyStruct.uniq

/--
A family of morphisms `f a : X a ⟶ B` indexed by `α` is effective epimorphic
provided that the `f a` exhibit `B` as a colimit of the diagram of all "relations"
`R → X a₁`, `R ⟶ X a₂` for all `a₁ a₂ : α`.
-/
class EffectiveEpiFamily {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) : Prop where
  effectiveEpiFamily : Nonempty (EffectiveEpiFamilyStruct X π)

attribute [nolint docBlame] EffectiveEpiFamily.effectiveEpiFamily

/-- Some chosen `EffectiveEpiFamilyStruct` associated to an effective epi family. -/
noncomputable
def EffectiveEpiFamily.getStruct {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] : EffectiveEpiFamilyStruct X π :=
  EffectiveEpiFamily.effectiveEpiFamily.some

/-- Descend along an effective epi family. -/
noncomputable
def EffectiveEpiFamily.desc {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) : B ⟶ W :=
  (EffectiveEpiFamily.getStruct X π).desc e h

@[reassoc (attr := simp)]
lemma EffectiveEpiFamily.fac {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) (a : α) :
    π a ≫ EffectiveEpiFamily.desc X π e h = e a :=
  (EffectiveEpiFamily.getStruct X π).fac e h a

/-
NOTE: The `simpNF` linter complains for some reason. See the two examples below.
Zulip discussion:
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/simpNF.20bug.3F
-/
attribute [nolint simpNF]
  EffectiveEpiFamily.fac
  EffectiveEpiFamily.fac_assoc

/-- The effective epi family structure on the identity -/
def effectiveEpiFamilyStructId {α : Unit → C} : EffectiveEpiFamilyStruct α (fun _ => 𝟙 (α ())) where
  desc := fun e _ => e ()
  fac := by aesop_cat
  uniq := by aesop_cat

instance {X : C} : EffectiveEpiFamily (fun _ => X : Unit → C) (fun _ => 𝟙 X) :=
  ⟨⟨effectiveEpiFamilyStructId⟩⟩

example {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) (a : α) :
    π a ≫ EffectiveEpiFamily.desc X π e h = e a :=
  by simp

example {B W Q : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) (a : α)
    (q : W ⟶ Q) :
    π a ≫ EffectiveEpiFamily.desc X π e h ≫ q = e a ≫ q :=
  by simp

lemma EffectiveEpiFamily.uniq {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
    (m : B ⟶ W) (hm : ∀ a, π a ≫ m = e a) :
    m = EffectiveEpiFamily.desc X π e h :=
  (EffectiveEpiFamily.getStruct X π).uniq e h m hm

-- TODO: Once we have "jointly epimorphic families", we could rephrase this as such a property.
lemma EffectiveEpiFamily.hom_ext {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (m₁ m₂ : B ⟶ W) (h : ∀ a, π a ≫ m₁ = π a ≫ m₂) :
    m₁ = m₂ := by
  have : m₂ = EffectiveEpiFamily.desc X π (fun a => π a ≫ m₂)
      (fun a₁ a₂ g₁ g₂ h => by simp only [← Category.assoc, h]) := by
    apply EffectiveEpiFamily.uniq; intro; rfl
  rw [this]
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
def isColimitOfEffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) (H : EffectiveEpiFamilyStruct X π) :
    IsColimit (Sieve.generateFamily X π : Presieve B).cocone :=
  letI D := FullSubcategory fun T : Over B => Sieve.generateFamily X π T.hom
  letI F : D ⥤ _ := (Sieve.generateFamily X π).arrows.diagram
  { desc := fun S => H.desc (fun a => S.ι.app ⟨Over.mk (π a), ⟨a,𝟙 _, by simp⟩⟩) <| by
      intro Z a₁ a₂ g₁ g₂ h
      dsimp
      let A₁ : D := ⟨Over.mk (π a₁), a₁, 𝟙 _, by simp⟩
      let A₂ : D := ⟨Over.mk (π a₂), a₂, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ π a₁), a₁, g₁, rfl⟩
      let i₁ : Z' ⟶ A₁ := Over.homMk g₁
      let i₂ : Z' ⟶ A₂ := Over.homMk g₂
      change F.map i₁ ≫ _ = F.map i₂ ≫ _
      simp only [S.w]
    fac := by
      intro S ⟨T, a, (g : T.left ⟶ X a), hT⟩
      dsimp
      nth_rewrite 1 [← hT, Category.assoc, H.fac]
      let A : D := ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      let B : D := ⟨Over.mk T.hom, a, g, hT⟩
      let i : B ⟶ A := Over.homMk g
      change F.map i ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm; dsimp
      apply H.uniq
      intro a
      exact hm ⟨Over.mk (π a), a, 𝟙 _, by simp⟩ }

/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
noncomputable
def effectiveEpiFamilyStructOfIsColimit {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B))
    (H : IsColimit (Sieve.generateFamily X π : Presieve B).cocone) :
    EffectiveEpiFamilyStruct X π :=
  let aux {W : C} (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) :
    Cocone (Sieve.generateFamily X π).arrows.diagram := {
      pt := W
      ι := {
        app := fun ⟨T,hT⟩ => hT.choose_spec.choose ≫ e hT.choose
        naturality := by
          intro ⟨A,a,(g₁ : A.left ⟶ _),ha⟩ ⟨B,b,(g₂ : B.left ⟶ _),hb⟩ (q : A ⟶ B)
          dsimp; rw [Category.comp_id, ← Category.assoc]
          apply h; rw [Category.assoc]
          generalize_proofs h1 h2 h3 h4
          rw [h2.choose_spec, h4.choose_spec, Over.w] } }
  { desc := fun {W} e h => H.desc (aux e h)
    fac := by
      intro W e h a
      dsimp
      have := H.fac (aux e h) ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      dsimp at this; rw [this]; clear this
      conv_rhs => rw [← Category.id_comp (e a)]
      apply h
      generalize_proofs h1 h2
      rw [h2.choose_spec, Category.id_comp]
    uniq := by
      intro W e h m hm
      apply H.uniq (aux e h)
      rintro ⟨T, a, (g : T.left ⟶ _), ha⟩
      dsimp
      nth_rewrite 1 [← ha, Category.assoc, hm]
      apply h
      generalize_proofs h1 h2
      rwa [h2.choose_spec] }

theorem Sieve.effectiveEpimorphic_family {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    (Presieve.ofArrows X π).EffectiveEpimorphic ↔ EffectiveEpiFamily X π := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateFamily_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiFamilyStructOfIsColimit _ _) h
  · rintro ⟨h⟩
    show Nonempty _
    rw [Sieve.generateFamily_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiFamilyStruct _ _) h


section instances

/--
Given an `EffectiveEpiFamily X π` such that the coproduct of `X` exists, `Sigma.desc π` is an
`EffectiveEpi`.
-/
noncomputable
def effectiveEpiStructDescOfEffectiveEpiFamily' {B : C} {α : Type*} (X : α → C)
    (c : Cofan X) (hc : IsColimit c) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] :
    EffectiveEpiStruct (hc.desc (Cofan.mk B π)) where
  desc e h := EffectiveEpiFamily.desc X π (fun a ↦ c.ι.app ⟨a⟩ ≫ e) (fun a₁ a₂ g₁ g₂ hg ↦ by
    simp only [← Category.assoc]
    apply h (g₁ ≫ c.ι.app ⟨a₁⟩) (g₂ ≫ c.ι.app ⟨a₂⟩)
    simpa)
  fac e h := hc.hom_ext (fun ⟨j⟩ ↦ (by simp))
  uniq e _ m hm :=
    EffectiveEpiFamily.uniq X π (fun a ↦ c.ι.app ⟨a⟩ ≫ e)
      (fun _ _ _ _ hg ↦ (by simp [← hm, reassoc_of% hg])) m (fun _ ↦ (by simp [← hm]))

/--
Given an `EffectiveEpiFamily X π` such that the coproduct of `X` exists, `Sigma.desc π` is an
`EffectiveEpi`.
-/
noncomputable
def effectiveEpiStructDescOfEffectiveEpiFamily {B : C} {α : Type*} (X : α → C)
    (π : (a : α) → (X a ⟶ B)) [HasCoproduct X] [h : EffectiveEpiFamily X π] :
    EffectiveEpiStruct (Sigma.desc π) := by
  simpa [coproductIsCoproduct] using
    effectiveEpiStructDescOfEffectiveEpiFamily' X _ (coproductIsCoproduct _) π

instance {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [HasCoproduct X]
    [EffectiveEpiFamily X π] : EffectiveEpi (Sigma.desc π) :=
  ⟨⟨effectiveEpiStructDescOfEffectiveEpiFamily X π⟩⟩

-- This was an instance before, but we now have the more general one above.
example {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]
    [HasCoproduct X] : Epi (Sigma.desc π) := inferInstance

/--
This is an auxiliary lemma used twice in the definition of  `EffectiveEpiFamilyOfEffectiveEpiDesc`.
It is the `h` hypothesis of `EffectiveEpi.desc` and `EffectiveEpi.fac`. 
-/
theorem effectiveEpiFamilyStructOfEffectiveEpiDesc_aux {B : C} {α : Type*} {X : α → C}
    {π : (a : α) → X a ⟶ B} [HasCoproduct X]
    [∀ {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
    [∀ {Z : C} (g : Z ⟶ ∐ X), HasCoproduct fun a ↦ pullback g (Sigma.ι X a)]
    [∀ {Z : C} (g : Z ⟶ ∐ X), Epi (Sigma.desc fun a ↦ pullback.fst (f := g) (g := (Sigma.ι X a)))]
    {W : C} {e : (a : α) → X a ⟶ W} (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂) {Z : C}
    {g₁ g₂ : Z ⟶ ∐ fun b ↦ X b} (hg : g₁ ≫ Sigma.desc π = g₂ ≫ Sigma.desc π) :
    g₁ ≫ Sigma.desc e = g₂ ≫ Sigma.desc e := by
  apply_fun ((Sigma.desc fun a ↦ pullback.fst (f := g₁) (g := (Sigma.ι X a))) ≫ ·) using
    (fun a b ↦ (cancel_epi _).mp)
  ext a
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app]
  rw [← Category.assoc, pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
  apply_fun ((Sigma.desc fun a ↦ pullback.fst (f := pullback.fst ≫ g₂)
    (g := (Sigma.ι X a))) ≫ ·) using (fun a b ↦ (cancel_epi _).mp)
  ext b
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app]
  simp only [← Category.assoc]
  rw [(Category.assoc _ _ g₂), pullback.condition]
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
  rw [← Category.assoc]
  apply h
  apply_fun (pullback.fst (f := g₁) (g := (Sigma.ι X a)) ≫ ·) at hg
  rw [← Category.assoc, pullback.condition] at hg
  simp only [Category.assoc, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app] at hg
  apply_fun ((Sigma.ι (fun a ↦ pullback _ _) b) ≫ (Sigma.desc fun a ↦ pullback.fst
    (f := pullback.fst ≫ g₂) (g := (Sigma.ι X a))) ≫ ·) at hg
  simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app] at hg
  simp only [← Category.assoc] at hg
  rw [(Category.assoc _ _ g₂), pullback.condition] at hg
  simpa using hg

/--
If a coproduct interacts well enough with pullbacks, then a family whose domains are the terms of
the coproduct is effective epimorphic whenever `Sigma.desc` induces an effective epimorphism from
the coproduct itself.
-/
noncomputable
def effectiveEpiFamilyStructOfEffectiveEpiDesc {B : C} {α : Type*} (X : α → C)
    (π : (a : α) → (X a ⟶ B)) [HasCoproduct X] [EffectiveEpi (Sigma.desc π)]
    [∀ {Z : C} (g : Z ⟶ ∐ X) (a : α), HasPullback g (Sigma.ι X a)]
    [∀ {Z : C} (g : Z ⟶ ∐ X), HasCoproduct (fun a ↦ pullback g (Sigma.ι X a))]
    [∀ {Z : C} (g : Z ⟶ ∐ X),
      Epi (Sigma.desc (fun a ↦ pullback.fst (f := g) (g := (Sigma.ι X a))))] :
    EffectiveEpiFamilyStruct X π where
  desc e h := EffectiveEpi.desc (Sigma.desc π) (Sigma.desc e) fun _ _ hg ↦
    effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg
  fac e h a := by
    rw [(by simp : π a = Sigma.ι X a ≫ Sigma.desc π), (by simp : e a = Sigma.ι X a ≫ Sigma.desc e),
      Category.assoc, EffectiveEpi.fac (Sigma.desc π) (Sigma.desc e) (fun g₁ g₂ hg ↦
      effectiveEpiFamilyStructOfEffectiveEpiDesc_aux h hg)]
  uniq _ _ _ hm := by
    apply EffectiveEpi.uniq (Sigma.desc π)
    ext
    simpa using hm _

/--
An `EffectiveEpiFamily` consisting of a single `EffectiveEpi`
-/
noncomputable
def effectiveEpiFamilyStructSingletonOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f] :
    EffectiveEpiFamilyStruct (fun () ↦ X) (fun () ↦ f) where
  desc e h := EffectiveEpi.desc f (e ()) (fun g₁ g₂ hg ↦ h () () g₁ g₂ hg)
  fac e h := fun _ ↦ EffectiveEpi.fac f (e ()) (fun g₁ g₂ hg ↦ h () () g₁ g₂ hg)
  uniq e h m hm := by apply EffectiveEpi.uniq f (e ()) (h () ()); exact hm ()

instance {B X : C} (f : X ⟶ B) [EffectiveEpi f] : EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f) :=
  ⟨⟨effectiveEpiFamilyStructSingletonOfEffectiveEpi f⟩⟩

/--
A single element `EffectiveEpiFamily` constists of an `EffectiveEpi`
-/
noncomputable
def effectiveEpiStructOfEffectiveEpiFamilySingleton {B X : C} (f : X ⟶ B)
    [EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f)] :
    EffectiveEpiStruct f where
  desc e h := EffectiveEpiFamily.desc
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg)
  fac e h := EffectiveEpiFamily.fac
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg) ()
  uniq e h m hm := EffectiveEpiFamily.uniq
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg) m (fun _ ↦ hm)

instance {B X : C} (f : X ⟶ B) [EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f)] :
    EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfEffectiveEpiFamilySingleton f⟩⟩

theorem effectiveEpi_iff_effectiveEpiFamily {B X : C} (f : X ⟶ B) :
    EffectiveEpi f ↔ EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/--
A family of morphisms with the same target inducing an isomorphism from the coproduct to the target
is an `EffectiveEpiFamily`.
-/
noncomputable
def effectiveEpiFamilyStructOfIsIsoDesc {B : C} {α : Type*} (X : α → C)
    (π : (a : α) → (X a ⟶ B)) [HasCoproduct X] [IsIso (Sigma.desc π)] :
    EffectiveEpiFamilyStruct X π where
  desc e _ := (asIso (Sigma.desc π)).inv ≫ (Sigma.desc e)
  fac e h := by
    intro a
    have : π a = Sigma.ι X a ≫ (asIso (Sigma.desc π)).hom := by simp only [asIso_hom,
      colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    rw [this, Category.assoc]
    simp only [asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc, colimit.ι_desc, Cofan.mk_pt,
      Cofan.mk_ι_app]
  uniq e h m hm := by
    simp only [asIso_inv, IsIso.eq_inv_comp]
    ext a
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.ι_desc]
    exact hm a

instance {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [HasCoproduct X]
    [IsIso (Sigma.desc π)] : EffectiveEpiFamily X π :=
  ⟨⟨effectiveEpiFamilyStructOfIsIsoDesc X π⟩⟩

/-- The identity is an effective epi. -/
noncomputable
def effectiveEpiStructOfIsIso {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpiStruct f where
  desc e _ := inv f ≫ e
  fac _ _ := by simp
  uniq _ _ _ h := by simpa using h

instance {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpi f := ⟨⟨effectiveEpiStructOfIsIso f⟩⟩

/--
A split epi followed by an effective epi is an effective epi. This version takes an explicit section
to the split epi, and is mainly used to define `effectiveEpiStructCompOfEffectiveEpiSplitEpi`,
which takes a `IsSplitEpi` instance instead.
-/
noncomputable
def effectiveEpiStructCompOfEffectiveEpiSplitEpi' {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) (i : X ⟶ Y)
    (hi : i ≫ g = 𝟙 _) [EffectiveEpi f] : EffectiveEpiStruct (g ≫ f) where
  desc e w := EffectiveEpi.desc f (i ≫ e) fun g₁ g₂ _ ↦ (by
    simp only [← Category.assoc]
    apply w (g₁ ≫ i) (g₂ ≫ i)
    simpa [← Category.assoc, hi])
  fac e w := by
    simp only [Category.assoc, EffectiveEpi.fac]
    rw [← Category.id_comp e, ← Category.assoc, ← Category.assoc]
    apply w
    simp only [Category.comp_id, Category.id_comp, ← Category.assoc]
    aesop
  uniq _ _ _ hm := by
    apply EffectiveEpi.uniq f
    rw [← hm, ← Category.assoc, ← Category.assoc, hi, Category.id_comp]

/-- A split epi followed by an effective epi is an effective epi. -/
noncomputable
def effectiveEpiStructCompOfEffectiveEpiSplitEpi {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) [IsSplitEpi g]
    [EffectiveEpi f] : EffectiveEpiStruct (g ≫ f) :=
  effectiveEpiStructCompOfEffectiveEpiSplitEpi' f g
    (IsSplitEpi.exists_splitEpi (f := g)).some.section_
    (IsSplitEpi.exists_splitEpi (f := g)).some.id

instance {B X Y : C} (f : X ⟶ B) (g : Y ⟶ X) [IsSplitEpi g] [EffectiveEpi f] :
    EffectiveEpi (g ≫ f) := ⟨⟨effectiveEpiStructCompOfEffectiveEpiSplitEpi f g⟩⟩

end instances

section Regular

open RegularEpi in
/-- The data of an `EffectiveEpi` structure on a `RegularEpi`. -/
def effectiveEpiStructOfRegularEpi {B X : C} (f : X ⟶ B) [RegularEpi f] :
    EffectiveEpiStruct f where
  desc _ h := Cofork.IsColimit.desc isColimit _ (h _ _ w)
  fac _ _ := Cofork.IsColimit.π_desc' isColimit _ _
  uniq _ _ _ hg := Cofork.IsColimit.hom_ext isColimit (hg.trans
    (Cofork.IsColimit.π_desc' _ _ _).symm)

instance {B X : C} (f : X ⟶ B) [RegularEpi f] : EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfRegularEpi f⟩⟩

/-- A morphism which is a coequalizer for its kernel pair is an effective epi. -/
theorem effectiveEpiOfKernelPair {B X : C} (f : X ⟶ B) [HasPullback f f]
    (hc : IsColimit (Cofork.ofπ f pullback.condition)) : EffectiveEpi f :=
  let _ := regularEpiOfKernelPair f hc
  inferInstance

/-- An effective epi which has a kernel pair is a regular epi. -/
noncomputable instance regularEpiOfEffectiveEpi {B X : C} (f : X ⟶ B) [HasPullback f f]
    [EffectiveEpi f] : RegularEpi f where
  W := pullback f f
  left := pullback.fst
  right := pullback.snd
  w := pullback.condition
  isColimit := {
    desc := fun s ↦ EffectiveEpi.desc f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
      simp only [Cofork.app_one_eq_π]
      rw [← pullback.lift_snd g₁ g₂ hg, Category.assoc, ← Cofork.app_zero_eq_comp_π_right]
      simp)
    fac := by
      intro s j
      have := EffectiveEpi.fac f (s.ι.app WalkingParallelPair.one) fun g₁ g₂ hg ↦ (by
          simp only [Cofork.app_one_eq_π]
          rw [← pullback.lift_snd g₁ g₂ hg, Category.assoc, ← Cofork.app_zero_eq_comp_π_right]
          simp)
      simp only [Functor.const_obj_obj, Cofork.app_one_eq_π] at this
      cases j with
      | zero => simp [this]
      | one => simp [this]
    uniq := fun _ _ h ↦ EffectiveEpi.uniq f _ _ _ (h WalkingParallelPair.one) }

end Regular

section Epi

variable [HasFiniteCoproducts C] (h : ∀ {α : Type} [Finite α] {B : C}
    (X : α → C) (π : (a : α) → (X a ⟶ B)), EffectiveEpiFamily X π ↔ Epi (Sigma.desc π ))

lemma effectiveEpi_iff_epi {X Y : C} (f : X ⟶ Y) : EffectiveEpi f ↔ Epi f := by
  rw [effectiveEpi_iff_effectiveEpiFamily, h]
  have w : f = (Limits.Sigma.ι (fun () ↦ X) ()) ≫ (Limits.Sigma.desc (fun () ↦ f)) := by
    simp only [Limits.colimit.ι_desc, Limits.Cofan.mk_pt, Limits.Cofan.mk_ι_app]
  refine ⟨?_, fun _ ↦ epi_of_epi_fac w.symm⟩
  intro
  rw [w]
  have : Epi (Limits.Sigma.ι (fun () ↦ X) ()) := ⟨fun _ _ h ↦ by ext; exact h⟩
  exact epi_comp _ _

end Epi

noncomputable section Equivalence

variable {D : Type*} [Category D] (e : C ≌ D) {B : C}

variable {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]

theorem effectiveEpiFamilyStructOfEquivalence_aux {W : D} (ε : (a : α) → e.functor.obj (X a) ⟶ W)
    (h : ∀ {Z : D} (a₁ a₂ : α) (g₁ : Z ⟶ e.functor.obj (X a₁)) (g₂ : Z ⟶ e.functor.obj (X a₂)),
      g₁ ≫ e.functor.map (π a₁) = g₂ ≫ e.functor.map (π a₂) → g₁ ≫ ε a₁ = g₂ ≫ ε a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₁ =
    g₂ ≫ (fun a ↦ e.unit.app (X a) ≫ e.inverse.map (ε a)) a₂ := by
  have := h a₁ a₂ (e.functor.map g₁) (e.functor.map g₂)
  simp only [← Functor.map_comp, hg] at this
  simpa using congrArg e.inverse.map (this (by trivial))

/-- Equivalences preserve effective epimorphic families -/
def effectiveEpiFamilyStructOfEquivalence : EffectiveEpiFamilyStruct (fun a ↦ e.functor.obj (X a))
    (fun a ↦ e.functor.map (π a)) where
  desc ε h := (e.toAdjunction.homEquiv _ _).symm
      (EffectiveEpiFamily.desc X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h))
  fac ε h a := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit, Functor.id_obj,
      Equivalence.toAdjunction_counit]
    have := congrArg ((fun f ↦ f ≫ e.counit.app _) ∘ e.functor.map)
      (EffectiveEpiFamily.fac X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h) a)
    simp only [Functor.id_obj, Functor.comp_obj, Function.comp_apply, Functor.map_comp,
        Category.assoc, Equivalence.fun_inv_map, Iso.inv_hom_id_app, Category.comp_id] at this
    simp [this]
  uniq ε h m hm := by
    simp only [Functor.comp_obj, Adjunction.homEquiv_counit, Functor.id_obj,
      Equivalence.toAdjunction_counit]
    have := EffectiveEpiFamily.uniq X π (fun a ↦ e.unit.app _ ≫ e.inverse.map (ε a))
      (effectiveEpiFamilyStructOfEquivalence_aux e X π ε h)
    specialize this (e.unit.app _ ≫ e.inverse.map m) fun a ↦ ?_
    · rw [← congrArg e.inverse.map (hm a)]
      simp
    · simp [← this]

instance (F : C ⥤ D) [IsEquivalence F] :
    EffectiveEpiFamily (fun a ↦ F.obj (X a)) (fun a ↦ F.map (π a)) :=
  ⟨⟨effectiveEpiFamilyStructOfEquivalence F.asEquivalence _ _⟩⟩

example {X B : C} (π : X ⟶ B) (F : C ⥤ D) [IsEquivalence F] [EffectiveEpi π] :
    EffectiveEpi <| F.map π := inferInstance

end Equivalence

section CompIso

variable {B B' : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]
  (i : B ⟶ B') [IsIso i]

theorem effectiveEpiFamilyStructCompIso_aux
    {W : C} (e : (a : α) → X a ⟶ W)
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ ≫ i = g₂ ≫ π a₂ ≫ i → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  apply h
  rw [← Category.assoc, hg]
  simp

/-- An effective epi family followed by an iso is an effective epi family. -/
noncomputable
def effectiveEpiFamilyStructCompIso : EffectiveEpiFamilyStruct X (fun a ↦ π a ≫ i) where
  desc e h := inv i ≫ EffectiveEpiFamily.desc X π e (effectiveEpiFamilyStructCompIso_aux X π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π e
      (effectiveEpiFamilyStructCompIso_aux X π i e h) (i ≫ m) hm]

instance : EffectiveEpiFamily X (fun a ↦ π a ≫ i) := ⟨⟨effectiveEpiFamilyStructCompIso X π i⟩⟩

end CompIso

section IsoComp

variable {B : C} {α : Type*} (X Y : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π]
  (i : (a : α) → Y a ⟶ X a) [∀ a, IsIso (i a)]

theorem effectiveEpiFamilyStructIsoComp_aux {W : C} (e : (a : α) → Y a ⟶ W)
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ Y a₁) (g₂ : Z ⟶ Y a₂),
      g₁ ≫ i a₁ ≫ π a₁ = g₂ ≫ i a₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂) (hg : g₁ ≫ π a₁ = g₂ ≫ π a₂) :
    g₁ ≫ (fun a ↦ inv (i a) ≫ e a) a₁ = g₂ ≫ (fun a ↦ inv (i a) ≫ e a) a₂ := by
  simp only [← Category.assoc]
  apply h
  simp [hg]

/-- An effective epi family preceded by a family of isos is an effective epi family. -/
noncomputable
def effectiveEpiFamilyStructIsoComp : EffectiveEpiFamilyStruct Y (fun a ↦ i a ≫ π a) where
  desc e h := EffectiveEpiFamily.desc X π (fun a ↦ inv (i a) ≫ e a)
    (effectiveEpiFamilyStructIsoComp_aux X Y π i e h)
  fac _ _ _ := by simp
  uniq e h m hm := by
    simp only [Category.assoc] at hm
    simp [← EffectiveEpiFamily.uniq X π (fun a ↦ inv (i a) ≫ e a)
      (effectiveEpiFamilyStructIsoComp_aux X Y π i e h) m fun a ↦ by simpa using hm a]

instance effectiveEpiFamilyIsoComp : EffectiveEpiFamily Y (fun a ↦ i a ≫ π a) :=
  ⟨⟨effectiveEpiFamilyStructIsoComp X Y π i⟩⟩

end IsoComp

section Preserves

variable {D : Type*} [Category D]

namespace Functor

/--
A functor preserves effective epimorphisms if it maps effective epimorphisms to effective
epimorphisms.
-/
class PreservesEffectiveEpis (F : C ⥤ D) : Prop where
  /--
  A functor preserves effective epimorphisms if it maps effective
  epimorphisms to effective epimorphisms.
  -/
  preserves : ∀ {X Y : C} (f : X ⟶ Y) [EffectiveEpi f], EffectiveEpi (F.map f)

instance map_effectiveEpi (F : C ⥤ D) [F.PreservesEffectiveEpis] {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi f] : EffectiveEpi (F.map f) :=
  PreservesEffectiveEpis.preserves f

instance (F : C ⥤ D) [IsEquivalence F] : F.PreservesEffectiveEpis where
  preserves _ := inferInstance

end Functor

end Preserves

end CategoryTheory
