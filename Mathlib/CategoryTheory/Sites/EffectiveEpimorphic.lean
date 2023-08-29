/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

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
then these definitions should be equivalent (project: formalize this!).
See [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
[Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions.

## References
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
- [Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions.

-/

set_option autoImplicit true

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
    -- ⊢ setOf (fun g => ∃ e, e ≫ f = g) (q ≫ e ≫ f)
    refine ⟨q ≫ e, by simp⟩
    -- 🎉 no goals

lemma Sieve.generateSingleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generateSingleton f := by
  ext Z g
  -- ⊢ (generate (Presieve.singleton f)).arrows g ↔ (generateSingleton f).arrows g
  constructor
  -- ⊢ (generate (Presieve.singleton f)).arrows g → (generateSingleton f).arrows g
  · rintro ⟨W,i,p,⟨⟩,rfl⟩
    -- ⊢ (generateSingleton f).arrows (i ≫ f)
    exact ⟨i,rfl⟩
    -- 🎉 no goals
  · rintro ⟨g,h⟩
    -- ⊢ (generate (Presieve.singleton f)).arrows g✝
    exact ⟨Y,g,f,⟨⟩,h⟩
    -- 🎉 no goals

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
def EffectiveEpi.getStruct {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] :
  EffectiveEpiStruct f := EffectiveEpi.effectiveEpi.some

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
  -- ⊢ ∀ {Z : C} (g h : X ⟶ Z), f ≫ g = f ≫ h → g = h
  intro W m₁ m₂ h
  -- ⊢ m₁ = m₂
  have : m₂ = EffectiveEpi.desc f (f ≫ m₂)
    (fun {Z} g₁ g₂ h => by simp only [← Category.assoc, h]) := EffectiveEpi.uniq _ _ _ _ rfl
  rw [this]
  -- ⊢ m₁ = EffectiveEpi.desc f (f ≫ m₂) (_ : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g …
  exact EffectiveEpi.uniq _ _ _ _ h
  -- 🎉 no goals

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
                                                           -- 🎉 no goals
      intro Z g₁ g₂ h
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = (Ove …
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = (Ove …
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = (Ove …
      let g₁' : Z' ⟶ Y' := Over.homMk g₁
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = (Ove …
      let g₂' : Z' ⟶ Y' := Over.homMk g₂ (by simp [h])
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = (Ove …
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      -- ⊢ F.map g₁' ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f …
      simp only [S.w]
      -- 🎉 no goals
    fac := by
      rintro S ⟨T,g,hT⟩
      -- ⊢ NatTrans.app (Presieve.cocone (Sieve.generateSingleton f).arrows).ι { obj := …
      dsimp
      -- ⊢ T.hom ≫ EffectiveEpiStruct.desc Hf (NatTrans.app S.ι { obj := Over.mk f, pro …
      nth_rewrite 1 [← hT, Category.assoc, Hf.fac]
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = f) }  …
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = f) }  …
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = f) }  …
      let g' : x ⟶ y := Over.homMk g
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f = f) }  …
      change F.map g' ≫ _ = _
      -- ⊢ F.map g' ≫ NatTrans.app S.ι { obj := Over.mk f, property := (_ : ∃ e, e ≫ f  …
      rw [S.w]
      -- ⊢ NatTrans.app S.ι x = NatTrans.app S.ι { obj := T, property := (_ : ∃ e, e ≫  …
      rfl
      -- 🎉 no goals
    uniq := by
      intro S m hm
      -- ⊢ m =
      dsimp
      -- ⊢ m = EffectiveEpiStruct.desc Hf (NatTrans.app S.ι { obj := Over.mk f, propert …
      generalize_proofs h1 h2
      -- ⊢ m = EffectiveEpiStruct.desc Hf (NatTrans.app S.ι { obj := Over.mk f, propert …
      apply Hf.uniq _ h2
      -- ⊢ f ≫ m = NatTrans.app S.ι { obj := Over.mk f, property := h1 }
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }
      -- 🎉 no goals

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
          -- ⊢ (Presieve.diagram (Sieve.generateSingleton f).arrows).map q ≫
          dsimp; simp only [← Category.assoc, Category.comp_id]
          -- ⊢ q.left ≫ Exists.choose hB ≫ e = (Exists.choose hA ≫ e) ≫ 𝟙 W
                 -- ⊢ (q.left ≫ Exists.choose hB) ≫ e = Exists.choose hA ≫ e
          apply h
          -- ⊢ (q.left ≫ Exists.choose hB) ≫ f = Exists.choose hA ≫ f
          rw [Category.assoc, hB.choose_spec, hA.choose_spec, Over.w] } }
          -- 🎉 no goals
  { desc := fun {W} e h => Hf.desc (aux e h)
    fac := by
      intro W e h
      -- ⊢ f ≫ (fun {W} e h => IsColimit.desc Hf (aux e (_ : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), …
      dsimp
      -- ⊢ f ≫ IsColimit.desc Hf { pt := W, ι := NatTrans.mk fun x => Exists.choose (_  …
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      -- ⊢ f ≫ IsColimit.desc Hf { pt := W, ι := NatTrans.mk fun x => Exists.choose (_  …
      dsimp at this; rw [this]; clear this
      -- ⊢ f ≫ IsColimit.desc Hf { pt := W, ι := NatTrans.mk fun x => Exists.choose (_  …
                     -- ⊢ Exists.choose (_ : ∃ e, e ≫ f = f) ≫ e = e
                                -- ⊢ Exists.choose (_ : ∃ e, e ≫ f = f) ≫ e = e
      nth_rewrite 2 [← Category.id_comp e]
      -- ⊢ Exists.choose (_ : ∃ e, e ≫ f = f) ≫ e = 𝟙 Y ≫ e
      apply h
      -- ⊢ Exists.choose (_ : ∃ e, e ≫ f = f) ≫ f = 𝟙 Y ≫ f
      generalize_proofs hh
      -- ⊢ Exists.choose hh ≫ f = 𝟙 Y ≫ f
      rw [hh.choose_spec, Category.id_comp]
      -- 🎉 no goals
    uniq := by
      intro W e h m hm
      -- ⊢ m = (fun {W} e h => IsColimit.desc Hf (aux e (_ : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), …
      dsimp
      -- ⊢ m = IsColimit.desc Hf { pt := W, ι := NatTrans.mk fun x => Exists.choose (_  …
      apply Hf.uniq (aux e h)
      -- ⊢ ∀ (j : FullSubcategory fun f_1 => (Sieve.generateSingleton f).arrows f_1.hom …
      rintro ⟨A,g,hA⟩
      -- ⊢ NatTrans.app (Presieve.cocone (Sieve.generateSingleton f).arrows).ι { obj := …
      dsimp
      -- ⊢ A.hom ≫ m = Exists.choose (_ : ∃ e, e ≫ f = A.hom) ≫ e
      nth_rewrite 1 [← hA, Category.assoc, hm]
      -- ⊢ g ≫ e = Exists.choose (_ : ∃ e, e ≫ f = A.hom) ≫ e
      apply h
      -- ⊢ g ≫ f = Exists.choose (_ : ∃ e, e ≫ f = A.hom) ≫ f
      generalize_proofs hh
      -- ⊢ g ≫ f = Exists.choose hh ≫ f
      rwa [hh.choose_spec] }
      -- 🎉 no goals

theorem Sieve.effectiveEpimorphic_singleton {X Y : C} (f : Y ⟶ X) :
    (Presieve.singleton f).EffectiveEpimorphic ↔ (EffectiveEpi f) := by
  constructor
  -- ⊢ Presieve.EffectiveEpimorphic (Presieve.singleton f) → EffectiveEpi f
  · intro (h : Nonempty _)
    -- ⊢ EffectiveEpi f
    rw [Sieve.generateSingleton_eq] at h
    -- ⊢ EffectiveEpi f
    constructor
    -- ⊢ Nonempty (EffectiveEpiStruct f)
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
    -- 🎉 no goals
  · rintro ⟨h⟩
    -- ⊢ Presieve.EffectiveEpimorphic (Presieve.singleton f)
    show Nonempty _
    -- ⊢ Nonempty (IsColimit (Presieve.cocone (generate (Presieve.singleton f)).arrow …
    rw [Sieve.generateSingleton_eq]
    -- ⊢ Nonempty (IsColimit (Presieve.cocone (generateSingleton f).arrows))
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h
    -- 🎉 no goals

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
    -- ⊢ setOf (fun f => ∃ a g, g ≫ π a = f) (e ≫ q ≫ π a)
    refine ⟨a, e ≫ q, by simp⟩
    -- 🎉 no goals

lemma Sieve.generateFamily_eq {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    Sieve.generate (Presieve.ofArrows X π) = Sieve.generateFamily X π := by
  ext Y g
  -- ⊢ (generate (Presieve.ofArrows X π)).arrows g ↔ (generateFamily X π).arrows g
  constructor
  -- ⊢ (generate (Presieve.ofArrows X π)).arrows g → (generateFamily X π).arrows g
  · rintro ⟨W, g, f, ⟨a⟩, rfl⟩
    -- ⊢ (generateFamily X π).arrows (g ≫ π a)
    exact ⟨a, g, rfl⟩
    -- 🎉 no goals
  · rintro ⟨a, g, rfl⟩
    -- ⊢ (generate (Presieve.ofArrows X π)).arrows (g ≫ π a)
    refine ⟨_, g, π a, ⟨a⟩, rfl⟩
    -- 🎉 no goals

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
def effectiveEpiFamilyStructId : EffectiveEpiFamilyStruct (α : Unit → C) (fun _ => 𝟙 (α ())) where
  desc := fun e _ => e ()
  fac := by aesop_cat
            -- 🎉 no goals
  uniq := by aesop_cat
             -- 🎉 no goals

instance : EffectiveEpiFamily (fun _ => X : Unit → C) (fun _ => 𝟙 X) :=
  ⟨⟨effectiveEpiFamilyStructId⟩⟩

example {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) (a : α) :
    π a ≫ EffectiveEpiFamily.desc X π e h = e a :=
  by simp
     -- 🎉 no goals

example {B W Q : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) (a : α)
    (q : W ⟶ Q) :
    π a ≫ EffectiveEpiFamily.desc X π e h ≫ q = e a ≫ q :=
  by simp
     -- 🎉 no goals

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
  -- ⊢ m₁ = desc X π (fun a => π a ≫ m₂) (_ : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) …
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h
  -- 🎉 no goals

instance epiCoproductDescOfEffectiveEpiFamily {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) [EffectiveEpiFamily X π] [HasCoproduct X] :
    Epi (Sigma.desc π) := by
  constructor
  -- ⊢ ∀ {Z : C} (g h : B ⟶ Z), Sigma.desc π ≫ g = Sigma.desc π ≫ h → g = h
  intro Z g h H
  -- ⊢ g = h
  apply EffectiveEpiFamily.hom_ext X π
  -- ⊢ ∀ (a : α), π a ≫ g = π a ≫ h
  intro a
  -- ⊢ π a ≫ g = π a ≫ h
  suffices (Sigma.ι _ a ≫ Sigma.desc π) ≫ g = (Sigma.ι _ a ≫ Sigma.desc π) ≫ h by
    simpa only [colimit.ι_desc] using this
  simp only [Category.assoc, H]
  -- 🎉 no goals

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
                                                                         -- 🎉 no goals
      intro Z a₁ a₂ g₁ g₂ h
      -- ⊢ g₁ ≫ (fun a => NatTrans.app S.ι { obj := Over.mk (π a), property := (_ : ∃ a …
      dsimp
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk (π a₁), property := (_ : ∃ a g, g ≫ π …
      let A₁ : D := ⟨Over.mk (π a₁), a₁, 𝟙 _, by simp⟩
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk (π a₁), property := (_ : ∃ a g, g ≫ π …
      let A₂ : D := ⟨Over.mk (π a₂), a₂, 𝟙 _, by simp⟩
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk (π a₁), property := (_ : ∃ a g, g ≫ π …
      let Z' : D := ⟨Over.mk (g₁ ≫ π a₁), a₁, g₁, rfl⟩
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk (π a₁), property := (_ : ∃ a g, g ≫ π …
      let i₁ : Z' ⟶ A₁ := Over.homMk g₁
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk (π a₁), property := (_ : ∃ a g, g ≫ π …
      let i₂ : Z' ⟶ A₂ := Over.homMk g₂
      -- ⊢ g₁ ≫ NatTrans.app S.ι { obj := Over.mk (π a₁), property := (_ : ∃ a g, g ≫ π …
      change F.map i₁ ≫ _ = F.map i₂ ≫ _
      -- ⊢ F.map i₁ ≫ NatTrans.app S.ι { obj := Over.mk (π a₁), property := (_ : ∃ a g, …
      simp only [S.w]
      -- 🎉 no goals
    fac := by
      intro S ⟨T, a, (g : T.left ⟶ X a), hT⟩
      -- ⊢ NatTrans.app (Presieve.cocone (Sieve.generateFamily X π).arrows).ι { obj :=  …
      dsimp
      -- ⊢ T.hom ≫ EffectiveEpiFamilyStruct.desc H (fun a => NatTrans.app S.ι { obj :=  …
      nth_rewrite 1 [← hT, Category.assoc, H.fac]
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk (π a), property := (_ : ∃ a_1 g, g ≫ π …
      let A : D := ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk (π a), property := (_ : ∃ a_1 g, g ≫ π …
      let B : D := ⟨Over.mk T.hom, a, g, hT⟩
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk (π a), property := (_ : ∃ a_1 g, g ≫ π …
      let i : B ⟶ A := Over.homMk g
      -- ⊢ g ≫ NatTrans.app S.ι { obj := Over.mk (π a), property := (_ : ∃ a_1 g, g ≫ π …
      change F.map i ≫ _ = _
      -- ⊢ F.map i ≫ NatTrans.app S.ι { obj := Over.mk (π a), property := (_ : ∃ a_1 g, …
      rw [S.w]
      -- ⊢ NatTrans.app S.ι B = NatTrans.app S.ι { obj := T, property := (_ : ∃ a g, g  …
      rfl
      -- 🎉 no goals
    uniq := by
      intro S m hm; dsimp
      -- ⊢ m = (fun S => EffectiveEpiFamilyStruct.desc H (fun a => NatTrans.app S.ι { o …
                    -- ⊢ m = EffectiveEpiFamilyStruct.desc H (fun a => NatTrans.app S.ι { obj := Over …
      apply H.uniq
      -- ⊢ ∀ (a : α), π a ≫ m = NatTrans.app S.ι { obj := Over.mk (π a), property := (_ …
      intro a
      -- ⊢ π a ≫ m = NatTrans.app S.ι { obj := Over.mk (π a), property := (_ : ∃ a_1 g, …
      exact hm ⟨Over.mk (π a), a, 𝟙 _, by simp⟩ }
      -- 🎉 no goals

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
          -- ⊢ (Presieve.diagram (Sieve.generateFamily X π).arrows).map q ≫
          dsimp; rw [Category.comp_id, ← Category.assoc]
          -- ⊢ q.left ≫ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a g, g ≫ π a =  …
                 -- ⊢ (q.left ≫ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a g, g ≫ π a = …
          apply h; rw [Category.assoc]
          -- ⊢ (q.left ≫ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a g, g ≫ π a = …
                   -- ⊢ q.left ≫ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a g, g ≫ π a =  …
          generalize_proofs h1 h2 h3 h4
          -- ⊢ q.left ≫ Exists.choose h2 ≫ π (Exists.choose h1) = Exists.choose h4 ≫ π (Exi …
          rw [h2.choose_spec, h4.choose_spec, Over.w] } }
          -- 🎉 no goals
  { desc := fun {W} e h => H.desc (aux e h)
    fac := by
      intro W e h a
      -- ⊢ π a ≫ (fun {W} e h => IsColimit.desc H (aux e (_ : ∀ {Z : C} (a₁ a₂ : α) (g₁ …
      dsimp
      -- ⊢ π a ≫ IsColimit.desc H { pt := W, ι := NatTrans.mk fun x => Exists.choose (_ …
      have := H.fac (aux e h) ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      -- ⊢ π a ≫ IsColimit.desc H { pt := W, ι := NatTrans.mk fun x => Exists.choose (_ …
      dsimp at this; rw [this]; clear this
      -- ⊢ π a ≫ IsColimit.desc H { pt := W, ι := NatTrans.mk fun x => Exists.choose (_ …
                     -- ⊢ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a_1 g, g ≫ π a_1 = π a)) …
                                -- ⊢ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a_1 g, g ≫ π a_1 = π a)) …
      conv_rhs => rw [← Category.id_comp (e a)]
      -- ⊢ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a_1 g, g ≫ π a_1 = π a)) …
      apply h
      -- ⊢ Exists.choose (_ : ∃ g, g ≫ π (Exists.choose (_ : ∃ a_1 g, g ≫ π a_1 = π a)) …
      generalize_proofs h1 h2
      -- ⊢ Exists.choose h2 ≫ π (Exists.choose h1) = 𝟙 (X a) ≫ π a
      rw [h2.choose_spec, Category.id_comp]
      -- 🎉 no goals
    uniq := by
      intro W e h m hm
      -- ⊢ m = (fun {W} e h => IsColimit.desc H (aux e (_ : ∀ {Z : C} (a₁ a₂ : α) (g₁ : …
      apply H.uniq (aux e h)
      -- ⊢ ∀ (j : FullSubcategory fun f => (Sieve.generateFamily X π).arrows f.hom), Na …
      rintro ⟨T, a, (g : T.left ⟶ _), ha⟩
      -- ⊢ NatTrans.app (Presieve.cocone (Sieve.generateFamily X π).arrows).ι { obj :=  …
      dsimp
      -- ⊢ T.hom ≫ m = Exists.choose (_ : ∃ g_1, g_1 ≫ π (Exists.choose (_ : ∃ a g, g ≫ …
      nth_rewrite 1 [← ha, Category.assoc, hm]
      -- ⊢ g ≫ e a = Exists.choose (_ : ∃ g_1, g_1 ≫ π (Exists.choose (_ : ∃ a g, g ≫ π …
      apply h
      -- ⊢ g ≫ π a = Exists.choose (_ : ∃ g_1, g_1 ≫ π (Exists.choose (_ : ∃ a g, g ≫ π …
      generalize_proofs h1 h2
      -- ⊢ g ≫ π a = Exists.choose h2 ≫ π (Exists.choose h1)
      rwa [h2.choose_spec] }
      -- 🎉 no goals

theorem Sieve.effectiveEpimorphic_family {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    (Presieve.ofArrows X π).EffectiveEpimorphic ↔ EffectiveEpiFamily X π := by
  constructor
  -- ⊢ Presieve.EffectiveEpimorphic (Presieve.ofArrows X π) → EffectiveEpiFamily X π
  · intro (h : Nonempty _)
    -- ⊢ EffectiveEpiFamily X π
    rw [Sieve.generateFamily_eq] at h
    -- ⊢ EffectiveEpiFamily X π
    constructor
    -- ⊢ Nonempty (EffectiveEpiFamilyStruct X π)
    apply Nonempty.map (effectiveEpiFamilyStructOfIsColimit _ _) h
    -- 🎉 no goals
  · rintro ⟨h⟩
    -- ⊢ Presieve.EffectiveEpimorphic (Presieve.ofArrows X π)
    show Nonempty _
    -- ⊢ Nonempty (IsColimit (Presieve.cocone (generate (Presieve.ofArrows X π)).arro …
    rw [Sieve.generateFamily_eq]
    -- ⊢ Nonempty (IsColimit (Presieve.cocone (generateFamily X π).arrows))
    apply Nonempty.map (isColimitOfEffectiveEpiFamilyStruct _ _) h
    -- 🎉 no goals

end CategoryTheory
