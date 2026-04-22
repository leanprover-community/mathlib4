/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
/-!

# Effective epimorphisms

We define the notion of effective epimorphism and effective epimorphic family of morphisms.

A morphism is an *effective epi* if it is a joint coequalizer of all pairs of
morphisms which it coequalizes.

A family of morphisms with fixed target is *effective epimorphic* if it is initial among families
of morphisms with its sources and a general fixed target, coequalizing every pair of morphisms it
coequalizes (here, the pair of morphisms coequalized can have different targets among the sources
of the family).

We have defined the notion of effective epi for morphisms and families of morphisms in such a
way that avoids requiring the existence of pullbacks. However, if the relevant pullbacks exist
then these definitions are equivalent, see the file
`Mathlib/CategoryTheory/EffectiveEpi/RegularEpi.lean`
See [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
[Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions. Note that
our notion of `EffectiveEpi` is often called "strict epi" in the literature.

## References
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
- [Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

variable {C : Type*} [Category* C]

/--
This structure encodes the data required for a morphism to be an effective epimorphism.
-/
structure EffectiveEpiStruct {X Y : C} (f : Y ⟶ X) where
  /--
  For every `W` with a morphism `e : Y ⟶ W` that coequalizes every pair of morphisms
  `g₁ g₂ : Z ⟶ Y` which `f` coequalizes, `desc e h` is a morphism `X ⟶ W`...
  -/
  desc : ∀ {W : C} (e : Y ⟶ W),
    (∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) → (X ⟶ W)
  /-- ...factorizing `e` through `f`... -/
  fac : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e),
    f ≫ desc e h = e
  /-- ...and as such, unique. -/
  uniq : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W), f ≫ m = e → m = desc e h

/--
A morphism `f : Y ⟶ X` is an effective epimorphism provided that `f` exhibits `X` as a colimit
of the diagram of all "relations" `R ⇉ Y`.
If `f` has a kernel pair, then this is equivalent to showing that the corresponding cofork is
a colimit.
-/
class EffectiveEpi {X Y : C} (f : Y ⟶ X) : Prop where
  /-- `f` is an effective epimorphism if there exists an `EffectiveEpiStruct` for `f`. -/
  effectiveEpi : Nonempty (EffectiveEpiStruct f)

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

open EffectiveEpi Category

instance epi_of_effectiveEpi {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : Epi f where
  left_cancellation m₁ m₂ h := by
    rw [show m₂ = desc f (f ≫ m₂) (fun _ _ h => by simp [← assoc, h]) from uniq _ _ _ _ rfl]
    exact uniq _ _ _ _ h

@[deprecated (since := "2025-11-20")] alias epiOfEffectiveEpi := epi_of_effectiveEpi

instance (priority := 100) strongEpi_of_effectiveEpi {X Y : C} (f : X ⟶ Y) [EffectiveEpi f] :
    StrongEpi f :=
  StrongEpi.mk' fun A B z hz u v sq ↦
    have : ∀ {Z : C} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ u = g₂ ≫ u := fun _ _ h ↦ by
      simpa [← sq.w, cancel_mono_assoc_iff] using h =≫ v
    CommSq.HasLift.mk' ⟨desc f u this, fac f u this, (cancel_epi f).1 ((by simp [← sq.w]))⟩

/--
This structure encodes the data required for a family of morphisms to be effective epimorphic.
-/
structure EffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) where
  /--
  For every `W` with a family of morphisms `e a : X a ⟶ W` that coequalizes every pair of morphisms
  `g₁ : Z ⟶ X a₁`, `g₂ : Z ⟶ X a₂` which the family `π` coequalizes, `desc e h` is a morphism
  `B ⟶ W`...
  -/
  desc : ∀ {W} (e : (a : α) → (X a ⟶ W)),
      (∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) → (B ⟶ W)
  /-- ...factorizing the components of `e` through the components of `π`... -/
  fac : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (a : α), π a ≫ desc e h = e a
  /-- ...and as such, unique. -/
  uniq : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (m : B ⟶ W), (∀ (a : α), π a ≫ m = e a) → m = desc e h

/--
A family of morphisms `π a : X a ⟶ B` indexed by `α` is effective epimorphic
provided that the `π a` exhibit `B` as a colimit of the diagram of all "relations"
`R ⟶ X a₁`, `R ⟶ X a₂` for all `a₁ a₂ : α`.
-/
class EffectiveEpiFamily {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) : Prop where
  /-- `π` is an effective epimorphic family if there exists an `EffectiveEpiFamilyStruct` for `π` -/
  effectiveEpiFamily : Nonempty (EffectiveEpiFamilyStruct X π)

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
      (fun a₁ a₂ g₁ g₂ h => by simp only [← assoc, h]) := by
    apply EffectiveEpiFamily.uniq; intro; rfl
  rw [this]
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h

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
A single element `EffectiveEpiFamily` consists of an `EffectiveEpi`
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

set_option backward.isDefEq.respectTransparency false in
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
    rw [this, assoc]
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

/-- Any isomorphism is an effective epi. -/
noncomputable
def effectiveEpiStructOfIsIso {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpiStruct f where
  desc e _ := inv f ≫ e
  fac _ _ := by simp
  uniq _ _ _ h := by simpa using h

instance {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpi f := ⟨⟨effectiveEpiStructOfIsIso f⟩⟩

example {X : C} : EffectiveEpiFamily (fun _ => X : Unit → C) (fun _ => 𝟙 X) := inferInstance

/--
Reindex the indexing type of an effective epi family struct.
-/
def EffectiveEpiFamilyStruct.reindex
    {B : C} {α α' : Type*}
    (X : α → C)
    (π : (a : α) → (X a ⟶ B))
    (e : α' ≃ α)
    (P : EffectiveEpiFamilyStruct (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamilyStruct X π where
  desc := fun f h => P.desc (fun _ => f _) (fun _ _ => h _ _)
  fac _ _ a := by
    obtain ⟨a, rfl⟩ := e.surjective a
    apply P.fac
  uniq _ _ _ hm := P.uniq _ _ _ fun _ => hm _

/--
Reindex the indexing type of an effective epi family.
-/
lemma EffectiveEpiFamily.reindex
    {B : C} {α α' : Type*}
    (X : α → C)
    (π : (a : α) → (X a ⟶ B))
    (e : α' ≃ α)
    (h : EffectiveEpiFamily (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamily X π :=
  .mk <| .intro <| @EffectiveEpiFamily.getStruct _ _ _ _ _ _ h |>.reindex _ _ e

end CategoryTheory
