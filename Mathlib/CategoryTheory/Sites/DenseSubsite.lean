/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-!
# Dense subsites

We define `IsCoverDense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

## Main results

- `CategoryTheory.Functor.IsCoverDense.Types.presheafHom`: If `G : C ⥤ (D, K)` is
  and cover-dense, then given any presheaf `ℱ` and sheaf `ℱ'` on `D`,
  and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`, we may glue them together to obtain
  a morphism of presheaves `ℱ ⟶ ℱ'`.
- `CategoryTheory.Functor.IsCoverDense.sheafIso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is
  and cover-dense, then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`,
  then `α` is an iso if `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `CategoryTheory.Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting`:
  If `G : (C, J) ⥤ (D, K)` is faithful, cover-lifting, cover-preserving, and cover-dense,
  then it will induce an equivalence of categories of sheaves valued in a complete category.

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/


universe w v u

namespace CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/-- An auxiliary structure that witnesses the fact that `f` factors through an image object of `G`.
-/
-- Porting note(#5171): removed `@[nolint has_nonempty_instance]`
structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by aesop_cat
attribute [nolint docBlame] Presieve.CoverByImageStructure.obj Presieve.CoverByImageStructure.lift
  Presieve.CoverByImageStructure.map Presieve.CoverByImageStructure.fac

attribute [reassoc (attr := simp)] Presieve.CoverByImageStructure.fac

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `Presieve.coverByImage G U` is the presieve
of `U` consisting of those arrows that factor through images of `G`.
-/
def Presieve.coverByImage (G : C ⥤ D) (U : D) : Presieve U := fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `Sieve.coverByImage G U` is the sieve of `U`
consisting of those arrows that factor through images of `G`.
-/
def Sieve.coverByImage (G : C ⥤ D) (U : D) : Sieve U :=
  ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩

theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩

-- /--
-- For a functor `G : C ⥤ D`, and an morphism `U ⟶ G.obj V`,
-- `Sieve.coverByImageHom G f` is the sieve of `U`
-- consisting of those arrows that factor through images of arrows of `G`.
-- -/
-- def Sieve.coverByImageHom (G : C ⥤ D) {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve (G.obj U) where
--   arrows Y i := ∃ (Y' : C) (lift : Y ⟶ G.obj Y') (fac₁ : Y' ⟶ V) (fac₂ : Y' ⟶ U),
--     G.map fac₁ = G.map fac₂ ≫ f ∧ lift ≫ G.map fac₂ = i
--   downward_closed := by
--     rintro Y₁ Y₂ i₁ ⟨Y'₁, lift₁, fac₁, fac₂, e₁, rfl⟩ i₂
--     refine ⟨_, _, _, fac₂, e₁, Category.assoc _ _ _⟩

/--
For a functor `G : C ⥤ D`, and an morphism `f : G.obj U ⟶ G.obj V`,
`Sieve.hasLift G f` is the sieve of `U`
consisting of those arrows whose composition with `f` has a lift in `G`.
-/
def Sieve.hasLift (G : C ⥤ D) {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve U where
  arrows Y i := ∃ l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩

lemma Sieve.coverByImage_le_hasLift (G : C ⥤ D) [G.Full] {U V : C} (f : G.obj U ⟶ G.obj V) :
    coverByImage G _ ≤ (hasLift G f).functorPushforward G := by
  rintro W g ⟨Z, lift, fac, e⟩
  exact ⟨Z, G.preimage fac, lift, ⟨G.preimage _, G.map_preimage _⟩, by simp [e]⟩

/--
For two arrows `f₁ f₂ : U ⟶ V`, the arrows `i` such that `i ≫ f₁ = i ≫ f₂` forms a sieve.
-/
@[simps]
def Sieve.equalizer {U V : C} (f₁ f₂ : U ⟶ V) : Sieve U where
  arrows Y i := i ≫ f₁ = i ≫ f₂
  downward_closed := by aesop

@[simp]
lemma Sieve.equalizer_self {U V : C} (f : U ⟶ V) : equalizer f f = ⊤ := by ext; simp

/-- A functor `G : (C, J) ⥤ (D, K)` is cover dense if for each object and arrows in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
class Functor.IsCoverDense (G : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  coverByImage_mem : ∀ U : D, Sieve.coverByImage G U ∈ K U
  functorPushforward_hasLift_mem : ∀ {U V} (f : G.obj U ⟶ G.obj V),
    (Sieve.hasLift G f).functorPushforward G ∈ K _
  functorPushforward_equalizer_mem : ∀ {U V : C} (f₁ f₂ : U ⟶ V), G.map f₁ = G.map f₂ →
    (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _

lemma Functor.coverByImage_mem (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] (U : D) : Sieve.coverByImage G U ∈ K U :=
  Functor.IsCoverDense.coverByImage_mem _

lemma Functor.functorPushforward_hasLift_mem (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] {U V} (f : G.obj U ⟶ G.obj V) :
    (Sieve.hasLift G f).functorPushforward G ∈ K _ :=
  Functor.IsCoverDense.functorPushforward_hasLift_mem _

lemma Functor.functorPushforward_equalizer_mem (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
      (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _ :=
  Functor.IsCoverDense.functorPushforward_equalizer_mem _ _ e

lemma Functor.isCoverDense_of_full_of_faithful (G : C ⥤ D) [Faithful G] [Full G]
    (K : GrothendieckTopology D)
    (coverByImage_mem : ∀ U : D, Sieve.coverByImage G U ∈ K U) : G.IsCoverDense K where
  coverByImage_mem := coverByImage_mem
  functorPushforward_hasLift_mem f :=
    K.superset_covering (Sieve.coverByImage_le_hasLift G f) (coverByImage_mem _)
  functorPushforward_equalizer_mem f₁ f₂ e := by obtain rfl := G.map_injective e; simp

lemma Functor.isCoverDense_of_generate_singleton_functor_π_mem (G : C ⥤ D) [Full G] [Faithful G]
    (K : GrothendieckTopology D)
    (h : ∀ B, ∃ (X : C) (f : G.obj X ⟶ B), Sieve.generate (Presieve.singleton f) ∈ K B) :
    G.IsCoverDense K := by
  apply Functor.isCoverDense_of_full_of_faithful
  intro B
  obtain ⟨X, f, h⟩ := h B
  refine K.superset_covering ?_ h
  rintro Y f ⟨Z, g, _, ⟨⟩, w⟩
  exact ⟨⟨_, g, _, w⟩⟩

open Presieve Opposite

namespace Functor

namespace IsCoverDense

variable {K}
variable {A : Type*} [Category A] (G : C ⥤ D) [G.IsCoverDense K]

-- this is not marked with `@[ext]` because `H` can not be inferred from the type
theorem ext (ℱ : SheafOfTypes K) (X : D) {s t : ℱ.val.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op s = ℱ.val.map f.op t) : s = t := by
  apply (ℱ.cond (Sieve.coverByImage G X) (G.coverByImage_mem K X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]

theorem ext_of_hom (ℱ : SheafOfTypes K) {X Y : C} (i : G.obj X ⟶ G.obj Y)
    {s t : ℱ.val.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X) (f : Z ⟶ Y), G.map f = G.map j ≫ i →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (ℱ.cond _ (G.functorPushforward_hasLift_mem K i)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, ⟨iWY, e⟩, rfl⟩
  simp [h iWX iWY e]

theorem ext_of_hom_eq (ℱ : SheafOfTypes K) {X Y : C} (i₁ i₂ : X ⟶ Y) (e : G.map i₁ = G.map i₂)
    {s t : ℱ.val.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X), j ≫ i₁ = j ≫ i₂ →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (ℱ.cond _ (G.functorPushforward_equalizer_mem K i₁ i₂ e)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, hiWX, rfl⟩
  simp [h iWX hiWX]

variable {G}

theorem functorPullback_pushforward_covering {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X) := by
  let 𝒰 := Sieve.bind T.1.arrows fun Y _ _ ↦ Sieve.coverByImage G Y
  have : ∀ (Y) (f : Y ⟶ G.obj X), 𝒰 f → Exists _ :=
    fun _ _ h ↦ h
  choose Z iYZ iZX hiZX H e using this
  refine K.superset_covering ?_
    (K.bind_covering (K.bind_covering T.property fun Y _ _ ↦ G.coverByImage_mem _ _)
      fun Z f hf ↦ K.pullback_stable (H _ _ hf).some.lift
        (G.functorPushforward_hasLift_mem K ((H _ _ hf).some.map ≫ iZX _ _ _)))
  rintro Y _ ⟨W, iYW, iWX, hiWX : 𝒰 _, ⟨V, iVU, iYV, ⟨iVX, e₁⟩, e₂⟩, rfl⟩
  generalize Nonempty.some (H W iWX hiWX) = L at *
  obtain ⟨U, iWU, iUZ, e₃⟩ := L
  dsimp only at *
  dsimp only at iVU
  refine ⟨_, iVX, iYV, ?_, ?_⟩
  · have := T.1.downward_closed (hiZX W iWX hiWX) (G.map iVU ≫ iUZ)
    rwa [Category.assoc, ← e₁] at this
  · rw [e₁, ← reassoc_of% e₂, reassoc_of% e₃, e]

/-- (Implementation). Given a hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain a hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps!]
def homOver {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ ℱ ⋙ coyoneda.obj (op X) ⟶ G.op ⋙ (sheafOver ℱ' X).val :=
  whiskerRight α (coyoneda.obj (op X))

/-- (Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps!]
def isoOver {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ (sheafOver ℱ X).val ≅ G.op ⋙ (sheafOver ℱ' X).val :=
  isoWhiskerRight α (coyoneda.obj (op X))

theorem sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT)
    (x : FamilyOfElements _ T) (hx) (t) (h : x.IsAmalgamation t) :
    t = (ℱ.cond X T hT).amalgamate x hx :=
  (ℱ.cond X T hT).isSeparatedFor x t _ h ((ℱ.cond X T hT).isAmalgamation hx)

namespace Types

variable {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : SheafOfTypes.{v} K} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val)

theorem naturality_apply {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) :
    ℱ'.1.map i.op (α.app _ x) = α.app _ (ℱ.map i.op x) := by
  have {X Y} (i : X ⟶ Y) (x) :
      ℱ'.1.map (G.map i).op (α.app _ x) = α.app _ (ℱ.map (G.map i).op x) := by
    exact congr_fun (α.naturality i.op).symm x
  refine ext_of_hom G _ i fun V iVX iVY e ↦ ?_
  simp only [comp_obj, types_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← e, this]

@[reassoc]
theorem naturality {X Y : C} (i : G.obj X ⟶ G.obj Y) :
    α.app _ ≫ ℱ'.1.map i.op = ℱ.map i.op ≫ α.app _ := types_ext _ _ (naturality_apply α i)

/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
-- Porting note: removed `@[simp, nolint unused_arguments]`
noncomputable def pushforwardFamily {X} (x : ℱ.obj (op X)) :
    FamilyOfElements ℱ'.val (coverByImage G X) := fun _ _ hf =>
  ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x : _)

-- Porting note: there are various `include` and `omit`s in this file  (e.g. one is removed here),
-- none of which are needed in Lean 4.

-- Porting note: `pushforward_family` was tagged `@[simp]` in Lean 3 so we add the
-- equation lemma
@[simp] theorem pushforwardFamily_def {X} (x : ℱ.obj (op X)) :
    pushforwardFamily α x = fun _ _ hf =>
  ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x : _) := rfl

example {C} [Category C] {X : C} (f₁ f₂ f₃ f₄ : X ⟶ X) (hyp : f₂ ≫ f₃ = 𝟙 _) :
    f₁ ≫ f₂ ≫ f₃ ≫ f₄ = f₁ ≫ f₄ := by
  rw [reassoc_of% hyp]

/-- (Implementation). The `pushforwardFamily` defined is compatible. -/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) :
    (pushforwardFamily α x).Compatible := by
  have {X Y} (i : X ⟶ Y) (x) :
      ℱ'.1.map (G.map i).op (α.app _ x) = α.app _ (ℱ.map (G.map i).op x) := by
    exact congr_fun (α.naturality i.op).symm x
  suffices ∀ {Z W₁ W₂} (iWX₁ : G.obj W₁ ⟶ X) (iWX₂ : G.obj W₂ ⟶ X) (iZW₁ : Z ⟶ G.obj W₁)
      (iZW₂ : Z ⟶ G.obj W₂), iZW₁ ≫ iWX₁ = iZW₂ ≫ iWX₂ →
      ℱ'.1.map iZW₁.op (α.app _ (ℱ.map iWX₁.op x)) = ℱ'.1.map iZW₂.op (α.app _ (ℱ.map iWX₂.op x)) by
    rintro Y₁ Y₂ Z iZY₁ iZY₂ f₁ f₂ h₁ h₂ e
    simp only [pushforwardFamily, ← FunctorToTypes.map_comp_apply, ← op_comp]
    generalize Nonempty.some h₁ = l₁
    generalize Nonempty.some h₂ = l₂
    obtain ⟨W₁, iYW₁, iWX₁, rfl⟩ := l₁
    obtain ⟨W₂, iYW₂, iWX₂, rfl⟩ := l₂
    exact this _ _ _ _ (by simpa only [Category.assoc] using e)
  introv e
  refine ext G _ _ fun V iVZ ↦ ?_
  simp only [← op_comp, ← FunctorToTypes.map_comp_apply, ← Functor.map_comp, naturality_apply,
    Category.assoc, e]

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforwardFamily`. -/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := fun x =>
  (ℱ'.cond _ (G.coverByImage_mem _ X)).amalgamate (pushforwardFamily α x)
    (pushforwardFamily_compatible α x)

@[simp]
theorem pushforwardFamily_apply {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) := by
  simp only [pushforwardFamily_def, op_obj]
  generalize Nonempty.some (Presieve.in_coverByImage G f) = l
  obtain ⟨W, iYW, iWX, rfl⟩ := l
  simp only [← op_comp, ← FunctorToTypes.map_comp_apply, naturality_apply]

@[simp]
theorem appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
    ℱ'.val.map f (appHom α X x) = α.app (op Y) (ℱ.map f x) :=
  ((ℱ'.cond _ (G.coverByImage_mem _ X)).valid_glue
      (pushforwardFamily_compatible α x) f.unop
          (Presieve.in_coverByImage G f.unop)).trans (pushforwardFamily_apply _ _ _)

@[simp]
theorem appHom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
    appHom α X ≫ ℱ'.val.map f = ℱ.map f ≫ α.app (op Y) := by
  ext
  apply appHom_restrict

/--
(Implementation). The maps given in `appIso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps]
noncomputable def appIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val)
    (X : D) : ℱ.val.obj (op X) ≅ ℱ'.val.obj (op X) where
  hom := appHom i.hom X
  inv := appHom i.inv X
  hom_inv_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp
  inv_hom_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp

/-- Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types, where `G` is
cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation between sheaves.
-/
@[simps]
noncomputable def presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val where
  app X := appHom α (unop X)
  naturality X Y f := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y' f'
    simp only [appHom_restrict, types_comp_apply, ← FunctorToTypes.map_comp_apply]
    -- Porting note: Lean 3 proof continued with a rewrite but we're done here

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
noncomputable def presheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val :=
  NatIso.ofComponents (fun X => appIso i (unop X)) @(presheafHom i.hom).naturality

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is
cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between sheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ ≅ ℱ' where
  hom := ⟨(presheafIso i).hom⟩
  inv := ⟨(presheafIso i).inv⟩
  hom_inv_id := by
    ext1
    apply (presheafIso i).hom_inv_id
  inv_hom_id := by
    ext1
    apply (presheafIso i).inv_hom_id

end Types

open Types

variable {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps]
noncomputable def sheafCoyonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ ⟶
      coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ'.val where
  app X := presheafHom (homOver α (unop X))
  naturality X Y f := by
    ext U x
    change
      appHom (homOver α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ appHom (homOver α (unop X)) (unop U) x
    symm
    apply sheaf_eq_amalgamation
    · apply G.coverByImage_mem
    -- Porting note: the following line closes a goal which didn't exist before reenableeta
    · exact pushforwardFamily_compatible (homOver α Y.unop) (f.unop ≫ x)
    intro Y' f' hf'
    change unop X ⟶ ℱ.obj (op (unop _)) at x
    dsimp
    simp only [pushforwardFamily, Functor.comp_map, coyoneda_obj_map, homOver_app, Category.assoc]
    congr 1
    conv_lhs => rw [← hf'.some.fac]
    simp only [← Category.assoc, op_comp, Functor.map_comp]
    congr 1
    exact (appHom_restrict (homOver α (unop X)) hf'.some.map.op x).trans (by simp)

/--
(Implementation). `sheafCoyonedaHom` but the order of the arguments of the functor are swapped.
-/
noncomputable def sheafYonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    ℱ ⋙ yoneda ⟶ ℱ'.val ⋙ yoneda where
  app U :=
    let α := (sheafCoyonedaHom α)
    { app := fun X => (α.app X).app U
      naturality := fun X Y f => by simpa using congr_app (α.naturality f) U }
  naturality U V i := by
    ext X x
    exact congr_fun (((sheafCoyonedaHom α).app X).naturality i) x

/-- Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation
between presheaves.
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
  let α' := sheafYonedaHom α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using α'.naturality f) }

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
noncomputable def presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val := by
  have : ∀ X : Dᵒᵖ, IsIso ((sheafHom i.hom).app X) := by
    intro X
    -- Porting note: somehow `apply` in Lean 3 is leaving a typeclass goal,
    -- perhaps due to elaboration order. The corresponding `apply` in Lean 4 fails
    -- because the instance can't yet be synthesized. I hence reorder the proof.
    suffices IsIso (yoneda.map ((sheafHom i.hom).app X)) by
      apply isIso_of_reflects_iso _ yoneda
    use (sheafYonedaHom i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheafHom, NatTrans.comp_app, NatTrans.id_app, Functor.map_preimage]
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).hom_inv_id
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).inv_hom_id
    -- Porting note: Lean 4 proof is finished, Lean 3 needed `inferInstance`
  haveI : IsIso (sheafHom i.hom) := by apply NatIso.isIso_of_isIso_app
  apply asIso (sheafHom i.hom)

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ' where
  hom := ⟨(presheafIso i).hom⟩
  inv := ⟨(presheafIso i).inv⟩
  hom_inv_id := by
    ext1
    apply (presheafIso i).hom_inv_id
  inv_hom_id := by
    ext1
    apply (presheafIso i).inv_hom_id

theorem sheafHom_app (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (X) :
    (sheafHom α).app (op <| G.obj X) = α.app (op X) := by
  apply yoneda.map_injective
  ext U
  -- Porting note: didn't need to provide the input to `map_preimage` in Lean 3
  erw [yoneda.map_preimage ((sheafYonedaHom α).app (G.op.obj (op X)))]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.coverByImage_mem _ _) _ (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  simp only [pushforwardFamily, Functor.comp_map, yoneda_map_app, coyoneda_obj_map, op_comp,
    FunctorToTypes.map_comp_apply, homOver_app, ← Category.assoc]
  congr 1
  simp only [Category.assoc]
  congr 1
  have := naturality_apply (G := G) (ℱ := ℱ ⋙ coyoneda.obj (op <| (G.op ⋙ ℱ).obj (op X)))
    (ℱ' := ⟨_, ℱ'.2 ((G.op ⋙ ℱ).obj (op X))⟩) (whiskerRight α (coyoneda.obj _)) hf.some.map (𝟙 _)
  simpa using this

/-- The constructed `sheafHom α` is equal to `α` when restricted onto `C`.
-/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    whiskerLeft G.op (sheafHom α) = α := NatTrans.ext' (funext fun X ↦ sheafHom_app α (unop X))

variable (G)

/-- If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
theorem sheafHom_eq (α : ℱ ⟶ ℱ'.val) : sheafHom (whiskerLeft G.op α) = α := by
  ext X
  apply yoneda.map_injective
  -- Porting note: deleted next line as it's not needed in Lean 4
  ext U
  -- Porting note: Lean 3 didn't need to be told the explicit input to map_preimage
  erw [yoneda.map_preimage ((sheafYonedaHom (whiskerLeft G.op α)).app X)]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.coverByImage_mem _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp

@[reassoc]
theorem naturality {X Y : C} (ℱ) (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (i : G.obj X ⟶ G.obj Y) :
    α.app _ ≫ ℱ'.1.map i.op = ℱ.map i.op ≫ α.app _ := by
  rw [← sheafHom_app, ← sheafHom_app, NatTrans.naturality]

variable {G}

/-- A cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val) where
  toFun := sheafHom
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq
  right_inv := sheafHom_eq _

/-- Given a cover-dense functor `G` and a natural transformation of sheaves `α : ℱ ⟶ ℱ'`,
if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.val)) :
    IsIso α := by
  convert (sheafIso (asIso (whiskerLeft G.op α.val))).isIso_hom using 1
  ext1
  apply (sheafHom_eq _ _).symm

variable (G K)

/-- A faithful cover-dense functor preserves compatible families. -/
lemma compatiblePreserving : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply Functor.IsCoverDense.ext G
  intro W i
  refine ext_of_hom G _ (i ≫ f₁) fun V₁ iVW iV₁Y₁ e₁ ↦ ?_
  refine ext_of_hom G _ (G.map iVW ≫ i ≫ f₂) fun V₂ iV₂V₁ iV₂Y₂ e₂ ↦ ?_
  refine ext_of_hom_eq G _ (iV₂V₁ ≫ iV₁Y₁ ≫ g₁) (iV₂Y₂ ≫ g₂) (by simp [e₁, e₂, eq]) ?_
  intro V₃ iV₃ e₄
  simp only [← op_comp, ← FunctorToTypes.map_comp_apply, ← e₁, ← e₂, ← Functor.map_comp]
  apply hx
  simpa using e₄

lemma isContinuous (Hp : CoverPreserving J K G) : G.IsContinuous J K :=
  isContinuous_of_coverPreserving (compatiblePreserving K G) Hp

instance full_sheafPushforwardContinuous [G.IsContinuous J K] :
    Full (G.sheafPushforwardContinuous A J K) where
  map_surjective α := ⟨⟨sheafHom α.val⟩, Sheaf.Hom.ext _ _ <| sheafHom_restrict_eq α.val⟩

instance faithful_sheafPushforwardContinuous [G.IsContinuous J K] :
    Faithful (G.sheafPushforwardContinuous A J K) where
  map_injective := by
    intro ℱ ℱ' α β e
    ext1
    apply_fun fun e => e.val at e
    dsimp [sheafPushforwardContinuous] at e
    rw [← sheafHom_eq G α.val, ← sheafHom_eq G β.val, e]

end IsCoverDense

/-- If `G : C ⥤ D` is cover dense and full, then the
map `(P ⟶ Q) → (G.op ⋙ P ⟶ G.op ⋙ Q)` is bijective when `Q` is a sheaf`. -/
lemma whiskerLeft_obj_map_bijective_of_isCoverDense (G : C ⥤ D)
    [G.IsCoverDense K] {A : Type*} [Category A]
    (P Q : Dᵒᵖ ⥤ A) (hQ : Presheaf.IsSheaf K Q) :
    Function.Bijective (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map : (P ⟶ Q) → _) :=
  (IsCoverDense.restrictHomEquivHom (ℱ' := ⟨Q, hQ⟩)).symm.bijective

variable {A : Type*} [Category A]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)

/-- The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` if `G` is cover-dense
and `S` is a cover of `C` if and only if the image of `S` in `D` is a cover. -/
class IsDenseSubsite : Prop where
  isDense : G.IsCoverDense K
  functorPushforward_mem_iff : ∀ {X : C} {S : Sieve X}, S.functorPushforward G ∈ K _ ↔ S ∈ J _

namespace IsDenseSubsite

lemma isCoverDense [G.IsDenseSubsite J K] : G.IsCoverDense K := isDense J

lemma coverPreserving [G.IsDenseSubsite J K] : CoverPreserving J K G :=
  ⟨functorPushforward_mem_iff.mpr⟩

instance (priority := 900) [G.IsDenseSubsite J K] : G.IsContinuous J K :=
  letI := IsDenseSubsite.isCoverDense J K G
  IsCoverDense.isContinuous J K G (IsDenseSubsite.coverPreserving J K G)

instance (priority := 900) [G.IsDenseSubsite J K] : G.IsCocontinuous J K where
  cover_lift hS :=
    letI := IsDenseSubsite.isCoverDense J K G
    IsDenseSubsite.functorPushforward_mem_iff.mp
      (IsCoverDense.functorPullback_pushforward_covering ⟨_, hS⟩)

instance full_sheafPushforwardContinuous [G.IsDenseSubsite J K] :
    Full (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  inferInstance

instance faithful_sheafPushforwardContinuous [G.IsDenseSubsite J K] :
    Faithful (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  inferInstance

lemma hasLift_mem [G.IsDenseSubsite J K] {U V} (f : G.obj U ⟶ G.obj V) :
    Sieve.hasLift G f ∈ J _ :=
  letI := IsDenseSubsite.isCoverDense J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_hasLift_mem K f)

lemma equalizer_mem [G.IsDenseSubsite J K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
    Sieve.equalizer f₁ f₂ ∈ J _ :=
  letI := IsDenseSubsite.isCoverDense J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_equalizer_mem K f₁ f₂ e)

end IsDenseSubsite

end Functor

end CategoryTheory

namespace CategoryTheory.Functor.IsCoverDense

open CategoryTheory Opposite

universe w'
variable {C D : Type*} [Category C] [Category D]
variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {A : Type w} [Category.{w'} A] [∀ X, Limits.HasLimitsOfShape (StructuredArrow X G.op) A]
variable [G.IsDenseSubsite J K]

lemma isIso_ranCounit_app_of_isDenseSubsite (Y : Sheaf J A) (U X) :
    IsIso ((yoneda.map ((G.op.ranCounit.app Y.val).app (op U))).app (op X)) := by
  rw [isIso_iff_bijective]
  constructor
  · intro f₁ f₂ e
    apply (isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).hom_ext
    rintro ⟨⟨⟨⟩⟩, ⟨W⟩, g⟩
    obtain ⟨g, rfl⟩ : ∃ g' : G.obj W ⟶ G.obj U, g = g'.op := ⟨g.unop, rfl⟩
    simp only [id_obj, comp_obj, StructuredArrow.proj_obj, RightExtension.coneAt_pt,
      RightExtension.mk_left, RightExtension.coneAt_π_app, const_obj_obj, op_obj,
      whiskeringLeft_obj_obj, RightExtension.mk_hom]
    apply (Y.2 X _ (IsDenseSubsite.hasLift_mem J K G g)).isSeparatedFor.ext
    rintro V iVW ⟨iVU, e'⟩
    have := congr($e ≫ Y.1.map iVU.op)
    simp only [comp_obj, yoneda_map_app, Category.assoc, coyoneda_obj_obj, comp_map,
      coyoneda_obj_map, ← NatTrans.naturality, op_obj, op_map, Quiver.Hom.unop_op, ← map_comp_assoc,
      ← op_comp, ← e'] at this ⊢
    erw [← NatTrans.naturality] at this
    exact this
  · intro f
    have (X Y Z) (f : X ⟶ Y) (g : G.obj Y ⟶ G.obj Z) (hf : Sieve.hasLift G g f) : Exists _ := hf
    choose l hl using this
    let c : Limits.Cone (StructuredArrow.proj (op (G.obj U)) G.op ⋙ Y.val) := by
      refine ⟨X, ⟨fun g ↦ ?_, ?_⟩⟩
      · refine Y.2.amalgamate ⟨_, IsDenseSubsite.hasLift_mem J K G g.hom.unop⟩
          (fun I ↦ f ≫ Y.1.map (l _ _ _ _ _ I.hf).op) fun I₁ I₂ r ↦ ?_
        apply (Y.2 X _ (IsDenseSubsite.equalizer_mem J K G (r.g₁ ≫ l _ _ _ _ _ I₁.hf)
          (r.g₂ ≫ l _ _ _ _ _ I₂.hf) ?_)).isSeparatedFor.ext fun V iUV (hiUV : _ = _) ↦ ?_
        · simp only [const_obj_obj, op_obj, map_comp, hl]
          simp only [← map_comp_assoc, r.w]
        · simp [← map_comp, ← op_comp, hiUV]
      · rintro ⟨⟨⟨⟩⟩, ⟨W₁⟩, g₁⟩ ⟨⟨⟨⟩⟩, ⟨W₂⟩, g₂⟩ ⟨⟨⟨⟨⟩⟩⟩, i, hi⟩
        dsimp at g₁ g₂ i hi
        obtain rfl : g₂ = g₁ ≫ (G.map i.unop).op := by simpa only [Category.id_comp] using hi
        obtain ⟨g, rfl⟩ : ∃ g' : G.obj W₁ ⟶ G.obj U, g₁ = g'.op := ⟨g₁.unop, rfl⟩
        obtain ⟨i, rfl⟩ : ∃ i' : W₂ ⟶ W₁, i = i'.op := ⟨i.unop, rfl⟩
        simp only [const_obj_obj, id_obj, comp_obj, StructuredArrow.proj_obj, const_obj_map, op_obj,
          unop_comp, Quiver.Hom.unop_op, Category.id_comp, comp_map, StructuredArrow.proj_map]
        apply Y.2.hom_ext ⟨_, IsDenseSubsite.hasLift_mem J K G (G.map i ≫ g)⟩
        intro I
        simp only [Presheaf.IsSheaf.amalgamate_map, Category.assoc, ← Functor.map_comp, ← op_comp]
        let I' : GrothendieckTopology.Cover.Arrow ⟨_, IsDenseSubsite.hasLift_mem J K G g⟩ :=
          ⟨_, I.f ≫ i, ⟨l _ _ _ _ _ I.hf, by simp [hl]⟩⟩
        refine Eq.trans ?_ (Y.2.amalgamate_map _ _ _ I').symm
        apply (Y.2 X _ (IsDenseSubsite.equalizer_mem J K G (l _ _ _ _ _ I.hf)
          (l _ _ _ _ _ I'.hf) (by simp [hl]))).isSeparatedFor.ext fun V iUV (hiUV : _ = _) ↦ ?_
        simp [← Functor.map_comp, ← op_comp, hiUV]
    refine ⟨(isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).lift c, ?_⟩
    · have := (isPointwiseRightKanExtensionRanCounit G.op Y.1 (.op (G.obj U))).fac c (.mk (𝟙 _))
      simp only [id_obj, comp_obj, StructuredArrow.proj_obj, StructuredArrow.mk_right,
        RightExtension.coneAt_pt, RightExtension.mk_left, RightExtension.coneAt_π_app,
        const_obj_obj, op_obj, StructuredArrow.mk_hom_eq_self, map_id, whiskeringLeft_obj_obj,
        RightExtension.mk_hom, Category.id_comp, StructuredArrow.mk_left, unop_id] at this
      simp only [id_obj, yoneda_map_app, this]
      apply Y.2.hom_ext ⟨_, IsDenseSubsite.hasLift_mem J K G (𝟙 (G.obj U))⟩ _ _ fun I ↦ ?_
      apply (Y.2 X _ (IsDenseSubsite.equalizer_mem J K G (l _ _ _ _ _ I.hf)
        I.f (by simp [hl]))).isSeparatedFor.ext fun V iUV (hiUV : _ = _) ↦ ?_
      simp [← Functor.map_comp, ← op_comp, hiUV]

instance (Y : Sheaf J A) : IsIso ((G.sheafAdjunctionCocontinuous A J K).counit.app Y) := by
  apply (config := { allowSynthFailures := true })
    ReflectsIsomorphisms.reflects (sheafToPresheaf J A)
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro ⟨U⟩
  apply (config := { allowSynthFailures := true }) ReflectsIsomorphisms.reflects yoneda
  apply (config := { allowSynthFailures := true }) NatIso.isIso_of_isIso_app
  intro ⟨X⟩
  simp only [comp_obj, sheafToPresheaf_obj, sheafPushforwardContinuous_obj_val_obj, yoneda_obj_obj,
    id_obj, sheafToPresheaf_map, sheafAdjunctionCocontinuous_counit_app_val, ranAdjunction_counit]
  exact isIso_ranCounit_app_of_isDenseSubsite G J K Y U X

variable (A)

/-- Given a functor between small sites that is cover-dense, cover-preserving, and cover-lifting,
it induces an equivalence of category of sheaves valued in a complete category.
-/
@[simps! functor inverse]
noncomputable def sheafEquivOfCoverPreservingCoverLifting : Sheaf J A ≌ Sheaf K A :=
  (G.sheafAdjunctionCocontinuous A J K).toEquivalence.symm

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The natural isomorphism exhibiting the compatibility of
`sheafEquivOfCoverPreservingCoverLifting` with sheafification. -/
noncomputable
abbrev sheafEquivOfCoverPreservingCoverLiftingSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf _ _ ≅
      presheafToSheaf _ _ ⋙ (sheafEquivOfCoverPreservingCoverLifting G J K A).inverse := by
  apply Functor.pushforwardContinuousSheafificationCompatibility

end CategoryTheory.Functor.IsCoverDense
