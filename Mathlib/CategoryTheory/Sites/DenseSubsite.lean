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

We will primarily consider cover-dense functors that are also full, since this notion is in general
not well-behaved otherwise. Note that https://ncatlab.org/nlab/show/dense+sub-site indeed has a
weaker notion of cover-dense that loosens this requirement, but it would not have all the properties
we would need, and some sheafification would be needed for here and there.

## Main results

- `CategoryTheory.Functor.IsCoverDense.Types.presheafHom`: If `G : C ⥤ (D, K)` is full
  and cover-dense, then given any presheaf `ℱ` and sheaf `ℱ'` on `D`,
  and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`, we may glue them together to obtain
  a morphism of presheaves `ℱ ⟶ ℱ'`.
- `CategoryTheory.Functor.IsCoverDense.sheafIso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is full
  and cover-dense, then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`,
  then `α` is an iso if `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `CategoryTheory.Functor.IsCoverDense.sheafEquivOfCoverPreservingCoverLifting`:
  If `G : (C, J) ⥤ (D, K)` is fully-faithful, cover-lifting, cover-preserving, and cover-dense,
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

/--
For a functor `G : C ⥤ D`, and an morphism `U ⟶ G.obj V`,
`Sieve.coverByImageHom G f` is the sieve of `U`
consisting of those arrows that factor through images of arrows of `G`.
-/
def Sieve.coverByImageHom (G : C ⥤ D) {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve (G.obj U) where
  arrows Y i := ∃ (Y' : C) (lift : Y ⟶ G.obj Y') (fac₁ : Y' ⟶ V) (fac₂ : Y' ⟶ U),
    G.map fac₁ = G.map fac₂ ≫ f ∧ lift ≫ G.map fac₂ = i
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨Y'₁, lift₁, fac₁, fac₂, e₁, rfl⟩ i₂
    refine ⟨_, _, _, fac₂, e₁, Category.assoc _ _ _⟩

lemma Sieve.coverByImageHom_le (G : C ⥤ D) [G.Full] {U V : C} (f : G.obj U ⟶ G.obj V) :
    coverByImage G _ ≤ coverByImageHom G f := by
  rintro W g ⟨Z, lift, fac, e⟩
  exact ⟨Z, lift, G.preimage (fac ≫ f), G.preimage fac,
    by rw [G.map_preimage, G.map_preimage], by rw [G.map_preimage, e]⟩

theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩

/-- A functor `G : (C, J) ⥤ (D, K)` is cover dense if for each object and arrows in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
class Functor.IsCoverDense (G : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  coverByImage_mem : ∀ U : D, Sieve.coverByImage G U ∈ K U
  coverByImageHom_mem : ∀ {U V} (f : G.obj U ⟶ G.obj V), Sieve.coverByImageHom G f ∈ K _

lemma Functor.coverByImage_mem (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] (U : D) : Sieve.coverByImage G U ∈ K U :=
  Functor.IsCoverDense.coverByImage_mem _

lemma Functor.coverByImageHom_mem (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] {U V} (f : G.obj U ⟶ G.obj V) : Sieve.coverByImageHom G f ∈ K _ :=
  Functor.IsCoverDense.coverByImageHom_mem _

lemma Functor.isCoverDense_of_full (G : C ⥤ D)
    [Full G]
    (K : GrothendieckTopology D)
    (coverByImage_mem : ∀ U : D, Sieve.coverByImage G U ∈ K U) : G.IsCoverDense K where
  coverByImage_mem := coverByImage_mem
  coverByImageHom_mem f :=
    K.superset_covering (Sieve.coverByImageHom_le G f) (coverByImage_mem _)

lemma Functor.isCoverDense_of_generate_singleton_functor_π_mem (G : C ⥤ D)
    [Full G]
    (K : GrothendieckTopology D)
    (h : ∀ B, ∃ (X : C) (f : G.obj X ⟶ B), Sieve.generate (Presieve.singleton f) ∈ K B) :
    G.IsCoverDense K := by
  apply Functor.isCoverDense_of_full
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
        (G.coverByImageHom_mem K ((H _ _ hf).some.map ≫ iZX _ _ _)))
  rintro Y _ ⟨W, iYW, iWX, hiWX : 𝒰 _, ⟨V, iYV, iVX, iVU, e₁, e₂⟩, rfl⟩
  generalize Nonempty.some (H W iWX hiWX) = L at *
  obtain ⟨U, iWU, iUZ, e₃⟩ := L
  dsimp only at *
  dsimp only at iVU
  refine ⟨_, iVX, iYV, ?_, ?_⟩
  · have := T.1.downward_closed (hiZX W iWX hiWX) (G.map iVU ≫ iUZ)
    rwa [Category.assoc, ← e₁] at this
  · rw [e₁, reassoc_of% e₂, reassoc_of% e₃, e]

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

/-- (Implementation). The `pushforwardFamily` defined is compatible. -/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) :
    (pushforwardFamily α x).Compatible := by
  rintro Y₁ Y₂ Z iZY₁ iZY₂ f₁ f₂ h₁ h₂ e
  simp only [pushforwardFamily, ← FunctorToTypes.map_comp_apply, ← op_comp]
  generalize Nonempty.some h₁ = l₁
  generalize Nonempty.some h₂ = l₂
  obtain ⟨W₁, iYW₁, iWX₁, rfl⟩ := l₁
  obtain ⟨W₂, iYW₂, iWX₂, rfl⟩ := l₂
  dsimp only
  simp_rw [← Category.assoc] at e
  generalize iZY₁ ≫ iYW₁ = iZW₁ at e ⊢
  generalize iZY₂ ≫ iYW₂ = iZW₂ at e ⊢
  clear iZY₁ iYW₁ iZY₂ iYW₂ h₁ h₂ Y₁ Y₂
  apply (ℱ'.2 _ (G.coverByImage_mem _ _)).isSeparatedFor.ext
  rintro Y iYZ ⟨V, iYV, iVZ, rfl⟩
  simp only [op_comp, FunctorToTypes.map_comp_apply]
  congr 1
  apply (ℱ'.2 _ (G.coverByImage_mem _ _)).isSeparatedFor.ext


  apply (ℱ'.2 _ (K.intersection_covering (G.coverByImageHom_mem _ (g₁ ≫ l₁.lift))
    (G.coverByImageHom_mem _ (g₂ ≫ l₂.lift)))).isSeparatedFor.ext
  rintro Y iYZ ⟨⟨U, iYU, iU₁, iUZ, e₁, rfl⟩, ⟨V, iYV, iV₂, iVZ, e₂, e₃⟩⟩
  change (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ ≫ ℱ'.val.map _) _ =
    (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ ≫ ℱ'.val.map _) _
  simp_rw [← Functor.map_comp, ← op_comp, Category.assoc]
  rw [← e₁, ← reassoc_of% e₃, ← e₂]
  simp_rw [op_comp, Functor.map_comp]
  rw [← iU₁.unop_op, ← iV₂.unop_op]
  simp_rw [← G.op_map, ← Functor.comp_map, ← α.naturality_assoc]
  simp only [Functor.comp_map, G.op_map, Quiver.Hom.unop_op, ← Functor.map_comp_assoc, ← op_comp, e₁, e₂,
    Category.assoc, Presieve.CoverByImageStructure.fac, e]
  -- rw [← G.map_preimage (f ≫ g₁ ≫ _)]
  -- rw [← G.map_preimage (f ≫ g₂ ≫ _)]
  -- erw [← α.naturality (G.preimage _).op]
  -- erw [← α.naturality (G.preimage _).op]
  -- refine congr_fun ?_ x
  -- simp only [Functor.comp_map, ← Category.assoc, Functor.op_map, Quiver.Hom.unop_op,
  --   ← ℱ.map_comp, ← op_comp, G.map_preimage]
  -- congr 3
  -- simp [e]

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforwardFamily`. -/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := fun x =>
  (ℱ'.cond _ (G.coverByImage_mem _ X)).amalgamate (pushforwardFamily α x)
    (pushforwardFamily_compatible α x)

@[simp]
theorem pushforwardFamily_apply {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) := by
  unfold pushforwardFamily
  -- Porting note: congr_fun was more powerful in Lean 3; I had to explicitly supply
  -- the type of the first input here even though it's obvious (there is a unique occurrence
  -- of x on each side of the equality)
  refine congr_fun (?_ :
    (fun t => ℱ'.val.map ((Nonempty.some (_ : coverByImage G X f)).lift.op)
      (α.app (op (Nonempty.some (_ : coverByImage G X f)).1)
        (ℱ.map ((Nonempty.some (_ : coverByImage G X f)).map.op) t))) =
    (fun t => α.app (op Y) (ℱ.map (f.op) t))) x
  rw [← G.map_preimage (Nonempty.some _ : Presieve.CoverByImageStructure _ _).lift]
  change ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ = ℱ.map f.op ≫ α.app (op Y)
  erw [← α.naturality (G.preimage _).op]
  simp only [← Functor.map_comp, ← Category.assoc, Functor.comp_map, G.map_preimage, G.op_map,
    Quiver.Hom.unop_op, ← op_comp, Presieve.CoverByImageStructure.fac]

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
full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation between sheaves.
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

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
noncomputable def presheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val :=
  NatIso.ofComponents (fun X => appIso i (unop X)) @(presheafHom i.hom).naturality

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between sheaves.
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
    · apply G.is_cover_of_isCoverDense
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
where `G` is full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation
between presheaves.
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
  let α' := sheafYonedaHom α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using α'.naturality f) }

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
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
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
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

/-- The constructed `sheafHom α` is equal to `α` when restricted onto `C`.
-/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    whiskerLeft G.op (sheafHom α) = α := by
  ext X
  apply yoneda.map_injective
  ext U
  -- Porting note: didn't need to provide the input to `map_preimage` in Lean 3
  erw [yoneda.map_preimage ((sheafYonedaHom α).app (G.op.obj X))]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  simp only [pushforwardFamily, Functor.comp_map, yoneda_map_app, coyoneda_obj_map, op_comp,
    FunctorToTypes.map_comp_apply, homOver_app, ← Category.assoc]
  congr 1
  simp only [Category.assoc]
  congr 1
  rw [← G.map_preimage hf.some.map]
  symm
  apply α.naturality (G.preimage hf.some.map).op
  -- porting note; Lean 3 needed a random `inferInstance` for cleanup here; not necessary in lean 4

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
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp

variable {G}

/-- A full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val) where
  toFun := sheafHom
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq
  right_inv := sheafHom_eq _

/-- Given a full and cover-dense functor `G` and a natural transformation of sheaves `α : ℱ ⟶ ℱ'`,
if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.val)) :
    IsIso α := by
  convert (sheafIso (asIso (whiskerLeft G.op α.val))).isIso_hom using 1
  ext1
  apply (sheafHom_eq _ _).symm

variable (G K)

/-- A fully faithful cover-dense functor preserves compatible families. -/
lemma compatiblePreserving [Faithful G] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply Functor.IsCoverDense.ext G
  intro W i
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  rw [← G.map_preimage (i ≫ f₁)]
  rw [← G.map_preimage (i ≫ f₂)]
  apply hx (G.preimage (i ≫ f₁)) ((G.preimage (i ≫ f₂))) hg₁ hg₂
  apply G.map_injective
  simp [eq]

lemma compatiblePreserving' (hG : CoverPreserving J K G) [Faithful G] :
    CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  -- apply Functor.IsCoverDense.ext G
  -- intro W i
  have := K.intersection_covering (K.pullback_stable f₁ (hG.1 (J.top_mem Y₁)))
    (K.pullback_stable f₂ (hG.1 (J.top_mem Y₂)))
  apply (ℱ.2 _ this).isSeparatedFor.ext
  rintro W i ⟨⟨W₁, i₁, j₁, -, e₁⟩, ⟨W₂, i₂, j₂, -, e₂⟩⟩
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp_rw [e₁, e₂, op_comp, FunctorToTypes.map_comp_apply]
  apply hx i₁ i₂ hg₁ hg₂
  apply G.map_injective
  simp [eq]

lemma isContinuous [Faithful G] (Hp : CoverPreserving J K G) : G.IsContinuous J K :=
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
    [G.IsCoverDense K] [G.Full] {A : Type*} [Category A]
    (P Q : Dᵒᵖ ⥤ A) (hQ : Presheaf.IsSheaf K Q) :
    Function.Bijective (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map : (P ⟶ Q) → _) :=
  (IsCoverDense.restrictHomEquivHom (ℱ' := ⟨Q, hQ⟩)).symm.bijective

end Functor

end CategoryTheory

namespace CategoryTheory.Functor.IsCoverDense

open CategoryTheory

universe w'
variable {C D : Type*} [Category C] [Category D]
variable (G : C ⥤ D) [Full G] [Faithful G]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {A : Type w} [Category.{w'} A] [∀ X, Limits.HasLimitsOfShape (StructuredArrow X G.op) A]
variable [G.IsCoverDense K] [G.IsContinuous J K] [G.IsCocontinuous J K]

instance (Y : Sheaf J A) : IsIso ((G.sheafAdjunctionCocontinuous A J K).counit.app Y) := by
    haveI : IsIso ((sheafToPresheaf J A).map
        ((G.sheafAdjunctionCocontinuous A J K).counit.app Y)) := by
      dsimp
      rw [sheafAdjunctionCocontinuous_counit_app_val]
      infer_instance
    apply ReflectsIsomorphisms.reflects (sheafToPresheaf J A)

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
