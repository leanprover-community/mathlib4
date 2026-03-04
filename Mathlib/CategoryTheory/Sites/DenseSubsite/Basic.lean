/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful

/-!
# Dense subsites

We define `IsCoverDense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

## Main results

- `CategoryTheory.Functor.IsCoverDense.Types.presheafHom`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any presheaf `ℱ` and sheaf `ℱ'` on `D`,
  and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`, we may glue them together to obtain
  a morphism of presheaves `ℱ ⟶ ℱ'`.
- `CategoryTheory.Functor.IsCoverDense.sheafIso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`,
  then `α` is an iso if `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `CategoryTheory.Functor.IsDenseSubsite`:
  The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` if `G` is cover-dense,
  locally fully-faithful, and `S` is a cover of `C` iff the image of `S` in `D` is a cover.
- `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`: the equivalence of
  categories `Sheaf J A ≌ Sheaf K A` when `(C, J)` is a dense subsite of `(D, K)` and
  the pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, which we show
  in two situations:
  * the sites are small and `A` has suitable limits (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/SheafEquiv.lean`).
  * the category `A` has limits of size `w` and `G` is `1`-hypercover cover dense
    relatively to the universe `w` (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/OneHypercoverDense.lean`).

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/-- An auxiliary structure that witnesses the fact that `f` factors through an image object of `G`.
-/
structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by cat_disch
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

/-- A functor `G : (C, J) ⥤ (D, K)` is cover dense if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
class Functor.IsCoverDense (G : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  is_cover : ∀ U : D, Sieve.coverByImage G U ∈ K U

lemma Functor.is_cover_of_isCoverDense (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] (U : D) : Sieve.coverByImage G U ∈ K U := by
  apply Functor.IsCoverDense.is_cover

lemma Functor.isCoverDense_of_generate_singleton_functor_π_mem (G : C ⥤ D)
    (K : GrothendieckTopology D)
    (h : ∀ B, ∃ (X : C) (f : G.obj X ⟶ B), Sieve.generate (Presieve.singleton f) ∈ K B) :
    G.IsCoverDense K where
  is_cover B := by
    obtain ⟨X, f, h⟩ := h B
    refine K.superset_covering ?_ h
    intro Y f ⟨Z, g, _, h, w⟩
    cases h
    exact ⟨⟨_, g, _, w⟩⟩

attribute [nolint docBlame] CategoryTheory.Functor.IsCoverDense.is_cover

open Presieve Opposite

namespace Functor

namespace IsCoverDense

variable {K}
variable {A : Type*} [Category* A] (G : C ⥤ D)

-- this is not marked with `@[ext]` because `H` cannot be inferred from the type
theorem ext [G.IsCoverDense K] (ℱ : Sheaf K (Type _)) (X : D) {s t : ℱ.val.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op s = ℱ.val.map f.op t) : s = t := by
  apply ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.cond
    (Sieve.coverByImage G X) (G.is_cover_of_isCoverDense K X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]

variable {G}

theorem functorPullback_pushforward_covering [G.IsCoverDense K] [G.IsLocallyFull K] {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X) := by
  refine K.transitive T.2 _ fun Y iYX hiYX ↦ ?_
  apply K.transitive (G.is_cover_of_isCoverDense _ _) _
  rintro W _ ⟨Z, iWZ, iZY, rfl⟩
  rw [Sieve.pullback_comp]; apply K.pullback_stable; clear W iWZ
  apply K.superset_covering ?_ (G.functorPushforward_imageSieve_mem _ (iZY ≫ iYX))
  rintro W _ ⟨V, iVZ, iWV, ⟨iVX, e⟩, rfl⟩
  exact ⟨_, iVX, iWV, by simpa [e] using T.1.downward_closed hiYX (G.map iVZ ≫ iZY), by simp [e]⟩

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

variable {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : Sheaf K (Type v)} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val)

theorem naturality_apply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) :
    ℱ'.1.map i.op (α.app _ x) = α.app _ (ℱ.map i.op x) := by
  have {X Y} (i : X ⟶ Y) (x) :
      ℱ'.1.map (G.map i).op (α.app _ x) = α.app _ (ℱ.map (G.map i).op x) := by
    exact congr_fun (α.naturality i.op).symm x
  refine IsLocallyFull.ext G _ i fun V iVX iVY e ↦ ?_
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, ← e, this]

@[reassoc]
theorem naturality [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) :
    α.app _ ≫ ℱ'.1.map i.op = ℱ.map i.op ≫ α.app _ := types_ext _ _ (naturality_apply α i)

/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
noncomputable def pushforwardFamily {X} (x : ℱ.obj (op X)) :
    FamilyOfElements ℱ'.val (coverByImage G X) := fun _ _ hf =>
  ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x)

@[simp] theorem pushforwardFamily_def {X} (x : ℱ.obj (op X)) :
    pushforwardFamily α x = fun _ _ hf =>
    ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x) := rfl

@[simp]
theorem pushforwardFamily_apply [G.IsLocallyFull K]
    {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) := by
  simp only [pushforwardFamily_def, op_obj]
  generalize Nonempty.some (Presieve.in_coverByImage G f) = l
  obtain ⟨W, iYW, iWX, rfl⟩ := l
  simp only [← op_comp, ← FunctorToTypes.map_comp_apply, naturality_apply]

variable [G.IsCoverDense K] [G.IsLocallyFull K]

/-- (Implementation). The `pushforwardFamily` defined is compatible. -/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) :
    (pushforwardFamily α x).Compatible := by
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
  simp only [← op_comp, ← FunctorToTypes.map_comp_apply, naturality_apply,
    Category.assoc, e]

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforwardFamily`. -/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := fun x =>
  ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.cond _
    (G.is_cover_of_isCoverDense _ X)).amalgamate (pushforwardFamily α x)
      (pushforwardFamily_compatible α x)

@[simp]
theorem appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
    ℱ'.val.map f (appHom α X x) = α.app (op Y) (ℱ.map f x) :=
  (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.cond _ (G.is_cover_of_isCoverDense _ X)).valid_glue
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
noncomputable def appIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val)
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

/--
Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ'` is a sheaf,
we may obtain a natural transformation between sheaves.
-/
@[simps]
noncomputable def presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val where
  app X := appHom α (unop X)
  naturality X Y f := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y' f'
    simp only [appHom_restrict, types_comp_apply, ← FunctorToTypes.map_comp_apply]

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
noncomputable def presheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val :=
  NatIso.ofComponents (fun X => appIso i (unop X)) @(presheafHom i.hom).naturality

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between sheaves.
-/
@[simps! hom_val inv_val]
noncomputable def sheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ ≅ ℱ' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

end Types

open Types

variable [G.IsCoverDense K] [G.IsLocallyFull K] {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

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
    simp only [Category.assoc]
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

/--
Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural
transformation between presheaves.
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
  let α' := sheafYonedaHom α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using α'.naturality f) }

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
noncomputable def presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val := by
  have : ∀ X : Dᵒᵖ, IsIso ((sheafHom i.hom).app X) := by
    intro X
    rw [← isIso_iff_of_reflects_iso _ yoneda]
    use (sheafYonedaHom i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheafHom, NatTrans.comp_app, NatTrans.id_app, Functor.map_preimage]
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).hom_inv_id
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).inv_hom_id
  haveI : IsIso (sheafHom i.hom) := by apply NatIso.isIso_of_isIso_app
  apply asIso (sheafHom i.hom)

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps! hom_val inv_val]
noncomputable def sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

set_option backward.isDefEq.respectTransparency false in
/-- The constructed `sheafHom α` is equal to `α` when restricted onto `C`. -/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    whiskerLeft G.op (sheafHom α) = α := by
  ext X
  apply yoneda.map_injective
  ext U
  erw [yoneda.map_preimage]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  simp only [pushforwardFamily, Functor.comp_map, yoneda_map_app, flip_obj_map, op_comp,
    FunctorToTypes.map_comp_apply, homOver_app]
  congr 1
  simp only [Category.assoc]
  congr 1
  have := naturality_apply (G := G) (ℱ := ℱ ⋙ coyoneda.obj (op <| (G.op ⋙ ℱ).obj X))
    (ℱ' := ⟨_, Presheaf.isSheaf_comp_of_isSheaf K ℱ'.val
      (coyoneda.obj (op ((G.op ⋙ ℱ).obj X))) ℱ'.cond⟩)
    (whiskerRight α (coyoneda.obj _)) hf.some.map (𝟙 _)
  simpa using this

variable (G) in
/--
If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
theorem sheafHom_eq (α : ℱ ⟶ ℱ'.val) : sheafHom (whiskerLeft G.op α) = α := by
  ext X
  apply yoneda.map_injective
  ext U
  erw [yoneda.map_preimage]
  symm
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp; simp

/--
A locally-full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val) where
  toFun := sheafHom
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq
  right_inv := sheafHom_eq _

@[reassoc]
lemma restrictHomEquivHom_naturality_right_symm
    (f : ℱ ⟶ ℱ'.val) {𝒢'} (g : ℱ' ⟶ 𝒢') :
    (restrictHomEquivHom (G := G)).symm (f ≫ g.val) =
      restrictHomEquivHom.symm f ≫ whiskerLeft _ g.val := rfl

@[reassoc]
lemma restrictHomEquivHom_naturality_right
    (f : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) {𝒢'} (g : ℱ' ⟶ 𝒢') :
    restrictHomEquivHom (f ≫ whiskerLeft G.op g.val) =
      restrictHomEquivHom f ≫ g.val := by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_right_symm (G := G) (restrictHomEquivHom f) g).symm

@[reassoc]
lemma restrictHomEquivHom_naturality_left_symm
    {𝒢} (f : 𝒢 ⟶ ℱ) (g : ℱ ⟶ ℱ'.val) :
    (restrictHomEquivHom (G := G)).symm (f ≫ g) =
      whiskerLeft G.op f ≫ restrictHomEquivHom.symm g := rfl

@[reassoc]
lemma restrictHomEquivHom_naturality_left
    {𝒢} (f : 𝒢 ⟶ ℱ) (g : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    restrictHomEquivHom (whiskerLeft _ f ≫ g) =
      f ≫ restrictHomEquivHom g := by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_left_symm (G := G) (f := f)
      (g := restrictHomEquivHom g)).symm

/-- Given a locally-full and cover-dense functor `G` and a natural transformation of sheaves
`α : ℱ ⟶ ℱ'`, if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.val)) :
    IsIso α := by
  convert (sheafIso (asIso (whiskerLeft G.op α.val))).isIso_hom using 1
  ext1
  apply (sheafHom_eq _ _).symm

variable (G K)

/-- A locally-fully-faithful and cover-dense functor preserves compatible families. -/
lemma compatiblePreserving [G.IsLocallyFaithful K] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply Functor.IsCoverDense.ext G
  intro W i
  refine IsLocallyFull.ext G _ (i ≫ f₁) fun V₁ iVW iV₁Y₁ e₁ ↦ ?_
  refine IsLocallyFull.ext G _ (G.map iVW ≫ i ≫ f₂) fun V₂ iV₂V₁ iV₂Y₂ e₂ ↦ ?_
  refine IsLocallyFaithful.ext G _ (iV₂V₁ ≫ iV₁Y₁ ≫ g₁) (iV₂Y₂ ≫ g₂) (by simp [e₁, e₂, eq]) ?_
  intro V₃ iV₃ e₄
  simp only [← op_comp, ← FunctorToTypes.map_comp_apply, ← e₁, ← e₂, ← Functor.map_comp]
  apply hx
  simpa using e₄

lemma isContinuous [G.IsLocallyFaithful K] (Hp : CoverPreserving J K G) : G.IsContinuous J K :=
  isContinuous_of_coverPreserving (compatiblePreserving K G) Hp

instance full_sheafPushforwardContinuous [G.IsContinuous J K] :
    Full (G.sheafPushforwardContinuous A J K) where
  map_surjective α := ⟨⟨sheafHom α.val⟩, Sheaf.Hom.ext <| sheafHom_restrict_eq α.val⟩

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
map `(P ⟶ Q) → (G.op ⋙ P ⟶ G.op ⋙ Q)` is bijective when `Q` is a sheaf. -/
lemma whiskerLeft_obj_map_bijective_of_isCoverDense (G : C ⥤ D)
    [G.IsCoverDense K] [G.IsLocallyFull K] {A : Type*} [Category* A]
    (P Q : Dᵒᵖ ⥤ A) (hQ : Presheaf.IsSheaf K Q) :
    Function.Bijective (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map : (P ⟶ Q) → _) :=
  (IsCoverDense.restrictHomEquivHom (ℱ' := ⟨Q, hQ⟩)).symm.bijective

variable (G : C ⥤ D) {A : Type*} [Category* A]

/-- The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`
if `G` is cover-dense, locally fully-faithful,
and `S` is a cover of `C` if and only if the image of `S` in `D` is a cover. -/
class IsDenseSubsite : Prop where
  isCoverDense' : G.IsCoverDense K := by infer_instance
  isLocallyFull' : G.IsLocallyFull K := by infer_instance
  isLocallyFaithful' : G.IsLocallyFaithful K := by infer_instance
  functorPushforward_mem_iff : ∀ {X : C} {S : Sieve X}, S.functorPushforward G ∈ K _ ↔ S ∈ J _

lemma functorPushforward_mem_iff {X : C} {S : Sieve X} [G.IsDenseSubsite J K] :
    S.functorPushforward G ∈ K _ ↔ S ∈ J _ := IsDenseSubsite.functorPushforward_mem_iff

namespace IsDenseSubsite

variable [G.IsDenseSubsite J K]

include J K

lemma isCoverDense : G.IsCoverDense K := isCoverDense' J
lemma isLocallyFull : G.IsLocallyFull K := isLocallyFull' J
lemma isLocallyFaithful : G.IsLocallyFaithful K := isLocallyFaithful' J

lemma coverPreserving : CoverPreserving J K G :=
  ⟨functorPushforward_mem_iff.mpr⟩

instance (priority := 900) : G.IsContinuous J K :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  letI := IsDenseSubsite.isLocallyFaithful J K G
  IsCoverDense.isContinuous J K G (IsDenseSubsite.coverPreserving J K G)

instance (priority := 900) : G.IsCocontinuous J K where
  cover_lift hS :=
    letI := IsDenseSubsite.isCoverDense J K G
    letI := IsDenseSubsite.isLocallyFull J K G
    IsDenseSubsite.functorPushforward_mem_iff.mp
      (IsCoverDense.functorPullback_pushforward_covering ⟨_, hS⟩)

instance full_sheafPushforwardContinuous :
    Full (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

instance faithful_sheafPushforwardContinuous :
    Faithful (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance

lemma imageSieve_mem {U V} (f : G.obj U ⟶ G.obj V) :
    G.imageSieve f ∈ J _ :=
  letI := IsDenseSubsite.isLocallyFull J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_imageSieve_mem K f)

lemma equalizer_mem {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
    Sieve.equalizer f₁ f₂ ∈ J _ :=
  letI := IsDenseSubsite.isLocallyFaithful J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_equalizer_mem K f₁ f₂ e)

variable {J} (F : Sheaf J A)

lemma map_eq_of_eq {X Y : C} (f₁ f₂ : X ⟶ Y)
    (h : G.map f₁ = G.map f₂) :
    F.val.map f₁.op = F.val.map f₂.op :=
  Presheaf.IsSheaf.hom_ext F.cond
    ⟨_, IsDenseSubsite.equalizer_mem J K G _ _ h⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      simp only [← Functor.map_comp, ← op_comp, ha])

/-- If `G : C ⥤ D` is a dense subsite and `F` a sheaf on `C`, this is the morphism
`F.val.obj (op Y) ⟶ F.val.obj (op X)` induced by a morphism
`G.obj X ⟶ G.obj Y` in the category `D`. -/
noncomputable def mapPreimage {X Y : C} (f : G.obj X ⟶ G.obj Y) :
    F.val.obj (op Y) ⟶ F.val.obj (op X) :=
  F.cond.amalgamate
    ⟨_, imageSieve_mem J K G f⟩ (fun ⟨W₀, a, ha⟩ ↦ F.val.map ha.choose.op) (by
      rintro ⟨W₀, a, ha⟩ ⟨W₀', a', ha'⟩ ⟨T₀, p₁, p₂, fac⟩
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
      apply map_eq_of_eq K G
      rw [Functor.map_comp, Functor.map_comp, ha.choose_spec, ha'.choose_spec,
        ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, fac])

lemma mapPreimage_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (p : Z ⟶ X) (g : Z ⟶ Y) (fac : G.map p ≫ f = G.map g) :
    mapPreimage K G F f ≫ F.val.map p.op = F.val.map g.op :=
  Presheaf.IsSheaf.hom_ext F.cond
    ⟨_, J.pullback_stable p (imageSieve_mem J K G f)⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      rw [Category.assoc, ← Functor.map_comp, ← op_comp, mapPreimage]
      rw [F.2.amalgamate_map ⟨_, imageSieve_mem J K G f⟩
        (fun ⟨W₀, a, ha⟩ ↦ F.val.map ha.choose.op) _ ⟨W₀, a ≫ p, ha⟩,
        ← Functor.map_comp, ← op_comp]
      apply map_eq_of_eq K G
      rw [ha.choose_spec, Functor.map_comp_assoc, Functor.map_comp, fac])

lemma mapPreimage_of_eq {X Y : C} (f : G.obj X ⟶ G.obj Y)
    (g : X ⟶ Y) (h : G.map g = f) :
    mapPreimage K G F f = F.val.map g.op := by
  simpa using mapPreimage_map_of_fac K G F f (𝟙 _) g (by simpa using h.symm)

@[simp]
lemma mapPreimage_map {X Y : C} (f : X ⟶ Y) :
    mapPreimage K G F (G.map f) = F.val.map f.op :=
  mapPreimage_of_eq K G F (G.map f) f rfl

@[simp]
lemma mapPreimage_id (X : C) :
    mapPreimage K G F (𝟙 (G.obj X)) = 𝟙 _ := by
  rw [← G.map_id, mapPreimage_map, op_id, map_id]

@[reassoc]
lemma mapPreimage_comp {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (g : G.obj Y ⟶ G.obj Z) :
    mapPreimage K G F (f ≫ g) = mapPreimage K G F g ≫ mapPreimage K G F f :=
  Presheaf.IsSheaf.hom_ext F.cond
    ⟨_, imageSieve_mem J K G f⟩ _ _ (by
      rintro ⟨T₀, a, ⟨b, fac₁⟩⟩
      apply Presheaf.IsSheaf.hom_ext F.cond
        ⟨_, J.pullback_stable b (imageSieve_mem J K G g)⟩
      rintro ⟨U₀, c, ⟨d, fac₂⟩⟩
      dsimp
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
      rw [mapPreimage_map_of_fac K G F (f ≫ g) (c ≫ a) d,
        mapPreimage_map_of_fac K G F f (c ≫ a) (c ≫ b),
        mapPreimage_map_of_fac K G F g (c ≫ b) d]
      all_goals
        simp only [Functor.map_comp, Category.assoc, fac₁, fac₂])

@[reassoc]
lemma mapPreimage_comp_map {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (g : Z ⟶ X) :
    mapPreimage K G F f ≫ F.val.map g.op =
      mapPreimage K G F (G.map g ≫ f) := by
  rw [mapPreimage_comp, mapPreimage_map]

section

variable (J) [IsEquivalence (sheafPushforwardContinuous G A J K)]

section

variable [HasWeakSheafify J A]

variable (A) in
/-- Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`)
and `sheafPushforwardContinuous G A J₀ J` is an equivalence of categories
this is a sheafification functor `(Dᵒᵖ ⥤ A) ⥤ Sheaf K A`
when `HasWeakSheafify J A` holds. -/
noncomputable def sheafifyOfIsEquivalence
    [IsEquivalence (sheafPushforwardContinuous G A J K)] :
    (Dᵒᵖ ⥤ A) ⥤ Sheaf K A :=
  (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A ⋙
    inv (G.sheafPushforwardContinuous A J K)

variable (A) in
/-- Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`)
and `sheafPushforwardContinuous G A J₀ J` is an equivalence of categories, this is
the isomorphism between `sheafifyOfIsEquivalence J K G A ⋙ G.sheafPushforwardContinuous A J K`
and the functor which sends a presheaf to the sheafification of its precomposition by `G.op`. -/
noncomputable def sheafifyOfIsEquivalenceCompIso
    [IsEquivalence (sheafPushforwardContinuous G A J K)] :
    sheafifyOfIsEquivalence J K G A ⋙ G.sheafPushforwardContinuous A J K ≅
      (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (sheafPushforwardContinuous G A J K).asEquivalence.counitIso ≪≫ Functor.rightUnitor _)

/-- Auxiliary definition for `sheafifyAdjunctionOfIsEquivalence`. -/
noncomputable def sheafifyHomEquivOfIsEquivalence
    {P : Dᵒᵖ ⥤ A} {Q : Sheaf K A} :
    ((sheafifyOfIsEquivalence J K G A).obj P ⟶ Q) ≃ (P ⟶ Q.val) :=
  haveI := IsDenseSubsite.isLocallyFull J K G
  haveI := IsDenseSubsite.isCoverDense J K G
  ((G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction J A).homEquiv _ _).trans IsCoverDense.restrictHomEquivHom)

@[reassoc]
lemma sheafifyHomEquivOfIsEquivalence_naturality_left
    {P₁ P₂ : Dᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) {Q : Sheaf K A}
    (g : (sheafifyOfIsEquivalence J K G A).obj P₂ ⟶ Q) :
      sheafifyHomEquivOfIsEquivalence J K G
        ((sheafifyOfIsEquivalence J K G A).map f ≫ g) =
        f ≫ sheafifyHomEquivOfIsEquivalence J K G g := by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _
    ((sheafifyOfIsEquivalence J K G A).map f ≫ g))) =
      f ≫ IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ g))
  rw [← IsCoverDense.restrictHomEquivHom_naturality_left]
  congr 2
  trans adj₂.homEquiv _ _ ((presheafToSheaf J A).map (G.op.whiskerLeft f) ≫
    (adj₁.homEquiv _ _) g)
  · congr 1
    apply adj₁.homEquiv_naturality_left
  · apply adj₂.homEquiv_naturality_left

@[reassoc]
lemma sheafifyHomEquivOfIsEquivalence_naturality_right
    {P : Dᵒᵖ ⥤ A} {Q₁ Q₂ : Sheaf K A}
    (f : (sheafifyOfIsEquivalence J K G A).obj P ⟶ Q₁) (g : Q₁ ⟶ Q₂) :
      sheafifyHomEquivOfIsEquivalence J K G (f ≫ g) =
        sheafifyHomEquivOfIsEquivalence J K G f ≫ g.val := by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ (f ≫ g))) =
    IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ f)) ≫ g.val
  rw [adj₁.homEquiv_naturality_right, adj₂.homEquiv_naturality_right]
  apply IsCoverDense.restrictHomEquivHom_naturality_right

variable (A)

set_option backward.isDefEq.respectTransparency false in
/-- Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`)
and `sheafPushforwardContinuous G A J K` is an equivalence of categories, and
that `HasWeakSheafify J A` holds, then this adjunction shows the existence
of a left adjoint to `sheafToPresheaf K A`. -/
noncomputable def sheafifyAdjunctionOfIsEquivalence :
    sheafifyOfIsEquivalence J K G A ⊣ sheafToPresheaf K A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q ↦ sheafifyHomEquivOfIsEquivalence J K G
      homEquiv_naturality_left_symm := fun {P₁ P₂ Q} f g ↦
        (sheafifyHomEquivOfIsEquivalence J K G).injective (by
          simp only [sheafToPresheaf_obj, Equiv.apply_symm_apply,
            sheafifyHomEquivOfIsEquivalence_naturality_left _ _ _ f])
      homEquiv_naturality_right :=
        sheafifyHomEquivOfIsEquivalence_naturality_right J K G }

include G K in
lemma hasWeakSheafify_of_isEquivalence :
    HasWeakSheafify K A := ⟨_, ⟨sheafifyAdjunctionOfIsEquivalence J K G A⟩⟩

end

open Limits in
include G in
lemma hasSheafify_of_isEquivalence [HasSheafify J A] [HasFiniteLimits A] :
    HasSheafify K A := by
  have : PreservesFiniteLimits (presheafToSheaf J A ⋙
    (G.sheafPushforwardContinuous A J K).inv) := by
    apply comp_preservesFiniteLimits
  have : PreservesFiniteLimits (sheafifyOfIsEquivalence J K G A) := by
    apply comp_preservesFiniteLimits
  exact HasSheafify.mk' _ _ (sheafifyAdjunctionOfIsEquivalence J K G A)

end

section

variable (J A) [IsEquivalence (sheafPushforwardContinuous G A J K)]

/--
If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, and the
pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, then this
is the equivalence `Sheaf K A ≌ Sheaf J A`. -/
@[simps! inverse]
noncomputable def sheafEquiv : Sheaf J A ≌ Sheaf K A :=
  (sheafPushforwardContinuous G A J K).asEquivalence.symm

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The natural isomorphism exhibiting the compatibility of
`IsDenseSubsite.sheafEquiv` with sheafification. -/
noncomputable
def sheafEquivSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
      presheafToSheaf K A ⋙ (sheafEquiv J K G A).inverse :=
  (sheafifyOfIsEquivalenceCompIso _ _ _ _).symm ≪≫
    isoWhiskerRight
      ((sheafifyAdjunctionOfIsEquivalence J K G A).leftAdjointUniq
        (sheafificationAdjunction K A)) _

end

end IsDenseSubsite

end Functor

end CategoryTheory
