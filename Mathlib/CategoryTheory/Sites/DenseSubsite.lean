/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

#align_import category_theory.sites.dense_subsite from "leanprover-community/mathlib"@"1d650c2e131f500f3c17f33b4d19d2ea15987f2c"
/-!
# Dense subsites

We define `CoverDense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

We will primarily consider cover-dense functors that are also full, since this notion is in general
not well-behaved otherwise. Note that https://ncatlab.org/nlab/show/dense+sub-site indeed has a
weaker notion of cover-dense that loosens this requirement, but it would not have all the properties
we would need, and some sheafification would be needed for here and there.

## Main results

- `CategoryTheory.CoverDense.Types.presheafHom`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any presheaf `ℱ` and sheaf `ℱ'` on `D`, and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`,
  we may glue them together to obtain a morphism of presheaves `ℱ ⟶ ℱ'`.
- `CategoryTheory.CoverDense.sheafIso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `CategoryTheory.CoverDense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is full and cover-dense,
  then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`, then `α` is an iso if
  `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `CategoryTheory.CoverDense.sheafEquivOfCoverPreservingCoverLifting`:
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
-- porting note: removed `@[nolint has_nonempty_instance]`
structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by aesop_cat
#align category_theory.presieve.cover_by_image_structure CategoryTheory.Presieve.CoverByImageStructure
attribute [nolint docBlame] Presieve.CoverByImageStructure.obj Presieve.CoverByImageStructure.lift
  Presieve.CoverByImageStructure.map Presieve.CoverByImageStructure.fac

attribute [reassoc (attr := simp)] Presieve.CoverByImageStructure.fac

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `Presieve.coverByImage G U` is the presieve
of `U` consisting of those arrows that factor through images of `G`.
-/
def Presieve.coverByImage (G : C ⥤ D) (U : D) : Presieve U := fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)
#align category_theory.presieve.cover_by_image CategoryTheory.Presieve.coverByImage

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `Sieve.coverByImage G U` is the sieve of `U`
consisting of those arrows that factor through images of `G`.
-/
def Sieve.coverByImage (G : C ⥤ D) (U : D) : Sieve U :=
  ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩
                                                   -- 🎉 no goals
#align category_theory.sieve.cover_by_image CategoryTheory.Sieve.coverByImage

theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩
                  -- 🎉 no goals
#align category_theory.presieve.in_cover_by_image CategoryTheory.Presieve.in_coverByImage

/-- A functor `G : (C, J) ⥤ (D, K)` is called `CoverDense` if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
structure CoverDense (K : GrothendieckTopology D) (G : C ⥤ D) : Prop where
  is_cover : ∀ U : D, Sieve.coverByImage G U ∈ K U
#align category_theory.cover_dense CategoryTheory.CoverDense

attribute [nolint docBlame] CategoryTheory.CoverDense.is_cover

open Presieve Opposite

namespace CoverDense

variable {K}

variable {A : Type*} [Category A] {G : C ⥤ D} (H : CoverDense K G)

-- this is not marked with `@[ext]` because `H` can not be inferred from the type
theorem ext (H : CoverDense K G) (ℱ : SheafOfTypes K) (X : D) {s t : ℱ.val.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op s = ℱ.val.map f.op t) : s = t := by
  apply (ℱ.cond (Sieve.coverByImage G X) (H.is_cover X)).isSeparatedFor.ext
  -- ⊢ ∀ ⦃Y : D⦄ ⦃f : Y ⟶ X⦄, (Sieve.coverByImage G X).arrows f → ℱ.val.map f.op s  …
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  -- ⊢ ℱ.val.map (f₁ ≫ f₂).op s = ℱ.val.map (f₁ ≫ f₂).op t
  simp [h f₂]
  -- 🎉 no goals
#align category_theory.cover_dense.ext CategoryTheory.CoverDense.ext

theorem functorPullback_pushforward_covering [Full G] (H : CoverDense K G) {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X) := by
  refine' K.superset_covering _ (K.bind_covering T.property fun Y f _ => H.is_cover Y)
  -- ⊢ (Sieve.bind (↑T).arrows fun Y f x => Sieve.coverByImage G Y) ≤ Sieve.functor …
  rintro Y _ ⟨Z, _, f, hf, ⟨W, g, f', ⟨rfl⟩⟩, rfl⟩
  -- ⊢ (Sieve.functorPushforward G (Sieve.functorPullback G ↑T)).arrows ((g ≫ f') ≫ …
  use W; use G.preimage (f' ≫ f); use g
  -- ⊢ ∃ g_1 h, (Sieve.functorPullback G ↑T).arrows g_1 ∧ (g ≫ f') ≫ f = h ≫ G.map  …
         -- ⊢ ∃ h, (Sieve.functorPullback G ↑T).arrows (G.preimage (f' ≫ f)) ∧ (g ≫ f') ≫  …
                                  -- ⊢ (Sieve.functorPullback G ↑T).arrows (G.preimage (f' ≫ f)) ∧ (g ≫ f') ≫ f = g …
  constructor
  -- ⊢ (Sieve.functorPullback G ↑T).arrows (G.preimage (f' ≫ f))
  · simpa using T.val.downward_closed hf f'
    -- 🎉 no goals
  · simp
    -- 🎉 no goals
#align category_theory.cover_dense.functor_pullback_pushforward_covering CategoryTheory.CoverDense.functorPullback_pushforward_covering

/-- (Implementation). Given a hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain a hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps!]
def homOver {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ ℱ ⋙ coyoneda.obj (op X) ⟶ G.op ⋙ (sheafOver ℱ' X).val :=
  whiskerRight α (coyoneda.obj (op X))
#align category_theory.cover_dense.hom_over CategoryTheory.CoverDense.homOver

/-- (Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps!]
def isoOver {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) (X : A) :
    G.op ⋙ (sheafOver ℱ X).val ≅ G.op ⋙ (sheafOver ℱ' X).val :=
  isoWhiskerRight α (coyoneda.obj (op X))
#align category_theory.cover_dense.iso_over CategoryTheory.CoverDense.isoOver

theorem sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT)
    (x : FamilyOfElements _ T) (hx) (t) (h : x.IsAmalgamation t) :
    t = (ℱ.cond X T hT).amalgamate x hx :=
  (ℱ.cond X T hT).isSeparatedFor x t _ h ((ℱ.cond X T hT).isAmalgamation hx)
#align category_theory.cover_dense.sheaf_eq_amalgamation CategoryTheory.CoverDense.sheaf_eq_amalgamation

variable [Full G]

namespace Types

variable {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : SheafOfTypes.{v} K} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val)

/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
-- porting note: removed `@[simp, nolint unused_arguments]`
noncomputable def pushforwardFamily {X} (x : ℱ.obj (op X)) :
    FamilyOfElements ℱ'.val (coverByImage G X) := fun _ _ hf =>
  ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x : _)
#align category_theory.cover_dense.types.pushforward_family CategoryTheory.CoverDense.Types.pushforwardFamily

-- porting note: there are various `include` and `omit`s in this file  (e.g. one is removed here),
-- none of which are needed in Lean 4.

-- porting note: `pushforward_family` was tagged `@[simp]` in Lean 3 so we add the
-- equation lemma
@[simp] theorem pushforwardFamily_def {X} (x : ℱ.obj (op X)) :
    pushforwardFamily α x = fun _ _ hf =>
  ℱ'.val.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x : _) := rfl

/-- (Implementation). The `pushforwardFamily` defined is compatible. -/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) :
    (pushforwardFamily α x).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ e
  -- ⊢ ℱ'.val.map g₁.op (pushforwardFamily α x f₁ h₁) = ℱ'.val.map g₂.op (pushforwa …
  apply H.ext
  -- ⊢ ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ Z), ℱ'.val.map f.op (ℱ'.val.map g₁.op (pushforwardF …
  intro Y f
  -- ⊢ ℱ'.val.map f.op (ℱ'.val.map g₁.op (pushforwardFamily α x f₁ h₁)) = ℱ'.val.ma …
  simp only [pushforwardFamily, ← FunctorToTypes.map_comp_apply, ← op_comp]
  -- ⊢ ℱ'.val.map (f ≫ g₁ ≫ (Nonempty.some h₁).lift).op (NatTrans.app α (op (Nonemp …
  change (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _ = (ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _) _
  -- ⊢ (ℱ.map (Nonempty.some h₁).map.op ≫ NatTrans.app α (op (Nonempty.some h₁).1)  …
  rw [← G.image_preimage (f ≫ g₁ ≫ _)]
  -- ⊢ (ℱ.map (Nonempty.some h₁).map.op ≫ NatTrans.app α (op (Nonempty.some h₁).1)  …
  rw [← G.image_preimage (f ≫ g₂ ≫ _)]
  -- ⊢ (ℱ.map (Nonempty.some h₁).map.op ≫ NatTrans.app α (op (Nonempty.some h₁).1)  …
  erw [← α.naturality (G.preimage _).op]
  -- ⊢ (ℱ.map (Nonempty.some h₁).map.op ≫ (G.op ⋙ ℱ).map (G.preimage (f ≫ g₁ ≫ (Non …
  erw [← α.naturality (G.preimage _).op]
  -- ⊢ (ℱ.map (Nonempty.some h₁).map.op ≫ (G.op ⋙ ℱ).map (G.preimage (f ≫ g₁ ≫ (Non …
  refine' congr_fun _ x
  -- ⊢ ℱ.map (Nonempty.some h₁).map.op ≫ (G.op ⋙ ℱ).map (G.preimage (f ≫ g₁ ≫ (None …
  -- porting note: these next 3 tactics (simp, rw, simp) were just one big `simp only` in Lean 3
  -- but I can't get `simp` to do the `rw` line.
  simp only [Functor.comp_map, ← Category.assoc, Functor.op_map, Quiver.Hom.unop_op]
  -- ⊢ (ℱ.map (Nonempty.some h₁).map.op ≫ ℱ.map (G.map (G.preimage ((f ≫ g₁) ≫ (Non …
  rw [← ℱ.map_comp, ← ℱ.map_comp] -- `simp only [← ℱ.map_comp]` does nothing, even if I add
  -- ⊢ ℱ.map ((Nonempty.some h₁).map.op ≫ (G.map (G.preimage ((f ≫ g₁) ≫ (Nonempty. …
  -- the relevant explicit inputs
  simp only [← op_comp, G.image_preimage]
  -- ⊢ ℱ.map (((f ≫ g₁) ≫ (Nonempty.some h₁).lift) ≫ (Nonempty.some h₁).map).op ≫ N …
  congr 3
  -- ⊢ ((f ≫ g₁) ≫ (Nonempty.some h₁).lift) ≫ (Nonempty.some h₁).map = ((f ≫ g₂) ≫  …
  simp [e]
  -- 🎉 no goals
#align category_theory.cover_dense.types.pushforward_family_compatible CategoryTheory.CoverDense.Types.pushforwardFamily_compatible

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforwardFamily`. -/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.val.obj (op X) := fun x =>
  (ℱ'.cond _ (H.is_cover X)).amalgamate (pushforwardFamily α x)
    (pushforwardFamily_compatible H α x)
#align category_theory.cover_dense.types.app_hom CategoryTheory.CoverDense.Types.appHom

@[simp]
theorem pushforwardFamily_apply {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) := by
  unfold pushforwardFamily
  -- ⊢ ℱ'.val.map (Nonempty.some (_ : coverByImage G X f)).lift.op (NatTrans.app α  …
  -- porting note: congr_fun was more powerful in Lean 3; I had to explicitly supply
  -- the type of the first input here even though it's obvious (there is a unique occurrence
  -- of x on each side of the equality)
  refine' congr_fun (_ :
    (fun t => ℱ'.val.map ((Nonempty.some (_ : coverByImage G X f)).lift.op)
      (α.app (op (Nonempty.some (_ : coverByImage G X f)).1)
        (ℱ.map ((Nonempty.some (_ : coverByImage G X f)).map.op) t))) =
    (fun t => α.app (op Y) (ℱ.map (f.op) t))) x
  rw [← G.image_preimage (Nonempty.some _ : Presieve.CoverByImageStructure _ _).lift]
  -- ⊢ (fun t => ℱ'.val.map (G.map (G.preimage (Nonempty.some (_ : coverByImage G X …
  change ℱ.map _ ≫ α.app (op _) ≫ ℱ'.val.map _ = ℱ.map f.op ≫ α.app (op Y)
  -- ⊢ ℱ.map (Nonempty.some (_ : coverByImage G X f)).map.op ≫ NatTrans.app α (op ( …
  erw [← α.naturality (G.preimage _).op]
  -- ⊢ ℱ.map (Nonempty.some (_ : coverByImage G X f)).map.op ≫ (G.op ⋙ ℱ).map (G.pr …
  simp only [← Functor.map_comp, ← Category.assoc, Functor.comp_map, G.image_preimage, G.op_map,
    Quiver.Hom.unop_op, ← op_comp, Presieve.CoverByImageStructure.fac]
#align category_theory.cover_dense.types.pushforward_family_apply CategoryTheory.CoverDense.Types.pushforwardFamily_apply

@[simp]
theorem appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
    ℱ'.val.map f (appHom H α X x) = α.app (op Y) (ℱ.map f x) := by
  refine'
    ((ℱ'.cond _ (H.is_cover X)).valid_glue (pushforwardFamily_compatible H α x) f.unop
          (Presieve.in_coverByImage G f.unop)).trans
      _
  apply pushforwardFamily_apply
  -- 🎉 no goals
#align category_theory.cover_dense.types.app_hom_restrict CategoryTheory.CoverDense.Types.appHom_restrict

@[simp]
theorem appHom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
    appHom H α X ≫ ℱ'.val.map f = ℱ.map f ≫ α.app (op Y) := by
  ext
  -- ⊢ (appHom H α X ≫ ℱ'.val.map f) a✝ = (ℱ.map f ≫ NatTrans.app α (op Y)) a✝
  apply appHom_restrict
  -- 🎉 no goals
#align category_theory.cover_dense.types.app_hom_valid_glue CategoryTheory.CoverDense.Types.appHom_valid_glue

/--
(Implementation). The maps given in `appIso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps]
noncomputable def appIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val)
    (X : D) : ℱ.val.obj (op X) ≅ ℱ'.val.obj (op X) where
  hom := appHom H i.hom X
  inv := appHom H i.inv X
  hom_inv_id := by
    ext x
    -- ⊢ (appHom H i.hom X ≫ appHom H i.inv X) x = 𝟙 (ℱ.val.obj (op X)) x
    apply H.ext
    -- ⊢ ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op ((appHom H i.hom X ≫ appHom H i. …
    intro Y f
    -- ⊢ ℱ.val.map f.op ((appHom H i.hom X ≫ appHom H i.inv X) x) = ℱ.val.map f.op (𝟙 …
    simp
    -- 🎉 no goals
  inv_hom_id := by
    ext x
    -- ⊢ (appHom H i.inv X ≫ appHom H i.hom X) x = 𝟙 (ℱ'.val.obj (op X)) x
    apply H.ext
    -- ⊢ ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ'.val.map f.op ((appHom H i.inv X ≫ appHom H i …
    intro Y f
    -- ⊢ ℱ'.val.map f.op ((appHom H i.inv X ≫ appHom H i.hom X) x) = ℱ'.val.map f.op  …
    simp
    -- 🎉 no goals
#align category_theory.cover_dense.types.app_iso CategoryTheory.CoverDense.Types.appIso

/-- Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types, where `G` is
full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation between sheaves.
-/
@[simps]
noncomputable def presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val where
  app X := appHom H α (unop X)
  naturality X Y f := by
    ext x
    -- ⊢ (ℱ.map f ≫ (fun X => appHom H α X.unop) Y) x = ((fun X => appHom H α X.unop) …
    apply H.ext ℱ' (unop Y)
    -- ⊢ ∀ ⦃Y_1 : C⦄ (f_1 : G.obj Y_1 ⟶ Y.unop), ℱ'.val.map f_1.op ((ℱ.map f ≫ (fun X …
    intro Y' f'
    -- ⊢ ℱ'.val.map f'.op ((ℱ.map f ≫ (fun X => appHom H α X.unop) Y) x) = ℱ'.val.map …
    simp only [appHom_restrict, types_comp_apply, ← FunctorToTypes.map_comp_apply]
    -- 🎉 no goals
    -- porting note: Lean 3 proof continued with a rewrite but we're done here
#align category_theory.cover_dense.types.presheaf_hom CategoryTheory.CoverDense.Types.presheafHom

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
noncomputable def presheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val :=
  NatIso.ofComponents (fun X => appIso H i (unop X)) @(presheafHom H i.hom).naturality
#align category_theory.cover_dense.types.presheaf_iso CategoryTheory.CoverDense.Types.presheafIso

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types, where `G` is full
and cover-dense, and `ℱ, ℱ'` are sheaves, we may obtain a natural isomorphism between sheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : SheafOfTypes.{v} K} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ ≅ ℱ' where
  hom := ⟨(presheafIso H i).hom⟩
  inv := ⟨(presheafIso H i).inv⟩
  hom_inv_id := by
    ext1
    -- ⊢ ({ val := (presheafIso H i).hom } ≫ { val := (presheafIso H i).inv }).val =  …
    apply (presheafIso H i).hom_inv_id
    -- 🎉 no goals
  inv_hom_id := by
    ext1
    -- ⊢ ({ val := (presheafIso H i).inv } ≫ { val := (presheafIso H i).hom }).val =  …
    apply (presheafIso H i).inv_hom_id
    -- 🎉 no goals
#align category_theory.cover_dense.types.sheaf_iso CategoryTheory.CoverDense.Types.sheafIso

end Types

open Types

variable {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps]
noncomputable def sheafCoyonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ ⟶
      coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ'.val where
  app X := presheafHom H (homOver α (unop X))
  naturality X Y f := by
    ext U x
    -- ⊢ NatTrans.app ((coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type ?u.90244)).obj ℱ).map  …
    change
      appHom H (homOver α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ appHom H (homOver α (unop X)) (unop U) x
    symm
    -- ⊢ f.unop ≫ appHom H (homOver α X.unop) U.unop x = appHom H (homOver α Y.unop)  …
    apply sheaf_eq_amalgamation
    apply H.is_cover
    -- ⊢ FamilyOfElements.Compatible fun Y_1 f_1 h => pushforwardFamily (homOver α Y. …
    -- porting note: the following line closes a goal which didn't exist before reenableeta
    · exact pushforwardFamily_compatible H (homOver α Y.unop) (f.unop ≫ x)
      -- 🎉 no goals
    intro Y' f' hf'
    -- ⊢ (ℱ'.val ⋙ coyoneda.obj (op Y.unop)).map f'.op (f.unop ≫ appHom H (homOver α  …
    change unop X ⟶ ℱ.obj (op (unop _)) at x
    -- ⊢ (ℱ'.val ⋙ coyoneda.obj (op Y.unop)).map f'.op (f.unop ≫ appHom H (homOver α  …
    dsimp
    -- ⊢ (f.unop ≫ appHom H (homOver α X.unop) U.unop x) ≫ ℱ'.val.map f'.op = (((f.un …
    simp only [pushforwardFamily, Functor.comp_map, coyoneda_obj_map, homOver_app, Category.assoc]
    -- ⊢ f.unop ≫ appHom H (homOver α X.unop) U.unop x ≫ ℱ'.val.map f'.op = f.unop ≫  …
    congr 1
    -- ⊢ appHom H (homOver α X.unop) U.unop x ≫ ℱ'.val.map f'.op = x ≫ ℱ.map (Nonempt …
    conv_lhs => rw [← hf'.some.fac]
    -- ⊢ appHom H (homOver α X.unop) U.unop x ≫ ℱ'.val.map ((Nonempty.some hf').lift  …
    simp only [← Category.assoc, op_comp, Functor.map_comp]
    -- ⊢ (appHom H (homOver α X.unop) U.unop x ≫ ℱ'.val.map (Nonempty.some hf').map.o …
    congr 1
    -- ⊢ appHom H (homOver α X.unop) U.unop x ≫ ℱ'.val.map (Nonempty.some hf').map.op …
    refine' (appHom_restrict H (homOver α (unop X)) hf'.some.map.op x).trans _
    -- ⊢ NatTrans.app (homOver α X.unop) (op (Nonempty.some hf').obj) ((ℱ ⋙ coyoneda. …
    simp
    -- 🎉 no goals
#align category_theory.cover_dense.sheaf_coyoneda_hom CategoryTheory.CoverDense.sheafCoyonedaHom

/--
(Implementation). `sheafCoyonedaHom` but the order of the arguments of the functor are swapped.
-/
noncomputable def sheafYonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    ℱ ⋙ yoneda ⟶ ℱ'.val ⋙ yoneda := by
  let α := sheafCoyonedaHom H α
  -- ⊢ ℱ ⋙ yoneda ⟶ ℱ'.val ⋙ yoneda
  refine'
    { app := _
      naturality := _ }
  · intro U
    -- ⊢ (ℱ ⋙ yoneda).obj U ⟶ (ℱ'.val ⋙ yoneda).obj U
    refine'
      { app := fun X => (α.app X).app U
        naturality := fun X Y f => by simpa using congr_app (α.naturality f) U }
  · intro U V i
    -- ⊢ ((ℱ ⋙ yoneda).map i ≫ NatTrans.mk fun X => NatTrans.app (NatTrans.app α X) V …
    ext X x
    -- ⊢ NatTrans.app ((ℱ ⋙ yoneda).map i ≫ NatTrans.mk fun X => NatTrans.app (NatTra …
    exact congr_fun ((α.app X).naturality i) x
    -- 🎉 no goals
#align category_theory.cover_dense.sheaf_yoneda_hom CategoryTheory.CoverDense.sheafYonedaHom

/-- Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural transformation
between presheaves.
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) : ℱ ⟶ ℱ'.val :=
  let α' := sheafYonedaHom H α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using α'.naturality f) }
                                                        -- 🎉 no goals
#align category_theory.cover_dense.sheaf_hom CategoryTheory.CoverDense.sheafHom

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
noncomputable def presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) :
    ℱ.val ≅ ℱ'.val := by
  have : ∀ X : Dᵒᵖ, IsIso ((sheafHom H i.hom).app X) := by
    intro X
    -- porting note: somehow `apply` in Lean 3 is leaving a typeclass goal,
    -- perhaps due to elaboration order. The corresponding `apply` in Lean 4 fails
    -- because the instance can't yet be synthesized. I hence reorder the proof.
    suffices IsIso (yoneda.map ((sheafHom H i.hom).app X)) by
      apply isIso_of_reflects_iso _ yoneda
    use (sheafYonedaHom H i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheafHom, NatTrans.comp_app, NatTrans.id_app, Functor.image_preimage]
    · exact ((Types.presheafIso H (isoOver i (unop x))).app X).hom_inv_id
    · exact ((Types.presheafIso H (isoOver i (unop x))).app X).inv_hom_id
    -- porting note: Lean 4 proof is finished, Lean 3 needed `inferInstance`
  haveI : IsIso (sheafHom H i.hom) := by apply NatIso.isIso_of_isIso_app
  -- ⊢ ℱ.val ≅ ℱ'.val
  apply asIso (sheafHom H i.hom)
  -- 🎉 no goals
#align category_theory.cover_dense.presheaf_iso CategoryTheory.CoverDense.presheafIso

/-- Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps]
noncomputable def sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.val ≅ G.op ⋙ ℱ'.val) : ℱ ≅ ℱ' where
  hom := ⟨(presheafIso H i).hom⟩
  inv := ⟨(presheafIso H i).inv⟩
  hom_inv_id := by
    ext1
    -- ⊢ ({ val := (presheafIso H i).hom } ≫ { val := (presheafIso H i).inv }).val =  …
    apply (presheafIso H i).hom_inv_id
    -- 🎉 no goals
  inv_hom_id := by
    ext1
    -- ⊢ ({ val := (presheafIso H i).inv } ≫ { val := (presheafIso H i).hom }).val =  …
    apply (presheafIso H i).inv_hom_id
    -- 🎉 no goals
#align category_theory.cover_dense.sheaf_iso CategoryTheory.CoverDense.sheafIso

/-- The constructed `sheafHom α` is equal to `α` when restricted onto `C`.
-/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) :
    whiskerLeft G.op (sheafHom H α) = α := by
  ext X
  -- ⊢ NatTrans.app (whiskerLeft G.op (sheafHom H α)) X = NatTrans.app α X
  apply yoneda.map_injective
  -- ⊢ yoneda.map (NatTrans.app (whiskerLeft G.op (sheafHom H α)) X) = yoneda.map ( …
  ext U
  -- ⊢ NatTrans.app (yoneda.map (NatTrans.app (whiskerLeft G.op (sheafHom H α)) X)) …
  -- porting note: didn't need to provide the input to `image_preimage` in Lean 3
  erw [yoneda.image_preimage ((H.sheafYonedaHom α).app (G.op.obj X))]
  -- ⊢ NatTrans.app (NatTrans.app (sheafYonedaHom H α) (G.op.obj X)) U a✝ = NatTran …
  symm
  -- ⊢ NatTrans.app (yoneda.map (NatTrans.app α X)) U a✝ = NatTrans.app (NatTrans.a …
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  -- ⊢ (let_fun this := NatTrans.app (yoneda.map (NatTrans.app α X)) U a✝;
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _)
  -- porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible H _ _)
    -- 🎉 no goals
  intro Y f hf
  -- ⊢ (ℱ'.val ⋙ coyoneda.obj (op U.unop)).map f.op
  conv_lhs => rw [← hf.some.fac]
  -- ⊢ (ℱ'.val ⋙ coyoneda.obj (op U.unop)).map ((Nonempty.some hf).lift ≫ (Nonempty …
  simp only [pushforwardFamily, Functor.comp_map, yoneda_map_app, coyoneda_obj_map, op_comp,
    FunctorToTypes.map_comp_apply, homOver_app, ← Category.assoc]
  congr 1
  -- ⊢ (a✝ ≫ NatTrans.app α X) ≫ ℱ'.val.map (Nonempty.some hf).map.op = (a✝ ≫ ℱ.map …
  simp only [Category.assoc]
  -- ⊢ a✝ ≫ NatTrans.app α X ≫ ℱ'.val.map (Nonempty.some hf).map.op = a✝ ≫ ℱ.map (N …
  congr 1
  -- ⊢ NatTrans.app α X ≫ ℱ'.val.map (Nonempty.some hf).map.op = ℱ.map (Nonempty.so …
  rw [← G.image_preimage hf.some.map]
  -- ⊢ NatTrans.app α X ≫ ℱ'.val.map (G.map (G.preimage (Nonempty.some hf).map)).op …
  symm
  -- ⊢ ℱ.map (G.map (G.preimage (Nonempty.some hf).map)).op ≫ NatTrans.app α (op (N …
  apply α.naturality (G.preimage hf.some.map).op
  -- 🎉 no goals
  -- porting note; Lean 3 needed a random `inferInstance` for cleanup here; not necessary in lean 4
#align category_theory.cover_dense.sheaf_hom_restrict_eq CategoryTheory.CoverDense.sheafHom_restrict_eq

/-- If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
theorem sheafHom_eq (α : ℱ ⟶ ℱ'.val) : sheafHom H (whiskerLeft G.op α) = α := by
  ext X
  -- ⊢ NatTrans.app (sheafHom H (whiskerLeft G.op α)) X = NatTrans.app α X
  apply yoneda.map_injective
  -- ⊢ yoneda.map (NatTrans.app (sheafHom H (whiskerLeft G.op α)) X) = yoneda.map ( …
  -- porting note: deleted next line as it's not needed in Lean 4
  ext U
  -- ⊢ NatTrans.app (yoneda.map (NatTrans.app (sheafHom H (whiskerLeft G.op α)) X)) …
  -- porting note: Lean 3 didn't need to be told the explicit input to image_preimage
  erw [yoneda.image_preimage ((H.sheafYonedaHom (whiskerLeft G.op α)).app X)]
  -- ⊢ NatTrans.app (NatTrans.app (sheafYonedaHom H (whiskerLeft G.op α)) X) U a✝ = …
  symm
  -- ⊢ NatTrans.app (yoneda.map (NatTrans.app α X)) U a✝ = NatTrans.app (NatTrans.a …
  change (show (ℱ'.val ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  -- ⊢ (let_fun this := NatTrans.app (yoneda.map (NatTrans.app α X)) U a✝;
  apply sheaf_eq_amalgamation ℱ' (H.is_cover _)
  -- porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible H _ _)
    -- 🎉 no goals
  intro Y f hf
  -- ⊢ (ℱ'.val ⋙ coyoneda.obj (op U.unop)).map f.op
  conv_lhs => rw [← hf.some.fac]
  -- ⊢ (ℱ'.val ⋙ coyoneda.obj (op U.unop)).map ((Nonempty.some hf).lift ≫ (Nonempty …
  dsimp
  -- ⊢ (a✝ ≫ NatTrans.app α X) ≫ ℱ'.val.map ((Nonempty.some hf).map.op ≫ (Nonempty. …
  simp
  -- 🎉 no goals
#align category_theory.cover_dense.sheaf_hom_eq CategoryTheory.CoverDense.sheafHom_eq

/-- A full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.val) ≃ (ℱ ⟶ ℱ'.val) where
  toFun := sheafHom H
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq H
  right_inv := sheafHom_eq H
#align category_theory.cover_dense.restrict_hom_equiv_hom CategoryTheory.CoverDense.restrictHomEquivHom

/-- Given a full and cover-dense functor `G` and a natural transformation of sheaves `α : ℱ ⟶ ℱ'`,
if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.val)) :
    IsIso α := by
  convert IsIso.of_iso (sheafIso H (asIso (whiskerLeft G.op α.val))) using 1
  -- ⊢ α = (sheafIso H (asIso (whiskerLeft G.op α.val))).hom
  ext1
  -- ⊢ α.val = (sheafIso H (asIso (whiskerLeft G.op α.val))).hom.val
  apply (sheafHom_eq H _).symm
  -- 🎉 no goals
#align category_theory.cover_dense.iso_of_restrict_iso CategoryTheory.CoverDense.iso_of_restrict_iso

/-- A fully faithful cover-dense functor preserves compatible families. -/
theorem compatiblePreserving [Faithful G] : CompatiblePreserving K G := by
  constructor
  -- ⊢ ∀ (ℱ : SheafOfTypes K) {Z : C} {T : Presieve Z} {x : FamilyOfElements (G.op  …
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  -- ⊢ ℱ.val.map f₁.op (x g₁ hg₁) = ℱ.val.map f₂.op (x g₂ hg₂)
  apply H.ext
  -- ⊢ ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.val.map f.op (ℱ.val.map f₁.op (x g₁ hg₁)) = ℱ …
  intro W i
  -- ⊢ ℱ.val.map i.op (ℱ.val.map f₁.op (x g₁ hg₁)) = ℱ.val.map i.op (ℱ.val.map f₂.o …
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  -- ⊢ ℱ.val.map (i ≫ f₁).op (x g₁ hg₁) = ℱ.val.map (i ≫ f₂).op (x g₂ hg₂)
  rw [← G.image_preimage (i ≫ f₁)]
  -- ⊢ ℱ.val.map (G.map (G.preimage (i ≫ f₁))).op (x g₁ hg₁) = ℱ.val.map (i ≫ f₂).o …
  rw [← G.image_preimage (i ≫ f₂)]
  -- ⊢ ℱ.val.map (G.map (G.preimage (i ≫ f₁))).op (x g₁ hg₁) = ℱ.val.map (G.map (G. …
  apply hx
  -- ⊢ Full.preimage (i ≫ f₁) ≫ g₁ = Full.preimage (i ≫ f₂) ≫ g₂
  apply G.map_injective
  -- ⊢ G.map (Full.preimage (i ≫ f₁) ≫ g₁) = G.map (Full.preimage (i ≫ f₂) ≫ g₂)
  simp [eq]
  -- 🎉 no goals
#align category_theory.cover_dense.compatible_preserving CategoryTheory.CoverDense.compatiblePreserving

noncomputable instance Sites.Pullback.full [Faithful G] (Hp : CoverPreserving J K G) :
    Full (Sites.pullback A H.compatiblePreserving Hp) where
  preimage α := ⟨H.sheafHom α.val⟩
  witness α := Sheaf.Hom.ext _ _ <| H.sheafHom_restrict_eq α.val
#align category_theory.cover_dense.sites.pullback.full CategoryTheory.CoverDense.Sites.Pullback.full

instance Sites.Pullback.faithful [Faithful G] (Hp : CoverPreserving J K G) :
    Faithful (Sites.pullback A H.compatiblePreserving Hp) where
  map_injective := by
    intro ℱ ℱ' α β e
    -- ⊢ α = β
    ext1
    -- ⊢ α.val = β.val
    apply_fun fun e => e.val at e
    -- ⊢ α.val = β.val
    dsimp at e
    -- ⊢ α.val = β.val
    rw [← H.sheafHom_eq α.val, ← H.sheafHom_eq β.val, e]
    -- 🎉 no goals
#align category_theory.cover_dense.sites.pullback.faithful CategoryTheory.CoverDense.Sites.Pullback.faithful

end CoverDense

end CategoryTheory

namespace CategoryTheory.CoverDense

open CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

variable {G : C ⥤ D} [Full G] [Faithful G]

variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

variable {A : Type w} [Category.{max u v} A] [Limits.HasLimits A]

variable (Hd : CoverDense K G) (Hp : CoverPreserving J K G) (Hl : CoverLifting J K G)

/-- Given a functor between small sites that is cover-dense, cover-preserving, and cover-lifting,
it induces an equivalence of category of sheaves valued in a complete category.
-/
@[simps! functor inverse]
noncomputable def sheafEquivOfCoverPreservingCoverLifting : Sheaf J A ≌ Sheaf K A := by
  symm
  -- ⊢ Sheaf K A ≌ Sheaf J A
  let α := Sites.pullbackCopullbackAdjunction.{w, v, u} A Hp Hl Hd.compatiblePreserving
  -- ⊢ Sheaf K A ≌ Sheaf J A
  have : ∀ X : Sheaf J A, IsIso (α.counit.app X) := by
    intro ℱ
    -- porting note: I don't know how to do `apply_with foo { instances := ff }`
    -- so I just create the instance first
    haveI : IsIso ((sheafToPresheaf J A).map (α.counit.app ℱ)) :=
      IsIso.of_iso ((@asIso _ _ _ _ _ (Ran.reflective A G.op)).app ℱ.val)
    apply ReflectsIsomorphisms.reflects (sheafToPresheaf J A)
  -- porting note: a bunch of instances are not synthesized in lean 4 for some reason
  haveI : IsIso α.counit := NatIso.isIso_of_isIso_app _
  -- ⊢ Sheaf K A ≌ Sheaf J A
  haveI : Full (Sites.pullback A Hd.compatiblePreserving Hp) :=
    CoverDense.Sites.Pullback.full J Hd Hp
  haveI : Faithful (Sites.pullback A Hd.compatiblePreserving Hp) :=
    CoverDense.Sites.Pullback.faithful J Hd Hp
  haveI : IsIso α.unit := CategoryTheory.unit_isIso_of_L_fully_faithful α
  -- ⊢ Sheaf K A ≌ Sheaf J A
  exact
    { functor := Sites.pullback A Hd.compatiblePreserving Hp
      inverse := Sites.copullback A Hl
      unitIso := asIso α.unit
      counitIso := asIso α.counit
      functor_unitIso_comp := fun ℱ => by convert α.left_triangle_components }
set_option linter.uppercaseLean3 false in
#align category_theory.cover_dense.Sheaf_equiv_of_cover_preserving_cover_lifting CategoryTheory.CoverDense.sheafEquivOfCoverPreservingCoverLifting

variable
  [ConcreteCategory.{max v u} A]
  [Limits.PreservesLimits (forget A)]
  [ReflectsIsomorphisms (forget A)]
  [∀ (X : C), Limits.PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget A)]
  [∀ (X : C), Limits.HasColimitsOfShape (J.Cover X)ᵒᵖ A]
  [∀ (X : D), Limits.PreservesColimitsOfShape (K.Cover X)ᵒᵖ (forget A)]
  [∀ (X : D), Limits.HasColimitsOfShape (K.Cover X)ᵒᵖ A]

/-- The natural isomorphism exhibiting the compatibility of
`sheafEquivOfCoverPreservingCoverLifting` with sheafification. -/
noncomputable
abbrev sheafEquivOfCoverPreservingCoverLiftingSheafificationCompatibility :
  (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf _ _ ≅
  presheafToSheaf _ _ ⋙ (sheafEquivOfCoverPreservingCoverLifting Hd Hp Hl).inverse :=
Sites.pullbackSheafificationCompatibility _ _ Hl _

end CategoryTheory.CoverDense
