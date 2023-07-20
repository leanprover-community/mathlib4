/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Data.Sum.Basic

#align_import category_theory.pi.basic from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

namespace CategoryTheory

universe w₀ w₁ w₂ v₁ v₂ u₁ u₂

variable {I : Type w₀} {J : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]


/-- `pi C` gives the cartesian product of an indexed family of categories.
-/
instance pi : Category.{max w₀ v₁} (∀ i, C i) where
  Hom X Y := ∀ i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i
#align category_theory.pi CategoryTheory.pi

/-- This provides some assistance to typeclass search in a common situation,
which otherwise fails. (Without this `CategoryTheory.Pi.has_limit_of_has_limit_comp_eval` fails.)
-/
abbrev pi' {I : Type v₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)] : Category.{v₁} (∀ i, C i) :=
  CategoryTheory.pi C
#align category_theory.pi' CategoryTheory.pi'

attribute [instance] pi'

namespace Pi

variable {C}

@[ext]
lemma hom_ext {X Y : ∀ i, C i} (f g : X ⟶ Y) (h : ∀ i, f i = g i) : f = g := funext h

variable (C)

@[simp]
theorem id_apply (X : ∀ i, C i) (i) : (𝟙 X : ∀ i, X i ⟶ X i) i = 𝟙 (X i) :=
  rfl
#align category_theory.pi.id_apply CategoryTheory.Pi.id_apply

@[simp]
theorem comp_apply {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
    (f ≫ g : ∀ i, X i ⟶ Z i) i = f i ≫ g i :=
  rfl
#align category_theory.pi.comp_apply CategoryTheory.Pi.comp_apply

-- Porting note: need to add an additional `ext` lemma.
@[ext]
lemma ext {X Y : ∀ i, C i} {f g : X ⟶ Y} (w : ∀ i, f i = g i) : f = g :=
  funext (w ·)

/--
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simps]
def eval (i : I) : (∀ i, C i) ⥤ C i where
  obj f := f i
  map α := α i
#align category_theory.pi.eval CategoryTheory.Pi.eval

section

variable {J : Type w₁}

/- Porting note: add this because Lean cannot see directly through the `∘` for
`Function.comp` -/

instance (f : J → I) : (j : J) → Category ((C ∘ f) j) := by
  dsimp
  infer_instance

/-- Pull back an `I`-indexed family of objects to a `J`-indexed family, along a function `J → I`.
-/
@[simps]
def comap (h : J → I) : (∀ i, C i) ⥤ (∀ j, C (h j)) where
  obj f i := f (h i)
  map α i := α (h i)
#align category_theory.pi.comap CategoryTheory.Pi.comap

variable (I)

/-- The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
def comapId : comap C (id : I → I) ≅ 𝟭 (∀ i, C i) where
  hom := { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }
#align category_theory.pi.comap_id CategoryTheory.Pi.comapId

example (g : J → I) : (j : J) → Category (C (g j)) := by infer_instance

variable {I}

variable {K : Type w₂}

/-- The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
@[simps!]
def comapComp (f : K → J) (g : J → I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) where
  hom :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
  inv :=
  { app := fun X b => 𝟙 (X (g (f b)))
    naturality := fun X Y f' => by simp only [comap, Function.comp]; funext; simp }
#align category_theory.pi.comap_comp CategoryTheory.Pi.comapComp

/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
@[simps!]
def comapEvalIsoEval (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  NatIso.ofComponents (fun f => Iso.refl _) (by simp only [Iso.refl]; aesop_cat)
#align category_theory.pi.comap_eval_iso_eval CategoryTheory.Pi.comapEvalIsoEval

end

section

variable {J : Type w₀} {D : J → Type u₁} [∀ j, Category.{v₁} (D j)]

/- Porting note: maybe mixing up universes -/
instance sumElimCategory : ∀ s : Sum I J, Category.{v₁} (Sum.elim C D s)
  | Sum.inl i => by
    dsimp
    infer_instance
  | Sum.inr j => by
    dsimp
    infer_instance
#align category_theory.pi.sum_elim_category CategoryTheory.Pi.sumElimCategoryₓ

/- Porting note: replaced `Sum.rec` with `match`'s per the error about
current state of code generation -/

/-- The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simps]
def sum : (∀ i, C i) ⥤ (∀ j, D j) ⥤ ∀ s : Sum I J, Sum.elim C D s where
  obj X :=
    { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {Y} {Y'} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr j => 𝟙 (Y j) }
#align category_theory.pi.sum CategoryTheory.Pi.sum

end

variable {C}

/-- An isomorphism between `I`-indexed objects gives an isomorphism between each
pair of corresponding components. -/
@[simps]
def isoApp {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i :=
  ⟨f.hom i, f.inv i, by
    dsimp
    rw [← comp_apply, Iso.hom_inv_id, id_apply], by
    dsimp
    rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩
#align category_theory.pi.iso_app CategoryTheory.Pi.isoApp

@[simp]
theorem isoApp_refl (X : ∀ i, C i) (i : I) : isoApp (Iso.refl X) i = Iso.refl (X i) :=
  rfl
#align category_theory.pi.iso_app_refl CategoryTheory.Pi.isoApp_refl

@[simp]
theorem isoApp_symm {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : isoApp f.symm i = (isoApp f i).symm :=
  rfl
#align category_theory.pi.iso_app_symm CategoryTheory.Pi.isoApp_symm

@[simp]
theorem isoApp_trans {X Y Z : ∀ i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I) :
    isoApp (f ≪≫ g) i = isoApp f i ≪≫ isoApp g i :=
  rfl
#align category_theory.pi.iso_app_trans CategoryTheory.Pi.isoApp_trans

end Pi

namespace Functor

variable {C}

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] {A : Type u₂} [Category.{v₂} A]

/-- Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
@[simps]
def pi (F : ∀ i, C i ⥤ D i) : (∀ i, C i) ⥤ ∀ i, D i where
  obj f i := (F i).obj (f i)
  map α i := (F i).map (α i)
#align category_theory.functor.pi CategoryTheory.Functor.pi

/-- Similar to `pi`, but all functors come from the same category `A`
-/
@[simps]
def pi' (f : ∀ i, A ⥤ C i) : A ⥤ ∀ i, C i where
  obj a i := (f i).obj a
  map h i := (f i).map h
#align category_theory.functor.pi' CategoryTheory.Functor.pi'

section EqToHom

@[simp]
theorem eqToHom_proj {x x' : ∀ i, C i} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (Function.funext_iff.mp h i) := by
  subst h
  rfl
#align category_theory.functor.eq_to_hom_proj CategoryTheory.Functor.eqToHom_proj

end EqToHom

-- One could add some natural isomorphisms showing
-- how `Functor.pi` commutes with `Pi.eval` and `Pi.comap`.
@[simp]
theorem pi'_eval (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙ Pi.eval C i = f i := by
  apply Functor.ext
  intro _ _ _
  · simp
  · intro _
    rfl
#align category_theory.functor.pi'_eval CategoryTheory.Functor.pi'_eval

/-- Two functors to a product category are equal iff they agree on every coordinate. -/
theorem pi_ext (f f' : A ⥤ ∀ i, C i) (h : ∀ i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i))
    : f = f' := by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    dsimp
    funext i
    specialize h i
    have := congr_hom h g
    simpa
#align category_theory.functor.pi_ext CategoryTheory.Functor.pi_ext

end Functor

namespace NatTrans

variable {C}

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps!]
def pi (α : ∀ i, F i ⟶ G i) : Functor.pi F ⟶ Functor.pi G where
  app f i := (α i).app (f i)
#align category_theory.nat_trans.pi CategoryTheory.NatTrans.pi

@[simps]
def pi' {E : Type _} [Category E] {F G : E ⥤ ∀ i, C i}
  (τ : ∀ i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i) : F ⟶ G :=
{ app := fun X i => (τ i).app X
  naturality := fun _ _ f => by
    ext i
    exact (τ i).naturality f }

end NatTrans

variable {C}

lemma isIso_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i, IsIso (f i) := by
  constructor
  . intro _ i
    exact IsIso.of_iso (Pi.isoApp (asIso f) i)
  . intro
    exact ⟨fun i => inv (f i), by aesop_cat, by aesop_cat⟩

namespace NatIso

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural isomorphisms into a single natural isomorphism.
-/
@[simps]
def pi (e : ∀ i, F i ≅ G i) : Functor.pi F ≅ Functor.pi G :=
{ hom := NatTrans.pi (fun i => (e i).hom)
  inv := NatTrans.pi (fun i => (e i).inv) }

@[simps]
def pi' {E : Type _} [Category E] {F G : E ⥤ ∀ i, C i}
  (e : ∀ i, F ⋙ Pi.eval C i ≅ G ⋙ Pi.eval C i) : F ≅ G :=
{ hom := NatTrans.pi' (fun i => (e i).hom)
  inv := NatTrans.pi' (fun i => (e i).inv) }

end NatIso

namespace Equivalence

variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

/-- Assemble an `I`-indexed family of equivalences of categories isomorphisms
into a single equivalence. -/
@[simps]
def pi (E : ∀ i, C i ≌ D i) :
  (∀ i, C i) ≌ (∀ i, D i) :=
{ functor := Functor.pi (fun i => (E i).functor)
  inverse := Functor.pi (fun i => (E i).inverse)
  unitIso := NatIso.pi (fun i => (E i).unitIso)
  counitIso := NatIso.pi (fun i => (E i).counitIso) }

instance (F : ∀ i, C i ⥤ D i) [∀ i, IsEquivalence (F i)] :
    IsEquivalence (Functor.pi F) :=
  IsEquivalence.ofEquivalence (pi (fun i => (F i).asEquivalence))

end Equivalence

section pi_option

variable (C' : Option J → Type u₁) [∀ i, Category.{v₁} (C' i)]
  (D' : Option J → Type u₂) [∀ i, Category.{v₂} (D' i)]

@[simps]
def pi_option_equivalence :
    (∀ i, C' i) ≌ C' none × (∀ (j : J), C' (some j)) :=
{ functor := Functor.prod' (Pi.eval C' none)
    (Functor.pi' (fun i => (Pi.eval _ (some i))))
  inverse := Functor.pi' (by
    rintro (_|i)
    . exact Prod.fst _ _
    . exact Prod.snd _ _ ⋙ (Pi.eval _ i))
  unitIso := by
    apply NatIso.pi'
    rintro (_|i) <;> apply Iso.refl
  counitIso := by exact Iso.refl _ }

end pi_option

/-- for a family of categories `C i` indexed by `I`, an equality `i = j` in `I` induces
an equivalence `C i ≌ C j`. -/
def Pi.equivalence_of_eq {I : Type u₂} (C : I → Type u₁)
  [∀ i, Category.{v₁} (C i)] {i j : I} (h : i = j) :
    C i ≌ C j := by
  subst h
  rfl

/-- when `i = j`, projections `Pi.eval C i` and `Pi.eval C j` are related by the equivalence
`Pi.equivalence_of_eq C h : C i ≌ C j`. -/
@[simp]
def Pi.eval_comp_equivalence_of_eq_functor {I : Type u₂} (C : I → Type u₁)
  [∀ i, Category.{v₁} (C i)] {i j : I} (h : i = j) :
  Pi.eval C i ⋙ (Pi.equivalence_of_eq C h).functor ≅
    Pi.eval C j := eqToIso (by subst h; rfl)

/-- the equivalences given by `Pi.equivalence_of_eq` are compatible with reindexing -/
@[simp]
def Pi.equivalence_of_eq_functor_iso {I : Type u₂} {I' : Type u₃}
  (C : I → Type u₁) [∀ i, Category.{v₁} (C i)] {i' j' : I'}
  (f : I' → I) (h : i' = j') :
    (Pi.equivalence_of_eq C (show f i' = f j' by rw [h])).functor ≅
      (Pi.equivalence_of_eq (fun i' => C (f i')) h).functor := eqToIso (by subst h; rfl)

/-- the projections of `Functor.pi' F` are isomorphic to the functors of the family `F` -/
@[simp]
def Functor.pi'_eval_iso {I : Type u₂} {C : I → Type u₁}
  [∀ i, Category.{v₁} (C i)] {A : Type u₄} [Category.{v₄} A]
  (F : ∀ i, A ⥤ C i) (i : I) : pi' F ⋙ Pi.eval C i ≅ F i :=
  eqToIso (Functor.pi'_eval _ _)

-- should be moved to Pi.Basic
/-- Reindexing a family of categories give two equivalent `Pi` categories -/
@[simps]
noncomputable def pi_equivalence_of_equiv {I : Type u₂} {I' : Type u₃} (C : I → Type u₁)
  [∀ i, Category.{v₁} (C i)] (e : I' ≃ I) :
  (∀ j, C (e j)) ≌ (∀ i, C i) :=
{ functor := Functor.pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.equivalence_of_eq C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => Functor.leftUnitor _ ≪≫
    (Pi.eval_comp_equivalence_of_eq_functor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
      isoWhiskerLeft _ ((Pi.equivalence_of_eq_functor_iso C e (e.symm_apply_apply i')).symm) ≪≫
      (Functor.pi'_eval_iso _ _).symm ≪≫ isoWhiskerLeft _ (Functor.pi'_eval_iso _ _).symm ≪≫
      (Functor.associator _ _ _).symm)
  counitIso := NatIso.pi' (fun i => (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.pi'_eval_iso _ _) _ ≪≫
    Pi.eval_comp_equivalence_of_eq_functor C (e.apply_symm_apply i) ≪≫
    (Functor.leftUnitor _).symm)
  functor_unitIso_comp := by
    intro
    ext
    dsimp
    simp [eqToHom_map] }

end CategoryTheory
