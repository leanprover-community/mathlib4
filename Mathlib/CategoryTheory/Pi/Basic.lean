/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Kim Morrison
-/
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Products.Basic

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

namespace CategoryTheory

universe w₀ w₁ w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {I : Type w₀} {J : Type w₁} (C : I → Type u₁) [∀ i, Category.{v₁} (C i)]


/-- `pi C` gives the cartesian product of an indexed family of categories.
-/
instance pi : Category.{max w₀ v₁} (∀ i, C i) where
  Hom X Y := ∀ i, X i ⟶ Y i
  id X i := 𝟙 (X i)
  comp f g i := f i ≫ g i

namespace Pi

@[simp]
theorem id_apply (X : ∀ i, C i) (i) : (𝟙 X : ∀ i, X i ⟶ X i) i = 𝟙 (X i) :=
  rfl

@[simp]
theorem comp_apply {X Y Z : ∀ i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
    (f ≫ g : ∀ i, X i ⟶ Z i) i = f i ≫ g i :=
  rfl

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

variable (I)

/-- The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
def comapId : comap C (id : I → I) ≅ 𝟭 (∀ i, C i) where
  hom := { app := fun X => 𝟙 X }
  inv := { app := fun X => 𝟙 X }

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

/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
@[simps!]
def comapEvalIsoEval (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by simp only [Iso.refl]; simp)

end

section

variable {J : Type w₀} {D : J → Type u₁} [∀ j, Category.{v₁} (D j)]

/- Porting note: maybe mixing up universes -/
instance sumElimCategory : ∀ s : I ⊕ J, Category.{v₁} (Sum.elim C D s)
  | Sum.inl i => by
    dsimp
    infer_instance
  | Sum.inr j => by
    dsimp
    infer_instance

/- Porting note: replaced `Sum.rec` with `match`'s per the error about
current state of code generation -/

/-- The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simps]
def sum : (∀ i, C i) ⥤ (∀ j, D j) ⥤ ∀ s : I ⊕ J, Sum.elim C D s where
  obj X :=
    { obj := fun Y s =>
        match s with
        | .inl i => X i
        | .inr j => Y j
      map := fun {_} {_} f s =>
        match s with
        | .inl i => 𝟙 (X i)
        | .inr j => f j }
  map {X} {X'} f :=
    { app := fun Y s =>
        match s with
        | .inl i => f i
        | .inr j => 𝟙 (Y j) }

end

variable {C}

/-- An isomorphism between `I`-indexed objects gives an isomorphism between each
pair of corresponding components. -/
@[simps]
def isoApp {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : X i ≅ Y i :=
  ⟨f.hom i, f.inv i,
    by rw [← comp_apply, Iso.hom_inv_id, id_apply], by rw [← comp_apply, Iso.inv_hom_id, id_apply]⟩

@[simp]
theorem isoApp_refl (X : ∀ i, C i) (i : I) : isoApp (Iso.refl X) i = Iso.refl (X i) :=
  rfl

@[simp]
theorem isoApp_symm {X Y : ∀ i, C i} (f : X ≅ Y) (i : I) : isoApp f.symm i = (isoApp f i).symm :=
  rfl

@[simp]
theorem isoApp_trans {X Y Z : ∀ i, C i} (f : X ≅ Y) (g : Y ≅ Z) (i : I) :
    isoApp (f ≪≫ g) i = isoApp f i ≪≫ isoApp g i :=
  rfl

end Pi

namespace Functor

variable {C}
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)] {A : Type u₃} [Category.{v₃} A]

/-- Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
@[simps]
def pi (F : ∀ i, C i ⥤ D i) : (∀ i, C i) ⥤ ∀ i, D i where
  obj f i := (F i).obj (f i)
  map α i := (F i).map (α i)

/-- Similar to `pi`, but all functors come from the same category `A`
-/
@[simps]
def pi' (f : ∀ i, A ⥤ C i) : A ⥤ ∀ i, C i where
  obj a i := (f i).obj a
  map h i := (f i).map h

/-- The projections of `Functor.pi' F` are isomorphic to the functors of the family `F` -/
@[simps!]
def pi'CompEval {A : Type*} [Category A] (F : ∀ i, A ⥤ C i) (i : I) :
    pi' F ⋙ Pi.eval C i ≅ F i :=
  Iso.refl _

section EqToHom

@[simp]
theorem eqToHom_proj {x x' : ∀ i, C i} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i) := by
  subst h
  rfl

end EqToHom

-- One could add some natural isomorphisms showing
-- how `Functor.pi` commutes with `Pi.eval` and `Pi.comap`.
@[simp]
theorem pi'_eval (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙ Pi.eval C i = f i := by
  apply Functor.ext
  · intro _ _ _
    simp
  · intro _
    rfl

/-- Two functors to a product category are equal iff they agree on every coordinate. -/
theorem pi_ext (f f' : A ⥤ ∀ i, C i) (h : ∀ i, f ⋙ (Pi.eval C i) = f' ⋙ (Pi.eval C i)) :
    f = f' := by
  apply Functor.ext; rotate_left
  · intro X
    ext i
    specialize h i
    have := congr_obj h X
    simpa
  · intro X Y g
    funext i
    specialize h i
    have := congr_hom h g
    simpa

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

/-- Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps]
def pi' {E : Type*} [Category E] {F G : E ⥤ ∀ i, C i}
    (τ : ∀ i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i) : F ⟶ G where
  app := fun X i => (τ i).app X
  naturality _ _ f := by
    ext i
    exact (τ i).naturality f

end NatTrans

namespace NatIso

variable {C}
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]
variable {F G : ∀ i, C i ⥤ D i}

/-- Assemble an `I`-indexed family of natural isomorphisms into a single natural isomorphism.
-/
@[simps]
def pi (e : ∀ i, F i ≅ G i) : Functor.pi F ≅ Functor.pi G where
  hom := NatTrans.pi (fun i => (e i).hom)
  inv := NatTrans.pi (fun i => (e i).inv)

/-- Assemble an `I`-indexed family of natural isomorphisms into a single natural isomorphism.
-/
@[simps]
def pi' {E : Type*} [Category E] {F G : E ⥤ ∀ i, C i}
    (e : ∀ i, F ⋙ Pi.eval C i ≅ G ⋙ Pi.eval C i) : F ≅ G where
  hom := NatTrans.pi' (fun i => (e i).hom)
  inv := NatTrans.pi' (fun i => (e i).inv)

end NatIso

variable {C}

lemma isIso_pi_iff {X Y : ∀ i, C i} (f : X ⟶ Y) :
    IsIso f ↔ ∀ i, IsIso (f i) := by
  constructor
  · intro _ i
    exact (Pi.isoApp (asIso f) i).isIso_hom
  · intro
    exact ⟨fun i => inv (f i), by aesop_cat, by aesop_cat⟩

variable (C)

/-- For a family of categories `C i` indexed by `I`, an equality `i = j` in `I` induces
an equivalence `C i ≌ C j`. -/
def Pi.eqToEquivalence {i j : I} (h : i = j) : C i ≌ C j := by subst h; rfl

/-- When `i = j`, projections `Pi.eval C i` and `Pi.eval C j` are related by the equivalence
`Pi.eqToEquivalence C h : C i ≌ C j`. -/
@[simps!]
def Pi.evalCompEqToEquivalenceFunctor {i j : I} (h : i = j) :
    Pi.eval C i ⋙ (Pi.eqToEquivalence C h).functor ≅
      Pi.eval C j :=
  eqToIso (by subst h; rfl)

/-- The equivalences given by `Pi.eqToEquivalence` are compatible with reindexing. -/
@[simps!]
def Pi.eqToEquivalenceFunctorIso (f : J → I) {i' j' : J} (h : i' = j') :
    (Pi.eqToEquivalence C (congr_arg f h)).functor ≅
      (Pi.eqToEquivalence (fun i' => C (f i')) h).functor :=
  eqToIso (by subst h; rfl)

attribute [local simp] eqToHom_map

/-- Reindexing a family of categories gives equivalent `Pi` categories. -/
@[simps]
noncomputable def Pi.equivalenceOfEquiv (e : J ≃ I) :
    (∀ j, C (e j)) ≌ (∀ i, C i) where
  functor := Functor.pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.eqToEquivalence C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => Functor.leftUnitor _ ≪≫
    (Pi.evalCompEqToEquivalenceFunctor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
    isoWhiskerLeft _ ((Pi.eqToEquivalenceFunctorIso C e (e.symm_apply_apply i')).symm) ≪≫
    (Functor.pi'CompEval _ _).symm ≪≫ isoWhiskerLeft _ (Functor.pi'CompEval _ _).symm ≪≫
    (Functor.associator _ _ _).symm)
  counitIso := NatIso.pi' (fun i => (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.pi'CompEval _ _) _ ≪≫
    Pi.evalCompEqToEquivalenceFunctor C (e.apply_symm_apply i) ≪≫
    (Functor.leftUnitor _).symm)

/-- A product of categories indexed by `Option J` identifies to a binary product. -/
@[simps]
def Pi.optionEquivalence (C' : Option J → Type u₁) [∀ i, Category.{v₁} (C' i)] :
    (∀ i, C' i) ≌ C' none × (∀ (j : J), C' (some j)) where
  functor := Functor.prod' (Pi.eval C' none)
    (Functor.pi' (fun i => (Pi.eval _ (some i))))
  inverse := Functor.pi' (fun i => match i with
    | none => Prod.fst _ _
    | some i => Prod.snd _ _ ⋙ (Pi.eval _ i))
  unitIso := NatIso.pi' (fun i => match i with
    | none => Iso.refl _
    | some _ => Iso.refl _)
  counitIso := by exact Iso.refl _

namespace Equivalence

variable {C}
variable {D : I → Type u₂} [∀ i, Category.{v₂} (D i)]

/-- Assemble an `I`-indexed family of equivalences of categories
into a single equivalence. -/
@[simps]
def pi (E : ∀ i, C i ≌ D i) : (∀ i, C i) ≌ (∀ i, D i) where
  functor := Functor.pi (fun i => (E i).functor)
  inverse := Functor.pi (fun i => (E i).inverse)
  unitIso := NatIso.pi (fun i => (E i).unitIso)
  counitIso := NatIso.pi (fun i => (E i).counitIso)

instance (F : ∀ i, C i ⥤ D i) [∀ i, (F i).IsEquivalence] :
    (Functor.pi F).IsEquivalence :=
  (pi (fun i => (F i).asEquivalence)).isEquivalence_functor

end Equivalence

end CategoryTheory
