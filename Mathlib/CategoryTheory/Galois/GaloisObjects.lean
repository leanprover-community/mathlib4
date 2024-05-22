/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.Logic.Equiv.TransferInstance

/-!
# Galois objects in Galois categories

We define when a connected object of a Galois category `C` is Galois in a fiber functor independent
way and show equivalent characterisations.

## Main definitions

* `IsGalois` : Connected object `X` of `C` such that `X / Aut X` is terminal.

## Main results

* `galois_iff_pretransitive` : A connected object `X` is Galois if and only if `Aut X`
                               acts transitively on `F.obj X` for a fiber functor `F`.

-/
universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

noncomputable instance {G : Type v} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) FintypeCat.incl.{w} := by
  choose G' hg hf e using Finite.exists_type_zero_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShapeOfEquiv (Classical.choice e).toSingleObjEquiv.symm _

/-- A connected object `X` of `C` is Galois if the quotient `X / Aut X` is terminal. -/
class IsGalois {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C)
    extends IsConnected X : Prop where
  quotientByAutTerminal : Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X)

variable {C : Type u₁} [Category.{u₂, u₁} C]

/-- The natural action of `Aut X` on `F.obj X`. -/
instance autMulFiber (F : C ⥤ FintypeCat.{w}) (X : C) : MulAction (Aut X) (F.obj X) where
  smul σ a := F.map σ.hom a
  one_smul a := by
    show F.map (𝟙 X) a = a
    simp only [map_id, FintypeCat.id_apply]
  mul_smul g h a := by
    show F.map (h.hom ≫ g.hom) a = (F.map h.hom ≫ F.map g.hom) a
    simp only [map_comp, FintypeCat.comp_apply]

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- For a connected object `X` of `C`, the quotient `X / Aut X` is terminal if and only if
the quotient `F.obj X / Aut X` has exactly one element. -/
noncomputable def quotientByAutTerminalEquivUniqueQuotient
    (X : C) [IsConnected X] :
    IsTerminal (colimit <| SingleObj.functor <| Aut.toEnd X) ≃
    Unique (MulAction.orbitRel.Quotient (Aut X) (F.obj X)) := by
  let J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  let e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  · apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
      (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _

lemma isGalois_iff_aux (X : C) [IsConnected X] :
    IsGalois X ↔ Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X) :=
  ⟨fun h ↦ h.quotientByAutTerminal, fun h ↦ ⟨h⟩⟩

/-- Given a fiber functor `F` and a connected object `X` of `C`. Then `X` is Galois if and only if
the natural action of `Aut X` on `F.obj X` is transitive. -/
theorem isGalois_iff_pretransitive (X : C) [IsConnected X] :
    IsGalois X ↔ MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [isGalois_iff_aux, Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm

/-- If `X` is Galois, the quotient `X / Aut X` is terminal.  -/
noncomputable def isTerminalQuotientOfIsGalois (X : C) [IsGalois X] :
    IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X :=
  Nonempty.some IsGalois.quotientByAutTerminal

/-- If `X` is Galois, then the action of `Aut X` on `F.obj X` is
transitive for every fiber functor `F`. -/
instance isPretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [← isGalois_iff_pretransitive]
  infer_instance

theorem evaluation_aut_surjective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Surjective (fun f : Aut A ↦ F.map f.hom a) :=
  MulAction.IsPretransitive.exists_smul_eq a

theorem evaluation_aut_bijective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Bijective (fun f : Aut A ↦ F.map f.hom a) :=
  ⟨evaluation_aut_injective_of_isConnected F A a, evaluation_aut_surjective_of_isGalois F A a⟩

/-- For Galois `A` and a point `a` of the fiber of `A`, the evaluation at `A` as an equivalence. -/
noncomputable def evaluationEquivOfIsGalois (A : C) [IsGalois A] (a : F.obj A) : Aut A ≃ F.obj A :=
  Equiv.ofBijective _ (evaluation_aut_bijective_of_isGalois F A a)

@[simp]
lemma evaluationEquivOfIsGalois_apply (A : C) [IsGalois A] (a : F.obj A) (φ : Aut A) :
    evaluationEquivOfIsGalois F A a φ = F.map φ.hom a :=
  rfl

@[simp]
lemma evaluationEquivOfIsGalois_symm_fiber (A : C) [IsGalois A] (a b : F.obj A) :
    F.map ((evaluationEquivOfIsGalois F A a).symm b).hom a = b := by
  change (evaluationEquivOfIsGalois F A a) _ = _
  simp

section AutMap

/-- For a morphism from a connected object `A` to a Galois object `B` and an automorphism
of `A`, there exists a unique automorphism of `B` making the canonical diagram commute. -/
lemma exists_autMap {A B : C} (f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut A) :
    ∃! (τ : Aut B), f ≫ τ.hom = σ.hom ≫ f := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  refine ⟨?_, ?_, ?_⟩
  · exact (evaluationEquivOfIsGalois F B (F.map f a)).symm (F.map (σ.hom ≫ f) a)
  · apply evaluation_injective_of_isConnected F A B a
    simp
  · intro τ hτ
    apply evaluation_aut_injective_of_isConnected F B (F.map f a)
    simpa using congr_fun (F.congr_map hτ) a

/-- A morphism from a connected object to a Galois object induces a map on automorphism
groups. This is a group homomorphism (see `autMapHom`). -/
noncomputable def autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) :
    Aut B :=
  (exists_autMap f σ).choose

@[simp]
lemma comp_autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) :
    f ≫ (autMap f σ).hom = σ.hom ≫ f :=
  (exists_autMap f σ).choose_spec.left

@[simp]
lemma comp_autMap_apply {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
    (a : F.obj A) :
    F.map (autMap f σ).hom (F.map f a) = F.map f (F.map σ.hom a) := by
  simpa [-comp_autMap] using congrFun (F.congr_map (comp_autMap f σ)) a

/-- `autMap` is uniquely characterized by making the canonical diagram commute. -/
lemma autMap_unique {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
    (τ : Aut B) (h : f ≫ τ.hom = σ.hom ≫ f) :
    autMap f σ = τ :=
  ((exists_autMap f σ).choose_spec.right τ h).symm

@[simp]
lemma autMap_id {A : C} [IsGalois A] : autMap (𝟙 A) = id :=
  funext fun σ ↦ autMap_unique (𝟙 A) σ _ (by simp)

@[simp]
lemma autMap_comp {X Y Z : C} [IsConnected X] [IsGalois Y] [IsGalois Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) : autMap (f ≫ g) = autMap g ∘ autMap f := by
  refine funext fun σ ↦ autMap_unique _ σ _ ?_
  rw [Function.comp_apply, Category.assoc, comp_autMap, ← Category.assoc]
  simp

/-- `autMap` is surjective, if the source is also Galois. -/
lemma autMap_surjective_of_isGalois {A B : C} [IsGalois A] [IsGalois B] (f : A ⟶ B) :
    Function.Surjective (autMap f) := by
  intro σ
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f (F.map σ.hom (F.map f a))
  obtain ⟨τ, (hτ : F.map τ.hom a = a')⟩ := MulAction.exists_smul_eq (Aut A) a a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B (F.map f a)
  simp [hτ, ha']

@[simp]
lemma autMap_apply_mul {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ τ : Aut A) :
    autMap f (σ * τ) = autMap f σ * autMap f τ := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply evaluation_aut_injective_of_isConnected F (B : C) (F.map f a)
  simp [Aut.Aut_mul_def]

/-- `MonoidHom` version of `autMap`. -/
@[simps!]
noncomputable def autMapHom {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) :
     Aut A →* Aut B :=
  MonoidHom.mk' (autMap f) (autMap_apply_mul f)

end AutMap

end PreGaloisCategory

end CategoryTheory
