import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

universe w v v' v'' u u' u''

namespace CategoryTheory

open Limits Opposite AlgebraicTopology

variable {C : Type u} [Category.{v} C] (J : Type u') [Category.{v'} J]
  (A : Type u'') [Category.{v''} A]

variable [∀ (I : Type w), HasProductsOfShape I A]

variable (C) in
structure FormalCoproduct where
  I : Type w
  obj (i : I) : C

namespace FormalCoproduct

structure Hom (X Y : FormalCoproduct.{w} C) where
  f : X.I → Y.I
  φ (i : X.I) : X.obj i ⟶ Y.obj (f i)

-- this category identifies to the fullsubcategory of the category of
-- presheaves of sets on `C` which are coproducts of representable presheaves
@[simps!] instance category : Category (FormalCoproduct.{w} C) where
  Hom := Hom
  id X := { f := id, φ := fun _ ↦ 𝟙 _ }
  comp α β := { f := β.f ∘ α.f, φ := fun _ ↦ α.φ _ ≫ β.φ _ }

@[ext]
lemma hom_ext {X Y : FormalCoproduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f)
    (h₂ : ∀ (i : X.I), f.φ i ≫ eqToHom (by rw [h₁]) = g.φ i): f = g := by
  sorry

@[simps] noncomputable def eval (X : FormalCoproduct.{w} C) : (Cᵒᵖ ⥤ A) ⥤ A where
  obj F := ∏ᶜ (fun (i : X.I) ↦ F.obj (op (X.obj i)))
  map α := Pi.map (fun _ ↦ α.app _)

variable (C)

@[simps] noncomputable def evalFunctor : (FormalCoproduct.{w} C)ᵒᵖ ⥤ (Cᵒᵖ ⥤ A) ⥤ A where
  obj X := X.unop.eval A
  map {X Y} π :=
    { app := fun F ↦ Pi.map' π.unop.f (fun i ↦ F.map (π.unop.φ i).op) }

noncomputable def evalFunctor' : (Jᵒᵖ ⥤ FormalCoproduct.{w} C)ᵒᵖ ⥤ (Cᵒᵖ ⥤ A) ⥤ (J ⥤ A) :=
  ((evalFunctor C A).flip ⋙ whiskeringRight J (FormalCoproduct C)ᵒᵖ A ⋙
    (whiskeringLeft _ _ _).obj ((Functor.leftOpRightOpEquiv _ _).functor)).flip

noncomputable abbrev simplicialEvalFunctor : (SimplicialObject (FormalCoproduct.{w} C))ᵒᵖ ⥤
    (Cᵒᵖ ⥤ A) ⥤ CosimplicialObject A :=
  evalFunctor' C SimplexCategory A

noncomputable abbrev cochainComplexFunctor [Preadditive A] :
    (SimplicialObject (FormalCoproduct.{w} C))ᵒᵖ ⥤
      (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  simplicialEvalFunctor C A ⋙ (whiskeringRight _ _ _).obj (alternatingCofaceMapComplex A)

-- this is a variant of `cechNerve`
variable {C} in
noncomputable def cechSimplicial {I : Type w} (U : I → C) [HasFiniteProducts C] :
    SimplicialObject (FormalCoproduct C) where
  obj := fun Δ ↦
    { I := Fin (Δ.unop.len + 1) → I
      obj := fun a ↦ ∏ᶜ (fun x ↦ U (a x)) }
  map {Δ Δ'} f :=
    { f := fun a x ↦ a (f.unop.toOrderHom x)
      φ := fun a ↦ Pi.map' (fun x ↦ f.unop.toOrderHom x) (fun x ↦ 𝟙 _) }
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

end FormalCoproduct

noncomputable def cechComplexFunctor {I : Type w} (U : I → C)
    [HasFiniteProducts C] [Preadditive A] :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  (FormalCoproduct.cochainComplexFunctor.{w} C A).obj (op (FormalCoproduct.cechSimplicial U))

-- apply this to a family of objects `U : I → C` which satisfies `J.CoversTop U` for
-- a Grothendieck topology, or if `X : C` and we have a covering family of arrows
--  `f i : U i ⟶ X` identified as a family of objects in `Over X`.

-- next step: show that if `V` refines `U`, then two refinements induce homotopic maps

end CategoryTheory
