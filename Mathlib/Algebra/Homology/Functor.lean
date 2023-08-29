/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Homology.HomologicalComplex

#align_import algebra.homology.functor from "leanprover-community/mathlib"@"8e25bb6c1645bb80670e13848b79a54aa45cb84f"

/-!
# Complexes in functor categories

We can view a complex valued in a functor category `T ⥤ V` as
a functor from `T` to complexes valued in `V`.

## Future work
In fact this is an equivalence of categories.

-/


universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace HomologicalComplex

variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

variable {ι : Type*} {c : ComplexShape ι}

/-- A complex of functors gives a functor to complexes. -/
@[simps obj map]
def asFunctor {T : Type*} [Category T] (C : HomologicalComplex (T ⥤ V) c) :
    T ⥤ HomologicalComplex V c where
  obj t :=
    { X := fun i => (C.X i).obj t
      d := fun i j => (C.d i j).app t
      d_comp_d' := fun i j k _ _ => by
        have := C.d_comp_d i j k
        -- ⊢ (fun i j => NatTrans.app (d C i j) t) i j ≫ (fun i j => NatTrans.app (d C i  …
        rw [NatTrans.ext_iff, Function.funext_iff] at this
        -- ⊢ (fun i j => NatTrans.app (d C i j) t) i j ≫ (fun i j => NatTrans.app (d C i  …
        exact this t
        -- ⊢ (fun i j => NatTrans.app (d C i j) t) i j = 0
        -- 🎉 no goals
        -- ⊢ (fun i j => NatTrans.app (d C i j) t) i j = 0
      shape := fun i j h => by
        -- 🎉 no goals
        have := C.shape _ _ h
        rw [NatTrans.ext_iff, Function.funext_iff] at this
        exact this t }
  map h :=
    { f := fun i => (C.X i).map h
      comm' := fun i j _ => NatTrans.naturality _ _ }
  map_id t := by
    ext i
    -- ⊢ Hom.f ({ obj := fun t => mk (fun i => (X C i).obj t) fun i j => NatTrans.app …
    dsimp
    -- ⊢ (X C i).map (𝟙 t) = 𝟙 ((X C i).obj t)
    rw [(C.X i).map_id]
    -- 🎉 no goals
  map_comp h₁ h₂ := by
    ext i
    -- ⊢ Hom.f ({ obj := fun t => mk (fun i => (X C i).obj t) fun i j => NatTrans.app …
    dsimp
    -- ⊢ (X C i).map (h₁ ≫ h₂) = (X C i).map h₁ ≫ (X C i).map h₂
    rw [Functor.map_comp]
    -- 🎉 no goals
#align homological_complex.as_functor HomologicalComplex.asFunctor

-- TODO in fact, this is an equivalence of categories.
/-- The functorial version of `HomologicalComplex.asFunctor`. -/
@[simps]
def complexOfFunctorsToFunctorToComplex {T : Type*} [Category T] :
    HomologicalComplex (T ⥤ V) c ⥤ T ⥤ HomologicalComplex V c where
  obj C := C.asFunctor
  map f :=
    { app := fun t =>
        { f := fun i => (f.f i).app t
          comm' := fun i j _ => NatTrans.congr_app (f.comm i j) t }
      naturality := fun t t' g => by
        ext i
        -- ⊢ Hom.f (((fun C => asFunctor C) X✝).map g ≫ (fun t => Hom.mk fun i => NatTran …
        exact (f.f i).naturality g }
        -- 🎉 no goals
#align homological_complex.complex_of_functors_to_functor_to_complex HomologicalComplex.complexOfFunctorsToFunctorToComplex

end HomologicalComplex
