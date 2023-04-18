/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.homology.functor
! leanprover-community/mathlib commit 8e25bb6c1645bb80670e13848b79a54aa45cb84f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.HomologicalComplex

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

variable {ι : Type _} {c : ComplexShape ι}

/-- A complex of functors gives a functor to complexes. -/
@[simps obj map]
def asFunctor {T : Type _} [Category T] (C : HomologicalComplex (T ⥤ V) c) :
    T ⥤ HomologicalComplex V c
    where
  obj t :=
    { pt := fun i => (C.pt i).obj t
      d := fun i j => (C.d i j).app t
      d_comp_d' := fun i j k hij hjk => by
        have := C.d_comp_d i j k
        rw [nat_trans.ext_iff, Function.funext_iff] at this
        exact this t
      shape' := fun i j h => by
        have := C.shape _ _ h
        rw [nat_trans.ext_iff, Function.funext_iff] at this
        exact this t }
  map t₁ t₂ h :=
    { f := fun i => (C.pt i).map h
      comm' := fun i j hij => NatTrans.naturality _ _ }
  map_id' t := by
    ext i
    dsimp
    rw [(C.X i).map_id]
  map_comp' t₁ t₂ t₃ h₁ h₂ := by
    ext i
    dsimp
    rw [functor.map_comp]
#align homological_complex.as_functor HomologicalComplex.asFunctor

-- TODO in fact, this is an equivalence of categories.
/-- The functorial version of `homological_complex.as_functor`. -/
@[simps]
def complexOfFunctorsToFunctorToComplex {T : Type _} [Category T] :
    HomologicalComplex (T ⥤ V) c ⥤ T ⥤ HomologicalComplex V c
    where
  obj C := C.asFunctor
  map C D f :=
    { app := fun t =>
        { f := fun i => (f.f i).app t
          comm' := fun i j w => NatTrans.congr_app (f.comm i j) t }
      naturality' := fun t t' g => by
        ext i
        exact (f.f i).naturality g }
#align homological_complex.complex_of_functors_to_functor_to_complex HomologicalComplex.complexOfFunctorsToFunctorToComplex

end HomologicalComplex

