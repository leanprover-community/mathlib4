/-
Copyright (c) 2026 Jingting Wang, Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.RingTheory.KoszulComplex.Complex
public import Mathlib.RingTheory.KoszulComplex.Cocomplex
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.Abelian.Ext

/-!
# The dual relation of Koszul complex and cocomplex

In this file, we prove the dual relation between Koszul complex and cocomplex.
-/

#check ComplexShape.Embedding.extendFunctor
set_option pp.universes true in
#check ChainComplex.linearYonedaObj
-- #loogle ComplexShape.Embedding

@[expose] public section

universe u v

open CategoryTheory Functor

/- `M`is set to be `Type u` to make universe problems easier. -/
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (x : M)



-- #check (koszulCocomplex R x).linearYonedaObj R (ModuleCat.of R R)
