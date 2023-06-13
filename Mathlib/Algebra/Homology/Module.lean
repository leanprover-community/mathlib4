/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module algebra.homology.Module
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Homology.Homotopy
import Mathbin.Algebra.Category.Module.Abelian
import Mathbin.Algebra.Category.Module.Subobject
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# Complexes of modules

We provide some additional API to work with homological complexes in `Module R`.
-/


universe v u

open scoped Classical

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {R : Type v} [Ring R]

variable {ι : Type _} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{u} R) c}

namespace ModuleCat

/-- To prove that two maps out of a homology group are equal,
it suffices to check they are equal on the images of cycles.
-/
theorem homology_ext {L M N K : ModuleCat R} {f : L ⟶ M} {g : M ⟶ N} (w : f ≫ g = 0)
    {h k : homology f g w ⟶ K}
    (w :
      ∀ x : LinearMap.ker g,
        h (cokernel.π (imageToKernel _ _ w) (toKernelSubobject x)) =
          k (cokernel.π (imageToKernel _ _ w) (toKernelSubobject x))) :
    h = k := by
  refine' cokernel_funext fun n => _
  -- Gosh it would be nice if `equiv_rw` could directly use an isomorphism, or an enriched `≃`.
  equiv_rw (kernel_subobject_iso g ≪≫ ModuleCat.kernelIsoKer g).toLinearEquiv.toEquiv at n 
  convert w n <;> simp [to_kernel_subobject]
#align Module.homology_ext ModuleCat.homology_ext

/-- Bundle an element `C.X i` such that `C.d_from i x = 0` as a term of `C.cycles i`. -/
abbrev toCycles {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    (x : LinearMap.ker (C.dFrom i)) : C.cycles i :=
  toKernelSubobject x
#align Module.to_cycles ModuleCat.toCycles

@[ext]
theorem cycles_ext {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι} {x y : C.cycles i}
    (w : (C.cycles i).arrow x = (C.cycles i).arrow y) : x = y :=
  by
  apply_fun (C.cycles i).arrow using (ModuleCat.mono_iff_injective _).mp (cycles C i).arrow_mono
  exact w
#align Module.cycles_ext ModuleCat.cycles_ext

attribute [local instance] concrete_category.has_coe_to_sort

@[simp]
theorem cyclesMap_toCycles (f : C ⟶ D) {i : ι} (x : LinearMap.ker (C.dFrom i)) :
    (cyclesMap f i) (toCycles x) = toCycles ⟨f.f i x.1, by simp [x.2]⟩ := by ext; simp
#align Module.cycles_map_to_cycles ModuleCat.cyclesMap_toCycles

/-- Build a term of `C.homology i` from an element `C.X i` such that `C.d_from i x = 0`. -/
abbrev toHomology {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    (x : LinearMap.ker (C.dFrom i)) : C.homology i :=
  homology.π (C.dTo i) (C.dFrom i) _ (toCycles x)
#align Module.to_homology ModuleCat.toHomology

@[ext]
theorem homology_ext' {M : ModuleCat R} (i : ι) {h k : C.homology i ⟶ M}
    (w : ∀ x : LinearMap.ker (C.dFrom i), h (toHomology x) = k (toHomology x)) : h = k :=
  homology_ext _ w
#align Module.homology_ext' ModuleCat.homology_ext'

/-- We give an alternative proof of `homology_map_eq_of_homotopy`,
specialized to the setting of `V = Module R`,
to demonstrate the use of extensionality lemmas for homology in `Module R`. -/
example (f g : C ⟶ D) (h : Homotopy f g) (i : ι) :
    (homologyFunctor (ModuleCat.{u} R) c i).map f = (homologyFunctor (ModuleCat.{u} R) c i).map g :=
  by
  -- To check that two morphisms out of a homology group agree, it suffices to check on cycles:
  ext
  simp only [homologyFunctor_map, homology.π_map_apply]
  -- To check that two elements are equal mod boundaries, it suffices to exhibit a boundary:
  ext1
  swap; exact (toPrev i h.hom) x.1
  -- Moreover, to check that two cycles are equal, it suffices to check their underlying elements:
  ext1
  simp only [map_add, imageToKernel_arrow_apply, HomologicalComplex.Hom.sqFrom_left,
    ModuleCat.toKernelSubobject_arrow, CategoryTheory.Limits.kernelSubobjectMap_arrow_apply,
    dNext_eq_dFrom_fromNext, Function.comp_apply, zero_add, ModuleCat.coe_comp, LinearMap.add_apply,
    map_zero, Subtype.val_eq_coe, CategoryTheory.Limits.imageSubobject_arrow_comp_apply,
    LinearMap.map_coe_ker, prevD_eq_toPrev_dTo, h.comm i, x.2]
  abel

end ModuleCat

