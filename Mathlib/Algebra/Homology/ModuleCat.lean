/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

#align_import algebra.homology.Module from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Complexes of modules

We provide some additional API to work with homological complexes in
`ModuleCat R`.
-/


universe v u

open scoped Classical

noncomputable section

open CategoryTheory Limits HomologicalComplex

variable {R : Type v} [Ring R]
variable {ι : Type*} {c : ComplexShape ι} {C D : HomologicalComplex (ModuleCat.{u} R) c}

namespace ModuleCat

/-- To prove that two maps out of a homology group are equal,
it suffices to check they are equal on the images of cycles.
-/
theorem homology'_ext {L M N K : ModuleCat.{u} R} {f : L ⟶ M} {g : M ⟶ N} (w : f ≫ g = 0)
    {h k : homology' f g w ⟶ K}
    (w :
      ∀ x : LinearMap.ker g,
        h (cokernel.π (imageToKernel _ _ w) (toKernelSubobject x)) =
          k (cokernel.π (imageToKernel _ _ w) (toKernelSubobject x))) :
    h = k := by
  refine Concrete.cokernel_funext fun n => ?_
  -- Porting note: as `equiv_rw` was not ported, it was replaced by `Equiv.surjective`
  -- Gosh it would be nice if `equiv_rw` could directly use an isomorphism, or an enriched `≃`.
  obtain ⟨n, rfl⟩ := (kernelSubobjectIso g ≪≫
    ModuleCat.kernelIsoKer g).toLinearEquiv.toEquiv.symm.surjective n
  exact w n
set_option linter.uppercaseLean3 false in
#align Module.homology_ext ModuleCat.homology'_ext

/-- Bundle an element `C.X i` such that `C.dFrom i x = 0` as a term of `C.cycles i`. -/
abbrev toCycles' {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    (x : LinearMap.ker (C.dFrom i)) : (C.cycles' i : Type u) :=
  toKernelSubobject x
set_option linter.uppercaseLean3 false in
#align Module.to_cycles ModuleCat.toCycles'

@[ext]
theorem cycles'_ext {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    {x y : (C.cycles' i : Type u)}
    (w : (C.cycles' i).arrow x = (C.cycles' i).arrow y) : x = y := by
  apply_fun (C.cycles' i).arrow using (ModuleCat.mono_iff_injective _).mp (cycles' C i).arrow_mono
  exact w
set_option linter.uppercaseLean3 false in
#align Module.cycles_ext ModuleCat.cycles'_ext

-- Porting note: both proofs by `rw` were proofs by `simp` which no longer worked
-- see https://github.com/leanprover-community/mathlib4/issues/5026
@[simp]
theorem cycles'Map_toCycles' (f : C ⟶ D) {i : ι} (x : LinearMap.ker (C.dFrom i)) :
    (cycles'Map f i) (toCycles' x) = toCycles' ⟨f.f i x.1, by
      -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
      rw [LinearMap.mem_ker]; erw [Hom.comm_from_apply, x.2, map_zero]⟩ := by
  ext
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [cycles'Map_arrow_apply, toKernelSubobject_arrow, toKernelSubobject_arrow]
  rfl
set_option linter.uppercaseLean3 false in
#align Module.cycles_map_to_cycles ModuleCat.cycles'Map_toCycles'

/-- Build a term of `C.homology i` from an element `C.X i` such that `C.d_from i x = 0`. -/
abbrev toHomology' {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    (x : LinearMap.ker (C.dFrom i)) : C.homology' i :=
  homology'.π (C.dTo i) (C.dFrom i) _ (toCycles' x)
set_option linter.uppercaseLean3 false in
#align Module.to_homology ModuleCat.toHomology'

@[ext]
theorem homology'_ext' {M : ModuleCat R} (i : ι) {h k : C.homology' i ⟶ M}
    (w : ∀ x : LinearMap.ker (C.dFrom i), h (toHomology' x) = k (toHomology' x)) : h = k := by
  apply homology'_ext _ w
set_option linter.uppercaseLean3 false in
#align Module.homology_ext' ModuleCat.homology'_ext'

-- Porting note: `erw` had to be used instead of `simp`
-- see https://github.com/leanprover-community/mathlib4/issues/5026
/-- We give an alternative proof of `homology'_map_eq_of_homotopy`,
specialized to the setting of `V = Module R`,
to demonstrate the use of extensionality lemmas for homology in `Module R`. -/
example (f g : C ⟶ D) (h : Homotopy f g) (i : ι) :
    (homology'Functor (ModuleCat.{u} R) c i).map f =
      (homology'Functor (ModuleCat.{u} R) c i).map g := by
  -- To check that two morphisms out of a homology group agree, it suffices to check on cycles:
  apply homology'_ext
  intro x
  simp only [homology'Functor_map]
  erw [homology'.π_map_apply, homology'.π_map_apply]
  -- To check that two elements are equal mod boundaries, it suffices to exhibit a boundary:
  refine cokernel_π_imageSubobject_ext _ _ ((toPrev i h.hom) x.1) ?_
  -- Moreover, to check that two cycles are equal, it suffices to check their underlying elements:
  ext
  erw [map_add, CategoryTheory.Limits.kernelSubobjectMap_arrow_apply,
    CategoryTheory.Limits.kernelSubobjectMap_arrow_apply,
    ModuleCat.toKernelSubobject_arrow, imageToKernel_arrow_apply, imageSubobject_arrow_comp_apply]
  rw [Hom.sqFrom_left, Hom.sqFrom_left, h.comm i]
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [LinearMap.add_apply]
  rw [LinearMap.add_apply, prevD_eq_toPrev_dTo, dNext_eq_dFrom_fromNext]
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [comp_apply, comp_apply]
  erw [x.2, map_zero]
  abel

end ModuleCat
