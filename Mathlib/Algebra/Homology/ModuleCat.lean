/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Limits.ConcreteCategory

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
theorem homology_ext {L M N K : ModuleCat R} {f : L ⟶ M} {g : M ⟶ N} (w : f ≫ g = 0)
    {h k : homology f g w ⟶ K}
    (w :
      ∀ x : LinearMap.ker g,
        h (cokernel.π (imageToKernel _ _ w) (toKernelSubobject x)) =
          k (cokernel.π (imageToKernel _ _ w) (toKernelSubobject x))) :
    h = k := by
  refine' cokernel_funext fun n => _
  -- ⊢ ↑h (↑(cokernel.π (imageToKernel f g w✝)) n) = ↑k (↑(cokernel.π (imageToKerne …
  -- porting note: as `equiv_rw` was not ported, it was replaced by `Equiv.surjective`
  -- Gosh it would be nice if `equiv_rw` could directly use an isomorphism, or an enriched `≃`.
  obtain ⟨n, rfl⟩ := (kernelSubobjectIso g ≪≫
    ModuleCat.kernelIsoKer g).toLinearEquiv.toEquiv.symm.surjective n
  exact w n
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Module.homology_ext ModuleCat.homology_ext

/-- Bundle an element `C.X i` such that `C.dFrom i x = 0` as a term of `C.cycles i`. -/
abbrev toCycles {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    (x : LinearMap.ker (C.dFrom i)) : (C.cycles i : Type u) :=
  toKernelSubobject x
set_option linter.uppercaseLean3 false in
#align Module.to_cycles ModuleCat.toCycles

@[ext]
theorem cycles_ext {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    {x y : (C.cycles i : Type u)}
    (w : (C.cycles i).arrow x = (C.cycles i).arrow y) : x = y := by
  apply_fun (C.cycles i).arrow using (ModuleCat.mono_iff_injective _).mp (cycles C i).arrow_mono
  -- ⊢ ↑(Subobject.arrow (cycles C i)) x = ↑(Subobject.arrow (cycles C i)) y
  exact w
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Module.cycles_ext ModuleCat.cycles_ext

-- porting note: both proofs by `rw` were proofs by `simp` which no longer worked
-- see https://github.com/leanprover-community/mathlib4/issues/5026
@[simp]
theorem cyclesMap_toCycles (f : C ⟶ D) {i : ι} (x : LinearMap.ker (C.dFrom i)) :
    (cyclesMap f i) (toCycles x) = toCycles ⟨f.f i x.1, by
      rw [LinearMap.mem_ker, Hom.comm_from_apply, x.2, map_zero]⟩ := by
      -- 🎉 no goals
  ext
  -- ⊢ ↑(Subobject.arrow (cycles D i)) (↑(cyclesMap f i) (toCycles x)) = ↑(Subobjec …
  rw [cyclesMap_arrow_apply, toKernelSubobject_arrow, toKernelSubobject_arrow]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Module.cycles_map_to_cycles ModuleCat.cyclesMap_toCycles

/-- Build a term of `C.homology i` from an element `C.X i` such that `C.d_from i x = 0`. -/
abbrev toHomology {C : HomologicalComplex (ModuleCat.{u} R) c} {i : ι}
    (x : LinearMap.ker (C.dFrom i)) : C.homology i :=
  homology.π (C.dTo i) (C.dFrom i) _ (toCycles x)
set_option linter.uppercaseLean3 false in
#align Module.to_homology ModuleCat.toHomology

@[ext]
theorem homology_ext' {M : ModuleCat R} (i : ι) {h k : C.homology i ⟶ M}
    (w : ∀ x : LinearMap.ker (C.dFrom i), h (toHomology x) = k (toHomology x)) : h = k :=
  homology_ext _ w
set_option linter.uppercaseLean3 false in
#align Module.homology_ext' ModuleCat.homology_ext'

set_option maxHeartbeats 400000 in
-- porting note: `erw` had to be used instead of `simp`
-- see https://github.com/leanprover-community/mathlib4/issues/5026
/-- We give an alternative proof of `homology_map_eq_of_homotopy`,
specialized to the setting of `V = Module R`,
to demonstrate the use of extensionality lemmas for homology in `Module R`. -/
example (f g : C ⟶ D) (h : Homotopy f g) (i : ι) :
    (homologyFunctor (ModuleCat.{u} R) c i).map f =
      (homologyFunctor (ModuleCat.{u} R) c i).map g := by
  -- To check that two morphisms out of a homology group agree, it suffices to check on cycles:
  apply homology_ext
  -- ⊢ ∀ (x : { x // x ∈ LinearMap.ker (dFrom C i) }), ↑((homologyFunctor (ModuleCa …
  intro x
  -- ⊢ ↑((homologyFunctor (ModuleCat R) c i).map f) (↑(cokernel.π (imageToKernel (d …
  simp only [homologyFunctor_map]
  -- ⊢ ↑(homology.map (_ : dTo C i ≫ dFrom C i = 0) (_ : dTo D i ≫ dFrom D i = 0) ( …
  erw [homology.π_map_apply, homology.π_map_apply]
  -- ⊢ ↑(homology.π (dTo D i) (dFrom D i) (_ : dTo D i ≫ dFrom D i = 0)) (↑(kernelS …
  -- To check that two elements are equal mod boundaries, it suffices to exhibit a boundary:
  refine' cokernel_π_imageSubobject_ext _ _ ((toPrev i h.hom) x.1) _
  -- ⊢ ↑(kernelSubobjectMap (Hom.sqFrom f i)) (↑toKernelSubobject x) = ↑(kernelSubo …
  -- Moreover, to check that two cycles are equal, it suffices to check their underlying elements:
  ext
  -- ⊢ ↑(Subobject.arrow (cycles D i)) (↑(kernelSubobjectMap (Hom.sqFrom f i)) (↑to …
  erw [map_add, CategoryTheory.Limits.kernelSubobjectMap_arrow_apply,
    CategoryTheory.Limits.kernelSubobjectMap_arrow_apply,
    ModuleCat.toKernelSubobject_arrow, imageToKernel_arrow_apply, imageSubobject_arrow_comp_apply]
  rw [Hom.sqFrom_left, Hom.sqFrom_left, h.comm i, LinearMap.add_apply,
    LinearMap.add_apply, prevD_eq_toPrev_dTo, dNext_eq_dFrom_fromNext, comp_apply, comp_apply,
    x.2, map_zero]
  dsimp
  -- ⊢ 0 + ↑(dTo D i) (↑(↑(toPrev i) h.hom) ↑x) + ↑(Hom.f g i) ↑x = ↑(Hom.f g i) ↑x …
  abel
  -- 🎉 no goals
  -- 🎉 no goals

end ModuleCat
