/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Order.JordanHolder

#align_import ring_theory.simple_module from "leanprover-community/mathlib"@"cce7f68a7eaadadf74c82bbac20721cdc03a1cc1"

/-!
# Simple Modules

## Main Definitions
  * `IsSimpleModule` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * `IsSemisimpleModule` indicates that every submodule has a complement, or equivalently,
    the module is a direct sum of simple modules.
  * A `DivisionRing` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero` shows that a linear map between simple modules
  is either bijective or 0, leading to a `DivisionRing` structure on the endomorphism ring.

## TODO
  * Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/


variable (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbrev IsSimpleModule :=
  IsSimpleOrder (Submodule R M)
#align is_simple_module IsSimpleModule

/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbrev IsSemisimpleModule :=
  ComplementedLattice (Submodule R M)
#align is_semisimple_module IsSemisimpleModule

-- Making this an instance causes the linter to complain of "dangerous instances"
theorem IsSimpleModule.nontrivial [IsSimpleModule R M] : Nontrivial M :=
  ⟨⟨0, by
      have h : (⊥ : Submodule R M) ≠ ⊤ := bot_ne_top
      contrapose! h
      ext x
      simp [Submodule.mem_bot, Submodule.mem_top, h x]⟩⟩
#align is_simple_module.nontrivial IsSimpleModule.nontrivial

variable {R} {M} -- Porting note: had break line or all hell breaks loose
variable {m : Submodule R M} {N : Type*} [AddCommGroup N] [Module R N]

theorem IsSimpleModule.congr (l : M ≃ₗ[R] N) [IsSimpleModule R N] : IsSimpleModule R M :=
  (Submodule.orderIsoMapComap l).isSimpleOrder
#align is_simple_module.congr IsSimpleModule.congr

theorem isSimpleModule_iff_isAtom : IsSimpleModule R m ↔ IsAtom m := by
  rw [← Set.isSimpleOrder_Iic_iff_isAtom]
  apply OrderIso.isSimpleOrder_iff
  exact Submodule.MapSubtype.relIso m
#align is_simple_module_iff_is_atom isSimpleModule_iff_isAtom

theorem isSimpleModule_iff_isCoatom : IsSimpleModule R (M ⧸ m) ↔ IsCoatom m := by
  rw [← Set.isSimpleOrder_Ici_iff_isCoatom]
  apply OrderIso.isSimpleOrder_iff
  exact Submodule.comapMkQRelIso m
#align is_simple_module_iff_is_coatom isSimpleModule_iff_isCoatom

theorem covby_iff_quot_is_simple {A B : Submodule R M} (hAB : A ≤ B) :
    A ⋖ B ↔ IsSimpleModule R (B ⧸ Submodule.comap B.subtype A) := by
  set f : Submodule R B ≃o Set.Iic B := Submodule.MapSubtype.relIso B with hf
  rw [covby_iff_coatom_Iic hAB, isSimpleModule_iff_isCoatom, ← OrderIso.isCoatom_iff f, hf]
  -- This used to be in the next `simp`, but we need `erw` after leanprover/lean4#2644
  erw [RelIso.coe_fn_mk]
  simp [-OrderIso.isCoatom_iff, Submodule.MapSubtype.relIso, Submodule.map_comap_subtype,
    inf_eq_right.2 hAB]
#align covby_iff_quot_is_simple covby_iff_quot_is_simple

namespace IsSimpleModule

variable [hm : IsSimpleModule R m]

@[simp]
theorem isAtom : IsAtom m :=
  isSimpleModule_iff_isAtom.1 hm
#align is_simple_module.is_atom IsSimpleModule.isAtom

end IsSimpleModule

theorem is_semisimple_of_sSup_simples_eq_top
    (h : sSup { m : Submodule R M | IsSimpleModule R m } = ⊤) : IsSemisimpleModule R M :=
  complementedLattice_of_sSup_atoms_eq_top (by simp_rw [← h, isSimpleModule_iff_isAtom])
#align is_semisimple_of_Sup_simples_eq_top is_semisimple_of_sSup_simples_eq_top

namespace IsSemisimpleModule

variable [IsSemisimpleModule R M]

theorem sSup_simples_eq_top : sSup { m : Submodule R M | IsSimpleModule R m } = ⊤ := by
  simp_rw [isSimpleModule_iff_isAtom]
  exact sSup_atoms_eq_top
#align is_semisimple_module.Sup_simples_eq_top IsSemisimpleModule.sSup_simples_eq_top

instance is_semisimple_submodule {m : Submodule R M} : IsSemisimpleModule R m :=
  haveI f : Submodule R m ≃o Set.Iic m := Submodule.MapSubtype.relIso m
  f.complementedLattice_iff.2 IsModularLattice.complementedLattice_Iic
#align is_semisimple_module.is_semisimple_submodule IsSemisimpleModule.is_semisimple_submodule

end IsSemisimpleModule

theorem is_semisimple_iff_top_eq_sSup_simples :
    sSup { m : Submodule R M | IsSimpleModule R m } = ⊤ ↔ IsSemisimpleModule R M :=
  ⟨is_semisimple_of_sSup_simples_eq_top, by
    intro
    exact IsSemisimpleModule.sSup_simples_eq_top⟩
#align is_semisimple_iff_top_eq_Sup_simples is_semisimple_iff_top_eq_sSup_simples

namespace LinearMap

theorem injective_or_eq_zero [IsSimpleModule R M] (f : M →ₗ[R] N) :
    Function.Injective f ∨ f = 0 := by
  rw [← ker_eq_bot, ← ker_eq_top]
  apply eq_bot_or_eq_top
#align linear_map.injective_or_eq_zero LinearMap.injective_or_eq_zero

theorem injective_of_ne_zero [IsSimpleModule R M] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Injective f :=
  f.injective_or_eq_zero.resolve_right h
#align linear_map.injective_of_ne_zero LinearMap.injective_of_ne_zero

theorem surjective_or_eq_zero [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Surjective f ∨ f = 0 := by
  rw [← range_eq_top, ← range_eq_bot, or_comm]
  apply eq_bot_or_eq_top
#align linear_map.surjective_or_eq_zero LinearMap.surjective_or_eq_zero

theorem surjective_of_ne_zero [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Surjective f :=
  f.surjective_or_eq_zero.resolve_right h
#align linear_map.surjective_of_ne_zero LinearMap.surjective_of_ne_zero

/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) :
    Function.Bijective f ∨ f = 0 := by
  by_cases h : f = 0
  · right
    exact h
  exact Or.intro_left _ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩
#align linear_map.bijective_or_eq_zero LinearMap.bijective_or_eq_zero

theorem bijective_of_ne_zero [IsSimpleModule R M] [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Bijective f :=
  f.bijective_or_eq_zero.resolve_right h
#align linear_map.bijective_of_ne_zero LinearMap.bijective_of_ne_zero

theorem isCoatom_ker_of_surjective [IsSimpleModule R N] {f : M →ₗ[R] N}
    (hf : Function.Surjective f) : IsCoatom (LinearMap.ker f) := by
  rw [← isSimpleModule_iff_isCoatom]
  exact IsSimpleModule.congr (f.quotKerEquivOfSurjective hf)
#align linear_map.is_coatom_ker_of_surjective LinearMap.isCoatom_ker_of_surjective

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance _root_.Module.End.divisionRing
    [DecidableEq (Module.End R M)] [IsSimpleModule R M] : DivisionRing (Module.End R M) :=
  {
    (Module.End.ring :
      Ring
        (Module.End R
          M)) with
    inv := fun f =>
      if h : f = 0 then 0
      else
        LinearMap.inverse f (Equiv.ofBijective _ (bijective_of_ne_zero h)).invFun
          (Equiv.ofBijective _ (bijective_of_ne_zero h)).left_inv
          (Equiv.ofBijective _ (bijective_of_ne_zero h)).right_inv
    exists_pair_ne :=
      ⟨0, 1, by
        haveI := IsSimpleModule.nontrivial R M
        have h := exists_pair_ne M
        contrapose! h
        intro x y
        simp_rw [ext_iff, one_apply, zero_apply] at h
        rw [← h x, h y]⟩
    mul_inv_cancel := by
      intro a a0
      change a * dite _ _ _ = 1
      ext x
      rw [dif_neg a0, mul_eq_comp, one_apply, comp_apply]
      exact (Equiv.ofBijective _ (bijective_of_ne_zero a0)).right_inv x
    inv_zero := dif_pos rfl }
#align module.End.division_ring Module.End.divisionRing

end LinearMap

-- Porting note: adding a namespace with all the new statements; existing result is not used in ML3
namespace JordanHolderModule

-- Porting note: jordanHolderModule was timing out so outlining the fields

/-- An isomorphism `X₂ / X₁ ∩ X₂ ≅ Y₂ / Y₁ ∩ Y₂` of modules for pairs
`(X₁,X₂) (Y₁,Y₂) : Submodule R M` -/
def Iso (X Y : Submodule R M × Submodule R M) : Prop :=
  Nonempty <| (X.2 ⧸ X.1.comap X.2.subtype) ≃ₗ[R] Y.2 ⧸ Y.1.comap Y.2.subtype

theorem iso_symm {X Y : Submodule R M × Submodule R M} : Iso X Y → Iso Y X :=
  fun ⟨f⟩ => ⟨f.symm⟩

theorem iso_trans {X Y Z : Submodule R M × Submodule R M} : Iso X Y → Iso Y Z → Iso X Z :=
  fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩

@[nolint unusedArguments]
theorem second_iso {X Y : Submodule R M} (_ : X ⋖ X ⊔ Y) :
    Iso (X,X ⊔ Y) (X ⊓ Y,Y) := by
  constructor
  rw [sup_comm, inf_comm]
  dsimp
  exact (LinearMap.quotientInfEquivSupQuotient Y X).symm

instance instJordanHolderLattice : JordanHolderLattice (Submodule R M) where
  IsMaximal := (· ⋖ ·)
  lt_of_isMaximal := Covby.lt
  sup_eq_of_isMaximal hxz hyz := Wcovby.sup_eq hxz.wcovby hyz.wcovby
  isMaximal_inf_left_of_isMaximal_sup := inf_covby_of_covby_sup_of_covby_sup_left
  Iso := Iso
  iso_symm := iso_symm
  iso_trans := iso_trans
  second_iso := second_iso
#align jordan_holder_module JordanHolderModule.instJordanHolderLattice

end JordanHolderModule
