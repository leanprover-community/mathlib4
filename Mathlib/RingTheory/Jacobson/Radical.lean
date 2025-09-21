/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Jacobson radical of modules and rings

## Main definitions

`Module.jacobson R M`: the Jacobson radical of a module `M` over a ring `R` is defined to be the
intersection of all maximal submodules of `M`.

`Ring.jacobson R`: the Jacobson radical of a ring `R` is the Jacobson radical of `R` as
an `R`-module, which is equal to the intersection of all maximal left ideals of `R`. It turns out
it is in fact a two-sided ideal, and equals the intersection of all maximal right ideals of `R`.

## Reference
* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

assert_not_exists Cardinal

namespace Module

open Submodule

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F τ₁₂ M M₂] (f : F)

/-- The Jacobson radical of an `R`-module `M` is the infimum of all maximal submodules in `M`. -/
def jacobson : Submodule R M :=
  sInf { m : Submodule R M | IsCoatom m }

variable {R R₂ M M₂}

theorem le_comap_jacobson : jacobson R M ≤ comap f (jacobson R₂ M₂) := by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm ↦ ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top

theorem map_jacobson_le : map f (jacobson R M) ≤ jacobson R₂ M₂ :=
  map_le_iff_le_comap.mpr (le_comap_jacobson f)

include τ₁₂ in
theorem jacobson_eq_bot_of_injective (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥) :
    jacobson R M = ⊥ :=
  le_bot_iff.mp <| (le_comap_jacobson f).trans <| by
    simp_rw [h, comap_bot, ((LinearMapClass.ker_eq_bot _).mpr inj).le]

variable {f}

theorem map_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  le_antisymm (map_jacobson_le f) <| by
    rw [jacobson, sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m ↦ sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)

theorem comap_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    comap f (jacobson R₂ M₂) = jacobson R M := by
  rw [← map_jacobson_of_ker_le surj le, comap_map_eq_self le]

theorem map_jacobson_of_bijective (hf : Function.Bijective f) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  map_jacobson_of_ker_le hf.2 <| by simp_rw [(LinearMapClass.ker_eq_bot _).mpr hf.1, bot_le]

theorem comap_jacobson_of_bijective (hf : Function.Bijective f) :
    comap f (jacobson R₂ M₂) = jacobson R M :=
  comap_jacobson_of_ker_le hf.2 <| by simp_rw [(LinearMapClass.ker_eq_bot _).mpr hf.1, bot_le]

theorem jacobson_quotient_of_le {N : Submodule R M} (le : N ≤ jacobson R M) :
    jacobson R (M ⧸ N) = map N.mkQ (jacobson R M) :=
  (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm

theorem jacobson_le_of_eq_bot {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥) :
    jacobson R M ≤ N := by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

variable (R M)

@[simp]
theorem jacobson_quotient_jacobson : jacobson R (M ⧸ jacobson R M) = ⊥ := by
  rw [jacobson_quotient_of_le le_rfl, mkQ_map_self]

theorem jacobson_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] : jacobson R M < ⊤ := by
  obtain ⟨m, hm, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  exact (sInf_le <| Set.mem_setOf.mpr hm).trans_lt hm.1.lt_top

example [Nontrivial M] [Module.Finite R M] : jacobson R M < ⊤ := jacobson_lt_top R M

variable {ι} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

theorem jacobson_pi_le : jacobson R (Π i, M i) ≤ Submodule.pi Set.univ (jacobson R <| M ·) := by
  simp_rw [← iInf_comap_proj, jacobson, sInf_eq_iInf', comap_iInf, le_iInf_iff]
  intro i m
  exact iInf_le_of_le ⟨_, (isCoatom_comap_iff <| LinearMap.proj_surjective i).mpr m.2⟩ le_rfl

/-- A product of modules with trivial Jacobson radical (e.g. simple modules) also has trivial
Jacobson radical. -/
theorem jacobson_pi_eq_bot (h : ∀ i, jacobson R (M i) = ⊥) : jacobson R (Π i, M i) = ⊥ :=
  le_bot_iff.mp <| (jacobson_pi_le R M).trans <| by simp_rw [h, pi_univ_bot, le_rfl]

end Module

section

variable (R R₂ : Type*) [Ring R] [Ring R₂] (f : R →+* R₂) [RingHomSurjective f]
variable (M : Type*) [AddCommGroup M] [Module R M]

namespace Ring

/-- The Jacobson radical of a ring `R` is the Jacobson radical of `R` as an `R`-module. -/
-- TODO: replace all `Ideal.jacobson ⊥` by this.
abbrev jacobson : Ideal R := Module.jacobson R R

theorem jacobson_eq_sInf_isMaximal : jacobson R = sInf {I : Ideal R | I.IsMaximal} := by
  simp_rw [jacobson, Module.jacobson, Ideal.isMaximal_def]

instance : (jacobson R).IsTwoSided :=
  ⟨fun b ha ↦ Module.le_comap_jacobson (f := LinearMap.toSpanSingleton R R b) ha⟩

variable {R R₂}

theorem le_comap_jacobson : jacobson R ≤ Ideal.comap f (jacobson R₂) :=
  Module.le_comap_jacobson f.toSemilinearMap

theorem map_jacobson_le : Submodule.map f.toSemilinearMap (jacobson R) ≤ jacobson R₂ :=
  Module.map_jacobson_le f.toSemilinearMap

variable {f} in
theorem map_jacobson_of_ker_le (le : RingHom.ker f ≤ jacobson R) :
    Submodule.map f.toSemilinearMap (jacobson R) = jacobson R₂ :=
  Module.map_jacobson_of_ker_le f.surjective le

theorem coe_jacobson_quotient (I : Ideal R) [I.IsTwoSided] :
    (jacobson (R ⧸ I) : Set (R ⧸ I)) = Module.jacobson R (R ⧸ I) := by
  let f : R ⧸ I →ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨AddHom.id _, fun _ _ ↦ rfl⟩
  rw [jacobson, ← Module.map_jacobson_of_ker_le (f := f) Function.surjective_id]
  · apply Set.image_id
  · rintro _ rfl; exact zero_mem _

theorem jacobson_quotient_of_le {I : Ideal R} [I.IsTwoSided] (le : I ≤ jacobson R) :
    jacobson (R ⧸ I) = Submodule.map (Ideal.Quotient.mk I).toSemilinearMap (jacobson R) :=
  .symm <| Module.map_jacobson_of_ker_le (by exact Ideal.Quotient.mk_surjective) <| by
    rwa [← I.ker_mkQ] at le

theorem jacobson_le_of_eq_bot {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) = ⊥) :
    jacobson R ≤ I :=
  Module.jacobson_le_of_eq_bot <| by
    rw [← le_bot_iff, ← SetLike.coe_subset_coe] at h ⊢
    rwa [← coe_jacobson_quotient]

variable (R)

@[simp]
theorem jacobson_quotient_jacobson : jacobson (R ⧸ jacobson R) = ⊥ :=
  (jacobson_quotient_of_le le_rfl).trans <| SetLike.ext' <| by
    apply SetLike.ext'_iff.mp (jacobson R).mkQ_map_self

theorem jacobson_lt_top [Nontrivial R] : jacobson R < ⊤ := Module.jacobson_lt_top R R

theorem jacobson_smul_top_le : jacobson R • (⊤ : Submodule R M) ≤ Module.jacobson R M :=
  Submodule.smul_le.mpr fun _ hr m _ ↦ Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr

end Ring

namespace Submodule

variable {R M}

theorem jacobson_smul_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Submodule R M) :
    Ring.jacobson R • N < ⊤ :=
  ((smul_mono_right _ le_top).trans <| Ring.jacobson_smul_top_le R M).trans_lt
    (Module.jacobson_lt_top R M)

theorem FG.jacobson_smul_lt {N : Submodule R M} (ne_bot : N ≠ ⊥) (fg : N.FG) :
    Ring.jacobson R • N < N := by
  rw [← Module.Finite.iff_fg] at fg
  rw [← nontrivial_iff_ne_bot] at ne_bot
  convert map_strictMono_of_injective N.injective_subtype (jacobson_smul_lt_top ⊤)
  on_goal 1 => rw [map_smul'']
  all_goals rw [Submodule.map_top, range_subtype]

/-- A form of Nakayama's lemma for modules over noncommutative rings. -/
theorem FG.eq_bot_of_le_jacobson_smul {N : Submodule R M} (fg : N.FG)
    (le : N ≤ Ring.jacobson R • N) : N = ⊥ := by
  contrapose! le; exact (jacobson_smul_lt le fg).not_ge

end Submodule

end
