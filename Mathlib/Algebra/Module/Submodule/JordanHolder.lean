/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import Mathlib.Order.JordanHolder
import Mathlib.Order.RelSeries
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.SimpleModule

/-!

# Composition Series of a module

This files relates `LTSeries` and `CompositionSeries` so that we can prove the two equivalent
definition of module length are the same

-/

variable {R : Type _} [CommRing R] {M : Type _} [AddCommGroup M] [Module R M]
variable (s : CompositionSeries (Submodule R M)) (N : Submodule R M)

namespace CompositionSeries

/-- if `x ≤ y` are both `R`-submodule of `M`, we can mathematically form their quotient but type
theoretically more complicated, so introduce a definition to use a notation. -/
@[reducible]
private def quot (x y : Submodule R M) : Type _ := x ⧸ (Submodule.comap x.subtype y)
local infix:80 "⧸ₛ" => quot

instance addCommGroup_quot (x y : Submodule R M)  : AddCommGroup (x ⧸ₛ y) := inferInstance

instance module_quot (x y : Submodule R M)  : Module R (x ⧸ₛ y) := inferInstance

/-- quotient factor of a composition series -/
@[reducible]
def qf (i : ℕ) (hi : i < s.length) : Type _ :=
s ⟨i + 1, (add_lt_add_iff_right _).mpr hi⟩ ⧸ₛ s ⟨i, hi.trans $ lt_add_one _⟩

instance qf_isSimpleModule (i : ℕ) (hi : i < s.length) : IsSimpleModule R (s.qf i hi) := by
  rw [←covby_iff_quot_is_simple (s.strictMono.monotone _)]
  pick_goal 2
  · norm_num
  exact s.step ⟨i, hi⟩

/-- Given an `R`-submodule `N`, we can form a list of submodule of `N` by taking intersections with
a given composition series-/
@[reducible]
def interList : List (Submodule R N) :=
  s.toList.map $ fun si => Submodule.comap N.subtype (N ⊓ si)

lemma interList_length : (s.interList N).length = s.length + 1 :=
by rw [interList, List.length_map, CompositionSeries.toList, List.length_ofFn]

lemma interList_get (i : ℕ) (hi : i < s.length + 1) :
    (s.interList N).get ⟨i, ((s.interList_length N).symm ▸ hi)⟩ =
    Submodule.comap N.subtype (N ⊓ s ⟨i, hi⟩) := by
  rw [List.get_map]
  congr 2
  exact List.get_ofFn _ ⟨i, _⟩

lemma interList_get_le_get_succ (i : ℕ) (hi : i < s.length) :
    (s.interList N).get ⟨i, by rw [s.interList_length N]; exact hi.trans (lt_add_one _)⟩ ≤
    (s.interList N).get ⟨i + 1, (s.interList_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi⟩ := by
  generalize_proofs h1 h2
  rw [interList_length] at h1 h2
  rw [interList_get _ _ _ h1, interList_get _ _ _ h2]
  refine Submodule.comap_mono (le_inf inf_le_left (inf_le_right.trans $ s.strictMono.monotone ?_))
  norm_num

/-- quotient factor of intersection between a submodule and a composition series. -/
@[reducible]
def interList_qf (i : ℕ) (hi : i < s.length) : Type _ :=
    (s.interList N).get ⟨i + 1, (s.interList_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi⟩ ⧸ₛ
    (s.interList N).get ⟨i, by rw [s.interList_length N]; exact hi.trans (lt_add_one _)⟩

instance interList_qf_addCommGroup (i : ℕ) (hi : i < s.length) :
    AddCommGroup (s.interList_qf N i hi) := by
  delta interList_qf; infer_instance

instance interList_qf_module (i : ℕ) (hi : i < s.length) :
    Module R (s.interList_qf N i hi) := by
  delta interList_qf; infer_instance

/-- Given composition series `s`, the canonical map `s_{i + 1} ⊓ N` to `i`-th quotient factor of
  `s`-/
@[reducible]
def interList_get_to_qf (i : ℕ) (hi : i < s.length) :
  (s.interList N).get ⟨i+1, (s.interList_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi⟩ →ₗ[R]
  s.qf i hi :=
(Submodule.mkQ _).comp $ N.subtype.restrict $ λ ⟨x, hx1⟩ hx2 ↦ by
  rw [interList_get, Submodule.mem_comap] at hx2
  exact hx2.2

lemma interList_get_to_qf_ker (i : ℕ) (hi : i < s.length) :
  LinearMap.ker (s.interList_get_to_qf N i hi) =
  (Submodule.comap
    ((s.interList N).get
      ⟨i + 1, (s.interList_length N).symm ▸ (add_lt_add_iff_right 1).mpr hi⟩).subtype
    ((s.interList N).get
      ⟨i, lt_of_lt_of_le hi $ (s.interList_length N).symm ▸ by norm_num⟩)) := by
  ext ⟨x, hx⟩
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.comp_apply,
    LinearMap.restrict_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap]
  simp_rw [Submodule.subtype_apply]
  rw [interList_get s N i (hi.trans (lt_add_one _)), Submodule.mem_comap,
    Submodule.subtype_apply, Submodule.mem_inf, iff_and_self]
  intros hx'
  rw [interList_get s N _ _] at hx
  pick_goal 2
  · linarith
  exact hx.1

end CompositionSeries
