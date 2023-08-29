/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Substructures

#align_import model_theory.finitely_generated from "leanprover-community/mathlib"@"0602c59878ff3d5f71dea69c2d32ccf2e93e5398"

/-!
# Finitely Generated First-Order Structures
This file defines what it means for a first-order (sub)structure to be finitely or countably
generated, similarly to other finitely-generated objects in the algebra library.

## Main Definitions
* `FirstOrder.Language.Substructure.FG` indicates that a substructure is finitely generated.
* `FirstOrder.Language.Structure.FG` indicates that a structure is finitely generated.
* `FirstOrder.Language.Substructure.CG` indicates that a substructure is countably generated.
* `FirstOrder.Language.Structure.CG` indicates that a structure is countably generated.


## TODO
Develop a more unified definition of finite generation using the theory of closure operators, or use
this definition of finite generation to define the others.

-/

open FirstOrder Set

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

namespace Substructure

/-- A substructure of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
def FG (N : L.Substructure M) : Prop :=
  ∃ S : Finset M, closure L S = N
#align first_order.language.substructure.fg FirstOrder.Language.Substructure.FG

theorem fg_def {N : L.Substructure M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ closure L S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    -- ⊢ FG (LowerAdjoint.toFun (closure L) t')
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    -- ⊢ FG (LowerAdjoint.toFun (closure L) ↑t)
    exact ⟨t, rfl⟩⟩
    -- 🎉 no goals
#align first_order.language.substructure.fg_def FirstOrder.Language.Substructure.fg_def

theorem fg_iff_exists_fin_generating_family {N : L.Substructure M} :
    N.FG ↔ ∃ (n : ℕ) (s : Fin n → M), closure L (range s) = N := by
  rw [fg_def]
  -- ⊢ (∃ S, Set.Finite S ∧ LowerAdjoint.toFun (closure L) S = N) ↔ ∃ n s, LowerAdj …
  constructor
  -- ⊢ (∃ S, Set.Finite S ∧ LowerAdjoint.toFun (closure L) S = N) → ∃ n s, LowerAdj …
  · rintro ⟨S, Sfin, hS⟩
    -- ⊢ ∃ n s, LowerAdjoint.toFun (closure L) (range s) = N
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    -- ⊢ ∃ n s, LowerAdjoint.toFun (closure L) (range s) = N
    exact ⟨n, f, hS⟩
    -- 🎉 no goals
  · rintro ⟨n, s, hs⟩
    -- ⊢ ∃ S, Set.Finite S ∧ LowerAdjoint.toFun (closure L) S = N
    refine' ⟨range s, finite_range s, hs⟩
    -- 🎉 no goals
#align first_order.language.substructure.fg_iff_exists_fin_generating_family FirstOrder.Language.Substructure.fg_iff_exists_fin_generating_family

theorem fg_bot : (⊥ : L.Substructure M).FG :=
  ⟨∅, by rw [Finset.coe_empty, closure_empty]⟩
         -- 🎉 no goals
#align first_order.language.substructure.fg_bot FirstOrder.Language.Substructure.fg_bot

theorem fg_closure {s : Set M} (hs : s.Finite) : FG (closure L s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩
                   -- 🎉 no goals
#align first_order.language.substructure.fg_closure FirstOrder.Language.Substructure.fg_closure

theorem fg_closure_singleton (x : M) : FG (closure L ({x} : Set M)) :=
  fg_closure (finite_singleton x)
#align first_order.language.substructure.fg_closure_singleton FirstOrder.Language.Substructure.fg_closure_singleton

theorem FG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩
                                           -- 🎉 no goals
#align first_order.language.substructure.fg.sup FirstOrder.Language.Substructure.FG.sup

theorem FG.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.FG) :
    (s.map f).FG :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩
                                     -- 🎉 no goals
#align first_order.language.substructure.fg.map FirstOrder.Language.Substructure.FG.map

theorem FG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).FG) : s.FG := by
  rcases hs with ⟨t, h⟩
  -- ⊢ FG s
  rw [fg_def]
  -- ⊢ ∃ S, Set.Finite S ∧ LowerAdjoint.toFun (closure L) S = s
  refine' ⟨f ⁻¹' t, t.finite_toSet.preimage (f.injective.injOn _), _⟩
  -- ⊢ LowerAdjoint.toFun (closure L) (↑f ⁻¹' ↑t) = s
  have hf : Function.Injective f.toHom := f.injective
  -- ⊢ LowerAdjoint.toFun (closure L) (↑f ⁻¹' ↑t) = s
  refine' map_injective_of_injective hf _
  -- ⊢ Substructure.map (Embedding.toHom f) (LowerAdjoint.toFun (closure L) (↑f ⁻¹' …
  rw [← h, map_closure, Embedding.coe_toHom, image_preimage_eq_of_subset]
  -- ⊢ ↑t ⊆ range ↑f
  intro x hx
  -- ⊢ x ∈ range ↑f
  have h' := subset_closure (L := L) hx
  -- ⊢ x ∈ range ↑f
  rw [h] at h'
  -- ⊢ x ∈ range ↑f
  exact Hom.map_le_range h'
  -- 🎉 no goals
#align first_order.language.substructure.fg.of_map_embedding FirstOrder.Language.Substructure.FG.of_map_embedding

/-- A substructure of `M` is countably generated if it is the closure of a countable subset of `M`.
-/
def CG (N : L.Substructure M) : Prop :=
  ∃ S : Set M, S.Countable ∧ closure L S = N
#align first_order.language.substructure.cg FirstOrder.Language.Substructure.CG

theorem cg_def {N : L.Substructure M} : N.CG ↔ ∃ S : Set M, S.Countable ∧ closure L S = N :=
  Iff.refl _
#align first_order.language.substructure.cg_def FirstOrder.Language.Substructure.cg_def

theorem FG.cg {N : L.Substructure M} (h : N.FG) : N.CG := by
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h
  -- ⊢ CG (LowerAdjoint.toFun (closure L) s)
  refine' ⟨s, hf.countable, rfl⟩
  -- 🎉 no goals
#align first_order.language.substructure.fg.cg FirstOrder.Language.Substructure.FG.cg

theorem cg_iff_empty_or_exists_nat_generating_family {N : L.Substructure M} :
    N.CG ↔ N = (∅ : Set M) ∨ ∃ s : ℕ → M, closure L (range s) = N := by
  rw [cg_def]
  -- ⊢ (∃ S, Set.Countable S ∧ LowerAdjoint.toFun (closure L) S = N) ↔ ↑N = ∅ ∨ ∃ s …
  constructor
  -- ⊢ (∃ S, Set.Countable S ∧ LowerAdjoint.toFun (closure L) S = N) → ↑N = ∅ ∨ ∃ s …
  · rintro ⟨S, Scount, hS⟩
    -- ⊢ ↑N = ∅ ∨ ∃ s, LowerAdjoint.toFun (closure L) (range s) = N
    cases' eq_empty_or_nonempty (N : Set M) with h h
    -- ⊢ ↑N = ∅ ∨ ∃ s, LowerAdjoint.toFun (closure L) (range s) = N
    · exact Or.intro_left _ h
      -- 🎉 no goals
    obtain ⟨f, h'⟩ :=
      (Scount.union (Set.countable_singleton h.some)).exists_eq_range
        (singleton_nonempty h.some).inr
    refine' Or.intro_right _ ⟨f, _⟩
    -- ⊢ LowerAdjoint.toFun (closure L) (range f) = N
    rw [← h', closure_union, hS, sup_eq_left, closure_le]
    -- ⊢ {Set.Nonempty.some h} ⊆ ↑N
    exact singleton_subset_iff.2 h.some_mem
    -- 🎉 no goals
  · intro h
    -- ⊢ ∃ S, Set.Countable S ∧ LowerAdjoint.toFun (closure L) S = N
    cases' h with h h
    -- ⊢ ∃ S, Set.Countable S ∧ LowerAdjoint.toFun (closure L) S = N
    · refine' ⟨∅, countable_empty, closure_eq_of_le (empty_subset _) _⟩
      -- ⊢ N ≤ LowerAdjoint.toFun (closure L) ∅
      rw [← SetLike.coe_subset_coe, h]
      -- ⊢ ∅ ⊆ ↑(LowerAdjoint.toFun (closure L) ∅)
      exact empty_subset _
      -- 🎉 no goals
    · obtain ⟨f, rfl⟩ := h
      -- ⊢ ∃ S, Set.Countable S ∧ LowerAdjoint.toFun (closure L) S = LowerAdjoint.toFun …
      exact ⟨range f, countable_range _, rfl⟩
      -- 🎉 no goals
#align first_order.language.substructure.cg_iff_empty_or_exists_nat_generating_family FirstOrder.Language.Substructure.cg_iff_empty_or_exists_nat_generating_family

theorem cg_bot : (⊥ : L.Substructure M).CG :=
  fg_bot.cg
#align first_order.language.substructure.cg_bot FirstOrder.Language.Substructure.cg_bot

theorem cg_closure {s : Set M} (hs : s.Countable) : CG (closure L s) :=
  ⟨s, hs, rfl⟩
#align first_order.language.substructure.cg_closure FirstOrder.Language.Substructure.cg_closure

theorem cg_closure_singleton (x : M) : CG (closure L ({x} : Set M)) :=
  (fg_closure_singleton x).cg
#align first_order.language.substructure.cg_closure_singleton FirstOrder.Language.Substructure.cg_closure_singleton

theorem CG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.CG) (hN₂ : N₂.CG) : (N₁ ⊔ N₂).CG :=
  let ⟨t₁, ht₁⟩ := cg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := cg_def.1 hN₂
  cg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩
                                           -- 🎉 no goals
#align first_order.language.substructure.cg.sup FirstOrder.Language.Substructure.CG.sup

theorem CG.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.CG) :
    (s.map f).CG :=
  let ⟨t, ht⟩ := cg_def.1 hs
  cg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩
                                     -- 🎉 no goals
#align first_order.language.substructure.cg.map FirstOrder.Language.Substructure.CG.map

theorem CG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).CG) : s.CG := by
  rcases hs with ⟨t, h1, h2⟩
  -- ⊢ CG s
  rw [cg_def]
  -- ⊢ ∃ S, Set.Countable S ∧ LowerAdjoint.toFun (closure L) S = s
  refine' ⟨f ⁻¹' t, h1.preimage f.injective, _⟩
  -- ⊢ LowerAdjoint.toFun (closure L) (↑f ⁻¹' t) = s
  have hf : Function.Injective f.toHom := f.injective
  -- ⊢ LowerAdjoint.toFun (closure L) (↑f ⁻¹' t) = s
  refine' map_injective_of_injective hf _
  -- ⊢ Substructure.map (Embedding.toHom f) (LowerAdjoint.toFun (closure L) (↑f ⁻¹' …
  rw [← h2, map_closure, Embedding.coe_toHom, image_preimage_eq_of_subset]
  -- ⊢ t ⊆ range ↑f
  intro x hx
  -- ⊢ x ∈ range ↑f
  have h' := subset_closure (L := L) hx
  -- ⊢ x ∈ range ↑f
  rw [h2] at h'
  -- ⊢ x ∈ range ↑f
  exact Hom.map_le_range h'
  -- 🎉 no goals
#align first_order.language.substructure.cg.of_map_embedding FirstOrder.Language.Substructure.CG.of_map_embedding

theorem cg_iff_countable [Countable (Σl, L.Functions l)] {s : L.Substructure M} :
    s.CG ↔ Countable s := by
  refine' ⟨_, fun h => ⟨s, h.to_set, s.closure_eq⟩⟩
  -- ⊢ CG s → Countable { x // x ∈ s }
  rintro ⟨s, h, rfl⟩
  -- ⊢ Countable { x // x ∈ LowerAdjoint.toFun (closure L) s }
  exact h.substructure_closure L
  -- 🎉 no goals
#align first_order.language.substructure.cg_iff_countable FirstOrder.Language.Substructure.cg_iff_countable

end Substructure

open Substructure

namespace Structure

set_option linter.uppercaseLean3 false

variable (L) (M)

/-- A structure is finitely generated if it is the closure of a finite subset. -/
class FG : Prop where
  out : (⊤ : L.Substructure M).FG
#align first_order.language.Structure.fg FirstOrder.Language.Structure.FG

/-- A structure is countably generated if it is the closure of a countable subset. -/
class CG : Prop where
  out : (⊤ : L.Substructure M).CG
#align first_order.language.Structure.cg FirstOrder.Language.Structure.CG

variable {L M}

theorem fg_def : FG L M ↔ (⊤ : L.Substructure M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align first_order.language.Structure.fg_def FirstOrder.Language.Structure.fg_def

/-- An equivalent expression of `Structure.FG` in terms of `Set.Finite` instead of `Finset`. -/
theorem fg_iff : FG L M ↔ ∃ S : Set M, S.Finite ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [fg_def, Substructure.fg_def]
  -- 🎉 no goals
#align first_order.language.Structure.fg_iff FirstOrder.Language.Structure.fg_iff

theorem FG.range {N : Type*} [L.Structure N] (h : FG L M) (f : M →[L] N) : f.range.FG := by
  rw [Hom.range_eq_map]
  -- ⊢ Substructure.FG (map f ⊤)
  exact (fg_def.1 h).map f
  -- 🎉 no goals
#align first_order.language.Structure.fg.range FirstOrder.Language.Structure.FG.range

theorem FG.map_of_surjective {N : Type*} [L.Structure N] (h : FG L M) (f : M →[L] N)
    (hs : Function.Surjective f) : FG L N := by
  rw [← Hom.range_eq_top] at hs
  -- ⊢ FG L N
  rw [fg_def, ← hs]
  -- ⊢ Substructure.FG (Hom.range f)
  exact h.range f
  -- 🎉 no goals
#align first_order.language.Structure.fg.map_of_surjective FirstOrder.Language.Structure.FG.map_of_surjective

theorem cg_def : CG L M ↔ (⊤ : L.Substructure M).CG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align first_order.language.Structure.cg_def FirstOrder.Language.Structure.cg_def

/-- An equivalent expression of `Structure.cg`. -/
theorem cg_iff : CG L M ↔ ∃ S : Set M, S.Countable ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [cg_def, Substructure.cg_def]
  -- 🎉 no goals
#align first_order.language.Structure.cg_iff FirstOrder.Language.Structure.cg_iff

theorem CG.range {N : Type*} [L.Structure N] (h : CG L M) (f : M →[L] N) : f.range.CG := by
  rw [Hom.range_eq_map]
  -- ⊢ Substructure.CG (map f ⊤)
  exact (cg_def.1 h).map f
  -- 🎉 no goals
#align first_order.language.Structure.cg.range FirstOrder.Language.Structure.CG.range

theorem CG.map_of_surjective {N : Type*} [L.Structure N] (h : CG L M) (f : M →[L] N)
    (hs : Function.Surjective f) : CG L N := by
  rw [← Hom.range_eq_top] at hs
  -- ⊢ CG L N
  rw [cg_def, ← hs]
  -- ⊢ Substructure.CG (Hom.range f)
  exact h.range f
  -- 🎉 no goals
#align first_order.language.Structure.cg.map_of_surjective FirstOrder.Language.Structure.CG.map_of_surjective

theorem cg_iff_countable [Countable (Σl, L.Functions l)] : CG L M ↔ Countable M := by
  rw [cg_def, Substructure.cg_iff_countable, topEquiv.toEquiv.countable_iff]
  -- 🎉 no goals
#align first_order.language.Structure.cg_iff_countable FirstOrder.Language.Structure.cg_iff_countable

theorem FG.cg (h : FG L M) : CG L M :=
  cg_def.2 (fg_def.1 h).cg
#align first_order.language.Structure.fg.cg FirstOrder.Language.Structure.FG.cg

instance (priority := 100) cg_of_fg [h : FG L M] : CG L M :=
  h.cg
#align first_order.language.Structure.cg_of_fg FirstOrder.Language.Structure.cg_of_fg

end Structure

theorem Equiv.fg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.FG L M ↔ Structure.FG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩
#align first_order.language.equiv.fg_iff FirstOrder.Language.Equiv.fg_iff

theorem Substructure.fg_iff_structure_fg (S : L.Substructure M) : S.FG ↔ Structure.FG L S := by
  rw [Structure.fg_def]
  -- ⊢ FG S ↔ FG ⊤
  refine' ⟨fun h => FG.of_map_embedding S.subtype _, fun h => _⟩
  -- ⊢ FG (map (Embedding.toHom (subtype S)) ⊤)
  · rw [← Hom.range_eq_map, range_subtype]
    -- ⊢ FG S
    exact h
    -- 🎉 no goals
  · have h := h.map S.subtype.toHom
    -- ⊢ FG S
    rw [← Hom.range_eq_map, range_subtype] at h
    -- ⊢ FG S
    exact h
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.substructure.fg_iff_Structure_fg FirstOrder.Language.Substructure.fg_iff_structure_fg

theorem Equiv.cg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.CG L M ↔ Structure.CG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩
#align first_order.language.equiv.cg_iff FirstOrder.Language.Equiv.cg_iff

theorem Substructure.cg_iff_structure_cg (S : L.Substructure M) : S.CG ↔ Structure.CG L S := by
  rw [Structure.cg_def]
  -- ⊢ CG S ↔ CG ⊤
  refine' ⟨fun h => CG.of_map_embedding S.subtype _, fun h => _⟩
  -- ⊢ CG (map (Embedding.toHom (subtype S)) ⊤)
  · rw [← Hom.range_eq_map, range_subtype]
    -- ⊢ CG S
    exact h
    -- 🎉 no goals
  · have h := h.map S.subtype.toHom
    -- ⊢ CG S
    rw [← Hom.range_eq_map, range_subtype] at h
    -- ⊢ CG S
    exact h
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.substructure.cg_iff_Structure_cg FirstOrder.Language.Substructure.cg_iff_structure_cg

end Language

end FirstOrder
