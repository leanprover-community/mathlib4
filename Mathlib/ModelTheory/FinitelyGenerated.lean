/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.ModelTheory.Substructures

/-!
# Finitely Generated First-Order Structures

This file defines what it means for a first-order (sub)structure to be finitely or countably
generated, similarly to other finitely-generated objects in the algebra library.

## Main Definitions

- `FirstOrder.Language.Substructure.FG` indicates that a substructure is finitely generated.
- `FirstOrder.Language.Structure.FG` indicates that a structure is finitely generated.
- `FirstOrder.Language.Substructure.CG` indicates that a substructure is countably generated.
- `FirstOrder.Language.Structure.CG` indicates that a structure is countably generated.


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

theorem fg_def {N : L.Substructure M} : N.FG ↔ ∃ S : Set M, S.Finite ∧ closure L S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_toSet t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases Finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩

theorem fg_iff_exists_fin_generating_family {N : L.Substructure M} :
    N.FG ↔ ∃ (n : ℕ) (s : Fin n → M), closure L (range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    exact ⟨range s, finite_range s, hs⟩

theorem fg_bot : (⊥ : L.Substructure M).FG :=
  ⟨∅, by rw [Finset.coe_empty, closure_empty]⟩

instance instInhabited_fg : Inhabited { S : L.Substructure M // S.FG } := ⟨⊥, fg_bot⟩

theorem fg_closure {s : Set M} (hs : s.Finite) : FG (closure L s) :=
  ⟨hs.toFinset, by rw [hs.coe_toFinset]⟩

theorem fg_closure_singleton (x : M) : FG (closure L ({x} : Set M)) :=
  fg_closure (finite_singleton x)

theorem FG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.FG) (hN₂ : N₂.FG) : (N₁ ⊔ N₂).FG :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

theorem FG.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.FG) :
    (s.map f).FG :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

theorem FG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).FG) : s.FG := by
  rcases hs with ⟨t, h⟩
  rw [fg_def]
  refine ⟨f ⁻¹' t, t.finite_toSet.preimage f.injective.injOn, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h, map_closure, Embedding.coe_toHom, image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure (L := L) hx
  rw [h] at h'
  exact Hom.map_le_range h'

theorem FG.of_finite {s : L.Substructure M} [h : Finite s] : s.FG :=
  ⟨Set.Finite.toFinset h, by simp only [Finite.coe_toFinset, closure_eq]⟩

theorem FG.finite [L.IsRelational] {S : L.Substructure M} (h : S.FG) : Finite S := by
  obtain ⟨s, rfl⟩ := h
  have hs := s.finite_toSet
  rw [← closure_eq_of_isRelational L (s : Set M)] at hs
  exact hs

theorem fg_iff_finite [L.IsRelational] {S : L.Substructure M} : S.FG ↔ Finite S :=
  ⟨FG.finite, fun _ => FG.of_finite⟩

/-- A substructure of `M` is countably generated if it is the closure of a countable subset of `M`.
-/
def CG (N : L.Substructure M) : Prop :=
  ∃ S : Set M, S.Countable ∧ closure L S = N

theorem cg_def {N : L.Substructure M} : N.CG ↔ ∃ S : Set M, S.Countable ∧ closure L S = N :=
  Iff.refl _

theorem FG.cg {N : L.Substructure M} (h : N.FG) : N.CG := by
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h
  exact ⟨s, hf.countable, rfl⟩

theorem cg_iff_empty_or_exists_nat_generating_family {N : L.Substructure M} :
    N.CG ↔ N = (∅ : Set M) ∨ ∃ s : ℕ → M, closure L (range s) = N := by
  rw [cg_def]
  constructor
  · rintro ⟨S, Scount, hS⟩
    rcases eq_empty_or_nonempty (N : Set M) with h | h
    · exact Or.intro_left _ h
    obtain ⟨f, h'⟩ :=
      (Scount.union (Set.countable_singleton h.some)).exists_eq_range
        (singleton_nonempty h.some).inr
    refine Or.intro_right _ ⟨f, ?_⟩
    rw [← h', closure_union, hS, sup_eq_left, closure_le]
    exact singleton_subset_iff.2 h.some_mem
  · intro h
    rcases h with h | h
    · refine ⟨∅, countable_empty, closure_eq_of_le (empty_subset _) ?_⟩
      rw [← SetLike.coe_subset_coe, h]
      exact empty_subset _
    · obtain ⟨f, rfl⟩ := h
      exact ⟨range f, countable_range _, rfl⟩

theorem cg_bot : (⊥ : L.Substructure M).CG :=
  fg_bot.cg

theorem cg_closure {s : Set M} (hs : s.Countable) : CG (closure L s) :=
  ⟨s, hs, rfl⟩

theorem cg_closure_singleton (x : M) : CG (closure L ({x} : Set M)) :=
  (fg_closure_singleton x).cg

theorem CG.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.CG) (hN₂ : N₂.CG) : (N₁ ⊔ N₂).CG :=
  let ⟨t₁, ht₁⟩ := cg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := cg_def.1 hN₂
  cg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [closure_union, ht₁.2, ht₂.2]⟩

theorem CG.map {N : Type*} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.CG) :
    (s.map f).CG :=
  let ⟨t, ht⟩ := cg_def.1 hs
  cg_def.2 ⟨f '' t, ht.1.image _, by rw [closure_image, ht.2]⟩

theorem CG.of_map_embedding {N : Type*} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).CG) : s.CG := by
  rcases hs with ⟨t, h1, h2⟩
  rw [cg_def]
  refine ⟨f ⁻¹' t, h1.preimage f.injective, ?_⟩
  have hf : Function.Injective f.toHom := f.injective
  refine map_injective_of_injective hf ?_
  rw [← h2, map_closure, Embedding.coe_toHom, image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure (L := L) hx
  rw [h2] at h'
  exact Hom.map_le_range h'

theorem cg_iff_countable [Countable (Σ l, L.Functions l)] {s : L.Substructure M} :
    s.CG ↔ Countable s := by
  refine ⟨?_, fun h => ⟨s, h.to_set, s.closure_eq⟩⟩
  rintro ⟨s, h, rfl⟩
  exact h.substructure_closure L

theorem cg_of_countable {s : L.Substructure M} [h : Countable s] : s.CG :=
  ⟨s, h.to_set, s.closure_eq⟩

end Substructure

open Substructure

namespace Structure

variable (L) (M)

/-- A structure is finitely generated if it is the closure of a finite subset. -/
class FG : Prop where
  out : (⊤ : L.Substructure M).FG

/-- A structure is countably generated if it is the closure of a countable subset. -/
class CG : Prop where
  out : (⊤ : L.Substructure M).CG

variable {L M}

theorem fg_def : FG L M ↔ (⊤ : L.Substructure M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Structure.FG` in terms of `Set.Finite` instead of `Finset`. -/
theorem fg_iff : FG L M ↔ ∃ S : Set M, S.Finite ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [fg_def, Substructure.fg_def]

theorem FG.range {N : Type*} [L.Structure N] (h : FG L M) (f : M →[L] N) : f.range.FG := by
  rw [Hom.range_eq_map]
  exact (fg_def.1 h).map f

theorem FG.map_of_surjective {N : Type*} [L.Structure N] (h : FG L M) (f : M →[L] N)
    (hs : Function.Surjective f) : FG L N := by
  rw [← Hom.range_eq_top] at hs
  rw [fg_def, ← hs]
  exact h.range f

theorem FG.countable_hom (N : Type*) [L.Structure N] [Countable N] (h : FG L M) :
    Countable (M →[L] N) := by
  let ⟨S, finite_S, closure_S⟩ := fg_iff.1 h
  let g : (M →[L] N) → (S → N) :=
    fun f ↦ f ∘ (↑)
  have g_inj : Function.Injective g := by
    intro f f' h
    apply Hom.eq_of_eqOn_dense closure_S
    intro x x_in_S
    exact congr_fun h ⟨x, x_in_S⟩
  have : Finite ↑S := (S.finite_coe_iff).2 finite_S
  exact Function.Embedding.countable ⟨g, g_inj⟩

instance FG.instCountable_hom (N : Type*) [L.Structure N] [Countable N] [h : FG L M] :
    Countable (M →[L] N) :=
  FG.countable_hom N h

theorem FG.countable_embedding (N : Type*) [L.Structure N] [Countable N] (_ : FG L M) :
    Countable (M ↪[L] N) :=
  Function.Embedding.countable ⟨Embedding.toHom, Embedding.toHom_injective⟩

instance Fg.instCountable_embedding (N : Type*) [L.Structure N]
    [Countable N] [h : FG L M] : Countable (M ↪[L] N) :=
  FG.countable_embedding N h

theorem FG.of_finite [Finite M] : FG L M := by
  simp only [fg_def, Substructure.FG.of_finite]

theorem FG.finite [L.IsRelational] (h : FG L M) : Finite M :=
  Finite.of_finite_univ (Substructure.FG.finite (fg_def.1 h))

theorem fg_iff_finite [L.IsRelational] : FG L M ↔ Finite M :=
  ⟨FG.finite, fun _ => FG.of_finite⟩

theorem cg_def : CG L M ↔ (⊤ : L.Substructure M).CG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Structure.cg`. -/
theorem cg_iff : CG L M ↔ ∃ S : Set M, S.Countable ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [cg_def, Substructure.cg_def]

theorem CG.range {N : Type*} [L.Structure N] (h : CG L M) (f : M →[L] N) : f.range.CG := by
  rw [Hom.range_eq_map]
  exact (cg_def.1 h).map f

theorem CG.map_of_surjective {N : Type*} [L.Structure N] (h : CG L M) (f : M →[L] N)
    (hs : Function.Surjective f) : CG L N := by
  rw [← Hom.range_eq_top] at hs
  rw [cg_def, ← hs]
  exact h.range f

theorem cg_iff_countable [Countable (Σ l, L.Functions l)] : CG L M ↔ Countable M := by
  rw [cg_def, Substructure.cg_iff_countable, topEquiv.toEquiv.countable_iff]

theorem cg_of_countable [Countable M] : CG L M := by
  simp only [cg_def, Substructure.cg_of_countable]

theorem FG.cg (h : FG L M) : CG L M :=
  cg_def.2 (fg_def.1 h).cg

instance (priority := 100) cg_of_fg [h : FG L M] : CG L M :=
  h.cg

end Structure

theorem Equiv.fg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.FG L M ↔ Structure.FG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

theorem Substructure.fg_iff_structure_fg (S : L.Substructure M) : S.FG ↔ Structure.FG L S := by
  rw [Structure.fg_def]
  refine ⟨fun h => FG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map, range_subtype] at h
    exact h

theorem Equiv.cg_iff {N : Type*} [L.Structure N] (f : M ≃[L] N) :
    Structure.CG L M ↔ Structure.CG L N :=
  ⟨fun h => h.map_of_surjective f.toHom f.toEquiv.surjective, fun h =>
    h.map_of_surjective f.symm.toHom f.toEquiv.symm.surjective⟩

theorem Substructure.cg_iff_structure_cg (S : L.Substructure M) : S.CG ↔ Structure.CG L S := by
  rw [Structure.cg_def]
  refine ⟨fun h => CG.of_map_embedding S.subtype ?_, fun h => ?_⟩
  · rw [← Hom.range_eq_map, range_subtype]
    exact h
  · have h := h.map S.subtype.toHom
    rw [← Hom.range_eq_map, range_subtype] at h
    exact h

theorem Substructure.countable_fg_substructures_of_countable [Countable M] :
    Countable { S : L.Substructure M // S.FG } := by
  let g : { S : L.Substructure M // S.FG } → Finset M :=
    fun S ↦ Exists.choose S.prop
  have g_inj : Function.Injective g := by
    intro S S' h
    apply Subtype.eq
    rw [(Exists.choose_spec S.prop).symm, (Exists.choose_spec S'.prop).symm]
    exact congr_arg (closure L ∘ SetLike.coe) h
  exact Function.Embedding.countable ⟨g, g_inj⟩

instance Substructure.instCountable_fg_substructures_of_countable [Countable M] :
    Countable { S : L.Substructure M // S.FG } :=
  countable_fg_substructures_of_countable

end Language

end FirstOrder
