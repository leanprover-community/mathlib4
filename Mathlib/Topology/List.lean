/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Order.Filter.ListTraverse
import Mathlib.Tactic.AdaptationNote

/-!
# Topology on lists and vectors

-/


open TopologicalSpace Set Filter

open Topology Filter

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

instance : TopologicalSpace (List α) :=
  TopologicalSpace.mkOfNhds (traverse nhds)

theorem nhds_list (as : List α) : 𝓝 as = traverse 𝓝 as := by
  refine nhds_mkOfNhds _ _ ?_ ?_
  · intro l
    induction l with
    | nil => exact le_rfl
    | cons a l ih =>
      suffices List.cons <$> pure a <*> pure l ≤ List.cons <$> 𝓝 a <*> traverse 𝓝 l by
        simpa only [functor_norm] using this
      exact Filter.seq_mono (Filter.map_mono <| pure_le_nhds a) ih
  · intro l s hs
    rcases (mem_traverse_iff _ _).1 hs with ⟨u, hu, hus⟩
    clear as hs
    have : ∃ v : List (Set α), l.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) v ∧ sequence v ⊆ s := by
      induction hu generalizing s with
      | nil =>
        exists []
        simp only [List.forall₂_nil_left_iff, exists_eq_left]
        exact ⟨trivial, hus⟩
      -- porting note -- renamed reordered variables based on previous types
      | cons ht _ ih =>
        rcases mem_nhds_iff.1 ht with ⟨u, hut, hu⟩
        rcases ih _ Subset.rfl with ⟨v, hv, hvss⟩
        exact
          ⟨u::v, List.Forall₂.cons hu hv,
            Subset.trans (Set.seq_mono (Set.image_subset _ hut) hvss) hus⟩
    rcases this with ⟨v, hv, hvs⟩
    have : sequence v ∈ traverse 𝓝 l :=
      mem_traverse _ _ <| hv.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha
    refine mem_of_superset this fun u hu ↦ ?_
    have hu := (List.mem_traverse _ _).1 hu
    have : List.Forall₂ (fun a s => IsOpen s ∧ a ∈ s) u v := by
      refine List.Forall₂.flip ?_
      replace hv := hv.flip
      simp only [List.forall₂_and_left, Function.flip_def] at hv ⊢
      exact ⟨hv.1, hu.flip⟩
    refine mem_of_superset ?_ hvs
    exact mem_traverse _ _ (this.imp fun a s ⟨hs, ha⟩ => IsOpen.mem_nhds hs ha)

@[simp]
theorem nhds_nil : 𝓝 ([] : List α) = pure [] := by
  rw [nhds_list, List.traverse_nil _]

theorem nhds_cons (a : α) (l : List α) : 𝓝 (a::l) = List.cons <$> 𝓝 a <*> 𝓝 l := by
  rw [nhds_list, List.traverse_cons _, ← nhds_list]

theorem List.tendsto_cons {a : α} {l : List α} :
    Tendsto (fun p : α × List α => List.cons p.1 p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a::l)) := by
  rw [nhds_cons, Tendsto, Filter.map_prod]; exact le_rfl

theorem Filter.Tendsto.cons {α : Type*} {f : α → β} {g : α → List β} {a : Filter α} {b : β}
    {l : List β} (hf : Tendsto f a (𝓝 b)) (hg : Tendsto g a (𝓝 l)) :
    Tendsto (fun a => List.cons (f a) (g a)) a (𝓝 (b::l)) :=
  List.tendsto_cons.comp (Tendsto.prod_mk hf hg)

namespace List

theorem tendsto_cons_iff {β : Type*} {f : List α → β} {b : Filter β} {a : α} {l : List α} :
    Tendsto f (𝓝 (a::l)) b ↔ Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ˢ 𝓝 l) b := by
  have : 𝓝 (a::l) = (𝓝 a ×ˢ 𝓝 l).map fun p : α × List α => p.1::p.2 := by
    simp only [nhds_cons, Filter.prod_eq, (Filter.map_def _ _).symm,
      (Filter.seq_eq_filter_seq _ _).symm]
    simp [-Filter.map_def, Function.comp_def, functor_norm]
  rw [this, Filter.tendsto_map'_iff]; rfl

theorem continuous_cons : Continuous fun x : α × List α => (x.1::x.2 : List α) :=
  continuous_iff_continuousAt.mpr fun ⟨_x, _y⟩ => continuousAt_fst.cons continuousAt_snd

theorem tendsto_nhds {β : Type*} {f : List α → β} {r : List α → Filter β}
    (h_nil : Tendsto f (pure []) (r []))
    (h_cons :
      ∀ l a,
        Tendsto f (𝓝 l) (r l) →
          Tendsto (fun p : α × List α => f (p.1::p.2)) (𝓝 a ×ˢ 𝓝 l) (r (a::l))) :
    ∀ l, Tendsto f (𝓝 l) (r l)
  | [] => by rwa [nhds_nil]
  | a::l => by
    rw [tendsto_cons_iff]; exact h_cons l a (@tendsto_nhds _ _ _ h_nil h_cons l)

instance [DiscreteTopology α] : DiscreteTopology (List α) := by
  rw [discreteTopology_iff_nhds]; intro l; induction l <;> simp [*, nhds_cons]

theorem continuousAt_length : ∀ l : List α, ContinuousAt List.length l := by
  simp only [ContinuousAt, nhds_discrete]
  refine tendsto_nhds ?_ ?_
  · exact tendsto_pure_pure _ _
  · intro l a ih
    dsimp only [List.length]
    refine Tendsto.comp (tendsto_pure_pure (fun x => x + 1) _) ?_
    exact Tendsto.comp ih tendsto_snd

/-- Continuity of `insertIdx` in terms of `Tendsto`. -/
theorem tendsto_insertIdx' {a : α} :
    ∀ {n : ℕ} {l : List α},
      Tendsto (fun p : α × List α => insertIdx n p.1 p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (insertIdx n a l))
  | 0, _ => tendsto_cons
  | n + 1, [] => by simp
  | n + 1, a'::l => by
    have : 𝓝 a ×ˢ 𝓝 (a'::l) =
        (𝓝 a ×ˢ (𝓝 a' ×ˢ 𝓝 l)).map fun p : α × α × List α => (p.1, p.2.1::p.2.2) := by
      simp only [nhds_cons, Filter.prod_eq, ← Filter.map_def, ← Filter.seq_eq_filter_seq]
      simp [-Filter.map_def, Function.comp_def, functor_norm]
    rw [this, tendsto_map'_iff]
    exact
      (tendsto_fst.comp tendsto_snd).cons
        ((@tendsto_insertIdx' _ n l).comp <| tendsto_fst.prod_mk <| tendsto_snd.comp tendsto_snd)

@[deprecated (since := "2024-10-21")] alias tendsto_insertNth' := tendsto_insertIdx'

theorem tendsto_insertIdx {β} {n : ℕ} {a : α} {l : List α} {f : β → α} {g : β → List α}
    {b : Filter β} (hf : Tendsto f b (𝓝 a)) (hg : Tendsto g b (𝓝 l)) :
    Tendsto (fun b : β => insertIdx n (f b) (g b)) b (𝓝 (insertIdx n a l)) :=
  tendsto_insertIdx'.comp (Tendsto.prod_mk hf hg)

@[deprecated (since := "2024-10-21")] alias tendsto_insertNth := tendsto_insertIdx'

theorem continuous_insertIdx {n : ℕ} : Continuous fun p : α × List α => insertIdx n p.1 p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq]; exact tendsto_insertIdx'

@[deprecated (since := "2024-10-21")] alias continuous_insertNth := continuous_insertIdx

theorem tendsto_eraseIdx :
    ∀ {n : ℕ} {l : List α}, Tendsto (eraseIdx · n) (𝓝 l) (𝓝 (eraseIdx l n))
  | _, [] => by rw [nhds_nil]; exact tendsto_pure_nhds _ _
  | 0, a::l => by rw [tendsto_cons_iff]; exact tendsto_snd
  | n + 1, a::l => by
    rw [tendsto_cons_iff]
    dsimp [eraseIdx]
    exact tendsto_fst.cons ((@tendsto_eraseIdx n l).comp tendsto_snd)

theorem continuous_eraseIdx {n : ℕ} : Continuous fun l : List α => eraseIdx l n :=
  continuous_iff_continuousAt.mpr fun _a => tendsto_eraseIdx

@[to_additive]
theorem tendsto_prod [MulOneClass α] [ContinuousMul α] {l : List α} :
    Tendsto List.prod (𝓝 l) (𝓝 l.prod) := by
  induction' l with x l ih
  · simp +contextual [nhds_nil, mem_of_mem_nhds, tendsto_pure_left]
  simp_rw [tendsto_cons_iff, prod_cons]
  have := continuous_iff_continuousAt.mp continuous_mul (x, l.prod)
  rw [ContinuousAt, nhds_prod_eq] at this
  exact this.comp (tendsto_id.prod_map ih)

@[to_additive]
theorem continuous_prod [MulOneClass α] [ContinuousMul α] : Continuous (prod : List α → α) :=
  continuous_iff_continuousAt.mpr fun _l => tendsto_prod

end List

namespace Vector

open List

open List (Vector)

instance (n : ℕ) : TopologicalSpace (List.Vector α n) := by unfold List.Vector; infer_instance

theorem tendsto_cons {n : ℕ} {a : α} {l : List.Vector α n} :
    Tendsto (fun p : α × List.Vector α n => p.1 ::ᵥ p.2) (𝓝 a ×ˢ 𝓝 l) (𝓝 (a ::ᵥ l)) := by
  rw [tendsto_subtype_rng, Vector.cons_val]
  exact tendsto_fst.cons (Tendsto.comp continuousAt_subtype_val tendsto_snd)

theorem tendsto_insertIdx {n : ℕ} {i : Fin (n + 1)} {a : α} :
    ∀ {l : List.Vector α n},
      Tendsto (fun p : α × List.Vector α n => Vector.insertIdx p.1 i p.2) (𝓝 a ×ˢ 𝓝 l)
        (𝓝 (Vector.insertIdx a i l))
  | ⟨l, hl⟩ => by
    rw [Vector.insertIdx, tendsto_subtype_rng]
    simp only [Vector.insertIdx_val]
    exact List.tendsto_insertIdx tendsto_fst (Tendsto.comp continuousAt_subtype_val tendsto_snd : _)

@[deprecated (since := "2024-10-21")] alias tendsto_insertNth := tendsto_insertIdx'

/-- Continuity of `Vector.insertIdx`. -/
theorem continuous_insertIdx' {n : ℕ} {i : Fin (n + 1)} :
    Continuous fun p : α × List.Vector α n => Vector.insertIdx p.1 i p.2 :=
  continuous_iff_continuousAt.mpr fun ⟨a, l⟩ => by
    rw [ContinuousAt, nhds_prod_eq]; exact tendsto_insertIdx

@[deprecated (since := "2024-10-21")] alias continuous_insertNth' := continuous_insertIdx'

theorem continuous_insertIdx {n : ℕ} {i : Fin (n + 1)} {f : β → α} {g : β → List.Vector α n}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun b => Vector.insertIdx (f b) i (g b) :=
  continuous_insertIdx'.comp (hf.prod_mk hg)

@[deprecated (since := "2024-10-21")] alias continuous_insertNth := continuous_insertIdx

theorem continuousAt_eraseIdx {n : ℕ} {i : Fin (n + 1)} :
    ∀ {l : List.Vector α (n + 1)}, ContinuousAt (List.Vector.eraseIdx i) l
  | ⟨l, hl⟩ => by
    rw [ContinuousAt, List.Vector.eraseIdx, tendsto_subtype_rng]
    simp only [Vector.eraseIdx_val]
    exact Tendsto.comp List.tendsto_eraseIdx continuousAt_subtype_val

theorem continuous_eraseIdx {n : ℕ} {i : Fin (n + 1)} :
    Continuous (List.Vector.eraseIdx i : List.Vector α (n + 1) → List.Vector α n) :=
  continuous_iff_continuousAt.mpr fun ⟨_a, _l⟩ => continuousAt_eraseIdx

end Vector
