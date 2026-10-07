/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Pairing
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.Order.NonemptyFiniteChains

/-!
# ...

-/

universe u

@[expose] public section

open CategoryTheory Simplicial

namespace PartialOrder.NonemptyFiniteChains

section

variable {X : Type u} [PartialOrder X]

@[simp]
lemma range_toN_simplex_obj {n : ℕ} (x : (nerve X) _⦋n⦌) :
    Set.range (SSet.S.mk x).toN.simplex.obj = Set.range x.obj := by
  conv_rhs => rw [← dsimp% (SSet.S.mk x).map_toNπ_op_apply]
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    have hπ : Epi ((SSet.S.mk x).toNπ)  := inferInstance
    rw [SimplexCategory.epi_iff_surjective] at hπ
    obtain ⟨j, rfl⟩ := hπ i
    exact ⟨j, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩

open Classical in
@[no_expose]
noncomputable def ofS (s : (nerve X).S) : NonemptyFiniteChains X where
  finset := Finset.univ.image s.simplex.obj
  nonempty := ⟨s.simplex.obj 0, by simp⟩
  comparable := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    obtain h | h := le_total i j
    · exact Or.inl (s.simplex.monotone h)
    · exact Or.inr (s.simplex.monotone h)

@[simp]
lemma mem_ofS_iff (s : (nerve X).S) (x : X) :
    x ∈ (ofS s).1 ↔ x ∈ Set.range s.simplex.obj := by
  simp [ofS]

lemma obj_mem_ofS (s : (nerve X).S) (i : Fin (s.dim + 1)) :
    s.simplex.obj i ∈ (ofS s).1 := by simp [ofS]

noncomputable def ofN (s : (nerve X).N) : NonemptyFiniteChains X := ofS s.toS

@[simp]
lemma mem_ofN_iff (s : (nerve X).N) (x : X) :
    x ∈ (ofN s).finset ↔ x ∈ Set.range s.simplex.obj := by
  simp [ofN]

lemma monotone_ofS : Monotone (ofS (X := X)) := by
  intro s t h
  rw [SSet.S.le_def, Subfunctor.ofSection_le_iff] at h
  obtain ⟨f, hf⟩ := h
  intro i hi
  rw [mem_ofS_iff, Set.mem_range] at hi ⊢
  obtain ⟨x, rfl⟩ := hi
  exact ⟨f.unop x,  by rw [← hf]; rfl⟩

lemma ofN_toN (s : (nerve X).S) : ofN s.toN = ofS s :=
  le_antisymm (monotone_ofS s.toS_toN_le_self) (monotone_ofS s.self_le_toS_toN)

@[simp]
lemma ofN_finset_le_ofN_finset_iff
    {s t : (nerve X).N} : (ofN s).finset ⊆ (ofN t).finset ↔ s ≤ t := by
  refine ⟨fun h ↦ ?_, fun h ↦ monotone_ofS h⟩
  rw [SSet.N.le_iff, Subfunctor.ofSection_le_iff, SSet.Subcomplex.mem_ofSimplex_obj_iff]
  have hst (i : Fin (s.dim + 1)) : s.simplex.obj i ∈ Set.range (t.simplex.obj) := by
    rw [← mem_ofS_iff]
    exact h (obj_mem_ofS _ _)
  choose φ hφ using hst
  refine ⟨SimplexCategory.Hom.mk ⟨φ, StrictMono.monotone ?_⟩, by ext; apply hφ⟩
  intro i₁ i₂ hi
  have hs := s.nonDegenerate
  have ht := t.nonDegenerate
  rw [mem_nerve_nonDegenerate_iff_strictMono] at hs ht
  rw [← ht.lt_iff_lt, hφ, hφ]
  exact hs hi

lemma injective_ofN : Function.Injective (ofN (X := X)) := by
  intro s t h
  rw [NonemptyFiniteChains.ext_iff] at h
  apply le_antisymm
  all_goals rw [← ofN_finset_le_ofN_finset_iff, h]

open Classical in
lemma surjective_ofN : Function.Surjective (ofN (X := X)) := by
  intro s
  let U : Type u := s.1
  let : LinearOrder U :=
    { le_total := s.comparable
      toDecidableLE := by infer_instance }
  obtain ⟨n, ⟨e⟩⟩ : ∃ (n : ℕ), Nonempty (Fin (n + 1) ≃o s.1) := by
    generalize hn : s.1.card = n
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (by grind [s.nonempty])
    exact ⟨n, ⟨Fintype.orderIsoFinOfCardEq _ (by simpa)⟩⟩
  refine ⟨⟨SSet.S.mk ((Subtype.mono_coe _).comp e.monotone).functor, ?_⟩, ?_⟩
  · rw [mem_nerve_nonDegenerate_iff_strictMono]
    intro _ _ _
    simpa
  · aesop

variable (X) in
lemma bijective_ofN : Function.Bijective (ofN (X := X)) :=
  ⟨injective_ofN, surjective_ofN⟩

@[simps! apply]
noncomputable def nerveNEquiv : (nerve X).N ≃o NonemptyFiniteChains X :=
  (Equiv.ofBijective _ (bijective_ofN X)).toOrderIso
    (fun s t h ↦ by simpa)
    (fun s t h ↦ by
      obtain ⟨s, rfl⟩ := surjective_ofN s
      obtain ⟨t, rfl⟩ := surjective_ofN t
      simpa using h)

end

section

variable {X : Type u} [LinearOrder X] [Fintype X] [Nontrivial X] (x₀ : X)

def horn : (nerve (NonemptyFiniteChains X)).Subcomplex where
  obj _ := Set.ofPred (fun s ↦ ∀ i, ¬ complSingleton x₀ ≤ s.obj i)
  map _ _ hs _ := hs _

lemma notMem_horn_iff {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∉ (horn x₀).obj _ ↔ complSingleton x₀ ≤ s.obj (Fin.last _) := by
  simp only [horn, nerve_obj, le_iff, Set.mem_ofPred_eq, not_forall, not_not]
  exact ⟨fun ⟨i, hi⟩ ↦ subset_trans hi (s.monotone (Fin.le_last _)), fun h ↦ ⟨_, h⟩⟩

lemma mem_horn_iff {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∈ (horn x₀).obj _ ↔
      ¬ complSingleton x₀ ≤ s.obj (Fin.last n) := by
  rw [← notMem_horn_iff, not_not]

lemma notMem_horn_iff' {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∉ (horn x₀).obj _ ↔
      s.obj (Fin.last _) = complSingleton x₀ ∨ s.obj (Fin.last _) = ⊤ := by
  simp [notMem_horn_iff, NonemptyFiniteChains.ext_iff,
    Finset.compl_singleton_subset_iff]

lemma mem_horn_iff' {n : ℕ} (s : (nerve (NonemptyFiniteChains X)) _⦋n⦌) :
    dsimp% s ∈ (horn x₀).obj _ ↔
      s.obj (Fin.last _) ≠ complSingleton x₀ ∧ s.obj (Fin.last _) ≠ ⊤ := by
  simp [mem_horn_iff, NonemptyFiniteChains.ext_iff,
    Finset.compl_singleton_subset_iff]

end

end PartialOrder.NonemptyFiniteChains
