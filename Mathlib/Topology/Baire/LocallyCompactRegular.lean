/-
Copyright (c) 2022 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Second Baire theorem

In this file we prove that a locally compact regular topological space has Baire property.
-/

@[expose] public section

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- **Second Baire theorem**: locally compact R₁ spaces are Baire. -/
instance (priority := 100) BaireSpace.of_t2Space_locallyCompactSpace
    [R1Space X] [LocallyCompactSpace X] : BaireSpace X := by
  constructor
  intro f ho hd
  /- To prove that an intersection of open dense subsets is dense, prove that its intersection
    with any open neighbourhood `U` is dense. Define recursively a decreasing sequence `K` of
    compact neighbourhoods: start with some compact neighbourhood inside `U`, then at each step,
    take its interior, intersect with `f n`, then choose a compact neighbourhood inside the
    intersection. -/
  rw [dense_iff_inter_open]
  intro U U_open U_nonempty
  -- Choose an antitone sequence of positive compacts such that `closure (K 0) ⊆ U`
  -- and `closure (K (n + 1)) ⊆ f n` for all `n`
  obtain ⟨K, hK_anti, hKf, hKU⟩ : ∃ K : ℕ → PositiveCompacts X,
      (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, closure ↑(K (n + 1)) ⊆ f n) ∧ closure ↑(K 0) ⊆ U := by
    rcases U_open.exists_positiveCompacts_closure_subset U_nonempty with ⟨K₀, hK₀⟩
    have : ∀ (n) (K : PositiveCompacts X),
        ∃ K' : PositiveCompacts X, closure ↑K' ⊆ f n ∩ interior K := by
      refine fun n K ↦ ((ho n).inter isOpen_interior).exists_positiveCompacts_closure_subset ?_
      rw [inter_comm]
      exact (hd n).inter_open_nonempty _ isOpen_interior K.interior_nonempty
    choose K_next hK_next using this
    -- The next two lines are faster than a single `refine`.
    use Nat.rec K₀ K_next
    refine ⟨fun n ↦ ?_, fun n ↦ (hK_next n _).trans inter_subset_left, hK₀⟩
    exact subset_closure.trans <| (hK_next _ _).trans <|
      inter_subset_right.trans interior_subset
  -- Prove that ̀`⋂ n : ℕ, closure (K n)` is inside `U ∩ ⋂ n : ℕ, f n`.
  have hK_subset : (⋂ n, closure (K n) : Set X) ⊆ U ∩ ⋂ n, f n := fun x hx ↦ by
    simp only [mem_iInter, mem_inter_iff] at hx ⊢
    exact ⟨hKU <| hx 0, fun n ↦ hKf n <| hx (n + 1)⟩
  /- Prove that `⋂ n : ℕ, closure (K n)` is not empty, as an intersection of a decreasing sequence
    of nonempty compact closed subsets. -/
  have hK_nonempty : (⋂ n, closure (K n) : Set X).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => closure_mono <| hK_anti n) (fun n => (K n).nonempty.closure)
      (K 0).isCompact.closure fun n => isClosed_closure
  exact hK_nonempty.mono hK_subset

/-- A dense Gδ subset of a Baire space is Baire. -/
theorem IsGδ.baireSpace_of_dense [BaireSpace X] (hG : IsGδ s) (hd : Dense s) : BaireSpace s := by
  constructor
  intro f hof hdf
  obtain ⟨V, hV⟩ : ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧ s = ⋂ n, V n := eq_iInter_nat hG
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Set X, (∀ n, IsOpen (g n)) ∧ (∀ n, Dense (g n)) ∧
    ∀ n, f n = Subtype.val ⁻¹' g n := by
    choose g hg1 hg2 hg3 using fun n => exists_open_dense_of_open_dense_subtype hd (hof n) (hdf n)
    exact ⟨g, hg1, hg2, fun n => (hg3 n).symm⟩
  have h_inter_dense : Dense (⋂ n, g n ∩ V n) := by
    exact BaireSpace.baire_property (fun n ↦ g n ∩ V n) (fun n => IsOpen.inter (hg1 n) (hV.1 n))
      (fun n => (hg2 n).inter_of_isOpen_left (Dense.mono (by simp [hV.2, iInter_subset]) hd)
      (hg1 n))
  have h_inter_eq : ⋂ n, g n ∩ V n = ⋂ n, f n := by
    ext
    simpa [hg3, hV] using ⟨fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩, fun h n => ⟨h.1 n, h.2 n⟩⟩
  rw [h_inter_eq] at h_inter_dense
  exact Subtype.dense_iff.mpr fun a _ ↦ h_inter_dense a

/-- A Gδ subset of a locally compact R₁ space is Baire. -/
theorem IsGδ.of_t2Space_locallyCompactSpace (hG : IsGδ s) [R1Space X] [LocallyCompactSpace X] :
    BaireSpace s := by
  have h_closure_baire : BaireSpace (closure s) := by
    convert BaireSpace.of_t2Space_locallyCompactSpace using 1
    · infer_instance
    · exact IsClosed.locallyCompactSpace isClosed_closure
  have h_s_baire : BaireSpace ((↑) ⁻¹' s : Set (closure s)) := IsGδ.baireSpace_of_dense
    (isGδ_induced continuous_subtype_val hG) (dense_in_closure s)
  -- Since `s` is homeomorphic to `s'`, we can conclude that `s` is a Baire space.
  have h_homeo : Homeomorph ((↑) ⁻¹' s : Set (closure s)) s := by
    refine' ⟨ _, _, _ ⟩;
    refine' ⟨ fun x => ⟨ x.1, _ ⟩, fun x => ⟨ ⟨ x.1, _ ⟩, _ ⟩, fun x => _, fun x => _ ⟩;
    exact x.2;
    exact subset_closure x.2;
    · grind
    · grind
    · grind
    · fun_prop
    · fun_prop
  -- Since `h_homeo` is a homeomorphism, we can conclude that `s` is a Baire space.
  have h_baire : BaireSpace s := by
    have := h_s_baire
    exact (by
    rcases this with ⟨ this ⟩;
    constructor;
    intro f hf hf';
    convert this ( fun n => h_homeo ⁻¹' f n ) ( fun n => ?_ ) ( fun n => ?_ ) using 1;
    · constructor <;> intro h <;> rw [ dense_iff_inter_open ] at * <;> aesop;
      · specialize h ( h_homeo '' U ) ; aesop;
        simpa only [ Set.preimage_iInter ] using h;
      · specialize h ( h_homeo ⁻¹' U ) ( h_homeo.isOpen_preimage.mpr a );
        obtain ⟨ x, hx ⟩ := h ( by rcases a_1 with ⟨ x, hx ⟩ ; exact ⟨ h_homeo.symm x, by simpa using hx ⟩ ) ; use h_homeo x; aesop;
    · exact h_homeo.continuous.isOpen_preimage _ ( hf n );
    · rw [ dense_iff_inter_open ] at *;
      intro U hU hU';
      have := hf' n;
      rw [ dense_iff_inter_open ] at this;
      contrapose! this;
      refine' ⟨ h_homeo '' U, _, _, _ ⟩;
      · exact h_homeo.isOpenMap U hU;
      · exact hU'.image _;
      · simp_all +decide [ Set.ext_iff ];
        grind);
  exact h_baire
