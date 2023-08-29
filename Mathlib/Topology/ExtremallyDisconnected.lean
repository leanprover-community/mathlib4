/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.StoneCech

#align_import topology.extremally_disconnected from "leanprover-community/mathlib"@"7e281deff072232a3c5b3e90034bd65dde396312"

/-!
# Extremally disconnected spaces

An extremally disconnected topological space is a space in which the closure of every open set is
open. Such spaces are also called Stonean spaces. They are the projective objects in the category of
compact Hausdorff spaces.

## Main declarations

* `ExtremallyDisconnected`: Predicate for a space to be extremally disconnected.
* `CompactT2.Projective`: Predicate for a topological space to be a projective object in the
  category of compact Hausdorff spaces.
* `CompactT2.Projective.extremallyDisconnected`: Compact Hausdorff spaces that are projective are
  extremally disconnected.
* `CompactT2.ExtremallyDisconnected.projective`: Extremally disconnected spaces are projective
  objects in the category of compact Hausdorff spaces.

## References

[Gleason, *Projective topological spaces*][gleason1958]
-/

set_option autoImplicit true

noncomputable section

open Classical Function Set

universe u

section

variable (X : Type u) [TopologicalSpace X]

/-- An extremally disconnected topological space is a space
in which the closure of every open set is open. -/
class ExtremallyDisconnected : Prop where
  /-- The closure of every open set is open. -/
  open_closure : ∀ U : Set X, IsOpen U → IsOpen (closure U)
#align extremally_disconnected ExtremallyDisconnected

section TotallySeparated

/-- Extremally disconnected spaces are totally separated. -/
instance [ExtremallyDisconnected X] [T2Space X] : TotallySeparatedSpace X :=
{ isTotallySeparated_univ := by
    intro x _ y _ hxy
    -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ univ ⊆ u ∪ v ∧ Disjoint u v
    obtain ⟨U, V, hUV⟩ := T2Space.t2 x y hxy
    -- ⊢ ∃ u v, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ univ ⊆ u ∪ v ∧ Disjoint u v
    use closure U
    -- ⊢ ∃ v, IsOpen (closure U) ∧ IsOpen v ∧ x ∈ closure U ∧ y ∈ v ∧ univ ⊆ closure  …
    use (closure U)ᶜ
    -- ⊢ IsOpen (closure U) ∧ IsOpen (closure U)ᶜ ∧ x ∈ closure U ∧ y ∈ (closure U)ᶜ  …
    refine ⟨ExtremallyDisconnected.open_closure U hUV.1,
      by simp only [isOpen_compl_iff, isClosed_closure], subset_closure hUV.2.2.1, ?_,
      by simp only [Set.union_compl_self, Set.subset_univ], disjoint_compl_right⟩
    simp only [Set.mem_compl_iff]
    -- ⊢ ¬y ∈ closure U
    rw [mem_closure_iff]
    -- ⊢ ¬∀ (o : Set X), IsOpen o → y ∈ o → Set.Nonempty (o ∩ U)
    push_neg
    -- ⊢ ∃ o, IsOpen o ∧ y ∈ o ∧ ¬Set.Nonempty (o ∩ U)
    refine' ⟨V, ⟨hUV.2.1, hUV.2.2.2.1, _⟩⟩
    -- ⊢ ¬Set.Nonempty (V ∩ U)
    rw [Set.nonempty_iff_ne_empty]
    -- ⊢ ¬V ∩ U ≠ ∅
    simp only [not_not]
    -- ⊢ V ∩ U = ∅
    rw [← Set.disjoint_iff_inter_eq_empty, disjoint_comm]
    -- ⊢ Disjoint U V
    exact hUV.2.2.2.2 }
    -- 🎉 no goals

end TotallySeparated

section

/-- The assertion `CompactT2.Projective` states that given continuous maps
`f : X → Z` and `g : Y → Z` with `g` surjective between `t_2`, compact topological spaces,
there exists a continuous lift `h : X → Y`, such that `f = g ∘ h`. -/
def CompactT2.Projective : Prop :=
  ∀ {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z],
    ∀ [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z],
      ∀ {f : X → Z} {g : Y → Z} (_ : Continuous f) (_ : Continuous g) (_ : Surjective g),
        ∃ h : X → Y, Continuous h ∧ g ∘ h = f
#align compact_t2.projective CompactT2.Projective

variable {X}

theorem StoneCech.projective [DiscreteTopology X] : CompactT2.Projective (StoneCech X) := by
  intro Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur
  -- ⊢ ∃ h, Continuous h ∧ g ∘ h = f
  let s : Z → Y := fun z => Classical.choose <| g_sur z
  -- ⊢ ∃ h, Continuous h ∧ g ∘ h = f
  have hs : g ∘ s = id := funext fun z => Classical.choose_spec (g_sur z)
  -- ⊢ ∃ h, Continuous h ∧ g ∘ h = f
  let t := s ∘ f ∘ stoneCechUnit
  -- ⊢ ∃ h, Continuous h ∧ g ∘ h = f
  have ht : Continuous t := continuous_of_discreteTopology
  -- ⊢ ∃ h, Continuous h ∧ g ∘ h = f
  let h : StoneCech X → Y := stoneCechExtend ht
  -- ⊢ ∃ h, Continuous h ∧ g ∘ h = f
  have hh : Continuous h := continuous_stoneCechExtend ht
  -- ⊢ ∃ h, Continuous h ∧ g ∘ h = f
  refine' ⟨h, hh, denseRange_stoneCechUnit.equalizer (hg.comp hh) hf _⟩
  -- ⊢ (g ∘ h) ∘ stoneCechUnit = f ∘ stoneCechUnit
  rw [comp.assoc, stoneCechExtend_extends ht, ← comp.assoc, hs, comp.left_id]
  -- 🎉 no goals
#align stone_cech.projective StoneCech.projective

protected theorem CompactT2.Projective.extremallyDisconnected [CompactSpace X] [T2Space X]
    (h : CompactT2.Projective X) : ExtremallyDisconnected X := by
  refine' { open_closure := fun U hU => _ }
  -- ⊢ IsOpen (closure U)
  let Z₁ : Set (X × Bool) := Uᶜ ×ˢ {true}
  -- ⊢ IsOpen (closure U)
  let Z₂ : Set (X × Bool) := closure U ×ˢ {false}
  -- ⊢ IsOpen (closure U)
  let Z : Set (X × Bool) := Z₁ ∪ Z₂
  -- ⊢ IsOpen (closure U)
  have hZ₁₂ : Disjoint Z₁ Z₂ := disjoint_left.2 fun x hx₁ hx₂ => by cases hx₁.2.symm.trans hx₂.2
  -- ⊢ IsOpen (closure U)
  have hZ₁ : IsClosed Z₁ := hU.isClosed_compl.prod (T1Space.t1 _)
  -- ⊢ IsOpen (closure U)
  have hZ₂ : IsClosed Z₂ := isClosed_closure.prod (T1Space.t1 false)
  -- ⊢ IsOpen (closure U)
  have hZ : IsClosed Z := hZ₁.union hZ₂
  -- ⊢ IsOpen (closure U)
  let f : Z → X := Prod.fst ∘ Subtype.val
  -- ⊢ IsOpen (closure U)
  have f_cont : Continuous f := continuous_fst.comp continuous_subtype_val
  -- ⊢ IsOpen (closure U)
  have f_sur : Surjective f := by
    intro x
    by_cases hx : x ∈ U
    · exact ⟨⟨(x, false), Or.inr ⟨subset_closure hx, mem_singleton _⟩⟩, rfl⟩
    · exact ⟨⟨(x, true), Or.inl ⟨hx, mem_singleton _⟩⟩, rfl⟩
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  -- ⊢ IsOpen (closure U)
  obtain ⟨g, hg, g_sec⟩ := h continuous_id f_cont f_sur
  -- ⊢ IsOpen (closure U)
  let φ := Subtype.val ∘ g
  -- ⊢ IsOpen (closure U)
  have hφ : Continuous φ := continuous_subtype_val.comp hg
  -- ⊢ IsOpen (closure U)
  have hφ₁ : ∀ x, (φ x).1 = x := congr_fun g_sec
  -- ⊢ IsOpen (closure U)
  suffices closure U = φ ⁻¹' Z₂ by
    rw [this, preimage_comp, ← isClosed_compl_iff, ← preimage_compl,
      ← preimage_subtype_coe_eq_compl Subset.rfl]
    · exact hZ₁.preimage hφ
    · rw [hZ₁₂.inter_eq, inter_empty]
  refine' (closure_minimal _ <| hZ₂.preimage hφ).antisymm fun x hx => _
  -- ⊢ U ⊆ φ ⁻¹' Z₂
  · intro x hx
    -- ⊢ x ∈ φ ⁻¹' Z₂
    have : φ x ∈ Z₁ ∪ Z₂ := (g x).2
    -- ⊢ x ∈ φ ⁻¹' Z₂
    -- Porting note: Originally `simpa [hx, hφ₁] using this`
    cases' this with hφ hφ
    -- ⊢ x ∈ φ ⁻¹' Z₂
    · exact ((hφ₁ x ▸ hφ.1) hx).elim
      -- 🎉 no goals
    · exact hφ
      -- 🎉 no goals
  · rw [← hφ₁ x]
    -- ⊢ (φ x).fst ∈ closure U
    exact hx.1
    -- 🎉 no goals
#align compact_t2.projective.extremally_disconnected CompactT2.Projective.extremallyDisconnected

end

section

variable {A D E : Type u} [TopologicalSpace A] [TopologicalSpace D] [TopologicalSpace E]

/-- Lemma 2.4 in [Gleason, *Projective topological spaces*][gleason1958]:
a continuous surjection $\pi$ from a compact space $D$ to a Fréchet space $A$ restricts to
a compact subset $E$ of $D$, such that $\pi$ maps $E$ onto $A$ and satisfies the
"Zorn subset condition", where $\pi(E_0) \ne A$ for any proper closed subset $E_0 \subsetneq E$. -/
lemma exists_compact_surjective_zorn_subset [T1Space A] [CompactSpace D] {π : D → A}
    (π_cont : Continuous π) (π_surj : π.Surjective) : ∃ E : Set D, CompactSpace E ∧ π '' E = univ ∧
    ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → E.restrict π '' E₀ ≠ univ := by
  -- suffices to apply Zorn's lemma on the subsets of $D$ that are closed and mapped onto $A$
  let S : Set <| Set D := {E : Set D | IsClosed E ∧ π '' E = univ}
  -- ⊢ ∃ E, CompactSpace ↑E ∧ π '' E = univ ∧ ∀ (E₀ : Set ↑E), E₀ ≠ univ → IsClosed …
  suffices ∀ (C : Set <| Set D) (_ : C ⊆ S) (_ : IsChain (· ⊆ ·) C), ∃ s ∈ S, ∀ c ∈ C, s ⊆ c by
    rcases zorn_superset S this with ⟨E, ⟨E_closed, E_surj⟩, E_min⟩
    refine ⟨E, isCompact_iff_compactSpace.mp E_closed.isCompact, E_surj, ?_⟩
    intro E₀ E₀_min E₀_closed
    contrapose! E₀_min
    exact eq_univ_of_coe_eq <|
      E_min E₀ ⟨E₀_closed.trans E_closed, image_coe_eq_restrict_image ▸ E₀_min⟩ coe_subset
  -- suffices to prove intersection of chain is minimal
  intro C C_sub C_chain
  -- ⊢ ∃ s, s ∈ S ∧ ∀ (c : Set D), c ∈ C → s ⊆ c
  -- prove intersection of chain is closed
  refine ⟨iInter (fun c : C => c), ⟨isClosed_iInter fun ⟨_, h⟩ => (C_sub h).left, ?_⟩,
    fun c hc _ h => mem_iInter.mp h ⟨c, hc⟩⟩
  -- prove intersection of chain is mapped onto $A$
  by_cases hC : Nonempty C
  -- ⊢ π '' ⋂ (c : ↑C), ↑c = univ
  · refine eq_univ_of_forall fun a => inter_nonempty_iff_exists_left.mp ?_
    -- ⊢ Set.Nonempty ((⋂ (c : ↑C), ↑c) ∩ fun a_1 => π a_1 = a)
    -- apply Cantor's intersection theorem
    refine iInter_inter (ι := C) (π ⁻¹' {a}) _ ▸
      IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed _
      ?_ (fun c => ?_) (fun c => IsClosed.isCompact ?_) (fun c => ?_)
    · replace C_chain : IsChain (· ⊇ ·) C := C_chain.symm
      -- ⊢ Directed (fun x x_1 => x ⊇ x_1) fun i => ↑i ∩ π ⁻¹' {a}
      have : ∀ s t : Set D, s ⊇ t → _ ⊇ _ := fun _ _ => inter_subset_inter_left <| π ⁻¹' {a}
      -- ⊢ Directed (fun x x_1 => x ⊇ x_1) fun i => ↑i ∩ π ⁻¹' {a}
      exact (directedOn_iff_directed.mp C_chain.directedOn).mono_comp (· ⊇ ·) this
      -- 🎉 no goals
    · rw [← image_inter_nonempty_iff, (C_sub c.mem).right, univ_inter]
      -- ⊢ Set.Nonempty {a}
      exact singleton_nonempty a
      -- 🎉 no goals
    all_goals exact (C_sub c.mem).left.inter <| (T1Space.t1 a).preimage π_cont
    -- 🎉 no goals
  · rw [@iInter_of_empty _ _ <| not_nonempty_iff.mp hC, image_univ_of_surjective π_surj]
    -- 🎉 no goals

/-- Lemma 2.1 in [Gleason, *Projective topological spaces*][gleason1958]:
if $\rho$ is a continuous surjection from a topological space $E$ to a topological space $A$
satisfying the "Zorn subset condition", then $\rho(G)$ is contained in
the closure of $A \setminus \rho(E \setminus G)}$ for any open set $G$ of $E$. -/
lemma image_subset_closure_compl_image_compl_of_isOpen {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ)
    {G : Set E} (hG : IsOpen G) : ρ '' G ⊆ closure ((ρ '' Gᶜ)ᶜ) := by
  -- suffices to prove for nonempty $G$
  by_cases G_empty : G = ∅
  -- ⊢ ρ '' G ⊆ closure (ρ '' Gᶜ)ᶜ
  · simpa only [G_empty, image_empty] using empty_subset _
    -- 🎉 no goals
  · -- let $a \in \rho(G)$
    intro a ha
    -- ⊢ a ∈ closure (ρ '' Gᶜ)ᶜ
    rw [mem_closure_iff]
    -- ⊢ ∀ (o : Set A), IsOpen o → a ∈ o → Set.Nonempty (o ∩ (ρ '' Gᶜ)ᶜ)
    -- let $N$ be a neighbourhood of $a$
    intro N N_open hN
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    -- get $x \in A$ from nonempty open $G \cap \rho^{-1}(N)$
    rcases (G.mem_image ρ a).mp ha with ⟨e, he, rfl⟩
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    have nonempty : (G ∩ ρ⁻¹' N).Nonempty := ⟨e, mem_inter he <| mem_preimage.mpr hN⟩
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    have is_open : IsOpen <| G ∩ ρ⁻¹' N := hG.inter <| N_open.preimage ρ_cont
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    have ne_univ : ρ '' (G ∩ ρ⁻¹' N)ᶜ ≠ univ :=
      zorn_subset _ (compl_ne_univ.mpr nonempty) is_open.isClosed_compl
    rcases nonempty_compl.mpr ne_univ with ⟨x, hx⟩
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    -- prove $x \in N \cap (A \setminus \rho(E \setminus G))$
    have hx' : x ∈ (ρ '' Gᶜ)ᶜ := fun h => hx <| image_subset ρ (by simp) h
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    rcases ρ_surj x with ⟨y, rfl⟩
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    have hy : y ∈ G ∩ ρ⁻¹' N := by simpa using mt (mem_image_of_mem ρ) <| mem_compl hx
    -- ⊢ Set.Nonempty (N ∩ (ρ '' Gᶜ)ᶜ)
    exact ⟨ρ y, mem_inter (mem_preimage.mp <| mem_of_mem_inter_right hy) hx'⟩
    -- 🎉 no goals

/-- Lemma 2.2 in [Gleason, *Projective topological spaces*][gleason1958]:
in an extremally disconnected space, if $U_1$ and $U_2$ are disjoint open sets,
then $\overline{U_1}$ and $\overline{U_2}$ are also disjoint. -/
lemma ExtremallyDisconnected.disjoint_closure_of_disjoint_IsOpen [ExtremallyDisconnected A]
    {U₁ U₂ : Set A} (h : Disjoint U₁ U₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) :
    Disjoint (closure U₁) (closure U₂) :=
  (h.closure_right hU₁).closure_left <| open_closure U₂ hU₂

private lemma ExtremallyDisconnected.homeoCompactToT2_injective [ExtremallyDisconnected A]
    [T2Space A] [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ)
    (ρ_surj : ρ.Surjective) (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) :
    ρ.Injective := by
  -- let $x_1, x_2 \in E$ be distinct points such that $\rho(x_1) = \rho(x_2)$
  intro x₁ x₂ hρx
  -- ⊢ x₁ = x₂
  by_contra hx
  -- ⊢ False
  -- let $G_1$ and $G_2$ be disjoint open neighbourhoods of $x_1$ and $x_2$ respectively
  rcases t2_separation hx with ⟨G₁, G₂, G₁_open, G₂_open, hx₁, hx₂, disj⟩
  -- ⊢ False
  -- prove $A \setminus \rho(E - G_1)$ and $A \setminus \rho(E - G_2)$ are disjoint
  have G₁_comp : IsCompact G₁ᶜ := IsClosed.isCompact G₁_open.isClosed_compl
  -- ⊢ False
  have G₂_comp : IsCompact G₂ᶜ := IsClosed.isCompact G₂_open.isClosed_compl
  -- ⊢ False
  have G₁_open' : IsOpen (ρ '' G₁ᶜ)ᶜ := (G₁_comp.image ρ_cont).isClosed.isOpen_compl
  -- ⊢ False
  have G₂_open' : IsOpen (ρ '' G₂ᶜ)ᶜ := (G₂_comp.image ρ_cont).isClosed.isOpen_compl
  -- ⊢ False
  have disj' : Disjoint (ρ '' G₁ᶜ)ᶜ (ρ '' G₂ᶜ)ᶜ := by
    rw [disjoint_iff_inter_eq_empty, ← compl_union, ← image_union, ← compl_inter,
      disjoint_iff_inter_eq_empty.mp disj, compl_empty, compl_empty_iff,
      image_univ_of_surjective ρ_surj]
  -- apply Lemma 2.2 to prove their closures are disjoint
  have disj'' : Disjoint (closure (ρ '' G₁ᶜ)ᶜ) (closure (ρ '' G₂ᶜ)ᶜ) :=
    disjoint_closure_of_disjoint_IsOpen disj' G₁_open' G₂_open'
  -- apply Lemma 2.1 to prove $\rho(x_1) = \rho(x_2)$ lies in their intersection
  have hx₁' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₁_open <|
    mem_image_of_mem ρ hx₁
  have hx₂' := image_subset_closure_compl_image_compl_of_isOpen ρ_cont ρ_surj zorn_subset G₂_open <|
    mem_image_of_mem ρ hx₂
  exact disj''.ne_of_mem hx₁' hx₂' hρx
  -- 🎉 no goals

/-- Lemma 2.3 in [Gleason, *Projective topological spaces*][gleason1958]:
a continuous surjection from a compact Hausdorff space to an extremally disconnected Hausdorff space
satisfying the "Zorn subset condition" is a homeomorphism. -/
noncomputable def ExtremallyDisconnected.homeoCompactToT2 [ExtremallyDisconnected A] [T2Space A]
    [T2Space E] [CompactSpace E] {ρ : E → A} (ρ_cont : Continuous ρ) (ρ_surj : ρ.Surjective)
    (zorn_subset : ∀ E₀ : Set E, E₀ ≠ univ → IsClosed E₀ → ρ '' E₀ ≠ univ) : E ≃ₜ A :=
  ρ_cont.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective ρ ⟨homeoCompactToT2_injective ρ_cont ρ_surj zorn_subset, ρ_surj⟩)

/-- Theorem 2.5 in [Gleason, *Projective topological spaces*][gleason1958]:
in the category of compact spaces and continuous maps,
the projective spaces are precisely the extremally disconnected spaces.-/
protected theorem CompactT2.ExtremallyDisconnected.projective [ExtremallyDisconnected A]
    [CompactSpace A] [T2Space A] : CompactT2.Projective A := by
  -- let $B$ and $C$ be compact; let $f : B \twoheadrightarrow C$ and $\phi : A \to C$ be continuous
  intro B C _ _ _ _ _ _ φ f φ_cont f_cont f_surj
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  -- let $D := \{(a, b) : \phi(a) = f(b)\}$ with projections $\pi_1 : D \to A$ and $\pi_2 : D \to B$
  let D : Set <| A × B := {x | φ x.fst = f x.snd}
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  have D_comp : CompactSpace D := isCompact_iff_compactSpace.mp
    (isClosed_eq (φ_cont.comp continuous_fst) (f_cont.comp continuous_snd)).isCompact
  -- apply Lemma 2.4 to get closed $E$ satisfying "Zorn subset condition"
  let π₁ : D → A := Prod.fst ∘ Subtype.val
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  have π₁_cont : Continuous π₁ := continuous_fst.comp continuous_subtype_val
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  have π₁_surj : π₁.Surjective := fun a => ⟨⟨⟨a, _⟩, (f_surj <| φ a).choose_spec.symm⟩, rfl⟩
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  rcases exists_compact_surjective_zorn_subset π₁_cont π₁_surj with ⟨E, _, E_onto, E_min⟩
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  -- apply Lemma 2.3 to get homeomorphism $\pi_1|_E : E \to A$
  let ρ : E → A := E.restrict π₁
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  have ρ_cont : Continuous ρ := π₁_cont.continuousOn.restrict
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  have ρ_surj : ρ.Surjective := fun a => by
    rcases (E_onto ▸ mem_univ a : a ∈ π₁ '' E) with ⟨d, ⟨hd, rfl⟩⟩; exact ⟨⟨d, hd⟩, rfl⟩
  let ρ' := ExtremallyDisconnected.homeoCompactToT2 ρ_cont ρ_surj E_min
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  -- prove $\rho := \pi_2|_E \circ \pi_1|_E^{-1}$ satisfies $\phi = f \circ \rho$
  let π₂ : D → B := Prod.snd ∘ Subtype.val
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  have π₂_cont : Continuous π₂ := continuous_snd.comp continuous_subtype_val
  -- ⊢ ∃ h, Continuous h ∧ f ∘ h = φ
  refine ⟨E.restrict π₂ ∘ ρ'.symm, ⟨π₂_cont.continuousOn.restrict.comp ρ'.symm.continuous, ?_⟩⟩
  -- ⊢ f ∘ restrict E π₂ ∘ ↑(Homeomorph.symm ρ') = φ
  suffices f ∘ E.restrict π₂ = φ ∘ ρ' by
    rw [← comp.assoc, this, comp.assoc, Homeomorph.self_comp_symm, comp.right_id]
  ext x
  -- ⊢ (f ∘ restrict E π₂) x = (φ ∘ ↑ρ') x
  exact x.val.mem.symm
  -- 🎉 no goals

protected theorem CompactT2.projective_iff_extremallyDisconnnected [CompactSpace A] [T2Space A] :
    Projective A ↔ ExtremallyDisconnected A :=
  ⟨Projective.extremallyDisconnected, fun _ => ExtremallyDisconnected.projective⟩

end

-- Note: It might be possible to use Gleason for this instead
/-- The sigma-type of extremally disconnected spaces is extremally disconnected. -/
instance instExtremallyDisconnected {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [h₀ : ∀ i, ExtremallyDisconnected (π i)] : ExtremallyDisconnected (Σ i, π i) := by
  constructor
  -- ⊢ ∀ (U : Set ((i : ι) × π i)), IsOpen U → IsOpen (closure U)
  intro s hs
  -- ⊢ IsOpen (closure s)
  rw [isOpen_sigma_iff] at hs ⊢
  -- ⊢ ∀ (i : ι), IsOpen (Sigma.mk i ⁻¹' closure s)
  intro i
  -- ⊢ IsOpen (Sigma.mk i ⁻¹' closure s)
  rcases h₀ i with ⟨h₀⟩
  -- ⊢ IsOpen (Sigma.mk i ⁻¹' closure s)
  have h₁ : IsOpen (closure (Sigma.mk i ⁻¹' s))
  -- ⊢ IsOpen (closure (Sigma.mk i ⁻¹' s))
  · apply h₀
    -- ⊢ IsOpen (Sigma.mk i ⁻¹' s)
    exact hs i
    -- 🎉 no goals
  suffices h₂ : Sigma.mk i ⁻¹' closure s = closure (Sigma.mk i ⁻¹' s)
  -- ⊢ IsOpen (Sigma.mk i ⁻¹' closure s)
  · rwa [h₂]
    -- 🎉 no goals
  apply IsOpenMap.preimage_closure_eq_closure_preimage
  -- ⊢ IsOpenMap (Sigma.mk i)
  intro U _
  -- ⊢ IsOpen (Sigma.mk i '' U)
  · rw [isOpen_sigma_iff]
    -- ⊢ ∀ (i_1 : ι), IsOpen (Sigma.mk i_1 ⁻¹' (Sigma.mk i '' U))
    intro j
    -- ⊢ IsOpen (Sigma.mk j ⁻¹' (Sigma.mk i '' U))
    by_cases ij : i = j
    -- ⊢ IsOpen (Sigma.mk j ⁻¹' (Sigma.mk i '' U))
    · rw [← ij]
      -- ⊢ IsOpen (Sigma.mk i ⁻¹' (Sigma.mk i '' U))
      rw [sigma_mk_preimage_image_eq_self]
      -- ⊢ IsOpen U
      assumption
      -- 🎉 no goals
    · rw [sigma_mk_preimage_image' ij]
      -- ⊢ IsOpen ∅
      apply isOpen_empty
      -- 🎉 no goals
  · continuity
    -- 🎉 no goals
