/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Tactic.StacksAttribute
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Topology.Connected.Clopen

/-!
# Regular, normal, T₃, T₄ and T₅ spaces

This file continues the study of separation properties of topological spaces, focusing
on conditions strictly stronger than T₂.

## Main definitions

* `RegularSpace`: A regular space is one where, given any closed `C` and `x ∉ C`,
  there are disjoint open sets containing `x` and `C` respectively. Such a space is not necessarily
  Hausdorff.
* `T3Space`: A T₃ space is a regular T₀ space. T₃ implies T₂.₅.
* `NormalSpace`: A normal space, is one where given two disjoint closed sets,
  we can find two open sets that separate them. Such a space is not necessarily Hausdorff, even if
  it is T₀.
* `T4Space`: A T₄ space is a normal T₁ space. T₄ implies T₃.
* `CompletelyNormalSpace`: A completely normal space is one in which for any two sets `s`, `t`
  such that if both `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`,
  then there exist disjoint neighbourhoods of `s` and `t`. `Embedding.completelyNormalSpace` allows
  us to conclude that this is equivalent to all subspaces being normal. Such a space is not
  necessarily Hausdorff or regular, even if it is T₀.
* `T5Space`: A T₅ space is a completely normal T₁ space. T₅ implies T₄.

See `Mathlib/Topology/Separation/GDelta.lean` for the definitions of `PerfectlyNormalSpace` and
`T6Space`.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

## Main results

### Regular spaces

If the space is also Lindelöf:

* `NormalSpace.of_regularSpace_lindelofSpace`: every regular Lindelöf space is normal.

### T₃ spaces

* `disjoint_nested_nhds`: Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and
  `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* <https://en.wikipedia.org/wiki/Normal_space>
* [Willard's *General Topology*][zbMATH02107988]

-/

public section

assert_not_exists UniformSpace

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section RegularSpace

/-- A topological space is called a *regular space* if for any closed set `s` and `a ∉ s`, there
exist disjoint open sets `U ⊇ s` and `V ∋ a`. We formulate this condition in terms of `Disjoint`ness
of filters `𝓝ˢ s` and `𝓝 a`. -/
@[mk_iff]
class RegularSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `a` is a point that does not belong to a closed set `s`, then `a` and `s` admit disjoint
  neighborhoods. -/
  regular : ∀ {s : Set X} {a}, IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a)

theorem regularSpace_TFAE (X : Type u) [TopologicalSpace X] :
    List.TFAE [RegularSpace X,
      ∀ (s : Set X) x, x ∉ closure s → Disjoint (𝓝ˢ s) (𝓝 x),
      ∀ (x : X) (s : Set X), Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s,
      ∀ (x : X) (s : Set X), s ∈ 𝓝 x → ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s,
      ∀ x : X, (𝓝 x).lift' closure ≤ 𝓝 x,
      ∀ x : X, (𝓝 x).lift' closure = 𝓝 x] := by
  tfae_have 1 ↔ 5 := by
    rw [regularSpace_iff, (@compl_surjective (Set X) _).forall, forall_comm]
    simp only [isClosed_compl_iff, mem_compl_iff, Classical.not_not, @and_comm (_ ∈ _),
      (nhds_basis_opens _).lift'_closure.le_basis_iff (nhds_basis_opens _), and_imp,
      (nhds_basis_opens _).disjoint_iff_right, ← subset_interior_iff_mem_nhdsSet,
      interior_compl, compl_subset_compl]
  tfae_have 5 → 6 := fun h a => (h a).antisymm (𝓝 _).le_lift'_closure
  tfae_have 6 → 4
  | H, a, s, hs => by
    rw [← H] at hs
    rcases (𝓝 a).basis_sets.lift'_closure.mem_iff.mp hs with ⟨U, hU, hUs⟩
    exact ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, hUs⟩
  tfae_have 4 → 2
  | H, s, a, ha => by
    have ha' : sᶜ ∈ 𝓝 a := by rwa [← mem_interior_iff_mem_nhds, interior_compl]
    rcases H _ _ ha' with ⟨U, hU, hUc, hUs⟩
    refine disjoint_of_disjoint_of_mem disjoint_compl_left ?_ hU
    rwa [← subset_interior_iff_mem_nhdsSet, hUc.isOpen_compl.interior_eq, subset_compl_comm]
  tfae_have 2 → 3 := by
    refine fun H a s => ⟨fun hd has => mem_closure_iff_nhds_ne_bot.mp has ?_, H s a⟩
    exact (hd.symm.mono_right <| @principal_le_nhdsSet _ _ s).eq_bot
  tfae_have 3 → 1 := fun H => ⟨fun hs ha => (H _ _).mpr <| hs.closure_eq.symm ▸ ha⟩
  tfae_finish

theorem RegularSpace.of_lift'_closure_le (h : ∀ x : X, (𝓝 x).lift' closure ≤ 𝓝 x) :
    RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 4) h

theorem RegularSpace.of_lift'_closure (h : ∀ x : X, (𝓝 x).lift' closure = 𝓝 x) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 5) h

theorem RegularSpace.of_hasBasis {ι : X → Sort*} {p : ∀ a, ι a → Prop} {s : ∀ a, ι a → Set X}
    (h₁ : ∀ a, (𝓝 a).HasBasis (p a) (s a)) (h₂ : ∀ a i, p a i → IsClosed (s a i)) :
    RegularSpace X :=
  .of_lift'_closure fun a => (h₁ a).lift'_closure_eq_self (h₂ a)

theorem RegularSpace.of_exists_mem_nhds_isClosed_subset
    (h : ∀ (x : X), ∀ s ∈ 𝓝 x, ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s) : RegularSpace X :=
  Iff.mpr ((regularSpace_TFAE X).out 0 3) h

/-- A weakly locally compact R₁ space is regular. -/
instance (priority := 100) [WeaklyLocallyCompactSpace X] [R1Space X] : RegularSpace X :=
  .of_hasBasis isCompact_isClosed_basis_nhds fun _ _ ⟨_, _, h⟩ ↦ h

/-- Given a subbasis `s`, it is enough to check the condition of regularity for complements of sets
in `s`. -/
theorem regularSpace_generateFrom {s : Set (Set X)} (h : ‹_› = generateFrom s) :
    RegularSpace X ↔ ∀ t ∈ s, ∀ a ∈ t, Disjoint (𝓝ˢ tᶜ) (𝓝 a) := by
  refine ⟨fun _ t ht a ha => RegularSpace.regular
    (h ▸ isOpen_generateFrom_of_mem ht).isClosed_compl
    (Set.notMem_compl_iff.mpr ha), fun h' => ⟨fun {t a} ht ha => ?_⟩⟩
  obtain ⟨t, rfl⟩ := compl_involutive.surjective t
  rw [isClosed_compl_iff, h] at ht
  rw [Set.notMem_compl_iff] at ha
  induction ht with
  | basic t ht => exact h' t ht a ha
  | univ => simp
  | inter t₁ t₂ _ _ ih₁ ih₂ => grind [compl_inter, nhdsSet_union, disjoint_sup_left]
  | sUnion S _ ih =>
    obtain ⟨t, ht, ha⟩ := ha
    grw [compl_sUnion, sInter_image, iInter₂_subset t ht]
    exact ih t ht ha

section
variable [RegularSpace X] {x : X} {s : Set X}

theorem disjoint_nhdsSet_nhds : Disjoint (𝓝ˢ s) (𝓝 x) ↔ x ∉ closure s := by
  have h := (regularSpace_TFAE X).out 0 2
  exact h.mp ‹_› _ _

theorem disjoint_nhds_nhdsSet : Disjoint (𝓝 x) (𝓝ˢ s) ↔ x ∉ closure s :=
  disjoint_comm.trans disjoint_nhdsSet_nhds

/-- A regular space is R₁. -/
instance (priority := 100) : R1Space X where
  specializes_or_disjoint_nhds _ _ := or_iff_not_imp_left.2 fun h ↦ by
    rwa [← nhdsSet_singleton, disjoint_nhdsSet_nhds, ← specializes_iff_mem_closure]

theorem exists_mem_nhds_isClosed_subset {x : X} {s : Set X} (h : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝 x, IsClosed t ∧ t ⊆ s := by
  have h' := (regularSpace_TFAE X).out 0 3
  exact h'.mp ‹_› _ _ h

theorem closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsClosed s) id :=
  hasBasis_self.2 fun _ => exists_mem_nhds_isClosed_subset

theorem lift'_nhds_closure (x : X) : (𝓝 x).lift' closure = 𝓝 x :=
  (closed_nhds_basis x).lift'_closure_eq_self fun _ => And.right

theorem Filter.HasBasis.nhds_closure {ι : Sort*} {x : X} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p fun i => closure (s i) :=
  lift'_nhds_closure x ▸ h.lift'_closure

theorem hasBasis_nhds_closure (x : X) : (𝓝 x).HasBasis (fun s => s ∈ 𝓝 x) closure :=
  (𝓝 x).basis_sets.nhds_closure

theorem hasBasis_opens_closure (x : X) : (𝓝 x).HasBasis (fun s => x ∈ s ∧ IsOpen s) closure :=
  (nhds_basis_opens x).nhds_closure

theorem IsCompact.exists_isOpen_closure_subset {K U : Set X} (hK : IsCompact K) (hU : U ∈ 𝓝ˢ K) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U := by
  have hd : Disjoint (𝓝ˢ K) (𝓝ˢ Uᶜ) := by
    simpa [hK.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
      ← subset_interior_iff_mem_nhdsSet] using hU
  rcases ((hasBasis_nhdsSet _).disjoint_iff (hasBasis_nhdsSet _)).1 hd
    with ⟨V, ⟨hVo, hKV⟩, W, ⟨hW, hUW⟩, hVW⟩
  refine ⟨V, hVo, hKV, Subset.trans ?_ (compl_subset_comm.1 hUW)⟩
  exact closure_minimal hVW.subset_compl_right hW.isClosed_compl

theorem IsCompact.lift'_closure_nhdsSet {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).lift' closure = 𝓝ˢ K := by
  refine le_antisymm (fun U hU ↦ ?_) (le_lift'_closure _)
  rcases hK.exists_isOpen_closure_subset hU with ⟨V, hVo, hKV, hVU⟩
  exact mem_of_superset (mem_lift' <| hVo.mem_nhdsSet.2 hKV) hVU

theorem TopologicalSpace.IsTopologicalBasis.nhds_basis_closure {B : Set (Set X)}
    (hB : IsTopologicalBasis B) (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ s ∈ B) closure := by
  simpa only [and_comm] using hB.nhds_hasBasis.nhds_closure

theorem TopologicalSpace.IsTopologicalBasis.exists_closure_subset {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {x : X} {s : Set X} (h : s ∈ 𝓝 x) :
    ∃ t ∈ B, x ∈ t ∧ closure t ⊆ s := by
  simpa only [exists_prop, and_assoc] using hB.nhds_hasBasis.nhds_closure.mem_iff.mp h

/-- In a regular space with a topological basis `B`, any open set `U` can be written as the union
of the sets in `B` whose closures are contained in `U`. -/
theorem TopologicalSpace.IsTopologicalBasis.open_eq_iUnion_of_closure_subset {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {U : Set X} (hU : IsOpen U) :
    U = ⋃ v ∈ B, ⋃ (_ : closure v ⊆ U), v := by
  ext x
  simp only [mem_iUnion, exists_prop]
  refine ⟨fun hx ↦ ?_, fun ⟨t, ht1, ht2, hx⟩ ↦ ht2 <| subset_closure hx⟩
  obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ : ∃ v, (x ∈ v ∧ v ∈ B) ∧ closure v ⊆ U :=
    hB.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
  exact ⟨v, hv2, hv3, hv1⟩

/-- In a regular space with a topological basis `B`, any open set `U` can be written as the union
of the sets in `B` whose closures are contained in `U`. -/
theorem TopologicalSpace.IsTopologicalBasis.open_eq_sUnion_of_closure_subset {B : Set (Set X)}
    (hB : IsTopologicalBasis B) {U : Set X} (hU : IsOpen U) :
    U = ⋃₀ {v | v ∈ B ∧ closure v ⊆ U} := by
  convert hB.open_eq_iUnion_of_closure_subset hU
  ext; simp; grind

/-- In a regular space with a topological basis `B`, any open set `U` can be written as the union
of the closures of the sets in `B` whose closures are contained in `U`. -/
theorem TopologicalSpace.IsTopologicalBasis.open_eq_iUnion_closure
    {B : Set (Set X)} (hB : IsTopologicalBasis B) {U : Set X} (hU : IsOpen U) :
    U = ⋃ v ∈ B, ⋃ (_ : closure v ⊆ U), closure v := by
  ext x
  simp only [mem_iUnion, exists_prop]
  refine ⟨fun hx ↦ ?_, fun ⟨t, ht1, ht2, hx⟩ ↦ ht2 hx⟩
  obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ : ∃ v, (x ∈ v ∧ v ∈ B) ∧ closure v ⊆ U :=
    hB.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
  exact ⟨v, hv2, hv3, subset_closure hv1⟩

/-- In a regular space with a topological basis `B`, any open set `U` can be written as the union
of the closures of the sets in `B` whose closures are contained in `U`. -/
theorem TopologicalSpace.IsTopologicalBasis.open_eq_sUnion_closure
    {B : Set (Set X)} (hB : IsTopologicalBasis B) {U : Set X} (hU : IsOpen U) :
    U = ⋃₀ {v | ∃ u ∈ B, closure u ⊆ U ∧ v = closure u} := by
  convert hB.open_eq_iUnion_closure hU
  ext; simp; grind

protected theorem Topology.IsInducing.regularSpace [TopologicalSpace Y] {f : Y → X}
    (hf : IsInducing f) : RegularSpace Y :=
  .of_hasBasis
    (fun b => by rw [hf.nhds_eq_comap b]; exact (closed_nhds_basis _).comap _)
    fun b s hs => by exact hs.2.preimage hf.continuous

theorem regularSpace_induced (f : Y → X) : @RegularSpace Y (induced f ‹_›) :=
  letI := induced f ‹_›
  (IsInducing.induced f).regularSpace

theorem regularSpace_sInf {X} {T : Set (TopologicalSpace X)} (h : ∀ t ∈ T, @RegularSpace X t) :
    @RegularSpace X (sInf T) := by
  let _ := sInf T
  have : ∀ a, (𝓝 a).HasBasis
      (fun If : Σ I : Set T, I → Set X =>
        If.1.Finite ∧ ∀ i : If.1, If.2 i ∈ @nhds X i a ∧ @IsClosed X i (If.2 i))
      fun If => ⋂ i : If.1, If.snd i := fun a ↦ by
    rw [nhds_sInf, ← iInf_subtype'']
    exact .iInf fun t : T => @closed_nhds_basis X t (h t t.2) a
  refine .of_hasBasis this fun a If hIf => isClosed_iInter fun i => ?_
  exact (hIf.2 i).2.mono (sInf_le (i : T).2)

theorem regularSpace_iInf {ι X} {t : ι → TopologicalSpace X} (h : ∀ i, @RegularSpace X (t i)) :
    @RegularSpace X (iInf t) :=
  regularSpace_sInf <| forall_mem_range.mpr h

theorem RegularSpace.inf {X} {t₁ t₂ : TopologicalSpace X} (h₁ : @RegularSpace X t₁)
    (h₂ : @RegularSpace X t₂) : @RegularSpace X (t₁ ⊓ t₂) := by
  rw [inf_eq_iInf]
  exact regularSpace_iInf (Bool.forall_bool.2 ⟨h₂, h₁⟩)

instance {p : X → Prop} : RegularSpace (Subtype p) :=
  IsEmbedding.subtypeVal.isInducing.regularSpace

instance [TopologicalSpace Y] [RegularSpace Y] : RegularSpace (X × Y) :=
  (regularSpace_induced (@Prod.fst X Y)).inf (regularSpace_induced (@Prod.snd X Y))

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, RegularSpace (X i)] :
    RegularSpace (∀ i, X i) :=
  regularSpace_iInf fun _ => regularSpace_induced _

/-- In a regular space, if a compact set and a closed set are disjoint, then they have disjoint
neighborhoods. -/
lemma SeparatedNhds.of_isCompact_isClosed {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) : SeparatedNhds s t := by
  simpa only [separatedNhds_iff_disjoint, hs.disjoint_nhdsSet_left, disjoint_nhds_nhdsSet,
    ht.closure_eq, disjoint_left] using hst

end

/-- This technique to witness `HasSeparatingCover` in regular Lindelöf topological spaces
will be used to prove regular Lindelöf spaces are normal. -/
lemma IsClosed.HasSeparatingCover {s t : Set X} [LindelofSpace X] [RegularSpace X]
    (s_cl : IsClosed s) (t_cl : IsClosed t) (st_dis : Disjoint s t) : HasSeparatingCover s t := by
  -- `IsLindelof.indexed_countable_subcover` requires the space be Nonempty
  rcases isEmpty_or_nonempty X with empty_X | nonempty_X
  · rw [subset_eq_empty (t := s) (fun ⦃_⦄ _ ↦ trivial) (univ_eq_empty_iff.mpr empty_X)]
    exact hasSeparatingCovers_iff_separatedNhds.mpr (SeparatedNhds.empty_left t) |>.1
  -- This is almost `HasSeparatingCover`, but is not countable. We define for all `a : X` for use
  -- with `IsLindelof.indexed_countable_subcover` momentarily.
  have (a : X) : ∃ n : Set X, IsOpen n ∧ Disjoint (closure n) t ∧ (a ∈ s → a ∈ n) := by
    wlog ains : a ∈ s
    · exact ⟨∅, isOpen_empty, SeparatedNhds.empty_left t |>.disjoint_closure_left, fun a ↦ ains a⟩
    obtain ⟨n, nna, ncl, nsubkc⟩ := ((regularSpace_TFAE X).out 0 3 :).mp ‹RegularSpace X› a tᶜ <|
      t_cl.compl_mem_nhds (disjoint_left.mp st_dis ains)
    exact
      ⟨interior n,
       isOpen_interior,
       disjoint_left.mpr fun ⦃_⦄ ain ↦
         nsubkc <| (IsClosed.closure_subset_iff ncl).mpr interior_subset ain,
       fun _ ↦ mem_interior_iff_mem_nhds.mpr nna⟩
  -- By Lindelöf, we may obtain a countable subcover witnessing `HasSeparatingCover`
  choose u u_open u_dis u_nhds using this
  obtain ⟨f, f_cov⟩ := s_cl.isLindelof.indexed_countable_subcover
    u u_open (fun a ainh ↦ mem_iUnion.mpr ⟨a, u_nhds a ainh⟩)
  exact ⟨u ∘ f, f_cov, fun n ↦ ⟨u_open (f n), u_dis (f n)⟩⟩

/-- Given two separable points `x` and `y`, we can find neighbourhoods
`x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`, with the `Vₖ` closed and the `Uₖ` open,
such that the `Uₖ` are disjoint. -/
theorem disjoint_nested_nhds_of_not_inseparable [RegularSpace X] {x y : X} (h : ¬Inseparable x y) :
    ∃ U₁ ∈ 𝓝 x, ∃ V₁ ∈ 𝓝 x, ∃ U₂ ∈ 𝓝 y, ∃ V₂ ∈ 𝓝 y,
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ Disjoint U₁ U₂ := by
  rcases r1_separation h with ⟨U₁, U₂, U₁_op, U₂_op, x_in, y_in, H⟩
  rcases exists_mem_nhds_isClosed_subset (U₁_op.mem_nhds x_in) with ⟨V₁, V₁_in, V₁_closed, h₁⟩
  rcases exists_mem_nhds_isClosed_subset (U₂_op.mem_nhds y_in) with ⟨V₂, V₂_in, V₂_closed, h₂⟩
  exact ⟨U₁, mem_of_superset V₁_in h₁, V₁, V₁_in, U₂, mem_of_superset V₂_in h₂, V₂, V₂_in,
    V₁_closed, V₂_closed, U₁_op, U₂_op, h₁, h₂, H⟩

end RegularSpace

section LocallyCompactRegularSpace

/-- In a (possibly non-Hausdorff) locally compact regular space, for every containment `K ⊆ U` of
  a compact set `K` in an open set `U`, there is a compact closed neighborhood `L`
  such that `K ⊆ L ⊆ U`: equivalently, there is a compact closed set `L` such
  that `K ⊆ interior L` and `L ⊆ U`. -/
theorem exists_compact_closed_between [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (h_KU : K ⊆ U) :
    ∃ L, IsCompact L ∧ IsClosed L ∧ K ⊆ interior L ∧ L ⊆ U :=
  let ⟨L, L_comp, KL, LU⟩ := exists_compact_between hK hU h_KU
  ⟨closure L, L_comp.closure, isClosed_closure, KL.trans <| interior_mono subset_closure,
    L_comp.closure_subset_of_isOpen hU LU⟩

/-- In a (possibly non-Hausdorff) locally compact regular space, for every compact set `K`,
`𝓝ˢ K` has a basis consisting of closed compact sets. -/
theorem IsCompact.nhdsSet_basis_isCompact_isClosed
    [LocallyCompactSpace X] [RegularSpace X] {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun L ↦ L ∈ 𝓝ˢ K ∧ IsCompact L ∧ IsClosed L) id := by
  rw [hasBasis_self, (hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hL', hKL, hLU⟩ := exists_compact_closed_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], ⟨hL, hL'⟩, hLU⟩

/-- In a locally compact regular space, given a compact set `K` inside an open set `U`, we can find
an open set `V` between these sets with compact closure: `K ⊆ V` and the closure of `V` is
inside `U`. -/
theorem exists_open_between_and_isCompact_closure [LocallyCompactSpace X] [RegularSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) := by
  rcases exists_compact_closed_between hK hU hKU with ⟨L, L_compact, L_closed, KL, LU⟩
  have A : closure (interior L) ⊆ L := by
    apply (closure_mono interior_subset).trans (le_of_eq L_closed.closure_eq)
  refine ⟨interior L, isOpen_interior, KL, A.trans LU, ?_⟩
  exact L_compact.closure_of_subset interior_subset

lemma IsCompact.closure_eq_nhdsKer [RegularSpace X] {s : Set X} (hs : IsCompact s) :
    closure s = nhdsKer s := by
  apply subset_antisymm
  · rw [nhdsKer, ← hs.lift'_closure_nhdsSet]
    simp +contextual [Filter.lift', Filter.lift, closure_mono, subset_of_mem_nhdsSet]
  · intro y hy
    by_contra! hy'
    rw [← _root_.disjoint_nhdsSet_nhds, Filter.disjoint_iff] at hy'
    obtain ⟨t, hts, t', ht'y, H⟩ := hy'
    exact Set.disjoint_iff.mp H ⟨hy t hts, mem_of_mem_nhds ht'y⟩

end LocallyCompactRegularSpace

section T25

/-- A T₂.₅ space, also known as a Urysohn space, is a topological space
  where for every pair `x ≠ y`, there are two open sets, with the intersection of closures
  empty, one containing `x` and the other `y` . -/
class T25Space (X : Type u) [TopologicalSpace X] : Prop where
  /-- Given two distinct points in a T₂.₅ space, their filters of closed neighborhoods are
  disjoint. -/
  t2_5 : ∀ ⦃x y : X⦄, x ≠ y → Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure)

@[simp]
theorem disjoint_lift'_closure_nhds [T25Space X] {x y : X} :
    Disjoint ((𝓝 x).lift' closure) ((𝓝 y).lift' closure) ↔ x ≠ y :=
  ⟨fun h hxy => by simp [hxy, nhds_neBot.ne] at h, fun h => T25Space.t2_5 h⟩

-- see Note [lower instance priority]
instance (priority := 100) T25Space.t2Space [T25Space X] : T2Space X :=
  t2Space_iff_disjoint_nhds.2 fun _ _ hne =>
    (disjoint_lift'_closure_nhds.2 hne).mono (le_lift'_closure _) (le_lift'_closure _)

theorem exists_nhds_disjoint_closure [T25Space X] {x y : X} (h : x ≠ y) :
    ∃ s ∈ 𝓝 x, ∃ t ∈ 𝓝 y, Disjoint (closure s) (closure t) :=
  ((𝓝 x).basis_sets.lift'_closure.disjoint_iff (𝓝 y).basis_sets.lift'_closure).1 <|
    disjoint_lift'_closure_nhds.2 h

theorem exists_open_nhds_disjoint_closure [T25Space X] {x y : X} (h : x ≠ y) :
    ∃ u : Set X,
      x ∈ u ∧ IsOpen u ∧ ∃ v : Set X, y ∈ v ∧ IsOpen v ∧ Disjoint (closure u) (closure v) := by
  simpa only [exists_prop, and_assoc] using
    ((nhds_basis_opens x).lift'_closure.disjoint_iff (nhds_basis_opens y).lift'_closure).1
      (disjoint_lift'_closure_nhds.2 h)

theorem T25Space.of_injective_continuous [TopologicalSpace Y] [T25Space Y] {f : X → Y}
    (hinj : Injective f) (hcont : Continuous f) : T25Space X where
  t2_5 x y hne := (tendsto_lift'_closure_nhds hcont x).disjoint (t2_5 <| hinj.ne hne)
    (tendsto_lift'_closure_nhds hcont y)

theorem Topology.IsEmbedding.t25Space [TopologicalSpace Y] [T25Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T25Space X :=
  .of_injective_continuous hf.injective hf.continuous

protected theorem Homeomorph.t25Space [TopologicalSpace Y] [T25Space X] (h : X ≃ₜ Y) : T25Space Y :=
  h.symm.isEmbedding.t25Space

instance Subtype.instT25Space [T25Space X] {p : X → Prop} : T25Space {x // p x} :=
  IsEmbedding.subtypeVal.t25Space

end T25

section T3

/-- A T₃ space is a T₀ space which is a regular space. Any T₃ space is a T₁ space, a T₂ space, and
a T₂.₅ space. -/
class T3Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, RegularSpace X

instance (priority := 90) instT3Space [T0Space X] [RegularSpace X] : T3Space X := ⟨⟩

theorem RegularSpace.t3Space_iff_t0Space [RegularSpace X] : T3Space X ↔ T0Space X := by
  constructor <;> intro <;> infer_instance

-- see Note [lower instance priority]
instance (priority := 100) T3Space.t25Space [T3Space X] : T25Space X := by
  refine ⟨fun x y hne => ?_⟩
  rw [lift'_nhds_closure, lift'_nhds_closure]
  have : x ∉ closure {y} ∨ y ∉ closure {x} :=
    (t0Space_iff_or_notMem_closure X).mp inferInstance hne
  simp only [← disjoint_nhds_nhdsSet, nhdsSet_singleton] at this
  exact this.elim id fun h => h.symm

protected theorem Topology.IsEmbedding.t3Space [TopologicalSpace Y] [T3Space Y] {f : X → Y}
    (hf : IsEmbedding f) : T3Space X :=
  { toT0Space := hf.t0Space
    toRegularSpace := hf.isInducing.regularSpace }

protected theorem Homeomorph.t3Space [TopologicalSpace Y] [T3Space X] (h : X ≃ₜ Y) : T3Space Y :=
  h.symm.isEmbedding.t3Space

instance Subtype.t3Space [T3Space X] {p : X → Prop} : T3Space (Subtype p) :=
  IsEmbedding.subtypeVal.t3Space

instance ULift.instT3Space [T3Space X] : T3Space (ULift X) :=
  IsEmbedding.uliftDown.t3Space

instance [TopologicalSpace Y] [T3Space X] [T3Space Y] : T3Space (X × Y) := ⟨⟩

instance {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T3Space (X i)] :
    T3Space (∀ i, X i) := ⟨⟩

/-- Given two points `x ≠ y`, we can find neighbourhoods `x ∈ V₁ ⊆ U₁` and `y ∈ V₂ ⊆ U₂`,
with the `Vₖ` closed and the `Uₖ` open, such that the `Uₖ` are disjoint. -/
theorem disjoint_nested_nhds [T3Space X] {x y : X} (h : x ≠ y) :
    ∃ U₁ ∈ 𝓝 x, ∃ V₁ ∈ 𝓝 x, ∃ U₂ ∈ 𝓝 y, ∃ V₂ ∈ 𝓝 y,
      IsClosed V₁ ∧ IsClosed V₂ ∧ IsOpen U₁ ∧ IsOpen U₂ ∧ V₁ ⊆ U₁ ∧ V₂ ⊆ U₂ ∧ Disjoint U₁ U₂ :=
  disjoint_nested_nhds_of_not_inseparable (mt Inseparable.eq h)

open SeparationQuotient

/-- The `SeparationQuotient` of a regular space is a T₃ space. -/
instance [RegularSpace X] : T3Space (SeparationQuotient X) where
  regular {s a} hs ha := by
    rcases surjective_mk a with ⟨a, rfl⟩
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhds_mk, comap_mk_nhdsSet]
    exact RegularSpace.regular (hs.preimage continuous_mk) ha

end T3

section NormalSpace

/-- A topological space is said to be a *normal space* if any two disjoint closed sets
have disjoint open neighborhoods. -/
class NormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Two disjoint sets in a normal space admit disjoint neighbourhoods. -/
  normal : ∀ s t : Set X, IsClosed s → IsClosed t → Disjoint s t → SeparatedNhds s t

theorem normal_separation [NormalSpace X] {s t : Set X} (H1 : IsClosed s) (H2 : IsClosed t)
    (H3 : Disjoint s t) : SeparatedNhds s t :=
  NormalSpace.normal s t H1 H2 H3

theorem disjoint_nhdsSet_nhdsSet [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : Disjoint (𝓝ˢ s) (𝓝ˢ t) :=
  (normal_separation hs ht hd).disjoint_nhdsSet

theorem normal_exists_closure_subset [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t)
    (hst : s ⊆ t) : ∃ u, IsOpen u ∧ s ⊆ u ∧ closure u ⊆ t := by
  have : Disjoint s tᶜ := Set.disjoint_left.mpr fun x hxs hxt => hxt (hst hxs)
  rcases normal_separation hs (isClosed_compl_iff.2 ht) this with
    ⟨s', t', hs', ht', hss', htt', hs't'⟩
  refine ⟨s', hs', hss', Subset.trans (closure_minimal ?_ (isClosed_compl_iff.2 ht'))
    (compl_subset_comm.1 htt')⟩
  exact fun x hxs hxt => hs't'.le_bot ⟨hxs, hxt⟩

/-- If the codomain of a closed embedding is a normal space, then so is the domain. -/
protected theorem Topology.IsClosedEmbedding.normalSpace [TopologicalSpace Y] [NormalSpace Y]
    {f : X → Y} (hf : IsClosedEmbedding f) : NormalSpace X where
  normal s t hs ht hst := by
    have H : SeparatedNhds (f '' s) (f '' t) :=
      NormalSpace.normal (f '' s) (f '' t) (hf.isClosedMap s hs) (hf.isClosedMap t ht)
        (disjoint_image_of_injective hf.injective hst)
    exact (H.preimage hf.continuous).mono (subset_preimage_image _ _) (subset_preimage_image _ _)

protected theorem Homeomorph.normalSpace [TopologicalSpace Y] [NormalSpace X] (h : X ≃ₜ Y) :
    NormalSpace Y :=
  h.symm.isClosedEmbedding.normalSpace

instance (priority := 100) NormalSpace.of_compactSpace_r1Space [CompactSpace X] [R1Space X] :
    NormalSpace X where
  normal _s _t hs ht := .of_isCompact_isCompact_isClosed hs.isCompact ht.isCompact ht

/-- A regular topological space with a Lindelöf topology is a normal space. A consequence of e.g.
Corollaries 20.8 and 20.10 of [Willard's *General Topology*][zbMATH02107988] (without the
assumption of Hausdorff). -/
instance (priority := 100) NormalSpace.of_regularSpace_lindelofSpace
    [RegularSpace X] [LindelofSpace X] : NormalSpace X where
  normal _ _ hcl kcl hkdis :=
    hasSeparatingCovers_iff_separatedNhds.mp
    ⟨hcl.HasSeparatingCover kcl hkdis, kcl.HasSeparatingCover hcl (Disjoint.symm hkdis)⟩

instance (priority := 100) NormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : NormalSpace X :=
  of_regularSpace_lindelofSpace

end NormalSpace

section Normality

/-- A T₄ space is a normal T₁ space. -/
class T4Space (X : Type u) [TopologicalSpace X] : Prop extends T1Space X, NormalSpace X

instance (priority := 100) [T1Space X] [NormalSpace X] : T4Space X := ⟨⟩

-- see Note [lower instance priority]
instance (priority := 100) T4Space.t3Space [T4Space X] : T3Space X where
  regular hs hxs := by simpa only [nhdsSet_singleton] using (normal_separation hs isClosed_singleton
    (disjoint_singleton_right.mpr hxs)).disjoint_nhdsSet

/-- If the codomain of a closed embedding is a T₄ space, then so is the domain. -/
protected theorem Topology.IsClosedEmbedding.t4Space [TopologicalSpace Y] [T4Space Y] {f : X → Y}
    (hf : IsClosedEmbedding f) : T4Space X where
  toT1Space := hf.isEmbedding.t1Space
  toNormalSpace := hf.normalSpace

protected theorem Homeomorph.t4Space [TopologicalSpace Y] [T4Space X] (h : X ≃ₜ Y) : T4Space Y :=
  h.symm.isClosedEmbedding.t4Space

instance ULift.instT4Space [T4Space X] : T4Space (ULift X) := IsClosedEmbedding.uliftDown.t4Space

namespace SeparationQuotient

/-- The `SeparationQuotient` of a normal space is a normal space. -/
instance [NormalSpace X] : NormalSpace (SeparationQuotient X) where
  normal s t hs ht hd := separatedNhds_iff_disjoint.2 <| by
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhdsSet, comap_mk_nhdsSet]
    exact disjoint_nhdsSet_nhdsSet (hs.preimage continuous_mk) (ht.preimage continuous_mk)
      (hd.preimage mk)

end SeparationQuotient

end Normality

section CompletelyNormal

/-- A topological space `X` is a *completely normal space* provided that for any two sets `s`, `t`
such that if both `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`,
then there exist disjoint neighbourhoods of `s` and `t`. -/
class CompletelyNormalSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- If `closure s` is disjoint with `t`, and `s` is disjoint with `closure t`, then `s` and `t`
  admit disjoint neighbourhoods. -/
  completely_normal :
    ∀ ⦃s t : Set X⦄, Disjoint (closure s) t → Disjoint s (closure t) → Disjoint (𝓝ˢ s) (𝓝ˢ t)

export CompletelyNormalSpace (completely_normal)

-- see Note [lower instance priority]
/-- A completely normal space is a normal space. -/
instance (priority := 100) CompletelyNormalSpace.toNormalSpace
    [CompletelyNormalSpace X] : NormalSpace X where
  normal s t hs ht hd := separatedNhds_iff_disjoint.2 <|
    completely_normal (by rwa [hs.closure_eq]) (by rwa [ht.closure_eq])

theorem Topology.IsEmbedding.completelyNormalSpace [TopologicalSpace Y] [CompletelyNormalSpace Y]
    {e : X → Y} (he : IsEmbedding e) : CompletelyNormalSpace X := by
  refine ⟨fun s t hd₁ hd₂ => ?_⟩
  simp only [he.isInducing.nhdsSet_eq_comap]
  refine disjoint_comap (completely_normal ?_ ?_)
  · rwa [← subset_compl_iff_disjoint_left, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_left]
  · rwa [← subset_compl_iff_disjoint_right, image_subset_iff, preimage_compl,
      ← he.closure_eq_preimage_closure_image, subset_compl_iff_disjoint_right]

/-- A subspace of a completely normal space is a completely normal space. -/
instance [CompletelyNormalSpace X] {p : X → Prop} : CompletelyNormalSpace { x // p x } :=
  IsEmbedding.subtypeVal.completelyNormalSpace

instance ULift.instCompletelyNormalSpace [CompletelyNormalSpace X] :
    CompletelyNormalSpace (ULift X) :=
  IsEmbedding.uliftDown.completelyNormalSpace

/--
A space is completely normal iff all open subspaces are normal.
-/
theorem completelyNormalSpace_iff_forall_isOpen_normalSpace :
    CompletelyNormalSpace X ↔ ∀ s : Set X, IsOpen s → NormalSpace s := by
  refine ⟨fun _ _ _ => inferInstance, fun h => ⟨fun s t hSt hsT => ?_⟩⟩
  let e := (closure s ∩ closure t)ᶜ
  have he : IsOpen e := (isClosed_closure.inter isClosed_closure).isOpen_compl
  specialize h e he
  have hst : Disjoint (((↑) : e → X) ⁻¹' closure s) (((↑) : e → X) ⁻¹' closure t) := by
    rw [disjoint_left]
    intro x hxs hxt
    exact x.2 ⟨hxs, hxt⟩
  obtain ⟨U, V, hU, hV, hsU, htV, hUV⟩ := normal_separation
    (isClosed_closure.preimage continuous_subtype_val)
    (isClosed_closure.preimage continuous_subtype_val) hst
  rw [Topology.IsInducing.subtypeVal.isOpen_iff] at hU hV
  obtain ⟨U, hU, rfl⟩ := hU
  obtain ⟨V, hV, rfl⟩ := hV
  rw [← separatedNhds_iff_disjoint]
  rw [Subtype.preimage_val_subset_preimage_val_iff, inter_comm e, inter_comm e] at hsU htV
  refine ⟨U ∩ e, V ∩ e, hU.inter he, hV.inter he, ?_, ?_, ?_⟩
  · intro x hx
    exact hsU ⟨subset_closure hx, fun h => hsT.notMem_of_mem_left hx h.2⟩
  · intro x hx
    exact htV ⟨subset_closure hx, fun h => hSt.notMem_of_mem_left h.1 hx⟩
  · rw [disjoint_left] at hUV ⊢
    intro x hxU hxV
    exact @hUV ⟨x, hxU.2⟩ hxU.1 hxV.1

/--
A space is completely normal iff it is hereditarily normal.
-/
theorem completelyNormalSpace_iff_forall_normalSpace :
    CompletelyNormalSpace X ↔ ∀ s : Set X, NormalSpace s :=
  ⟨fun _ _ => inferInstance, fun h =>
    completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s _ => h s⟩

alias ⟨_, CompletelyNormalSpace.of_forall_isOpen_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_isOpen_normalSpace
alias ⟨_, CompletelyNormalSpace.of_forall_normalSpace⟩ :=
  completelyNormalSpace_iff_forall_normalSpace

instance (priority := 100) CompletelyNormalSpace.of_regularSpace_secondCountableTopology
    [RegularSpace X] [SecondCountableTopology X] : CompletelyNormalSpace X :=
  .of_forall_normalSpace fun _ => .of_regularSpace_secondCountableTopology

/-- A T₅ space is a completely normal T₁ space. -/
class T5Space (X : Type u) [TopologicalSpace X] : Prop extends T1Space X, CompletelyNormalSpace X

theorem Topology.IsEmbedding.t5Space [TopologicalSpace Y] [T5Space Y] {e : X → Y}
    (he : IsEmbedding e) : T5Space X where
  __ := he.t1Space
  completely_normal := by
    have := he.completelyNormalSpace
    exact completely_normal

protected theorem Homeomorph.t5Space [TopologicalSpace Y] [T5Space X] (h : X ≃ₜ Y) : T5Space Y :=
  h.symm.isClosedEmbedding.t5Space

-- see Note [lower instance priority]
/-- A `T₅` space is a `T₄` space. -/
instance (priority := 100) T5Space.toT4Space [T5Space X] : T4Space X where
  -- follows from type-class inference

/-- A subspace of a T₅ space is a T₅ space. -/
instance [T5Space X] {p : X → Prop} : T5Space { x // p x } :=
  IsEmbedding.subtypeVal.t5Space

instance ULift.instT5Space [T5Space X] : T5Space (ULift X) :=
  IsEmbedding.uliftDown.t5Space

/--
A space is a `T5Space` iff all its open subspaces are `T4Space`.
-/
theorem t5Space_iff_forall_isOpen_t4Space :
    T5Space X ↔ ∀ s : Set X, IsOpen s → T4Space s where
  mp _ _ _ := inferInstance
  mpr h :=
    { toCompletelyNormalSpace :=
        completelyNormalSpace_iff_forall_isOpen_normalSpace.2 fun s hs => (h s hs).toNormalSpace
      toT1Space :=
        have := h univ isOpen_univ
        t1Space_of_injective_of_continuous
          (fun _ _ => congrArg Subtype.val) (continuous_id.subtype_mk mem_univ) }

/--
A space is `T5Space` iff it is hereditarily `T4Space`.
-/
theorem t5Space_iff_forall_t4Space :
    T5Space X ↔ ∀ s : Set X, T4Space s :=
  ⟨fun _ _ => inferInstance, fun h => t5Space_iff_forall_isOpen_t4Space.2 fun s _ => h s⟩

alias ⟨_, T5Space.of_forall_isOpen_t4Space⟩ := t5Space_iff_forall_isOpen_t4Space
alias ⟨_, T5Space.of_forall_t4Space⟩ := t5Space_iff_forall_t4Space

open SeparationQuotient

/-- The `SeparationQuotient` of a completely normal R₀ space is a T₅ space. -/
instance [CompletelyNormalSpace X] [R0Space X] : T5Space (SeparationQuotient X) where
  t1 := by
    rwa [((t1Space_TFAE (SeparationQuotient X)).out 1 0 :), SeparationQuotient.t1Space_iff]
  completely_normal s t hd₁ hd₂ := by
    rw [← disjoint_comap_iff surjective_mk, comap_mk_nhdsSet, comap_mk_nhdsSet]
    apply completely_normal <;> rw [← preimage_mk_closure]
    exacts [hd₁.preimage mk, hd₂.preimage mk]

end CompletelyNormal

/-- In a compact T₂ space, the connected component of a point equals the intersection of all
its clopen neighbourhoods. -/
theorem connectedComponent_eq_iInter_isClopen [T2Space X] [CompactSpace X] (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s := by
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  -- Reduce to showing that the clopen intersection is connected.
  refine IsPreconnected.subset_connectedComponent ?_ (mem_iInter.2 fun s => s.2.2)
  -- We do this by showing that any disjoint cover by two closed sets implies
  -- that one of these closed sets must contain our whole thing.
  -- To reduce to the case where the cover is disjoint on all of `X` we need that `s` is closed
  have hs : @IsClosed X _ (⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s) :=
    isClosed_iInter fun s => s.2.1.1
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hs]
  intro a b ha hb hab ab_disj
  -- Since our space is normal, we get two larger disjoint open sets containing the disjoint
  -- closed sets. If we can show that our intersection is a subset of any of these we can then
  -- "descend" this to show that it is a subset of either a or b.
  rcases normal_separation ha hb ab_disj with ⟨u, v, hu, hv, hau, hbv, huv⟩
  obtain ⟨s, H⟩ : ∃ s : Set X, IsClopen s ∧ x ∈ s ∧ s ⊆ u ∪ v := by
    /- Now we find a clopen set `s` around `x`, contained in `u ∪ v`. We utilize the fact that
    `X \ u ∪ v` will be compact, so there must be some finite intersection of clopen neighbourhoods
    of `X` disjoint to it, but a finite intersection of clopen sets is clopen,
    so we let this be our `s`. -/
    have H1 := (hu.union hv).isClosed_compl.isCompact.inter_iInter_nonempty
      (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s) fun s => s.2.1.1
    rw [← not_disjoint_iff_nonempty_inter, imp_not_comm, not_forall] at H1
    obtain ⟨si, H2⟩ :=
      H1 (disjoint_compl_left_iff_subset.2 <| hab.trans <| union_subset_union hau hbv)
    refine ⟨⋂ U ∈ si, Subtype.val U, ?_, ?_, ?_⟩
    · exact isClopen_biInter_finset fun s _ => s.2.1
    · exact mem_iInter₂.2 fun s _ => s.2.2
    · rwa [← disjoint_compl_left_iff_subset, disjoint_iff_inter_eq_empty,
        ← not_nonempty_iff_eq_empty]
  -- So, we get a disjoint decomposition `s = s ∩ u ∪ s ∩ v` of clopen sets. The intersection of all
  -- clopen neighbourhoods will then lie in whichever of u or v x lies in and hence will be a subset
  -- of either a or b.
  · have H1 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hu hv huv
    rw [union_comm] at H
    have H2 := isClopen_inter_of_disjoint_cover_clopen H.1 H.2.2 hv hu huv.symm
    by_cases hxu : x ∈ u <;> [left; right]
    -- The x ∈ u case.
    · suffices ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, ↑s ⊆ u
        from Disjoint.left_le_of_le_sup_right hab (huv.mono this hbv)
      · apply Subset.trans _ s.inter_subset_right
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s.1)
          ⟨s ∩ u, H1, mem_inter H.2.1 hxu⟩
    -- If x ∉ u, we get x ∈ v since x ∈ u ∪ v. The rest is then like the x ∈ u case.
    · have h1 : x ∈ v :=
        (hab.trans (union_subset_union hau hbv) (mem_iInter.2 fun i => i.2.2)).resolve_left hxu
      suffices ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, ↑s ⊆ v
        from (huv.symm.mono this hau).left_le_of_le_sup_left hab
      · refine Subset.trans ?_ s.inter_subset_right
        exact iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => s.1)
          ⟨s ∩ v, H2, mem_inter H.2.1 h1⟩

/-- `ConnectedComponents X` is Hausdorff when `X` is Hausdorff and compact -/
@[stacks 0900 "The Stacks entry proves profiniteness."]
instance ConnectedComponents.t2 [T2Space X] [CompactSpace X] : T2Space (ConnectedComponents X) := by
  -- Fix 2 distinct connected components, with points a and b
  refine ⟨ConnectedComponents.surjective_coe.forall₂.2 fun a b ne => ?_⟩
  rw [ConnectedComponents.coe_ne_coe] at ne
  have h := connectedComponent_disjoint ne
  -- write ↑b as the intersection of all clopen subsets containing it
  rw [connectedComponent_eq_iInter_isClopen b, disjoint_iff_inter_eq_empty] at h
  -- Now we show that this can be reduced to some clopen containing `↑b` being disjoint to `↑a`
  obtain ⟨U, V, hU, ha, hb, rfl⟩ : ∃ (U : Set X) (V : Set (ConnectedComponents X)),
      IsClopen U ∧ connectedComponent a ∩ U = ∅ ∧ connectedComponent b ⊆ U ∧ (↑) ⁻¹' V = U := by
    have h :=
      (isClosed_connectedComponent (α := X)).isCompact.elim_finite_subfamily_closed
        _ (fun s : { s : Set X // IsClopen s ∧ b ∈ s } => s.2.1.1) h
    obtain ⟨fin_a, ha⟩ := h
    -- This clopen and its complement will separate the connected components of `a` and `b`
    set U : Set X := ⋂ (i : { s // IsClopen s ∧ b ∈ s }) (_ : i ∈ fin_a), i
    have hU : IsClopen U := isClopen_biInter_finset fun i _ => i.2.1
    exact ⟨U, (↑) '' U, hU, ha, subset_iInter₂ fun s _ => s.2.1.connectedComponent_subset s.2.2,
      (connectedComponents_preimage_image U).symm ▸ hU.biUnion_connectedComponent_eq⟩
  rw [ConnectedComponents.isQuotientMap_coe.isClopen_preimage] at hU
  refine ⟨Vᶜ, V, hU.compl.isOpen, hU.isOpen, ?_, hb mem_connectedComponent, disjoint_compl_left⟩
  exact fun h => flip Set.Nonempty.ne_empty ha ⟨a, mem_connectedComponent, h⟩
