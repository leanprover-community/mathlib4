/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Data.Rel
import Mathlib.Order.Filter.SmallSets
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.ContinuousOn

/-!
# Basic results on uniform spaces

Uniform spaces are a generalization of metric spaces and topological groups.

## Main definitions

In this file we define a complete lattice structure on the type `UniformSpace X`
of uniform structures on `X`, as well as the pullback (`UniformSpace.comap`) of uniform structures
coming from the pullback of filters.
Like distance functions, uniform structures cannot be pushed forward in general.

## Notation

Localized in `Uniformity`, we have the notation `𝓤 X` for the uniformity on a uniform space `X`,
and `○` for composition of relations, seen as terms with type `Set (X × X)`.

## References

The formalization uses the books:

* [N. Bourbaki, *General Topology*][bourbaki1966]
* [I. M. James, *Topologies and Uniformities*][james1999]

But it makes a more systematic use of the filter library.
-/

open Set Filter Topology
open scoped SetRel Uniformity

universe u v ua ub uc ud

/-!
### Relations, seen as `SetRel α α`
-/

variable {α : Type ua} {β : Type ub} {γ : Type uc} {δ : Type ud} {ι : Sort*}

open scoped SetRel in
lemma IsOpen.relComp [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {s : SetRel α β} {t : SetRel β γ} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ○ t) := by
  conv =>
    arg 1; equals ⋃ b, (fun p => (p.1, b)) ⁻¹' s ∩ (fun p => (b, p.2)) ⁻¹' t => ext ⟨_, _⟩; simp
  exact isOpen_iUnion fun a ↦ hs.preimage (by fun_prop) |>.inter <| ht.preimage (by fun_prop)

lemma IsOpen.relInv [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) : IsOpen s.inv :=
  hs.preimage continuous_swap

lemma IsOpen.relImage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set α} : IsOpen (s.image t) := by
  simp_rw [SetRel.image, ← exists_prop, Set.setOf_exists]
  exact isOpen_biUnion fun _ _ => hs.preimage <| .prodMk_right _

lemma IsOpen.relPreimage [TopologicalSpace α] [TopologicalSpace β]
    {s : SetRel α β} (hs : IsOpen s) {t : Set β} : IsOpen (s.preimage t) :=
  hs.relInv.relImage

section UniformSpace

variable [UniformSpace α]

/-- If `s ∈ 𝓤 α`, then for any natural `n`, for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ○ ... ○ t ⊆ s` (`n` compositions). -/
theorem eventually_uniformity_iterate_comp_subset {s : SetRel α α} (hs : s ∈ 𝓤 α) (n : ℕ) :
    ∀ᶠ t in (𝓤 α).smallSets, (t ○ ·)^[n] t ⊆ s := by
  suffices ∀ᶠ t in (𝓤 α).smallSets, t ⊆ s ∧ (t ○ ·)^[n] t ⊆ s from (eventually_and.1 this).2
  induction n generalizing s with
  | zero => simpa
  | succ _ ihn =>
    rcases comp_mem_uniformity_sets hs with ⟨t, htU, hts⟩
    refine (ihn htU).mono fun U hU => ?_
    rw [Function.iterate_succ_apply']
    have : SetRel.IsRefl t := SetRel.id_subset_iff.1 <| refl_le_uniformity htU
    exact ⟨hU.1.trans <| SetRel.left_subset_comp.trans hts,
     (SetRel.comp_subset_comp hU.1 hU.2).trans hts⟩

/-- If `s ∈ 𝓤 α`, then for a subset `t` of a sufficiently small set in `𝓤 α`,
we have `t ○ t ⊆ s`. -/
theorem eventually_uniformity_comp_subset {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∀ᶠ t in (𝓤 α).smallSets, t ○ t ⊆ s :=
  eventually_uniformity_iterate_comp_subset hs 1

/-!
### Balls in uniform spaces
-/

namespace UniformSpace

open UniformSpace (ball)

lemma isOpen_ball (x : α) {V : SetRel α α} (hV : IsOpen V) : IsOpen (ball x V) :=
  hV.preimage <| .prodMk_right _

lemma isClosed_ball (x : α) {V : SetRel α α} (hV : IsClosed V) : IsClosed (ball x V) :=
  hV.preimage <| .prodMk_right _

/-!
### Neighborhoods in uniform spaces
-/

theorem hasBasis_nhds_prod (x y : α) :
    HasBasis (𝓝 (x, y)) (fun s => s ∈ 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s ×ˢ ball y s := by
  rw [nhds_prod_eq]
  apply (hasBasis_nhds x).prod_same_index (hasBasis_nhds y)
  rintro U V ⟨U_in, U_symm⟩ ⟨V_in, V_symm⟩
  exact ⟨U ∩ V, ⟨(𝓤 α).inter_sets U_in V_in, inferInstance⟩, ball_inter_left x U V,
    ball_inter_right y U V⟩

end UniformSpace

open UniformSpace

theorem nhds_eq_uniformity_prod {a b : α} :
    𝓝 (a, b) =
      (𝓤 α).lift' fun s : SetRel α α => { y : α | (y, a) ∈ s } ×ˢ { y : α | (b, y) ∈ s } := by
  rw [nhds_prod_eq, nhds_nhds_eq_uniformity_uniformity_prod, lift_lift'_same_eq_lift']
  · exact fun s => monotone_const.set_prod monotone_preimage
  · refine fun t => Monotone.set_prod ?_ monotone_const
    exact monotone_preimage (f := fun y => (y, a))

theorem nhdset_of_mem_uniformity {d : SetRel α α} (s : SetRel α α) (hd : d ∈ 𝓤 α) :
    ∃ t : SetRel α α, IsOpen t ∧ s ⊆ t ∧
      t ⊆ { p | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d } := by
  let cl_d := { p : α × α | ∃ x y, (p.1, x) ∈ d ∧ (x, y) ∈ s ∧ (y, p.2) ∈ d }
  have : ∀ p ∈ s, ∃ t, t ⊆ cl_d ∧ IsOpen t ∧ p ∈ t := fun ⟨x, y⟩ hp =>
    mem_nhds_iff.mp <|
      show cl_d ∈ 𝓝 (x, y) by
        rw [nhds_eq_uniformity_prod, mem_lift'_sets]
        · exact ⟨d, hd, fun ⟨a, b⟩ ⟨ha, hb⟩ => ⟨x, y, ha, hp, hb⟩⟩
        · exact fun _ _ h _ h' => ⟨h h'.1, h h'.2⟩
  choose t ht using this
  exact ⟨(⋃ p : α × α, ⋃ h : p ∈ s, t p h : SetRel α α),
    isOpen_iUnion fun p : α × α => isOpen_iUnion fun hp => (ht p hp).right.left,
    fun ⟨a, b⟩ hp => by
      simp only [mem_iUnion, Prod.exists]; exact ⟨a, b, hp, (ht (a, b) hp).right.right⟩,
    iUnion_subset fun p => iUnion_subset fun hp => (ht p hp).left⟩

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhds_le_uniformity (x : α) : 𝓝 (x, x) ≤ 𝓤 α := by
  intro V V_in
  rcases comp_symm_mem_uniformity_sets V_in with ⟨w, w_in, w_symm, w_sub⟩
  have : ball x w ×ˢ ball x w ∈ 𝓝 (x, x) := by
    rw [nhds_prod_eq]
    exact prod_mem_prod (ball_mem_nhds x w_in) (ball_mem_nhds x w_in)
  apply mem_of_superset this
  rintro ⟨u, v⟩ ⟨u_in, v_in⟩
  exact w_sub (mem_comp_of_mem_ball u_in v_in)

/-- Entourages are neighborhoods of the diagonal. -/
theorem iSup_nhds_le_uniformity : ⨆ x : α, 𝓝 (x, x) ≤ 𝓤 α :=
  iSup_le nhds_le_uniformity

/-- Entourages are neighborhoods of the diagonal. -/
theorem nhdsSet_diagonal_le_uniformity : 𝓝ˢ (diagonal α) ≤ 𝓤 α :=
  (nhdsSet_diagonal α).trans_le iSup_nhds_le_uniformity

section

variable (α)

theorem UniformSpace.has_seq_basis [IsCountablyGenerated <| 𝓤 α] :
    ∃ V : ℕ → SetRel α α, HasAntitoneBasis (𝓤 α) V ∧ ∀ n, SetRel.IsSymm (V n) :=
  let ⟨U, hsym, hbasis⟩ := (@UniformSpace.hasBasis_symmetric α _).exists_antitone_subbasis
  ⟨U, hbasis, fun n => (hsym n).2⟩

end

/-!
### Closure and interior in uniform spaces
-/

theorem closure_eq_uniformity (s : Set <| α × α) :
    closure s = ⋂ V ∈ {V | V ∈ 𝓤 α ∧ SetRel.IsSymm V}, V ○ s ○ V := by
  ext ⟨x, y⟩
  simp +contextual only
    [mem_closure_iff_nhds_basis (UniformSpace.hasBasis_nhds_prod x y), mem_iInter, mem_setOf_eq,
      and_imp, mem_comp_comp, ← mem_inter_iff, inter_comm, Set.Nonempty]

theorem uniformity_hasBasis_closed :
    HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsClosed V) id := by
  refine Filter.hasBasis_self.2 fun t h => ?_
  rcases comp_comp_symm_mem_uniformity_sets h with ⟨w, w_in, w_symm, r⟩
  refine ⟨closure w, mem_of_superset w_in subset_closure, isClosed_closure, ?_⟩
  refine Subset.trans ?_ r
  rw [closure_eq_uniformity]
  apply iInter_subset_of_subset
  apply iInter_subset
  exact ⟨w_in, w_symm⟩

theorem uniformity_eq_uniformity_closure : 𝓤 α = (𝓤 α).lift' closure :=
  Eq.symm <| uniformity_hasBasis_closed.lift'_closure_eq_self fun _ => And.right

theorem Filter.HasBasis.uniformity_closure {p : ι → Prop} {U : ι → SetRel α α}
    (h : (𝓤 α).HasBasis p U) : (𝓤 α).HasBasis p fun i => closure (U i) :=
  (@uniformity_eq_uniformity_closure α _).symm ▸ h.lift'_closure

/-- Closed entourages form a basis of the uniformity filter. -/
theorem uniformity_hasBasis_closure : HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α) closure :=
  (𝓤 α).basis_sets.uniformity_closure

theorem closure_eq_inter_uniformity {t : SetRel α α} : closure t = ⋂ d ∈ 𝓤 α, d ○ (t ○ d) :=
  calc
    closure t = ⋂ (V) (_ : V ∈ 𝓤 α ∧ SetRel.IsSymm V), V ○ t ○ V := closure_eq_uniformity t
    _ = ⋂ V ∈ 𝓤 α, V ○ t ○ V :=
      Eq.symm <|
        UniformSpace.hasBasis_symmetric.biInter_mem fun _ _ hV => by dsimp at *; gcongr
    _ = ⋂ V ∈ 𝓤 α, V ○ (t ○ V) := by simp [SetRel.comp_assoc]

theorem uniformity_eq_uniformity_interior : 𝓤 α = (𝓤 α).lift' interior :=
  le_antisymm
    (le_iInf₂ fun d hd => by
      let ⟨s, hs, hs_comp⟩ := comp3_mem_uniformity hd
      let ⟨t, ht, hst, ht_comp⟩ := nhdset_of_mem_uniformity s hs
      have : s ⊆ interior d :=
        calc
          s ⊆ t := hst
          _ ⊆ interior d :=
            ht.subset_interior_iff.mpr fun x (hx : x ∈ t) =>
              let ⟨x, y, h₁, h₂, h₃⟩ := ht_comp hx
              hs_comp ⟨x, h₁, y, h₂, h₃⟩
      have : interior d ∈ 𝓤 α := by filter_upwards [hs] using this
      simp [this])
    fun _ hs => ((𝓤 α).lift' interior).sets_of_superset (mem_lift' hs) interior_subset

theorem interior_mem_uniformity {s : SetRel α α} (hs : s ∈ 𝓤 α) : interior s ∈ 𝓤 α := by
  rw [uniformity_eq_uniformity_interior]; exact mem_lift' hs

theorem mem_uniformity_isClosed {s : SetRel α α} (h : s ∈ 𝓤 α) : ∃ t ∈ 𝓤 α, IsClosed t ∧ t ⊆ s :=
  let ⟨t, ⟨ht_mem, htc⟩, hts⟩ := uniformity_hasBasis_closed.mem_iff.1 h
  ⟨t, ht_mem, htc, hts⟩

theorem isOpen_iff_isOpen_ball_subset {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∃ V ∈ 𝓤 α, IsOpen V ∧ ball x V ⊆ s := by
  rw [isOpen_iff_ball_subset]
  constructor <;> intro h x hx
  · obtain ⟨V, hV, hV'⟩ := h x hx
    exact
      ⟨interior V, interior_mem_uniformity hV, isOpen_interior,
        (ball_mono interior_subset x).trans hV'⟩
  · obtain ⟨V, hV, -, hV'⟩ := h x hx
    exact ⟨V, hV, hV'⟩

/-- The uniform neighborhoods of all points of a dense set cover the whole space. -/
theorem Dense.biUnion_uniformity_ball {s : Set α} {U : SetRel α α} (hs : Dense s) (hU : U ∈ 𝓤 α) :
    ⋃ x ∈ s, ball x U = univ := by
  refine iUnion₂_eq_univ_iff.2 fun y => ?_
  rcases hs.inter_nhds_nonempty (mem_nhds_right y hU) with ⟨x, hxs, hxy : (x, y) ∈ U⟩
  exact ⟨x, hxs, hxy⟩

/-- The uniform neighborhoods of all points of a dense indexed collection cover the whole space. -/
lemma DenseRange.iUnion_uniformity_ball {ι : Type*} {xs : ι → α}
    (xs_dense : DenseRange xs) {U : SetRel α α} (hU : U ∈ uniformity α) :
    ⋃ i, UniformSpace.ball (xs i) U = univ := by
  rw [← biUnion_range (f := xs) (g := fun x ↦ UniformSpace.ball x U)]
  exact Dense.biUnion_uniformity_ball xs_dense hU

/-!
### Uniformity bases
-/

/-- Open elements of `𝓤 α` form a basis of `𝓤 α`. -/
theorem uniformity_hasBasis_open : HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsOpen V) id :=
  hasBasis_self.2 fun s hs =>
    ⟨interior s, interior_mem_uniformity hs, isOpen_interior, interior_subset⟩

theorem Filter.HasBasis.mem_uniformity_iff {p : β → Prop} {s : β → SetRel α α}
    (h : (𝓤 α).HasBasis p s) {t : SetRel α α} :
    t ∈ 𝓤 α ↔ ∃ i, p i ∧ ∀ a b, (a, b) ∈ s i → (a, b) ∈ t :=
  h.mem_iff.trans <| by simp only [Prod.forall, subset_def]

/-- Open elements `s : SetRel α α` of `𝓤 α` such that `(x, y) ∈ s ↔ (y, x) ∈ s` form a basis
of `𝓤 α`. -/
theorem uniformity_hasBasis_open_symmetric :
    HasBasis (𝓤 α) (fun V : SetRel α α => V ∈ 𝓤 α ∧ IsOpen V ∧ SetRel.IsSymm V) id := by
  simp only [← and_assoc]
  refine uniformity_hasBasis_open.restrict fun s hs => ⟨SetRel.symmetrize s, ?_⟩
  exact
    ⟨⟨symmetrize_mem_uniformity hs.1, IsOpen.inter hs.2 (hs.2.preimage continuous_swap)⟩,
      inferInstance, SetRel.symmetrize_subset_self⟩

theorem comp_open_symm_mem_uniformity_sets {s : SetRel α α} (hs : s ∈ 𝓤 α) :
    ∃ t ∈ 𝓤 α, IsOpen t ∧ SetRel.IsSymm t ∧ t ○ t ⊆ s := by
  obtain ⟨t, ht₁, ht₂⟩ := comp_mem_uniformity_sets hs
  obtain ⟨u, ⟨hu₁, hu₂, hu₃⟩, hu₄ : u ⊆ t⟩ := uniformity_hasBasis_open_symmetric.mem_iff.mp ht₁
  exact ⟨u, hu₁, hu₂, hu₃, (SetRel.comp_subset_comp hu₄ hu₄).trans ht₂⟩

end UniformSpace

open uniformity

section Constructions

instance : PartialOrder (UniformSpace α) :=
  PartialOrder.lift (fun u => 𝓤[u]) fun _ _ => UniformSpace.ext

protected theorem UniformSpace.le_def {u₁ u₂ : UniformSpace α} : u₁ ≤ u₂ ↔ 𝓤[u₁] ≤ 𝓤[u₂] := Iff.rfl

instance : InfSet (UniformSpace α) :=
  ⟨fun s =>
    UniformSpace.ofCore
      { uniformity := ⨅ u ∈ s, 𝓤[u]
        refl := le_iInf fun u => le_iInf fun _ => u.toCore.refl
        symm := le_iInf₂ fun u hu =>
          le_trans (map_mono <| iInf_le_of_le _ <| iInf_le _ hu) u.symm
        comp := le_iInf₂ fun u hu =>
          le_trans (lift'_mono (iInf_le_of_le _ <| iInf_le _ hu) <| le_rfl) u.comp }⟩

protected theorem UniformSpace.sInf_le {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : t ∈ tt) : sInf tt ≤ t :=
  show ⨅ u ∈ tt, 𝓤[u] ≤ 𝓤[t] from iInf₂_le t h

protected theorem UniformSpace.le_sInf {tt : Set (UniformSpace α)} {t : UniformSpace α}
    (h : ∀ t' ∈ tt, t ≤ t') : t ≤ sInf tt :=
  show 𝓤[t] ≤ ⨅ u ∈ tt, 𝓤[u] from le_iInf₂ h

instance : Top (UniformSpace α) :=
  ⟨@UniformSpace.mk α ⊤ ⊤ le_top le_top fun x ↦ by simp only [nhds_top, comap_top]⟩

instance : Bot (UniformSpace α) :=
  ⟨{  toTopologicalSpace := ⊥
      uniformity := 𝓟 SetRel.id
      symm := by simp [Tendsto, SetRel.id]
      comp := lift'_le (mem_principal_self _) <| principal_mono.2 (SetRel.id_comp _).subset
      nhds_eq_comap_uniformity := fun s => by
        let _ : TopologicalSpace α := ⊥; have := discreteTopology_bot α
        simp [SetRel.id] }⟩

instance : Min (UniformSpace α) :=
  ⟨fun u₁ u₂ =>
    { uniformity := 𝓤[u₁] ⊓ 𝓤[u₂]
      symm := u₁.symm.inf u₂.symm
      comp := (lift'_inf_le _ _ _).trans <| inf_le_inf u₁.comp u₂.comp
      toTopologicalSpace := u₁.toTopologicalSpace ⊓ u₂.toTopologicalSpace
      nhds_eq_comap_uniformity := fun _ ↦ by
        rw [@nhds_inf _ u₁.toTopologicalSpace _, @nhds_eq_comap_uniformity _ u₁,
          @nhds_eq_comap_uniformity _ u₂, comap_inf] }⟩

instance : CompleteLattice (UniformSpace α) :=
  { inferInstanceAs (PartialOrder (UniformSpace α)) with
    sup := fun a b => sInf { x | a ≤ x ∧ b ≤ x }
    le_sup_left := fun _ _ => UniformSpace.le_sInf fun _ ⟨h, _⟩ => h
    le_sup_right := fun _ _ => UniformSpace.le_sInf fun _ ⟨_, h⟩ => h
    sup_le := fun _ _ _ h₁ h₂ => UniformSpace.sInf_le ⟨h₁, h₂⟩
    inf := (· ⊓ ·)
    le_inf := fun a _ _ h₁ h₂ => show a.uniformity ≤ _ from le_inf h₁ h₂
    inf_le_left := fun a _ => show _ ≤ a.uniformity from inf_le_left
    inf_le_right := fun _ b => show _ ≤ b.uniformity from inf_le_right
    top := ⊤
    le_top := fun a => show a.uniformity ≤ ⊤ from le_top
    bot := ⊥
    bot_le := fun u => u.toCore.refl
    sSup := fun tt => sInf { t | ∀ t' ∈ tt, t' ≤ t }
    le_sSup := fun _ _ h => UniformSpace.le_sInf fun _ h' => h' _ h
    sSup_le := fun _ _ h => UniformSpace.sInf_le h
    sInf := sInf
    le_sInf := fun _ _ hs => UniformSpace.le_sInf hs
    sInf_le := fun _ _ ha => UniformSpace.sInf_le ha }

theorem iInf_uniformity {ι : Sort*} {u : ι → UniformSpace α} : 𝓤[iInf u] = ⨅ i, 𝓤[u i] :=
  iInf_range

theorem inf_uniformity {u v : UniformSpace α} : 𝓤[u ⊓ v] = 𝓤[u] ⊓ 𝓤[v] := rfl

lemma bot_uniformity : 𝓤[(⊥ : UniformSpace α)] = 𝓟 SetRel.id := rfl

lemma top_uniformity : 𝓤[(⊤ : UniformSpace α)] = ⊤ := rfl

instance inhabitedUniformSpace : Inhabited (UniformSpace α) :=
  ⟨⊥⟩

instance inhabitedUniformSpaceCore : Inhabited (UniformSpace.Core α) :=
  ⟨@UniformSpace.toCore _ default⟩

instance [Subsingleton α] : Unique (UniformSpace α) where
  uniq u := bot_unique <| le_principal_iff.2 <| by
    rw [SetRel.id, ← diagonal, diagonal_eq_univ]; exact univ_mem

/-- Given `f : α → β` and a uniformity `u` on `β`, the inverse image of `u` under `f`
  is the inverse image in the filter sense of the induced function `α × α → β × β`.
  See note [reducible non-instances]. -/
abbrev UniformSpace.comap (f : α → β) (u : UniformSpace β) : UniformSpace α where
  uniformity := 𝓤[u].comap fun p : α × α => (f p.1, f p.2)
  symm := by
    simp only [tendsto_comap_iff]
    exact tendsto_swap_uniformity.comp tendsto_comap
  comp := le_trans
    (by
      rw [comap_lift'_eq, comap_lift'_eq2]
      · exact lift'_mono' fun s _ ⟨a₁, a₂⟩ ⟨x, h₁, h₂⟩ => ⟨f x, h₁, h₂⟩
      · exact monotone_id.relComp monotone_id)
    (comap_mono u.comp)
  toTopologicalSpace := u.toTopologicalSpace.induced f
  nhds_eq_comap_uniformity x := by
    simp only [nhds_induced, nhds_eq_comap_uniformity, comap_comap, Function.comp_def]

theorem uniformity_comap {_ : UniformSpace β} (f : α → β) :
    𝓤[UniformSpace.comap f ‹_›] = comap (Prod.map f f) (𝓤 β) :=
  rfl

lemma ball_preimage {f : α → β} {U : SetRel β β} {x : α} :
    UniformSpace.ball x (Prod.map f f ⁻¹' U) = f ⁻¹' UniformSpace.ball (f x) U := by
  ext : 1
  simp only [UniformSpace.ball, mem_preimage, Prod.map_apply]

@[simp]
theorem uniformSpace_comap_id {α : Type*} : UniformSpace.comap (id : α → α) = id := by
  ext : 2
  rw [uniformity_comap, Prod.map_id, comap_id]

theorem UniformSpace.comap_comap {α β γ} {uγ : UniformSpace γ} {f : α → β} {g : β → γ} :
    UniformSpace.comap (g ∘ f) uγ = UniformSpace.comap f (UniformSpace.comap g uγ) := by
  ext1
  simp only [uniformity_comap, Filter.comap_comap, Prod.map_comp_map]

theorem UniformSpace.comap_inf {α γ} {u₁ u₂ : UniformSpace γ} {f : α → γ} :
    (u₁ ⊓ u₂).comap f = u₁.comap f ⊓ u₂.comap f :=
  UniformSpace.ext Filter.comap_inf

theorem UniformSpace.comap_iInf {ι α γ} {u : ι → UniformSpace γ} {f : α → γ} :
    (⨅ i, u i).comap f = ⨅ i, (u i).comap f := by
  ext : 1
  simp [uniformity_comap, iInf_uniformity]

theorem UniformSpace.comap_mono {α γ} {f : α → γ} :
    Monotone fun u : UniformSpace γ => u.comap f := fun _ _ hu =>
  Filter.comap_mono hu

theorem uniformContinuous_iff {α β} {uα : UniformSpace α} {uβ : UniformSpace β} {f : α → β} :
    UniformContinuous f ↔ uα ≤ uβ.comap f :=
  Filter.map_le_iff_le_comap

theorem le_iff_uniformContinuous_id {u v : UniformSpace α} :
    u ≤ v ↔ @UniformContinuous _ _ u v id := by
  rw [uniformContinuous_iff, uniformSpace_comap_id, id]

theorem uniformContinuous_comap {f : α → β} [u : UniformSpace β] :
    @UniformContinuous α β (UniformSpace.comap f u) u f :=
  tendsto_comap

theorem uniformContinuous_comap' {f : γ → β} {g : α → γ} [v : UniformSpace β] [u : UniformSpace α]
    (h : UniformContinuous (f ∘ g)) : @UniformContinuous α γ u (UniformSpace.comap f v) g :=
  tendsto_comap_iff.2 h

namespace UniformSpace

theorem to_nhds_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) (a : α) :
    @nhds _ (@UniformSpace.toTopologicalSpace _ u₁) a ≤
      @nhds _ (@UniformSpace.toTopologicalSpace _ u₂) a := by
  rw [@nhds_eq_uniformity α u₁ a, @nhds_eq_uniformity α u₂ a]; exact lift'_mono h le_rfl

theorem toTopologicalSpace_mono {u₁ u₂ : UniformSpace α} (h : u₁ ≤ u₂) :
    @UniformSpace.toTopologicalSpace _ u₁ ≤ @UniformSpace.toTopologicalSpace _ u₂ :=
  le_of_nhds_le_nhds <| to_nhds_mono h

theorem toTopologicalSpace_comap {f : α → β} {u : UniformSpace β} :
    @UniformSpace.toTopologicalSpace _ (UniformSpace.comap f u) =
      TopologicalSpace.induced f (@UniformSpace.toTopologicalSpace β u) :=
  rfl

lemma uniformSpace_eq_bot {u : UniformSpace α} : u = ⊥ ↔ SetRel.id ∈ 𝓤[u] :=
  le_bot_iff.symm.trans le_principal_iff

protected lemma _root_.Filter.HasBasis.uniformSpace_eq_bot {ι p} {s : ι → SetRel α α}
    {u : UniformSpace α} (h : 𝓤[u].HasBasis p s) :
    u = ⊥ ↔ ∃ i, p i ∧ Pairwise fun x y : α ↦ (x, y) ∉ s i := by
  simp [uniformSpace_eq_bot, h.mem_iff, subset_def, Pairwise, not_imp_not]

theorem toTopologicalSpace_bot : @UniformSpace.toTopologicalSpace α ⊥ = ⊥ := rfl

theorem toTopologicalSpace_top : @UniformSpace.toTopologicalSpace α ⊤ = ⊤ := rfl

theorem toTopologicalSpace_iInf {ι : Sort*} {u : ι → UniformSpace α} :
    (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopologicalSpace :=
  TopologicalSpace.ext_nhds fun a ↦ by simp only [@nhds_eq_comap_uniformity _ (iInf u), nhds_iInf,
    iInf_uniformity, @nhds_eq_comap_uniformity _ (u _), Filter.comap_iInf]

theorem toTopologicalSpace_sInf {s : Set (UniformSpace α)} :
    (sInf s).toTopologicalSpace = ⨅ i ∈ s, @UniformSpace.toTopologicalSpace α i := by
  rw [sInf_eq_iInf]
  simp only [← toTopologicalSpace_iInf]

theorem toTopologicalSpace_inf {u v : UniformSpace α} :
    (u ⊓ v).toTopologicalSpace = u.toTopologicalSpace ⊓ v.toTopologicalSpace :=
  rfl

end UniformSpace

section

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] {f : α → β} {s t : Set α}

theorem UniformContinuous.continuous (hf : UniformContinuous f) : Continuous f :=
  continuous_iff_le_induced.mpr <| UniformSpace.toTopologicalSpace_mono <|
    uniformContinuous_iff.1 hf

lemma UniformContinuous.uniformContinuousOn (hf : UniformContinuous f) :
    UniformContinuousOn f s :=
  tendsto_inf_left hf

lemma UniformContinuousOn.mono (hf : UniformContinuousOn f s) (ht : t ⊆ s) :
    UniformContinuousOn f t :=
  Tendsto.mono_left hf (inf_le_inf le_rfl (by simp [ht]))

lemma UniformContinuousOn.congr {f g : α → β} {s : Set α}
    (hf : UniformContinuousOn f s) (h : EqOn f g s) :
    UniformContinuousOn g s := by
  apply hf.congr'
  apply EventuallyEq.filter_mono _ inf_le_right
  filter_upwards [mem_principal_self _] with ⟨a, b⟩ ⟨ha, hb⟩ using by simp [h ha, h hb]

lemma UniformContinuousOn.comp {g : β → γ} {t : Set β} (hg : UniformContinuousOn g t)
    (hf : UniformContinuousOn f s) (hst : MapsTo f s t) : UniformContinuousOn (g ∘ f) s := by
  change Tendsto ((fun x ↦ (g x.1, g x.2)) ∘ (fun x ↦ (f x.1, f x.2))) (𝓤 α ⊓ 𝓟 (s ×ˢ s)) (𝓤 γ)
  apply Tendsto.comp hg
  refine tendsto_inf.2 ⟨hf, tendsto_inf_right ?_⟩
  simp only [tendsto_principal, mem_prod, eventually_principal, and_imp, Prod.forall]
  exact fun a b ha hb ↦ ⟨hst ha, hst hb⟩

lemma UniformContinuous.comp_uniformContinuousOn {g : β → γ}
    (hg : UniformContinuous g) (hf : UniformContinuousOn f s) : UniformContinuousOn (g ∘ f) s :=
  (hg.uniformContinuousOn (s := univ)).comp hf (mapsTo_univ _ _)

end

/-- Uniform space structure on `ULift α`. -/
instance ULift.uniformSpace [UniformSpace α] : UniformSpace (ULift α) :=
  UniformSpace.comap ULift.down ‹_›

/-- Uniform space structure on `αᵒᵈ`. -/
instance OrderDual.instUniformSpace [UniformSpace α] : UniformSpace (αᵒᵈ) :=
  ‹UniformSpace α›

section UniformContinuousInfi

-- TODO: add an `iff` lemma?
theorem UniformContinuous.inf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ u₃ : UniformSpace β}
    (h₁ : UniformContinuous[u₁, u₂] f) (h₂ : UniformContinuous[u₁, u₃] f) :
    UniformContinuous[u₁, u₂ ⊓ u₃] f :=
  tendsto_inf.mpr ⟨h₁, h₂⟩

theorem UniformContinuous.inf_dom_left {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₁, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_left hf

theorem UniformContinuous.inf_dom_right {f : α → β} {u₁ u₂ : UniformSpace α} {u₃ : UniformSpace β}
    (hf : UniformContinuous[u₂, u₃] f) : UniformContinuous[u₁ ⊓ u₂, u₃] f :=
  tendsto_inf_right hf

theorem uniformContinuous_sInf_dom {f : α → β} {u₁ : Set (UniformSpace α)} {u₂ : UniformSpace β}
    {u : UniformSpace α} (h₁ : u ∈ u₁) (hf : UniformContinuous[u, u₂] f) :
    UniformContinuous[sInf u₁, u₂] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity]
  exact tendsto_iInf' ⟨u, h₁⟩ hf

theorem uniformContinuous_sInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : Set (UniformSpace β)} :
    UniformContinuous[u₁, sInf u₂] f ↔ ∀ u ∈ u₂, UniformContinuous[u₁, u] f := by
  delta UniformContinuous
  rw [sInf_eq_iInf', iInf_uniformity, tendsto_iInf, SetCoe.forall]

theorem uniformContinuous_iInf_dom {f : α → β} {u₁ : ι → UniformSpace α} {u₂ : UniformSpace β}
    {i : ι} (hf : UniformContinuous[u₁ i, u₂] f) : UniformContinuous[iInf u₁, u₂] f := by
  delta UniformContinuous
  rw [iInf_uniformity]
  exact tendsto_iInf' i hf

theorem uniformContinuous_iInf_rng {f : α → β} {u₁ : UniformSpace α} {u₂ : ι → UniformSpace β} :
    UniformContinuous[u₁, iInf u₂] f ↔ ∀ i, UniformContinuous[u₁, u₂ i] f := by
  delta UniformContinuous
  rw [iInf_uniformity, tendsto_iInf]

end UniformContinuousInfi

/-- A uniform space with the discrete uniformity has the discrete topology. -/
theorem discreteTopology_of_discrete_uniformity [hα : UniformSpace α]
    (h : uniformity α = 𝓟 SetRel.id) : DiscreteTopology α :=
  ⟨(UniformSpace.ext h.symm : ⊥ = hα) ▸ rfl⟩

instance : UniformSpace Empty := ⊥
instance : UniformSpace PUnit := ⊥
instance : UniformSpace Bool := ⊥
instance : UniformSpace ℕ := ⊥
instance : UniformSpace ℤ := ⊥

section

variable [UniformSpace α]

open Additive Multiplicative

instance : UniformSpace (Additive α) := ‹UniformSpace α›
instance : UniformSpace (Multiplicative α) := ‹UniformSpace α›

theorem uniformContinuous_ofMul : UniformContinuous (ofMul : α → Additive α) :=
  uniformContinuous_id

theorem uniformContinuous_toMul : UniformContinuous (toMul : Additive α → α) :=
  uniformContinuous_id

theorem uniformContinuous_ofAdd : UniformContinuous (ofAdd : α → Multiplicative α) :=
  uniformContinuous_id

theorem uniformContinuous_toAdd : UniformContinuous (toAdd : Multiplicative α → α) :=
  uniformContinuous_id

theorem uniformity_additive : 𝓤 (Additive α) = (𝓤 α).map (Prod.map ofMul ofMul) := rfl

theorem uniformity_multiplicative : 𝓤 (Multiplicative α) = (𝓤 α).map (Prod.map ofAdd ofAdd) := rfl

end

instance instUniformSpaceSubtype {p : α → Prop} [t : UniformSpace α] : UniformSpace (Subtype p) :=
  UniformSpace.comap Subtype.val t

theorem uniformity_subtype {p : α → Prop} [UniformSpace α] :
    𝓤 (Subtype p) = comap (fun q : Subtype p × Subtype p => (q.1.1, q.2.1)) (𝓤 α) :=
  rfl

theorem uniformity_setCoe {s : Set α} [UniformSpace α] :
    𝓤 s = comap (Prod.map ((↑) : s → α) ((↑) : s → α)) (𝓤 α) :=
  rfl

theorem map_uniformity_set_coe {s : Set α} [UniformSpace α] :
    map (Prod.map (↑) (↑)) (𝓤 s) = 𝓤 α ⊓ 𝓟 (s ×ˢ s) := by
  rw [uniformity_setCoe, map_comap, range_prodMap, Subtype.range_val]

theorem uniformContinuous_subtype_val {p : α → Prop} [UniformSpace α] :
    UniformContinuous (Subtype.val : { a : α // p a } → α) :=
  uniformContinuous_comap

theorem UniformContinuous.subtype_mk {p : α → Prop} [UniformSpace α] [UniformSpace β] {f : β → α}
    (hf : UniformContinuous f) (h : ∀ x, p (f x)) :
    UniformContinuous (fun x => ⟨f x, h x⟩ : β → Subtype p) :=
  uniformContinuous_comap' hf

theorem UniformContinuous.subtype_map [UniformSpace α] [UniformSpace β] {p : α → Prop}
    {q : β → Prop} {f : α → β} (hf : UniformContinuous f) (h : ∀ x, p x → q (f x)) :
    UniformContinuous (Subtype.map f h) :=
  (hf.comp uniformContinuous_subtype_val).subtype_mk _

theorem uniformContinuousOn_iff_restrict [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α} :
    UniformContinuousOn f s ↔ UniformContinuous (s.restrict f) := by
  delta UniformContinuousOn UniformContinuous
  rw [← map_uniformity_set_coe, tendsto_map'_iff]; rfl

theorem tendsto_of_uniformContinuous_subtype [UniformSpace α] [UniformSpace β] {f : α → β}
    {s : Set α} {a : α} (hf : UniformContinuous fun x : s => f x.val) (ha : s ∈ 𝓝 a) :
    Tendsto f (𝓝 a) (𝓝 (f a)) := by
  rw [(@map_nhds_subtype_coe_eq_nhds α _ s a (mem_of_mem_nhds ha) ha).symm]
  exact tendsto_map' hf.continuous.continuousAt

theorem UniformContinuousOn.continuousOn [UniformSpace α] [UniformSpace β] {f : α → β} {s : Set α}
    (h : UniformContinuousOn f s) : ContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict] at h
  rw [continuousOn_iff_continuous_restrict]
  exact h.continuous

@[to_additive]
instance [UniformSpace α] : UniformSpace αᵐᵒᵖ :=
  UniformSpace.comap MulOpposite.unop ‹_›

@[to_additive]
theorem uniformity_mulOpposite [UniformSpace α] :
    𝓤 αᵐᵒᵖ = comap (fun q : αᵐᵒᵖ × αᵐᵒᵖ => (q.1.unop, q.2.unop)) (𝓤 α) :=
  rfl

@[to_additive (attr := simp)]
theorem comap_uniformity_mulOpposite [UniformSpace α] :
    comap (fun p : α × α => (MulOpposite.op p.1, MulOpposite.op p.2)) (𝓤 αᵐᵒᵖ) = 𝓤 α := by
  simpa [uniformity_mulOpposite, comap_comap, (· ∘ ·)] using comap_id

namespace MulOpposite

@[to_additive]
theorem uniformContinuous_unop [UniformSpace α] : UniformContinuous (unop : αᵐᵒᵖ → α) :=
  uniformContinuous_comap

@[to_additive]
theorem uniformContinuous_op [UniformSpace α] : UniformContinuous (op : α → αᵐᵒᵖ) :=
  uniformContinuous_comap' uniformContinuous_id

end MulOpposite

section Prod

open UniformSpace

/- a similar product space is possible on the function space (uniformity of pointwise convergence),
  but we want to have the uniformity of uniform convergence on function spaces -/
instance instUniformSpaceProd [u₁ : UniformSpace α] [u₂ : UniformSpace β] : UniformSpace (α × β) :=
  u₁.comap Prod.fst ⊓ u₂.comap Prod.snd

-- check the above produces no diamond for `simp` and typeclass search
example [UniformSpace α] [UniformSpace β] :
    (instTopologicalSpaceProd : TopologicalSpace (α × β)) = UniformSpace.toTopologicalSpace := by
  with_reducible_and_instances rfl

theorem uniformity_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      ((𝓤 α).comap fun p : (α × β) × α × β => (p.1.1, p.2.1)) ⊓
        (𝓤 β).comap fun p : (α × β) × α × β => (p.1.2, p.2.2) :=
  rfl

instance [UniformSpace α] [IsCountablyGenerated (𝓤 α)]
    [UniformSpace β] [IsCountablyGenerated (𝓤 β)] : IsCountablyGenerated (𝓤 (α × β)) := by
  rw [uniformity_prod]
  infer_instance

theorem uniformity_prod_eq_comap_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) =
      comap (fun p : (α × β) × α × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  simp_rw [uniformity_prod, prod_eq_inf, Filter.comap_inf, Filter.comap_comap, Function.comp_def]

theorem uniformity_prod_eq_prod [UniformSpace α] [UniformSpace β] :
    𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (𝓤 α ×ˢ 𝓤 β) := by
  rw [map_swap4_eq_comap, uniformity_prod_eq_comap_prod]

theorem mem_uniformity_of_uniformContinuous_invariant [UniformSpace α] [UniformSpace β]
    {s : SetRel β β} {f : α → α → β} (hf : UniformContinuous fun p : α × α => f p.1 p.2)
    (hs : s ∈ 𝓤 β) : ∃ u ∈ 𝓤 α, ∀ a b c, (a, b) ∈ u → (f a c, f b c) ∈ s := by
  rw [UniformContinuous, uniformity_prod_eq_prod, tendsto_map'_iff] at hf
  rcases mem_prod_iff.1 (mem_map.1 <| hf hs) with ⟨u, hu, v, hv, huvt⟩
  exact ⟨u, hu, fun a b c hab => @huvt ((_, _), (_, _)) ⟨hab, refl_mem_uniformity hv⟩⟩

/-- An entourage of the diagonal in `α` and an entourage in `β` yield an entourage in `α × β`
once we permute coordinates. -/
def entourageProd (u : SetRel α α) (v : SetRel β β) : SetRel (α × β) (α × β) :=
  {((a₁, b₁),(a₂, b₂)) | (a₁, a₂) ∈ u ∧ (b₁, b₂) ∈ v}

theorem mem_entourageProd {u : SetRel α α} {v : SetRel β β} {p : (α × β) × α × β} :
    p ∈ entourageProd u v ↔ (p.1.1, p.2.1) ∈ u ∧ (p.1.2, p.2.2) ∈ v := Iff.rfl

theorem entourageProd_mem_uniformity [t₁ : UniformSpace α] [t₂ : UniformSpace β] {u : SetRel α α}
    {v : SetRel β β} (hu : u ∈ 𝓤 α) (hv : v ∈ 𝓤 β) :
    entourageProd u v ∈ 𝓤 (α × β) := by
  rw [uniformity_prod]; exact inter_mem_inf (preimage_mem_comap hu) (preimage_mem_comap hv)

theorem ball_entourageProd (u : SetRel α α) (v : SetRel β β) (x : α × β) :
    ball x (entourageProd u v) = ball x.1 u ×ˢ ball x.2 v := by
  ext p; simp only [ball, entourageProd, Set.mem_setOf_eq, Set.mem_prod, Set.mem_preimage]

instance IsSymm_entourageProd {u : SetRel α α} {v : SetRel β β} [u.IsSymm] [v.IsSymm] :
    (entourageProd u v).IsSymm where
  symm _ _ := .imp u.symm v.symm

theorem Filter.HasBasis.uniformity_prod {ιa ιb : Type*} [UniformSpace α] [UniformSpace β]
    {pa : ιa → Prop} {pb : ιb → Prop} {sa : ιa → SetRel α α} {sb : ιb → SetRel β β}
    (ha : (𝓤 α).HasBasis pa sa) (hb : (𝓤 β).HasBasis pb sb) :
    (𝓤 (α × β)).HasBasis (fun i : ιa × ιb ↦ pa i.1 ∧ pb i.2)
    (fun i ↦ entourageProd (sa i.1) (sb i.2)) :=
  (ha.comap _).inf (hb.comap _)

theorem entourageProd_subset [UniformSpace α] [UniformSpace β]
    {s : Set ((α × β) × α × β)} (h : s ∈ 𝓤 (α × β)) :
    ∃ u ∈ 𝓤 α, ∃ v ∈ 𝓤 β, entourageProd u v ⊆ s := by
  rcases (((𝓤 α).basis_sets.uniformity_prod (𝓤 β).basis_sets).mem_iff' s).1 h with ⟨w, hw⟩
  use w.1, hw.1.1, w.2, hw.1.2, hw.2

theorem tendsto_prod_uniformity_fst [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.1, p.2.1)) (𝓤 (α × β)) (𝓤 α) :=
  le_trans (map_mono inf_le_left) map_comap_le

theorem tendsto_prod_uniformity_snd [UniformSpace α] [UniformSpace β] :
    Tendsto (fun p : (α × β) × α × β => (p.1.2, p.2.2)) (𝓤 (α × β)) (𝓤 β) :=
  le_trans (map_mono inf_le_right) map_comap_le

theorem uniformContinuous_fst [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.1 :=
  tendsto_prod_uniformity_fst

theorem uniformContinuous_snd [UniformSpace α] [UniformSpace β] :
    UniformContinuous fun p : α × β => p.2 :=
  tendsto_prod_uniformity_snd

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ]

theorem UniformContinuous.prodMk {f₁ : α → β} {f₂ : α → γ} (h₁ : UniformContinuous f₁)
    (h₂ : UniformContinuous f₂) : UniformContinuous fun a => (f₁ a, f₂ a) := by
  rw [UniformContinuous, uniformity_prod]
  exact tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

@[deprecated (since := "2025-03-10")]
alias UniformContinuous.prod_mk := UniformContinuous.prodMk

theorem UniformContinuous.prodMk_left {f : α × β → γ} (h : UniformContinuous f) (b) :
    UniformContinuous fun a => f (a, b) :=
  h.comp (uniformContinuous_id.prodMk uniformContinuous_const)

@[deprecated (since := "2025-03-10")]
alias UniformContinuous.prod_mk_left := UniformContinuous.prodMk_left

theorem UniformContinuous.prodMk_right {f : α × β → γ} (h : UniformContinuous f) (a) :
    UniformContinuous fun b => f (a, b) :=
  h.comp (uniformContinuous_const.prodMk uniformContinuous_id)

@[deprecated (since := "2025-03-10")]
alias UniformContinuous.prod_mk_right := UniformContinuous.prodMk_right

theorem UniformContinuous.prodMap [UniformSpace δ] {f : α → γ} {g : β → δ}
    (hf : UniformContinuous f) (hg : UniformContinuous g) : UniformContinuous (Prod.map f g) :=
  (hf.comp uniformContinuous_fst).prodMk (hg.comp uniformContinuous_snd)

lemma uniformContinuous_swap :
    UniformContinuous (Prod.swap : α × β → β × α) :=
  uniformContinuous_snd.prodMk uniformContinuous_fst

theorem toTopologicalSpace_prod {α} {β} [u : UniformSpace α] [v : UniformSpace β] :
    @UniformSpace.toTopologicalSpace (α × β) instUniformSpaceProd =
      @instTopologicalSpaceProd α β u.toTopologicalSpace v.toTopologicalSpace :=
  rfl

/-- A version of `UniformContinuous.inf_dom_left` for binary functions -/
theorem uniformContinuous_inf_dom_left₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua1; haveI := ub1; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_left₂`
  have ha := @UniformContinuous.inf_dom_left _ _ id ua1 ua2 ua1 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_left _ _ id ub1 ub2 ub1 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua1 ub1 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `UniformContinuous.inf_dom_right` for binary functions -/
theorem uniformContinuous_inf_dom_right₂ {α β γ} {f : α → β → γ} {ua1 ua2 : UniformSpace α}
    {ub1 ub2 : UniformSpace β} {uc1 : UniformSpace γ}
    (h : by haveI := ua2; haveI := ub2; exact UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := ua1 ⊓ ua2; haveI := ub1 ⊓ ub2
      exact UniformContinuous fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_inf_dom_right₂`
  have ha := @UniformContinuous.inf_dom_right _ _ id ua1 ua2 ua2 (@uniformContinuous_id _ (id _))
  have hb := @UniformContinuous.inf_dom_right _ _ id ub1 ub2 ub2 (@uniformContinuous_id _ (id _))
  have h_unif_cont_id :=
    @UniformContinuous.prodMap _ _ _ _ (ua1 ⊓ ua2) (ub1 ⊓ ub2) ua2 ub2 _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ h h_unif_cont_id

/-- A version of `uniformContinuous_sInf_dom` for binary functions -/
theorem uniformContinuous_sInf_dom₂ {α β γ} {f : α → β → γ} {uas : Set (UniformSpace α)}
    {ubs : Set (UniformSpace β)} {ua : UniformSpace α} {ub : UniformSpace β} {uc : UniformSpace γ}
    (ha : ua ∈ uas) (hb : ub ∈ ubs) (hf : UniformContinuous fun p : α × β => f p.1 p.2) : by
      haveI := sInf uas; haveI := sInf ubs
      exact @UniformContinuous _ _ _ uc fun p : α × β => f p.1 p.2 := by
  -- proof essentially copied from `continuous_sInf_dom`
  let _ : UniformSpace (α × β) := instUniformSpaceProd
  have ha := uniformContinuous_sInf_dom ha uniformContinuous_id
  have hb := uniformContinuous_sInf_dom hb uniformContinuous_id
  have h_unif_cont_id := @UniformContinuous.prodMap _ _ _ _ (sInf uas) (sInf ubs) ua ub _ _ ha hb
  exact @UniformContinuous.comp _ _ _ (id _) (id _) _ _ _ hf h_unif_cont_id

end Prod

section

open UniformSpace Function

variable {δ' : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]
  [UniformSpace δ']
local notation f " ∘₂ " g => Function.bicompr f g

/-- Uniform continuity for functions of two variables. -/
def UniformContinuous₂ (f : α → β → γ) :=
  UniformContinuous (uncurry f)

theorem uniformContinuous₂_def (f : α → β → γ) :
    UniformContinuous₂ f ↔ UniformContinuous (uncurry f) :=
  Iff.rfl

theorem UniformContinuous₂.uniformContinuous {f : α → β → γ} (h : UniformContinuous₂ f) :
    UniformContinuous (uncurry f) :=
  h

theorem uniformContinuous₂_curry (f : α × β → γ) :
    UniformContinuous₂ (Function.curry f) ↔ UniformContinuous f := by
  rw [UniformContinuous₂, uncurry_curry]

theorem UniformContinuous₂.comp {f : α → β → γ} {g : γ → δ} (hg : UniformContinuous g)
    (hf : UniformContinuous₂ f) : UniformContinuous₂ (g ∘₂ f) :=
  hg.comp hf

theorem UniformContinuous₂.bicompl {f : α → β → γ} {ga : δ → α} {gb : δ' → β}
    (hf : UniformContinuous₂ f) (hga : UniformContinuous ga) (hgb : UniformContinuous gb) :
    UniformContinuous₂ (bicompl f ga gb) :=
  hf.uniformContinuous.comp (hga.prodMap hgb)

end

theorem toTopologicalSpace_subtype [u : UniformSpace α] {p : α → Prop} :
    @UniformSpace.toTopologicalSpace (Subtype p) instUniformSpaceSubtype =
      @instTopologicalSpaceSubtype α p u.toTopologicalSpace :=
  rfl

section Sum

variable [UniformSpace α] [UniformSpace β]

open Sum

-- Obsolete auxiliary definitions and lemmas

/-- Uniformity on a disjoint union. Entourages of the diagonal in the union are obtained
by taking independently an entourage of the diagonal in the first part, and an entourage of
the diagonal in the second part. -/
instance Sum.instUniformSpace : UniformSpace (α ⊕ β) where
  uniformity := map (fun p : α × α => (inl p.1, inl p.2)) (𝓤 α) ⊔
    map (fun p : β × β => (inr p.1, inr p.2)) (𝓤 β)
  symm := fun _ hs ↦ ⟨symm_le_uniformity hs.1, symm_le_uniformity hs.2⟩
  comp := fun s hs ↦ by
    rcases comp_mem_uniformity_sets hs.1 with ⟨tα, htα, Htα⟩
    rcases comp_mem_uniformity_sets hs.2 with ⟨tβ, htβ, Htβ⟩
    filter_upwards [mem_lift' (union_mem_sup (image_mem_map htα) (image_mem_map htβ))]
    rintro ⟨_, _⟩ ⟨z, ⟨⟨a, b⟩, hab, ⟨⟩⟩ | ⟨⟨a, b⟩, hab, ⟨⟩⟩, ⟨⟨_, c⟩, hbc, ⟨⟩⟩ | ⟨⟨_, c⟩, hbc, ⟨⟩⟩⟩
    exacts [@Htα (_, _) ⟨b, hab, hbc⟩, @Htβ (_, _) ⟨b, hab, hbc⟩]
  nhds_eq_comap_uniformity x := by
    ext
    cases x <;> simp [mem_comap', -mem_comap, nhds_inl, nhds_inr, nhds_eq_comap_uniformity,
      Prod.ext_iff]

/-- The union of an entourage of the diagonal in each set of a disjoint union is again an entourage
of the diagonal. -/
theorem union_mem_uniformity_sum {a : SetRel α α} (ha : a ∈ 𝓤 α) {b : SetRel β β} (hb : b ∈ 𝓤 β) :
    Prod.map inl inl '' a ∪ Prod.map inr inr '' b ∈ 𝓤 (α ⊕ β) :=
  union_mem_sup (image_mem_map ha) (image_mem_map hb)

theorem Sum.uniformity : 𝓤 (α ⊕ β) = map (Prod.map inl inl) (𝓤 α) ⊔ map (Prod.map inr inr) (𝓤 β) :=
  rfl

lemma uniformContinuous_inl : UniformContinuous (Sum.inl : α → α ⊕ β) := le_sup_left
lemma uniformContinuous_inr : UniformContinuous (Sum.inr : β → α ⊕ β) := le_sup_right

instance [IsCountablyGenerated (𝓤 α)] [IsCountablyGenerated (𝓤 β)] :
    IsCountablyGenerated (𝓤 (α ⊕ β)) := by
  rw [Sum.uniformity]
  infer_instance

end Sum

end Constructions

/-!
### Expressing continuity properties in uniform spaces

We reformulate the various continuity properties of functions taking values in a uniform space
in terms of the uniformity in the target. Since the same lemmas (essentially with the same names)
also exist for metric spaces and emetric spaces (reformulating things in terms of the distance or
the edistance in the target), we put them in a namespace `Uniform` here.

In the metric and emetric space setting, there are also similar lemmas where one assumes that
both the source and the target are metric spaces, reformulating things in terms of the distance
on both sides. These lemmas are generally written without primes, and the versions where only
the target is a metric space is primed. We follow the same convention here, thus giving lemmas
with primes.
-/


namespace Uniform

variable [UniformSpace α]

theorem tendsto_nhds_right {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity, tendsto_comap_iff]; rfl

theorem tendsto_nhds_left {f : Filter β} {u : β → α} {a : α} :
    Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α) := by
  rw [nhds_eq_comap_uniformity', tendsto_comap_iff]; rfl

theorem continuousAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_right]

theorem continuousAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) := by
  rw [ContinuousAt, tendsto_nhds_left]

theorem continuousAt_iff_prod [TopologicalSpace β] {f : β → α} {b : β} :
    ContinuousAt f b ↔ Tendsto (fun x : β × β => (f x.1, f x.2)) (𝓝 (b, b)) (𝓤 α) :=
  ⟨fun H => le_trans (H.prodMap' H) (nhds_le_uniformity _), fun H =>
    continuousAt_iff'_left.2 <| H.comp <| tendsto_id.prodMk_nhds tendsto_const_nhds⟩

theorem continuousWithinAt_iff'_right [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_right]

theorem continuousWithinAt_iff'_left [TopologicalSpace β] {f : β → α} {b : β} {s : Set β} :
    ContinuousWithinAt f s b ↔ Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  rw [ContinuousWithinAt, tendsto_nhds_left]

theorem continuousOn_iff'_right [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f b, f x)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_right]

theorem continuousOn_iff'_left [TopologicalSpace β] {f : β → α} {s : Set β} :
    ContinuousOn f s ↔ ∀ b ∈ s, Tendsto (fun x => (f x, f b)) (𝓝[s] b) (𝓤 α) := by
  simp [ContinuousOn, continuousWithinAt_iff'_left]

theorem continuous_iff'_right [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f b, f x)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_right

theorem continuous_iff'_left [TopologicalSpace β] {f : β → α} :
    Continuous f ↔ ∀ b, Tendsto (fun x => (f x, f b)) (𝓝 b) (𝓤 α) :=
  continuous_iff_continuousAt.trans <| forall_congr' fun _ => tendsto_nhds_left

/-- Consider two functions `f` and `g` which coincide on a set `s` and are continuous there.
Then there is an open neighborhood of `s` on which `f` and `g` are uniformly close. -/
lemma exists_is_open_mem_uniformity_of_forall_mem_eq
    [TopologicalSpace β] {r : SetRel α α} {s : Set β}
    {f g : β → α} (hf : ∀ x ∈ s, ContinuousAt f x) (hg : ∀ x ∈ s, ContinuousAt g x)
    (hfg : s.EqOn f g) (hr : r ∈ 𝓤 α) :
    ∃ t, IsOpen t ∧ s ⊆ t ∧ ∀ x ∈ t, (f x, g x) ∈ r := by
  have A : ∀ x ∈ s, ∃ t, IsOpen t ∧ x ∈ t ∧ ∀ z ∈ t, (f z, g z) ∈ r := by
    intro x hx
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    have A : {z | (f x, f z) ∈ t} ∈ 𝓝 x := (hf x hx).preimage_mem_nhds (mem_nhds_left (f x) ht)
    have B : {z | (g x, g z) ∈ t} ∈ 𝓝 x := (hg x hx).preimage_mem_nhds (mem_nhds_left (g x) ht)
    rcases _root_.mem_nhds_iff.1 (inter_mem A B) with ⟨u, hu, u_open, xu⟩
    refine ⟨u, u_open, xu, fun y hy ↦ ?_⟩
    have I1 : (f y, f x) ∈ t := SetRel.symm t (hu hy).1
    have I2 : (g x, g y) ∈ t := (hu hy).2
    rw [hfg hx] at I1
    exact htr (SetRel.prodMk_mem_comp I1 I2)
  choose! t t_open xt ht using A
  refine ⟨⋃ x ∈ s, t x, isOpen_biUnion t_open, fun x hx ↦ mem_biUnion hx (xt x hx), ?_⟩
  rintro x hx
  simp only [mem_iUnion, exists_prop] at hx
  rcases hx with ⟨y, ys, hy⟩
  exact ht y ys x hy

end Uniform

theorem Filter.Tendsto.congr_uniformity {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hf : Tendsto f l (𝓝 b)) (hg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto g l (𝓝 b) :=
  Uniform.tendsto_nhds_right.2 <| (Uniform.tendsto_nhds_right.1 hf).uniformity_trans hg

theorem Uniform.tendsto_congr {α β} [UniformSpace β] {f g : α → β} {l : Filter α} {b : β}
    (hfg : Tendsto (fun x => (f x, g x)) l (𝓤 β)) : Tendsto f l (𝓝 b) ↔ Tendsto g l (𝓝 b) :=
  ⟨fun h => h.congr_uniformity hfg, fun h => h.congr_uniformity hfg.uniformity_symm⟩
