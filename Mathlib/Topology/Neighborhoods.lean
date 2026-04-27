/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Closure

/-!
# Neighborhoods in topological spaces

Each point `x` of `X` gets a neighborhood filter `𝓝 x`.

## Tags

neighborhood
-/

public section

open Set Filter Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Sort v} {α : Type*} {x : X} {s t : Set X}

theorem nhds_def' (x : X) : 𝓝 x = ⨅ (s : Set X) (_ : IsOpen s) (_ : x ∈ s), 𝓟 s := by
  simp only [nhds_def, mem_setOf_eq, @and_comm (x ∈ _), iInf_and]

/-- The open sets containing `x` are a basis for the neighborhood filter. See `nhds_basis_opens'`
for a variant using open neighborhoods instead. -/
theorem nhds_basis_opens (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => x ∈ s ∧ IsOpen s) fun s => s := by
  rw [nhds_def]
  exact hasBasis_biInf_principal
    (fun s ⟨has, hs⟩ t ⟨hat, ht⟩ =>
      ⟨s ∩ t, ⟨⟨has, hat⟩, IsOpen.inter hs ht⟩, ⟨inter_subset_left, inter_subset_right⟩⟩)
    ⟨univ, ⟨mem_univ x, isOpen_univ⟩⟩

theorem nhds_basis_closeds (x : X) : (𝓝 x).HasBasis (fun s : Set X => x ∉ s ∧ IsClosed s) compl :=
  ⟨fun t => (nhds_basis_opens x).mem_iff.trans <|
    compl_surjective.exists.trans <| by simp only [isOpen_compl_iff, mem_compl_iff]⟩

@[simp]
theorem lift'_nhds_interior (x : X) : (𝓝 x).lift' interior = 𝓝 x :=
  (nhds_basis_opens x).lift'_interior_eq_self fun _ ↦ And.right

theorem Filter.HasBasis.nhds_interior {x : X} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 x).HasBasis p s) : (𝓝 x).HasBasis p (interior <| s ·) :=
  lift'_nhds_interior x ▸ h.lift'_interior

/-- A filter lies below the neighborhood filter at `x` iff it contains every open set around `x`. -/
theorem le_nhds_iff {f} : f ≤ 𝓝 x ↔ ∀ s : Set X, x ∈ s → IsOpen s → s ∈ f := by simp [nhds_def]

/-- To show a filter is above the neighborhood filter at `x`, it suffices to show that it is above
the principal filter of some open set `s` containing `x`. -/
theorem nhds_le_of_le {f} (h : x ∈ s) (o : IsOpen s) (sf : 𝓟 s ≤ f) : 𝓝 x ≤ f := by
  rw [nhds_def]; exact iInf₂_le_of_le s ⟨h, o⟩ sf

theorem mem_nhds_iff : s ∈ 𝓝 x ↔ ∃ t ⊆ s, IsOpen t ∧ x ∈ t :=
  (nhds_basis_opens x).mem_iff.trans <| exists_congr fun _ =>
    ⟨fun h => ⟨h.2, h.1.2, h.1.1⟩, fun h => ⟨⟨h.2.2, h.2.1⟩, h.1⟩⟩

/-- A predicate is true in a neighborhood of `x` iff it is true for all the points in an open set
containing `x`. -/
theorem eventually_nhds_iff {p : X → Prop} :
    (∀ᶠ y in 𝓝 x, p y) ↔ ∃ t : Set X, (∀ y ∈ t, p y) ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff.trans <| by simp only [subset_def, mem_setOf_eq]

theorem frequently_nhds_iff {p : X → Prop} :
    (∃ᶠ y in 𝓝 x, p y) ↔ ∀ U : Set X, x ∈ U → IsOpen U → ∃ y ∈ U, p y :=
  (nhds_basis_opens x).frequently_iff.trans <| by simp

theorem mem_interior_iff_mem_nhds : x ∈ interior s ↔ s ∈ 𝓝 x :=
  mem_interior.trans mem_nhds_iff.symm

theorem map_nhds {f : X → α} :
    map f (𝓝 x) = ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 (f '' s) :=
  ((nhds_basis_opens x).map f).eq_biInf

theorem mem_of_mem_nhds : s ∈ 𝓝 x → x ∈ s := fun H =>
  let ⟨_t, ht, _, hs⟩ := mem_nhds_iff.1 H; ht hs

/-- If a predicate is true in a neighborhood of `x`, then it is true for `x`. -/
theorem Filter.Eventually.self_of_nhds {p : X → Prop} (h : ∀ᶠ y in 𝓝 x, p y) : p x :=
  mem_of_mem_nhds h

theorem IsOpen.mem_nhds (hs : IsOpen s) (hx : x ∈ s) : s ∈ 𝓝 x :=
  mem_nhds_iff.2 ⟨s, Subset.refl _, hs, hx⟩

protected theorem IsOpen.mem_nhds_iff (hs : IsOpen s) : s ∈ 𝓝 x ↔ x ∈ s :=
  ⟨mem_of_mem_nhds, fun hx => mem_nhds_iff.2 ⟨s, Subset.rfl, hs, hx⟩⟩

theorem IsClosed.compl_mem_nhds (hs : IsClosed s) (hx : x ∉ s) : sᶜ ∈ 𝓝 x :=
  hs.isOpen_compl.mem_nhds (mem_compl hx)

theorem IsOpen.eventually_mem (hs : IsOpen s) (hx : x ∈ s) :
    ∀ᶠ x in 𝓝 x, x ∈ s :=
  IsOpen.mem_nhds hs hx

/-- The open neighborhoods of `x` are a basis for the neighborhood filter. See `nhds_basis_opens`
for a variant using open sets around `x` instead. -/
theorem nhds_basis_opens' (x : X) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsOpen s) fun x => x := by
  convert nhds_basis_opens x using 2
  exact and_congr_left_iff.2 IsOpen.mem_nhds_iff

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of `s`:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds {U : Set X} (h : ∀ x ∈ s, U ∈ 𝓝 x) :
    ∃ V : Set X, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  ⟨interior U, fun x hx => mem_interior_iff_mem_nhds.2 <| h x hx, isOpen_interior, interior_subset⟩

/-- If `U` is a neighborhood of each point of a set `s` then it is a neighborhood of s:
it contains an open set containing `s`. -/
theorem exists_open_set_nhds' {U : Set X} (h : U ∈ ⨆ x ∈ s, 𝓝 x) :
    ∃ V : Set X, s ⊆ V ∧ IsOpen V ∧ V ⊆ U :=
  exists_open_set_nhds (by simpa using h)

/-- If a predicate is true in a neighbourhood of `x`, then for `y` sufficiently close
to `x` this predicate is true in a neighbourhood of `y`. -/
theorem Filter.Eventually.eventually_nhds {p : X → Prop} (h : ∀ᶠ y in 𝓝 x, p y) :
    ∀ᶠ y in 𝓝 x, ∀ᶠ x in 𝓝 y, p x :=
  let ⟨t, htp, hto, ha⟩ := eventually_nhds_iff.1 h
  eventually_nhds_iff.2 ⟨t, fun _x hx => eventually_nhds_iff.2 ⟨t, htp, hto, hx⟩, hto, ha⟩

@[simp]
theorem eventually_eventually_nhds {p : X → Prop} :
    (∀ᶠ y in 𝓝 x, ∀ᶠ x in 𝓝 y, p x) ↔ ∀ᶠ x in 𝓝 x, p x :=
  ⟨fun h => h.self_of_nhds, fun h => h.eventually_nhds⟩

@[simp]
theorem frequently_frequently_nhds {p : X → Prop} :
    (∃ᶠ x' in 𝓝 x, ∃ᶠ x'' in 𝓝 x', p x'') ↔ ∃ᶠ x in 𝓝 x, p x := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_eventually_nhds]

@[simp]
theorem eventually_mem_nhds_iff : (∀ᶠ x' in 𝓝 x, s ∈ 𝓝 x') ↔ s ∈ 𝓝 x :=
  eventually_eventually_nhds

@[simp]
theorem nhds_bind_nhds : (𝓝 x).bind 𝓝 = 𝓝 x :=
  Filter.ext fun _ => eventually_eventually_nhds

@[simp]
theorem eventually_eventuallyEq_nhds {f g : X → α} :
    (∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g) ↔ f =ᶠ[𝓝 x] g :=
  eventually_eventually_nhds

theorem Filter.EventuallyEq.eq_of_nhds {f g : X → α} (h : f =ᶠ[𝓝 x] g) : f x = g x :=
  h.self_of_nhds

@[simp]
theorem eventually_eventuallyLE_nhds [LE α] {f g : X → α} :
    (∀ᶠ y in 𝓝 x, f ≤ᶠ[𝓝 y] g) ↔ f ≤ᶠ[𝓝 x] g :=
  eventually_eventually_nhds

/-- If two functions are equal in a neighbourhood of `x`, then for `y` sufficiently close
to `x` these functions are equal in a neighbourhood of `y`. -/
theorem Filter.EventuallyEq.eventuallyEq_nhds {f g : X → α} (h : f =ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, f =ᶠ[𝓝 y] g :=
  h.eventually_nhds

/-- If `f x ≤ g x` in a neighbourhood of `x`, then for `y` sufficiently close to `x` we have
`f x ≤ g x` in a neighbourhood of `y`. -/
theorem Filter.EventuallyLE.eventuallyLE_nhds [LE α] {f g : X → α} (h : f ≤ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, f ≤ᶠ[𝓝 y] g :=
  h.eventually_nhds

theorem all_mem_nhds (x : X) (P : Set X → Prop) (hP : ∀ s t, s ⊆ t → P s → P t) :
    (∀ s ∈ 𝓝 x, P s) ↔ ∀ s, IsOpen s → x ∈ s → P s :=
  ((nhds_basis_opens x).forall_iff hP).trans <| by simp only [@and_comm (x ∈ _), and_imp]

theorem all_mem_nhds_filter (x : X) (f : Set X → Set α) (hf : ∀ s t, s ⊆ t → f s ⊆ f t)
    (l : Filter α) : (∀ s ∈ 𝓝 x, f s ∈ l) ↔ ∀ s, IsOpen s → x ∈ s → f s ∈ l :=
  all_mem_nhds _ _ fun s t ssubt h => mem_of_superset h (hf s t ssubt)

theorem tendsto_nhds {f : α → X} {l : Filter α} :
    Tendsto f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f ⁻¹' s ∈ l :=
  all_mem_nhds_filter _ _ (fun _ _ h => preimage_mono h) _

theorem tendsto_atTop_nhds [Nonempty α] [SemilatticeSup α] {f : α → X} :
    Tendsto f atTop (𝓝 x) ↔ ∀ U : Set X, x ∈ U → IsOpen U → ∃ N, ∀ n, N ≤ n → f n ∈ U :=
  (atTop_basis.tendsto_iff (nhds_basis_opens x)).trans <| by
    simp only [and_imp, true_and, mem_Ici]

theorem tendsto_const_nhds {f : Filter α} : Tendsto (fun _ : α => x) f (𝓝 x) :=
  tendsto_nhds.mpr fun _ _ ha => univ_mem' fun _ => ha

theorem tendsto_atTop_of_eventually_const {ι : Type*} [Preorder ι]
    {u : ι → X} {i₀ : ι} (h : ∀ i ≥ i₀, u i = x) : Tendsto u atTop (𝓝 x) :=
  Tendsto.congr' (EventuallyEq.symm ((eventually_ge_atTop i₀).mono h)) tendsto_const_nhds

theorem tendsto_atBot_of_eventually_const {ι : Type*} [Preorder ι]
    {u : ι → X} {i₀ : ι} (h : ∀ i ≤ i₀, u i = x) : Tendsto u atBot (𝓝 x) :=
  tendsto_atTop_of_eventually_const (ι := ιᵒᵈ) h

theorem pure_le_nhds : pure ≤ (𝓝 : X → Filter X) := fun _ _ hs => mem_pure.2 <| mem_of_mem_nhds hs

theorem tendsto_pure_nhds (f : α → X) (a : α) : Tendsto f (pure a) (𝓝 (f a)) :=
  (tendsto_pure_pure f a).mono_right (pure_le_nhds _)

theorem OrderTop.tendsto_atTop_nhds [PartialOrder α] [OrderTop α] (f : α → X) :
    Tendsto f atTop (𝓝 (f ⊤)) :=
  (tendsto_atTop_pure f).mono_right (pure_le_nhds _)

@[simp]
instance nhds_neBot : NeBot (𝓝 x) :=
  neBot_of_le (pure_le_nhds x)

theorem tendsto_nhds_of_eventually_eq {l : Filter α} {f : α → X} (h : ∀ᶠ x' in l, f x' = x) :
    Tendsto f l (𝓝 x) :=
  tendsto_const_nhds.congr' (.symm h)

theorem Filter.EventuallyEq.tendsto {l : Filter α} {f : α → X} (hf : f =ᶠ[l] fun _ ↦ x) :
    Tendsto f l (𝓝 x) :=
  tendsto_nhds_of_eventually_eq hf

/-! ### Interior, closure and frontier in terms of neighborhoods -/

theorem interior_eq_nhds' : interior s = { x | s ∈ 𝓝 x } :=
  Set.ext fun x => by simp only [mem_interior, mem_nhds_iff, mem_setOf_eq]

theorem interior_eq_nhds : interior s = { x | 𝓝 x ≤ 𝓟 s } :=
  interior_eq_nhds'.trans <| by simp only [le_principal_iff]

@[simp]
theorem interior_mem_nhds : interior s ∈ 𝓝 x ↔ s ∈ 𝓝 x :=
  ⟨fun h => mem_of_superset h interior_subset, fun h =>
    IsOpen.mem_nhds isOpen_interior (mem_interior_iff_mem_nhds.2 h)⟩

theorem interior_setOf_eq {p : X → Prop} : interior { x | p x } = { x | ∀ᶠ y in 𝓝 x, p y } :=
  interior_eq_nhds'

theorem isOpen_setOf_eventually_nhds {p : X → Prop} : IsOpen { x | ∀ᶠ y in 𝓝 x, p y } := by
  simp only [← interior_setOf_eq, isOpen_interior]

theorem subset_interior_iff_nhds {V : Set X} : s ⊆ interior V ↔ ∀ x ∈ s, V ∈ 𝓝 x := by
  simp_rw [subset_def, mem_interior_iff_mem_nhds]

theorem isOpen_iff_nhds : IsOpen s ↔ ∀ x ∈ s, 𝓝 x ≤ 𝓟 s :=
  calc
    IsOpen s ↔ s ⊆ interior s := subset_interior_iff_isOpen.symm
    _ ↔ ∀ x ∈ s, 𝓝 x ≤ 𝓟 s := by simp_rw [interior_eq_nhds, subset_def, mem_setOf]

theorem TopologicalSpace.ext_iff_nhds {X} {t t' : TopologicalSpace X} :
    t = t' ↔ ∀ x, @nhds _ t x = @nhds _ t' x :=
  ⟨fun H _ ↦ congrFun (congrArg _ H) _, fun H ↦ by ext; simp_rw [@isOpen_iff_nhds _ _ _, H]⟩

alias ⟨_, TopologicalSpace.ext_nhds⟩ := TopologicalSpace.ext_iff_nhds

theorem isOpen_iff_mem_nhds : IsOpen s ↔ ∀ x ∈ s, s ∈ 𝓝 x :=
  isOpen_iff_nhds.trans <| forall_congr' fun _ => imp_congr_right fun _ => le_principal_iff

/-- A set `s` is open iff for every point `x` in `s` and every `y` close to `x`, `y` is in `s`. -/
theorem isOpen_iff_eventually : IsOpen s ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, y ∈ s :=
  isOpen_iff_mem_nhds

theorem isOpen_singleton_iff_nhds_eq_pure (x : X) : IsOpen ({x} : Set X) ↔ 𝓝 x = pure x := by
  simp [← (pure_le_nhds _).ge_iff_eq', isOpen_iff_mem_nhds]

theorem isOpen_singleton_iff_punctured_nhds (x : X) : IsOpen ({x} : Set X) ↔ 𝓝[≠] x = ⊥ := by
  rw [isOpen_singleton_iff_nhds_eq_pure, nhdsWithin, ← mem_iff_inf_principal_compl,
      le_antisymm_iff]
  simp [pure_le_nhds x]

theorem mem_closure_iff_frequently : x ∈ closure s ↔ ∃ᶠ x in 𝓝 x, x ∈ s := by
  rw [Filter.Frequently, Filter.Eventually, ← mem_interior_iff_mem_nhds,
    closure_eq_compl_interior_compl, mem_compl_iff, compl_def]

alias ⟨_, Filter.Frequently.mem_closure⟩ := mem_closure_iff_frequently

/-- A set `s` is closed iff for every point `x`, if there is a point `y` close to `x` that belongs
to `s` then `x` is in `s`. -/
theorem isClosed_iff_frequently : IsClosed s ↔ ∀ x, (∃ᶠ y in 𝓝 x, y ∈ s) → x ∈ s := by
  rw [← closure_subset_iff_isClosed]
  refine forall_congr' fun x => ?_
  rw [mem_closure_iff_frequently]

lemma nhdsWithin_neBot : (𝓝[s] x).NeBot ↔ ∀ ⦃t⦄, t ∈ 𝓝 x → (t ∩ s).Nonempty := by
  rw [nhdsWithin, inf_neBot_iff]
  exact forall₂_congr fun U _ ↦
    ⟨fun h ↦ h (mem_principal_self _), fun h u hsu ↦ h.mono <| inter_subset_inter_right _ hsu⟩

@[gcongr]
theorem nhdsWithin_mono (x : X) {s t : Set X} (h : s ⊆ t) : 𝓝[s] x ≤ 𝓝[t] x :=
  inf_le_inf_left _ (principal_mono.mpr h)

theorem IsClosed.interior_union_left (_ : IsClosed s) :
    interior (s ∪ t) ⊆ s ∪ interior t := fun a ⟨u, ⟨⟨hu₁, hu₂⟩, ha⟩⟩ =>
  (Classical.em (a ∈ s)).imp_right fun h =>
    mem_interior.mpr
      ⟨u ∩ sᶜ, fun _x hx => (hu₂ hx.1).resolve_left hx.2, IsOpen.inter hu₁ IsClosed.isOpen_compl,
        ⟨ha, h⟩⟩

theorem IsClosed.interior_union_right (h : IsClosed t) :
    interior (s ∪ t) ⊆ interior s ∪ t := by
  simpa only [union_comm _ t] using h.interior_union_left

theorem IsOpen.inter_closure (h : IsOpen s) : s ∩ closure t ⊆ closure (s ∩ t) :=
  compl_subset_compl.mp <| by
    simpa only [← interior_compl, compl_inter] using IsClosed.interior_union_left h.isClosed_compl

theorem IsOpen.closure_inter (h : IsOpen t) : closure s ∩ t ⊆ closure (s ∩ t) := by
  simpa only [inter_comm t] using h.inter_closure

theorem Dense.open_subset_closure_inter (hs : Dense s) (ht : IsOpen t) :
    t ⊆ closure (t ∩ s) :=
  calc
    t = t ∩ closure s := by rw [hs.closure_eq, inter_univ]
    _ ⊆ closure (t ∩ s) := ht.inter_closure

/-- The intersection of an open dense set with a dense set is a dense set. -/
theorem Dense.inter_of_isOpen_left (hs : Dense s) (ht : Dense t) (hso : IsOpen s) :
    Dense (s ∩ t) := fun x =>
  closure_minimal hso.inter_closure isClosed_closure <| by simp [hs.closure_eq, ht.closure_eq]

/-- The intersection of a dense set with an open dense set is a dense set. -/
theorem Dense.inter_of_isOpen_right (hs : Dense s) (ht : Dense t) (hto : IsOpen t) :
    Dense (s ∩ t) :=
  inter_comm t s ▸ ht.inter_of_isOpen_left hs hto

theorem Dense.inter_nhds_nonempty (hs : Dense s) (ht : t ∈ 𝓝 x) :
    (s ∩ t).Nonempty :=
  let ⟨U, hsub, ho, hx⟩ := mem_nhds_iff.1 ht
  (hs.inter_open_nonempty U ho ⟨x, hx⟩).mono fun _y hy => ⟨hy.2, hsub hy.1⟩

theorem closure_diff : closure s \ closure t ⊆ closure (s \ t) :=
  calc
    closure s \ closure t = (closure t)ᶜ ∩ closure s := by simp only [diff_eq, inter_comm]
    _ ⊆ closure ((closure t)ᶜ ∩ s) := (isOpen_compl_iff.mpr <| isClosed_closure).inter_closure
    _ = closure (s \ closure t) := by simp only [diff_eq, inter_comm]
    _ ⊆ closure (s \ t) := closure_mono <| diff_subset_diff (Subset.refl s) subset_closure

theorem Filter.Frequently.mem_of_closed (h : ∃ᶠ x in 𝓝 x, x ∈ s)
    (hs : IsClosed s) : x ∈ s :=
  hs.closure_subset h.mem_closure

theorem IsClosed.mem_of_frequently_of_tendsto {f : α → X} {b : Filter α}
    (hs : IsClosed s) (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 x)) : x ∈ s :=
  (hf.frequently <| show ∃ᶠ x in b, (fun y => y ∈ s) (f x) from h).mem_of_closed hs

theorem IsClosed.mem_of_tendsto {f : α → X} {b : Filter α} [NeBot b]
    (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ s :=
  hs.mem_of_frequently_of_tendsto h.frequently hf

theorem mem_closure_of_frequently_of_tendsto {f : α → X} {b : Filter α}
    (h : ∃ᶠ x in b, f x ∈ s) (hf : Tendsto f b (𝓝 x)) : x ∈ closure s :=
  (hf.frequently h).mem_closure

theorem mem_closure_of_tendsto {f : α → X} {b : Filter α} [NeBot b]
    (hf : Tendsto f b (𝓝 x)) (h : ∀ᶠ x in b, f x ∈ s) : x ∈ closure s :=
  mem_closure_of_frequently_of_tendsto h.frequently hf

/-- Suppose that `f` sends the complement to `s` to a single point `x`, and `l` is some filter.
Then `f` tends to `x` along `l` restricted to `s` if and only if it tends to `x` along `l`. -/
theorem tendsto_inf_principal_nhds_iff_of_forall_eq {f : α → X} {l : Filter α} {s : Set α}
    (h : ∀ a ∉ s, f a = x) : Tendsto f (l ⊓ 𝓟 s) (𝓝 x) ↔ Tendsto f l (𝓝 x) := by
  rw [tendsto_iff_comap, tendsto_iff_comap]
  replace h : 𝓟 sᶜ ≤ comap f (𝓝 x) := by
    rintro U ⟨t, ht, htU⟩ x hx
    have : f x ∈ t := (h x hx).symm ▸ mem_of_mem_nhds ht
    exact htU this
  refine ⟨fun h' => ?_, le_trans inf_le_left⟩
  have := sup_le h' h
  rw [sup_inf_right, sup_principal, union_compl_self, principal_univ, inf_top_eq, sup_le_iff]
    at this
  exact this.1
