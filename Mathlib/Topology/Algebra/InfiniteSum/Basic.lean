/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Lee
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Order.Filter.AtTopBot.BigOperators

/-!
# Lemmas on infinite sums and products in topological monoids

This file contains many simple lemmas on `tsum`, `HasSum` etc, which are placed here in order to
keep the basic file of definitions as short as possible.

Results requiring a group (rather than monoid) structure on the target should go in `Group.lean`.

-/

public section

noncomputable section

open Filter Finset Function Topology SummationFilter

variable {α β γ : Type*}

section HasProd

variable [CommMonoid α] [TopologicalSpace α]
variable {f g : β → α} {a b : α} {L : SummationFilter β}

/-- Constant one function has product `1` -/
@[to_additive (attr := simp) /-- Constant zero function has sum `0` -/]
theorem hasProd_one : HasProd (fun _ ↦ 1 : β → α) 1 L := by simp [HasProd, tendsto_const_nhds]

@[to_additive (attr := simp)]
theorem hasProd_empty [IsEmpty β] : HasProd f 1 L := by
  convert hasProd_one

@[to_additive (attr := nontriviality)]
theorem HasProd.of_subsingleton_cod [Subsingleton α] : HasProd f 1 L := by
  convert hasProd_one

@[to_additive (attr := simp)]
theorem multipliable_one : Multipliable (fun _ ↦ 1 : β → α) L :=
  hasProd_one.multipliable

@[to_additive (attr := simp)]
theorem multipliable_empty [IsEmpty β] : Multipliable f L :=
  hasProd_empty.multipliable

@[to_additive (attr := nontriviality)]
theorem Multipliable.of_subsingleton_cod [Subsingleton α] : Multipliable f L :=
  HasProd.of_subsingleton_cod.multipliable

/-- See `multipliable_congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/
@[to_additive /-- See `summable_congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/]
theorem multipliable_congr (hfg : ∀ b, f b = g b) : Multipliable f L ↔ Multipliable g L :=
  iff_of_eq (congr_arg (Multipliable · L) <| funext hfg)

/-- See `Multipliable.congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/
@[to_additive /-- See `Summable.congr_cofinite` for a version allowing the functions to
disagree on a finite set. -/]
theorem Multipliable.congr (hf : Multipliable f L) (hfg : ∀ b, f b = g b) : Multipliable g L :=
  (multipliable_congr hfg).mp hf

@[to_additive]
lemma HasProd.congr_fun (hf : HasProd f a L) (h : ∀ x : β, g x = f x) : HasProd g a L :=
  (funext h : g = f) ▸ hf

@[to_additive]
theorem HasProd.hasProd_of_prod_eq {g : γ → α}
    (h_eq : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' →
      ∃ u', u ⊆ u' ∧ ∏ x ∈ u', g x = ∏ b ∈ v', f b)
    (hf : HasProd g a) : HasProd f a :=
  le_trans (map_atTop_finset_prod_le_of_prod_eq h_eq) hf

@[to_additive]
theorem hasProd_iff_hasProd {g : γ → α}
    (h₁ : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' →
      ∃ u', u ⊆ u' ∧ ∏ x ∈ u', g x = ∏ b ∈ v', f b)
    (h₂ : ∀ v : Finset β, ∃ u : Finset γ, ∀ u', u ⊆ u' →
      ∃ v', v ⊆ v' ∧ ∏ b ∈ v', f b = ∏ x ∈ u', g x) :
    HasProd f a ↔ HasProd g a :=
  ⟨HasProd.hasProd_of_prod_eq h₂, HasProd.hasProd_of_prod_eq h₁⟩

@[to_additive]
theorem Function.Injective.multipliable_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x ∉ Set.range g, f x = 1) : Multipliable (f ∘ g) ↔ Multipliable f :=
  exists_congr fun _ ↦ hg.hasProd_iff hf

@[to_additive (attr := simp)] theorem hasProd_extend_one {g : β → γ} (hg : Injective g) :
    HasProd (extend g f 1) a ↔ HasProd f a := by
  rw [← hg.hasProd_iff, extend_comp hg]
  exact extend_apply' _ _

@[to_additive (attr := simp)] theorem multipliable_extend_one {g : β → γ} (hg : Injective g) :
    Multipliable (extend g f 1) ↔ Multipliable f :=
  exists_congr fun _ ↦ hasProd_extend_one hg

@[to_additive]
theorem hasProd_subtype_iff_mulIndicator {s : Set β} :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd (s.mulIndicator f) a := by
  rw [← Set.mulIndicator_range_comp, Subtype.range_coe,
    hasProd_subtype_iff_of_mulSupport_subset Set.mulSupport_mulIndicator_subset]

@[to_additive]
theorem multipliable_subtype_iff_mulIndicator {s : Set β} :
    Multipliable (f ∘ (↑) : s → α) ↔ Multipliable (s.mulIndicator f) :=
  exists_congr fun _ ↦ hasProd_subtype_iff_mulIndicator

@[to_additive (attr := simp)]
theorem hasProd_subtype_mulSupport : HasProd (f ∘ (↑) : mulSupport f → α) a ↔ HasProd f a :=
  hasProd_subtype_iff_of_mulSupport_subset <| Set.Subset.refl _

@[to_additive]
protected theorem Finset.multipliable (s : Finset β) (f : β → α) :
    Multipliable (f ∘ (↑) : (↑s : Set β) → α) :=
  (s.hasProd f).multipliable

@[to_additive]
protected theorem Set.Finite.multipliable {s : Set β} (hs : s.Finite) (f : β → α) :
    Multipliable (f ∘ (↑) : s → α) := by
  have := hs.toFinset.multipliable f
  rwa [hs.coe_toFinset] at this

@[to_additive]
theorem multipliable_of_hasFiniteMulSupport [L.HasSupport] (h : HasFiniteMulSupport f) :
    Multipliable f L := by
  apply multipliable_of_ne_finset_one (s := h.toFinset); simp

@[deprecated (since := "2026-03-03")] alias
  multipliable_of_finite_mulSupport := multipliable_of_hasFiniteMulSupport

@[deprecated (since := "2026-03-03")] alias
  summable_of_finite_support := summable_of_hasFiniteSupport

@[to_additive]
lemma Multipliable.of_finite [Finite β] [L.HasSupport] {f : β → α} : Multipliable f L :=
  multipliable_of_hasFiniteMulSupport <| Set.finite_univ.subset (Set.subset_univ _)

@[to_additive]
theorem hasProd_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 1)
    (L := unconditional β) [L.LeAtTop] : HasProd f (f b) L :=
  suffices HasProd f (∏ b' ∈ {b}, f b') L by simpa using this
  hasProd_prod_of_ne_finset_one <| by simpa [hf]

@[to_additive (attr := simp)]
lemma hasProd_unique [Unique β] (f : β → α) (L := unconditional β) [L.LeAtTop] :
    HasProd f (f default) L :=
  hasProd_single default (fun _ hb ↦ False.elim <| hb <| Unique.uniq ..) L

@[to_additive (attr := simp)]
lemma hasProd_singleton (m : β) (f : β → α) : HasProd (({m} : Set β).restrict f) (f m) :=
  hasProd_unique (Set.restrict {m} f)

@[to_additive]
theorem hasProd_ite_eq (b : β) [DecidablePred (· = b)] (a : α) (L := unconditional β) [L.LeAtTop] :
    HasProd (fun b' ↦ if b' = b then a else 1) a L := by
  convert hasProd_single b (hf := fun b' hb' ↦ if_neg hb') (L := L)
  exact (if_pos rfl).symm

@[to_additive]
theorem Equiv.hasProd_iff (e : γ ≃ β) : HasProd (f ∘ e) a ↔ HasProd f a :=
  e.injective.hasProd_iff <| by simp

@[to_additive]
theorem Function.Injective.hasProd_range_iff {g : γ → β} (hg : Injective g) :
    HasProd (fun x : Set.range g ↦ f x) a ↔ HasProd (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasProd_iff.symm

@[to_additive]
theorem Equiv.multipliable_iff (e : γ ≃ β) : Multipliable (f ∘ e) ↔ Multipliable f :=
  exists_congr fun _ ↦ e.hasProd_iff

@[to_additive]
theorem Equiv.hasProd_iff_of_mulSupport {g : γ → α} (e : mulSupport f ≃ mulSupport g)
    (he : ∀ x : mulSupport f, g (e x) = f x) : HasProd f a ↔ HasProd g a := by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  rw [← hasProd_subtype_mulSupport, ← this, e.hasProd_iff, hasProd_subtype_mulSupport]

@[to_additive]
theorem hasProd_iff_hasProd_of_ne_one_bij {g : γ → α} (i : mulSupport g → β)
    (hi : Injective i) (hf : mulSupport f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : HasProd f a ↔ HasProd g a :=
  Iff.symm <|
    Equiv.hasProd_iff_of_mulSupport
      (Equiv.ofBijective (fun x ↦ ⟨i x, fun hx ↦ x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun _ _ h ↦ hi <| Subtype.ext_iff.1 h, fun y ↦
          (hf y.coe_prop).imp fun _ hx ↦ Subtype.ext hx⟩)
      hfg

@[to_additive]
theorem Equiv.multipliable_iff_of_mulSupport {g : γ → α} (e : mulSupport f ≃ mulSupport g)
    (he : ∀ x : mulSupport f, g (e x) = f x) : Multipliable f ↔ Multipliable g :=
  exists_congr fun _ ↦ e.hasProd_iff_of_mulSupport he

@[to_additive]
protected theorem HasProd.map [CommMonoid γ] [TopologicalSpace γ] (hf : HasProd f a L) {G}
    [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    HasProd (g ∘ f) (g a) L := by
  have : (g ∘ fun s : Finset β ↦ ∏ b ∈ s, f b) = fun s : Finset β ↦ ∏ b ∈ s, (g ∘ f) b :=
    funext <| map_prod g _
  unfold HasProd
  rw [← this]
  exact (hg.tendsto a).comp hf

@[to_additive]
protected theorem Topology.IsInducing.hasProd_iff [CommMonoid γ] [TopologicalSpace γ] {G}
    [FunLike G α γ] [MonoidHomClass G α γ] {g : G} (hg : IsInducing g) (f : β → α) (a : α) :
    HasProd (g ∘ f) (g a) L ↔ HasProd f a L := by
  simp_rw [HasProd, comp_apply, ← map_prod]
  exact hg.tendsto_nhds_iff.symm

@[to_additive]
protected theorem Multipliable.map [CommMonoid γ] [TopologicalSpace γ]
    (hf : Multipliable f L) {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    Multipliable (g ∘ f) L :=
  (hf.hasProd.map g hg).multipliable

@[to_additive]
protected theorem Multipliable.map_iff_of_leftInverse [CommMonoid γ]
    [TopologicalSpace γ] {G G'}
    [FunLike G α γ] [MonoidHomClass G α γ] [FunLike G' γ α] [MonoidHomClass G' γ α]
    (g : G) (g' : G') (hg : Continuous g) (hg' : Continuous g') (hinv : Function.LeftInverse g' g) :
    Multipliable (g ∘ f) L ↔ Multipliable f L :=
  ⟨fun h ↦ by
    have := h.map _ hg'
    rwa [← Function.comp_assoc, hinv.id] at this, fun h ↦ h.map _ hg⟩

@[to_additive]
theorem Multipliable.map_tprod [L.NeBot] [CommMonoid γ] [TopologicalSpace γ] [T2Space γ]
    (hf : Multipliable f L) {G} [FunLike G α γ] [MonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    g (∏'[L] i, f i) = ∏'[L] i, g (f i) :=
  (HasProd.tprod_eq (HasProd.map hf.hasProd g hg)).symm

@[to_additive]
lemma Topology.IsClosedEmbedding.map_tprod {ι α α' G : Type*}
    [CommMonoid α] [CommMonoid α'] [TopologicalSpace α] [TopologicalSpace α'] [T2Space α']
    (f : ι → α) {L : SummationFilter ι} {g : G} [FunLike G α α'] [MonoidHomClass G α α']
    (hge : Topology.IsClosedEmbedding g) :
    g (∏'[L] i, f i) = ∏'[L] i, g (f i) := by
  by_cases hL : L.NeBot
  · by_cases h : Multipliable f L
    · exact h.map_tprod g hge.continuous
    · rw [tprod_eq_one_of_not_multipliable h, tprod_eq_one_of_not_multipliable, map_one]
      contrapose! h
      -- need to show `g ∘ f` multipliable implies `g` multipliable
      simp only [Multipliable, HasProd] at h ⊢
      obtain ⟨b, hb⟩ := h
      obtain ⟨a, ha⟩ : b ∈ Set.range g :=
        hge.isClosed_range.mem_of_tendsto hb (.of_forall <| by simp [← map_prod])
      use a
      simp [hge.tendsto_nhds_iff, Function.comp_def, ha, hb]
  · simpa [tprod_bot hL] using
      (MonoidHomClass.toMonoidHom g).map_finprod_of_injective hge.injective _

/-- Special case of `Topology.IsClosedEmbedding.map_tprod`, logically weaker but possibly easier
to apply in practice. -/
@[to_additive /-- Special case of `Topology.IsClosedEmbedding.map_tsum`, logically weaker but
possibly easier to apply in practice. -/]
lemma Function.LeftInverse.map_tprod {G : Type*} (f : β → α) [CommMonoid γ] [TopologicalSpace γ]
    [T2Space γ] {g : G} [FunLike G α γ] [MonoidHomClass G α γ] (hg : Continuous g)
    {g' : γ → α} (hg' : Continuous g') (hgg' : LeftInverse g' g) :
    g (∏'[L] b, f b) = ∏'[L] b, g (f b) :=
  (hgg'.isClosedEmbedding hg' hg).map_tprod _

@[to_additive]
lemma Topology.IsInducing.multipliable_iff_tprod_comp_mem_range [CommMonoid γ] [TopologicalSpace γ]
    [T2Space γ] {G} [FunLike G α γ] [MonoidHomClass G α γ] {g : G} (hg : IsInducing g) (f : β → α) :
    Multipliable f L ↔ Multipliable (g ∘ f) L ∧ ∏'[L] i, g (f i) ∈ Set.range g := by
  constructor
  · intro hf
    constructor
    · exact hf.map g hg.continuous
    · by_cases hL : L.NeBot
      · exact ⟨_, hf.map_tprod g hg.continuous⟩
      · by_cases hfs : (mulSupport fun x ↦ g (f x)).Finite
        · simp [tprod_bot hL, finprod_eq_prod _ hfs, ← map_prod]
        · exact ⟨1, by simp [tprod_bot hL, finprod_of_infinite_mulSupport hfs]⟩
  · rintro ⟨hgf, a, ha⟩
    use a
    have := hgf.hasProd
    simp_rw [comp_apply, ← ha] at this
    exact (hg.hasProd_iff f a).mp this

/-- "A special case of `Multipliable.map_iff_of_leftInverse` for convenience" -/
@[to_additive /-- A special case of `Summable.map_iff_of_leftInverse` for convenience -/]
protected theorem Multipliable.map_iff_of_equiv [CommMonoid γ] [TopologicalSpace γ] {G}
    [EquivLike G α γ] [MulEquivClass G α γ] (g : G) (hg : Continuous g)
    (hg' : Continuous (EquivLike.inv g : γ → α)) :
    Multipliable (g ∘ f) L ↔ Multipliable f L :=
  Multipliable.map_iff_of_leftInverse g (g : α ≃* γ).symm hg hg' (EquivLike.left_inv g)

@[to_additive]
theorem Function.Surjective.multipliable_iff_of_hasProd_iff {α' : Type*} [CommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'}
    (he : ∀ {a}, HasProd f (e a) ↔ HasProd g a) : Multipliable f ↔ Multipliable g :=
  hes.exists.trans <| exists_congr <| @he

variable [ContinuousMul α]

@[to_additive]
theorem HasProd.mul (hf : HasProd f a L) (hg : HasProd g b L) :
    HasProd (fun b ↦ f b * g b) (a * b) L := by
  dsimp only [HasProd] at hf hg ⊢
  simp_rw [prod_mul_distrib]
  exact hf.mul hg

@[to_additive]
theorem Multipliable.mul (hf : Multipliable f L) (hg : Multipliable g L) :
    Multipliable (fun b ↦ f b * g b) L :=
  (hf.hasProd.mul hg.hasProd).multipliable

@[to_additive]
theorem hasProd_prod {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀ i ∈ s, HasProd (f i) (a i) L) → HasProd (fun b ↦ ∏ i ∈ s, f i b) (∏ i ∈ s, a i) L := by
  classical
  exact Finset.induction_on s (by simp only [hasProd_one, prod_empty, forall_true_iff]) <| by
    simp +contextual only [mem_insert, forall_eq_or_imp, not_false_iff,
      prod_insert, and_imp]
    exact fun x s _ IH hx h ↦ hx.mul (IH h)

@[to_additive]
theorem multipliable_prod {f : γ → β → α} {s : Finset γ}
    (hf : ∀ i ∈ s, Multipliable (f i) L) : Multipliable (fun b ↦ ∏ i ∈ s, f i b) L :=
  (hasProd_prod fun i hi ↦ (hf i hi).hasProd).multipliable

@[to_additive]
theorem HasProd.mul_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : t → α) b) : HasProd (f ∘ (↑) : (s ∪ t : Set β) → α) (a * b) := by
  rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Set.mulIndicator_union_of_disjoint hs]
  exact ha.mul hb

@[to_additive]
theorem hasProd_prod_disjoint {ι} (s : Finset ι) {t : ι → Set β} {a : ι → α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, HasProd (f ∘ (↑) : t i → α) (a i)) :
    HasProd (f ∘ (↑) : (⋃ i ∈ s, t i) → α) (∏ i ∈ s, a i) := by
  simp_rw [hasProd_subtype_iff_mulIndicator] at *
  rw [Finset.mulIndicator_biUnion _ _ hs]
  exact hasProd_prod hf

@[to_additive]
theorem HasProd.mul_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : t → α) b) : HasProd f (a * b) := by
  simpa [← hs.compl_eq] using
    (hasProd_subtype_iff_mulIndicator.1 ha).mul (hasProd_subtype_iff_mulIndicator.1 hb)

@[to_additive]
theorem HasProd.mul_compl {s : Set β} (ha : HasProd (f ∘ (↑) : s → α) a)
    (hb : HasProd (f ∘ (↑) : (sᶜ : Set β) → α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl hb

@[to_additive]
theorem Multipliable.mul_compl {s : Set β} (hs : Multipliable (f ∘ (↑) : s → α))
    (hsc : Multipliable (f ∘ (↑) : (sᶜ : Set β) → α)) : Multipliable f :=
  (hs.hasProd.mul_compl hsc.hasProd).multipliable

@[to_additive]
theorem HasProd.compl_mul {s : Set β} (ha : HasProd (f ∘ (↑) : (sᶜ : Set β) → α) a)
    (hb : HasProd (f ∘ (↑) : s → α) b) : HasProd f (a * b) :=
  ha.mul_isCompl isCompl_compl.symm hb

@[to_additive]
theorem Multipliable.compl_add {s : Set β} (hs : Multipliable (f ∘ (↑) : (sᶜ : Set β) → α))
    (hsc : Multipliable (f ∘ (↑) : s → α)) : Multipliable f :=
  (hs.hasProd.compl_mul hsc.hasProd).multipliable

/-- Version of `HasProd.update` for `CommMonoid` rather than `CommGroup`.
Rather than showing that `f.update` has a specific product in terms of `HasProd`,
it gives a relationship between the products of `f` and `f.update` given that both exist. -/
@[to_additive /-- Version of `HasSum.update` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that `f.update` has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/]
theorem HasProd.update' [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
    [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β → α} {a a' : α} (hf : HasProd f a L)
    (b : β) (x : α) (hf' : HasProd (update f b x) a' L) :
    a * x = a' * f b := by
  have : ∀ b', f b' * ite (b' = b) x 1 = update f b x b' * ite (b' = b) (f b) 1 := by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using mul_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.mul (hasProd_ite_eq b x L)
  simp_rw [this] at h
  exact HasProd.unique h (hf'.mul (hasProd_ite_eq b (f b) L))

/-- Version of `hasProd_ite_div_hasProd` for `CommMonoid` rather than `CommGroup`.
Rather than showing that the `ite` expression has a specific product in terms of `HasProd`, it gives
a relationship between the products of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
@[to_additive /-- Version of `hasSum_ite_sub_hasSum` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that the `ite` expression has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/]
theorem eq_mul_of_hasProd_ite [L.LeAtTop] [L.NeBot] {α : Type*} [TopologicalSpace α] [CommMonoid α]
    [T2Space α] [ContinuousMul α] [DecidableEq β] {f : β → α} {a : α} (hf : HasProd f a L) (b : β)
    (a' : α) (hf' : HasProd (fun n ↦ ite (n = b) 1 (f n)) a' L) : a = a' * f b := by
  refine (mul_one a).symm.trans (hf.update' b 1 ?_)
  convert hf'
  apply update_apply

end HasProd

section tprod

variable [CommMonoid α] [TopologicalSpace α] {f g : β → α} {L : SummationFilter β}

@[to_additive]
theorem tprod_congr_set_coe (f : β → α) {s t : Set β} (h : s = t) :
    ∏' x : s, f x = ∏' x : t, f x := by rw [h]

@[to_additive]
theorem tprod_congr_subtype (f : β → α) {P Q : β → Prop} (h : ∀ x, P x ↔ Q x) :
    ∏' x : {x // P x}, f x = ∏' x : {x // Q x}, f x :=
  tprod_congr_set_coe f <| Set.ext h

@[to_additive]
theorem tprod_eq_finprod [L.LeAtTop] (hf : HasFiniteMulSupport f) :
    ∏'[L] b, f b = ∏ᶠ b, f b := by
  simp [tprod_def, multipliable_of_hasFiniteMulSupport hf, show Set.Finite _ from hf,
    show L.HasSupport by infer_instance]

@[to_additive]
theorem tprod_eq_prod' [L.LeAtTop] {s : Finset β} (hf : mulSupport f ⊆ s) :
    ∏'[L] b, f b = ∏ b ∈ s, f b := by
  rw [tprod_eq_finprod (s.finite_toSet.subset hf), finprod_eq_prod_of_mulSupport_subset _ hf]

@[to_additive]
theorem tprod_eq_prod [L.LeAtTop] {s : Finset β} (hf : ∀ b ∉ s, f b = 1) :
    ∏'[L] b, f b = ∏ b ∈ s, f b :=
  tprod_eq_prod' <| mulSupport_subset_iff'.2 hf

@[to_additive (attr := simp)]
theorem tprod_one : ∏'[L] _, (1 : α) = 1 := by
  rw [tprod_def, dif_pos multipliable_one, mulSupport_fun_one, Set.empty_inter,
    Set.mulIndicator_one, finprod_one, eq_true_intro hasProd_one, if_true, ite_self]

@[to_additive (attr := simp)]
theorem tprod_empty [IsEmpty β] : ∏'[L] b, f b = 1 := by
  convert tprod_one (L := L)

@[to_additive]
theorem tprod_congr {f g : β → α}
    (hfg : ∀ b, f b = g b) : ∏'[L] b, f b = ∏'[L] b, g b :=
  congr_arg (tprod · L) (funext hfg)

@[to_additive]
theorem tprod_congr₂ {f g : β → γ → α} {M : SummationFilter γ}
    (hfg : ∀ b c, f b c = g b c) : ∏'[L] b, ∏'[M] c, f b c = ∏'[L] b, ∏'[M] c, g b c :=
  tprod_congr fun b ↦ tprod_congr fun c ↦ hfg b c

@[to_additive (attr := simp)]
theorem tprod_fintype [L.LeAtTop] [Fintype β] (f : β → α) : ∏'[L] b, f b = ∏ b, f b := by
  apply tprod_eq_prod; simp

@[to_additive]
theorem prod_eq_tprod_mulIndicator (f : β → α) (s : Finset β) (L := unconditional β) [L.LeAtTop] :
    ∏ x ∈ s, f x = ∏'[L] x, Set.mulIndicator (↑s) f x := by
  rw [tprod_eq_prod' (Set.mulSupport_mulIndicator_subset),
      Finset.prod_mulIndicator_subset _ Finset.Subset.rfl]

@[to_additive]
theorem tprod_bool (f : Bool → α) : ∏' i : Bool, f i = f false * f true := by
  rw [tprod_fintype, Fintype.prod_bool, mul_comm]

@[to_additive]
theorem tprod_eq_mulSingle [L.LeAtTop] {f : β → α} (b : β) (hf : ∀ b' ≠ b, f b' = 1) :
    ∏'[L] b, f b = f b := by
  rw [tprod_eq_prod (s := {b}), prod_singleton]
  exact fun b' hb' ↦ hf b' (by simpa using hb')

@[to_additive]
theorem tprod_tprod_eq_mulSingle
    (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ b' ≠ b, f b' c = 1)
    (hfc : ∀ b', ∀ c' ≠ c, f b' c' = 1) : ∏' (b') (c'), f b' c' = f b c :=
  calc
    ∏' (b') (c'), f b' c' = ∏' b', f b' c := tprod_congr fun b' ↦ tprod_eq_mulSingle _ (hfc b')
    _ = f b c := tprod_eq_mulSingle _ hfb

@[to_additive (attr := simp)]
theorem tprod_ite_eq (b : β) [DecidablePred (· = b)] (a : β → α)
    (L := unconditional β) [L.LeAtTop] :
    ∏'[L] b', (if b' = b then a b' else 1) = a b := by
  rw [tprod_eq_mulSingle b]
  · simp
  · intro b' hb'; simp [hb']

@[to_additive]
theorem Finset.tprod_subtype (s : Finset β) (f : β → α) :
    ∏' x : { x // x ∈ s }, f x = ∏ x ∈ s, f x := by
  rw [← prod_attach]; exact tprod_fintype _

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
theorem Finset.tprod_subtype' (s : Finset β) (f : β → α) :
    ∏' x : (s : Set β), f x = ∏ x ∈ s, f x := by
  simp [prod_attach]

@[to_additive]
theorem tprod_singleton (b : β) (f : β → α) : ∏' x : ({b} : Set β), f x = f b := by simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
theorem Function.Injective.tprod_eq {g : γ → β} (hg : Injective g) {f : β → α}
    (hf : mulSupport f ⊆ Set.range g) : ∏' c, f (g c) = ∏' b, f b := by
  classical
  have : mulSupport f = g '' mulSupport (f ∘ g) := by
    rw [mulSupport_comp_eq_preimage, Set.image_preimage_eq_iff.2 hf]
  rw [← Function.comp_def]
  by_cases hf_fin : (mulSupport f).Finite
  · have hfg_fin : (mulSupport (f ∘ g)).Finite := hf_fin.preimage hg.injOn
    lift g to γ ↪ β using hg
    simp_rw [tprod_eq_prod' hf_fin.coe_toFinset.ge, tprod_eq_prod' hfg_fin.coe_toFinset.ge,
      comp_apply, ← Finset.prod_map]
    refine Finset.prod_congr (Finset.coe_injective ?_) fun _ _ ↦ rfl
    simp [this]
  · have hf_fin' : ¬ Set.Finite (mulSupport (f ∘ g)) := by
      rwa [this, Set.finite_image_iff hg.injOn] at hf_fin
    simp_rw [tprod_def, SummationFilter.support_eq_univ, Set.inter_univ,
      show (unconditional β).HasSupport by infer_instance,
      show (unconditional γ).HasSupport by infer_instance, true_and,
      if_neg hf_fin, if_neg hf_fin', Multipliable]
    simp [hg.hasProd_iff (mulSupport_subset_iff'.1 hf)]

@[to_additive]
theorem Equiv.tprod_eq (e : γ ≃ β) (f : β → α) : ∏' c, f (e c) = ∏' b, f b :=
  e.injective.tprod_eq <| by simp

@[to_additive (attr := simp)]
theorem tprod_comp_neg {β : Type*} [InvolutiveNeg β] (f : β → α) :
    ∏' d, f (-d) = ∏' d, f d :=
  (Equiv.neg β).tprod_eq f

/-! ### `tprod` on subsets - part 1 -/

@[to_additive]
theorem tprod_subtype_eq_of_mulSupport_subset {f : β → α} {s : Set β} (hs : mulSupport f ⊆ s) :
    ∏' x : s, f x = ∏' x, f x :=
  Subtype.val_injective.tprod_eq <| by simpa

@[to_additive]
theorem tprod_subtype_mulSupport (f : β → α) : ∏' x : mulSupport f, f x = ∏' x, f x :=
  tprod_subtype_eq_of_mulSupport_subset Set.Subset.rfl

@[to_additive]
theorem tprod_subtype (s : Set β) (f : β → α) : ∏' x : s, f x = ∏' x, s.mulIndicator f x := by
  rw [← tprod_subtype_eq_of_mulSupport_subset Set.mulSupport_mulIndicator_subset, tprod_congr]
  simp

@[to_additive (attr := simp)]
theorem tprod_univ (f : β → α) : ∏' x : (Set.univ : Set β), f x = ∏' x, f x :=
  tprod_subtype_eq_of_mulSupport_subset <| Set.subset_univ _

@[to_additive]
theorem tprod_image {g : γ → β} (f : β → α) {s : Set γ} (hg : Set.InjOn g s) :
    ∏' x : g '' s, f x = ∏' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tprod_eq fun x ↦ f x).symm

@[to_additive]
theorem tprod_range {g : γ → β} (f : β → α) (hg : Injective g) :
    ∏' x : Set.range g, f x = ∏' x, f (g x) := by
  rw [← Set.image_univ, tprod_image f hg.injOn]
  simp_rw [← comp_apply (g := g), tprod_univ (f ∘ g)]

/-- If `f b = 1` for all `b ∈ t`, then the product of `f a` with `a ∈ s` is the same as the
product of `f a` with `a ∈ s ∖ t`. -/
@[to_additive /-- If `f b = 0` for all `b ∈ t`, then the sum of `f a` with `a ∈ s` is the same as
the sum of `f a` with `a ∈ s ∖ t`. -/]
lemma tprod_setElem_eq_tprod_setElem_diff {f : β → α} (s t : Set β)
    (hf₀ : ∀ b ∈ t, f b = 1) :
    ∏' a : s, f a = ∏' a : (s \ t : Set β), f a :=
  .symm <| (Set.inclusion_injective (t := s) Set.diff_subset).tprod_eq (f := f ∘ (↑)) <|
    mulSupport_subset_iff'.2 fun b hb ↦ hf₀ b <| by simpa using hb

/-- If `f b = 1`, then the product of `f a` with `a ∈ s` is the same as the product of `f a` for
`a ∈ s ∖ {b}`. -/
@[to_additive /-- If `f b = 0`, then the sum of `f a` with `a ∈ s` is the same as the sum of `f a`
for `a ∈ s ∖ {b}`. -/]
lemma tprod_eq_tprod_diff_singleton {f : β → α} (s : Set β) {b : β} (hf₀ : f b = 1) :
    ∏' a : s, f a = ∏' a : (s \ {b} : Set β), f a :=
  tprod_setElem_eq_tprod_setElem_diff s {b} fun _ ha ↦ ha ▸ hf₀

@[to_additive]
theorem tprod_eq_tprod_of_ne_one_bij {g : γ → α} (i : mulSupport g → β) (hi : Injective i)
    (hf : mulSupport f ⊆ Set.range i) (hfg : ∀ x, f (i x) = g x) : ∏' x, f x = ∏' y, g y := by
  rw [← tprod_subtype_mulSupport g, ← hi.tprod_eq hf]
  simp only [hfg]

@[to_additive]
theorem Equiv.tprod_eq_tprod_of_mulSupport {f : β → α} {g : γ → α}
    (e : mulSupport f ≃ mulSupport g) (he : ∀ x, g (e x) = f x) :
    ∏' x, f x = ∏' y, g y :=
  .symm <| tprod_eq_tprod_of_ne_one_bij _ (Subtype.val_injective.comp e.injective) (by simp) he

@[to_additive]
theorem tprod_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    ∏'[L] b, (if h : P then 1 else x b h) = if h : P then 1 else ∏'[L] b, x b h := by
  by_cases hP : P <;> simp [hP]

@[to_additive]
theorem tprod_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    ∏'[L] b, (if h : P then x b h else 1) = if h : P then ∏'[L] b, x b h else 1 := by
  by_cases hP : P <;> simp [hP]

@[to_additive (attr := simp)]
lemma tprod_extend_one {γ : Type*} {g : γ → β} (hg : Injective g) (f : γ → α) :
    ∏' y, extend g f 1 y = ∏' x, f x := by
  have : mulSupport (extend g f 1) ⊆ Set.range g := mulSupport_subset_iff'.2 <| extend_apply' _ _
  simp_rw [← hg.tprod_eq this, hg.extend_apply]

variable [T2Space α]

@[to_additive]
theorem Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd {α' : Type*} [CommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) (h1 : e 1 = 1) {f : β → α}
    {g : γ → α'} (h : ∀ {a}, HasProd f (e a) ↔ HasProd g a) : ∏' b, f b = e (∏' c, g c) :=
  by_cases (fun x ↦ (h.mpr x.hasProd).tprod_eq) fun hg : ¬Multipliable g ↦ by
    have hf : ¬Multipliable f := mt (hes.multipliable_iff_of_hasProd_iff @h).1 hg
    simp [tprod_def, hf, hg, h1]

@[to_additive]
theorem tprod_eq_tprod_of_hasProd_iff_hasProd {f : β → α} {g : γ → α}
    (h : ∀ {a}, HasProd f a ↔ HasProd g a) : ∏' b, f b = ∏' c, g c :=
  surjective_id.tprod_eq_tprod_of_hasProd_iff_hasProd rfl @h

section ContinuousMul

variable [ContinuousMul α]

@[to_additive]
protected theorem Multipliable.tprod_mul [L.NeBot]
    (hf : Multipliable f L) (hg : Multipliable g L) :
    ∏'[L] b, (f b * g b) = (∏'[L] b, f b) * ∏'[L] b, g b :=
  (hf.hasProd.mul hg.hasProd).tprod_eq

@[to_additive]
protected theorem Multipliable.tprod_finsetProd [L.NeBot] {f : γ → β → α} {s : Finset γ}
    (hf : ∀ i ∈ s, Multipliable (f i) L) : ∏'[L] b, ∏ i ∈ s, f i b = ∏ i ∈ s, ∏'[L] b, f i b :=
  (hasProd_prod fun i hi ↦ (hf i hi).hasProd).tprod_eq

/-- Version of `tprod_eq_mul_tprod_ite` for `CommMonoid` rather than `CommGroup`.
Requires a different convergence assumption involving `Function.update`. -/
@[to_additive /-- Version of `tsum_eq_add_tsum_ite` for `AddCommMonoid` rather than `AddCommGroup`.
Requires a different convergence assumption involving `Function.update`. -/]
protected theorem Multipliable.tprod_eq_mul_tprod_ite' [DecidableEq β] [L.LeAtTop] [L.NeBot]
    {f : β → α} (b : β) (hf : Multipliable (update f b 1) L) :
    ∏'[L] x, f x = f b * ∏'[L] x, ite (x = b) 1 (f x) :=
  calc
    ∏'[L] x, f x = ∏'[L] x, (ite (x = b) (f x) 1 * update f b 1 x) :=
      tprod_congr fun n ↦ by split_ifs with h <;> simp [update_apply, h]
    _ = (∏'[L] x, ite (x = b) (f x) 1) * ∏'[L] x, update f b 1 x :=
      Multipliable.tprod_mul ⟨ite (b = b) (f b) 1, hasProd_single b (fun _ hb ↦ if_neg hb) L⟩ hf
    _ = ite (b = b) (f b) 1 * ∏'[L] x, update f b 1 x := by
      congr
      exact tprod_eq_mulSingle b fun b' hb' ↦ if_neg hb'
    _ = f b * ∏'[L] x, ite (x = b) 1 (f x) := by
      simp only [update, if_true, eq_rec_constant, dite_eq_ite]

@[to_additive]
protected theorem Multipliable.tprod_mul_tprod_compl {s : Set β}
    (hs : Multipliable (f ∘ (↑) : s → α)) (hsc : Multipliable (f ∘ (↑) : ↑sᶜ → α)) :
    (∏' x : s, f x) * ∏' x : ↑sᶜ, f x = ∏' x, f x :=
  (hs.hasProd.mul_compl hsc.hasProd).tprod_eq.symm

@[to_additive]
protected theorem Multipliable.tprod_union_disjoint {s t : Set β} (hd : Disjoint s t)
    (hs : Multipliable (f ∘ (↑) : s → α)) (ht : Multipliable (f ∘ (↑) : t → α)) :
    ∏' x : ↑(s ∪ t), f x = (∏' x : s, f x) * ∏' x : t, f x :=
  (hs.hasProd.mul_disjoint hd ht.hasProd).tprod_eq

@[to_additive]
protected theorem Multipliable.tprod_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι → Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, Multipliable (f ∘ (↑) : t i → α)) :
    ∏' x : ⋃ i ∈ s, t i, f x = ∏ i ∈ s, ∏' x : t i, f x :=
  (hasProd_prod_disjoint _ hd fun i hi ↦ (hf i hi).hasProd).tprod_eq

end ContinuousMul

end tprod

section CommMonoidWithZero
variable [CommMonoidWithZero α] [TopologicalSpace α] {f : β → α} {L : SummationFilter β}

lemma hasProd_zero_of_exists_eq_zero (hf : ∃ b, f b = 0) [L.LeAtTop] : HasProd f 0 L := by
  obtain ⟨b, hb⟩ := hf
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_ge_atTop {b}).filter_mono L.le_atTop] with s hs
  exact (Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) hb).symm

lemma multipliable_of_exists_eq_zero (hf : ∃ b, f b = 0) [L.LeAtTop] : Multipliable f L :=
  ⟨0, hasProd_zero_of_exists_eq_zero hf⟩

lemma tprod_of_exists_eq_zero [T2Space α] [L.NeBot] [L.LeAtTop] (hf : ∃ b, f b = 0) :
    ∏'[L] b, f b = 0 :=
  (hasProd_zero_of_exists_eq_zero hf).tprod_eq

end CommMonoidWithZero
