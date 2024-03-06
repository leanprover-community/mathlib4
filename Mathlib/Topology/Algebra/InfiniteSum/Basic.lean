/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.Monoid

/-!
# Lemmas on infinite sums in topological monoids

This file contains many simple lemmas on `tsum`, `HasSum` etc, which are placed here in order to
keep the basic file of definitions as short as possible.

Results requiring a group (rather than monoid) structure on the target should go in `Group.lean`.

-/

noncomputable section

open Filter Finset Function

open scoped BigOperators Topology

variable {α β γ δ : Type*}

section HasSum

variable [AddCommMonoid α] [TopologicalSpace α]

variable {f g : β → α} {a b : α} {s : Finset β}

/-- Constant zero function has sum `0` -/
theorem hasSum_zero : HasSum (fun _ ↦ 0 : β → α) 0 := by simp [HasSum, tendsto_const_nhds]
#align has_sum_zero hasSum_zero

theorem hasSum_empty [IsEmpty β] : HasSum f 0 := by
  convert @hasSum_zero α β _ _
#align has_sum_empty hasSum_empty

theorem summable_zero : Summable (fun _ ↦ 0 : β → α) :=
  hasSum_zero.summable
#align summable_zero summable_zero

theorem summable_empty [IsEmpty β] : Summable f :=
  hasSum_empty.summable
#align summable_empty summable_empty

theorem summable_congr (hfg : ∀ b, f b = g b) : Summable f ↔ Summable g :=
  iff_of_eq (congr_arg Summable <| funext hfg)
#align summable_congr summable_congr

theorem Summable.congr (hf : Summable f) (hfg : ∀ b, f b = g b) : Summable g :=
  (summable_congr hfg).mp hf
#align summable.congr Summable.congr

theorem HasSum.hasSum_of_sum_eq {g : γ → α}
    (h_eq : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' →
      ∃ u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
    (hf : HasSum g a) : HasSum f a :=
  le_trans (map_atTop_finset_sum_le_of_sum_eq h_eq) hf
#align has_sum.has_sum_of_sum_eq HasSum.hasSum_of_sum_eq

theorem hasSum_iff_hasSum {g : γ → α}
    (h₁ : ∀ u : Finset γ, ∃ v : Finset β, ∀ v', v ⊆ v' →
      ∃ u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
    (h₂ : ∀ v : Finset β, ∃ u : Finset γ, ∀ u', u ⊆ u' →
      ∃ v', v ⊆ v' ∧ ∑ b in v', f b = ∑ x in u', g x) :
    HasSum f a ↔ HasSum g a :=
  ⟨HasSum.hasSum_of_sum_eq h₂, HasSum.hasSum_of_sum_eq h₁⟩
#align has_sum_iff_has_sum hasSum_iff_hasSum

theorem Function.Injective.summable_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x ∉ Set.range g, f x = 0) : Summable (f ∘ g) ↔ Summable f :=
  exists_congr fun _ ↦ hg.hasSum_iff hf
#align function.injective.summable_iff Function.Injective.summable_iff

@[simp] theorem hasSum_extend_zero {g : β → γ} (hg : Injective g) :
    HasSum (extend g f 0) a ↔ HasSum f a := by
  rw [← hg.hasSum_iff, extend_comp hg]
  exact extend_apply' _ _

@[simp] theorem summable_extend_zero {g : β → γ} (hg : Injective g) :
    Summable (extend g f 0) ↔ Summable f :=
  exists_congr fun _ ↦ hasSum_extend_zero hg

theorem hasSum_subtype_iff_indicator {s : Set β} :
    HasSum (f ∘ (↑) : s → α) a ↔ HasSum (s.indicator f) a := by
  rw [← Set.indicator_range_comp, Subtype.range_coe,
    hasSum_subtype_iff_of_support_subset Set.support_indicator_subset]
#align has_sum_subtype_iff_indicator hasSum_subtype_iff_indicator

theorem summable_subtype_iff_indicator {s : Set β} :
    Summable (f ∘ (↑) : s → α) ↔ Summable (s.indicator f) :=
  exists_congr fun _ ↦ hasSum_subtype_iff_indicator
#align summable_subtype_iff_indicator summable_subtype_iff_indicator

@[simp]
theorem hasSum_subtype_support : HasSum (f ∘ (↑) : support f → α) a ↔ HasSum f a :=
  hasSum_subtype_iff_of_support_subset <| Set.Subset.refl _
#align has_sum_subtype_support hasSum_subtype_support

protected theorem Finset.summable (s : Finset β) (f : β → α) :
    Summable (f ∘ (↑) : (↑s : Set β) → α) :=
  (s.hasSum f).summable
#align finset.summable Finset.summable

protected theorem Set.Finite.summable {s : Set β} (hs : s.Finite) (f : β → α) :
    Summable (f ∘ (↑) : s → α) := by
  have := hs.toFinset.summable f
  rwa [hs.coe_toFinset] at this
#align set.finite.summable Set.Finite.summable

theorem summable_of_finite_support (h : (support f).Finite) : Summable f := by
  apply summable_of_ne_finset_zero (s := h.toFinset); simp

theorem hasSum_single {f : β → α} (b : β) (hf : ∀ (b') (_ : b' ≠ b), f b' = 0) : HasSum f (f b) :=
  suffices HasSum f (∑ b' in {b}, f b') by simpa using this
  hasSum_sum_of_ne_finset_zero <| by simpa [hf]
#align has_sum_single hasSum_single

@[simp] lemma hasSum_unique [Unique β] (f : β → α) : HasSum f (f default) :=
  hasSum_single default (fun _ hb ↦ False.elim <| hb <| Unique.uniq ..)

@[simp] lemma hasSum_singleton (m : β) (f : β → α) : HasSum (({m} : Set β).restrict f) (f m) :=
  hasSum_unique (Set.restrict {m} f)

theorem hasSum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    HasSum (fun b' ↦ if b' = b then a else 0) a := by
  convert @hasSum_single _ _ _ _ (fun b' ↦ if b' = b then a else 0) b (fun b' hb' ↦ if_neg hb')
  exact (if_pos rfl).symm
#align has_sum_ite_eq hasSum_ite_eq

theorem Equiv.hasSum_iff (e : γ ≃ β) : HasSum (f ∘ e) a ↔ HasSum f a :=
  e.injective.hasSum_iff <| by simp
#align equiv.has_sum_iff Equiv.hasSum_iff

theorem Function.Injective.hasSum_range_iff {g : γ → β} (hg : Injective g) :
    HasSum (fun x : Set.range g ↦ f x) a ↔ HasSum (f ∘ g) a :=
  (Equiv.ofInjective g hg).hasSum_iff.symm
#align function.injective.has_sum_range_iff Function.Injective.hasSum_range_iff

theorem Equiv.summable_iff (e : γ ≃ β) : Summable (f ∘ e) ↔ Summable f :=
  exists_congr fun _ ↦ e.hasSum_iff
#align equiv.summable_iff Equiv.summable_iff

theorem Equiv.hasSum_iff_of_support {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x : support f, g (e x) = f x) : HasSum f a ↔ HasSum g a := by
  have : (g ∘ (↑)) ∘ e = f ∘ (↑) := funext he
  rw [← hasSum_subtype_support, ← this, e.hasSum_iff, hasSum_subtype_support]
#align equiv.has_sum_iff_of_support Equiv.hasSum_iff_of_support

theorem hasSum_iff_hasSum_of_ne_zero_bij {g : γ → α} (i : support g → β)
    (hi : Injective i) (hf : support f ⊆ Set.range i)
    (hfg : ∀ x, f (i x) = g x) : HasSum f a ↔ HasSum g a :=
  Iff.symm <|
    Equiv.hasSum_iff_of_support
      (Equiv.ofBijective (fun x ↦ ⟨i x, fun hx ↦ x.coe_prop <| hfg x ▸ hx⟩)
        ⟨fun _ _ h ↦ hi <| Subtype.ext_iff.1 h, fun y ↦
          (hf y.coe_prop).imp fun _ hx ↦ Subtype.ext hx⟩)
      hfg
#align has_sum_iff_has_sum_of_ne_zero_bij hasSum_iff_hasSum_of_ne_zero_bij

theorem Equiv.summable_iff_of_support {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x : support f, g (e x) = f x) : Summable f ↔ Summable g :=
  exists_congr fun _ ↦ e.hasSum_iff_of_support he
#align equiv.summable_iff_of_support Equiv.summable_iff_of_support

protected theorem HasSum.map [AddCommMonoid γ] [TopologicalSpace γ] (hf : HasSum f a) {G}
    [FunLike G α γ] [AddMonoidHomClass G α γ] (g : G) (hg : Continuous g) :
    HasSum (g ∘ f) (g a) :=
  have : (g ∘ fun s : Finset β ↦ ∑ b in s, f b) = fun s : Finset β ↦ ∑ b in s, g (f b) :=
    funext <| map_sum g _
  show Tendsto (fun s : Finset β ↦ ∑ b in s, g (f b)) atTop (𝓝 (g a)) from
    this ▸ (hg.tendsto a).comp hf
#align has_sum.map HasSum.map

protected theorem Summable.map [AddCommMonoid γ] [TopologicalSpace γ] (hf : Summable f) {G}
    [FunLike G α γ] [AddMonoidHomClass G α γ] (g : G) (hg : Continuous g) : Summable (g ∘ f) :=
  (hf.hasSum.map g hg).summable
#align summable.map Summable.map

protected theorem Summable.map_iff_of_leftInverse [AddCommMonoid γ] [TopologicalSpace γ] {G G'}
    [FunLike G α γ] [AddMonoidHomClass G α γ] [FunLike G' γ α] [AddMonoidHomClass G' γ α]
    (g : G) (g' : G') (hg : Continuous g)
    (hg' : Continuous g') (hinv : Function.LeftInverse g' g) : Summable (g ∘ f) ↔ Summable f :=
  ⟨fun h ↦ by
    have := h.map _ hg'
    rwa [← Function.comp.assoc, hinv.id] at this, fun h ↦ h.map _ hg⟩
#align summable.map_iff_of_left_inverse Summable.map_iff_of_leftInverse

/-- A special case of `Summable.map_iff_of_leftInverse` for convenience -/
protected theorem Summable.map_iff_of_equiv [AddCommMonoid γ] [TopologicalSpace γ] {G}
    [EquivLike G α γ] [AddEquivClass G α γ] (g : G) (hg : Continuous g)
    (hg' : Continuous (EquivLike.inv g : γ → α)) : Summable (g ∘ f) ↔ Summable f :=
  Summable.map_iff_of_leftInverse g (g : α ≃+ γ).symm hg hg' (EquivLike.left_inv g)
#align summable.map_iff_of_equiv Summable.map_iff_of_equiv

theorem Function.Surjective.summable_iff_of_hasSum_iff {α' : Type*} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) {f : β → α} {g : γ → α'}
    (he : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : Summable f ↔ Summable g :=
  hes.exists.trans <| exists_congr <| @he
#align function.surjective.summable_iff_of_has_sum_iff Function.Surjective.summable_iff_of_hasSum_iff

variable [ContinuousAdd α]

theorem HasSum.add (hf : HasSum f a) (hg : HasSum g b) : HasSum (fun b ↦ f b + g b) (a + b) := by
  dsimp only [HasSum] at hf hg ⊢
  simp_rw [sum_add_distrib]
  exact hf.add hg
#align has_sum.add HasSum.add

theorem Summable.add (hf : Summable f) (hg : Summable g) : Summable fun b ↦ f b + g b :=
  (hf.hasSum.add hg.hasSum).summable
#align summable.add Summable.add

theorem hasSum_sum {f : γ → β → α} {a : γ → α} {s : Finset γ} :
    (∀ i ∈ s, HasSum (f i) (a i)) → HasSum (fun b ↦ ∑ i in s, f i b) (∑ i in s, a i) := by
  classical
  exact Finset.induction_on s (by simp only [hasSum_zero, sum_empty, forall_true_iff]) <| by
    -- Porting note: with some help, `simp` used to be able to close the goal
    simp (config := { contextual := true }) only [mem_insert, forall_eq_or_imp, not_false_iff,
      sum_insert, and_imp]
    exact fun x s _ IH hx h ↦ hx.add (IH h)
#align has_sum_sum hasSum_sum

theorem summable_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    Summable fun b ↦ ∑ i in s, f i b :=
  (hasSum_sum fun i hi ↦ (hf i hi).hasSum).summable
#align summable_sum summable_sum

theorem HasSum.add_disjoint {s t : Set β} (hs : Disjoint s t) (ha : HasSum (f ∘ (↑) : s → α) a)
    (hb : HasSum (f ∘ (↑) : t → α) b) : HasSum (f ∘ (↑) : (s ∪ t : Set β) → α) (a + b) := by
  rw [hasSum_subtype_iff_indicator] at *
  rw [Set.indicator_union_of_disjoint hs]
  exact ha.add hb
#align has_sum.add_disjoint HasSum.add_disjoint

theorem hasSum_sum_disjoint {ι} (s : Finset ι) {t : ι → Set β} {a : ι → α}
    (hs : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, HasSum (f ∘ (↑) : t i → α) (a i)) :
    HasSum (f ∘ (↑) : (⋃ i ∈ s, t i) → α) (∑ i in s, a i) := by
  simp_rw [hasSum_subtype_iff_indicator] at *
  rw [Finset.indicator_biUnion _ _ hs]
  exact hasSum_sum hf
#align has_sum_sum_disjoint hasSum_sum_disjoint

theorem HasSum.add_isCompl {s t : Set β} (hs : IsCompl s t) (ha : HasSum (f ∘ (↑) : s → α) a)
    (hb : HasSum (f ∘ (↑) : t → α) b) : HasSum f (a + b) := by
  simpa [← hs.compl_eq] using
    (hasSum_subtype_iff_indicator.1 ha).add (hasSum_subtype_iff_indicator.1 hb)
#align has_sum.add_is_compl HasSum.add_isCompl

theorem HasSum.add_compl {s : Set β} (ha : HasSum (f ∘ (↑) : s → α) a)
    (hb : HasSum (f ∘ (↑) : (sᶜ : Set β) → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl hb
#align has_sum.add_compl HasSum.add_compl

theorem Summable.add_compl {s : Set β} (hs : Summable (f ∘ (↑) : s → α))
    (hsc : Summable (f ∘ (↑) : (sᶜ : Set β) → α)) : Summable f :=
  (hs.hasSum.add_compl hsc.hasSum).summable
#align summable.add_compl Summable.add_compl

theorem HasSum.compl_add {s : Set β} (ha : HasSum (f ∘ (↑) : (sᶜ : Set β) → α) a)
    (hb : HasSum (f ∘ (↑) : s → α) b) : HasSum f (a + b) :=
  ha.add_isCompl isCompl_compl.symm hb
#align has_sum.compl_add HasSum.compl_add

theorem Summable.compl_add {s : Set β} (hs : Summable (f ∘ (↑) : (sᶜ : Set β) → α))
    (hsc : Summable (f ∘ (↑) : s → α)) : Summable f :=
  (hs.hasSum.compl_add hsc.hasSum).summable
#align summable.compl_add Summable.compl_add

/-- Version of `HasSum.update` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that `f.update` has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `f.update` given that both exist. -/
theorem HasSum.update' {α β : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] [DecidableEq β] {f : β → α} {a a' : α} (hf : HasSum f a) (b : β) (x : α)
    (hf' : HasSum (update f b x) a') : a + x = a' + f b := by
  have : ∀ b', f b' + ite (b' = b) x 0 = update f b x b' + ite (b' = b) (f b) 0 := by
    intro b'
    split_ifs with hb'
    · simpa only [Function.update_apply, hb', eq_self_iff_true] using add_comm (f b) x
    · simp only [Function.update_apply, hb', if_false]
  have h := hf.add (hasSum_ite_eq b x)
  simp_rw [this] at h
  exact HasSum.unique h (hf'.add (hasSum_ite_eq b (f b)))
#align has_sum.update' HasSum.update'

/-- Version of `hasSum_ite_sub_hasSum` for `AddCommMonoid` rather than `AddCommGroup`.
Rather than showing that the `ite` expression has a specific sum in terms of `HasSum`,
it gives a relationship between the sums of `f` and `ite (n = b) 0 (f n)` given that both exist. -/
theorem eq_add_of_hasSum_ite {α β : Type*} [TopologicalSpace α] [AddCommMonoid α] [T2Space α]
    [ContinuousAdd α] [DecidableEq β] {f : β → α} {a : α} (hf : HasSum f a) (b : β) (a' : α)
    (hf' : HasSum (fun n ↦ ite (n = b) 0 (f n)) a') : a = a' + f b := by
  refine' (add_zero a).symm.trans (hf.update' b 0 _)
  convert hf'
  apply update_apply
#align eq_add_of_has_sum_ite eq_add_of_hasSum_ite

end HasSum

section tsum

variable [AddCommMonoid α] [TopologicalSpace α] {f g : β → α} {a a₁ a₂ : α}

theorem tsum_congr_set_coe (f : β → α) {s t : Set β} (h : s = t) :
    ∑' x : s, f x = ∑' x : t, f x := by rw [h]
#align tsum_congr_subtype tsum_congr_set_coe

theorem tsum_congr_subtype (f : β → α) {P Q : β → Prop} (h : ∀ x, P x ↔ Q x):
    ∑' x : {x // P x}, f x = ∑' x : {x // Q x}, f x :=
  tsum_congr_set_coe f <| Set.ext h

theorem tsum_eq_finsum (hf : (support f).Finite) :
    ∑' b, f b = ∑ᶠ b, f b := by simp [tsum_def, summable_of_finite_support hf, hf]

theorem tsum_eq_sum' {s : Finset β} (hf : support f ⊆ s) :
    ∑' b, f b = ∑ b in s, f b := by
  rw [tsum_eq_finsum (s.finite_toSet.subset hf), finsum_eq_sum_of_support_subset _ hf]

theorem tsum_eq_sum {s : Finset β} (hf : ∀ b ∉ s, f b = 0) :
    ∑' b, f b = ∑ b in s, f b :=
  tsum_eq_sum' <| support_subset_iff'.2 hf
#align tsum_eq_sum tsum_eq_sum

@[simp]
theorem tsum_zero : ∑' _ : β, (0 : α) = 0 := by rw [tsum_eq_finsum] <;> simp
#align tsum_zero tsum_zero
#align tsum_zero' tsum_zero

@[simp]
theorem tsum_empty [IsEmpty β] : ∑' b, f b = 0 := by
  rw [tsum_eq_sum (s := (∅ : Finset β))] <;> simp
#align tsum_empty tsum_empty

theorem tsum_congr {f g : β → α}
    (hfg : ∀ b, f b = g b) : ∑' b, f b = ∑' b, g b :=
  congr_arg tsum (funext hfg)
#align tsum_congr tsum_congr

theorem tsum_fintype [Fintype β] (f : β → α) : ∑' b, f b = ∑ b, f b := by
  apply tsum_eq_sum; simp
#align tsum_fintype tsum_fintype

theorem sum_eq_tsum_indicator (f : β → α) (s : Finset β) :
    ∑ x in s, f x = ∑' x, Set.indicator (↑s) f x := by
  rw [tsum_eq_sum' (Set.support_indicator_subset), Finset.sum_indicator_subset _ Finset.Subset.rfl]
#align sum_eq_tsum_indicator sum_eq_tsum_indicator

theorem tsum_bool (f : Bool → α) : ∑' i : Bool, f i = f false + f true := by
  rw [tsum_fintype, Fintype.sum_bool, add_comm]
#align tsum_bool tsum_bool

theorem tsum_eq_single {f : β → α} (b : β) (hf : ∀ b' ≠ b, f b' = 0) :
    ∑' b, f b = f b := by
  rw [tsum_eq_sum (s := {b}), sum_singleton]
  exact fun b' hb' ↦ hf b' (by simpa using hb')
#align tsum_eq_single tsum_eq_single

theorem tsum_tsum_eq_single (f : β → γ → α) (b : β) (c : γ) (hfb : ∀ b' ≠ b, f b' c = 0)
    (hfc : ∀ b', ∀ c' ≠ c, f b' c' = 0) : ∑' (b') (c'), f b' c' = f b c :=
  calc
    ∑' (b') (c'), f b' c' = ∑' b', f b' c := tsum_congr fun b' ↦ tsum_eq_single _ (hfc b')
    _ = f b c := tsum_eq_single _ hfb
#align tsum_tsum_eq_single tsum_tsum_eq_single

@[simp]
theorem tsum_ite_eq (b : β) [DecidablePred (· = b)] (a : α) :
    ∑' b', (if b' = b then a else 0) = a := by
  rw [tsum_eq_single b]
  · simp
  · intro b' hb'; simp [hb']
#align tsum_ite_eq tsum_ite_eq

-- Porting note: Added nolint simpNF, simpNF falsely claims that lhs does not simplify under simp
@[simp, nolint simpNF]
theorem Finset.tsum_subtype (s : Finset β) (f : β → α) :
    ∑' x : { x // x ∈ s }, f x = ∑ x in s, f x := by
  rw [← sum_attach]; exact tsum_fintype _
#align finset.tsum_subtype Finset.tsum_subtype

theorem Finset.tsum_subtype' (s : Finset β) (f : β → α) :
    ∑' x : (s : Set β), f x = ∑ x in s, f x := by simp
#align finset.tsum_subtype' Finset.tsum_subtype'

-- Porting note: Added nolint simpNF, simpNF falsely claims that lhs does not simplify under simp
@[simp, nolint simpNF]
theorem tsum_singleton (b : β) (f : β → α) : ∑' x : ({b} : Set β), f x = f b := by
  rw [← coe_singleton, Finset.tsum_subtype', sum_singleton]
#align tsum_singleton tsum_singleton

open Classical in
theorem Function.Injective.tsum_eq {g : γ → β} (hg : Injective g) {f : β → α}
    (hf : support f ⊆ Set.range g) : ∑' c, f (g c) = ∑' b, f b := by
  have : support f = g '' support (f ∘ g) := by
    rw [support_comp_eq_preimage, Set.image_preimage_eq_iff.2 hf]
  rw [← Function.comp_def]
  by_cases hf_fin : (support f).Finite
  · have hfg_fin : (support (f ∘ g)).Finite := hf_fin.preimage (hg.injOn _)
    lift g to γ ↪ β using hg
    simp_rw [tsum_eq_sum' hf_fin.coe_toFinset.ge, tsum_eq_sum' hfg_fin.coe_toFinset.ge,
      comp_apply, ← Finset.sum_map]
    refine Finset.sum_congr (Finset.coe_injective ?_) fun _ _ ↦ rfl
    simp [this]
  · have hf_fin' : ¬ Set.Finite (support (f ∘ g)) := by
      rwa [this, Set.finite_image_iff (hg.injOn _)] at hf_fin
    simp_rw [tsum_def, if_neg hf_fin, if_neg hf_fin', Summable,
      hg.hasSum_iff (support_subset_iff'.1 hf)]

theorem Equiv.tsum_eq (e : γ ≃ β) (f : β → α) : ∑' c, f (e c) = ∑' b, f b :=
  e.injective.tsum_eq <| by simp
#align equiv.tsum_eq Equiv.tsum_eq

/-! ### `tsum` on subsets - part 1 -/

theorem tsum_subtype_eq_of_support_subset {f : β → α} {s : Set β} (hs : support f ⊆ s) :
    ∑' x : s, f x = ∑' x, f x :=
  Subtype.val_injective.tsum_eq <| by simpa
#align tsum_subtype_eq_of_support_subset tsum_subtype_eq_of_support_subset

theorem tsum_subtype_support (f : β → α) : ∑' x : support f, f x = ∑' x, f x :=
  tsum_subtype_eq_of_support_subset Set.Subset.rfl

theorem tsum_subtype (s : Set β) (f : β → α) : ∑' x : s, f x = ∑' x, s.indicator f x := by
  rw [← tsum_subtype_eq_of_support_subset Set.support_indicator_subset, tsum_congr]
  simp
#align tsum_subtype tsum_subtype

-- Porting note: Added nolint simpNF, simpNF falsely claims that lhs does not simplify under simp
@[simp, nolint simpNF]
theorem tsum_univ (f : β → α) : ∑' x : (Set.univ : Set β), f x = ∑' x, f x :=
  tsum_subtype_eq_of_support_subset <| Set.subset_univ _
#align tsum_univ tsum_univ

theorem tsum_image {g : γ → β} (f : β → α) {s : Set γ} (hg : Set.InjOn g s) :
    ∑' x : g '' s, f x = ∑' x : s, f (g x) :=
  ((Equiv.Set.imageOfInjOn _ _ hg).tsum_eq fun x ↦ f x).symm
#align tsum_image tsum_image

theorem tsum_range {g : γ → β} (f : β → α) (hg : Injective g) :
    ∑' x : Set.range g, f x = ∑' x, f (g x) := by
  rw [← Set.image_univ, tsum_image f (hg.injOn _)]
  simp_rw [← comp_apply (g := g), tsum_univ (f ∘ g)]
#align tsum_range tsum_range

/-- If `f b = 0` for all `b ∈ t`, then the sum over `f a` with `a ∈ s` is the same as the
sum over `f a` with `a ∈ s ∖ t`. -/
lemma tsum_setElem_eq_tsum_setElem_diff {f : β → α} (s t : Set β)
    (hf₀ : ∀ b ∈ t, f b = 0) :
    ∑' a : s, f a = ∑' a : (s \ t : Set β), f a :=
  .symm <| (Set.inclusion_injective (Set.diff_subset s t)).tsum_eq (f := f ∘ (↑)) <|
    support_subset_iff'.2 fun b hb ↦ hf₀ b <| by simpa using hb

/-- If `f b = 0`, then the sum over `f a` with `a ∈ s` is the same as the sum over `f a` for
`a ∈ s ∖ {b}`. -/
lemma tsum_eq_tsum_diff_singleton {f : β → α} (s : Set β) {b : β} (hf₀ : f b = 0) :
    ∑' a : s, f a = ∑' a : (s \ {b} : Set β), f a :=
  tsum_setElem_eq_tsum_setElem_diff s {b} fun _ ha ↦ ha ▸ hf₀

theorem tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : support g → β) (hi : Injective i)
    (hf : support f ⊆ Set.range i) (hfg : ∀ x, f (i x) = g x) : ∑' x, f x = ∑' y, g y := by
  rw [← tsum_subtype_support g, ← hi.tsum_eq hf]
  simp only [hfg]
#align tsum_eq_tsum_of_ne_zero_bij tsum_eq_tsum_of_ne_zero_bij

theorem Equiv.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : support f ≃ support g)
    (he : ∀ x, g (e x) = f x) : ∑' x, f x = ∑' y, g y :=
  .symm <| tsum_eq_tsum_of_ne_zero_bij _ (Subtype.val_injective.comp e.injective) (by simp) he
#align equiv.tsum_eq_tsum_of_support Equiv.tsum_eq_tsum_of_support

theorem tsum_dite_right (P : Prop) [Decidable P] (x : β → ¬P → α) :
    ∑' b : β, (if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑' b : β, x b h := by
  by_cases hP : P <;> simp [hP]
#align tsum_dite_right tsum_dite_right

theorem tsum_dite_left (P : Prop) [Decidable P] (x : β → P → α) :
    ∑' b : β, (if h : P then x b h else 0) = if h : P then ∑' b : β, x b h else 0 := by
  by_cases hP : P <;> simp [hP]
#align tsum_dite_left tsum_dite_left

@[simp]
lemma tsum_extend_zero {γ : Type*} {g : γ → β} (hg : Injective g) (f : γ → α) :
    ∑' y, extend g f 0 y = ∑' x, f x := by
  have : support (extend g f 0) ⊆ Set.range g := support_subset_iff'.2 <| extend_apply' _ _
  simp_rw [← hg.tsum_eq this, hg.extend_apply]

variable [T2Space α]

theorem Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum {α' : Type*} [AddCommMonoid α']
    [TopologicalSpace α'] {e : α' → α} (hes : Function.Surjective e) (h0 : e 0 = 0) {f : β → α}
    {g : γ → α'} (h : ∀ {a}, HasSum f (e a) ↔ HasSum g a) : ∑' b, f b = e (∑' c, g c) :=
  by_cases (fun x ↦ (h.mpr x.hasSum).tsum_eq) fun hg : ¬Summable g ↦ by
    have hf : ¬Summable f := mt (hes.summable_iff_of_hasSum_iff @h).1 hg
    simp [tsum_def, hf, hg, h0]
#align function.surjective.tsum_eq_tsum_of_has_sum_iff_has_sum Function.Surjective.tsum_eq_tsum_of_hasSum_iff_hasSum

theorem tsum_eq_tsum_of_hasSum_iff_hasSum {f : β → α} {g : γ → α}
    (h : ∀ {a}, HasSum f a ↔ HasSum g a) : ∑' b, f b = ∑' c, g c :=
  surjective_id.tsum_eq_tsum_of_hasSum_iff_hasSum rfl @h
#align tsum_eq_tsum_of_has_sum_iff_has_sum tsum_eq_tsum_of_hasSum_iff_hasSum

section ContinuousAdd

variable [ContinuousAdd α]

theorem tsum_add (hf : Summable f) (hg : Summable g) :
    ∑' b, (f b + g b) = ∑' b, f b + ∑' b, g b :=
  (hf.hasSum.add hg.hasSum).tsum_eq
#align tsum_add tsum_add

theorem tsum_sum {f : γ → β → α} {s : Finset γ} (hf : ∀ i ∈ s, Summable (f i)) :
    ∑' b, ∑ i in s, f i b = ∑ i in s, ∑' b, f i b :=
  (hasSum_sum fun i hi ↦ (hf i hi).hasSum).tsum_eq
#align tsum_sum tsum_sum

/-- Version of `tsum_eq_add_tsum_ite` for `AddCommMonoid` rather than `AddCommGroup`.
Requires a different convergence assumption involving `Function.update`. -/
theorem tsum_eq_add_tsum_ite' [DecidableEq β] {f : β → α} (b : β) (hf : Summable (update f b 0)) :
    ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
  calc
    ∑' x, f x = ∑' x, (ite (x = b) (f x) 0 + update f b 0 x) :=
      tsum_congr fun n ↦ by split_ifs with h <;> simp [update_apply, h]
    _ = ∑' x, ite (x = b) (f x) 0 + ∑' x, update f b 0 x :=
      tsum_add ⟨ite (b = b) (f b) 0, hasSum_single b fun b hb ↦ if_neg hb⟩ hf
    _ = ite (b = b) (f b) 0 + ∑' x, update f b 0 x := by
      congr
      exact tsum_eq_single b fun b' hb' ↦ if_neg hb'
    _ = f b + ∑' x, ite (x = b) 0 (f x) := by
      simp only [update, eq_self_iff_true, if_true, eq_rec_constant, dite_eq_ite]
#align tsum_eq_add_tsum_ite' tsum_eq_add_tsum_ite'

theorem tsum_add_tsum_compl {s : Set β} (hs : Summable (f ∘ (↑) : s → α))
    (hsc : Summable (f ∘ (↑) : ↑sᶜ → α)) : ∑' x : s, f x + ∑' x : ↑sᶜ, f x = ∑' x, f x :=
  (hs.hasSum.add_compl hsc.hasSum).tsum_eq.symm
#align tsum_add_tsum_compl tsum_add_tsum_compl

theorem tsum_union_disjoint {s t : Set β} (hd : Disjoint s t) (hs : Summable (f ∘ (↑) : s → α))
    (ht : Summable (f ∘ (↑) : t → α)) : ∑' x : ↑(s ∪ t), f x = ∑' x : s, f x + ∑' x : t, f x :=
  (hs.hasSum.add_disjoint hd ht.hasSum).tsum_eq
#align tsum_union_disjoint tsum_union_disjoint

theorem tsum_finset_bUnion_disjoint {ι} {s : Finset ι} {t : ι → Set β}
    (hd : (s : Set ι).Pairwise (Disjoint on t)) (hf : ∀ i ∈ s, Summable (f ∘ (↑) : t i → α)) :
    ∑' x : ⋃ i ∈ s, t i, f x = ∑ i in s, ∑' x : t i, f x :=
  (hasSum_sum_disjoint _ hd fun i hi ↦ (hf i hi).hasSum).tsum_eq
#align tsum_finset_bUnion_disjoint tsum_finset_bUnion_disjoint

end ContinuousAdd

end tsum
