/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module
public import Mathlib.Data.DFinsupp.BigOperators

/-!
# Miscellaneous definitions, lemmas, and constructions using dfinsupp

This should be kept in sync with Finsupp where possible.
-/

@[expose] public section

namespace DFinsupp

variable {ι α β γ : Type*} {M : β → Type*} {N : Type*}

section MapDomain

variable [∀ b, AddCommMonoid (M b)] [AddCommMonoid N]
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Given `f : α → β` and `v : Π₀ a, M (f a)`, `mapDomain f v : Π₀ b : β, M b`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def mapDomain (f : α → β) (v : Π₀ a : α, M (f a)) : Π₀ b : β, M b :=
  sumAddHom (fun i => singleAddHom M (f i)) v

-- sanity check; `f` can be inferred in the input
example : Π₀ _ : ℕ, ℕ :=
  mapDomain (· * 2 : ℕ → ℕ) (DFinsupp.single 0 1)

theorem mapDomain_eq_sum (f : α → β) (v : Π₀ a : α, M (f a))
    [∀ i (x : M (f i)), Decidable (x ≠ 0)] :
    v.mapDomain f = v.sum fun i x => single (f i) x := by
  classical
  exact sumAddHom_apply _ _

@[simp] theorem mapDomain_apply
    {f : α → β} (hf : Function.Injective f) (x : Π₀ a, M (f a)) (a : α) :
    mapDomain f x (f a) = x a := by
  classical
  rw [mapDomain_eq_sum, sum_apply, sum, Finset.sum_eq_single a, single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne (hf.ne hba.symm)
  · intro h
    rw [notMem_support_iff] at h
    rw [single_eq_same, h]

theorem mapDomain_notin_range {f : α → β} (x : Π₀ a, M (f a)) (a : β) (h : a ∉ Set.range f) :
    mapDomain f x a = 0 := by
  classical
  rw [mapDomain_eq_sum, sum_apply, sum]
  exact Finset.sum_eq_zero fun a' _ => single_eq_of_ne fun eq => h <| eq ▸ Set.mem_range_self _

@[simp]
theorem mapDomain_id (x : Π₀ b, M b) : mapDomain id x = x :=
  congr($(sumAddHom_singleAddHom) x)

theorem mapDomain_comp (g : α → β) (f : γ → α) (x : Π₀ c, M (g (f c))) :
    mapDomain (g ∘ f) x = mapDomain g (mapDomain f x) := by
  classical
  simp_rw [mapDomain_eq_sum]
  refine ((sum_sum_index ?_ ?_).trans ?_).symm
  · intro
    exact single_zero _
  · intro
    exact single_add _
  refine sum_congr _ _ fun _ _ => sum_single_index ?_
  exact single_zero _

@[simp]
theorem mapDomain_single {f : α → β} {a : α} {b : M (f a)} :
    mapDomain f (single a b) = single (f a) b :=
  sumAddHom_single _ _ _

@[simp]
theorem mapDomain_zero {f : α → β} : mapDomain f (0 : Π₀ a, M (f a)) = 0 :=
  map_zero _

theorem mapDomain_congr {f g : α → β} [(x : N) → Decidable (x ≠ 0)]
    (v : Π₀ _ : α, N) (h : ∀ x ∈ v.support, f x = g x) :
    v.mapDomain f = (mapDomain g v : Π₀ _ : β, N) := by
  simp_rw [mapDomain_eq_sum]
  apply sum_congr
  simp +contextual [h]

theorem mapDomain_add {f : α → β} (v₁ v₂ : Π₀ a, M (f a)) :
    mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂ :=
  map_add _ _ _

lemma mapDomain_sub {M : β → Type*} [∀ b, AddCommGroup (M b)]
    {f : α → β} (v₁ v₂ : Π₀ a, M (f a)) :
    mapDomain f (v₁ - v₂) = mapDomain f v₁ - mapDomain f v₂ :=
  map_sub _ _ _

@[simp]
theorem mapDomain_equiv_apply {f : α ≃ β} (x : Π₀ a, M (f a)) (a : β) :
    mapDomain f x a = f.apply_symm_apply a ▸ x (f.symm a) := by
  conv_lhs => rw! (castMode := .all) [← f.apply_symm_apply a]
  rw [mapDomain_apply f.injective]

/-- `Finsupp.mapDomain` is an `AddMonoidHom`. -/
def mapDomain.addMonoidHom (f : α → β) : (Π₀ a, M (f a)) →+ (Π₀ b, M b) :=
  sumAddHom fun i => singleAddHom M (f i)

@[simp]
theorem mapDomain.addMonoidHom_apply (f : α → β) (v : Π₀ a, M (f a)) :
    mapDomain.addMonoidHom f v = v.mapDomain f := rfl

@[simp]
theorem mapDomain.addMonoidHom_id : mapDomain.addMonoidHom id = AddMonoidHom.id (Π₀ b, M b) :=
  AddMonoidHom.ext fun _ => mapDomain_id _

theorem mapDomain.addMonoidHom_comp (g : α → β) (f : γ → α) :
    (mapDomain.addMonoidHom (g ∘ f) : (Π₀ b, M (g (f b))) →+ (Π₀ b, M b)) =
      (mapDomain.addMonoidHom g).comp (mapDomain.addMonoidHom f) :=
  AddMonoidHom.ext fun _ => mapDomain_comp _ _ _

theorem mapDomain_finsetSum {f : α → β} {s : Finset ι} {v : ι → Π₀ a, M (f a)} :
    mapDomain f (∑ i ∈ s, v i) = ∑ i ∈ s, mapDomain f (v i) :=
  map_sum (mapDomain.addMonoidHom f) _ _

theorem mapDomain_sum {f : α → β} {s : Π₀ _, N} {v : α → N → Π₀ a, M (f a)}
    [(x : N) → Decidable (x ≠ 0)] :
    mapDomain f (s.sum v) = s.sum fun a b => mapDomain f (v a b) :=
  map_dfinsuppSum (mapDomain.addMonoidHom f : (Π₀ a, M (f a)) →+ Π₀ b, M b) _ _

theorem mapDomain_support [(i : β) → (x : M i) → Decidable (x ≠ 0)]
    {f : α → β} {s : Π₀ a, M (f a)} :
    (s.mapDomain f).support ⊆ s.support.image f := by
  rw [mapDomain_eq_sum]
  exact
  Finset.Subset.trans support_sum <|
    Finset.Subset.trans (Finset.biUnion_mono fun _ _ => support_single_subset) <| by
      rw [Finset.biUnion_singleton]
/-
TODO: everything else


theorem mapDomain_apply' (S : Set α) {f : α → β} (x : Π₀ b, M b) (hS : (x.support : Set α) ⊆ S)
    (hf : Set.InjOn f S) {a : α} (ha : a ∈ S) : mapDomain f x (f a) = x a := by
  classical
    rw [mapDomain, sum_apply, sum]
    simp_rw [single_apply]
    by_cases hax : a ∈ x.support
    · rw [← Finset.add_sum_erase _ _ hax, if_pos rfl]
      convert add_zero (x a)
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact (hf.mono hS).ne (Finset.mem_of_mem_erase hi) hax (Finset.ne_of_mem_erase hi)
    · rw [notMem_support_iff.1 hax]
      refine Finset.sum_eq_zero fun i hi => if_neg ?_
      exact hf.ne (hS hi) ha (ne_of_mem_of_not_mem hi hax)

theorem mapDomain_support_of_injOn [DecidableEq β] {f : α → β} (s : Π₀ b, M b)
    (hf : Set.InjOn f s.support) : (mapDomain f s).support = Finset.image f s.support :=
  Finset.Subset.antisymm mapDomain_support <| by
    intro x hx
    simp only [mem_image, mem_support_iff, Ne] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [mem_support_iff, Ne]
    rw [mapDomain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
    · simp_rw [mem_coe, mem_support_iff, Ne]
      exact hx_h_left
    · exact Subset.refl _

theorem mapDomain_support_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (s : Π₀ b, M b) : (mapDomain f s).support = Finset.image f s.support :=
  mapDomain_support_of_injOn s hf.injOn

@[to_additive]
theorem prod_mapDomain_index [CommMonoid N] {f : α → β} {s : Π₀ b, M b} {h : β → M → N}
    (h_zero : ∀ b, h b 0 = 1) (h_add : ∀ b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
    (mapDomain f s).prod h = s.prod fun a m => h (f a) m :=
  (prod_sum_index h_zero h_add).trans <| prod_congr fun _ _ => prod_single_index (h_zero _)

-- Note that in `prod_mapDomain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `MonoidHom`.
/-- A version of `sum_mapDomain_index` that takes a bundled `AddMonoidHom`,
rather than separate linearity hypotheses.
-/
@[simp]
theorem sum_mapDomain_index_addMonoidHom [AddCommMonoid N] {f : α → β} {s : Π₀ b, M b}
    (h : β → M →+ N) : ((mapDomain f s).sum fun b m => h b m) = s.sum fun a m => h (f a) m :=
  sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)

theorem embDomain_eq_mapDomain (f : α ↪ β) (v : Π₀ b, M b) : embDomain f v = mapDomain f v := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective, embDomain_apply_self]
  · rw [mapDomain_notin_range, embDomain_notin_range] <;> assumption

@[to_additive]
theorem prod_mapDomain_index_inj [CommMonoid N] {f : α → β} {s : Π₀ b, M b} {h : β → M → N}
    (hf : Function.Injective f) : (s.mapDomain f).prod h = s.prod fun a b => h (f a) b := by
  rw [← Function.Embedding.coeFn_mk f hf, ← embDomain_eq_mapDomain, prod_embDomain]

theorem mapDomain_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (α →₀ M) → β →₀ M) := by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this

theorem mapDomain_surjective {f : α → β} (hf : f.Surjective) :
    (mapDomain (M := M) f).Surjective := by
  intro x
  use mapDomain (surjInv hf) x
  rw [← mapDomain_comp, (rightInverse_surjInv hf).id, mapDomain_id]

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ) ↪ (β →₀ ℕ)` given by `mapDomain`. -/
@[simps]
def mapDomainEmbedding {α β : Type*} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
  ⟨Finsupp.mapDomain f, Finsupp.mapDomain_injective f.injective⟩

theorem mapDomain.addMonoidHom_comp_mapRange [AddCommMonoid N] (f : α → β) (g : M →+ N) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom g) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) := by
  ext
  simp

/-- When `g` preserves addition, `mapRange` and `mapDomain` commute. -/
theorem mapDomain_mapRange [AddCommMonoid N] (f : α → β) (v : Π₀ b, M b) (g : M → N) (h0 : g 0 = 0)
    (hadd : ∀ x y, g (x + y) = g x + g y) :
    mapDomain f (mapRange g h0 v) = mapRange g h0 (mapDomain f v) :=
  let g' : M →+ N :=
    { toFun := g
      map_zero' := h0
      map_add' := hadd }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v

theorem sum_update_add [AddZeroClass α] [AddCommMonoid β] (f : ι →₀ α) (i : ι) (a : α)
    (g : ι → α → β) (hg : ∀ i, g i 0 = 0)
    (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
    (f.update i a).sum g + g i (f i) = f.sum g + g i a := by
  rw [update_eq_erase_add_single, sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assoc, add_assoc]
  congr 1
  rw [add_comm, sum_single_index (hg _), sum_single_index (hg _)]

theorem mapDomain_injOn (S : Set α) {f : α → β} (hf : Set.InjOn f S) :
    Set.InjOn (mapDomain f : (α →₀ M) → β →₀ M) { w | (w.support : Set α) ⊆ S } := by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  classical
    by_cases h : a ∈ v₁.support ∪ v₂.support
    · rw [← mapDomain_apply' S _ hv₁ hf _, ← mapDomain_apply' S _ hv₂ hf _, eq] <;>
        · apply Set.union_subset hv₁ hv₂
          exact mod_cast h
    · simp_all

theorem equivMapDomain_eq_mapDomain {M} [AddCommMonoid M] (f : α ≃ β) (l : Π₀ b, M b) :
    equivMapDomain f l = mapDomain f l := by ext x; simp
-/
end MapDomain

end DFinsupp
