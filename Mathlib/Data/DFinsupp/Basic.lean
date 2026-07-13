/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.Multiset.Find

/-!
# Miscellaneous definitions, lemmas, and constructions using dfinsupp

This should be kept in sync with Finsupp where possible.

## Main definitions

* `DFinsupp.embDomain`
* `DFinsupp.mapDomain`
-/

@[expose] public section


variable {ι α β γ : Type*} {M : β → Type*} {N : Type*}

section EmbDomain
variable [∀ b, Zero (M b)] [DecidableEq β]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `DFinsupp.embDomain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def embDomain (f : α ↪ β) (v : Π₀ a, M (f a)) : Π₀ b, M b where
  toFun b :=
    let eval (s : Multiset α) :=
      match h : s.find? (fun a => f a = b) (f.injective.subsingleton_fiber _) with
      | some a => s.find?_some _ _ h ▸ v a
      | none => 0
    v.support'.lift
      (eval ·.1)
      (fun ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ => by
        let p := fun a => f a = b
        have hp : {x | p x}.Subsingleton := f.injective.subsingleton_fiber _
        dsimp only
        by_cases h : ∃ a, f a = b
        · rcases h with ⟨a, rfl⟩
          have h_eq (s) (hs : ∀ i, i ∈ s ∨ v i = 0) : eval s = v a := by
            dsimp [eval]
            by_cases ha : a ∈ s
            · have h_find : s.find? p hp = some a := by grind
              grind
            · grind
          rw [h_eq s₁ hs₁, h_eq s₂ hs₂]
        · push Not at h
          have h_eq (s) : eval s = 0 := by grind
          rw [h_eq s₁, h_eq s₂])
  support' :=
    v.support'.map <| Subtype.map (Multiset.map f) fun s_outer h i => by
      induction v.support' using Trunc.induction_on with | _ s =>
      cases s with | _ s hs =>
      simp only [Multiset.mem_map, toFun_eq_coe, Trunc.lift_mk]
      by_cases hi : ∃ a, f a = i
      · rcases hi with ⟨a, rfl⟩
        by_cases ha : a ∈ s_outer
        · exact Or.inl ⟨a, ha, rfl⟩
        · right
          have hva : v a = 0 := (h a).resolve_left ha
          grind
      · right
        grind

@[simp]
lemma embDomain_apply_self (f : α ↪ β) (v : Π₀ a, M (f a)) (a : α) :
    embDomain f v (f a) = v a := by
  dsimp [embDomain]
  induction v.support' using Trunc.induction_on with | _ s_inner
  dsimp [Trunc.lift_mk]
  cases s_inner with | _ s hs =>
  have hp : {x | f x = f a}.Subsingleton := fun _ _ hx hy => by grind
  by_cases ha : a ∈ s
  · have h_find : s.find? _ hp = some a := by grind
    grind
  · split
    · grind
    · exact (hs a).resolve_left ha |>.symm

lemma embDomain_notin_range (f : α ↪ β) (v : Π₀ a, M (f a)) {b : β} (hb : b ∉ Set.range f) :
    embDomain f v b = 0 := by
  dsimp [embDomain]
  induction v.support' using Trunc.induction_on with | _ s_inner
  dsimp [Trunc.lift_mk]
  grind

@[simp]
lemma support_embDomain [DecidableEq α] [∀ i (x : M i), Decidable (x ≠ 0)]
    (f : α ↪ β) (v : Π₀ a, M (f a)) :
    (embDomain f v).support = v.support.map f := by
  ext b
  simp only [DFinsupp.mem_support_toFun, Finset.mem_map]
  by_cases hb : b ∈ Set.range f
  · rcases hb with ⟨a, rfl⟩
    rw [embDomain_apply_self]
    grind
  · rw [embDomain_notin_range f v hb]
    grind

@[to_additive]
lemma prod_embDomain [DecidableEq α] [∀ i (x : M i), Decidable (x ≠ 0)] [CommMonoid N]
    (f : α ↪ β) (v : Π₀ a, M (f a)) (g : ∀ b, M b → N) :
    (embDomain f v).prod g = v.prod fun a m => g (f a) m := by
  rw [prod, support_embDomain, Finset.prod_map]
  exact Finset.prod_congr rfl fun a _ => congr_arg _ (embDomain_apply_self f v a)

end EmbDomain

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

/-- `DFinsupp.mapDomain` is an `AddMonoidHom`. -/
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

theorem mapDomain_support [∀ i (x : M i), Decidable (x ≠ 0)]
    {f : α → β} {s : Π₀ a, M (f a)} :
    (s.mapDomain f).support ⊆ s.support.image f := by
  rw [mapDomain_eq_sum]
  exact
  Finset.Subset.trans support_sum <|
    Finset.Subset.trans (Finset.biUnion_mono fun _ _ => support_single_subset) <| by
      rw [Finset.biUnion_singleton]

theorem mapDomain_apply' [∀ i (x : M i), Decidable (x ≠ 0)]
    (S : Set α) {f : α → β} (x : Π₀ a, M (f a)) (hS : (x.support : Set α) ⊆ S)
    (hf : Set.InjOn f S) {a : α} (ha : a ∈ S) : mapDomain f x (f a) = x a := by
  classical
    rw [mapDomain_eq_sum, sum_apply, sum]
    simp_rw [single_apply]
    by_cases hax : a ∈ x.support
    · rw [← Finset.add_sum_erase _ _ hax, dif_pos rfl]
      convert add_zero (x a)
      refine Finset.sum_eq_zero fun i hi => dif_neg ?_
      exact (hf.mono hS).ne (Finset.mem_of_mem_erase hi) hax (Finset.ne_of_mem_erase hi)
    · rw [notMem_support_iff.1 hax]
      refine Finset.sum_eq_zero fun i hi => dif_neg ?_
      exact hf.ne (hS hi) ha (ne_of_mem_of_not_mem hi hax)

open Finset

theorem mapDomain_support_of_injOn
    [∀ i (x : M i), Decidable (x ≠ 0)] {f : α → β} (s : Π₀ a, M (f a))
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

theorem mapDomain_support_of_injective
    [∀ i (x : M i), Decidable (x ≠ 0)] {f : α → β} (hf : Function.Injective f)
    (s : Π₀ a, M (f a)) : (mapDomain f s).support = Finset.image f s.support :=
  mapDomain_support_of_injOn s hf.injOn

@[to_additive]
theorem prod_mapDomain_index {N} [∀ i (x : M i), Decidable (x ≠ 0)] [CommMonoid N]
    {f : α → β} {s : Π₀ a, M (f a)} {h : (b : β) → M b → N}
    (h_zero : ∀ b, h b 0 = 1) (h_add : ∀ b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) :
    (mapDomain f s).prod h = s.prod fun a m => h (f a) m := by
  rw [mapDomain_eq_sum, prod_sum_index h_zero h_add]
  exact prod_congr _ _ fun _ _ => prod_single_index (h_zero _)

-- Note that in `prod_mapDomain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `MonoidHom`.
/-- A version of `sum_mapDomain_index` that takes a bundled `AddMonoidHom`,
rather than separate linearity hypotheses.
-/
@[simp]
theorem sum_mapDomain_index_addMonoidHom
    [∀ i (x : M i), Decidable (x ≠ 0)] {f : α → β} {s : Π₀ a, M (f a)}
    (h : (b : β) → M b →+ N) :
    ((mapDomain f s).sum fun b m => h b m) = s.sum fun a m => h (f a) m :=
  sum_mapDomain_index (fun b => (h b).map_zero) (fun b _ _ => (h b).map_add _ _)

theorem embDomain_eq_mapDomain (f : α ↪ β) (v : Π₀ a, M (f a)) : embDomain f v = mapDomain f v := by
  ext a
  by_cases h : a ∈ Set.range f
  · rcases h with ⟨a, rfl⟩
    rw [mapDomain_apply f.injective, embDomain_apply_self]
  · rw [mapDomain_notin_range, embDomain_notin_range] <;> assumption

@[to_additive]
theorem prod_mapDomain_index_inj {N}
    [∀ i (x : M i), Decidable (x ≠ 0)] [CommMonoid N]
    {f : α → β} {s : Π₀ a, M (f a)} {h : (b : β) → M b → N} (hf : Function.Injective f) :
    (s.mapDomain f).prod h = s.prod fun a b => h (f a) b := by
  lift f to α ↪ β using hf
  rw [← embDomain_eq_mapDomain, prod_embDomain]

theorem mapDomain_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (Π₀ a, M (f a)) → (Π₀ b, M b)) := by
  intro v₁ v₂ eq
  ext a
  have : mapDomain f v₁ (f a) = mapDomain f v₂ (f a) := by rw [eq]
  rwa [mapDomain_apply hf, mapDomain_apply hf] at this

open Function

theorem mapDomain_rightInverse {f : α → β} {g : β → α} (hf : RightInverse g f) :
    RightInverse
      (mapDomain g ∘ mapRange (fun b x => hf b |>.symm ▸ x) (by grind))
      (mapDomain (M := M) f) := by
  intro x
  have mapDomain_congr {F : β → β} (hF : F = id) (v : Π₀ b, M (F b)) :
      mapDomain F v =
        mapDomain id
          (mapRange (fun b x => (show F b = b from congrFun hF b) ▸ x) (by grind) v) := by
    cases hF
    congr
    erw [mapRange_id]
  rw [Function.comp_apply, ← mapDomain_comp]
  rw [mapDomain_congr hf.id, mapDomain_id]
  convert mapRange_comp _ _ _ _ _ x |>.symm
  · simp only [Function.comp_def]
    convert mapRange_id _ _ |>.symm <;> grind
  · grind

theorem mapDomain_surjective {f : α → β} (hf : f.Surjective) :
    (mapDomain (M := M) f).Surjective := by
  obtain ⟨g, hf⟩ := hf.hasRightInverse
  exact mapDomain_rightInverse hf |>.surjective

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ) ↪ (β →₀ ℕ)` given by `mapDomain`. -/
@[simps]
def mapDomainEmbedding (f : α ↪ β) : (Π₀ a, M (f a)) ↪ (Π₀ b, M b) :=
  ⟨DFinsupp.mapDomain f, DFinsupp.mapDomain_injective f.injective⟩

section
variable {Nb : β → Type*} [∀ b, AddCommMonoid (Nb b)]

theorem mapDomain.addMonoidHom_comp_mapRange (f : α → β) (g : ∀ b, M b →+ Nb b) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom (fun _ => g _)) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) := by
  ext
  simp

/-- When `g` preserves addition, `mapRange` and `mapDomain` commute. -/
theorem mapDomain_mapRange
    (f : α → β) (v : Π₀ a, M (f a)) (g : ∀ b, M b → Nb b) (h0 : ∀ b, g b 0 = 0)
    (hadd : ∀ b x y, g b (x + y) = g b x + g b y) :
    mapDomain f (mapRange (fun _ => g _) (fun _ => h0 _) v) = mapRange g h0 (mapDomain f v) :=
  let g' (b) : M b →+ Nb b :=
    { toFun := g b
      map_zero' := h0 b
      map_add' := hadd b }
  DFunLike.congr_fun (mapDomain.addMonoidHom_comp_mapRange f g') v

end

theorem mapDomain_injOn [∀ i (x : M i), Decidable (x ≠ 0)]
    (S : Set α) {f : α → β} (hf : Set.InjOn f S) :
    Set.InjOn (mapDomain f : (Π₀ a, M (f a)) → (Π₀ b, M b)) { w | (w.support : Set α) ⊆ S } := by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  classical
    by_cases h : a ∈ v₁.support ∪ v₂.support
    · rw [← mapDomain_apply' S _ hv₁ hf _, ← mapDomain_apply' S _ hv₂ hf _, eq] <;>
        · apply Set.union_subset hv₁ hv₂
          exact mod_cast h
    · simp_all

theorem equivCongrLeft_symm_eq_mapDomain (f : β ≃ α) (l : Π₀ a, M (f.symm a)) :
    (DFinsupp.equivCongrLeft f).symm l = mapDomain f.symm l := by
  ext x
  simp [equivCongrLeft]
  grind

end MapDomain

end DFinsupp
