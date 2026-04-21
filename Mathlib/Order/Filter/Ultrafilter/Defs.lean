/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Map
public import Mathlib.Order.ZornAtoms

/-!
# Ultrafilters

An ultrafilter is a minimal (maximal in the set order) proper filter.
In this file we define

* `Ultrafilter.of`: an ultrafilter that is less than or equal to a given filter;
* `Ultrafilter`: subtype of ultrafilters;
* `pure x : Ultrafilter α`: `pure x` as an `Ultrafilter`;
* `Ultrafilter.map`, `Ultrafilter.bind`, `Ultrafilter.comap` : operations on ultrafilters;
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists Set.Finite

universe u v

variable {α : Type u} {β : Type v} {γ : Type*}

open Set Filter Function

/-- `Filter α` is an atomic type: for every filter there exists an ultrafilter that is less than or
equal to this filter. -/
instance : IsAtomic (Filter α) :=
  IsAtomic.of_isChain_bounded fun c hc hne hb =>
    ⟨sInf c, (sInf_neBot_of_directed' hne (show IsChain (· ≥ ·) c from hc.symm).directedOn hb).ne,
      fun _ hx => sInf_le hx⟩

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
structure Ultrafilter (α : Type*) extends Filter α where
  /-- An ultrafilter is nontrivial. -/
  protected neBot' : NeBot toFilter
  /-- If `g` is a nontrivial filter that is less than or equal to an ultrafilter, then it is greater
  than or equal to the ultrafilter. -/
  protected le_of_le : ∀ g, Filter.NeBot g → g ≤ toFilter → toFilter ≤ g

namespace Ultrafilter

variable {f g : Ultrafilter α} {s t : Set α} {p q : α → Prop}

attribute [coe] Ultrafilter.toFilter

instance : CoeTC (Ultrafilter α) (Filter α) :=
  ⟨Ultrafilter.toFilter⟩

instance : Membership (Set α) (Ultrafilter α) :=
  ⟨fun f s => s ∈ (f : Filter α)⟩

theorem unique (f : Ultrafilter α) {g : Filter α} (h : g ≤ f) (hne : NeBot g := by infer_instance) :
    g = f :=
  le_antisymm h <| f.le_of_le g hne h

instance neBot (f : Ultrafilter α) : NeBot (f : Filter α) :=
  f.neBot'

protected theorem isAtom (f : Ultrafilter α) : IsAtom (f : Filter α) :=
  ⟨f.neBot.ne, fun _ hgf => by_contra fun hg => hgf.ne <| f.unique hgf.le ⟨hg⟩⟩

@[simp, norm_cast]
theorem mem_coe : s ∈ (f : Filter α) ↔ s ∈ f :=
  Iff.rfl

theorem coe_injective : Injective ((↑) : Ultrafilter α → Filter α)
  | ⟨f, h₁, h₂⟩, ⟨g, _, _⟩, _ => by congr

theorem eq_of_le {f g : Ultrafilter α} (h : (f : Filter α) ≤ g) : f = g :=
  coe_injective (g.unique h)

@[simp, norm_cast]
theorem coe_le_coe {f g : Ultrafilter α} : (f : Filter α) ≤ g ↔ f = g :=
  ⟨fun h => eq_of_le h, fun h => h ▸ le_rfl⟩

@[simp, norm_cast]
theorem coe_inj : (f : Filter α) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext ⦃f g : Ultrafilter α⦄ (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g :=
  coe_injective <| Filter.ext h

theorem le_of_inf_neBot (f : Ultrafilter α) {g : Filter α} (hg : NeBot (↑f ⊓ g)) : ↑f ≤ g :=
  le_of_inf_eq (f.unique inf_le_left hg)

theorem le_of_inf_neBot' (f : Ultrafilter α) {g : Filter α} (hg : NeBot (g ⊓ f)) : ↑f ≤ g :=
  f.le_of_inf_neBot <| by rwa [inf_comm]

theorem inf_neBot_iff {f : Ultrafilter α} {g : Filter α} : NeBot (↑f ⊓ g) ↔ ↑f ≤ g :=
  ⟨le_of_inf_neBot f, fun h => (inf_of_le_left h).symm ▸ f.neBot⟩

theorem disjoint_iff_not_le {f : Ultrafilter α} {g : Filter α} : Disjoint (↑f) g ↔ ¬↑f ≤ g := by
  rw [← inf_neBot_iff, neBot_iff, Ne, not_not, disjoint_iff]

@[simp]
theorem compl_notMem_iff : sᶜ ∉ f ↔ s ∈ f :=
  ⟨fun hsc =>
    le_principal_iff.1 <|
      f.le_of_inf_neBot ⟨fun h => hsc <| mem_of_eq_bot <| by rwa [compl_compl]⟩,
    compl_notMem⟩

@[simp]
theorem frequently_iff_eventually : (∃ᶠ x in f, p x) ↔ ∀ᶠ x in f, p x :=
  compl_notMem_iff

alias ⟨_root_.Filter.Frequently.eventually, _⟩ := frequently_iff_eventually

theorem compl_mem_iff_notMem : sᶜ ∈ f ↔ s ∉ f := by rw [← compl_notMem_iff, compl_compl]

theorem diff_mem_iff (f : Ultrafilter α) : s \ t ∈ f ↔ s ∈ f ∧ t ∉ f :=
  inter_mem_iff.trans <| and_congr Iff.rfl compl_mem_iff_notMem

/-- If `sᶜ ∉ f ↔ s ∈ f`, then `f` is an ultrafilter. The other implication is given by
`Ultrafilter.compl_notMem_iff`. -/
def ofComplNotMemIff (f : Filter α) (h : ∀ s, sᶜ ∉ f ↔ s ∈ f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨fun hf => by simp [hf] at h⟩
  le_of_le _ _ hgf s hs := (h s).1 fun hsc => compl_notMem hs (hgf hsc)

/-- If `f : Filter α` is an atom, then it is an ultrafilter. -/
def ofAtom (f : Filter α) (hf : IsAtom f) : Ultrafilter α where
  toFilter := f
  neBot' := ⟨hf.1⟩
  le_of_le g hg := (isAtom_iff_le_of_ge.1 hf).2 g hg.ne

theorem nonempty_of_mem (hs : s ∈ f) : s.Nonempty :=
  Filter.nonempty_of_mem hs

theorem ne_empty_of_mem (hs : s ∈ f) : s ≠ ∅ :=
  (nonempty_of_mem hs).ne_empty

@[simp]
theorem empty_notMem : ∅ ∉ f :=
  Filter.empty_notMem (f : Filter α)

@[simp]
theorem le_sup_iff {u : Ultrafilter α} {f g : Filter α} : ↑u ≤ f ⊔ g ↔ ↑u ≤ f ∨ ↑u ≤ g :=
  not_iff_not.1 <| by simp only [← disjoint_iff_not_le, not_or, disjoint_sup_right]

@[simp]
theorem union_mem_iff : s ∪ t ∈ f ↔ s ∈ f ∨ t ∈ f := by
  simp only [← mem_coe, ← le_principal_iff, ← sup_principal, le_sup_iff]

theorem mem_or_compl_mem (f : Ultrafilter α) (s : Set α) : s ∈ f ∨ sᶜ ∈ f :=
  or_iff_not_imp_left.2 compl_mem_iff_notMem.2

protected theorem em (f : Ultrafilter α) (p : α → Prop) : (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, ¬p x :=
  f.mem_or_compl_mem { x | p x }

theorem eventually_or : (∀ᶠ x in f, p x ∨ q x) ↔ (∀ᶠ x in f, p x) ∨ ∀ᶠ x in f, q x :=
  union_mem_iff

@[push ← high] -- higher priority than `Filter.not_eventually`
theorem eventually_not : (∀ᶠ x in f, ¬p x) ↔ ¬∀ᶠ x in f, p x :=
  compl_mem_iff_notMem

theorem eventually_imp : (∀ᶠ x in f, p x → q x) ↔ (∀ᶠ x in f, p x) → ∀ᶠ x in f, q x := by
  simp only [imp_iff_not_or, eventually_or, eventually_not]

/-- Pushforward for ultrafilters. -/
nonrec def map (m : α → β) (f : Ultrafilter α) : Ultrafilter β :=
  ofComplNotMemIff (map m f) fun s => @compl_notMem_iff _ f (m ⁻¹' s)

@[simp, norm_cast]
theorem coe_map (m : α → β) (f : Ultrafilter α) : (map m f : Filter β) = Filter.map m ↑f :=
  rfl

@[simp]
theorem mem_map {m : α → β} {f : Ultrafilter α} {s : Set β} : s ∈ map m f ↔ m ⁻¹' s ∈ f :=
  Iff.rfl

@[simp]
nonrec theorem map_id (f : Ultrafilter α) : f.map id = f :=
  coe_injective map_id

@[simp]
theorem map_id' (f : Ultrafilter α) : (f.map fun x => x) = f :=
  map_id _

@[simp]
nonrec theorem map_map (f : Ultrafilter α) (m : α → β) (n : β → γ) :
    (f.map m).map n = f.map (n ∘ m) :=
  coe_injective map_map

/-- The pullback of an ultrafilter along an injection whose range is large with respect to the given
ultrafilter. -/
nonrec def comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) :
    Ultrafilter α where
  toFilter := comap m u
  neBot' := u.neBot'.comap_of_range_mem large
  le_of_le g hg hgu := by
    simp only [← u.unique (map_le_iff_le_comap.2 hgu), comap_map inj, le_rfl]

@[simp]
theorem mem_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u)
    {s : Set α} : s ∈ u.comap inj large ↔ m '' s ∈ u :=
  mem_comap_iff inj large

@[simp, norm_cast]
theorem coe_comap {m : α → β} (u : Ultrafilter β) (inj : Injective m) (large : Set.range m ∈ u) :
    (u.comap inj large : Filter α) = Filter.comap m u :=
  rfl

@[simp]
nonrec theorem comap_id (f : Ultrafilter α) (h₀ : Injective (id : α → α) := injective_id)
    (h₁ : range id ∈ f := (by rw [range_id]; exact univ_mem)) :
    f.comap h₀ h₁ = f :=
  coe_injective comap_id

@[simp]
nonrec theorem comap_comap (f : Ultrafilter γ) {m : α → β} {n : β → γ} (inj₀ : Injective n)
    (large₀ : range n ∈ f) (inj₁ : Injective m) (large₁ : range m ∈ f.comap inj₀ large₀)
    (inj₂ : Injective (n ∘ m) := inj₀.comp inj₁)
    (large₂ : range (n ∘ m) ∈ f :=
      (by rw [range_comp]; exact image_mem_of_mem_comap large₀ large₁)) :
    (f.comap inj₀ large₀).comap inj₁ large₁ = f.comap inj₂ large₂ :=
  coe_injective comap_comap

/-- The principal ultrafilter associated to a point `x`. -/
instance : Pure Ultrafilter :=
  ⟨fun a => ofComplNotMemIff (pure a) fun s => by simp⟩

@[simp]
theorem mem_pure {a : α} {s : Set α} : s ∈ (pure a : Ultrafilter α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem coe_pure (a : α) : ↑(pure a : Ultrafilter α) = (pure a : Filter α) :=
  rfl

@[simp]
theorem map_pure (m : α → β) (a : α) : map m (pure a) = pure (m a) :=
  rfl

@[simp]
theorem comap_pure {m : α → β} (a : α) (inj : Injective m) (large) :
    comap (pure <| m a) inj large = pure a :=
  coe_injective <|
    Filter.comap_pure.trans <| by
      rw [coe_pure, ← principal_singleton, ← image_singleton, preimage_image_eq _ inj]

theorem pure_injective : Injective (pure : α → Ultrafilter α) := fun _ _ h =>
  Filter.pure_injective (congr_arg Ultrafilter.toFilter h :)

instance [Inhabited α] : Inhabited (Ultrafilter α) :=
  ⟨pure default⟩

instance [Nonempty α] : Nonempty (Ultrafilter α) :=
  Nonempty.map pure inferInstance

/-- Monadic bind for ultrafilters, coming from the one on filters
defined in terms of map and join. -/
def bind (f : Ultrafilter α) (m : α → Ultrafilter β) : Ultrafilter β :=
  ofComplNotMemIff (Filter.bind ↑f fun x => ↑(m x)) fun s => by
    simp only [mem_bind', mem_coe, ← compl_mem_iff_notMem, compl_setOf, compl_compl]

instance instBind : Bind Ultrafilter :=
  ⟨@Ultrafilter.bind⟩

instance functor : Functor Ultrafilter where map := @Ultrafilter.map

instance monad : Monad Ultrafilter where map := @Ultrafilter.map

section

attribute [local instance] Filter.monad Filter.lawfulMonad

instance lawfulMonad : LawfulMonad Ultrafilter where
  id_map f := coe_injective (id_map f.toFilter)
  pure_bind a f := coe_injective (Filter.pure_bind a ((Ultrafilter.toFilter) ∘ f))
  bind_assoc _ _ _ := coe_injective (filter_eq rfl)
  bind_pure_comp f x := coe_injective (bind_pure_comp f x.1)
  map_const := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_map _ _ := rfl

end

/-- The ultrafilter lemma: Any proper filter is contained in an ultrafilter. -/
theorem exists_le (f : Filter α) [h : NeBot f] : ∃ u : Ultrafilter α, ↑u ≤ f :=
  let ⟨u, hu, huf⟩ := (eq_bot_or_exists_atom_le f).resolve_left h.ne
  ⟨ofAtom u hu, huf⟩

alias _root_.Filter.exists_ultrafilter_le := exists_le

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def of (f : Filter α) [NeBot f] : Ultrafilter α :=
  Classical.choose (exists_le f)

theorem of_le (f : Filter α) [NeBot f] : ↑(of f) ≤ f :=
  Classical.choose_spec (exists_le f)

theorem of_coe (f : Ultrafilter α) : of ↑f = f :=
  coe_inj.1 <| f.unique (of_le f.toFilter)

end Ultrafilter

namespace Filter

variable {f : Filter α} {s : Set α} {a : α}

open Ultrafilter

theorem isAtom_pure : IsAtom (pure a : Filter α) :=
  (pure a : Ultrafilter α).isAtom

protected theorem NeBot.le_pure_iff (hf : f.NeBot) : f ≤ pure a ↔ f = pure a :=
  ⟨Ultrafilter.unique (pure a), le_of_eq⟩

protected theorem NeBot.eq_pure_iff (hf : f.NeBot) {x : α} :
    f = pure x ↔ {x} ∈ f := by
  rw [← hf.le_pure_iff, le_pure_iff]

@[simp]
theorem lt_pure_iff : f < pure a ↔ f = ⊥ :=
  isAtom_pure.lt_iff

theorem le_pure_iff' : f ≤ pure a ↔ f = ⊥ ∨ f = pure a :=
  isAtom_pure.le_iff

@[simp]
theorem Iic_pure (a : α) : Iic (pure a : Filter α) = {⊥, pure a} :=
  isAtom_pure.Iic_eq

theorem mem_iff_ultrafilter : s ∈ f ↔ ∀ g : Ultrafilter α, ↑g ≤ f → s ∈ g := by
  refine ⟨fun hf g hg => hg hf, fun H => by_contra fun hf => ?_⟩
  set g : Filter (sᶜ : Set α) := comap (↑) f
  haveI : NeBot g := comap_neBot_iff_compl_range.2 (by simpa [compl_setOf])
  simpa using H ((of g).map (↑)) (map_le_iff_le_comap.mpr (of_le g))

theorem le_iff_ultrafilter {f₁ f₂ : Filter α} : f₁ ≤ f₂ ↔ ∀ g : Ultrafilter α, ↑g ≤ f₁ → ↑g ≤ f₂ :=
  ⟨fun h _ h₁ => h₁.trans h, fun h _ hs => mem_iff_ultrafilter.2 fun g hg => h g hg hs⟩

/-- A filter equals the intersection of all the ultrafilters which contain it. -/
theorem iSup_ultrafilter_le_eq (f : Filter α) :
    ⨆ (g : Ultrafilter α) (_ : g ≤ f), (g : Filter α) = f :=
  eq_of_forall_ge_iff fun f' => by simp only [iSup_le_iff, ← le_iff_ultrafilter]

theorem exists_ultrafilter_iff {f : Filter α} : (∃ u : Ultrafilter α, ↑u ≤ f) ↔ NeBot f :=
  ⟨fun ⟨_, uf⟩ => neBot_of_le uf, fun h => @exists_ultrafilter_le _ _ h⟩

theorem forall_neBot_le_iff {g : Filter α} {p : Filter α → Prop} (hp : Monotone p) :
    (∀ f : Filter α, NeBot f → f ≤ g → p f) ↔ ∀ f : Ultrafilter α, ↑f ≤ g → p f := by
  refine ⟨fun H f hf => H f f.neBot hf, ?_⟩
  intro H f hf hfg
  exact hp (of_le f) (H _ ((of_le f).trans hfg))

end Filter

namespace Ultrafilter

variable {m : α → β} {s : Set α} {g : Ultrafilter β}

theorem comap_inf_principal_neBot_of_image_mem (h : m '' s ∈ g) : (Filter.comap m g ⊓ 𝓟 s).NeBot :=
  Filter.comap_inf_principal_neBot_of_image_mem g.neBot h

/-- Ultrafilter extending the inf of a comapped ultrafilter and a principal ultrafilter. -/
noncomputable def ofComapInfPrincipal (h : m '' s ∈ g) : Ultrafilter α :=
  @of _ (Filter.comap m g ⊓ 𝓟 s) (comap_inf_principal_neBot_of_image_mem h)

theorem ofComapInfPrincipal_mem (h : m '' s ∈ g) : s ∈ ofComapInfPrincipal h := by
  let f := Filter.comap m g ⊓ 𝓟 s
  haveI : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  have : s ∈ f := mem_inf_of_right (mem_principal_self s)
  exact le_def.mp (of_le _) s this

theorem ofComapInfPrincipal_eq_of_map (h : m '' s ∈ g) : (ofComapInfPrincipal h).map m = g := by
  let f := Filter.comap m g ⊓ 𝓟 s
  haveI : f.NeBot := comap_inf_principal_neBot_of_image_mem h
  apply eq_of_le
  calc
    Filter.map m (of f) ≤ Filter.map m f := map_mono (of_le _)
    _ ≤ (Filter.map m <| Filter.comap m g) ⊓ Filter.map m (𝓟 s) := map_inf_le
    _ = (Filter.map m <| Filter.comap m g) ⊓ (𝓟 <| m '' s) := by rw [map_principal]
    _ ≤ ↑g ⊓ (𝓟 <| m '' s) := inf_le_inf_right _ map_comap_le
    _ = ↑g := inf_of_le_left (le_principal_iff.mpr h)

theorem eq_of_le_pure {X : Type _} {α : Filter X} (hα : α.NeBot) {x y : X}
    (hx : α ≤ pure x) (hy : α ≤ pure y) : x = y :=
  Filter.pure_injective (hα.le_pure_iff.mp hx ▸ hα.le_pure_iff.mp hy)

end Ultrafilter
