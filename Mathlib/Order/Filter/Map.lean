/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Control.Basic
import Mathlib.Data.Set.Lattice.Image
import Mathlib.Order.Filter.Basic

/-!
# Theorems about map and comap on filters.
-/

assert_not_exists OrderedSemiring Fintype

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α β γ δ : Type*} {ι : Sort*} {F : Filter α} {G : Filter β}

/-! ### Push-forwards, pull-backs, and the monad structure -/

section Map

@[simp]
theorem map_principal {s : Set α} {f : α → β} : map f (𝓟 s) = 𝓟 (Set.image f s) :=
  Filter.ext fun _ => image_subset_iff.symm

variable {f : Filter α} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

@[simp]
theorem eventually_map {P : β → Prop} : (∀ᶠ b in map m f, P b) ↔ ∀ᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
theorem frequently_map {P : β → Prop} : (∃ᶠ b in map m f, P b) ↔ ∃ᶠ a in f, P (m a) :=
  Iff.rfl

@[simp]
theorem eventuallyEq_map {f₁ f₂ : β → γ} : f₁ =ᶠ[map m f] f₂ ↔ f₁ ∘ m =ᶠ[f] f₂ ∘ m := .rfl

@[simp]
theorem eventuallyLE_map [LE γ] {f₁ f₂ : β → γ} : f₁ ≤ᶠ[map m f] f₂ ↔ f₁ ∘ m ≤ᶠ[f] f₂ ∘ m := .rfl

@[simp]
theorem mem_map : t ∈ map m f ↔ m ⁻¹' t ∈ f :=
  Iff.rfl

theorem mem_map' : t ∈ map m f ↔ { x | m x ∈ t } ∈ f :=
  Iff.rfl

theorem image_mem_map (hs : s ∈ f) : m '' s ∈ map m f :=
  f.sets_of_superset hs <| subset_preimage_image m s

-- The simpNF linter says that the LHS can be simplified via `Filter.mem_map`.
-- However this is a higher priority lemma.
-- It seems the side condition `hf` is not applied by `simpNF`.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem image_mem_map_iff (hf : Injective m) : m '' s ∈ map m f ↔ s ∈ f :=
  ⟨fun h => by rwa [← preimage_image_eq s hf], image_mem_map⟩

theorem range_mem_map : range m ∈ map m f := by
  rw [← image_univ]
  exact image_mem_map univ_mem

theorem mem_map_iff_exists_image : t ∈ map m f ↔ ∃ s ∈ f, m '' s ⊆ t :=
  ⟨fun ht => ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩, fun ⟨_, hs, ht⟩ =>
    mem_of_superset (image_mem_map hs) ht⟩

@[simp]
theorem map_id : Filter.map id f = f :=
  filter_eq <| rfl

@[simp]
theorem map_id' : Filter.map (fun x => x) f = f :=
  map_id

@[simp]
theorem map_compose : Filter.map m' ∘ Filter.map m = Filter.map (m' ∘ m) :=
  funext fun _ => filter_eq <| rfl

@[simp]
theorem map_map : Filter.map m' (Filter.map m f) = Filter.map (m' ∘ m) f :=
  congr_fun Filter.map_compose f

/-- If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter. -/
theorem map_congr {m₁ m₂ : α → β} {f : Filter α} (h : m₁ =ᶠ[f] m₂) : map m₁ f = map m₂ f :=
  Filter.ext' fun _ => eventually_congr (h.mono fun _ hx => hx ▸ Iff.rfl)

end Map

section Comap

variable {f : α → β} {l : Filter β} {p : α → Prop} {s : Set α}

theorem mem_comap' : s ∈ comap f l ↔ { y | ∀ ⦃x⦄, f x = y → x ∈ s } ∈ l :=
  ⟨fun ⟨t, ht, hts⟩ => mem_of_superset ht fun y hy x hx => hts <| mem_preimage.2 <| by rwa [hx],
    fun h => ⟨_, h, fun _ hx => hx rfl⟩⟩

-- TODO: it would be nice to use `kernImage` much more to take advantage of common name and API,
-- and then this would become `mem_comap'`
theorem mem_comap'' : s ∈ comap f l ↔ kernImage f s ∈ l :=
  mem_comap'

/-- RHS form is used, e.g., in the definition of `UniformSpace`. -/
lemma mem_comap_prodMk {x : α} {s : Set β} {F : Filter (α × β)} :
    s ∈ comap (Prod.mk x) F ↔ {p : α × β | p.fst = x → p.snd ∈ s} ∈ F := by
  simp_rw [mem_comap', Prod.ext_iff, and_imp, @forall_swap β (_ = _), forall_eq, eq_comm]

@[deprecated (since := "2025-03-10")]
alias mem_comap_prod_mk := mem_comap_prodMk

@[simp]
theorem eventually_comap : (∀ᶠ a in comap f l, p a) ↔ ∀ᶠ b in l, ∀ a, f a = b → p a :=
  mem_comap'

@[simp]
theorem frequently_comap : (∃ᶠ a in comap f l, p a) ↔ ∃ᶠ b in l, ∃ a, f a = b ∧ p a := by
  simp only [Filter.Frequently, eventually_comap, not_exists, _root_.not_and]

theorem mem_comap_iff_compl : s ∈ comap f l ↔ (f '' sᶜ)ᶜ ∈ l := by
  simp only [mem_comap'', kernImage_eq_compl]

theorem compl_mem_comap : sᶜ ∈ comap f l ↔ (f '' s)ᶜ ∈ l := by rw [mem_comap_iff_compl, compl_compl]

end Comap


instance : LawfulFunctor (Filter : Type u → Type u) where
  id_map _ := map_id
  comp_map _ _ _ := map_map.symm
  map_const := rfl

theorem pure_sets (a : α) : (pure a : Filter α).sets = { s | a ∈ s } :=
  rfl

@[simp]
theorem eventually_pure {a : α} {p : α → Prop} : (∀ᶠ x in pure a, p x) ↔ p a :=
  Iff.rfl

@[simp]
theorem principal_singleton (a : α) : 𝓟 {a} = pure a :=
  Filter.ext fun s => by simp only [mem_pure, mem_principal, singleton_subset_iff]

@[simp]
theorem map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
  rfl

theorem pure_le_principal {s : Set α} (a : α) : pure a ≤ 𝓟 s ↔ a ∈ s := by
  simp

@[simp] theorem join_pure (f : Filter α) : join (pure f) = f := rfl

@[simp]
theorem pure_bind (a : α) (m : α → Filter β) : bind (pure a) m = m a := by
  simp only [bind, map_pure, join_pure]

theorem map_bind {α β} (m : β → γ) (f : Filter α) (g : α → Filter β) :
    map m (bind f g) = bind f (map m ∘ g) :=
  rfl

theorem bind_map {α β} (m : α → β) (f : Filter α) (g : β → Filter γ) :
    (bind (map m f) g) = bind f (g ∘ m) :=
  rfl

/-!
### `Filter` as a `Monad`

In this section we define `Filter.monad`, a `Monad` structure on `Filter`s. This definition is not
an instance because its `Seq` projection is not equal to the `Filter.seq` function we use in the
`Applicative` instance on `Filter`.
-/

section

/-- The monad structure on filters. -/
protected def monad : Monad Filter where map := @Filter.map

attribute [local instance] Filter.monad

protected theorem lawfulMonad : LawfulMonad Filter where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

end

instance : Alternative Filter where
  seq := fun x y => x.seq (y ())
  failure := ⊥
  orElse x y := x ⊔ y ()

@[simp]
theorem map_def {α β} (m : α → β) (f : Filter α) : m <$> f = map m f :=
  rfl

@[simp]
theorem bind_def {α β} (f : Filter α) (m : α → Filter β) : f >>= m = bind f m :=
  rfl

/-! #### `map` and `comap` equations -/

section Map

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Filter β} {m : α → β} {m' : β → γ} {s : Set α} {t : Set β}

@[simp] theorem mem_comap : s ∈ comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s := Iff.rfl

theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
  ⟨t, ht, Subset.rfl⟩

theorem Eventually.comap {p : β → Prop} (hf : ∀ᶠ b in g, p b) (f : α → β) :
    ∀ᶠ a in comap f g, p (f a) :=
  preimage_mem_comap hf

theorem comap_id : comap id f = f :=
  le_antisymm (fun _ => preimage_mem_comap) fun _ ⟨_, ht, hst⟩ => mem_of_superset ht hst

theorem comap_id' : comap (fun x => x) f = f := comap_id

theorem comap_const_of_notMem {x : β} (ht : t ∈ g) (hx : x ∉ t) : comap (fun _ : α => x) g = ⊥ :=
  empty_mem_iff_bot.1 <| mem_comap'.2 <| mem_of_superset ht fun _ hx' _ h => hx <| h.symm ▸ hx'

@[deprecated (since := "2025-05-23")] alias comap_const_of_not_mem := comap_const_of_notMem

theorem comap_const_of_mem {x : β} (h : ∀ t ∈ g, x ∈ t) : comap (fun _ : α => x) g = ⊤ :=
  top_unique fun _ hs => univ_mem' fun _ => h _ (mem_comap'.1 hs) rfl

theorem map_const [NeBot f] {c : β} : (f.map fun _ => c) = pure c := by
  ext s
  by_cases h : c ∈ s <;> simp [h]

theorem comap_comap {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
  Filter.coext fun s => by simp only [compl_mem_comap, image_image, (· ∘ ·)]

section comm

/-!
The variables in the following lemmas are used as in this diagram:
```
    φ
  α → β
θ ↓   ↓ ψ
  γ → δ
    ρ
```
-/


variable {φ : α → β} {θ : α → γ} {ψ : β → δ} {ρ : γ → δ}

theorem map_comm (H : ψ ∘ φ = ρ ∘ θ) (F : Filter α) :
    map ψ (map φ F) = map ρ (map θ F) := by
  rw [Filter.map_map, H, ← Filter.map_map]

theorem comap_comm (H : ψ ∘ φ = ρ ∘ θ) (G : Filter δ) :
    comap φ (comap ψ G) = comap θ (comap ρ G) := by
  rw [Filter.comap_comap, H, ← Filter.comap_comap]

end comm

theorem _root_.Function.Semiconj.filter_map {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) :=
  map_comm h.comp_eq

theorem _root_.Function.Commute.filter_map {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.semiconj.filter_map

theorem _root_.Function.Semiconj.filter_comap {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (comap f) (comap gb) (comap ga) :=
  comap_comm h.comp_eq.symm

theorem _root_.Function.Commute.filter_comap {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (comap f) (comap g) :=
  h.semiconj.filter_comap

section

open Filter

theorem _root_.Function.LeftInverse.filter_map {f : α → β} {g : β → α} (hfg : LeftInverse g f) :
    LeftInverse (map g) (map f) := fun F ↦ by
  rw [map_map, hfg.comp_eq_id, map_id]

theorem _root_.Function.LeftInverse.filter_comap {f : α → β} {g : β → α} (hfg : LeftInverse g f) :
    RightInverse (comap g) (comap f) := fun F ↦ by
  rw [comap_comap, hfg.comp_eq_id, comap_id]

nonrec theorem _root_.Function.RightInverse.filter_map {f : α → β} {g : β → α}
    (hfg : RightInverse g f) : RightInverse (map g) (map f) :=
  hfg.filter_map

nonrec theorem _root_.Function.RightInverse.filter_comap {f : α → β} {g : β → α}
    (hfg : RightInverse g f) : LeftInverse (comap g) (comap f) :=
  hfg.filter_comap

theorem _root_.Set.LeftInvOn.filter_map_Iic {f : α → β} {g : β → α} (hfg : LeftInvOn g f s) :
    LeftInvOn (map g) (map f) (Iic <| 𝓟 s) := fun F (hF : F ≤ 𝓟 s) ↦ by
  have : (g ∘ f) =ᶠ[𝓟 s] id := by simpa only [eventuallyEq_principal] using hfg
  rw [map_map, map_congr (this.filter_mono hF), map_id]

nonrec theorem _root_.Set.RightInvOn.filter_map_Iic {f : α → β} {g : β → α}
    (hfg : RightInvOn g f t) : RightInvOn (map g) (map f) (Iic <| 𝓟 t) :=
  hfg.filter_map_Iic

end

section KernMap

/-- The analog of `Set.kernImage` for filters.
A set `s` belongs to `Filter.kernMap m f` if either of the following equivalent conditions hold.

1. There exists a set `t ∈ f` such that `s = Set.kernImage m t`. This is used as a definition.
2. There exists a set `t` such that `tᶜ ∈ f` and `sᶜ = m '' t`, see `Filter.mem_kernMap_iff_compl`
and `Filter.compl_mem_kernMap`.

This definition is useful because it gives a right adjoint to `Filter.comap`, and because it has a
nice interpretation when working with `co-` filters (`Filter.cocompact`, `Filter.cofinite`, ...).
For example, `kernMap m (cocompact α)` is the filter generated by the complements of the sets
`m '' K` where `K` is a compact subset of `α`. -/
def kernMap (m : α → β) (f : Filter α) : Filter β where
  sets := (kernImage m) '' f.sets
  univ_sets := ⟨univ, f.univ_sets, by simp [kernImage_eq_compl]⟩
  sets_of_superset := by
    rintro _ t ⟨s, hs, rfl⟩ hst
    refine ⟨s ∪ m ⁻¹' t, mem_of_superset hs subset_union_left, ?_⟩
    rw [kernImage_union_preimage, union_eq_right.mpr hst]
  inter_sets := by
    rintro _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩
    exact ⟨s₁ ∩ s₂, f.inter_sets h₁ h₂, Set.preimage_kernImage.u_inf⟩

variable {m : α → β} {f : Filter α}

theorem mem_kernMap {s : Set β} : s ∈ kernMap m f ↔ ∃ t ∈ f, kernImage m t = s :=
  Iff.rfl

theorem mem_kernMap_iff_compl {s : Set β} : s ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = sᶜ := by
  rw [mem_kernMap, compl_surjective.exists]
  refine exists_congr (fun x ↦ and_congr_right fun _ ↦ ?_)
  rw [kernImage_compl, compl_eq_comm, eq_comm]

theorem compl_mem_kernMap {s : Set β} : sᶜ ∈ kernMap m f ↔ ∃ t, tᶜ ∈ f ∧ m '' t = s := by
  simp_rw [mem_kernMap_iff_compl, compl_compl]

theorem comap_le_iff_le_kernMap : comap m g ≤ f ↔ g ≤ kernMap m f := by
  simp [Filter.le_def, mem_comap'', mem_kernMap, -mem_comap]

theorem gc_comap_kernMap (m : α → β) : GaloisConnection (comap m) (kernMap m) :=
  fun _ _ ↦ comap_le_iff_le_kernMap

theorem kernMap_principal {s : Set α} : kernMap m (𝓟 s) = 𝓟 (kernImage m s) := by
  refine eq_of_forall_le_iff (fun g ↦ ?_)
  rw [← comap_le_iff_le_kernMap, le_principal_iff, le_principal_iff, mem_comap'']

end KernMap

@[simp]
theorem comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t) :=
  Filter.ext fun _ => ⟨fun ⟨_u, hu, b⟩ => (preimage_mono hu).trans b,
    fun h => ⟨t, Subset.rfl, h⟩⟩

theorem principal_subtype {α : Type*} (s : Set α) (t : Set s) :
    𝓟 t = comap (↑) (𝓟 (((↑) : s → α) '' t)) := by
  rw [comap_principal, preimage_image_eq _ Subtype.coe_injective]

@[simp]
theorem comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b}) := by
  rw [← principal_singleton, comap_principal]

theorem map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
  ⟨fun h _ ⟨_, ht, hts⟩ => mem_of_superset (h ht) hts, fun h _ ht => h ⟨_, ht, Subset.rfl⟩⟩

theorem gc_map_comap (m : α → β) : GaloisConnection (map m) (comap m) :=
  fun _ _ => map_le_iff_le_comap

@[mono]
theorem map_mono : Monotone (map m) :=
  (gc_map_comap m).monotone_l

@[mono]
theorem comap_mono : Monotone (comap m) :=
  (gc_map_comap m).monotone_u

/-- Temporary lemma that we can tag with `gcongr` -/
@[gcongr] theorem _root_.GCongr.Filter.map_le_map {F G : Filter α} (h : F ≤ G) :
    map m F ≤ map m G := map_mono h

/-- Temporary lemma that we can tag with `gcongr` -/
@[gcongr]
theorem _root_.GCongr.Filter.comap_le_comap {F G : Filter β} (h : F ≤ G) :
    comap m F ≤ comap m G := comap_mono h

@[simp] theorem map_bot : map m ⊥ = ⊥ := (gc_map_comap m).l_bot

@[simp] theorem map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_comap m).l_sup

@[simp]
theorem map_iSup {f : ι → Filter α} : map m (⨆ i, f i) = ⨆ i, map m (f i) :=
  (gc_map_comap m).l_iSup

@[simp]
theorem map_top (f : α → β) : map f ⊤ = 𝓟 (range f) := by
  rw [← principal_univ, map_principal, image_univ]

@[simp] theorem comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top

@[simp] theorem comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf

@[simp]
theorem comap_iInf {f : ι → Filter β} : comap m (⨅ i, f i) = ⨅ i, comap m (f i) :=
  (gc_map_comap m).u_iInf

theorem le_comap_top (f : α → β) (l : Filter α) : l ≤ comap f ⊤ := by
  rw [comap_top]
  exact le_top

theorem map_comap_le : map m (comap m g) ≤ g :=
  (gc_map_comap m).l_u_le _

theorem le_comap_map : f ≤ comap m (map m f) :=
  (gc_map_comap m).le_u_l _

@[simp]
theorem comap_bot : comap m ⊥ = ⊥ :=
  bot_unique fun s _ => ⟨∅, mem_bot, by simp only [empty_subset, preimage_empty]⟩

theorem neBot_of_comap (h : (comap m g).NeBot) : g.NeBot := by
  rw [neBot_iff] at *
  contrapose! h
  rw [h]
  exact comap_bot

theorem comap_inf_principal_range : comap m (g ⊓ 𝓟 (range m)) = comap m g := by
  simp

theorem disjoint_comap (h : Disjoint g₁ g₂) : Disjoint (comap m g₁) (comap m g₂) := by
  simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]

theorem comap_iSup {ι} {f : ι → Filter β} {m : α → β} : comap m (iSup f) = ⨆ i, comap m (f i) :=
  (gc_comap_kernMap m).l_iSup

theorem comap_sSup {s : Set (Filter β)} {m : α → β} : comap m (sSup s) = ⨆ f ∈ s, comap m f := by
  simp only [sSup_eq_iSup, comap_iSup]

theorem comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ := by
  rw [sup_eq_iSup, comap_iSup, iSup_bool_eq, Bool.cond_true, Bool.cond_false]

theorem map_comap (f : Filter β) (m : α → β) : (f.comap m).map m = f ⊓ 𝓟 (range m) := by
  refine le_antisymm (le_inf map_comap_le <| le_principal_iff.2 range_mem_map) ?_
  rintro t' ⟨t, ht, sub⟩
  refine mem_inf_principal.2 (mem_of_superset ht ?_)
  rintro _ hxt ⟨x, rfl⟩
  exact sub hxt

theorem map_comap_setCoe_val (f : Filter β) (s : Set β) :
    (f.comap ((↑) : s → β)).map (↑) = f ⊓ 𝓟 s := by
  rw [map_comap, Subtype.range_val]

theorem map_comap_of_mem {f : Filter β} {m : α → β} (hf : range m ∈ f) : (f.comap m).map m = f := by
  rw [map_comap, inf_eq_left.2 (le_principal_iff.2 hf)]

instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Filter α) (Filter β) (map c) fun f => ∀ᶠ x : α in f, p x where
  prf f hf := ⟨comap c f, map_comap_of_mem <| hf.mono CanLift.prf⟩

theorem comap_le_comap_iff {f g : Filter β} {m : α → β} (hf : range m ∈ f) :
    comap m f ≤ comap m g ↔ f ≤ g :=
  ⟨fun h => map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, fun h => comap_mono h⟩

theorem map_comap_of_surjective {f : α → β} (hf : Surjective f) (l : Filter β) :
    map f (comap f l) = l :=
  map_comap_of_mem <| by simp only [hf.range_eq, univ_mem]

theorem comap_injective {f : α → β} (hf : Surjective f) : Injective (comap f) :=
  LeftInverse.injective <| map_comap_of_surjective hf

theorem _root_.Function.Surjective.filter_map_top {f : α → β} (hf : Surjective f) : map f ⊤ = ⊤ :=
  (congr_arg _ comap_top).symm.trans <| map_comap_of_surjective hf ⊤

theorem subtype_coe_map_comap (s : Set α) (f : Filter α) :
    map ((↑) : s → α) (comap ((↑) : s → α) f) = f ⊓ 𝓟 s := by rw [map_comap, Subtype.range_coe]

theorem image_mem_of_mem_comap {f : Filter α} {c : β → α} (h : range c ∈ f) {W : Set β}
    (W_in : W ∈ comap c f) : c '' W ∈ f := by
  rw [← map_comap_of_mem h]
  exact image_mem_map W_in

theorem image_coe_mem_of_mem_comap {f : Filter α} {U : Set α} (h : U ∈ f) {W : Set U}
    (W_in : W ∈ comap ((↑) : U → α) f) : (↑) '' W ∈ f :=
  image_mem_of_mem_comap (by simp [h]) W_in

theorem comap_map {f : Filter α} {m : α → β} (h : Injective m) : comap m (map m f) = f :=
  le_antisymm
    (fun s hs =>
      mem_of_superset (preimage_mem_comap <| image_mem_map hs) <| by
        simp only [preimage_image_eq s h, Subset.rfl])
    le_comap_map

theorem mem_comap_iff {f : Filter β} {m : α → β} (inj : Injective m) (large : Set.range m ∈ f)
    {S : Set α} : S ∈ comap m f ↔ m '' S ∈ f := by
  rw [← image_mem_map_iff inj, map_comap_of_mem large]

theorem map_le_map_iff_of_injOn {l₁ l₂ : Filter α} {f : α → β} {s : Set α} (h₁ : s ∈ l₁)
    (h₂ : s ∈ l₂) (hinj : InjOn f s) : map f l₁ ≤ map f l₂ ↔ l₁ ≤ l₂ :=
  ⟨fun h _t ht =>
    mp_mem h₁ <|
      mem_of_superset (h <| image_mem_map (inter_mem h₂ ht)) fun _y ⟨_x, ⟨hxs, hxt⟩, hxy⟩ hys =>
        hinj hxs hys hxy ▸ hxt,
    fun h => map_mono h⟩

theorem map_le_map_iff {f g : Filter α} {m : α → β} (hm : Injective m) :
    map m f ≤ map m g ↔ f ≤ g := by rw [map_le_iff_le_comap, comap_map hm]

theorem map_eq_map_iff_of_injOn {f g : Filter α} {m : α → β} {s : Set α} (hsf : s ∈ f) (hsg : s ∈ g)
    (hm : InjOn m s) : map m f = map m g ↔ f = g := by
  simp only [le_antisymm_iff, map_le_map_iff_of_injOn hsf hsg hm,
    map_le_map_iff_of_injOn hsg hsf hm]

theorem map_inj {f g : Filter α} {m : α → β} (hm : Injective m) : map m f = map m g ↔ f = g :=
  map_eq_map_iff_of_injOn univ_mem univ_mem hm.injOn

theorem map_injective {m : α → β} (hm : Injective m) : Injective (map m) := fun _ _ =>
  (map_inj hm).1

theorem comap_neBot_iff {f : Filter β} {m : α → β} : NeBot (comap m f) ↔ ∀ t ∈ f, ∃ a, m a ∈ t := by
  simp only [← forall_mem_nonempty_iff_neBot, mem_comap, forall_exists_index, and_imp]
  exact ⟨fun h t t_in => h (m ⁻¹' t) t t_in Subset.rfl, fun h s t ht hst => (h t ht).imp hst⟩

theorem comap_neBot {f : Filter β} {m : α → β} (hm : ∀ t ∈ f, ∃ a, m a ∈ t) : NeBot (comap m f) :=
  comap_neBot_iff.mpr hm

theorem comap_neBot_iff_frequently {f : Filter β} {m : α → β} :
    NeBot (comap m f) ↔ ∃ᶠ y in f, y ∈ range m := by
  simp only [comap_neBot_iff, frequently_iff, mem_range, @and_comm (_ ∈ _), exists_exists_eq_and]

theorem comap_neBot_iff_compl_range {f : Filter β} {m : α → β} :
    NeBot (comap m f) ↔ (range m)ᶜ ∉ f :=
  comap_neBot_iff_frequently

theorem comap_eq_bot_iff_compl_range {f : Filter β} {m : α → β} : comap m f = ⊥ ↔ (range m)ᶜ ∈ f :=
  not_iff_not.mp <| neBot_iff.symm.trans comap_neBot_iff_compl_range

theorem comap_surjective_eq_bot {f : Filter β} {m : α → β} (hm : Surjective m) :
    comap m f = ⊥ ↔ f = ⊥ := by
  rw [comap_eq_bot_iff_compl_range, hm.range_eq, compl_univ, empty_mem_iff_bot]

theorem disjoint_comap_iff (h : Surjective m) :
    Disjoint (comap m g₁) (comap m g₂) ↔ Disjoint g₁ g₂ := by
  rw [disjoint_iff, disjoint_iff, ← comap_inf, comap_surjective_eq_bot h]

theorem NeBot.comap_of_range_mem {f : Filter β} {m : α → β} (_ : NeBot f) (hm : range m ∈ f) :
    NeBot (comap m f) :=
  comap_neBot_iff_frequently.2 <| Eventually.frequently hm

section Sum
open Sum

@[simp]
theorem comap_inl_map_inr : comap inl (map (@inr α β) g) = ⊥ := by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]
theorem comap_inr_map_inl : comap inr (map (@inl α β) f) = ⊥ := by
  ext
  rw [mem_comap_iff_compl]
  simp

@[simp]
theorem map_inl_inf_map_inr : map inl f ⊓ map inr g = ⊥ := by
  apply le_bot_iff.mp
  trans map inl ⊤ ⊓ map inr ⊤
  · apply inf_le_inf <;> simp
  · simp

@[simp]
theorem map_inr_inf_map_inl : map inr f ⊓ map inl g = ⊥ := by
  rw [inf_comm, map_inl_inf_map_inr]

theorem comap_sumElim_eq (l : Filter γ) (m₁ : α → γ) (m₂ : β → γ) :
    comap (Sum.elim m₁ m₂) l = map inl (comap m₁ l) ⊔ map inr (comap m₂ l) := by
  ext s
  simp_rw [mem_sup, mem_map, mem_comap_iff_compl]
  simp [image_sumElim]

theorem map_comap_inl_sup_map_comap_inr (l : Filter (α ⊕ β)) :
    map inl (comap inl l) ⊔ map inr (comap inr l) = l := by
  rw [← comap_sumElim_eq, Sum.elim_inl_inr, comap_id]

theorem map_sumElim_eq (l : Filter (α ⊕ β)) (m₁ : α → γ) (m₂ : β → γ) :
    map (Sum.elim m₁ m₂) l = map m₁ (comap inl l) ⊔ map m₂ (comap inr l) := by
  rw [← map_comap_inl_sup_map_comap_inr l]
  simp [map_sup, map_map, comap_sup, (gc_map_comap _).u_l_u_eq_u]

end Sum

@[simp]
theorem comap_fst_neBot_iff {f : Filter α} :
    (f.comap (Prod.fst : α × β → α)).NeBot ↔ f.NeBot ∧ Nonempty β := by
  cases isEmpty_or_nonempty β
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp [*]
  · simp [comap_neBot_iff_frequently, *]

@[instance]
theorem comap_fst_neBot [Nonempty β] {f : Filter α} [NeBot f] :
    (f.comap (Prod.fst : α × β → α)).NeBot :=
  comap_fst_neBot_iff.2 ⟨‹_›, ‹_›⟩

@[simp]
theorem comap_snd_neBot_iff {f : Filter β} :
    (f.comap (Prod.snd : α × β → β)).NeBot ↔ Nonempty α ∧ f.NeBot := by
  rcases isEmpty_or_nonempty α with hα | hα
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]; simp
  · simp [comap_neBot_iff_frequently, hα]

@[instance]
theorem comap_snd_neBot [Nonempty α] {f : Filter β} [NeBot f] :
    (f.comap (Prod.snd : α × β → β)).NeBot :=
  comap_snd_neBot_iff.2 ⟨‹_›, ‹_›⟩

theorem comap_eval_neBot_iff' {ι : Type*} {α : ι → Type*} {i : ι} {f : Filter (α i)} :
    (comap (eval i) f).NeBot ↔ (∀ j, Nonempty (α j)) ∧ NeBot f := by
  rcases isEmpty_or_nonempty (∀ j, α j) with H | H
  · rw [filter_eq_bot_of_isEmpty (f.comap _), ← not_iff_not]
    simp [← Classical.nonempty_pi]
  · have : ∀ j, Nonempty (α j) := Classical.nonempty_pi.1 H
    simp [comap_neBot_iff_frequently, *]

@[simp]
theorem comap_eval_neBot_iff {ι : Type*} {α : ι → Type*} [∀ j, Nonempty (α j)] {i : ι}
    {f : Filter (α i)} : (comap (eval i) f).NeBot ↔ NeBot f := by simp [comap_eval_neBot_iff', *]

@[instance]
theorem comap_eval_neBot {ι : Type*} {α : ι → Type*} [∀ j, Nonempty (α j)] (i : ι)
    (f : Filter (α i)) [NeBot f] : (comap (eval i) f).NeBot :=
  comap_eval_neBot_iff.2 ‹_›

theorem comap_coe_neBot_of_le_principal {s : Set γ} {l : Filter γ} [h : NeBot l] (h' : l ≤ 𝓟 s) :
    NeBot (comap ((↑) : s → γ) l) :=
  h.comap_of_range_mem <| (@Subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)

theorem NeBot.comap_of_surj {f : Filter β} {m : α → β} (hf : NeBot f) (hm : Surjective m) :
    NeBot (comap m f) :=
  hf.comap_of_range_mem <| univ_mem' hm

theorem NeBot.comap_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f) :=
  hf.comap_of_range_mem <| mem_of_superset hs (image_subset_range _ _)

@[simp]
theorem map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
  ⟨by
    rw [← empty_mem_iff_bot, ← empty_mem_iff_bot]
    exact id, fun h => by simp only [h, map_bot]⟩

theorem map_neBot_iff (f : α → β) {F : Filter α} : NeBot (map f F) ↔ NeBot F := by
  simp only [neBot_iff, Ne, map_eq_bot_iff]

theorem NeBot.map (hf : NeBot f) (m : α → β) : NeBot (map m f) :=
  (map_neBot_iff m).2 hf

theorem NeBot.of_map : NeBot (f.map m) → NeBot f :=
  (map_neBot_iff m).1

instance map_neBot [hf : NeBot f] : NeBot (f.map m) :=
  hf.map m

theorem sInter_comap_sets (f : α → β) (F : Filter β) : ⋂₀ (comap f F).sets = ⋂ U ∈ F, f ⁻¹' U := by
  ext x
  suffices (∀ (A : Set α) (B : Set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔
      ∀ B : Set β, B ∈ F → f x ∈ B by
    simp only [mem_sInter, mem_iInter, Filter.mem_sets, mem_comap, this, and_imp,
      mem_preimage, exists_imp]
  constructor
  · intro h U U_in
    simpa only [Subset.rfl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in
  · intro h V U U_in f_U_V
    exact f_U_V (h U U_in)

end Map

-- this is a generic rule for monotone functions:
theorem map_iInf_le {f : ι → Filter α} {m : α → β} : map m (iInf f) ≤ ⨅ i, map m (f i) :=
  le_iInf fun _ => map_mono <| iInf_le _ _

theorem map_iInf_eq {f : ι → Filter α} {m : α → β} (hf : Directed (· ≥ ·) f) [Nonempty ι] :
    map m (iInf f) = ⨅ i, map m (f i) :=
  map_iInf_le.antisymm fun s (hs : m ⁻¹' s ∈ iInf f) =>
    let ⟨i, hi⟩ := (mem_iInf_of_directed hf _).1 hs
    have : ⨅ i, map m (f i) ≤ 𝓟 s :=
      iInf_le_of_le i <| by simpa only [le_principal_iff, mem_map]
    Filter.le_principal_iff.1 this

theorem map_biInf_eq {ι : Type w} {f : ι → Filter α} {m : α → β} {p : ι → Prop}
    (h : DirectedOn (f ⁻¹'o (· ≥ ·)) { x | p x }) (ne : ∃ i, p i) :
    map m (⨅ (i) (_ : p i), f i) = ⨅ (i) (_ : p i), map m (f i) := by
  haveI := nonempty_subtype.2 ne
  simp only [iInf_subtype']
  exact map_iInf_eq h.directed_val

theorem map_inf_le {f g : Filter α} {m : α → β} : map m (f ⊓ g) ≤ map m f ⊓ map m g :=
  (@map_mono _ _ m).map_inf_le f g

theorem map_inf {f g : Filter α} {m : α → β} (h : Injective m) :
    map m (f ⊓ g) = map m f ⊓ map m g := by
  refine map_inf_le.antisymm ?_
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ ∩ s₂⟩
  refine mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) ?_
  rw [← image_inter h, image_subset_iff, ht]

theorem map_inf' {f g : Filter α} {m : α → β} {t : Set α} (htf : t ∈ f) (htg : t ∈ g)
    (h : InjOn m t) : map m (f ⊓ g) = map m f ⊓ map m g := by
  lift f to Filter t using htf; lift g to Filter t using htg
  replace h : Injective (m ∘ ((↑) : t → α)) := h.injective
  simp only [map_map, ← map_inf Subtype.coe_injective, map_inf h]

lemma disjoint_of_map {α β : Type*} {F G : Filter α} {f : α → β}
    (h : Disjoint (map f F) (map f G)) : Disjoint F G :=
  disjoint_iff.mpr <| map_eq_bot_iff.mp <| le_bot_iff.mp <| trans map_inf_le (disjoint_iff.mp h)

theorem disjoint_map {m : α → β} (hm : Injective m) {f₁ f₂ : Filter α} :
    Disjoint (map m f₁) (map m f₂) ↔ Disjoint f₁ f₂ := by
  simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]

theorem map_equiv_symm (e : α ≃ β) (f : Filter β) : map e.symm f = comap e f :=
  map_injective e.injective <| by
    rw [map_map, e.self_comp_symm, map_id, map_comap_of_surjective e.surjective]

theorem map_eq_comap_of_inverse {f : Filter α} {m : α → β} {n : β → α} (h₁ : m ∘ n = id)
    (h₂ : n ∘ m = id) : map m f = comap n f :=
  map_equiv_symm ⟨n, m, congr_fun h₁, congr_fun h₂⟩ f

theorem comap_equiv_symm (e : α ≃ β) (f : Filter α) : comap e.symm f = map e f :=
  (map_eq_comap_of_inverse e.self_comp_symm e.symm_comp_self).symm

theorem map_swap_eq_comap_swap {f : Filter (α × β)} : map Prod.swap f = comap Prod.swap f :=
  map_eq_comap_of_inverse Prod.swap_swap_eq Prod.swap_swap_eq

/-- A useful lemma when dealing with uniformities. -/
theorem map_swap4_eq_comap {f : Filter ((α × β) × γ × δ)} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f =
      comap (fun p : (α × γ) × β × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) f :=
  map_eq_comap_of_inverse (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl) (funext fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl)

theorem le_map {f : Filter α} {m : α → β} {g : Filter β} (h : ∀ s ∈ f, m '' s ∈ g) : g ≤ f.map m :=
  fun _ hs => mem_of_superset (h _ hs) <| image_preimage_subset _ _

theorem le_map_iff {f : Filter α} {m : α → β} {g : Filter β} : g ≤ f.map m ↔ ∀ s ∈ f, m '' s ∈ g :=
  ⟨fun h _ hs => h (image_mem_map hs), le_map⟩

protected theorem push_pull (f : α → β) (F : Filter α) (G : Filter β) :
    map f (F ⊓ comap f G) = map f F ⊓ G := by
  apply le_antisymm
  · calc
      map f (F ⊓ comap f G) ≤ map f F ⊓ (map f <| comap f G) := map_inf_le
      _ ≤ map f F ⊓ G := inf_le_inf_left (map f F) map_comap_le
  · rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩
    apply mem_inf_of_inter (image_mem_map V_in) Z_in
    calc
      f '' V ∩ Z = f '' (V ∩ f ⁻¹' Z) := by rw [image_inter_preimage]
      _ ⊆ f '' (V ∩ W) := image_subset _ (inter_subset_inter_right _ ‹_›)
      _ = f '' (f ⁻¹' U) := by rw [h]
      _ ⊆ U := image_preimage_subset f U

protected theorem push_pull' (f : α → β) (F : Filter α) (G : Filter β) :
    map f (comap f G ⊓ F) = G ⊓ map f F := by simp only [Filter.push_pull, inf_comm]

theorem disjoint_comap_iff_map {f : α → β} {F : Filter α} {G : Filter β} :
    Disjoint F (comap f G) ↔ Disjoint (map f F) G := by
  simp only [disjoint_iff, ← Filter.push_pull, map_eq_bot_iff]

theorem disjoint_comap_iff_map' {f : α → β} {F : Filter α} {G : Filter β} :
    Disjoint (comap f G) F ↔ Disjoint G (map f F) := by
  simp only [disjoint_iff, ← Filter.push_pull', map_eq_bot_iff]

theorem neBot_inf_comap_iff_map {f : α → β} {F : Filter α} {G : Filter β} :
    NeBot (F ⊓ comap f G) ↔ NeBot (map f F ⊓ G) := by
  rw [← map_neBot_iff, Filter.push_pull]

theorem neBot_inf_comap_iff_map' {f : α → β} {F : Filter α} {G : Filter β} :
    NeBot (comap f G ⊓ F) ↔ NeBot (G ⊓ map f F) := by
  rw [← map_neBot_iff, Filter.push_pull']

theorem comap_inf_principal_neBot_of_image_mem {f : Filter β} {m : α → β} (hf : NeBot f) {s : Set α}
    (hs : m '' s ∈ f) : NeBot (comap m f ⊓ 𝓟 s) := by
  rw [neBot_inf_comap_iff_map', map_principal, ← frequently_mem_iff_neBot]
  exact Eventually.frequently hs

theorem principal_eq_map_coe_top (s : Set α) : 𝓟 s = map ((↑) : s → α) ⊤ := by simp

theorem inf_principal_eq_bot_iff_comap {F : Filter α} {s : Set α} :
    F ⊓ 𝓟 s = ⊥ ↔ comap ((↑) : s → α) F = ⊥ := by
  rw [principal_eq_map_coe_top s, ← Filter.push_pull', inf_top_eq, map_eq_bot_iff]

lemma map_generate_le_generate_preimage_preimage (U : Set (Set β)) (f : β → α) :
    map f (generate U) ≤ generate ((f ⁻¹' ·) ⁻¹' U) := by
  rw [le_generate_iff]
  exact fun u hu ↦ mem_generate_of_mem hu

lemma generate_image_preimage_le_comap (U : Set (Set α)) (f : β → α) :
    generate ((f ⁻¹' ·) '' U) ≤ comap f (generate U) := by
  rw [← map_le_iff_le_comap, le_generate_iff]
  exact fun u hu ↦ mem_generate_of_mem ⟨u, hu, rfl⟩

section Applicative

theorem singleton_mem_pure {a : α} : {a} ∈ (pure a : Filter α) :=
  mem_singleton a

theorem pure_injective : Injective (pure : α → Filter α) := fun a _ hab =>
  (Filter.ext_iff.1 hab { x | a = x }).1 rfl

instance pure_neBot {α : Type u} {a : α} : NeBot (pure a) :=
  ⟨mt empty_mem_iff_bot.2 <| notMem_empty a⟩

@[simp]
theorem le_pure_iff {f : Filter α} {a : α} : f ≤ pure a ↔ {a} ∈ f := by
  rw [← principal_singleton, le_principal_iff]

theorem mem_seq_def {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, ∀ x ∈ u, ∀ y ∈ t, (x : α → β) y ∈ s :=
  Iff.rfl

theorem mem_seq_iff {f : Filter (α → β)} {g : Filter α} {s : Set β} :
    s ∈ f.seq g ↔ ∃ u ∈ f, ∃ t ∈ g, Set.seq u t ⊆ s := by
  simp only [mem_seq_def, seq_subset]

theorem mem_map_seq_iff {f : Filter α} {g : Filter β} {m : α → β → γ} {s : Set γ} :
    s ∈ (f.map m).seq g ↔ ∃ t u, t ∈ g ∧ u ∈ f ∧ ∀ x ∈ u, ∀ y ∈ t, m x y ∈ s :=
  Iff.intro (fun ⟨t, ht, s, hs, hts⟩ => ⟨s, m ⁻¹' t, hs, ht, fun _ => hts _⟩)
    fun ⟨t, s, ht, hs, hts⟩ =>
    ⟨m '' s, image_mem_map hs, t, ht, fun _ ⟨_, has, Eq⟩ => Eq ▸ hts _ has⟩

theorem seq_mem_seq {f : Filter (α → β)} {g : Filter α} {s : Set (α → β)} {t : Set α} (hs : s ∈ f)
    (ht : t ∈ g) : s.seq t ∈ f.seq g :=
  ⟨s, hs, t, ht, fun f hf a ha => ⟨f, hf, a, ha, rfl⟩⟩

theorem le_seq {f : Filter (α → β)} {g : Filter α} {h : Filter β}
    (hh : ∀ t ∈ f, ∀ u ∈ g, Set.seq t u ∈ h) : h ≤ seq f g := fun _ ⟨_, ht, _, hu, hs⟩ =>
  mem_of_superset (hh _ ht _ hu) fun _ ⟨_, hm, _, ha, eq⟩ => eq ▸ hs _ hm _ ha

@[mono]
theorem seq_mono {f₁ f₂ : Filter (α → β)} {g₁ g₂ : Filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.seq g₁ ≤ f₂.seq g₂ :=
  le_seq fun _ hs _ ht => seq_mem_seq (hf hs) (hg ht)

@[simp]
theorem pure_seq_eq_map (g : α → β) (f : Filter α) : seq (pure g) f = f.map g := by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← singleton_seq]
    apply seq_mem_seq _ hs
    exact singleton_mem_pure
  · refine sets_of_superset (map g f) (image_mem_map ht) ?_
    rintro b ⟨a, ha, rfl⟩
    exact ⟨g, hs, a, ha, rfl⟩

@[simp]
theorem seq_pure (f : Filter (α → β)) (a : α) : seq f (pure a) = map (fun g : α → β => g a) f := by
  refine le_antisymm (le_map fun s hs => ?_) (le_seq fun s hs t ht => ?_)
  · rw [← seq_singleton]
    exact seq_mem_seq hs singleton_mem_pure
  · refine sets_of_superset (map (fun g : α → β => g a) f) (image_mem_map hs) ?_
    rintro b ⟨g, hg, rfl⟩
    exact ⟨g, hg, a, ht, rfl⟩

@[simp]
theorem seq_assoc (x : Filter α) (g : Filter (α → β)) (h : Filter (β → γ)) :
    seq h (seq g x) = seq (seq (map (· ∘ ·) h) g) x := by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩
    refine mem_of_superset ?_ (Set.seq_mono ((Set.seq_mono hu Subset.rfl).trans hs) Subset.rfl)
    rw [← Set.seq_seq]
    exact seq_mem_seq hw (seq_mem_seq hv ht)
  · rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩
    refine mem_of_superset ?_ (Set.seq_mono Subset.rfl ht)
    rw [Set.seq_seq]
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv

theorem prod_map_seq_comm (f : Filter α) (g : Filter β) :
    (map Prod.mk f).seq g = seq (map (fun b a => (a, b)) g) f := by
  refine le_antisymm (le_seq fun s hs t ht => ?_) (le_seq fun s hs t ht => ?_)
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine mem_of_superset ?_ (Set.seq_mono hs Subset.rfl)
    rw [← Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu
  · rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩
    refine mem_of_superset ?_ (Set.seq_mono hs Subset.rfl)
    rw [Set.prod_image_seq_comm]
    exact seq_mem_seq (image_mem_map ht) hu

theorem seq_eq_filter_seq {α β : Type u} (f : Filter (α → β)) (g : Filter α) :
    f <*> g = seq f g :=
  rfl

instance : LawfulApplicative (Filter : Type u → Type u) where
  map_pure := map_pure
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  seq_pure := seq_pure
  pure_seq := pure_seq_eq_map
  seq_assoc := seq_assoc

instance : CommApplicative (Filter : Type u → Type u) :=
  ⟨fun f g => prod_map_seq_comm f g⟩

end Applicative

/-! #### `bind` equations -/


section Bind

@[simp]
theorem eventually_bind {f : Filter α} {m : α → Filter β} {p : β → Prop} :
    (∀ᶠ y in bind f m, p y) ↔ ∀ᶠ x in f, ∀ᶠ y in m x, p y :=
  Iff.rfl

@[simp]
theorem frequently_bind {f : Filter α} {m : α → Filter β} {p : β → Prop} :
    (∃ᶠ y in bind f m, p y) ↔ ∃ᶠ x in f, ∃ᶠ y in m x, p y := by
  rw [← not_iff_not]
  simp only [not_frequently, eventually_bind]

@[simp]
theorem eventuallyEq_bind {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ =ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ =ᶠ[m x] g₂ :=
  Iff.rfl

@[simp]
theorem eventuallyLE_bind [LE γ] {f : Filter α} {m : α → Filter β} {g₁ g₂ : β → γ} :
    g₁ ≤ᶠ[bind f m] g₂ ↔ ∀ᶠ x in f, g₁ ≤ᶠ[m x] g₂ :=
  Iff.rfl

theorem mem_bind' {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f :=
  Iff.rfl

@[simp]
theorem mem_bind {s : Set β} {f : Filter α} {m : α → Filter β} :
    s ∈ bind f m ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x :=
  calc
    s ∈ bind f m ↔ { a | s ∈ m a } ∈ f := Iff.rfl
    _ ↔ ∃ t ∈ f, t ⊆ { a | s ∈ m a } := exists_mem_subset_iff.symm
    _ ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x := Iff.rfl

theorem bind_le {f : Filter α} {g : α → Filter β} {l : Filter β} (h : ∀ᶠ x in f, g x ≤ l) :
    f.bind g ≤ l :=
  join_le <| eventually_map.2 h

@[mono]
theorem bind_mono {f₁ f₂ : Filter α} {g₁ g₂ : α → Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ᶠ[f₁] g₂) :
    bind f₁ g₁ ≤ bind f₂ g₂ := by
  refine le_trans (fun s hs => ?_) (join_mono <| map_mono hf)
  simp only [mem_join, mem_bind', mem_map] at hs ⊢
  filter_upwards [hg, hs] with _ hx hs using hx hs

theorem bind_inf_principal {f : Filter α} {g : α → Filter β} {s : Set β} :
    (f.bind fun x => g x ⊓ 𝓟 s) = f.bind g ⊓ 𝓟 s :=
  Filter.ext fun s => by simp only [mem_bind, mem_inf_principal]

theorem sup_bind {f g : Filter α} {h : α → Filter β} : bind (f ⊔ g) h = bind f h ⊔ bind g h := rfl

theorem principal_bind {s : Set α} {f : α → Filter β} : bind (𝓟 s) f = ⨆ x ∈ s, f x :=
  show join (map f (𝓟 s)) = ⨆ x ∈ s, f x by
    simp only [sSup_image, join_principal_eq_sSup, map_principal]

end Bind

end Filter

open Filter

variable {α β : Type*} {F : Filter α} {G : Filter β}

-- TODO(Anatole): unify with the global case
theorem Filter.map_surjOn_Iic_iff_le_map {m : α → β} :
    SurjOn (map m) (Iic F) (Iic G) ↔ G ≤ map m F := by
  refine ⟨fun hm ↦ ?_, fun hm ↦ ?_⟩
  · rcases hm right_mem_Iic with ⟨H, (hHF : H ≤ F), rfl⟩
    exact map_mono hHF
  · have : RightInvOn (F ⊓ comap m ·) (map m) (Iic G) :=
      fun H (hHG : H ≤ G) ↦ by simpa [Filter.push_pull] using hHG.trans hm
    exact this.surjOn fun H _ ↦ mem_Iic.mpr inf_le_left

theorem Filter.map_surjOn_Iic_iff_surjOn {s : Set α} {t : Set β} {m : α → β} :
    SurjOn (map m) (Iic <| 𝓟 s) (Iic <| 𝓟 t) ↔ SurjOn m s t := by
  rw [map_surjOn_Iic_iff_le_map, map_principal, principal_mono, SurjOn]

alias ⟨_, Set.SurjOn.filter_map_Iic⟩ := Filter.map_surjOn_Iic_iff_surjOn

theorem Filter.filter_injOn_Iic_iff_injOn {s : Set α} {m : α → β} :
    InjOn (map m) (Iic <| 𝓟 s) ↔ InjOn m s := by
  refine ⟨fun hm x hx y hy hxy ↦ ?_, fun hm F hF G hG ↦ ?_⟩
  · rwa [← pure_injective.eq_iff, ← map_pure, ← map_pure, hm.eq_iff, pure_injective.eq_iff]
      at hxy <;> rwa [mem_Iic, pure_le_principal]
  · simp [map_eq_map_iff_of_injOn (le_principal_iff.mp hF) (le_principal_iff.mp hG) hm]

alias ⟨_, Set.InjOn.filter_map_Iic⟩ := Filter.filter_injOn_Iic_iff_injOn
