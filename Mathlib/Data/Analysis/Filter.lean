/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Order.Filter.Cofinite

#align_import data.analysis.filter from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Computational realization of filters (experimental)

This file provides infrastructure to compute with filters.

## Main declarations

* `CFilter`: Realization of a filter base. Note that this is in the generality of filters on
  lattices, while `Filter` is filters of sets (so corresponding to `CFilter (Set α) σ`).
* `Filter.Realizer`: Realization of a `Filter`. `CFilter` that generates the given filter.
-/


open Set Filter

-- Porting note: TODO write doc strings
/-- A `CFilter α σ` is a realization of a filter (base) on `α`,
  represented by a type `σ` together with operations for the top element and
  the binary `inf` operation. -/
structure CFilter (α σ : Type*) [PartialOrder α] where
  f : σ → α
  pt : σ
  inf : σ → σ → σ
  inf_le_left : ∀ a b : σ, f (inf a b) ≤ f a
  inf_le_right : ∀ a b : σ, f (inf a b) ≤ f b
#align cfilter CFilter

variable {α : Type*} {β : Type*} {σ : Type*} {τ : Type*}

instance [Inhabited α] [SemilatticeInf α] : Inhabited (CFilter α α) :=
  ⟨{  f := id
      pt := default
      inf := (· ⊓ ·)
      inf_le_left := fun _ _ ↦ inf_le_left
      inf_le_right := fun _ _ ↦ inf_le_right }⟩

namespace CFilter

section

variable [PartialOrder α] (F : CFilter α σ)

instance : CoeFun (CFilter α σ) fun _ ↦ σ → α :=
  ⟨CFilter.f⟩

/- Porting note: Due to the CoeFun instance, the lhs of this lemma has a variable (f) as its head
symbol (simpnf linter problem). Replacing it with a FunLike instance would not be mathematically
meaningful here, since the coercion to f cannot be injective, hence need to remove @[simp]. -/
-- @[simp]
theorem coe_mk (f pt inf h₁ h₂ a) : (@CFilter.mk α σ _ f pt inf h₁ h₂) a = f a :=
  rfl
#align cfilter.coe_mk CFilter.coe_mk

/-- Map a `CFilter` to an equivalent representation type. -/
def ofEquiv (E : σ ≃ τ) : CFilter α σ → CFilter α τ
  | ⟨f, p, g, h₁, h₂⟩ =>
    { f := fun a ↦ f (E.symm a)
      pt := E p
      inf := fun a b ↦ E (g (E.symm a) (E.symm b))
      inf_le_left := fun a b ↦ by simpa using h₁ (E.symm a) (E.symm b)
                                  -- 🎉 no goals
      inf_le_right := fun a b ↦ by simpa using h₂ (E.symm a) (E.symm b) }
                                   -- 🎉 no goals
#align cfilter.of_equiv CFilter.ofEquiv

@[simp]
theorem ofEquiv_val (E : σ ≃ τ) (F : CFilter α σ) (a : τ) : F.ofEquiv E a = F (E.symm a) := by
  cases F; rfl
  -- ⊢ f (ofEquiv E { f := f✝, pt := pt✝, inf := inf✝, inf_le_left := inf_le_left✝, …
           -- 🎉 no goals
#align cfilter.of_equiv_val CFilter.ofEquiv_val

end

/-- The filter represented by a `CFilter` is the collection of supersets of
  elements of the filter base. -/
def toFilter (F : CFilter (Set α) σ) : Filter α where
  sets := { a | ∃ b, F b ⊆ a }
  univ_sets := ⟨F.pt, subset_univ _⟩
  sets_of_superset := fun ⟨b, h⟩ s ↦ ⟨b, Subset.trans h s⟩
  inter_sets := fun ⟨a, h₁⟩ ⟨b, h₂⟩ ↦ ⟨F.inf a b,
    subset_inter (Subset.trans (F.inf_le_left _ _) h₁) (Subset.trans (F.inf_le_right _ _) h₂)⟩
#align cfilter.to_filter CFilter.toFilter

@[simp]
theorem mem_toFilter_sets (F : CFilter (Set α) σ) {a : Set α} : a ∈ F.toFilter ↔ ∃ b, F b ⊆ a :=
  Iff.rfl
#align cfilter.mem_to_filter_sets CFilter.mem_toFilter_sets

end CFilter

-- Porting note: TODO write doc strings
/-- A realizer for filter `f` is a cfilter which generates `f`. -/
structure Filter.Realizer (f : Filter α) where
  σ : Type*
  F : CFilter (Set α) σ
  eq : F.toFilter = f
#align filter.realizer Filter.Realizer

/-- A `CFilter` realizes the filter it generates. -/
protected def CFilter.toRealizer (F : CFilter (Set α) σ) : F.toFilter.Realizer :=
  ⟨σ, F, rfl⟩
#align cfilter.to_realizer CFilter.toRealizer

namespace Filter.Realizer

theorem mem_sets {f : Filter α} (F : f.Realizer) {a : Set α} : a ∈ f ↔ ∃ b, F.F b ⊆ a := by
  cases F; subst f; rfl
  -- ⊢ a ∈ f ↔ ∃ b, CFilter.f { σ := σ✝, F := F✝, eq := eq✝ }.F b ⊆ a
           -- ⊢ a ∈ CFilter.toFilter F✝ ↔ ∃ b, CFilter.f { σ := σ✝, F := F✝, eq := (_ : CFil …
                    -- 🎉 no goals
#align filter.realizer.mem_sets Filter.Realizer.mem_sets

/-- Transfer a realizer along an equality of filter. This has better definitional equalities than
the `Eq.rec` proof. -/
def ofEq {f g : Filter α} (e : f = g) (F : f.Realizer) : g.Realizer :=
  ⟨F.σ, F.F, F.eq.trans e⟩
#align filter.realizer.of_eq Filter.Realizer.ofEq

/-- A filter realizes itself. -/
def ofFilter (f : Filter α) : f.Realizer :=
  ⟨f.sets,
    { f := Subtype.val
      pt := ⟨univ, univ_mem⟩
      inf := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦ ⟨_, inter_mem h₁ h₂⟩
      inf_le_left := fun ⟨x, _⟩ ⟨y, _⟩ ↦ inter_subset_left x y
      inf_le_right := fun ⟨x, _⟩ ⟨y, _⟩ ↦ inter_subset_right x y },
    filter_eq <| Set.ext fun _ ↦ by simp [exists_mem_subset_iff]⟩
                                    -- 🎉 no goals
#align filter.realizer.of_filter Filter.Realizer.ofFilter

/-- Transfer a filter realizer to another realizer on a different base type. -/
def ofEquiv {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) : f.Realizer :=
  ⟨τ, F.F.ofEquiv E, by
    refine' Eq.trans _ F.eq
    -- ⊢ CFilter.toFilter (CFilter.ofEquiv E F.F) = CFilter.toFilter F.F
    exact filter_eq (Set.ext fun _ ↦
      ⟨fun ⟨s, h⟩ ↦ ⟨E.symm s, by simpa using h⟩, fun ⟨t, h⟩ ↦ ⟨E t, by simp [h]⟩⟩)⟩
#align filter.realizer.of_equiv Filter.Realizer.ofEquiv

@[simp]
theorem ofEquiv_σ {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) : (F.ofEquiv E).σ = τ :=
  rfl
#align filter.realizer.of_equiv_σ Filter.Realizer.ofEquiv_σ

@[simp]
theorem ofEquiv_F {f : Filter α} (F : f.Realizer) (E : F.σ ≃ τ) (s : τ) :
    (F.ofEquiv E).F s = F.F (E.symm s) := rfl
set_option linter.uppercaseLean3 false in
#align filter.realizer.of_equiv_F Filter.Realizer.ofEquiv_F

/-- `Unit` is a realizer for the principal filter -/
protected def principal (s : Set α) : (principal s).Realizer :=
  ⟨Unit,
    { f := fun _ ↦ s
      pt := ()
      inf := fun _ _ ↦ ()
      inf_le_left := fun _ _ ↦ le_rfl
      inf_le_right := fun _ _ ↦ le_rfl },
    filter_eq <| Set.ext fun _ ↦ ⟨fun ⟨_, s⟩ ↦ s, fun h ↦ ⟨(), h⟩⟩⟩
#align filter.realizer.principal Filter.Realizer.principal

@[simp]
theorem principal_σ (s : Set α) : (Realizer.principal s).σ = Unit :=
  rfl
#align filter.realizer.principal_σ Filter.Realizer.principal_σ

@[simp]
theorem principal_F (s : Set α) (u : Unit) : (Realizer.principal s).F u = s :=
  rfl
set_option linter.uppercaseLean3 false in
#align filter.realizer.principal_F Filter.Realizer.principal_F

instance (s : Set α) : Inhabited (principal s).Realizer :=
  ⟨Realizer.principal s⟩

/-- `Unit` is a realizer for the top filter -/
protected def top : (⊤ : Filter α).Realizer :=
  (Realizer.principal _).ofEq principal_univ
#align filter.realizer.top Filter.Realizer.top

@[simp]
theorem top_σ : (@Realizer.top α).σ = Unit :=
  rfl
#align filter.realizer.top_σ Filter.Realizer.top_σ

@[simp]
theorem top_F (u : Unit) : (@Realizer.top α).F u = univ :=
  rfl
set_option linter.uppercaseLean3 false in
#align filter.realizer.top_F Filter.Realizer.top_F

/-- `Unit` is a realizer for the bottom filter -/
protected def bot : (⊥ : Filter α).Realizer :=
  (Realizer.principal _).ofEq principal_empty
#align filter.realizer.bot Filter.Realizer.bot

@[simp]
theorem bot_σ : (@Realizer.bot α).σ = Unit :=
  rfl
#align filter.realizer.bot_σ Filter.Realizer.bot_σ

@[simp]
theorem bot_F (u : Unit) : (@Realizer.bot α).F u = ∅ :=
  rfl
set_option linter.uppercaseLean3 false in
#align filter.realizer.bot_F Filter.Realizer.bot_F

/-- Construct a realizer for `map m f` given a realizer for `f` -/
protected def map (m : α → β) {f : Filter α} (F : f.Realizer) : (map m f).Realizer :=
  ⟨F.σ,
    { f := fun s ↦ image m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ ↦ image_subset _ (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ ↦ image_subset _ (F.F.inf_le_right _ _) },
    filter_eq <| Set.ext fun _ ↦ by
      simp only [CFilter.toFilter, image_subset_iff, mem_setOf_eq, Filter.mem_sets, mem_map]
      -- ⊢ (∃ b, CFilter.f F.F b ⊆ m ⁻¹' x✝) ↔ m ⁻¹' x✝ ∈ f
      rw [F.mem_sets]⟩
      -- 🎉 no goals
#align filter.realizer.map Filter.Realizer.map

@[simp]
theorem map_σ (m : α → β) {f : Filter α} (F : f.Realizer) : (F.map m).σ = F.σ :=
  rfl
#align filter.realizer.map_σ Filter.Realizer.map_σ

@[simp]
theorem map_F (m : α → β) {f : Filter α} (F : f.Realizer) (s) : (F.map m).F s = image m (F.F s) :=
  rfl
set_option linter.uppercaseLean3 false in
#align filter.realizer.map_F Filter.Realizer.map_F

/-- Construct a realizer for `comap m f` given a realizer for `f` -/
protected def comap (m : α → β) {f : Filter β} (F : f.Realizer) : (comap m f).Realizer :=
  ⟨F.σ,
    { f := fun s ↦ preimage m (F.F s)
      pt := F.F.pt
      inf := F.F.inf
      inf_le_left := fun _ _ ↦ preimage_mono (F.F.inf_le_left _ _)
      inf_le_right := fun _ _ ↦ preimage_mono (F.F.inf_le_right _ _) },
    filter_eq <| Set.ext fun _ ↦ by
      cases F; subst f
      -- ⊢ x✝ ∈ (CFilter.toFilter { f := fun s => m ⁻¹' CFilter.f { σ := σ✝, F := F✝, e …
               -- ⊢ x✝ ∈ (CFilter.toFilter { f := fun s => m ⁻¹' CFilter.f { σ := σ✝, F := F✝, e …
      exact ⟨fun ⟨s, h⟩ ↦ ⟨_, ⟨s, Subset.refl _⟩, h⟩,
        fun ⟨_, ⟨s, h⟩, h₂⟩ ↦ ⟨s, Subset.trans (preimage_mono h) h₂⟩⟩⟩
#align filter.realizer.comap Filter.Realizer.comap

/-- Construct a realizer for the sup of two filters -/
protected def sup {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f ⊔ g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ ↦ F.F s ∪ G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ ↦ (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ ↦ union_subset_union (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ ↦ union_subset_union (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
    filter_eq <| Set.ext fun _ ↦ by cases F; cases G; substs f g; simp [CFilter.toFilter]⟩
                                    -- ⊢ x✝ ∈
                                             -- ⊢ x✝ ∈
                                                      -- ⊢ x✝ ∈
                                                                  -- 🎉 no goals
#align filter.realizer.sup Filter.Realizer.sup

/-- Construct a realizer for the inf of two filters -/
protected def inf {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f ⊓ g).Realizer :=
  ⟨F.σ × G.σ,
    { f := fun ⟨s, t⟩ ↦ F.F s ∩ G.F t
      pt := (F.F.pt, G.F.pt)
      inf := fun ⟨a, a'⟩ ⟨b, b'⟩ ↦ (F.F.inf a b, G.F.inf a' b')
      inf_le_left := fun _ _ ↦ inter_subset_inter (F.F.inf_le_left _ _) (G.F.inf_le_left _ _)
      inf_le_right := fun _ _ ↦ inter_subset_inter (F.F.inf_le_right _ _) (G.F.inf_le_right _ _) },
    by
      cases F; cases G; substs f g; simp only [CFilter.toFilter, Prod.exists]; ext
      -- ⊢ CFilter.toFilter
               -- ⊢ CFilter.toFilter
                        -- ⊢ CFilter.toFilter
                                    -- ⊢ { sets := {a | ∃ a_1 b, CFilter.f F✝¹ a_1 ∩ CFilter.f F✝ b ⊆ a}, univ_sets : …
                                                                               -- ⊢ s✝ ∈ { sets := {a | ∃ a_1 b, CFilter.f F✝¹ a_1 ∩ CFilter.f F✝ b ⊆ a}, univ_s …
      constructor
      -- ⊢ s✝ ∈ { sets := {a | ∃ a_1 b, CFilter.f F✝¹ a_1 ∩ CFilter.f F✝ b ⊆ a}, univ_s …
      · rintro ⟨s, t, h⟩
        -- ⊢ s✝ ∈ { sets := {a | ∃ b, CFilter.f F✝¹ b ⊆ a}, univ_sets := (_ : ∃ b, CFilte …
        apply mem_inf_of_inter _ _ h
        -- ⊢ CFilter.f F✝¹ s ∈ { sets := {a | ∃ b, CFilter.f F✝¹ b ⊆ a}, univ_sets := (_  …
        use s
        -- ⊢ CFilter.f F✝ t ∈ { sets := {a | ∃ b, CFilter.f F✝ b ⊆ a}, univ_sets := (_ :  …
        use t
        -- 🎉 no goals
      · rintro ⟨_, ⟨a, ha⟩, _, ⟨b, hb⟩, rfl⟩
        -- ⊢ w✝¹ ∩ w✝ ∈ { sets := {a | ∃ a_1 b, CFilter.f F✝¹ a_1 ∩ CFilter.f F✝ b ⊆ a},  …
        exact ⟨a, b, inter_subset_inter ha hb⟩⟩
        -- 🎉 no goals
#align filter.realizer.inf Filter.Realizer.inf

/-- Construct a realizer for the cofinite filter -/
protected def cofinite [DecidableEq α] : (@cofinite α).Realizer :=
  ⟨Finset α,
    { f := fun s ↦ { a | a ∉ s }
      pt := ∅
      inf := (· ∪ ·)
      inf_le_left := fun _ _ _ ↦ mt (Finset.mem_union_left _)
      inf_le_right := fun _ _ _ ↦ mt (Finset.mem_union_right _) },
    filter_eq <|
      Set.ext fun _ ↦
        ⟨fun ⟨s, h⟩ ↦ s.finite_toSet.subset (compl_subset_comm.1 h), fun h ↦
          ⟨h.toFinset, by simp [Subset.rfl]⟩⟩⟩
                          -- 🎉 no goals
#align filter.realizer.cofinite Filter.Realizer.cofinite

/-- Construct a realizer for filter bind -/
protected def bind {f : Filter α} {m : α → Filter β} (F : f.Realizer) (G : ∀ i, (m i).Realizer) :
    (f.bind m).Realizer :=
  ⟨Σs : F.σ, ∀ i ∈ F.F s, (G i).σ,
    { f := fun ⟨s, f⟩ ↦ ⋃ i ∈ F.F s, (G i).F (f i (by assumption))
                                                      -- 🎉 no goals
      pt := ⟨F.F.pt, fun i _ ↦ (G i).F.pt⟩
      inf := fun ⟨a, f⟩ ⟨b, f'⟩ ↦
        ⟨F.F.inf a b, fun i h ↦
          (G i).F.inf (f i (F.F.inf_le_left _ _ h)) (f' i (F.F.inf_le_right _ _ h))⟩
      inf_le_left := fun _ _ _ ↦ by
        simp only [mem_iUnion, forall_exists_index]
        -- ⊢ ∀ (x : α) (x_1 : x ∈ CFilter.f F.F (CFilter.inf F.F x✝².fst x✝¹.fst)), x✝ ∈  …
        exact fun i h₁ h₂ ↦ ⟨i, F.F.inf_le_left _ _ h₁, (G i).F.inf_le_left _ _ h₂⟩
        -- 🎉 no goals
      inf_le_right := fun _ _ _ ↦ by
        simp only [mem_iUnion, forall_exists_index]
        -- ⊢ ∀ (x : α) (x_1 : x ∈ CFilter.f F.F (CFilter.inf F.F x✝².fst x✝¹.fst)), x✝ ∈  …
        exact fun i h₁ h₂ ↦ ⟨i, F.F.inf_le_right _ _ h₁, (G i).F.inf_le_right _ _ h₂⟩ },
        -- 🎉 no goals
    filter_eq <| Set.ext fun _ ↦ by
      cases' F with _ F _; subst f
      -- ⊢ x✝ ∈
                           -- ⊢ x✝ ∈
      simp only [CFilter.toFilter, iUnion_subset_iff, Sigma.exists, Filter.mem_sets, mem_bind]
      -- ⊢ x✝ ∈ {a | ∃ a_1 b, ∀ (i : α) (i_1 : i ∈ CFilter.f F { fst := a_1, snd := b } …
      exact
        ⟨fun ⟨s, f, h⟩ ↦
          ⟨F s, ⟨s, Subset.refl _⟩, fun i H ↦ (G i).mem_sets.2 ⟨f i H, fun _ h' ↦ h i H h'⟩⟩,
          fun ⟨_, ⟨s, h⟩, f⟩ ↦
          let ⟨f', h'⟩ := Classical.axiom_of_choice fun i : F s ↦ (G i).mem_sets.1 (f i (h i.2))
          ⟨s, fun i h ↦ f' ⟨i, h⟩, fun _ H _ m ↦ h' ⟨_, H⟩ m⟩⟩⟩
#align filter.realizer.bind Filter.Realizer.bind

-- Porting note: `iSup` had a long dubious translation message. I added `ₓ` to be safe.
/-- Construct a realizer for indexed supremum -/
protected def iSup {f : α → Filter β} (F : ∀ i, (f i).Realizer) : (⨆ i, f i).Realizer :=
  let F' : (⨆ i, f i).Realizer :=
    (Realizer.bind Realizer.top F).ofEq <|
      filter_eq <| Set.ext <| by simp [Filter.bind, eq_univ_iff_forall, iSup_sets_eq]
                                 -- 🎉 no goals
  F'.ofEquiv <|
    show (Σ_ : Unit, ∀ i : α, True → (F i).σ) ≃ ∀ i, (F i).σ from
      ⟨fun ⟨_, f⟩ i ↦ f i ⟨⟩, fun f ↦ ⟨(), fun i _ ↦ f i⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
#align filter.realizer.Sup Filter.Realizer.iSupₓ

/-- Construct a realizer for the product of filters -/
protected def prod {f g : Filter α} (F : f.Realizer) (G : g.Realizer) : (f.prod g).Realizer :=
  (F.comap _).inf (G.comap _)
#align filter.realizer.prod Filter.Realizer.prod

theorem le_iff {f g : Filter α} (F : f.Realizer) (G : g.Realizer) :
    f ≤ g ↔ ∀ b : G.σ, ∃ a : F.σ, F.F a ≤ G.F b :=
  ⟨fun H t ↦ F.mem_sets.1 (H (G.mem_sets.2 ⟨t, Subset.refl _⟩)), fun H _ h ↦
    F.mem_sets.2 <|
      let ⟨s, h₁⟩ := G.mem_sets.1 h
      let ⟨t, h₂⟩ := H s
      ⟨t, Subset.trans h₂ h₁⟩⟩
#align filter.realizer.le_iff Filter.Realizer.le_iff

theorem tendsto_iff (f : α → β) {l₁ : Filter α} {l₂ : Filter β} (L₁ : l₁.Realizer)
    (L₂ : l₂.Realizer) : Tendsto f l₁ l₂ ↔ ∀ b, ∃ a, ∀ x ∈ L₁.F a, f x ∈ L₂.F b :=
  (le_iff (L₁.map f) L₂).trans <| forall_congr' fun _ ↦ exists_congr fun _ ↦ image_subset_iff
#align filter.realizer.tendsto_iff Filter.Realizer.tendsto_iff

theorem ne_bot_iff {f : Filter α} (F : f.Realizer) : f ≠ ⊥ ↔ ∀ a : F.σ, (F.F a).Nonempty := by
  rw [not_iff_comm, ← le_bot_iff, F.le_iff Realizer.bot, not_forall]
  -- ⊢ (∃ x, ¬Set.Nonempty (CFilter.f F.F x)) ↔ ∀ (b : Realizer.bot.σ), ∃ a, CFilte …
  simp only [Set.not_nonempty_iff_eq_empty]
  -- ⊢ (∃ x, CFilter.f F.F x = ∅) ↔ ∀ (b : Realizer.bot.σ), ∃ a, CFilter.f F.F a ≤  …
  exact ⟨fun ⟨x, e⟩ _ ↦ ⟨x, le_of_eq e⟩, fun h ↦
    let ⟨x, h⟩ := h ()
    ⟨x, le_bot_iff.1 h⟩⟩
#align filter.realizer.ne_bot_iff Filter.Realizer.ne_bot_iff

end Filter.Realizer
