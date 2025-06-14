/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
import Mathlib.Order.Filter.Bases.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Nat
import Mathlib.Tactic.Subsingleton

/-!
# Basic results on `Filter.atTop` and `Filter.atBot` filters

In this file we prove many lemmas like “if `f → +∞`, then `f ± c → +∞`”.
-/

assert_not_exists Finset

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

section IsDirected
variable [Preorder α] [IsDirected α (· ≤ ·)] {p : α → Prop}

theorem hasAntitoneBasis_atTop [Nonempty α] : (@atTop α _).HasAntitoneBasis Ici :=
  .iInf_principal fun _ _ ↦ Ici_subset_Ici.2

theorem atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fun _ => True) Ici :=
  hasAntitoneBasis_atTop.1

lemma atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@atTop α _).HasBasis (fun _ => True) Ioi :=
  atTop_basis.to_hasBasis (fun a ha => ⟨a, ha, Ioi_subset_Ici_self⟩) fun a ha =>
    (exists_gt a).imp fun _b hb => ⟨ha, Ici_subset_Ioi.2 hb⟩

lemma atTop_basis_Ioi' [NoMaxOrder α] (a : α) : atTop.HasBasis (a < ·) Ioi := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis_Ioi.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  obtain ⟨d, hcd⟩ := exists_gt c
  exact ⟨d, hac.trans_lt hcd, Ioi_subset_Ioi (hbc.trans hcd.le)⟩

theorem atTop_basis' (a : α) : atTop.HasBasis (a ≤ ·) Ici := by
  have : Nonempty α := ⟨a⟩
  refine atTop_basis.to_hasBasis (fun b _ ↦ ?_) fun b _ ↦ ⟨b, trivial, Subset.rfl⟩
  obtain ⟨c, hac, hbc⟩ := exists_ge_ge a b
  exact ⟨c, hac, Ici_subset_Ici.2 hbc⟩

variable [Nonempty α]

@[instance]
lemma atTop_neBot : NeBot (atTop : Filter α) := atTop_basis.neBot_iff.2 fun _ => nonempty_Ici

theorem atTop_neBot_iff {α : Type*} [Preorder α] :
    (atTop : Filter α).NeBot ↔ Nonempty α ∧ IsDirected α (· ≤ ·) := by
  refine ⟨fun h ↦ ⟨nonempty_of_neBot atTop, ⟨fun x y ↦ ?_⟩⟩, fun ⟨h₁, h₂⟩ ↦ atTop_neBot⟩
  exact ((eventually_ge_atTop x).and (eventually_ge_atTop y)).exists

theorem atBot_neBot_iff {α : Type*} [Preorder α] :
    (atBot : Filter α).NeBot ↔ Nonempty α ∧ IsDirected α (· ≥ ·) :=
  atTop_neBot_iff (α := αᵒᵈ)

@[simp] lemma mem_atTop_sets {s : Set α} : s ∈ (atTop : Filter α) ↔ ∃ a : α, ∀ b ≥ a, b ∈ s :=
  atTop_basis.mem_iff.trans <| exists_congr fun _ => iff_of_eq (true_and _)

@[simp] lemma eventually_atTop : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b ≥ a, p b := mem_atTop_sets

theorem frequently_atTop : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b ≥ a, p b :=
  atTop_basis.frequently_iff.trans <| by simp

alias ⟨Eventually.exists_forall_of_atTop, _⟩ := eventually_atTop

lemma exists_eventually_atTop {r : α → β → Prop} :
    (∃ b, ∀ᶠ a in atTop, r a b) ↔ ∀ᶠ a₀ in atTop, ∃ b, ∀ a ≥ a₀, r a b := by
  simp_rw [eventually_atTop, ← exists_swap (α := α)]
  exact exists_congr fun a ↦ .symm <| forall_ge_iff <| Monotone.exists fun _ _ _ hb H n hn ↦
    H n (hb.trans hn)

theorem map_atTop_eq {f : α → β} : atTop.map f = ⨅ a, 𝓟 (f '' { a' | a ≤ a' }) :=
  (atTop_basis.map f).eq_iInf

theorem frequently_atTop' [NoMaxOrder α] : (∃ᶠ x in atTop, p x) ↔ ∀ a, ∃ b > a, p b :=
  atTop_basis_Ioi.frequently_iff.trans <| by simp

end IsDirected

section IsCodirected
variable [Preorder α] [IsDirected α (· ≥ ·)] {p : α → Prop}

lemma atBot_basis_Iio [Nonempty α] [NoMinOrder α] : (@atBot α _).HasBasis (fun _ => True) Iio :=
  atTop_basis_Ioi (α := αᵒᵈ)

lemma atBot_basis_Iio' [NoMinOrder α] (a : α) : atBot.HasBasis (· < a) Iio :=
  atTop_basis_Ioi' (α := αᵒᵈ) a

lemma atBot_basis' (a : α) : (@atBot α _).HasBasis (fun x => x ≤ a) Iic := atTop_basis' (α := αᵒᵈ) _

variable [Nonempty α]

lemma atBot_basis : (@atBot α _).HasBasis (fun _ => True) Iic := atTop_basis (α := αᵒᵈ)

@[instance] lemma atBot_neBot : NeBot (atBot : Filter α) := atTop_neBot (α := αᵒᵈ)

@[simp] lemma mem_atBot_sets {s : Set α} : s ∈ (atBot : Filter α) ↔ ∃ a : α, ∀ b ≤ a, b ∈ s :=
  mem_atTop_sets (α := αᵒᵈ)

@[simp] lemma eventually_atBot : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ b ≤ a, p b := mem_atBot_sets

theorem frequently_atBot : (∃ᶠ x in atBot, p x) ↔ ∀ a, ∃ b ≤ a, p b := frequently_atTop (α := αᵒᵈ)

alias ⟨Eventually.exists_forall_of_atBot, _⟩ := eventually_atBot

lemma exists_eventually_atBot {r : α → β → Prop} :
    (∃ b, ∀ᶠ a in atBot, r a b) ↔ ∀ᶠ a₀ in atBot, ∃ b, ∀ a ≤ a₀, r a b :=
  exists_eventually_atTop (α := αᵒᵈ)

theorem map_atBot_eq {f : α → β} : atBot.map f = ⨅ a, 𝓟 (f '' { a' | a' ≤ a }) :=
  map_atTop_eq (α := αᵒᵈ)

theorem frequently_atBot' [NoMinOrder α] : (∃ᶠ x in atBot, p x) ↔ ∀ a, ∃ b < a, p b :=
  frequently_atTop' (α := αᵒᵈ)

end IsCodirected

/-!
### Sequences
-/

@[deprecated (since := "2025-04-20")] alias extraction_of_frequently_atTop' :=
  Nat.exists_strictMono_subsequence

theorem extraction_of_frequently_atTop {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  rw [frequently_atTop'] at h
  exact Nat.exists_strictMono_subsequence h

theorem extraction_of_eventually_atTop {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) :=
  extraction_of_frequently_atTop h.frequently

theorem extraction_forall_of_frequently {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) := by
  simp only [frequently_atTop'] at h
  choose u hu hu' using h
  use (fun n => Nat.recOn n (u 0 0) fun n v => u (n + 1) v : ℕ → ℕ)
  constructor
  · apply strictMono_nat_of_lt_succ
    intro n
    apply hu
  · intro n
    cases n <;> simp [hu']

theorem extraction_forall_of_eventually {P : ℕ → ℕ → Prop} (h : ∀ n, ∀ᶠ k in atTop, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) :=
  extraction_forall_of_frequently fun n => (h n).frequently

theorem extraction_forall_of_eventually' {P : ℕ → ℕ → Prop} (h : ∀ n, ∃ N, ∀ k ≥ N, P n k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P n (φ n) :=
  extraction_forall_of_eventually (by simp [eventually_atTop, h])

section IsDirected
variable [Preorder α] [IsDirected α (· ≤ ·)] {F : Filter β} {u : α → β}

theorem inf_map_atTop_neBot_iff [Nonempty α] :
    NeBot (F ⊓ map u atTop) ↔ ∀ U ∈ F, ∀ N, ∃ n ≥ N, u n ∈ U := by
  simp_rw [inf_neBot_iff_frequently_left, frequently_map, frequently_atTop]; rfl

variable [Preorder β]

lemma exists_le_of_tendsto_atTop (h : Tendsto u atTop atTop) (a : α) (b : β) :
    ∃ a' ≥ a, b ≤ u a' := by
  have : Nonempty α := ⟨a⟩
  have : ∀ᶠ x in atTop, a ≤ x ∧ b ≤ u x :=
    (eventually_ge_atTop a).and (h.eventually <| eventually_ge_atTop b)
  exact this.exists

theorem exists_le_of_tendsto_atBot (h : Tendsto u atTop atBot) :
    ∀ a b, ∃ a' ≥ a, u a' ≤ b := exists_le_of_tendsto_atTop (β := βᵒᵈ) h

theorem exists_lt_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto u atTop atTop) (a : α) (b : β) :
    ∃ a' ≥ a, b < u a' := by
  obtain ⟨b', hb'⟩ := exists_gt b
  rcases exists_le_of_tendsto_atTop h a b' with ⟨a', ha', ha''⟩
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩

theorem exists_lt_of_tendsto_atBot [NoMinOrder β] (h : Tendsto u atTop atBot) :
    ∀ a b, ∃ a' ≥ a, u a' < b := exists_lt_of_tendsto_atTop (β := βᵒᵈ) h

end IsDirected

section IsCodirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] {F : Filter β} {u : α → β}

theorem inf_map_atBot_neBot_iff : NeBot (F ⊓ map u atBot) ↔ ∀ U ∈ F, ∀ N, ∃ n ≤ N, u n ∈ U :=
  inf_map_atTop_neBot_iff (α := αᵒᵈ)

end IsCodirected

section IsDirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] {f : α → β} {l : Filter β}

theorem tendsto_atTop' : Tendsto f atTop l ↔ ∀ s ∈ l, ∃ a, ∀ b ≥ a, f b ∈ s := by
  simp only [tendsto_def, mem_atTop_sets, mem_preimage]

theorem tendsto_atTop_principal {s : Set β} : Tendsto f atTop (𝓟 s) ↔ ∃ N, ∀ n ≥ N, f n ∈ s := by
  simp_rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_atTop_sets, mem_preimage]

variable [Preorder β]

/-- A function `f` grows to `+∞` independent of an order-preserving embedding `e`. -/
theorem tendsto_atTop_atTop : Tendsto f atTop atTop ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a :=
  tendsto_iInf.trans <| forall_congr' fun _ => tendsto_atTop_principal

theorem tendsto_atTop_atBot : Tendsto f atTop atBot ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → f a ≤ b :=
  tendsto_atTop_atTop (β := βᵒᵈ)

theorem tendsto_atTop_atTop_iff_of_monotone (hf : Monotone f) :
    Tendsto f atTop atTop ↔ ∀ b : β, ∃ a, b ≤ f a :=
  tendsto_atTop_atTop.trans <| forall_congr' fun _ => exists_congr fun a =>
    ⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans h <| hf ha'⟩

theorem tendsto_atTop_atBot_iff_of_antitone (hf : Antitone f) :
    Tendsto f atTop atBot ↔ ∀ b : β, ∃ a, f a ≤ b :=
  tendsto_atTop_atTop_iff_of_monotone (β := βᵒᵈ) hf

end IsDirected

section IsCodirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] {f : α → β} {l : Filter β}

theorem tendsto_atBot' : Tendsto f atBot l ↔ ∀ s ∈ l, ∃ a, ∀ b ≤ a, f b ∈ s :=
  tendsto_atTop' (α := αᵒᵈ)

theorem tendsto_atBot_principal {s : Set β} : Tendsto f atBot (𝓟 s) ↔ ∃ N, ∀ n ≤ N, f n ∈ s :=
  tendsto_atTop_principal (α := αᵒᵈ) (β := βᵒᵈ)

variable [Preorder β]

theorem tendsto_atBot_atTop : Tendsto f atBot atTop ↔ ∀ b : β, ∃ i : α, ∀ a : α, a ≤ i → b ≤ f a :=
  tendsto_atTop_atTop (α := αᵒᵈ)

theorem tendsto_atBot_atBot : Tendsto f atBot atBot ↔ ∀ b : β, ∃ i : α, ∀ a : α, a ≤ i → f a ≤ b :=
  tendsto_atTop_atTop (α := αᵒᵈ) (β := βᵒᵈ)

theorem tendsto_atBot_atBot_iff_of_monotone (hf : Monotone f) :
    Tendsto f atBot atBot ↔ ∀ b : β, ∃ a, f a ≤ b :=
  tendsto_atBot_atBot.trans <| forall_congr' fun _ => exists_congr fun a =>
    ⟨fun h => h a (le_refl a), fun h _a' ha' => le_trans (hf ha') h⟩

theorem tendsto_atBot_atTop_iff_of_antitone (hf : Antitone f) :
    Tendsto f atBot atTop ↔ ∀ b : β, ∃ a, b ≤ f a :=
  tendsto_atBot_atBot_iff_of_monotone (β := βᵒᵈ) hf

end IsCodirected

alias _root_.Monotone.tendsto_atTop_atTop_iff := tendsto_atTop_atTop_iff_of_monotone

alias _root_.Monotone.tendsto_atBot_atBot_iff := tendsto_atBot_atBot_iff_of_monotone

theorem Tendsto.subseq_mem {F : Filter α} {V : ℕ → Set α} (h : ∀ n, V n ∈ F) {u : ℕ → α}
    (hu : Tendsto u atTop F) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, u (φ n) ∈ V n :=
  extraction_forall_of_eventually'
    (fun n => tendsto_atTop'.mp hu _ (h n) : ∀ n, ∃ N, ∀ k ≥ N, u k ∈ V n)

/-- A function `f` maps upwards closed sets (atTop sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connection above `b`. -/
theorem map_atTop_eq_of_gc_preorder
    [Preorder α] [IsDirected α (· ≤ ·)] [Preorder β] [IsDirected β (· ≤ ·)] {f : α → β}
    (hf : Monotone f) (b : β)
    (hgi : ∀ c ≥ b, ∃ x, f x = c ∧ ∀ a, f a ≤ c ↔ a ≤ x) : map f atTop = atTop := by
  have : Nonempty α := (hgi b le_rfl).nonempty
  choose! g hfg hgle using hgi
  refine le_antisymm (hf.tendsto_atTop_atTop fun c ↦ ?_) ?_
  · rcases exists_ge_ge c b with ⟨d, hcd, hbd⟩
    exact ⟨g d, hcd.trans (hfg d hbd).ge⟩
  · have : Nonempty α := ⟨g b⟩
    rw [(atTop_basis.map f).ge_iff]
    intro a _
    filter_upwards [eventually_ge_atTop (f a), eventually_ge_atTop b] with c hac hbc
    exact ⟨g c, (hgle _ hbc _).1 hac, hfg _ hbc⟩


/-- A function `f` maps upwards closed sets (atTop sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connection above `b`. -/
theorem map_atTop_eq_of_gc
    [Preorder α] [IsDirected α (· ≤ ·)] [PartialOrder β] [IsDirected β (· ≤ ·)]
    {f : α → β} (g : β → α) (b : β) (hf : Monotone f)
    (gc : ∀ a, ∀ c ≥ b, f a ≤ c ↔ a ≤ g c) (hgi : ∀ c ≥ b, c ≤ f (g c)) :
    map f atTop = atTop :=
  map_atTop_eq_of_gc_preorder hf b fun c hc ↦
    ⟨g c, le_antisymm ((gc _ _ hc).2 le_rfl) (hgi c hc), (gc · c hc)⟩

theorem map_atBot_eq_of_gc_preorder
    [Preorder α] [IsDirected α (· ≥ ·)] [Preorder β] [IsDirected β (· ≥ ·)] {f : α → β}
    (hf : Monotone f) (b : β)
    (hgi : ∀ c ≤ b, ∃ x, f x = c ∧ ∀ a, c ≤ f a ↔ x ≤ a) : map f atBot = atBot :=
  map_atTop_eq_of_gc_preorder (α := αᵒᵈ) (β := βᵒᵈ) hf.dual _ hgi

theorem map_atBot_eq_of_gc [Preorder α] [IsDirected α (· ≥ ·)]
    [PartialOrder β] [IsDirected β (· ≥ ·)] {f : α → β} (g : β → α) (b' : β)
    (hf : Monotone f) (gc : ∀ a, ∀ b ≤ b', b ≤ f a ↔ g b ≤ a) (hgi : ∀ b ≤ b', f (g b) ≤ b) :
    map f atBot = atBot :=
  map_atTop_eq_of_gc (α := αᵒᵈ) (β := βᵒᵈ) _ _ hf.dual gc hgi

theorem map_val_atTop_of_Ici_subset [Preorder α] [IsDirected α (· ≤ ·)] {a : α} {s : Set α}
    (h : Ici a ⊆ s) : map ((↑) : s → α) atTop = atTop := by
  choose f hl hr using exists_ge_ge (α := α)
  have : DirectedOn (· ≤ ·) s := fun x _ y _ ↦
    ⟨f a (f x y), h <| hl _ _, (hl x y).trans (hr _ _), (hr x y).trans (hr _ _)⟩
  have : IsDirected s (· ≤ ·) := by
    rw [directedOn_iff_directed] at this
    rwa [← directed_id_iff]
  refine map_atTop_eq_of_gc_preorder (Subtype.mono_coe _) a fun c hc ↦ ?_
  exact ⟨⟨c, h hc⟩, rfl, fun _ ↦ .rfl⟩

@[simp]
theorem _root_.Nat.map_cast_int_atTop : map ((↑) : ℕ → ℤ) atTop = atTop := by
  refine map_atTop_eq_of_gc_preorder (fun _ _ ↦ Int.ofNat_le.2) 0 fun n hn ↦ ?_
  lift n to ℕ using hn
  exact ⟨n, rfl, fun _ ↦ Int.ofNat_le⟩

/-- The image of the filter `atTop` on `Ici a` under the coercion equals `atTop`. -/
@[simp]
theorem map_val_Ici_atTop [Preorder α] [IsDirected α (· ≤ ·)] (a : α) :
    map ((↑) : Ici a → α) atTop = atTop :=
  map_val_atTop_of_Ici_subset Subset.rfl

/-- The image of the filter `atTop` on `Ioi a` under the coercion equals `atTop`. -/
@[simp]
theorem map_val_Ioi_atTop [Preorder α] [IsDirected α (· ≤ ·)] [NoMaxOrder α] (a : α) :
    map ((↑) : Ioi a → α) atTop = atTop :=
  let ⟨_b, hb⟩ := exists_gt a
  map_val_atTop_of_Ici_subset <| Ici_subset_Ioi.2 hb

/-- The `atTop` filter for an open interval `Ioi a` comes from the `atTop` filter in the ambient
order. -/
theorem atTop_Ioi_eq [Preorder α] [IsDirected α (· ≤ ·)] (a : α) :
    atTop = comap ((↑) : Ioi a → α) atTop := by
  rcases isEmpty_or_nonempty (Ioi a) with h|⟨⟨b, hb⟩⟩
  · subsingleton
  · rw [← map_val_atTop_of_Ici_subset (Ici_subset_Ioi.2 hb), comap_map Subtype.coe_injective]

/-- The `atTop` filter for an open interval `Ici a` comes from the `atTop` filter in the ambient
order. -/
theorem atTop_Ici_eq [Preorder α] [IsDirected α (· ≤ ·)] (a : α) :
    atTop = comap ((↑) : Ici a → α) atTop := by
  rw [← map_val_Ici_atTop a, comap_map Subtype.coe_injective]

/-- The `atBot` filter for an open interval `Iio a` comes from the `atBot` filter in the ambient
order. -/
@[simp]
theorem map_val_Iio_atBot [Preorder α] [IsDirected α (· ≥ ·)] [NoMinOrder α] (a : α) :
    map ((↑) : Iio a → α) atBot = atBot :=
  map_val_Ioi_atTop (OrderDual.toDual a)

/-- The `atBot` filter for an open interval `Iio a` comes from the `atBot` filter in the ambient
order. -/
theorem atBot_Iio_eq [Preorder α] [IsDirected α (· ≥ ·)] (a : α) :
    atBot = comap ((↑) : Iio a → α) atBot :=
  atTop_Ioi_eq (OrderDual.toDual a)

/-- The `atBot` filter for an open interval `Iic a` comes from the `atBot` filter in the ambient
order. -/
@[simp]
theorem map_val_Iic_atBot [Preorder α] [IsDirected α (· ≥ ·)] (a : α) :
    map ((↑) : Iic a → α) atBot = atBot :=
  map_val_Ici_atTop (OrderDual.toDual a)

/-- The `atBot` filter for an open interval `Iic a` comes from the `atBot` filter in the ambient
order. -/
theorem atBot_Iic_eq [Preorder α] [IsDirected α (· ≥ ·)] (a : α) :
    atBot = comap ((↑) : Iic a → α) atBot :=
  atTop_Ici_eq (OrderDual.toDual a)

theorem tendsto_Ioi_atTop [Preorder α] [IsDirected α (· ≤ ·)]
    {a : α} {f : β → Ioi a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ioi_eq, tendsto_comap_iff, Function.comp_def]

theorem tendsto_Iio_atBot [Preorder α] [IsDirected α (· ≥ ·)]
    {a : α} {f : β → Iio a} {l : Filter β} :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : α)) l atBot :=
  tendsto_Ioi_atTop (α := αᵒᵈ)

theorem tendsto_Ici_atTop [Preorder α] [IsDirected α (· ≤ ·)]
    {a : α} {f : β → Ici a} {l : Filter β} :
    Tendsto f l atTop ↔ Tendsto (fun x => (f x : α)) l atTop := by
  rw [atTop_Ici_eq, tendsto_comap_iff, Function.comp_def]

theorem tendsto_Iic_atBot [Preorder α] [IsDirected α (· ≥ ·)]
    {a : α} {f : β → Iic a} {l : Filter β} :
    Tendsto f l atBot ↔ Tendsto (fun x => (f x : α)) l atBot :=
  tendsto_Ici_atTop (α := αᵒᵈ)

@[simp]
theorem tendsto_comp_val_Ioi_atTop [Preorder α] [IsDirected α (· ≤ ·)] [NoMaxOrder α]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Ioi a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ioi_atTop a, tendsto_map'_iff, Function.comp_def]

@[simp]
theorem tendsto_comp_val_Ici_atTop [Preorder α] [IsDirected α (· ≤ ·)]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Ici a => f x) atTop l ↔ Tendsto f atTop l := by
  rw [← map_val_Ici_atTop a, tendsto_map'_iff, Function.comp_def]

@[simp]
theorem tendsto_comp_val_Iio_atBot [Preorder α] [IsDirected α (· ≥ ·)] [NoMinOrder α]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Iio a => f x) atBot l ↔ Tendsto f atBot l :=
  tendsto_comp_val_Ioi_atTop (α := αᵒᵈ)

@[simp]
theorem tendsto_comp_val_Iic_atBot [Preorder α] [IsDirected α (· ≥ ·)]
    {a : α} {f : α → β} {l : Filter β} :
    Tendsto (fun x : Iic a => f x) atBot l ↔ Tendsto f atBot l :=
  tendsto_comp_val_Ici_atTop (α := αᵒᵈ)

theorem map_add_atTop_eq_nat (k : ℕ) : map (fun a => a + k) atTop = atTop :=
  map_atTop_eq_of_gc (· - k) k (fun _ _ h => Nat.add_le_add_right h k)
    (fun _ _ h => (Nat.le_sub_iff_add_le h).symm) fun a h => by rw [Nat.sub_add_cancel h]

theorem map_sub_atTop_eq_nat (k : ℕ) : map (fun a => a - k) atTop = atTop :=
  map_atTop_eq_of_gc (· + k) 0 (fun _ _ h => Nat.sub_le_sub_right h _)
    (fun _ _ _ => Nat.sub_le_iff_le_add) fun b _ => by rw [Nat.add_sub_cancel_right]

theorem tendsto_add_atTop_nat (k : ℕ) : Tendsto (fun a => a + k) atTop atTop :=
  le_of_eq (map_add_atTop_eq_nat k)

theorem tendsto_sub_atTop_nat (k : ℕ) : Tendsto (fun a => a - k) atTop atTop :=
  le_of_eq (map_sub_atTop_eq_nat k)

theorem tendsto_add_atTop_iff_nat {f : ℕ → α} {l : Filter α} (k : ℕ) :
    Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f atTop l :=
  show Tendsto (f ∘ fun n => n + k) atTop l ↔ Tendsto f atTop l by
    rw [← tendsto_map'_iff, map_add_atTop_eq_nat]

theorem map_div_atTop_eq_nat (k : ℕ) (hk : 0 < k) : map (fun a => a / k) atTop = atTop :=
  map_atTop_eq_of_gc (fun b => k * b + (k - 1)) 1 (fun _ _ h => Nat.div_le_div_right h)
    (fun a b _ => by rw [Nat.div_le_iff_le_mul_add_pred hk])
    fun b _ => by rw [Nat.mul_add_div hk, Nat.div_eq_of_lt, Nat.add_zero]; omega

section NeBot
variable [Preorder β] {l : Filter α} [NeBot l] {f : α → β}

theorem not_bddAbove_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto f l atTop) :
    ¬BddAbove (range f) := by
  rintro ⟨M, hM⟩
  have : ∀ x, f x ≤ M := by aesop
  have : ∅ = f ⁻¹' Ioi M := by aesop (add forward safe not_le_of_gt)
  apply Filter.empty_notMem l
  aesop (add safe Ioi_mem_atTop)

theorem not_bddBelow_of_tendsto_atBot [NoMinOrder β] (h : Tendsto f l atBot) :
    ¬BddBelow (range f) := not_bddAbove_of_tendsto_atTop (β := βᵒᵈ) h

@[deprecated (since := "2025-04-28")]
alias unbounded_of_tendsto_atTop := not_bddAbove_of_tendsto_atTop

@[deprecated (since := "2025-04-28")]
alias unbounded_of_tendsto_atBot := not_bddBelow_of_tendsto_atBot

@[deprecated (since := "2025-04-28")]
alias unbounded_of_tendsto_atTop' := not_bddAbove_of_tendsto_atTop

@[deprecated (since := "2025-04-28")]
alias unbounded_of_tendsto_atBot' := not_bddBelow_of_tendsto_atBot

end NeBot

theorem HasAntitoneBasis.eventually_subset [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) {t : Set α} (ht : t ∈ l) : ∀ᶠ i in atTop, s i ⊆ t :=
  let ⟨i, _, hi⟩ := hl.1.mem_iff.1 ht
  (eventually_ge_atTop i).mono fun _j hj => (hl.antitone hj).trans hi

protected theorem HasAntitoneBasis.tendsto [Preorder ι] {l : Filter α} {s : ι → Set α}
    (hl : l.HasAntitoneBasis s) {φ : ι → α} (h : ∀ i : ι, φ i ∈ s i) : Tendsto φ atTop l :=
  fun _t ht => mem_map.2 <| (hl.eventually_subset ht).mono fun i hi => hi (h i)

theorem HasAntitoneBasis.comp_mono [Nonempty ι] [Preorder ι] [IsDirected ι (· ≤ ·)] [Preorder ι']
    {l : Filter α}
    {s : ι' → Set α} (hs : l.HasAntitoneBasis s) {φ : ι → ι'} (φ_mono : Monotone φ)
    (hφ : Tendsto φ atTop atTop) : l.HasAntitoneBasis (s ∘ φ) :=
  ⟨hs.1.to_hasBasis
      (fun n _ => (hφ.eventually_ge_atTop n).exists.imp fun _m hm => ⟨trivial, hs.antitone hm⟩)
      fun n _ => ⟨φ n, trivial, Subset.rfl⟩,
    hs.antitone.comp_monotone φ_mono⟩

theorem HasAntitoneBasis.comp_strictMono {l : Filter α} {s : ℕ → Set α} (hs : l.HasAntitoneBasis s)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : l.HasAntitoneBasis (s ∘ φ) :=
  hs.comp_mono hφ.monotone hφ.tendsto_atTop

theorem subseq_forall_of_frequently {ι : Type*} {x : ℕ → ι} {p : ι → Prop} {l : Filter ι}
    (h_tendsto : Tendsto x atTop l) (h : ∃ᶠ n in atTop, p (x n)) :
    ∃ ns : ℕ → ℕ, Tendsto (fun n => x (ns n)) atTop l ∧ ∀ n, p (x (ns n)) := by
  choose ns hge hns using frequently_atTop.1 h
  exact ⟨ns, h_tendsto.comp (tendsto_atTop_mono hge tendsto_id), hns⟩

end Filter
