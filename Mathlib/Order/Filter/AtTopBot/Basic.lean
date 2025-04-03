/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
import Mathlib.Order.Filter.Bases
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Filter.AtTopBot.Prod

/-!
# Basic results on `Filter.atTop` and `Filter.atBot` filters

In this file we prove many lemmas like “if `f → +∞`, then `f ± c → +∞`”.
-/

variable {ι ι' α β γ : Type*}

open Set

namespace Filter

theorem eventually_forall_ge_atTop [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atTop, ∀ y, x ≤ y → p y) ↔ ∀ᶠ x in atTop, p x := by
  refine ⟨fun h ↦ h.mono fun x hx ↦ hx x le_rfl, fun h ↦ ?_⟩
  rcases (hasBasis_iInf_principal_finite _).eventually_iff.1 h with ⟨S, hSf, hS⟩
  refine mem_iInf_of_iInter hSf (V := fun x ↦ Ici x.1) (fun _ ↦ Subset.rfl) fun x hx y hy ↦ ?_
  simp only [mem_iInter] at hS hx
  exact hS fun z hz ↦ le_trans (hx ⟨z, hz⟩) hy

theorem eventually_forall_le_atBot [Preorder α] {p : α → Prop} :
    (∀ᶠ x in atBot, ∀ y, y ≤ x → p y) ↔ ∀ᶠ x in atBot, p x :=
  eventually_forall_ge_atTop (α := αᵒᵈ)

theorem Tendsto.eventually_forall_ge_atTop [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atTop) (h_evtl : ∀ᶠ x in atTop, p x) :
    ∀ᶠ x in l, ∀ y, f x ≤ y → p y := by
  rw [← Filter.eventually_forall_ge_atTop] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

theorem Tendsto.eventually_forall_le_atBot [Preorder β] {l : Filter α}
    {p : β → Prop} {f : α → β} (hf : Tendsto f l atBot) (h_evtl : ∀ᶠ x in atBot, p x) :
    ∀ᶠ x in l, ∀ y, y ≤ f x → p y := by
  rw [← Filter.eventually_forall_le_atBot] at h_evtl; exact (h_evtl.comap f).filter_mono hf.le_comap

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

theorem extraction_of_frequently_atTop' {P : ℕ → Prop} (h : ∀ N, ∃ n > N, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  choose u hu hu' using h
  refine ⟨fun n => u^[n + 1] 0, strictMono_nat_of_lt_succ fun n => ?_, fun n => ?_⟩
  · exact Trans.trans (hu _) (Function.iterate_succ_apply' _ _ _).symm
  · simpa only [Function.iterate_succ_apply'] using hu' _

theorem extraction_of_frequently_atTop {P : ℕ → Prop} (h : ∃ᶠ n in atTop, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, P (φ n) := by
  rw [frequently_atTop'] at h
  exact extraction_of_frequently_atTop' h

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

theorem Eventually.atTop_of_arithmetic {p : ℕ → Prop} {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ k < n, ∀ᶠ a in atTop, p (n * a + k)) : ∀ᶠ a in atTop, p a := by
  simp only [eventually_atTop] at hp ⊢
  choose! N hN using hp
  refine ⟨(Finset.range n).sup (n * N ·), fun b hb => ?_⟩
  rw [← Nat.div_add_mod b n]
  have hlt := Nat.mod_lt b hn.bot_lt
  refine hN _ hlt _ ?_
  rw [ge_iff_le, Nat.le_div_iff_mul_le hn.bot_lt, mul_comm]
  exact (Finset.le_sup (f := (n * N ·)) (Finset.mem_range.2 hlt)).trans hb

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

-- @[nolint ge_or_gt] -- Porting note: restore attribute
theorem exists_le_of_tendsto_atBot (h : Tendsto u atTop atBot) :
    ∀ a b, ∃ a' ≥ a, u a' ≤ b := exists_le_of_tendsto_atTop (β := βᵒᵈ) h

theorem exists_lt_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto u atTop atTop) (a : α) (b : β) :
    ∃ a' ≥ a, b < u a' := by
  obtain ⟨b', hb'⟩ := exists_gt b
  rcases exists_le_of_tendsto_atTop h a b' with ⟨a', ha', ha''⟩
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩

-- @[nolint ge_or_gt] -- Porting note: restore attribute
theorem exists_lt_of_tendsto_atBot [NoMinOrder β] (h : Tendsto u atTop atBot) :
    ∀ a b, ∃ a' ≥ a, u a' < b := exists_lt_of_tendsto_atTop (β := βᵒᵈ) h

end IsDirected

section IsCodirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] {F : Filter β} {u : α → β}

theorem inf_map_atBot_neBot_iff : NeBot (F ⊓ map u atBot) ↔ ∀ U ∈ F, ∀ N, ∃ n ≤ N, u n ∈ U :=
  inf_map_atTop_neBot_iff (α := αᵒᵈ)

end IsCodirected

/-- If `u` is a sequence which is unbounded above,
then after any point, it reaches a value strictly greater than all previous values.
-/
theorem high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β} (hu : Tendsto u atTop atTop) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u k < u n := by
  intro N
  obtain ⟨k : ℕ, - : k ≤ N, hku : ∀ l ≤ N, u l ≤ u k⟩ : ∃ k ≤ N, ∀ l ≤ N, u l ≤ u k :=
    exists_max_image _ u (finite_le_nat N) ⟨N, le_refl N⟩
  have ex : ∃ n ≥ N, u k < u n := exists_lt_of_tendsto_atTop hu _ _
  obtain ⟨n : ℕ, hnN : n ≥ N, hnk : u k < u n, hn_min : ∀ m, m < n → N ≤ m → u m ≤ u k⟩ :
      ∃ n ≥ N, u k < u n ∧ ∀ m, m < n → N ≤ m → u m ≤ u k := by
    rcases Nat.findX ex with ⟨n, ⟨hnN, hnk⟩, hn_min⟩
    push_neg at hn_min
    exact ⟨n, hnN, hnk, hn_min⟩
  use n, hnN
  rintro (l : ℕ) (hl : l < n)
  have hlk : u l ≤ u k := by
    rcases (le_total l N : l ≤ N ∨ N ≤ l) with H | H
    · exact hku l H
    · exact hn_min l hl H
  calc
    u l ≤ u k := hlk
    _ < u n := hnk

-- see Note [nolint_ge]
/-- If `u` is a sequence which is unbounded below,
then after any point, it reaches a value strictly smaller than all previous values.
-/
-- @[nolint ge_or_gt] Porting note: restore attribute
theorem low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β} (hu : Tendsto u atTop atBot) :
    ∀ N, ∃ n ≥ N, ∀ k < n, u n < u k :=
  @high_scores βᵒᵈ _ _ _ hu

/-- If `u` is a sequence which is unbounded above,
then it `Frequently` reaches a value strictly greater than all previous values.
-/
theorem frequently_high_scores [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ᶠ n in atTop, ∀ k < n, u k < u n := by
  simpa [frequently_atTop] using high_scores hu

/-- If `u` is a sequence which is unbounded below,
then it `Frequently` reaches a value strictly smaller than all previous values.
-/
theorem frequently_low_scores [LinearOrder β] [NoMinOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atBot) : ∃ᶠ n in atTop, ∀ k < n, u n < u k :=
  @frequently_high_scores βᵒᵈ _ _ _ hu

theorem strictMono_subseq_of_tendsto_atTop [LinearOrder β] [NoMaxOrder β] {u : ℕ → β}
    (hu : Tendsto u atTop atTop) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  let ⟨φ, h, h'⟩ := extraction_of_frequently_atTop (frequently_high_scores hu)
  ⟨φ, h, fun _ m hnm => h' m _ (h hnm)⟩

theorem strictMono_subseq_of_id_le {u : ℕ → ℕ} (hu : ∀ n, n ≤ u n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictMono (u ∘ φ) :=
  strictMono_subseq_of_tendsto_atTop (tendsto_atTop_mono hu tendsto_id)

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

theorem eventually_atBot_prod_self [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ k l, k ≤ a → l ≤ a → p (k, l) := by
  simp [← prod_atBot_atBot_eq, (@atBot_basis α _ _).prod_self.eventually_iff]

theorem eventually_atTop_prod_self [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k l, a ≤ k → a ≤ l → p (k, l) :=
  eventually_atBot_prod_self (α := αᵒᵈ)

theorem eventually_atBot_prod_self'  [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atBot, p x) ↔ ∃ a, ∀ k ≤ a, ∀ l ≤ a, p (k, l) := by
  simp only [eventually_atBot_prod_self, forall_cond_comm]

theorem eventually_atTop_prod_self' [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    {p : α × α → Prop} : (∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ k ≥ a, ∀ l ≥ a, p (k, l) := by
  simp only [eventually_atTop_prod_self, forall_cond_comm]

theorem eventually_atTop_curry [Preorder α] [Preorder β] {p : α × β → Prop}
    (hp : ∀ᶠ x : α × β in Filter.atTop, p x) : ∀ᶠ k in atTop, ∀ᶠ l in atTop, p (k, l) := by
  rw [← prod_atTop_atTop_eq] at hp
  exact hp.curry

theorem eventually_atBot_curry [Preorder α] [Preorder β] {p : α × β → Prop}
    (hp : ∀ᶠ x : α × β in Filter.atBot, p x) : ∀ᶠ k in atBot, ∀ᶠ l in atBot, p (k, l) :=
  @eventually_atTop_curry αᵒᵈ βᵒᵈ _ _ _ hp

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
    -- Porting note: there was a parse error in `calc`, use `simp` instead
    (fun a b _ => by rw [Nat.div_le_iff_le_mul_add_pred hk])
    fun b _ => by rw [Nat.mul_add_div hk, Nat.div_eq_of_lt, add_zero]; omega

section IsDirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)] [Preorder β] {f : α → β}

theorem unbounded_of_tendsto_atTop [NoMaxOrder β] (h : Tendsto f atTop atTop) :
    ¬BddAbove (range f) := by
  rintro ⟨M, hM⟩
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp (h <| Ioi_mem_atTop M)
  apply lt_irrefl M
  calc
    M < f a := ha a le_rfl
    _ ≤ M := hM (Set.mem_range_self a)

theorem unbounded_of_tendsto_atBot [NoMinOrder β] (h : Tendsto f atTop atBot) :
    ¬BddBelow (range f) := unbounded_of_tendsto_atTop (β := βᵒᵈ) h

end IsDirected

section IsCodirected
variable [Nonempty α] [Preorder α] [IsDirected α (· ≥ ·)] [Preorder β] {f : α → β}

theorem unbounded_of_tendsto_atTop' [NoMaxOrder β] (h : Tendsto f atBot atTop) :
    ¬BddAbove (range f) := unbounded_of_tendsto_atTop (α := αᵒᵈ) h

theorem unbounded_of_tendsto_atBot' [NoMinOrder β] (h : Tendsto f atBot atBot) :
    ¬BddBelow (range f) := unbounded_of_tendsto_atTop (α := αᵒᵈ) (β := βᵒᵈ) h

end IsCodirected

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

/-- Given an antitone basis `s : ℕ → Set α` of a filter, extract an antitone subbasis `s ∘ φ`,
`φ : ℕ → ℕ`, such that `m < n` implies `r (φ m) (φ n)`. This lemma can be used to extract an
antitone basis with basis sets decreasing "sufficiently fast". -/
theorem HasAntitoneBasis.subbasis_with_rel {f : Filter α} {s : ℕ → Set α}
    (hs : f.HasAntitoneBasis s) {r : ℕ → ℕ → Prop} (hr : ∀ m, ∀ᶠ n in atTop, r m n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ ⦃m n⦄, m < n → r (φ m) (φ n)) ∧ f.HasAntitoneBasis (s ∘ φ) := by
  rsuffices ⟨φ, hφ, hrφ⟩ : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m n, m < n → r (φ m) (φ n)
  · exact ⟨φ, hφ, hrφ, hs.comp_strictMono hφ⟩
  have : ∀ t : Set ℕ, t.Finite → ∀ᶠ n in atTop, ∀ m ∈ t, m < n ∧ r m n := fun t ht =>
    (eventually_all_finite ht).2 fun m _ => (eventually_gt_atTop m).and (hr _)
  rcases seq_of_forall_finite_exists fun t ht => (this t ht).exists with ⟨φ, hφ⟩
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_swap.2 hφ.1, forall_swap.2 hφ.2⟩

theorem subseq_forall_of_frequently {ι : Type*} {x : ℕ → ι} {p : ι → Prop} {l : Filter ι}
    (h_tendsto : Tendsto x atTop l) (h : ∃ᶠ n in atTop, p (x n)) :
    ∃ ns : ℕ → ℕ, Tendsto (fun n => x (ns n)) atTop l ∧ ∀ n, p (x (ns n)) := by
  choose ns hge hns using frequently_atTop.1 h
  exact ⟨ns, h_tendsto.comp (tendsto_atTop_mono hge tendsto_id), hns⟩

end Filter

open Filter Finset

namespace Nat

theorem eventually_pow_lt_factorial_sub (c d : ℕ) : ∀ᶠ n in atTop, c ^ n < (n - d)! := by
  rw [eventually_atTop]
  refine ⟨2 * (c ^ 2 + d + 1), ?_⟩
  intro n hn
  obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain (rfl | c0) := c.eq_zero_or_pos
  · simp [Nat.two_mul, ← Nat.add_assoc, Nat.add_right_comm _ 1, Nat.factorial_pos]
  refine (Nat.le_mul_of_pos_right _ (Nat.pow_pos (n := d') c0)).trans_lt ?_
  convert_to (c ^ 2) ^ (c ^ 2 + d' + d + 1) < (c ^ 2 + (c ^ 2 + d' + d + 1) + 1)!
  · rw [← pow_mul, ← pow_add]
    congr 1
    omega
  · congr 1
    omega
  refine (lt_of_lt_of_le ?_ Nat.factorial_mul_pow_le_factorial).trans_le <|
    (factorial_le (Nat.le_succ _))
  rw [← one_mul (_ ^ _ : ℕ)]
  apply Nat.mul_lt_mul_of_le_of_lt
  · exact Nat.one_le_of_lt (Nat.factorial_pos _)
  · exact Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)
  · exact (Nat.factorial_pos _)

theorem eventually_mul_pow_lt_factorial_sub (a c d : ℕ) :
    ∀ᶠ n in atTop, a * c ^ n < (n - d)! := by
  filter_upwards [Nat.eventually_pow_lt_factorial_sub (a * c) d, Filter.eventually_gt_atTop 0]
    with n hn hn0
  rw [mul_pow] at hn
  exact (Nat.mul_le_mul_right _ (Nat.le_self_pow hn0.ne' _)).trans_lt hn

@[deprecated eventually_pow_lt_factorial_sub (since := "2024-09-25")]
theorem exists_pow_lt_factorial (c : ℕ) : ∃ n0 > 1, ∀ n ≥ n0, c ^ n < (n - 1)! :=
  let ⟨n0, h⟩ := (eventually_pow_lt_factorial_sub c 1).exists_forall_of_atTop
  ⟨max n0 2, by omega, fun n hn ↦ h n (by omega)⟩

@[deprecated eventually_mul_pow_lt_factorial_sub (since := "2024-09-25")]
theorem exists_mul_pow_lt_factorial (a : ℕ) (c : ℕ) : ∃ n0, ∀ n ≥ n0, a * c ^ n < (n - 1)! :=
  (eventually_mul_pow_lt_factorial_sub a c 1).exists_forall_of_atTop

end Nat
