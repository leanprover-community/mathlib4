/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Flag.Counting
set_option linter.style.header false
namespace SimpleGraph

variable {α β ι : Type*} {k : ℕ}

/--
A `Flag α ι` consists of `G : SimpleGraph α` and a labelling of `ι` vertices of `G` by an
injective map `θ : ι ↪ α`. (We call this a `σ`-flag if the labelled subgraph is
`σ : SimpleGraph ι`).
-/
structure Flag (α ι : Type*) where
  G : SimpleGraph α
  θ : ι ↪ α

/--
Given a flag `F = (G, θ)` and set `t ⊆ V(G)` containing `im(θ)` `F.induce t`
is the flag induced by `t` with the same labels_eq.
-/
def Flag.induce {α ι : Type*} (F : Flag α ι) (t : Set α) (ht : ∀ i, F.θ i ∈ t) : Flag t ι :=
  ⟨F.G.induce t, ⟨fun i ↦ ⟨F.θ i, ht i⟩, fun h ↦ by simp_all⟩⟩

def Flag.induce_copy {α ι : Type*} (F : Flag α ι) {s t : Set α} (h : s = t) (hs : ∀ i, F.θ i ∈ s) :
    Flag t ι := by
  subst_vars; exact F.induce t hs

lemma Flag.induce_copy_eq {α ι : Type*} (F : Flag α ι) {s t : Set α} (h : s = t)
    (hs : ∀ i, F.θ i ∈ s) (ht : ∀ i, F.θ i ∈ t) : F.induce t ht = F.induce_copy h hs := by
  subst_vars; rfl

lemma Flag.induce_adj {α ι : Type*} (F : Flag α ι) (t : Set α) (ht : ∀ i, F.θ i ∈ t) :
    (F.induce t ht).G = (F.G.induce t) := rfl

lemma Flag.induce_labels_eq {α ι : Type*} {F : Flag α ι} (t : Set α) (ht : ∀ i, F.θ i ∈ t) {i : ι} :
    (F.induce t ht).θ i = F.θ i := rfl

/-- Added to prove `Fintype` instance later -/
def Flag_equiv_prod (α ι : Type*) : Flag α ι ≃ (SimpleGraph α) × (ι ↪ α) where
  toFun := fun F ↦ (F.G, F.θ)
  invFun := fun p ↦ { G := p.1, θ := p.2 }
  left_inv := fun F ↦ by cases F; rfl
  right_inv := fun p ↦ by cases p; rfl

/-- An embedding of flags is an embedding of the underlying graphs that preserves labels. -/
@[ext]
structure FlagEmbedding {α β ι : Type*} (F₁ : Flag α ι) (F₂ : Flag β ι) extends F₁.G ↪g F₂.G where
 labels_eq : F₂.θ = toEmbedding ∘ F₁.θ

/-- An isomorphism of flags is an isomorphism of the underlying graphs that preserves labels. -/
@[ext]
structure FlagIso {α β ι : Type*} (F₁ : Flag α ι) (F₂ : Flag β ι) extends F₁.G ≃g F₂.G where
 labels_eq : F₂.θ = toEquiv ∘ F₁.θ

@[inherit_doc] infixl:50 " ↪f " => FlagEmbedding
@[inherit_doc] infixl:50 " ≃f " => FlagIso


section test
variable {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} (e : F₁ ↪f F₂) {a : α}
#check e.toFun a

end test

@[simp]
lemma FlagEmbedding.labels_subset_range {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι}
    (e : F₁ ↪f F₂) : Set.range F₂.θ ⊆ Set.range e.toFun := by
  intro i hi
  rw [e.labels_eq] at hi
  aesop

theorem FlagEmbedding.toRelEmbedding_injective {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} :
    Function.Injective (FlagEmbedding.toRelEmbedding : F₁ ↪f F₂ → (F₁.G ↪g F₂.G)) := by
  rintro ⟨f, _⟩ ⟨g, _⟩; simp

variable [Fintype α] [Fintype β] (G : SimpleGraph α) (H : SimpleGraph β)

noncomputable instance FlagEmbedding.instfintypeOfEmbeddings {α β ι : Type*} {F₁ : Flag α ι}
    {F₂ : Flag β ι} [Fintype α] [Fintype β] : Fintype (F₁ ↪f F₂) := by
  exact Fintype.ofInjective _ FlagEmbedding.toRelEmbedding_injective

variable {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} {e : F₁ ↪f F₂}

lemma FlagIso.symm {α β ι : Type*} {F₁ : Flag α ι} {F₂ : Flag β ι} (e : F₁ ≃f F₂)
     : F₁.θ = e.symm ∘ F₂.θ := by
  ext x; simp [e.labels_eq]

/--
`F` is a `σ`-flag iff the labelled subgraph given by `θ` is `σ`
-/
def Flag.IsSigma (F : Flag α ι) (σ : SimpleGraph ι) : Prop :=
  F.G.comap F.θ = σ

lemma Flag.isSigma_self (F : Flag α ι) : F.IsSigma (F.G.comap F.θ) := rfl

lemma Flag.isSigma_of_embedding {α β ι : Type*} {σ : SimpleGraph ι} {F₁ : Flag α ι}
    {F₂ : Flag β ι} (e : F₁ ↪f F₂)  (h1 : F₁.IsSigma σ) : F₂.IsSigma σ := by
  rw [IsSigma, e.labels_eq, ← h1] at *
  ext; simp

variable {α ι  : Type*} [Fintype α] [Fintype ι] [DecidableEq α]

noncomputable instance : Fintype (Flag α ι) :=  Fintype.ofEquiv _ (Flag_equiv_prod α ι).symm

open Classical in
/--
The Finset of all `σ`-flags with vertex type `α` (where both `α` and `ι` are finite).
-/
noncomputable def SigmaFlags (σ : SimpleGraph ι) : Finset (Flag α ι) := {F | F.IsSigma σ}

/--
Flag embeddings of `F₁` in `F₂[t]` are equivalent to embeddings of `F₁` in `F₂` that map into `t`.
(Note: that `F₂[t]` is only defined if all the labels_eq of `F₂` lie in `t`).
-/
def Flag.induceEquiv (F₁ : Flag α ι) (F₂ : Flag β ι) (t : Set β) (h : ∀ i, F₂.θ i ∈ t) :
    F₁ ↪f (F₂.induce t h) ≃ {e : F₁ ↪f F₂ | Set.range e.toEmbedding ⊆ t}
    where
  toFun := fun e ↦ ⟨⟨Embedding.induce _|>.comp e.toRelEmbedding, by
                ext; rw [← F₂.induce_labels_eq t h, e.labels_eq]; rfl⟩, by rintro x ⟨y , rfl⟩; simp⟩
  invFun := fun e ↦ ⟨⟨⟨fun a : α ↦ ⟨e.1.toRelEmbedding a , by apply e.2; simp⟩, fun _ ↦ by simp⟩,
                by simp [Flag.induce_adj]⟩, by ext i; simp [F₂.induce_labels_eq t h, e.1.labels_eq]⟩
  left_inv := fun e ↦ by ext; simp
  right_inv := fun e ↦ by ext; simp

/--
Two flag embeddings `e₁ : F₁ ↪f F` and `e₂ : F₂ ↪f F` are compatible if they are in
`general position`, i.e. the intersection of their images is exactly the set of labelled vertices
of `F`.
-/
@[simp]
def FlagEmbedding.Compat {β : Type*} {F₁ : Flag β ι} {F₂ : Flag β ι} {F : Flag α ι}
    (e₁ : F₁ ↪f F) (e₂ : F₂ ↪f F) : Prop :=
  ∀ b₁ b₂, e₁.toRelEmbedding b₁ = e₂.toRelEmbedding b₂ → ∃ i, F.θ i = e₁.toRelEmbedding b₁

omit [Fintype α] [Fintype ι] [DecidableEq α] in
lemma FlagEmbedding.Compat.symm {β : Type*} {F₁ F₂ : Flag β ι} {F : Flag α ι} {e₁ : F₁ ↪f F}
    {e₂ : F₂ ↪f F} (h : e₁.Compat e₂) : e₂.Compat e₁ := by
  simp only [FlagEmbedding.Compat, RelEmbedding.coe_toEmbedding] at *
  intro b₁ b₂ he
  obtain ⟨i, he'⟩ := h _ _ he.symm
  use i, (he ▸ he')

omit [Fintype α] [Fintype ι] [DecidableEq α] in
lemma FlagEmbedding.compat_iff_inter_eq {β : Type*} {F₁ F₂ : Flag β ι} {F : Flag α ι} {e₁ : F₁ ↪f F}
    {e₂ : F₂ ↪f F} : e₁.Compat e₂ ↔ Set.range e₁.toFun ∩ Set.range e₂.toFun =
        Set.range F.θ := by
  constructor <;> intro h
  · apply subset_antisymm
    · intro a; simp only [Set.mem_inter_iff, Set.mem_range]
      rintro ⟨⟨y,rfl⟩,⟨z, hz⟩⟩;
      obtain ⟨i, hi⟩ := h _ _ hz.symm
      use i, hi
    · rw [Set.subset_inter_iff]
      exact ⟨e₁.labels_subset_range, e₂.labels_subset_range⟩
  · intro b₁ b₂ hb
    simp_rw [← Set.mem_range,← h, Set.mem_inter_iff]
    nth_rw 2 [hb]
    simp

/-!
## TODO:
  1. Prove that:

    ‖{(e₁, e₂) : (F₁ ↪f F) × (F₁ ↪f F) // ¬ e₁.Compat e₂}‖ ≤
      (‖β‖!)² * #{ (A, B) | A,B ‖β‖-sets in α, with F.θ.image ⊆ A ∩ B ≠ F.θ.image}

    (e₁, e₂) ↦ {(A, B) : A,B ‖β‖-sets in α, with F.θ.image ⊆ A ∩ B ≠ F.θ.image}

      Give C := F.θ.image (so `#C = ‖ι‖` )
      #{(A, B) | #A = #B = ‖β‖ ∧ A ∩ B = C} =
                      ((‖α‖ - ‖ι‖).choose (‖β‖ - ‖ι‖)) * ((‖α‖ - ‖β‖).choose (‖β‖ - ‖ι‖))


  2. We can count compatible pairs by averaging over induced subflags ✓

-/

variable {k m n : ℕ}
local notation "‖" x "‖" => Fintype.card x

open Finset



/-- **The principle of counting induced flags by averaging**
If `F` is an  `α, ι`-flag and `F₁` is a `β, ι`-flag, then we can count embeddings of `F₁` in `F`
using `#(F₁ ↪f F) * (choose (‖α‖ - ‖β‖) (k - ‖β‖))` is equal to the sum of the number of embeddings
`F₁ ↪f (F.induce t)` over subsets `t` of `α` of size `k`, that contain the image of `F.θ`, i.e.
`t` contains all the labelled vertices of `F` (otherwise there are no embeddings of `F₁` into
`F.induce t`, since any such embedding preserves the labels).
-/
lemma Flag.sum_card_embeddings_induce_eq (F₁ : Flag β ι) (F : Flag α ι) [Fintype β] {k : ℕ}
  (hk : ‖β‖ ≤ k) : ∑ t : Finset α with #t = k,
    (if ht : ∀ i, F.θ i ∈ t then  ‖F₁ ↪f (F.induce t ht)‖ else 0)
                              = ‖F₁ ↪f F‖ * Nat.choose (‖α‖ - ‖β‖) (k - ‖β‖) := by
  classical
  calc
  _ = ∑ t : Finset α , ∑ e : F₁ ↪f F,
          ite (#t = k ∧ (∀ i, F.θ i ∈ t) ∧ Set.range e.toEmbedding ⊆ t) 1 0 := by
    simp_rw [Fintype.card_congr <| Flag.induceEquiv .., dite_eq_ite, sum_filter, sum_boole,
              Set.coe_setOf, Fintype.card_subtype]
    congr with t
    split_ifs with h1 h2
    · congr with e
      constructor <;> intro he
      · exact  ⟨h1 , h2, he⟩
      · exact he.2.2
    · contrapose! h2
      obtain ⟨e, he⟩ := card_ne_zero.1 h2.symm
      simp only [mem_filter, mem_univ, true_and] at he
      exact he.2.1
    · contrapose! h1
      obtain ⟨e, he⟩ := card_ne_zero.1 h1.symm
      simp only [mem_filter, mem_univ, true_and] at he
      exact he.1
  _ = _ := by
    rw [sum_comm, ← card_univ (α := (F₁ ↪f F)), card_eq_sum_ones, sum_mul, one_mul]
    congr with e
    have : ∀ (i : ι), F.θ i ∈ Set.range e.toEmbedding := fun i ↦ ⟨F₁.θ i, by simp [e.labels_eq]⟩
    calc
    _ =  #{t : Finset α | #t = k  ∧ Set.range e.toEmbedding ⊆ t} := by
      rw [sum_boole]
      congr with t; simp only [and_congr_right_iff, and_iff_right_iff_imp]
      intro hk hs i
      exact hs <| this i
    _ = _ := by
      have hs : #((Set.range e.toEmbedding).toFinset) = ‖β‖ :=
        Set.toFinset_range e.toEmbedding ▸ card_image_of_injective _ e.toEmbedding.injective
      rw [← hs, ← card_supersets (hs ▸ hk)]
      congr with t
      constructor <;> intro ⟨ht1, ht2⟩ <;> exact ⟨ht1, fun x hx ↦ ht2 (by simpa using hx)⟩

/--
The set of all compatible embeddings of a pair of `(β,ι)`-flags in a `(α,ι)`-flag.
-/
abbrev compat_pairs (F₁₂ : Flag β ι × Flag β ι) (F : Flag α ι) :=
  {(e₁, e₂) : F₁₂.1 ↪f F × F₁₂.2 ↪f F | e₁.Compat e₂}

@[inherit_doc] infixl:50 " ↪f₂ " => compat_pairs

abbrev compat_pair_to_pair {F₁₂ : Flag β ι × Flag β ι} {F : Flag α ι} :
  F₁₂ ↪f₂ F → (F₁₂.1 ↪f F) × (F₁₂.2 ↪f F) := fun e ↦ e.1

lemma compat_pairs_inj {α β ι : Type*} {F : Flag α ι} {F₁₂ : Flag β ι × Flag β ι}:
  Function.Injective (compat_pair_to_pair : F₁₂ ↪f₂ F → (F₁₂.1 ↪f F) × (F₁₂.2 ↪f F)) := by
  rintro ⟨f, _⟩ ⟨g, _⟩; simp

noncomputable instance FlagEmbedding.instfintypeOfCompatEmbeddings {α β ι : Type*} {F : Flag α ι}
    {F₁₂ : Flag β ι × Flag β ι} [Fintype α] [Fintype β] : Fintype (F₁₂ ↪f₂ F) :=
  Fintype.ofInjective _ compat_pairs_inj

/--
Compatible pairs of flag embeddings of `(F₁, F₂)` into `F[t]` are equivalent to compatible pairs
of flag embeddings of `(F₁,F₂)` into `F` that map into `t`.
(Note: that `F[t]` is only defined if all the labels_eq of `F₂` lie in `t`).
-/
def Flag₂.induceEquiv (F₁ F₂ : Flag β ι) (F : Flag α ι) (t : Set α ) (h : ∀ i, F.θ i ∈ t) :
    (F₁, F₂) ↪f₂ (F.induce t h) ≃
      {e : (F₁, F₂) ↪f₂ F | Set.range e.1.1.toFun ⊆ t ∧ Set.range e.1.2.toFun ⊆ t}
    where
  toFun := fun e ↦ by
    let f₁ : F₁ ↪f F:=⟨Embedding.induce _|>.comp e.1.1.toRelEmbedding,
      by ext i; rw [← F.induce_labels_eq t h, e.1.1.labels_eq]; rfl⟩
    let f₂ : F₂ ↪f F:=⟨Embedding.induce _|>.comp e.1.2.toRelEmbedding,
      by ext i; rw [← F.induce_labels_eq t h, e.1.2.labels_eq];rfl⟩
    have he : e.val.1.Compat e.val.2 := e.2
    have he1: ∀ b, e.val.1.toRelEmbedding b = f₁.toRelEmbedding b := by intro b; rfl
    have he2: ∀ b, e.val.2.toRelEmbedding b = f₂.toRelEmbedding b := by intro b; rfl
    have hf : f₁.Compat f₂ := by
      intro x y heq
      have he3 : e.val.1.toRelEmbedding x = e.val.2.toRelEmbedding y := by
        rwa [Subtype.ext_iff, he1, he2]
      obtain ⟨i, heq'⟩ := he x y he3
      have : (F.induce t h).θ i = F.θ i := F.induce_labels_eq t h
      use i, by rw [← he1 x, ← this, ← Subtype.ext_iff,heq']
    refine ⟨⟨(f₁,f₂), hf⟩,?_⟩
    simp; constructor <;> intro a ⟨b,hb⟩
    · rw [← he1] at hb; rw [← hb]; simp
    · rw [← he2] at hb; rw [← hb]; simp
  invFun := fun e ↦ by
    have : ∀ b, e.1.1.1.toRelEmbedding b ∈ t := by intro b; apply e.2.1; simp
    let f₁ : (F₁ ↪f (F.induce t h)) := ⟨⟨⟨fun b : β ↦ ⟨e.1.1.1.toRelEmbedding b, e.2.1 (by simp)⟩,
      fun _ _ hb ↦ by simpa using hb⟩, by simp [Flag.induce_adj]⟩,
      by ext i; simp [F.induce_labels_eq t h, e.1.1.1.labels_eq]⟩
    let f₂ : (F₂ ↪f (F.induce t h)) := ⟨⟨⟨fun b : β ↦ ⟨e.1.1.2.toRelEmbedding b, e.2.2 (by simp)⟩,
      fun _ _ hb ↦ by simpa using hb⟩, by simp [Flag.induce_adj]⟩,
      by ext i; simp [F.induce_labels_eq t h, e.1.1.2.labels_eq]⟩
    refine ⟨(f₁,f₂), ?_⟩
    have : ∀ b₁ b₂, e.1.1.1.toRelEmbedding b₁ = e.1.1.2.toRelEmbedding b₂ →
      ∃ i, F.θ i = e.1.1.1.toRelEmbedding b₁  := e.1.2
    simp only [Set.mem_setOf_eq, FlagEmbedding.Compat]
    have he1: ∀ b, e.1.1.1.toRelEmbedding b = f₁.toRelEmbedding b := by intro b; rfl
    have he2: ∀ b, e.1.1.2.toRelEmbedding b = f₂.toRelEmbedding b := by intro b; rfl
    intro b₁ b₂ hb
    have heq : e.1.1.1.toRelEmbedding b₁ = e.1.1.2.toRelEmbedding b₂ := by
      rwa [he1, he2, ← Subtype.ext_iff]
    obtain ⟨i, hi⟩ := this _ _ heq
    use i
    have :=F.induce_labels_eq t h (i := i)
    rwa [← this, he1, ←Subtype.ext_iff] at hi
  left_inv := fun e ↦ by ext <;> dsimp
  right_inv := fun e ↦ by ext <;> dsimp

open Classical in
/-- **The principle of counting induced pairs of compatible flag embeddings by averaging**
If `F : Flag α ι` and `F₁, F₂ : Flag β ι` then
`#((F₁, F₂) ↪f G) * (choose (‖α‖ - (2 * ‖β‖ - ‖ι‖)) (k - (2 * ‖β‖ - ‖ι‖)))` is equal to the sum of
the number of embeddings
`(F₁, F₂) ↪f₂ (F.induce t)` over subsets `t` of `α` of size `k`, for any `2 * ‖β‖ - ‖ι‖ ≤ k`.
(Note: the inequality is required for there to exist any compatible pair of flag embeddings into
a subset of size `k` since the two embeddings meet in the labels only i.e. in a `‖ι‖`-set and each
have image of size `‖β‖`).
-/
lemma Flag.sum_card_embeddings_induce_eq_compat (F₁ F₂ : Flag β ι) (F : Flag α ι) [Fintype β]
  {k : ℕ} (hk : 2 * ‖β‖ - ‖ι‖ ≤ k) : ∑ t : Finset α with #t = k,
    (if ht : ∀ i, F.θ i ∈ t then  ‖(F₁, F₂) ↪f₂ (F.induce t ht)‖ else 0)
              = ‖(F₁, F₂) ↪f₂ F‖ * Nat.choose (‖α‖ - (2 * ‖β‖ - ‖ι‖) ) (k - (2 * ‖β‖ - ‖ι‖)) := by
  calc
  _ = ∑ t : Finset α , ∑ e : ((F₁,F₂) ↪f₂ F),
          ite (#t = k ∧ (∀ i, F.θ i ∈ t) ∧ Set.range e.1.1.toFun ⊆ t
            ∧ Set.range e.1.2.toFun ⊆ t) 1 0 := by
    simp_rw [Fintype.card_congr <| Flag₂.induceEquiv .., dite_eq_ite]
    rw [sum_filter];
    simp only [Set.coe_setOf, FlagEmbedding.Compat, Set.mem_setOf_eq, sum_boole, Nat.cast_id]
    congr with t
    split_ifs with h1 h2
    · simp_rw [h1, h2]
      simp only [Fintype.card_subtype, implies_true, true_and]
      convert rfl
    · by_contra! he
      obtain ⟨e, he⟩ := card_ne_zero.1 he.symm
      simp only [mem_filter, mem_univ, true_and] at he
      exact h2 he.2.1
    · contrapose! h1
      obtain ⟨e, he⟩ := card_ne_zero.1 h1.symm
      simp only [mem_filter, mem_univ, true_and] at he
      exact he.1
  _ = _ := by
    rw [sum_comm, ← card_univ (α := ((F₁,F₂) ↪f₂ F)), card_eq_sum_ones, sum_mul, one_mul]
    congr with e
    have he1 : ∀ (i : ι), F.θ i ∈ Set.range e.1.1.toFun :=
      fun i ↦ ⟨F₁.θ i, by simp [e.1.1.labels_eq]⟩
    calc
    _ = #{t : Finset α | #t = k ∧ Set.range e.1.1.toFun ⊆ t
              ∧ Set.range e.1.2.toFun ⊆ t} := by
      simp only [sum_boole,Set.mem_setOf_eq, FlagEmbedding.Compat, and_self]
      congr with t; simp only [and_congr_right_iff, and_iff_right_iff_imp]
      intro hk hs i
      exact hs.1 <| he1 i
    _ =  #{t : Finset α | #t = k ∧
      Set.range e.1.1.toFun ∪ Set.range e.1.2.toFun ⊆ t} := by
      congr with t; simp
    _ = _ := by
      have hint := FlagEmbedding.compat_iff_inter_eq.1 e.2
      have hs1 : #((Set.range e.1.1.toFun).toFinset) = ‖β‖ := Set.toFinset_range
        e.1.1.toFun ▸ card_image_of_injective _ e.1.1.toRelEmbedding.injective
      have hs2 : #((Set.range e.1.2.toFun).toFinset) = ‖β‖ := Set.toFinset_range
        e.1.2.toFun ▸ card_image_of_injective _ e.1.2.toRelEmbedding.injective
      have hl : #(Set.range F.θ).toFinset = ‖ι‖ :=
        Set.toFinset_range F.θ ▸ card_image_of_injective _ F.θ.injective
      have : #((Set.range e.1.1.toFun ∪ Set.range e.1.2.toFun).toFinset)
        = 2* ‖β‖- ‖ι‖ := by
        simp_rw [Set.toFinset_union, card_union, hs1, hs2, ← Set.toFinset_inter, hint, hl, two_mul]
      convert card_supersets (this ▸ hk) with t <;> try exact this.symm
      · constructor <;> intro h <;> intro _ hx
        · exact Finset.mem_coe.1 <| h <| Set.mem_toFinset.1 hx
        · exact h <| Set.mem_toFinset.2 hx




end SimpleGraph
