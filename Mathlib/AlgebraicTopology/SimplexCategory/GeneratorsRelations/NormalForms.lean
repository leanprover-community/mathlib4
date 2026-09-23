/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.EpiMono
/-! # Normal forms for morphisms in `SimplexCategoryGenRel`.

In this file, we establish that `P_δ` and `P_σ` morphisms in `SimplexCategoryGenRel`
each admits a normal form.

In both cases, the normal forms are encoded as an integer `m`, and a strictly increasing
list of integers `[i₀,…,iₙ]` such that `iₖ ≤ m + k` for all `k`. We define a predicate
`isAdmissible m : List ℕ → Prop` encoding this property. And provide some lemmas to help
work with such lists.

Normal forms for `P_σ` morphisms are encoded by `m`-admissible lists, in which case the list
`[i₀,…,iₙ]` represents the morphism `σ iₙ ≫ ⋯ ≫ σ i₀ : .mk (m + n) ⟶ .mk n`.

Normal forms for `P_δ` morphisms are encoded by `(m + 1)`-admissible lists, in which case the list
`[i₀,…,iₙ]` represents the morphism `δ i₀ ≫ ⋯ ≫ δ iₙ : .mk n ⟶ .mk (m + n)`.

The results in this file are to be treated as implementation-only, and they only serve as stepping
stones towards proving that the canonical functor
`toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory` is an equivalence.

## References:
* [Kerodon Tag 04FQ](https://kerodon.net/tag/04FQ)
* [Kerodon Tag 04FT](https://kerodon.net/tag/04FT)

## TODOs:
- Show that every `P_δ` admits a unique normal form.
-/

@[expose] public section

namespace SimplexCategoryGenRel

open CategoryTheory

section AdmissibleLists
-- Impl. note: We are not bundling admissible lists as a subtype of `List ℕ` so that it remains
-- easier to perform inductive constructions and proofs on such lists, and we instead bundle
-- propositions asserting that various List constructions produce admissible lists.

variable (m : ℕ)
/-- A list of natural numbers `[i₀, ⋯, iₙ]` is said to be `m`-admissible (for `m : ℕ`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`. This would suggest the definition
`L.IsChain (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k`.
However, we instead define `IsAdmissible` inductively and show, in
`isAdmissible_iff_isChain_and_le`, that this is equivalent to the non-inductive definition.
-/
@[mk_iff]
inductive IsAdmissible : (m : ℕ) → (L : List ℕ) → Prop
  | nil (m : ℕ) : IsAdmissible m []
  | singleton {m a} (ha : a ≤ m) : IsAdmissible m [a]
  | cons_cons {m a b L'} (hab : a < b) (hbL : IsAdmissible (m + 1) (b :: L'))
      (ha : a ≤ m) : IsAdmissible m (a :: b :: L')

attribute [simp, grind ←] IsAdmissible.nil
attribute [grind →] IsAdmissible.cons_cons

section IsAdmissible

variable {m a b : ℕ} {L : List ℕ}

@[simp, grind =]
theorem isAdmissible_singleton_iff : IsAdmissible m [a] ↔ a ≤ m :=
  ⟨fun | .singleton h => h, .singleton⟩

@[simp, grind =]
theorem isAdmissible_cons_cons_iff : IsAdmissible m (a :: b :: L) ↔
    a < b ∧ IsAdmissible (m + 1) (b :: L) ∧ a ≤ m :=
  ⟨fun | .cons_cons hab hbL ha => ⟨hab, hbL, ha⟩, by grind⟩

theorem isAdmissible_cons_iff : IsAdmissible m (a :: L) ↔
    a ≤ m ∧ ((_ : 0 < L.length) → a < L[0]) ∧ IsAdmissible (m + 1) L := by
  cases L <;> grind

theorem isAdmissible_iff_isChain_and_le : IsAdmissible m L ↔
    L.IsChain (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k := by
  induction L using List.twoStepInduction generalizing m with
  | nil => grind
  | singleton _ => simp
  | cons_cons _ _ _ _ IH =>
    simp_rw [isAdmissible_cons_cons_iff, IH, List.length_cons, and_assoc,
      List.isChain_cons_cons, and_assoc, and_congr_right_iff, and_comm]
    exact fun _ _ => ⟨fun h => by grind,
      fun h => ⟨h 0 (by grind), fun k _ => (h (k + 1) (by grind)).trans (by grind)⟩⟩

theorem isAdmissible_iff_pairwise_and_le : IsAdmissible m L ↔
    L.Pairwise (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k := by
  rw [isAdmissible_iff_isChain_and_le, List.isChain_iff_pairwise]

theorem isAdmissible_of_isChain_of_forall_getElem_le {m L} (hL : L.IsChain (· < ·))
    (hL₂ : ∀ k, (h : k < L.length) → L[k] ≤ m + k) : IsAdmissible m L :=
  isAdmissible_iff_isChain_and_le.mpr ⟨hL, hL₂⟩

namespace IsAdmissible

@[grind →] theorem isChain {m L} (hL : IsAdmissible m L) :
    L.IsChain (· < ·) := (isAdmissible_iff_isChain_and_le.mp hL).1

@[grind →] theorem le {m} {L : List ℕ} (hL : IsAdmissible m L) : ∀ k (h : k < L.length),
    L[k] ≤ m + k := (isAdmissible_iff_isChain_and_le.mp hL).2

/-- The tail of an `m`-admissible list is (m+1)-admissible. -/
@[grind →] lemma of_cons {m a L} (h : IsAdmissible m (a :: L)) :
    IsAdmissible (m + 1) L := by cases L <;> grind

lemma cons {m a L} (hL : IsAdmissible (m + 1) L) (ha : a ≤ m)
    (ha' : (_ : 0 < L.length) → a < L[0]) : IsAdmissible m (a :: L) := by cases L <;> grind

theorem sortedLT {m L} (hL : IsAdmissible m L) : L.SortedLT :=
  hL.isChain.sortedLT

@[deprecated (since := "2025-11-27")] alias pairwise := sortedLT

@[deprecated (since := "2025-10-16")]
alias sorted := pairwise

/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
@[grind →]
lemma head_lt {m a L} (hL : IsAdmissible m (a :: L)) :
    ∀ a' ∈ L, a < a' := fun _ => L.rel_of_pairwise_cons hL.sortedLT.pairwise

@[grind →] lemma getElem_lt {m L} (hL : IsAdmissible m L)
    {k : ℕ} {hk : k < L.length} : L[k] < m + L.length :=
  (hL.le k hk).trans_lt (Nat.add_lt_add_left hk _)

/-- An element of an `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
def getElemAsFin {m L} (hl : IsAdmissible m L) (k : ℕ)
    (hK : k < L.length) : Fin (m + k + 1) :=
  Fin.mk L[k] <| Nat.le_iff_lt_add_one.mp (by grind)

/-- The head of an `m`-admissible list. -/
@[simps!]
def head {m a L} (hl : IsAdmissible m (a :: L)) : Fin (m + 1) :=
  hl.getElemAsFin 0 (by grind)

theorem mono {n} (hmn : m ≤ n) (hL : IsAdmissible m L) : IsAdmissible n L :=
  isAdmissible_of_isChain_of_forall_getElem_le (by grind) (by grind)

end IsAdmissible

end IsAdmissible

/-- The construction `simplicialInsert` describes inserting an element in a list of integer and
moving it to its "right place" according to the simplicial relations. Somewhat miraculously,
the algorithm is the same for the first or the fifth simplicial relations, making it "valid"
when we treat the list as a normal form for a morphism satisfying `P_δ`, or for a morphism
satisfying `P_σ`!

This is similar in nature to `List.orderedInsert`, but note that we increment one of the element
every time we perform an exchange, making it a different construction. -/
@[local grind]
def simplicialInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: simplicialInsert (a + 1) l

/-- `simplicialInsert` just adds one to the length. -/
lemma simplicialInsert_length (a : ℕ) (L : List ℕ) :
    (simplicialInsert a L).length = L.length + 1 := by
  induction L generalizing a <;> grind

/-- `simplicialInsert` preserves admissibility -/
theorem simplicialInsert_isAdmissible (L : List ℕ) (hL : IsAdmissible (m + 1) L) (j : ℕ)
    (hj : j ≤ m) :
    IsAdmissible m <| simplicialInsert j L := by
  induction L generalizing j m with
  | nil => exact IsAdmissible.singleton hj
  | cons a L h_rec => cases L <;> grind

end AdmissibleLists

section NormalFormsP_σ

-- Impl note.: The definition is a bit awkward with the extra parameters, but this
-- is necessary in order to avoid some type theory hell when proving that `orderedInsert`
-- behaves as expected...

/-- Given a sequence `L = [ i 0, ..., i b ]`, `standardσ m L` i is the morphism
`σ (i b) ≫ … ≫ σ (i 0)`. The construction is provided for any list of natural numbers,
but it is intended to behave well only when the list is admissible. -/
def standardσ (L : List ℕ) {m₁ m₂ : ℕ} (h : m₂ + L.length = m₁) : mk m₁ ⟶ mk m₂ :=
  match L with
  | .nil => eqToHom (by grind)
  | .cons a t => standardσ t (by grind) ≫ σ (Fin.ofNat _ a)

@[simp]
lemma standardσ_nil (m : ℕ) : standardσ .nil (by grind) = 𝟙 (mk m) := rfl

@[simp, reassoc]
lemma standardσ_cons (L : List ℕ) (a : ℕ) {m₁ m₂ : ℕ} (h : m₂ + (a :: L).length = m₁) :
    standardσ (L.cons a) h = standardσ L (by grind) ≫ σ (Fin.ofNat _ a) := rfl

@[reassoc]
lemma standardσ_comp_standardσ (L₁ L₂ : List ℕ) {m₁ m₂ m₃ : ℕ}
    (h : m₂ + L₁.length = m₁) (h' : m₃ + L₂.length = m₂) :
    standardσ L₁ h ≫ standardσ L₂ h' = standardσ (L₂ ++ L₁) (by grind) := by
  induction L₂ generalizing L₁ m₁ m₂ m₃ with
  | nil =>
    obtain rfl : m₃ = m₂ := by grind
    simp
  | cons a t H =>
    dsimp at h' ⊢
    obtain rfl : m₂ = (m₃ + t.length) + 1 := by grind
    simp [reassoc_of% (H L₁ (m₁ := m₁) (m₂ := m₃ + t.length + 1) (m₃ := m₃ + 1)
      (by grind) (by grind))]

variable (m : ℕ) (L : List ℕ)

/-- `simplicialEvalσ` is a lift to ℕ of `(toSimplexCategory.map (standardσ m L _ _)).toOrderHom`.
Rather than defining it as such, we define it inductively for less painful inductive reasoning,
(see `simplicialEvalσ_of_isAdmissible`).
It is expected to produce the correct result only if `L` is admissible, and values for
non-admissible lists should be considered junk values. Similarly, values for out-of-bounds inputs
are junk values. -/
@[local grind]
def simplicialEvalσ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

@[grind ←]
lemma simplicialEvalσ_of_le_mem (j : ℕ) (hj : ∀ k ∈ L, j ≤ k) : simplicialEvalσ L j = j := by
  induction L with | nil => grind | cons _ _ _ => simp only [List.forall_mem_cons] at hj; grind

@[deprecated (since := "2025-10-16")]
alias simplicialEvalσ_of_lt_mem := simplicialEvalσ_of_le_mem

lemma simplicialEvalσ_monotone (L : List ℕ) : Monotone (simplicialEvalσ L) := by
  induction L <;> grind [Monotone]

variable {m}

set_option backward.isDefEq.respectTransparency false in
/- We prove that `simplicialEvalσ` is indeed a lift of
`(toSimplexCategory.map (standardσ m L _ _)).toOrderHom` when the list is admissible. -/
lemma simplicialEvalσ_of_isAdmissible
    (m₁ m₂ : ℕ) (hL : IsAdmissible m₂ L) (hk : m₂ + L.length = m₁)
    (j : ℕ) (hj : j < m₁ + 1) :
    (toSimplexCategory.map <| standardσ L hk).toOrderHom ⟨j, hj⟩ =
    simplicialEvalσ L j := by
  induction L generalizing m₁ m₂ with
  | nil =>
    obtain rfl : m₁ = m₂ := by grind
    simp [simplicialEvalσ]
  | cons a L h_rec =>
    simp only [List.length_cons] at hk
    subst hk
    set a₀ := hL.head
    have aux (t : Fin (m₂ + 2)) :
        (a₀.predAbove t : ℕ) = if a < ↑t then (t : ℕ) - 1 else ↑t := by
      simp only [Fin.predAbove, a₀]
      split_ifs with h₁ h₂ h₂
      · rfl
      · simp only [Fin.lt_def, Fin.val_castSucc, IsAdmissible.head_val] at h₁; grind
      · simp only [Fin.lt_def, Fin.val_castSucc, IsAdmissible.head_val, not_lt] at h₁; grind
      · rfl
    have := h_rec _ _ hL.of_cons (by grind) hj
    have ha₀ : Fin.ofNat (m₂ + 1) a = a₀ := by ext; simpa [a₀] using hL.head.prop
    simpa only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, standardσ_cons, Functor.map_comp,
      toSimplexCategory_map_σ, SimplexCategory.σ, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, Fin.predAboveOrderHom_coe, simplicialEvalσ, ha₀, ← this] using aux _

/-- Performing a simplicial insertion in a list is the same as composition on the right by the
corresponding degeneracy operator. -/
lemma standardσ_simplicialInsert (hL : IsAdmissible (m + 1) L) (j : ℕ) (hj : j < m + 1)
    (m₁ : ℕ) (hm₁ : m + L.length + 1 = m₁) :
    standardσ (m₂ := m) (simplicialInsert j L) (m₁ := m₁)
      (by simpa only [simplicialInsert_length, add_assoc]) =
    standardσ (m₂ := m + 1) L (by grind) ≫ σ (Fin.ofNat _ j) := by
  induction L generalizing m j with
  | nil => simp [standardσ, simplicialInsert]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs
    · simp
    · have : ∀ (j k : ℕ) (h : j < (k + 1)), Fin.ofNat (k + 1) j = j := by simp -- helps grind below
      have : a < m + 2 := by grind -- helps grind below
      have : σ (Fin.ofNat (m + 2) a) ≫ σ (.ofNat _ j) = σ (.ofNat _ (j + 1)) ≫ σ (.ofNat _ a) := by
        convert σ_comp_σ_nat (n := m) a j (by grind) (by grind) (by grind) <;> grind
      grind [standardσ_cons]

set_option backward.isDefEq.respectTransparency false in
attribute [local grind! .] simplicialInsert_length simplicialInsert_isAdmissible in
/-- Using `standardσ_simplicialInsert`, we can prove that every morphism satisfying `P_σ` is equal
to some `standardσ` for some admissible list of indices. -/
theorem exists_normal_form_P_σ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_σ f) :
    ∃ L : List ℕ,
    ∃ m : ℕ, ∃ b : ℕ,
    ∃ h₁ : mk m = y, ∃ h₂ : x = mk (m + b), ∃ h : L.length = b,
    IsAdmissible m L ∧ f = standardσ L (by rw [h, h₁.symm, h₂]; rfl) := by
  induction hf with
  | id n =>
    use [], n.len, 0, rfl, rfl, rfl, IsAdmissible.nil _
    rfl
  | of f hf =>
    cases hf with | @σ m k =>
    use [k.val], m, 1, rfl, rfl, rfl, IsAdmissible.singleton k.is_le
    simp [standardσ]
  | @comp_of _ j x' g g' hg hg' h_rec =>
    cases hg' with | @σ m k =>
    obtain ⟨L₁, m₁, b₁, h₁', rfl, h', hL₁, e₁⟩ := h_rec
    obtain rfl : m₁ = m + 1 := congrArg (fun x ↦ x.len) h₁'
    use simplicialInsert k.val L₁, m, b₁ + 1, rfl, by grind, by grind, by grind
    subst_vars
    have := standardσ (m₁ := m + 1 + L₁.length) [] (by grind) ≫=
      (standardσ_simplicialInsert L₁ hL₁ k k.prop _ rfl).symm
    simp_all [Fin.ofNat_eq_cast, Fin.cast_val_eq_self, standardσ_comp_standardσ_assoc,
      standardσ_comp_standardσ]

section MemIsAdmissible

lemma IsAdmissible.simplicialEvalσ_succ_getElem (hL : IsAdmissible m L)
    {k : ℕ} {hk : k < L.length} : simplicialEvalσ L L[k] = simplicialEvalσ L (L[k] + 1) := by
  induction L generalizing m k <;> grind [→ IsAdmissible.singleton]

local grind_pattern IsAdmissible.simplicialEvalσ_succ_getElem =>
  IsAdmissible m L, simplicialEvalσ L L[k]

lemma mem_isAdmissible_of_lt_and_eval_eq_eval_add_one (hL : IsAdmissible m L)
    (j : ℕ) (hj₁ : j < m + L.length) (hj₂ : simplicialEvalσ L j = simplicialEvalσ L (j + 1)) :
    j ∈ L := by
  induction L generalizing m with
  | nil => grind
  | cons a L h_rec =>
    have := simplicialEvalσ_monotone L (a := a + 1)
    rcases lt_trichotomy j a with h | h | h <;> grind

lemma lt_and_eval_eq_eval_add_one_of_mem_isAdmissible (hL : IsAdmissible m L) (j : ℕ) (hj : j ∈ L) :
    j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  grind [List.mem_iff_getElem]

/-- We can characterize elements in an admissible list as exactly those for which
`simplicialEvalσ` takes the same value twice in a row. -/
lemma mem_isAdmissible_iff (hL : IsAdmissible m L) (j : ℕ) :
    j ∈ L ↔ j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  grind [lt_and_eval_eq_eval_add_one_of_mem_isAdmissible,
    mem_isAdmissible_of_lt_and_eval_eq_eval_add_one]

end MemIsAdmissible

end NormalFormsP_σ

end SimplexCategoryGenRel
