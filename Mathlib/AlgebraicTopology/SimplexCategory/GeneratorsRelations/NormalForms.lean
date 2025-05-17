/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.EpiMono
/-! # Normal forms for morphisms in `SimplexCategoryGenRel`.

In this file, we establish that `P_δ` and `P_σ` morphisms in `SimplexCategoryGenRel`
each admits a normal form.

In both cases, the normal forms are encoded as an integer `m`, and a strictly increasing
lists of integers `[i₀,…,iₙ]` such that `iₖ ≤ m + k` for all `k`. We define a predicate
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

namespace SimplexCategoryGenRel

open CategoryTheory

section AdmissibleLists
-- Impl. note: We are not bundling admissible lists as a subtype of `List ℕ` so that it remains
-- easier to perform inductive constructions and proofs on such lists, and we instead bundle
-- propositions asserting that various List constructions produce admissible lists.

variable (m : ℕ)
/-- A list of natural numbers [i₀, ⋯, iₙ]) is said to be `m`-admissible (for `m : ℕ`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`.
-/
def IsAdmissible (L : List ℕ) : Prop :=
  List.Sorted (· < ·) L ∧
  ∀ (k : ℕ), (h : k < L.length) → L[k] ≤ m + k

namespace IsAdmissible

lemma nil : IsAdmissible m [] := by simp [IsAdmissible]

variable {m}

lemma sorted {L : List ℕ} (hL : IsAdmissible m L) : L.Sorted (· < ·) := hL.1

lemma le {L : List ℕ} (hL : IsAdmissible m L) : ∀ (k : ℕ), (h : k < L.length) → L[k] ≤ m + k := hL.2

/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
lemma head_lt (a : ℕ) (L : List ℕ) (hl : IsAdmissible m (a :: L)) :
    ∀ a' ∈ L, a < a' := fun i hi ↦ (List.sorted_cons.mp hl.sorted).left i hi

/-- If `L` is a `(m + 1)`-admissible list, and `a` is natural number such that a ≤ m and a < L[0],
then `a::L` is `m`-admissible -/
lemma cons (L : List ℕ) (hL : IsAdmissible (m + 1) L) (a : ℕ) (ha : a ≤ m)
    (ha' : (_ : 0 < L.length) → a < L[0]) : IsAdmissible m (a :: L) := by
  cases L with
  | nil => constructor <;> simp [ha]
  | cons head tail =>
    simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true, List.getElem_cons_zero,
      forall_const] at ha'
    simp only [IsAdmissible, List.sorted_cons, List.mem_cons, forall_eq_or_imp]
    constructor <;> repeat constructor
    · exact ha'
    · rw [← List.forall_getElem]
      intro i hi
      exact ha'.trans <| (List.sorted_cons.mp hL.sorted).left tail[i] <| List.getElem_mem hi
    · exact List.sorted_cons.mp hL.sorted
    · rintro ⟨_ | _⟩ hi
      · simp [ha]
      · haveI := hL.le _ <| Nat.lt_of_succ_lt_succ hi
        rw [List.getElem_cons_succ]
        omega

/-- The tail of an `m`-admissible list is (m+1)-admissible. -/
lemma tail (a : ℕ) (l : List ℕ) (h : IsAdmissible m (a::l)) :
    IsAdmissible (m + 1) l := by
  refine ⟨(List.sorted_cons.mp h.sorted).right, ?_⟩
  intro k _
  simpa [Nat.add_assoc, Nat.add_comm 1] using h.le (k + 1) (by simpa)

/-- An element of a `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
def getElemAsFin {L : List ℕ} (hl : IsAdmissible m L) (k : ℕ)
    (hK : k < L.length) : Fin (m + k + 1) :=
  Fin.mk L[k] <| Nat.le_iff_lt_add_one.mp (by simp [hl.le])

/-- The head of an `m`-admissible list. -/
@[simps!]
def head (a : ℕ) (L : List ℕ) (hl : IsAdmissible m (a :: L)) : Fin (m + 1) :=
  hl.getElemAsFin 0 (by simp)

end IsAdmissible

/-- The construction `simplicialInsert` describes inserting an element in a list of integer and
moving it to its "right place" according to the simplicial relations. Somewhat miraculously,
the algorithm is the same for the first or the fifth simplicial relations, making it "valid"
when we treat the list as a normal form for a morphism satisfying `P_δ`, or for a morphism
satisfying `P_σ`!

This is similar in nature to `List.orderedInsert`, but note that we increment one of the element
every time we perform an exchange, making it a different construction. -/
def simplicialInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: simplicialInsert (a + 1) l

/-- `simplicialInsert` just adds one to the length. -/
lemma simplicialInsert_length (a : ℕ) (L : List ℕ) :
    (simplicialInsert a L).length = L.length + 1 := by
  induction L generalizing a with
  | nil => rfl
  | cons head tail h_rec =>
    dsimp only [simplicialInsert, List.length_cons]
    split_ifs with h <;> simp only [List.length_cons, add_left_inj, h_rec (a + 1)]

/-- `simplicialInsert` preserves admissibility -/
theorem simplicialInsert_isAdmissible (L : List ℕ) (hL : IsAdmissible (m + 1) L) (j : ℕ)
    (hj : j < m + 1) :
    IsAdmissible m <| simplicialInsert j L := by
  induction L generalizing j m with
  | nil => constructor <;> simp [simplicialInsert, j.le_of_lt_add_one hj]
  | cons a L h_rec =>
    dsimp only [simplicialInsert]
    split_ifs with ha
    · exact .cons _ hL _ (j.le_of_lt_add_one hj) (fun _ ↦ ha)
    · refine IsAdmissible.cons _ ?_ _ (not_lt.mp ha |>.trans <| j.le_of_lt_add_one hj) ?_
      · refine h_rec _ (.tail a L hL) _ (by simp [hj])
      · rw [not_lt, Nat.le_iff_lt_add_one] at ha
        intro u
        cases L with
        | nil => simp [simplicialInsert, ha]
        | cons a' l' =>
          dsimp only [simplicialInsert]
          split_ifs
          · exact ha
          · exact (List.sorted_cons_cons.mp hL.sorted).1

end AdmissibleLists

section NormalFormsP_σ

-- Impl note.: The definition is a bit awkward with the extra parameter `k`, but this
-- is necessary in order to avoid some type theory hell when proving that `orderedInsert`
-- behaves as expected...

/-- Given a sequence `L = [ i 0, ..., i b ]`, `standardσ m L` i is the morphism
`σ (i b) ≫ … ≫ σ (i 0)`. The construction is provided for any list of natural numbers,
but it is intended to behave well only when the list is admissible. -/
def standardσ (m : ℕ) (L : List ℕ) (k : ℕ) (hK : L.length = k) : mk (m + k) ⟶ mk m :=
  match L with
  | .nil => eqToHom <| by rw [← hK]; rfl
  | .cons a t => eqToHom (by rw [← hK, List.length_cons, Nat.add_comm t.length 1, Nat.add_assoc]) ≫
      standardσ (m + 1) t t.length rfl ≫ σ a

variable (m : ℕ) (L : List ℕ)
-- Because we gave a degree of liberty with the parameter `k`, we need this kind of lemma to ease
-- working with different `k`s
lemma standardσ_heq (k₁ : ℕ) (hk₁ : L.length = k₁) (k₂ : ℕ) (hk₂ : L.length = k₂) :
    HEq (standardσ m L k₁ hk₁) (standardσ m L k₂ hk₂) := by
  subst hk₁
  subst hk₂
  simp

/-- `simplicialEvalσ` is a lift to ℕ of `toSimplexCategory.map (standardσ m L _ _)).toOrderHom`.
Rather than defining it as such, we define it inductively for less painful inductive reasoning,
and we keep the `eqToHom` business in the proof that it is indeed such a lift
(see `simplicialEvalσ_of_isAdmissible`).
It is expected to produce the correct result only if `L` is admissible, and values for
non-admissible lists should be considered junk values. Similarly, values for out-of-bonds inputs
are junk values. -/
def simplicialEvalσ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

@[simp]
private lemma eqToHom_toOrderHom_eq_cast {m n : ℕ}
    (h : SimplexCategory.mk m = SimplexCategory.mk n) :
    (eqToHom h).toOrderHom =
      (Fin.castOrderIso <| congrArg (fun x ↦ x.len + 1) h).toOrderEmbedding.toOrderHom := by
  ext
  haveI := congrArg (fun x ↦ x.len + 1) h
  simp only [SimplexCategory.len_mk, add_left_inj] at this
  subst this
  simp

variable {m}
-- most of the proof is about fighting with `eqToHom`s...
/- We prove that `simplicialEvalσ` is indeed a lift of
`toSimplexCategory.map (standardσ m L _ _)).toOrderHom` when the list is admissible. -/
lemma simplicialEvalσ_of_isAdmissible (hL : IsAdmissible m L)
    (k : ℕ) (hk : L.length = k)
    (j : ℕ) (hj : j < m + k + 1) :
    ((toSimplexCategory.map <| standardσ m L k hk).toOrderHom ⟨j, hj⟩ : ℕ) =
    simplicialEvalσ L j := by
  induction L generalizing m k with
  | nil => simp [simplicialEvalσ, standardσ, eqToHom_map]
  | cons a L h_rec =>
    subst hk
    haveI := h_rec hL.tail L.length rfl <|
      by simpa [← Nat.add_comm 1 L.length, ← Nat.add_assoc] using hj
    simp only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, List.length_cons, standardσ,
      Functor.map_comp, eqToHom_map, toSimplexCategory_map_σ, SimplexCategory.σ,
      SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
      eqToHom_toOrderHom_eq_cast, Nat.add_eq, Nat.succ_eq_add_one, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
      Fin.predAboveOrderHom_coe, Fin.predAbove, simplicialEvalσ, ← this]
    split_ifs with h₁ h₂ h₂
    · generalize_proofs _ pf
      rw [Fin.castOrderIso_apply pf ⟨j, hj⟩] at h₁
      simp only [Fin.cast_mk, Fin.coe_pred] at h₁ ⊢
      congr
    · exfalso
      rw [Fin.lt_def] at h₁
      simp only [Fin.coe_castSucc, Fin.val_natCast, not_lt] at h₁ h₂
      haveI := Nat.mod_eq_of_lt <| Fin.prop <| hL.head
      dsimp [IsAdmissible.head] at this
      rw [this] at h₁
      haveI := h₂.trans_lt h₁
      simp only [Fin.val_fin_lt] at this
      generalize_proofs _ pf at this
      conv_rhs at this =>
        arg 2
        equals ⟨j, pf⟩ => ext; rfl
      exact (lt_self_iff_false _).mp this
    · exfalso
      rw [Fin.lt_def] at h₁
      simp only [Fin.coe_castSucc, Fin.val_natCast, not_lt] at h₁ h₂
      haveI := Nat.mod_eq_of_lt <| Fin.prop <| hL.head
      dsimp [IsAdmissible.head] at this
      rw [this] at h₁
      haveI := h₁.trans_lt h₂
      simp only [Fin.val_fin_lt] at this
      generalize_proofs pf1 pf2 pf3 at this
      conv_rhs at this =>
        arg 2
        equals ⟨j, pf3⟩ => ext; rfl
      exact (lt_self_iff_false _).mp this
    · generalize_proofs _ pf
      rw [Fin.castOrderIso_apply pf ⟨j, hj⟩] at h₁
      simp only [Fin.cast_mk, not_lt, Fin.coe_castPred] at h₁ ⊢
      congr

lemma simplicialEvalσ_of_lt_mem (j : ℕ) (hj : ∀ k ∈ L, j ≤ k) : simplicialEvalσ L j = j := by
  induction L with
  | nil => simp [simplicialEvalσ]
  | cons a h h_rec =>
    dsimp only [simplicialEvalσ]
    split_ifs with h1 <;> {
      simp only [List.mem_cons, forall_eq_or_imp] at hj
      haveI := h_rec hj.2
      linarith }

lemma simplicialEvalσ_monotone (L : List ℕ) : Monotone (simplicialEvalσ L) := by
  intro a b hab
  induction L generalizing a b with
  | nil => exact hab
  | cons head tail h_rec =>
    dsimp only [simplicialEvalσ]
    haveI := h_rec hab
    split_ifs with h h' h' <;> omega

/-- Performing a simplicial insert in a list is (up to some unfortunate `eqToHom`) the same
as composition on the right by the corresponding degeneracy operator. -/
lemma standardσ_simplicialInsert (hL : IsAdmissible (m + 1) L) (j : ℕ)
    (hj : j < m + 1) :
    standardσ m (simplicialInsert j L) (L.length + 1) (simplicialInsert_length _ _) =
    eqToHom (by rw [Nat.add_assoc, Nat.add_comm 1]) ≫ standardσ (m + 1) L L.length rfl ≫ σ j := by
  induction L generalizing m j with
  | nil => simp [standardσ, simplicialInsert]
  | cons a L h_rec =>
    simp only [List.length_cons, eqToHom_refl, simplicialInsert, Category.id_comp]
    split_ifs <;> rename_i h <;> simp only [standardσ, eqToHom_trans_assoc, Category.assoc]
    slice_rhs 3 5 => equals σ ↑(j + 1) ≫ σ a =>
      have ha : a < m + 1 := Nat.lt_of_le_of_lt (not_lt.mp h) hj
      haveI := σ_comp_σ_nat a j ha hj (not_lt.mp h)
      generalize_proofs p p' at this
      -- We have to get rid of the natCasts...
      have ha₁ : (⟨a, p⟩ : Fin <| m + 1 + 1) = ↑a := by ext; simp [Nat.mod_eq_of_lt p]
      have ha₂ : (⟨a, ha⟩ : Fin <| m + 1) = ↑a := by ext; simp [Nat.mod_eq_of_lt ha]
      have hj₁ : (⟨j + 1, p'⟩ : Fin <| m + 1 + 1) = ↑(j + 1) := by ext; simp [Nat.mod_eq_of_lt p']
      have hj₂ : (⟨j, hj⟩ : Fin <| m + 1) = ↑j := by ext; simp [Nat.mod_eq_of_lt hj]
      rwa [← ha₁, ← ha₂, ← hj₁, ← hj₂]
    haveI := h_rec hL.tail (j + 1) (by simpa)
    simp only [eqToHom_refl, Category.id_comp] at this
    rw [← eqToHom_comp_iff (by ext; simp [Nat.add_assoc, Nat.add_comm 1, Nat.add_comm 2])] at this
    rw [← reassoc_of% this]
    simp only [eqToHom_trans_assoc]
    rw [← heq_iff_eq, eqToHom_comp_heq_iff, HEq.comm, eqToHom_comp_heq_iff]
    apply heq_comp <;> try simp [simplicialInsert_length, heq_iff_eq]
    apply standardσ_heq

/-- Using `standardσ_simplicialInsert`, we can prove that every morphism satisfying `P_σ` is equal
to some `standardσ` for some admissible list of indices. Because morphisms of the form `standardσ`
have a rather  constrained sources and targets, we have again to splice in some `eqToHom`'s to make
everything work. -/
theorem exists_normal_form_P_σ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_σ f) :
    ∃ L : List ℕ,
    ∃ m : ℕ, ∃ b : ℕ,
    ∃ h₁ : mk m = y, ∃ h₂ : x = mk (m + b), ∃ h : L.length = b,
    IsAdmissible m L ∧ f = eqToHom h₂ ≫ standardσ m L b h ≫ eqToHom h₁ := by
  induction hf with
  | id n =>
    use [], n.len, 0, rfl, rfl, rfl, IsAdmissible.nil _
    simp [standardσ]
  | of f hf =>
    cases hf with | @σ m k =>
    use [k.val], m, 1 , rfl, rfl, rfl
    constructor <;> simp [IsAdmissible, Nat.le_of_lt_add_one k.prop, standardσ]
  | @comp_of _ j x' g g' hg hg' h_rec =>
    cases hg' with | @σ m k =>
    obtain ⟨L₁, m₁, b₁, h₁', h₂', h', hL₁, e₁⟩ := h_rec
    have hm₁ : m₁ = m + 1 := congrArg (fun x ↦ x.len) h₁'
    use simplicialInsert k.val L₁, m, b₁ + 1, rfl, ?_, ?_, ?_
    rotate_right 3
    · rwa [← Nat.add_comm 1, ← Nat.add_assoc, ← hm₁]
    · rw [simplicialInsert_length, h']
    · exact simplicialInsert_isAdmissible _ _ (by rwa [← hm₁]) _ k.prop
    · subst e₁
      subst h'
      rw [standardσ_simplicialInsert]
      · subst m₁
        simp
      · simpa [← hm₁]
      · exact k.prop

section MemIsAdmissible

lemma mem_isAdmissible_of_lt_and_eval_eq_eval_succ (hL : IsAdmissible m L)
    (j : ℕ) (hj₁ : j < m + L.length) (hj₂ : simplicialEvalσ L j = simplicialEvalσ L j.succ) :
    j ∈ L := by
  induction L generalizing m with
  | nil => simp [simplicialEvalσ] at hj₂
  | cons a L h_rec =>
    simp only [List.mem_cons]
    by_cases hja : j = a
    · left; exact hja
    · right
      apply h_rec hL.tail
      · simpa [← Nat.add_comm 1 L.length, ← Nat.add_assoc] using hj₁
      · simp only [simplicialEvalσ, Nat.succ_eq_add_one] at hj₂
        split_ifs at hj₂ with h₁ h₂ h₂
        · simp only [Nat.succ_eq_add_one]
          omega
        · rw [← hj₂, Nat.eq_self_sub_one]
          rw [not_lt] at h₂
          haveI : simplicialEvalσ L j ≤ simplicialEvalσ L (j + 1) :=
            simplicialEvalσ_monotone L (by simp)
          linarith
        · rw [hj₂, Nat.succ_eq_add_one, Eq.comm, Nat.eq_self_sub_one]
          rw [not_lt] at h₁
          simp only [IsAdmissible, List.sorted_cons, List.length_cons] at hL
          obtain h | h | h := Nat.lt_trichotomy j a
          · haveI : simplicialEvalσ L j ≤ simplicialEvalσ L (j + 1) :=
              simplicialEvalσ_monotone L (by simp)
            have ha := simplicialEvalσ_of_lt_mem L a <| fun x h ↦ le_of_lt <| hL.1.1 x h
            have hj₁ := simplicialEvalσ_monotone L h
            linarith
          · exfalso; exact hja h
          · haveI := simplicialEvalσ_of_lt_mem L a <| fun x h ↦ le_of_lt <| hL.1.1 x h
            rw [← this] at h₁ h₂
            have ha₁ := le_antisymm (simplicialEvalσ_monotone L <| le_of_lt h) h₁
            have ha₂ := simplicialEvalσ_of_lt_mem L (a + 1) <| fun x h ↦ hL.1.1 x h
            rw (occs := .pos [2]) [← this] at ha₂
            rw [ha₁, hj₂] at ha₂
            by_cases h' : simplicialEvalσ L (j + 1) = 0
            · exact h'
            · rw [Nat.sub_one_add_one h'] at ha₂
              have ha₃ := simplicialEvalσ_monotone L h
              rw [Nat.succ_eq_add_one] at ha₃
              linarith
        · exact hj₂

lemma lt_and_eval_eq_eval_succ_of_mem_isAdmissible (hL : IsAdmissible m L) (j : ℕ) (hj : j ∈ L) :
    j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L j.succ := by
  induction L generalizing m with
  | nil => simp [simplicialEvalσ] at hj
  | cons a L h_rec =>
    constructor
    · simp only [IsAdmissible, List.sorted_cons] at hL
      have aux : ∀ (k : ℕ), (_ : k < (a::L).length) → (a::L)[k] < m + (a::L).length := by
        intro k hk
        apply hL.2 k hk|>.trans_lt
        simpa using hk
      obtain ⟨k, hk, hk'⟩ := List.mem_iff_getElem.mp hj
      subst hk'
      exact aux k hk
    · simp only [List.mem_cons] at hj
      obtain h | h := hj
      · subst h
        simp only [simplicialEvalσ, Nat.succ_eq_add_one]
        simp only [IsAdmissible, List.sorted_cons] at hL
        rw [simplicialEvalσ_of_lt_mem L j <| fun x hx ↦ le_of_lt <| hL.1.1 x hx,
          simplicialEvalσ_of_lt_mem L (j + 1) <| fun x hx ↦ hL.1.1 x hx]
        simp
      · simp only [simplicialEvalσ, Nat.succ_eq_add_one]
        split_ifs with h₁ h₂ h₂
        · rw [h_rec hL.tail h |>.2]
        · rw [h_rec hL.tail h |>.2]
          rw [not_lt] at h₂
          haveI : simplicialEvalσ L j ≤ simplicialEvalσ L (j + 1) :=
            simplicialEvalσ_monotone L (by simp)
          linarith
        · rw [not_lt] at h₁
          obtain ⟨h_rec₁, h_rec₂⟩ := h_rec hL.tail h
          linarith
        · rw [h_rec hL.tail h |>.2]

/-- We can characterize elements in an admissible list as exactly those for which
`simplicialEvalσ` takes the same value twice in a row. -/
lemma mem_isAdmissible_iff (hL : IsAdmissible m L) (j : ℕ) :
    j ∈ L ↔ j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L j.succ := by
  constructor
  · intro hj
    exact lt_and_eval_eq_eval_succ_of_mem_isAdmissible _ hL j hj
  · rintro ⟨hj₁, hj₂⟩
    exact mem_isAdmissible_of_lt_and_eval_eq_eval_succ L hL j hj₁ hj₂

end MemIsAdmissible

end NormalFormsP_σ

end SimplexCategoryGenRel
