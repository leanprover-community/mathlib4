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

-/

namespace SimplexCategoryGenRel

open CategoryTheory

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
        cutsat

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

lemma head_lt' (a : ℕ) (L : List ℕ) (hl : IsAdmissible m (a :: L)) : a < m + 1 :=
  hl.getElemAsFin 0 (by simp)|>.prop

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
    split_ifs with h <;> simp only [List.length_cons, h_rec (a + 1)]

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

/-- `simplicialEvalσ` is a lift to ℕ of `toSimplexCategory.map (standardσ m L _ _)).toOrderHom`.
Rather than defining it as such, we define it inductively for less painful inductive reasoning,
and we keep the (hidden) `eqToHom` business in the proof that it is indeed such a lift
(see `simplicialEvalσ_of_isAdmissible`).
It is expected to produce the correct result only if `L` is admissible, and values for
non-admissible lists should be considered junk values. Similarly, values for out-of-bonds inputs
are junk values. -/
def simplicialEvalσ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

lemma simplicialEvalσ_of_lt_mem (j : ℕ) (hj : ∀ k ∈ L, j ≤ k) : simplicialEvalσ L j = j := by
  induction L with
  | nil => grind [simplicialEvalσ]
  | cons _ _ _ =>
    simp only [List.mem_cons, forall_eq_or_imp] at hj
    grind [simplicialEvalσ]

lemma simplicialEvalσ_monotone (L : List ℕ) : Monotone (simplicialEvalσ L) := by
  intro a b hab
  induction L generalizing a b with
  | nil => exact hab
  | cons head tail h_rec => grind [simplicialEvalσ]

variable {m}
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
      · simp only [Fin.lt_def, Fin.coe_castSucc, IsAdmissible.head_val] at h₁; grind
      · simp only [Fin.lt_def, Fin.coe_castSucc, IsAdmissible.head_val, not_lt] at h₁; grind
      · rfl
    have := h_rec _ _ hL.tail (by grind) hj
    have ha₀ : Fin.ofNat (m₂ + 1) a = a₀ := by ext; simpa [a₀] using hL.head.prop
    simpa only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, standardσ_cons, Functor.map_comp,
      toSimplexCategory_map_σ, SimplexCategory.σ, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, Fin.predAboveOrderHom_coe, simplicialEvalσ, ha₀, ← this] using aux _

/-- Performing a simplicial insert in a list is the same as composition on the right by the
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
    · have : ∀ (j k : ℕ) (h : j < (k + 1)), Fin.ofNat (k + 1) j = j := by simp
      have : σ (Fin.ofNat (m + 2) a) ≫ σ (.ofNat _ j) = σ (.ofNat _ (j + 1)) ≫ σ (.ofNat _ a) := by
        convert σ_comp_σ_nat (n := m) a j (by grind) (by grind) (by grind) <;> grind
      simp only [standardσ_cons, Category.assoc, this,
        h_rec hL.tail (j + 1) (by grind) (by grind)]

attribute [local grind] simplicialInsert_length simplicialInsert_isAdmissible in
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
    use [k.val], m, 1 , rfl, rfl, rfl
    constructor <;> simp [IsAdmissible, Nat.le_of_lt_add_one k.prop, standardσ]
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

lemma mem_isAdmissible_of_lt_and_eval_eq_eval_add_one (hL : IsAdmissible m L)
    (j : ℕ) (hj₁ : j < m + L.length) (hj₂ : simplicialEvalσ L j = simplicialEvalσ L (j + 1)) :
    j ∈ L := by
  induction L generalizing m with
  | nil => grind [simplicialEvalσ]
  | cons a L h_rec =>
    have := h_rec hL.tail (by grind)
    suffices ¬j = a → (simplicialEvalσ L j = simplicialEvalσ L (j + 1)) by grind
    intro hja
    simp only [simplicialEvalσ] at hj₂
    have : simplicialEvalσ L j ≤ simplicialEvalσ L (j + 1) :=
      simplicialEvalσ_monotone L (by grind)
    suffices ¬a < simplicialEvalσ L j → a < simplicialEvalσ L (j + 1) →
      simplicialEvalσ L j = simplicialEvalσ L (j + 1) - 1 →
      simplicialEvalσ L j = simplicialEvalσ L (j + 1) by grind
    intro h₁ h₂ hj₂
    simp only [IsAdmissible, List.sorted_cons, List.length_cons] at hL
    obtain h | rfl | h := Nat.lt_trichotomy j a
    · grind [simplicialEvalσ_monotone, Monotone, simplicialEvalσ_of_lt_mem]
    · grind
    · have := simplicialEvalσ_of_lt_mem L (a + 1) <| fun x h ↦ hL.1.1 x h
      grind [simplicialEvalσ_monotone, Monotone]

lemma lt_and_eval_eq_eval_add_one_of_mem_isAdmissible (hL : IsAdmissible m L) (j : ℕ) (hj : j ∈ L) :
    j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  induction L generalizing m with
  | nil => grind
  | cons a L h_rec =>
    constructor
    · grind [List.mem_iff_getElem, IsAdmissible, List.sorted_cons]
    · obtain rfl | h := List.mem_cons.mp hj
      · grind [simplicialEvalσ_of_lt_mem, simplicialEvalσ, IsAdmissible, List.sorted_cons]
      · have := h_rec hL.tail h
        grind [simplicialEvalσ]

/-- We can characterize elements in an admissible list as exactly those for which
`simplicialEvalσ` takes the same value twice in a row. -/
lemma mem_isAdmissible_iff (hL : IsAdmissible m L) (j : ℕ) :
    j ∈ L ↔ j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  grind [lt_and_eval_eq_eval_add_one_of_mem_isAdmissible,
    mem_isAdmissible_of_lt_and_eval_eq_eval_add_one]

end MemIsAdmissible

end NormalFormsP_σ

section NormalFormsP_δ

/-- Given a sequence `L = [ i 0, ..., i b ]`, `standardδ n L` i is the morphism
`δ (i b) ≫ … ≫ δ (i 0)`. The construction is provided for any list of natural numbers,
but it is intended to behave well only when the list is admissible. -/
def standardδ (L : List ℕ) {k l : ℕ} (hkl : k + L.length = l) : mk k ⟶ mk l :=
  match L with
  | .nil => eqToHom (by grind)
  | .cons a t => δ (Fin.ofNat (k + 2) a) ≫ standardδ t (by grind)

@[simp]
lemma standardδ_nil (m : ℕ) : standardδ .nil (by grind) = 𝟙 (mk m) := rfl

@[simp, reassoc]
lemma standardδ_cons (L : List ℕ) (a : ℕ) {k l : ℕ}
    (hkl : k + (a::L).length = l) :
    standardδ (a::L) hkl = δ (Fin.ofNat _ a) ≫ standardδ L (by grind) := rfl

@[reassoc]
lemma standardδ_comp_standardδ (L₁ L₂ : List ℕ) {m₁ m₂ m₃ : ℕ}
    (h : m₁ + L₁.length = m₂) (h' : m₂ + L₂.length = m₃) :
    standardδ L₁ h ≫ standardδ L₂ h' = standardδ (L₁ ++ L₂) (by grind) := by
  induction L₁ generalizing L₂ m₁ m₂ m₃ with
  | nil =>
    obtain rfl : m₁ = m₂ := by grind
    simp
  | cons a t H =>
    dsimp at h' ⊢
    grind

/-- `simplicialEvalδ` is a lift to ℕ of `(toSimplexCategory.map (standardδ m L _ _)).toOrderHom`,
but we define it in an explicit recursive way to enable for less painful inductive reasoning.
It is expected to produce the correct result only if `L` is admissible but it is more convenient
to have it defined for any list of natural numbers.
See `simplicialEvalδ_of_isAdmissible` for the fact that it is the function we claim it is when
the list is admissible. -/
def simplicialEvalδ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => simplicialEvalδ L (if j < a then j else j + 1)

variable {n : ℕ} (L : List ℕ)

/-- We prove that simplicialEvalδ is indeed a lift to ℕ of
`(toSimplexCategory.map <| standardδ L hnl).toOrderHom` when the list is admissible. -/
lemma simplicialEvalδ_of_isAdmissible (hL : IsAdmissible (n + 1) L)
    {l : ℕ} (hnl : n + L.length = l)
    (j : ℕ) (hj : j < n + 1) :
    (toSimplexCategory.map <| standardδ L hnl).toOrderHom ⟨j, hj⟩ =
    simplicialEvalδ L j := by
  induction L generalizing j n l with
  | nil =>
    obtain rfl : n = l := by grind
    simp [standardδ, simplicialEvalδ]
  | cons a L h_rec =>
    simp only [List.length_cons] at hnl
    subst hnl
    set a₀ := hL.head
    have aux (t : Fin (n + 1)) :
        (a₀.succAbove t : ℕ) = if ↑t < a then (t : ℕ) else ↑t + 1 := by
      simp only [Fin.succAbove, a₀]
      split_ifs with h₁ _ _
      · rfl
      · simp only [Fin.lt_def, Fin.coe_castSucc, IsAdmissible.head_val] at h₁; grind
      · simp only [Fin.lt_def, Fin.coe_castSucc, IsAdmissible.head_val, not_lt] at h₁; grind
      · rfl
    have ha₀ : a = a₀ := by simp [a₀]
    have := h_rec (l := n + (L.length + 1)) hL.tail (by grind) ↑(a₀.succAbove ⟨j, hj⟩)
      (a₀.succAbove ⟨j, hj⟩).prop
    simp only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, Fin.eta] at this
    simp [standardδ, simplicialEvalδ, SimplexCategory.δ, ha₀, this, aux]

lemma simplicialEvalδ_monotone : Monotone (simplicialEvalδ L) := by
  intro a b hab
  induction L generalizing a b with
  | nil => exact hab
  | cons head tail h_rec =>
    dsimp only [simplicialEvalδ]
    split_ifs with h h' h' <;> exact h_rec (by grind)

variable (j : ℕ)

lemma le_simplicialEvalδ_self : j ≤ simplicialEvalδ L j := by
  induction L generalizing j with
  | nil => grind [simplicialEvalδ]
  | cons head tail h_rec => grind [simplicialEvalδ]

lemma simplicialEvalδ_eq_self_of_isAdmissible_and_lt (hL : IsAdmissible (n + 1) L)
    (hj : ∀ k ∈ L, j < k) : simplicialEvalδ L j = j := by
  induction L generalizing n j with
  | nil => grind [simplicialEvalδ]
  | cons a L h_rec => grind [simplicialEvalδ, → IsAdmissible.tail]

lemma simplicialEvalδ_eq_self_of_isAdmissible_cons (a : ℕ)
    (hL : IsAdmissible (n + 1) (a :: L)) : simplicialEvalδ L a = a :=
  simplicialEvalδ_eq_self_of_isAdmissible_and_lt _ _ hL.tail hL.head_lt

/-- Performing a simplicial insertion in a list is the same
as composition on the left by the corresponding face operator. -/
lemma standardδ_simplicialInsert (hL : IsAdmissible (n + 2) L) (j : ℕ) (hj : j < n + 2)
    (m₁ : ℕ) (hm₁ : n + L.length + 1 = m₁) :
    standardδ (k := n) (l := m₁) (simplicialInsert j L)
      (by grind [simplicialInsert_length]) =
    δ (Fin.ofNat _ j) ≫ standardδ L (by grind) := by
  induction L generalizing n j with
  | nil => grind [standardδ, simplicialInsert]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs
    · simp
    · have : ∀ (j k : ℕ) (h : j < k + 1), Fin.ofNat (k + 1) j = j := by simp
      have : δ (Fin.ofNat (n + 2) a) ≫ δ (.ofNat _ (j + 1)) = δ (.ofNat _ j) ≫ δ (.ofNat _ a) := by
        convert δ_comp_δ_nat (n := n) a j (by grind) (by grind) (by grind) <;> grind
      simp only [standardδ_cons, reassoc_of% this, h_rec hL.tail (j + 1) (by grind) (by grind)]

attribute [local grind] simplicialInsert_length simplicialInsert_isAdmissible in
/-- Using `standardδ_simplicialInsert`, we can prove that every morphism satisfying
`P_δ` is equal to some `standardδ` for some admissible list of indices, which shows
that every such morphism is equal to a morphism in "normal form". -/
theorem exists_normal_form_P_δ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_δ f) :
    ∃ L : List ℕ,
    ∃ m : ℕ,
    ∃ b : ℕ,
    ∃ h₁ : mk m = x, ∃ h₂ : y = mk b, ∃ h : m + L.length = b,
    (IsAdmissible (m + 1) L) ∧ f = standardδ L (by rwa [← h₁, h₂]) := by
  dsimp [P_δ] at hf
  rw [MorphismProperty.multiplicativeClosure_eq_multiplicativeClosure'] at hf
  induction hf with
  | id n =>
    use [], n.len, n.len, rfl, rfl, rfl, IsAdmissible.nil _
    exact (standardδ_nil _).symm
  | of f hf =>
    cases hf with | @δ n j
    use [j.val], n, (n + 1) , rfl, rfl, rfl
    constructor <;> simp [IsAdmissible, Nat.le_of_lt_add_one j.prop, standardδ]
  | @of_comp x' m j f g hf hg h_rec =>
    cases hf with | @δ n j
    obtain ⟨L₁, m₁, b₁, h₁', rfl, h', hL₁, e₁⟩ := h_rec
    obtain rfl : m₁ = n + 1 := congrArg (fun x ↦ x.len) h₁'
    use simplicialInsert j.val L₁, n, n + 1 + L₁.length, rfl, by grind, by grind, by grind
    subst_vars
    symm
    have := standardδ_simplicialInsert L₁ hL₁ j
    rw [show Fin.ofNat (n + 2) ↑j = j by simp] at this
    apply this (by grind)
    simp +arith [SimplexCategoryGenRel.mk]

/-- An admissible list is fully determined by its length and the attached function
`simplicialEvalδ`, which are both determined by the morphism in the usual `SimplexCategory`
corresponding to `standarδ` of this list.
This essentially shows that the admissible list from `exists_normal_form_P_δ` is unique. -/
lemma eq_of_simplicialEvalδ_eq
    (L₁ : List ℕ) (hL₁ : IsAdmissible (n + 1) L₁)
    (L₂ : List ℕ) (hL₂ : IsAdmissible (n + 1) L₂)
    (h : ∀ x < n + 1, simplicialEvalδ L₁ x = simplicialEvalδ L₂ x) :
    (L₁.length = L₂.length) → (L₁ = L₂) := by
  induction L₁ generalizing L₂ n with
  | nil => grind [List.eq_nil_of_length_eq_zero]
  | cons a L₁ hrec =>
    cases L₂ with
    | nil => tauto
    | cons b L₂ =>
      obtain rfl : a = b := by
        have ha₁ := h a
        have hb₁ := h b
        simp only [simplicialEvalδ, lt_self_iff_false, ↓reduceIte] at ha₁ hb₁
        split_ifs at ha₁ with ha₂ <;> split_ifs at hb₁ with hb₂ <;>
        grind [→ IsAdmissible.head_lt', le_simplicialEvalδ_self,
          simplicialEvalδ_eq_self_of_isAdmissible_and_lt, → IsAdmissible.tail,
          IsAdmissible, List.sorted_cons]
      intro h_length
      simp only [List.cons.injEq, true_and]
      refine hrec hL₁.tail _ hL₂.tail (fun x hx => ?_) (by grind)
      obtain hx | rfl := Nat.lt_add_one_iff_lt_or_eq.mp hx
      · obtain hax | rfl | hax := Nat.lt_trichotomy x a
        · grind [simplicialEvalδ]
        · grind [simplicialEvalδ_eq_self_of_isAdmissible_cons]
        · have := h (x - 1) (by grind)
          grind [simplicialEvalδ]
      · have := h n (by grind)
        grind [simplicialEvalδ, simplicialEvalδ_eq_self_of_isAdmissible_cons,
          → IsAdmissible.head_lt']

end NormalFormsP_δ

end SimplexCategoryGenRel
