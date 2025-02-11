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

open CategoryTheory

section AdmissibleLists
-- Impl. note: We are not bundling admissible lists as a subtype of `List ℕ` so that it remains
-- easier to perform inductive constructions and proofs on such lists, and we instead bundle
-- propositions asserting that various List constructions produce admissible lists.

variable (m : ℕ)
/-- A list of natural numbers [i₀, ⋯, iₙ]) is said to be `m`-admissible (for `m : ℕ`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`.
-/
def isAdmissible (L : List ℕ) : Prop :=
  List.Sorted (· < ·) L ∧
  ∀ k: ℕ, (h : k < L.length) → L[k] ≤ m + k

lemma isAdmissible_nil : isAdmissible m [] := by simp [isAdmissible]

variable {m}
/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
lemma isAdmissible_head_lt (a : ℕ) (L : List ℕ) (hl : isAdmissible m (a :: L)) :
    ∀ a' ∈ L, a < a' := by
  obtain ⟨h₁, h₂⟩ := hl
  intro i hi
  exact (List.sorted_cons.mp h₁).left i hi

/-- If `L` is (m+1)-admissible index, and `a` is natural number such that a ≤ m and a < L[0], then
  `a::L` is `m`-admissible -/
lemma isAdmissible_cons (L : List ℕ) (hL : isAdmissible (m + 1) L) (a : ℕ) (ha : a ≤ m)
    (ha' : (_ : 0 < L.length) → a < L[0]) : isAdmissible m (a :: L) := by
  dsimp [isAdmissible] at hL ⊢
  cases L with
  | nil => constructor <;> simp [ha]
  | cons head tail =>
    simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff,
      Nat.lt_one_iff, pos_of_gt, or_true, List.getElem_cons_zero,
      forall_const] at ha'
    have ⟨P₁, P₂⟩ := hL
    simp only [List.sorted_cons, List.mem_cons, forall_eq_or_imp] at P₁ ⊢
    constructor <;> repeat constructor
    · exact ha'
    · have h_tail := P₁.left
      rw [← List.forall_getElem] at h_tail ⊢
      intro i hi
      exact ha'.trans <| h_tail i hi
    · exact P₁
    · intro i hi
      cases i with
      | zero => simp [ha]
      | succ i =>
          simp only [List.getElem_cons_succ]
          haveI := P₂ i <| Nat.lt_of_succ_lt_succ hi
          rwa [← add_comm 1, ← add_assoc]

/-- The tail of an `m`-admissible list is (m+1)-admissible. -/
lemma isAdmissible_tail (a : ℕ) (l : List ℕ) (h : isAdmissible m (a::l)) :
      isAdmissible (m + 1) l := by
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨(List.sorted_cons.mp h₁).right, ?_⟩
  intro k hk
  haveI := h₂ (k + 1) (by simpa)
  simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Since they are strictly sorted, two admissible lists with same elements are equal -/
lemma isAdmissible_ext (L₁ : List ℕ) (L₂ : List ℕ)
    (hL₁ : isAdmissible m L₁) (hL₂ : isAdmissible m L₂)
    (h : ∀ x : ℕ, x ∈ L₁ ↔ x ∈ L₂) : L₁ = L₂ := by
  obtain ⟨hL₁, hL₁₂⟩ := hL₁
  obtain ⟨hL₂, hL₂₂⟩ := hL₂
  clear hL₁₂ hL₂₂
  induction L₁ generalizing L₂ with
  | nil =>
    simp only [List.nil_eq, List.eq_nil_iff_forall_not_mem]
    intro a ha
    exact List.not_mem_nil _ ((h a).mpr ha)
  | cons a L₁ h_rec =>
    cases L₂ with
    | nil =>
      simp only [List.nil_eq, List.eq_nil_iff_forall_not_mem]
      intro a ha
      exact List.not_mem_nil _ ((h a).mp ha)
    | cons b L₂ =>
      rw [List.cons_eq_cons]
      simp only [List.mem_cons] at h
      simp only [List.sorted_cons] at hL₁ hL₂
      obtain ⟨haL₁, hL₁⟩ := hL₁
      obtain ⟨hbL₂, hL₂⟩ := hL₂
      have hab : a = b := by
        haveI := h b
        simp only [true_or, iff_true] at this
        obtain hb | bL₁ := this
        · exact hb.symm
        · have ha := h a
          simp only [true_or, true_iff] at ha
          obtain hab | aL₂ := ha
          · exact hab
          · have f₁ := haL₁ _ bL₁
            have f₂ := hbL₂ _ aL₂
            linarith
      refine ⟨hab, ?_⟩
      apply h_rec L₂ _ hL₁ hL₂
      intro x
      subst hab
      haveI := h x
      by_cases hax : x = a
      · subst hax
        constructor
        · intro h₁
          haveI := haL₁ x h₁
          linarith
        · intro h₁
          haveI := hbL₂ x h₁
          linarith
      simpa [hax] using this

/-- An element of a `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
def isAdmissibleGetElemAsFin (L : List ℕ) (hl : isAdmissible m L) (k : ℕ)
    (hK : k < L.length) : Fin (m + k + 1) :=
  Fin.mk L[k] <| Nat.le_iff_lt_add_one.mp (by simp [hl.right])

/-- The head of an `m`-admissible list is a special case of this.  -/
@[simps!]
def isAdmissibleHead (a : ℕ) (L : List ℕ) (hl : isAdmissible m (a :: L)) : Fin (m + 1) :=
  isAdmissibleGetElemAsFin (a :: L) hl 0 (by simp)

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

/-- `simplicialInsert ` just adds one to the length. -/
lemma simplicialInsert_length (a : ℕ) (L : List ℕ) :
    (simplicialInsert a L).length = L.length + 1 := by
  induction L generalizing a with
  | nil => rfl
  | cons head tail h_rec =>
    simp only [simplicialInsert, List.length_cons]
    split_ifs with h <;> simp only [List.length_cons, add_left_inj]
    exact h_rec (a + 1)

/-- `simplicialInsert` preserves admissibility -/
theorem simplicialInsert_isAdmissible (L : List ℕ) (hL : isAdmissible (m + 1) L) (j : ℕ)
    (hj : j < m + 1) :
    isAdmissible m (simplicialInsert j L) := by
  have ⟨h₁, h₂⟩ := hL
  induction L generalizing j m with
  | nil =>
    simp only [simplicialInsert]
    constructor
    · simp
    · simp [j.le_of_lt_add_one hj]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs <;> rename_i ha
    · exact isAdmissible_cons _ hL _ (j.le_of_lt_add_one hj) (fun _ ↦ ha)
    · apply isAdmissible_cons
      · apply h_rec
        · exact isAdmissible_tail a L hL
        · simp [hj]
        · exact (List.sorted_cons.mp h₁).right
        · intro k hk
          haveI := h₂ (k + 1) (by simpa)
          conv_rhs at this => rw [k.add_comm 1, ← Nat.add_assoc]
          exact this
      · rw [not_lt] at ha
        apply ha.trans
        exact j.le_of_lt_add_one hj
      · rw [not_lt, Nat.le_iff_lt_add_one] at ha
        intro u
        cases L with
        | nil => simp [simplicialInsert, ha]
        | cons a' l' =>
          simp only [simplicialInsert]
          split_ifs <;> rename_i h'
          · exact ha
          · simp only [List.sorted_cons, List.mem_cons, forall_eq_or_imp] at h₁
            simpa using h₁.left.left

end AdmissibleLists

section NormalFormsP_σ

-- Impl note.: The definition is a bit akward with the extra parameter `k`, but this
-- is necessary in order to avoid some type theory hell when proving that `orderedInsert`
-- behaves as expected...

/-- Given a sequence `L = [ i 0, ..., i b ]`, `standardσ m L` i is the morphism
`σ (i b) ≫ … ≫ σ (i 0)`. The construction is provided for any list of natural numbers,
but it is intended to behave well only when the list is admissible. -/
def standardσ (m : ℕ) (L : List ℕ) (k : ℕ) (hK : L.length = k): mk (m + k) ⟶ mk m :=
  match L with
  | .nil => eqToHom (by rw [← hK]; rfl)
  | .cons a t => eqToHom
    (by rw [← hK, List.length_cons, Nat.add_comm t.length 1, Nat.add_assoc]) ≫
      standardσ (m + 1) t t.length rfl ≫ σ a

variable (m : ℕ) (L : List ℕ)
-- Because we gave a degree of liberty with the parameter `k`, we need this kind of lemma to ease
-- working with different `k`s
lemma standardσ_heq (k₁ : ℕ) (hk₁ : L.length = k₁) (k₂ : ℕ) (hk₂ : L.length = k₂) :
    HEq (standardσ m L k₁ hk₁) (standardσ m L k₂ hk₂) := by
  subst hk₁
  subst hk₂
  simp

/-- `simplicialEvalσ` is a lift to ℕ of `toSimplexCategory.map (standardσ m L _ _)).toOrderHom`,
but we define it this way to enable for less painful inductive reasoning,
and we keep the eqToHom shenanigans in the proof that it is indeed such a lift
(see `simplicialEvalσ_of_isAdmissible`). It is expected to produce the "correct result" only if
`L` is admissible, but as usual, it is more convenient to have it defined for any list. -/
def simplicialEvalσ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

@[simp]
private lemma eqToHom_toOrderHom_eq_cast {m n : ℕ}
    (h : SimplexCategory.mk m = SimplexCategory.mk n) :
    (eqToHom h).toOrderHom =
      (Fin.castOrderIso (congrArg (fun x ↦ x.len + 1) h)).toOrderEmbedding.toOrderHom := by
  ext
  haveI := congrArg (fun x ↦ x.len + 1) h
  simp only [SimplexCategory.len_mk, add_left_inj] at this
  subst this
  simp

variable {m}
-- most of the proof is about fighting with `eqToHom`s...
/-- We prove that simplicialEvalσ is indeed the lift we claimed when the list is admissible. -/
lemma simplicialEvalσ_of_isAdmissible (hL : isAdmissible m L)
    (k : ℕ) (hk : L.length = k)
    (j : ℕ) (hj : j < m + k + 1) :
    ((toSimplexCategory.map (standardσ m L k hk)).toOrderHom ⟨j, hj⟩ : ℕ)
      = simplicialEvalσ L j := by
  induction L generalizing m k with
  | nil =>
    simp [simplicialEvalσ, standardσ, eqToHom_map]
  | cons a L h_rec =>
    subst hk
    haveI := h_rec (isAdmissible_tail a L hL) L.length rfl <|
      by simpa [← Nat.add_comm 1 L.length, ← Nat.add_assoc] using hj
    simp only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, List.length_cons, standardσ,
      Functor.map_comp, eqToHom_map, toSimplexCategory_map_σ, SimplexCategory.σ,
      SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk,
      eqToHom_toOrderHom_eq_cast, Nat.add_eq, Nat.succ_eq_add_one, OrderHom.comp_coe,
      OrderHom.coe_mk, OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
      Function.comp_apply, Fin.predAbove, simplicialEvalσ, ← this]
    split_ifs with h₁ h₂ h₂
    · generalize_proofs _ pf
      rw [Fin.castOrderIso_apply pf ⟨j, hj⟩] at h₁
      simp only [Fin.cast_mk, Fin.coe_pred] at h₁ ⊢
      congr
    · exfalso
      rw [Fin.lt_def] at h₁
      simp only [Fin.coe_castSucc, Fin.val_natCast, not_lt] at h₁ h₂
      haveI := Nat.mod_eq_of_lt (isAdmissibleHead a L hL).prop
      dsimp [isAdmissibleHead] at this
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
      haveI := Nat.mod_eq_of_lt (isAdmissibleHead a L hL).prop
      dsimp [isAdmissibleHead] at this
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

lemma simplicialEvalσ_of_lt_mem (j : ℕ) (hj : ∀ k ∈ L, j ≤ k) :
    simplicialEvalσ L j = j := by
  induction L with
  | nil => simp [simplicialEvalσ]
  | cons a h h_rec =>
    dsimp only [simplicialEvalσ]
    split_ifs with h1 <;> {
      simp only [List.mem_cons, forall_eq_or_imp] at hj
      obtain ⟨hj₁, hj₂⟩ := hj
      haveI := h_rec hj₂
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
lemma standardσ_simplicialInsert (hL : isAdmissible (m + 1) L) (j : ℕ)
    (hj : j < m + 1) :
      standardσ m (simplicialInsert j L) (L.length + 1) (simplicialInsert_length _ _) =
        eqToHom (by rw [Nat.add_assoc, Nat.add_comm 1]) ≫
          standardσ (m + 1) L L.length rfl ≫
            σ j := by
  induction L generalizing m j with
  | nil => simp [standardσ, simplicialInsert]
  | cons a L h_rec =>
    simp only [List.length_cons, eqToHom_refl, simplicialInsert, Category.id_comp]
    split_ifs <;> rename_i h <;> simp only [standardσ]
    simp only [eqToHom_trans_assoc, Category.assoc]
    haveI := h_rec
      (isAdmissible_tail a L hL)
      (j + 1)
      (by simpa)
    simp only [eqToHom_refl, Category.id_comp] at this
    slice_rhs 3 5 => equals σ (↑(j + 1)) ≫ σ a =>
      have ha : a < m + 1 := Nat.lt_of_le_of_lt (not_lt.mp h) hj
      haveI := σ_comp_σ_nat a j ha hj (not_lt.mp h)
      generalize_proofs p p' at this
      -- We have to get rid of the natCasts...
      have ha₁ : (⟨a, p⟩ : Fin (m + 1 + 1)) = ↑a := by
        ext
        simp [Nat.mod_eq_of_lt p]
      have ha₂ : (⟨a, ha⟩ : Fin (m + 1)) = ↑a := by
        ext
        simp [Nat.mod_eq_of_lt ha]
      have hj₁ : (⟨j + 1, p'⟩ : Fin (m + 1 + 1)) = ↑(j + 1) := by
        ext
        simp [Nat.mod_eq_of_lt p']
      have hj₂ : (⟨j, hj⟩ : Fin (m + 1)) = ↑j := by
        ext
        simp [Nat.mod_eq_of_lt hj]
      rwa [← ha₁, ← ha₂, ← hj₁, ← hj₂]
    rw [← eqToHom_comp_iff] at this
    rotate_left
    · ext; simp [Nat.add_assoc, Nat.add_comm 1, Nat.add_comm 2]
    · rw [← reassoc_of%this]
      simp only [eqToHom_trans_assoc]
      rw [← heq_iff_eq, eqToHom_comp_heq_iff, HEq.comm, eqToHom_comp_heq_iff]
      apply heq_comp <;> try simp [simplicialInsert_length, heq_iff_eq]
      apply standardσ_heq

/-- Using the above property, we can prove that every morphism satisfying `P_σ` is equal to some
`standardσ` for some admissible list of indices. Because morphisms of the form `standardσ` have a
rather  constrained sources and targets, we have again to splice in some `eqToHom`'s to make
everything work. -/
theorem exists_normal_form_P_σ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_σ f) :
    ∃ L : List ℕ,
    ∃ m : ℕ,
    ∃ b : ℕ,
    ∃ h₁ : mk m = y,
    ∃ h₂ : x = mk (m + b),
    ∃ h: (L.length = b),
    isAdmissible m L ∧ f = eqToHom h₂ ≫ standardσ m L b h ≫ eqToHom h₁ := by
  induction hf with
  | @id n =>
    use [], n, 0, rfl, rfl, rfl, isAdmissible_nil _
    simp [standardσ]
  | @σ m j =>
    use [j.val], m, 1 , rfl, rfl, rfl
    constructor <;> simp [isAdmissible, Nat.le_of_lt_add_one j.prop, standardσ]
  | @comp m j x' g hg h_rec =>
    obtain ⟨L₁, m₁, b₁, h₁', h₂', h', hL₁, e₁⟩ := h_rec
    have hm₁ : m₁ = m + 1 := by haveI := h₁'; apply_fun (fun x ↦ x.len) at this; exact this
    use simplicialInsert j.val L₁, m, b₁ + 1, rfl, ?_, ?_, ?_
    rotate_right 3
    · rwa [← Nat.add_comm 1, ← Nat.add_assoc, ← hm₁]
    · rw [simplicialInsert_length, h']
    · exact simplicialInsert_isAdmissible _ (by rwa [← hm₁]) _ (j.prop)
    · subst e₁
      subst h'
      rw [standardσ_simplicialInsert]
      · simp only [Category.assoc, Fin.cast_val_eq_self, eqToHom_refl, Category.comp_id,
        eqToHom_trans_assoc]
        subst m₁
        simp
      · subst m₁
        exact hL₁
      · exact j.prop

section MemIsAdmissible

lemma mem_isAdmissible_of_lt_and_eval_eq_eval_succ (hL : isAdmissible m L)
    (j : ℕ) (hj₁ : j < m + L.length) (hj₂ : simplicialEvalσ L j = simplicialEvalσ L j.succ) :
    j ∈ L := by
  induction L generalizing m with
  | nil => simp [simplicialEvalσ] at hj₂
  | cons a L h_rec =>
    simp only [List.mem_cons]
    by_cases hja : j = a
    · left; exact hja
    · right
      haveI := (h_rec (isAdmissible_tail a L hL))
      apply this
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
          simp only [isAdmissible, List.sorted_cons, List.length_cons] at hL
          obtain ⟨⟨hL₁, hL₂⟩, hL₃⟩ := hL
          obtain h | h | h := Nat.lt_trichotomy j a
          · haveI : simplicialEvalσ L j ≤ simplicialEvalσ L (j + 1) :=
              simplicialEvalσ_monotone L (by simp)
            have ha := simplicialEvalσ_of_lt_mem L a (fun x h ↦ (le_of_lt (hL₁ x h)))
            have hj₁ := (simplicialEvalσ_monotone L h)
            linarith
          · exfalso; exact hja h
          · haveI := simplicialEvalσ_of_lt_mem L a (fun x h ↦ (le_of_lt (hL₁ x h)))
            rw [← this] at h₁ h₂
            have ha₁ := le_antisymm (simplicialEvalσ_monotone L (le_of_lt h)) h₁
            have ha₂ := simplicialEvalσ_of_lt_mem L (a + 1) (fun x h ↦ (hL₁ x h))
            rw (occs := .pos [2]) [← this] at ha₂
            rw [ha₁, hj₂] at ha₂
            by_cases h': simplicialEvalσ L (j + 1) = 0
            · exact h'
            · rw [Nat.sub_one_add_one h'] at ha₂
              have ha₃ := simplicialEvalσ_monotone L h
              rw [Nat.succ_eq_add_one] at ha₃
              linarith
        · exact hj₂

lemma lt_and_eval_eq_eval_succ_of_mem_isAdmissible (hL : isAdmissible m L) (j : ℕ) (hj : j ∈ L) :
    j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L j.succ := by
  induction L generalizing m with
  | nil => simp [simplicialEvalσ] at hj
  | cons a L h_rec =>
    constructor
    · simp only [isAdmissible, List.sorted_cons] at hL
      obtain ⟨⟨hL₁, hL₂⟩, hL₃⟩ := hL
      haveI : ∀ (k : ℕ), (_ : k < (a::L).length) → (a::L)[k] < m + (a::L).length := by
        intro k hk
        apply (hL₃ k hk).trans_lt
        simpa using hk
      obtain ⟨k, hk, hk'⟩ := List.mem_iff_getElem.mp hj
      subst hk'
      exact this k hk
    · simp only [List.mem_cons] at hj
      obtain h | h := hj
      · subst h
        simp only [simplicialEvalσ, Nat.succ_eq_add_one]
        simp only [isAdmissible, List.sorted_cons] at hL
        obtain ⟨⟨hL₁, hL₂⟩, hL₃⟩ := hL
        rw [simplicialEvalσ_of_lt_mem L j (fun x hx ↦ le_of_lt (hL₁ x hx)),
          simplicialEvalσ_of_lt_mem L (j + 1) (fun x hx ↦ (hL₁ x hx))]
        simp
      · simp only [simplicialEvalσ, Nat.succ_eq_add_one]
        obtain ⟨h_rec₁, h_rec₂⟩ := h_rec (isAdmissible_tail a L hL) h
        split_ifs with h₁ h₂ h₂
        · rw [h_rec₂]
        · rw [h_rec₂]
          rw [not_lt] at h₂
          haveI : simplicialEvalσ L j ≤ simplicialEvalσ L (j + 1) :=
            simplicialEvalσ_monotone L (by simp)
          linarith
        · rw [not_lt] at h₁
          linarith
        · rw [h_rec₂]

/-- The key point: we can characterize elements in an admissible list as
exactly those for which `simplicialEvalσ` takes the same value two times successively. -/
lemma mem_isAdmissible_iff (hL : isAdmissible m L) (j : ℕ) :
    j ∈ L ↔
      j < m + L.length ∧
      simplicialEvalσ L j =
        simplicialEvalσ L j.succ := by
  constructor
  · intro hj
    exact lt_and_eval_eq_eval_succ_of_mem_isAdmissible _ hL j hj
  · rintro ⟨hj₁, hj₂⟩
    exact mem_isAdmissible_of_lt_and_eval_eq_eval_succ L hL j hj₁ hj₂

end MemIsAdmissible

end NormalFormsP_σ

section NormalFormsP_δ

/-- Given a sequence `L = [ i 0, ..., i b ]`, `standardδ n L` i is the morphism
`δ (i b) ≫ … ≫ δ (i 0)`. The construction is provided for any list of natural numbers,
but it is intended to behave well only when the list is δ-admissible. -/
def standardδ (n : ℕ) (L: List ℕ) (k : ℕ) (hK : L.length = k): mk n ⟶ mk (n + k) :=
  match L with
  | .nil => eqToHom (by rw [← hK]; rfl)
  | .cons a t =>
      δ a ≫ (standardδ (n + 1) t t.length rfl) ≫
        eqToHom (by ext; simp [← hK, Nat.add_assoc, Nat.add_comm 1])

-- Because we gave a degree of liberty with the parameter `k`, we need this kind of lemma to ease
-- working with different `k`s
lemma standardδ_heq (n : ℕ) (L: List ℕ) (k₁ : ℕ) (hk₁ : L.length = k₁)
    (k₂ : ℕ) (hk₂ : L.length = k₂) : HEq (standardδ n L k₁ hk₁) (standardδ n L k₂ hk₂) := by
  subst hk₁
  subst hk₂
  simp

/-- `simplicialEvalδ` is a lift to ℕ of `toSimplexCategory.map (standardδ m L _ _)).toOrderHom`,
but we define it this way to enable for less painful inductive reasoning,
and we keep the eqToHom shenanigans in the proof that it is indeed such a lift
(see `simplicialEvalδ_of_isAdmissible`). It is expected to produce the "correct result" only if
`L` is admissible, but as usual, it is more convenient to have it defined for any list. -/
def simplicialEvalδ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => simplicialEvalδ L (if j < a then j else j + 1)

variable {n : ℕ} (L : List ℕ)

/-- We prove that simplicialEvalδ is indeed the lift we claimed when the list is admissible. -/
lemma simplicialEvalδ_of_isAdmissible (hL : isAdmissible (n + 1) L)
    (k : ℕ) (hk : L.length = k)
    (j : ℕ) (hj : j < n + 1) :
    ((toSimplexCategory.map (standardδ n L k hk)).toOrderHom ⟨j, hj⟩ : ℕ)
      = simplicialEvalδ L j := by
  induction L generalizing j n k with
  | nil =>
    simp [standardδ, simplicialEvalδ, eqToHom_map, eqToHom_toOrderHom_eq_cast]
  | cons a L h_rec =>
    simp only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, standardδ, Functor.map_comp,
      toSimplexCategory_map_δ, SimplexCategory.δ, SimplexCategory.mkHom, eqToHom_map,
      SimplexCategory.comp_toOrderHom, eqToHom_toOrderHom_eq_cast, Nat.add_eq, Nat.add_zero,
      Nat.succ_eq_add_one, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Function.comp_apply,
      Fin.succAboveOrderEmb_apply, Fin.castOrderIso_apply, Fin.coe_cast, simplicialEvalδ]
    have adm_L : isAdmissible (n + 1 + 1) L := isAdmissible_tail a L hL
    split_ifs with hj₁
    · rw [Fin.succAbove]
      split_ifs with hj₂
      · apply h_rec (n := n + 1) (j := j) (hj := Nat.lt_succ_of_lt hj) adm_L
      · simp only [Fin.lt_def, Fin.coe_castSucc, Fin.val_natCast, not_lt] at hj₁ hj₂
        haveI := h_rec (j := j) (hj := Nat.lt_succ_of_lt hj) adm_L L.length rfl
        rw [← this]
        have ha₁ : a < n + 1 + 1 := by
          dsimp only [isAdmissible] at hL
          haveI := hL.right 0 (by simp)
          simp only [List.getElem_cons_zero, tsub_zero] at this
          omega
        rw [Nat.mod_eq_of_lt ha₁] at hj₂
        omega
    · rw [Fin.succAbove]
      split_ifs with hj₂
      · simp only [Fin.lt_def, Fin.coe_castSucc, Fin.val_natCast, not_lt] at hj₁ hj₂
        haveI := h_rec (j := j) adm_L L.length rfl
        have ha₁ : a < n + 1 + 1 := by
          dsimp only [isAdmissible] at hL
          haveI := hL.right 0 (by simp)
          simp only [List.getElem_cons_zero, tsub_zero] at this
          omega
        rw [Nat.mod_eq_of_lt ha₁] at hj₂
        omega
      · rw [not_lt] at hj₁ hj₂
        simp only [Fin.succ_mk]
        apply h_rec adm_L

lemma simplicialEvalδ_monotone : Monotone (simplicialEvalδ L) := by
  intro a b hab
  induction L generalizing a b with
  | nil => exact hab
  | cons head tail h_rec =>
    dsimp only [simplicialEvalδ]
    split_ifs with h h' h'
    · exact h_rec hab
    · have hab' : a ≤ b + 1 := by omega
      exact h_rec hab'
    · have hab' : a + 1 ≤ b := by omega
      exact h_rec hab'
    · exact h_rec (Nat.succ_le_succ hab)

variable (j : ℕ)

lemma le_simplicialEvalδ_self : j ≤ simplicialEvalδ L j := by
  induction L generalizing j with
  | nil => simp [simplicialEvalδ]
  | cons head tail h_rec =>
    dsimp only [simplicialEvalδ]
    split_ifs with h
    · haveI := h_rec j
      omega
    · have hj := simplicialEvalδ_monotone tail (j.le_succ)
      haveI := h_rec j
      exact this.trans hj

lemma simplicialEvalδ_eq_self_of_isAdmissible_and_lt (hL : isAdmissible (n + 1) L)
    (hj : ∀ k ∈ L, j < k) : simplicialEvalδ L j = j := by
  induction L generalizing n j with
  | nil => simp [simplicialEvalδ]
  | cons a L h_rec =>
    dsimp only [simplicialEvalδ]
    split_ifs with h
    · apply h_rec _ (isAdmissible_tail a L hL)
      simp only [List.mem_cons, forall_eq_or_imp] at hj
      exact hj.right
    · simp only [not_lt] at h
      simp only [List.mem_cons, forall_eq_or_imp] at hj
      obtain ⟨hj₁, hj₂⟩ := hj
      linarith

lemma simplicialEvalδ_eq_self_of_isAdmissible_cons (a : ℕ)
    (hL : isAdmissible (n + 1) (a :: L)) : simplicialEvalδ L a = a := by
  apply simplicialEvalδ_eq_self_of_isAdmissible_and_lt _ _ (isAdmissible_tail a L hL)
  simp only [isAdmissible, List.sorted_cons] at hL
  tauto

/-- Performing a simplicial insert in a list is (up to some unfortunate `eqToHom`) the same
as composition on the right by the corresponding face operator. -/
lemma standardδ_simplicialInsert (hL : isAdmissible (n + 2) L) (j : ℕ) (hj : j < n + 2) :
    standardδ n (simplicialInsert j L) (L.length + 1) (simplicialInsert_length _ _) =
        δ j ≫ standardδ (n + 1) L L.length rfl ≫
          eqToHom (by rw [← Nat.add_comm 1 L.length, Nat.add_assoc]) := by
  induction L generalizing n j with
  | nil =>
    simp [standardδ, simplicialInsert]
  | cons a L h_rec =>
    simp only [List.length_cons, eqToHom_refl, simplicialInsert, Category.id_comp]
    split_ifs <;> rename_i h <;> simp only [standardδ, eqToHom_refl, Category.comp_id,
      Category.assoc]
    haveI : isAdmissible (n + 2) (a::L) := by
      rw [isAdmissible] at hL ⊢
      refine ⟨hL.left, ?_⟩
      intro k hk
      haveI := hL.right k hk
      simp only [not_lt] at h
      omega
    haveI := h_rec (isAdmissible_tail a L hL) (j + 1) (by omega)
    simp only [eqToHom_refl, Category.id_comp] at this
    simp only [gt_iff_lt, not_lt] at h
    slice_rhs 1 2 => equals δ a ≫ δ (↑(j + 1)) =>
      haveI := hL.right 0 (by simp)
      simp only [List.getElem_cons_zero, tsub_zero] at this
      -- same dance as previously: getting rid of natCasts
      have simplicial_id := δ_comp_δ_nat (n:=n) a j (h.trans_lt hj) hj h
      generalize_proofs p p' p'' at simplicial_id
      have ha₁ : (⟨a, p⟩ : Fin (n + 1 + 1)) = ↑a := by ext; simp [Nat.mod_eq_of_lt p]
      have ha₂ : (⟨a, p''⟩ : Fin (n + 1 + 2)) = ↑a := by ext; simp [Nat.mod_eq_of_lt p'']
      have hj₁ : (⟨j + 1, p'⟩ : Fin (n + 1 + 2)) = ↑(j + 1) := by ext; simp [Nat.mod_eq_of_lt p']
      have hj₂ : (⟨j, hj⟩ : Fin (n + 1 + 1)) = ↑j := by ext; simp [Nat.mod_eq_of_lt hj]
      symm
      rwa [← ha₁, ← ha₂, ← hj₁, ← hj₂]
    slice_rhs 2 4 => rw [← this]
    rw [← heq_iff_eq, ← Category.assoc, comp_eqToHom_heq_iff]
    congr 1 <;> try { ext; simp [simplicialInsert_length, ← Nat.add_comm 1 L.length, add_assoc] }
    simp only [heq_comp_eqToHom_iff]
    apply standardδ_heq

/-- Using the above property, we can prove that every morphism satisfying `P_δ` is equal to some
`standardδ` for some admissible list of indices. Because morphisms of the form `standardδ` have a
rather  constrained sources and targets, we have again to splice in some `eqToHom`'s to make
everything work. -/
theorem exists_normal_form_P_δ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_δ f) :
    ∃ L : List ℕ,
    ∃ m : ℕ,
    ∃ b : ℕ,
    ∃ h₁ : x = mk m,
    ∃ h₂ : mk (m + b) = y,
    ∃ h: (L.length = b),
    (isAdmissible (m + 1) L) ∧ f = eqToHom h₁ ≫ (standardδ m L b h) ≫ eqToHom h₂ := by
  rw [P_δ_eq_P_δ'] at hf
  induction hf with
  | @id n =>
    use [], n, 0, rfl, rfl, rfl, isAdmissible_nil _
    simp [standardδ]
  | @δ n j =>
    use [j.val], n, 1 , rfl, rfl, rfl
    constructor <;> simp [isAdmissible, Nat.le_of_lt_add_one j.prop, standardδ]
  | @comp x' m j g hg h_rec =>
    obtain ⟨L₁, m₁, b₁, h₁', h₂', h', hL₁, e₁⟩ := h_rec
    have hm₁ : m + 1 = m₁ := by haveI := h₁'; apply_fun (fun x ↦ x.len) at this; exact this
    use simplicialInsert j.val L₁, m, b₁ + 1, rfl, ?_, ?_, ?_
    rotate_right 3
    · rwa [← Nat.add_comm 1, ← Nat.add_assoc, hm₁]
    · rw [simplicialInsert_length, h']
    · exact simplicialInsert_isAdmissible _ (by rwa [hm₁]) _ (j.prop)
    · subst e₁
      subst h'
      rw [standardδ_simplicialInsert]
      · simp only [Category.assoc, Fin.cast_val_eq_self, eqToHom_refl, Category.comp_id,
        eqToHom_trans_assoc]
        subst m₁
        simp
      · subst m₁
        exact hL₁
      · exact j.prop

private lemma head_eq_head_of_simplicialEvalδ_eq
    (L₁ : List ℕ) (a : ℕ) (hL₁ : isAdmissible (n + 1) (a :: L₁))
    (L₂ : List ℕ) (b : ℕ) (hL₂ : isAdmissible (n + 1) (b :: L₂))
    (h : ∀ x < n + 1, simplicialEvalδ (a::L₁) x = simplicialEvalδ (b::L₂) x) :
    a = b := by
  have ha₁ := h a
  simp only [simplicialEvalδ, lt_self_iff_false, ↓reduceIte] at ha₁
  have hb₁ := h b
  simp only [simplicialEvalδ, lt_self_iff_false, ↓reduceIte] at hb₁
  split_ifs at ha₁ with ha₂ <;> split_ifs at hb₁ with hb₂
  · omega
  · exfalso
    haveI : simplicialEvalδ L₂ a = a := by
      apply simplicialEvalδ_eq_self_of_isAdmissible_and_lt L₂ _ (isAdmissible_tail b L₂ hL₂)
      simp only [isAdmissible, List.sorted_cons, List.length_cons] at hL₂
      intro k hk
      haveI := hL₂.left.left k hk
      omega
    rw [this] at ha₁
    haveI := le_simplicialEvalδ_self L₁ (a + 1)
    obtain hb | hb := Nat.lt_add_one_iff_lt_or_eq.mp (isAdmissibleHead b L₂ hL₂).prop
    · haveI := hb₁ hb
      haveI := ha₁ (ha₂.trans hb)
      linarith
    · dsimp only [isAdmissibleHead_val] at hb
      subst hb
      omega
  · exfalso
    haveI : simplicialEvalδ L₁ b = b := by
      apply simplicialEvalδ_eq_self_of_isAdmissible_and_lt L₁ _ (isAdmissible_tail a L₁ hL₁)
      simp only [isAdmissible, List.sorted_cons, List.length_cons] at hL₁
      intro k hk
      haveI := hL₁.left.left k hk
      omega
    rw [this] at hb₁
    haveI := le_simplicialEvalδ_self L₂ (b + 1)
    obtain ha | ha := Nat.lt_add_one_iff_lt_or_eq.mp (isAdmissibleHead a L₁ hL₁).prop
    · haveI := ha₁ ha
      haveI := hb₁ (hb₂.trans ha)
      linarith
    · dsimp at ha
      subst ha
      omega
  · omega

/-- Again, the key point is that admissible lists are determined by simplicialEvalδ, which only
depends on the realization of `standardδ` in the usual simplex category. -/
lemma eq_of_simplicialEvalδ_eq
    (L₁ : List ℕ) (hL₁ : isAdmissible (n + 1) L₁)
    (L₂ : List ℕ) (hL₂ : isAdmissible (n + 1) L₂)
    (h : ∀ x < n + 1, simplicialEvalδ L₁ x = simplicialEvalδ L₂ x) :
    (L₁.length = L₂.length) → (L₁ = L₂) := by
  induction L₁ generalizing L₂ n with
  | nil =>
    intro a
    symm at a ⊢
    simpa using a
  | cons a L₁ hrec =>
    cases L₂ with
    | nil => tauto
    | cons b L₂ =>
      haveI : a = b := head_eq_head_of_simplicialEvalδ_eq L₁ a hL₁ L₂ b hL₂ h
      subst this
      simp only [List.cons.injEq, true_and]
      intro h_length
      apply hrec (isAdmissible_tail a L₁ hL₁) _ (isAdmissible_tail a L₂ hL₂)
      · intro x hx
        obtain hx | hx := Nat.lt_add_one_iff_lt_or_eq.mp hx
        · haveI := h x hx
          by_cases hax : x < a
          · simpa [simplicialEvalδ, hax] using this
          · haveI := h x
            simp only [simplicialEvalδ] at this
            simp only [not_lt] at hax
            split_ifs at this with hax₁
            · exact this hx
            · cases x with
              | zero =>
                haveI : a = 0 := by omega
                subst this
                rw [simplicialEvalδ_eq_self_of_isAdmissible_cons L₁ 0 hL₁
                  , simplicialEvalδ_eq_self_of_isAdmissible_cons L₂ 0 hL₂]
              | succ x =>
                haveI := h x (Nat.lt_of_add_right_lt hx)
                simp only [simplicialEvalδ] at this
                split_ifs at this
                · simp at hax₁
                  haveI : a = x + 1 := by omega
                  subst this
                  rw [simplicialEvalδ_eq_self_of_isAdmissible_cons L₁ (x + 1) hL₁
                    , simplicialEvalδ_eq_self_of_isAdmissible_cons L₂ (x + 1) hL₂]
                · linarith
        · subst hx
          obtain ha | ha := Nat.lt_add_one_iff_lt_or_eq.mp (isAdmissibleHead a L₁ hL₁).prop
          · dsimp at ha
            haveI := h n (by simp)
            simp only [simplicialEvalδ] at this
            split_ifs at this <;> linarith
          · dsimp at ha
            subst ha
            rw [simplicialEvalδ_eq_self_of_isAdmissible_cons L₁ (n + 1) hL₁
              , simplicialEvalδ_eq_self_of_isAdmissible_cons L₂ (n + 1) hL₂]
      · simpa using h_length

end NormalFormsP_δ

end SimplexCategoryGenRel
