/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Extension.Linear
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Interval.Set.Infinite

/-!
# Ramsey's theorem for infinite hypergraphs

Ramsey's theorem for infinite hypergraphs states that, for any colouring of the `k`-subsets of an
infinite set `S` with a finite set of colours, there is an infinite subset `S₀` of `S`
so that all `k`-subsets of `S₀` have the same colour. We prove this theorem, and state
a few equivalent versions.

## Main results

The results below all work even if the colours are in `Sort` rather than `Type`, since
'colour according to whether X is true' is a common application of Ramsey results.

- `Ramsey.exists_monochromatic_infinite_subset`: the infinite hypergraph Ramsey theorem;
  if we colour every `s : Finset α` with `s.card = k` in an `Infinite` type `α`
  with a colour from a finite set of colours, then there is an
  infinite `y : Set α` whose `k`-element subsets all have the same colour.

- `Ramsey.exists_monochromatic_subsequence_tuple`: the infinite hypergraph Ramsey theorem where the
  objects being coloured are embeddings `Fin k ↪o ℕ`, and the infinite monochromatic subset is
  instead a subsequence.

- `Ramsey.exists_monochromatic_subsequence_finset`: the infinite hypergraph Ramsey theorem where the
  objects being coloured are terms `s : Finset ℕ` with `s.card = k`.

- `Ramsey.exists_strong_monochromatic_subsequence_finset` : a version of the infinite hypergraph
  Ramsey theorem where the objects being coloured are terms `s : Finset ℕ` with `s.card < k`,
  and the colour belongs to a type depending on the cardinality of `s`. The theorem states that
  there is a monochromatic subsequence in which the colour of a subset depends only on its
  cardinality.

- `Ramsey.exists_strong_monochromatic_subsequence_finset'` : a type-homogeneous version of the
  unprimed theorem.

## Implementation Details

The theorem is often stated and thought of in terms of arbitrary sets and their subsets,
but to make the inductive proof work smoothly, it is convenient to work in the type `ℕ`,
and to think of everything as a function. This way, instead of considering with images of sets
and the relevant coercions, we can deal with compositions of functions.

Specifically, we encode each `s : Finset ℕ` with `s.card = k` as an order-embedding `s : Fin k ↪o ℕ`
and we think of an subsequence `g : ℕ ↪o ℕ` instead of an infinite subset of `ℕ`. Once the proof
is done, it is easy to derive the more traditionally stated versions.

Doing things this way isn't necessary, but should be the right perspective when proving more
complicated but related Ramsey results such as the canonical hypergraph Ramsey theorem,
in which the global ordering is crucial even for the statement.

## TODO : Finite versions.

The infinite version of hypergraph Ramsey is stronger than the finite versions; it implies them
via Konig's infinity lemma, a standard compactness result. This method won't give explicit bounds,
but gives a straightforward way to get to the finite results from what is done here.
-/


open Set Function

variable {α κ : Type*} [Finite κ] {f g : ℕ ↪o ℕ} {i j k n : ℕ}

theorem orderEmbedding_fin_finite {α : Type*} [Preorder α] [LocallyFiniteOrderBot α] (k : ℕ)
    (a : α) : Set.Finite {s : Fin (k + 1) ↪o α | s ⊤ ≤ a} := by
  refine Set.Finite.of_finite_image (f := fun s ↦ range s) ?_ fun _ _ _ _ ↦ by
    rw [OrderEmbedding.range_inj]
    exact id
  refine (finite_Iic a).finite_subsets.subset ?_
  rintro _ ⟨s, (hs : s ⊤ ≤ a), rfl⟩ _ ⟨i, rfl⟩
  exact (s.monotone le_top).trans hs

theorem exists_enum_set_card (k : ℕ) : ∃ (e : ℕ ≃ (Fin (k + 1) ↪o ℕ)), Monotone (e · ⊤) :=
  exists_nat_equiv_monotone_comp (α := Fin (k + 1) ↪o ℕ) (fun s ↦ s ⊤)
   fun m ↦ (orderEmbedding_fin_finite k m).subset fun _ (hs : _ = _) ↦ hs.le

namespace Ramsey

/-- A function `f` is `Stable` with respect to `s` if it is the identity on `s`. -/
def Stable (s : Fin k ↪o ℕ) (f : ℕ ↪o ℕ) : Prop := ∀ i, f (s i) = s i

theorem Stable.trans_eq {s : Fin k ↪o ℕ} (h : Stable s f) : s.trans f = s :=
  RelEmbedding.ext fun i ↦ by simp [h i]

theorem Stable.apply_of_le {s : Fin k ↪o ℕ} (h : Stable s f) (i : Fin k) (hn : n ≤ s i) : f n = n :=
  Nat.orderEmbedding_apply_eq_self_of_le f (h _).le hn

theorem Stable.mono {s t : Fin (k + 1) ↪o ℕ} (h : Stable s f) (hts : t ⊤ ≤ s ⊤) : Stable t f :=
  fun _ ↦ h.apply_of_le _ ((t.monotone le_top).trans hts)

/-- Given a colouring `c` of all `(k + 1)`-sets in `ℕ`, a `k`-set `s` is right-monochromatic if
  all sets obtained by adding an element above the maximum of `s` have the same colour. -/
def RightMonochromatic (c : (Fin (k + 1) ↪o ℕ) → κ) (s : Fin k ↪o ℕ) : Prop :=
  ∃ c₀, ∀ (x : ℕ) (hx : ∀ i, s i < x), c (appendRight s x hx) = c₀

omit [Finite κ] in
theorem rightMonochromatic_iff_forall {k : ℕ} {c : (Fin (k + 1) ↪o ℕ) → κ} {s : Fin k ↪o ℕ} :
    RightMonochromatic c s ↔ ∀ ⦃x y⦄ (hx : ∀ i, s i < x) (hy : ∀ i, s i < y),
      c (appendRight s x hx) = c (appendRight s y hy) := by
  refine ⟨fun ⟨c₀, hc₀⟩ x y hxy hx ↦ by rw [hc₀, hc₀], fun h ↦ ?_⟩
  induction' k using Nat.recAux with k
  · exact ⟨c <| appendRight s 0 (by simp), fun x _ ↦ by simpa using @h _ _⟩
  exact ⟨c <| appendRight s (s ⊤ + 1) (fun i ↦ Nat.lt_add_one_iff.2 (s.monotone le_top) ),
    fun x hx ↦ by rw [eq_comm,h]⟩

omit [Finite κ] in
theorem rightMonochromatic_iff_forall' {k : ℕ} {c : (Fin (k + 1) ↪o ℕ) → κ} {s : Fin k ↪o ℕ} :
    RightMonochromatic c s ↔ ∀ ⦃x y⦄ (hxy : x < y) (hx : ∀ i, s i < x),
      c (appendRight s x hx) = c (appendRight s y (fun i ↦ (hx i).trans hxy)) := by
  rw [rightMonochromatic_iff_forall]
  refine ⟨fun h x y hxy hx ↦ h hx fun i ↦ (hx i).trans hxy, fun h x y hx hy ↦ ?_⟩
  obtain (hlt | hle) := lt_or_ge x y
  · rw [h hlt]
  obtain (rfl | hlt) := hle.eq_or_lt
  · rfl
  rw [h hlt]

omit [Finite κ] in
theorem RightMonochromatic.trans_right {c : (Fin (k + 1) ↪o ℕ) → κ} {s : Fin k ↪o ℕ}
    (h : RightMonochromatic c s) (hf : Stable s f) : RightMonochromatic c (s.trans f) :=
  let ⟨c₀, h⟩ := h
  ⟨c₀, fun _ _ ↦ by simp [hf.trans_eq, h]⟩

omit [Finite κ] in
theorem RightMonochromatic.trans_left {c : (Fin (k + 1) ↪o ℕ) → κ} {s : Fin k ↪o ℕ}
    (h : RightMonochromatic c (s.trans g)) : RightMonochromatic (fun x ↦ c (x.trans g)) s :=
  let ⟨c₀, h⟩ := h
  ⟨c₀, fun x hx ↦ by simp [← h (g x) fun i ↦ g.strictMono (hx i)]⟩

/-- Given a `k`-set `s` in `ℕ` and a colouring of the `(k + 1)`-sets, we can find a subsequence
  on which `s` is right-monochromatic. -/
theorem exists_rightMonochromatic_trans (c : (Fin (k + 1) ↪o ℕ) → κ) (s : Fin k ↪o ℕ) :
    ∃ (g : ℕ ↪o ℕ), Stable s g ∧ RightMonochromatic (fun x ↦ c (x.trans g)) s := by
  classical
  have hinf : Infinite {x // ∀ i, s i < x} := by
    obtain ⟨b, (hb : ∀ _, _)⟩ := Finite.bddAbove (finite_range s)
    refine infinite_coe_iff.2 (show {x | ∀ i, s i < x}.Infinite from (Ioi_infinite b).mono ?_)
    simp only [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hb
    exact fun j (hbj : b < j) i ↦ (hb _).trans_lt hbj

  obtain ⟨c₀, hc₀⟩ := Finite.exists_infinite_fiber (α := {x // ∀ i, s i < x})
    (fun i ↦ c (appendRight s i.1 i.2))
  replace hc₀ := (infinite_coe_iff.1 hc₀).image Subtype.val_injective.injOn
  set f := @Nat.orderEmbeddingOfSet _ hc₀.to_subtype _
  set g' := fun (n : ℕ) ↦ if ∀ i, s i < n then f n else n with hg'_def

  have hg' : StrictMono g' := by
    intro i j hij
    simp_rw [hg'_def]
    obtain (h1 | ⟨a, h2⟩) := forall_or_exists_not (fun x ↦ s x < i)
    · rwa [if_pos h1, if_pos (fun i ↦ (h1 i).trans hij), f.lt_iff_lt]
    rw [if_neg (fun h ↦ h2 (h _))]
    exact hij.trans_le (le_trans (le_inf (f.strictMono.id_le _) rfl.le) (inf_le_ite _ _ _))

  set g := OrderEmbedding.ofStrictMono g' hg' with hg_def

  have hls : Stable s g := fun i ↦ by
    suffices (∀ j, j < i) → f (s i) = s i by simpa [hg_def, hg'_def]
    exact fun h ↦ False.elim <| (h i).ne rfl

  refine ⟨g, hls, ⟨c₀, fun x hx ↦ ?_⟩⟩
  simp only [appendRight_trans]
  have h_mem := mem_range_self (f := f) x
  simp only [f, @Nat.orderEmbeddingOfSet_range _ hc₀.to_subtype _, mem_image, mem_preimage,
    mem_singleton_iff, Subtype.exists, exists_and_right, exists_eq_right] at h_mem
  obtain ⟨hx', h'⟩ := h_mem
  rw [← h']
  simp [hg_def, hg'_def, hx]
  congr
  rw [hls.trans_eq]

/-- Choose a subsequence that cleans up a particular `k`-set `s`. -/
noncomputable def refineAt (c : (Fin (k + 1) ↪o ℕ) → κ) (s : Fin k ↪o ℕ) : ℕ ↪o ℕ :=
  Classical.choose <| exists_rightMonochromatic_trans c s

theorem refineAt_stable (c : (Fin (k + 1) ↪o ℕ) → κ) (s : Fin k ↪o ℕ) :
    Stable s (refineAt c s) :=
  (Classical.choose_spec <| exists_rightMonochromatic_trans c s).1

theorem refineAt_rightMonochromatic (c : (Fin (k + 1) ↪o ℕ) → κ) (s : Fin k ↪o ℕ) :
    RightMonochromatic (fun x ↦ c (x.trans (refineAt c s))) s :=
  (Classical.choose_spec <| exists_rightMonochromatic_trans c s).2

/-- The sequence of increasingly sparse subsequences whose limit will give the proof of
  Ramsey's theorem. Each subsequence is obtained from the previous one by cleaning up
  a set in the sequence `ss`. -/
noncomputable def refs (c : (Fin (k + 1) ↪o ℕ) → κ) (ss : ℕ → (Fin k ↪o ℕ)) (n : ℕ) : ℕ ↪o ℕ :=
  match n with
  | 0    => refineAt c (ss 0)
  | n+1  => let g := refs c ss n
        (refineAt (fun x ↦ c (x.trans g)) (ss (n+1))).trans g

@[simp] theorem refs_succ (c : (Fin (k + 1) ↪o ℕ) → κ) (ss : ℕ → (Fin k ↪o ℕ)) (n : ℕ) :
    refs c ss (n+1) =
      (refineAt (fun x ↦ c (x.trans (refs c ss n))) (ss (n+1))).trans (refs c ss n) := rfl

theorem refs_stable (c : (Fin (k + 2) ↪o ℕ) → κ) (ss : ℕ → (Fin (k + 1) ↪o ℕ))
    (hss : Monotone (ss · ⊤)) {i j x : ℕ} (hij : i ≤ j) (hxi : x ≤ ss i ⊤) :
    refs c ss i x = refs c ss j x := by
  induction' j, hij using Nat.le_induction with n hin ih
  · rfl
  rw [ih, refs_succ, RelEmbedding.coe_trans, comp_apply, EmbeddingLike.apply_eq_iff_eq,
    (refineAt_stable _ _).apply_of_le _ (hxi.trans (hss (hin.trans (Nat.le_add_right _ 1))))]

theorem refs_monochromatic (c : (Fin (k + 2) ↪o ℕ) → κ) {ss : ℕ → (Fin (k + 1) ↪o ℕ)}
    (hss : Monotone (ss · ⊤)) (hij : i ≤ j) :
    RightMonochromatic (fun x ↦ c (RelEmbedding.trans x (refs c ss j))) (ss i) := by
  induction' j, hij using Nat.le_induction with n hin ih
  · induction' i using Nat.recAux with i
    · exact refineAt_rightMonochromatic c (ss 0)
    simp [refs]
    exact refineAt_rightMonochromatic (fun x ↦ c (RelEmbedding.trans x (refs c ss i))) _
  simp only [refs]
  set c' := (fun x ↦ c (RelEmbedding.trans x (refs c ss n )))
  have h := (refineAt_stable c' (ss (n+1))).mono (hss <| hin.trans (Nat.le_add_right _ _))
  exact (ih.trans_right h).trans_left

theorem exists_ub_fn (ss : ℕ ↪ (Fin (k + 1) ↪o ℕ)) :
    ∃ b : ℕ →o ℕ, ∀ ⦃n j⦄, b n ≤ j → n < ss j ⊤ := by
  have aux : ∀ m, {s : Fin (k + 1) ↪o ℕ | s ⊤ ≤ m}.Finite := by
    refine fun m ↦ Set.Finite.of_finite_image (f := fun x ↦ range x) ?_
      fun _ _ _ _ ↦ by rw [OrderEmbedding.range_inj]; exact id
    refine (finite_Iic m).finite_subsets.subset ?_
    rintro _ ⟨s, (hs : s ⊤ ≤ m), rfl⟩ _ ⟨i, rfl⟩
    exact (s.monotone le_top).trans hs
  choose t' ht' using fun m ↦ ((aux m).preimage ss.injective.injOn).bddAbove
  simp only [preimage_setOf_eq, mem_upperBounds, mem_setOf_eq] at ht'

  refine ⟨⟨fun i ↦ (Finset.range (i+1)).sup t' +1 , fun m n h ↦ ?_⟩, ?_⟩
  · exact add_le_add_right (Finset.sup_mono (Finset.range_mono (add_le_add_right h _))) _
  simp only [OrderHom.coe_mk, Nat.add_one_le_iff]
  refine fun n j h ↦ ?_
  by_contra! h'
  exact (ht' _ _ h').not_gt <| (Finset.le_sup (show n ∈ Finset.range (n+1) by simp)).trans_lt h

/-- Choose a function `t` so that for all `i ≥ t n`, the set `ss i` has maximum above `n`. -/
noncomputable def ub_fn (ss : ℕ ↪ (Fin (k + 1) ↪o ℕ)) : ℕ →o ℕ :=
    Classical.choose <| exists_ub_fn ss

/-- The subsequence to which the `refs c ss` converge pointwise. -/
noncomputable def lim (c : (Fin (k + 2) ↪o ℕ) → κ) {ss : ℕ ↪ (Fin (k + 1) ↪o ℕ)}
    (hss : Monotone (ss · ⊤)) : ℕ ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun n ↦ refs c ss (ub_fn ss n) n)
  (fun i j hij ↦ by
    simp only [refs_stable c ss hss ((ub_fn ss).mono hij.le)
      ((Classical.choose_spec <| exists_ub_fn ss) rfl.le).le]
    apply OrderEmbedding.strictMono _ hij )

theorem refs_eq_lim (c : (Fin (k + 2) ↪o ℕ) → κ) {ss : ℕ ↪ (Fin (k + 1) ↪o ℕ)}
    (hss : Monotone (ss · ⊤)) (hi : ub_fn ss n ≤ i) : refs c ss i n = lim c hss n :=
  Eq.symm <| refs_stable c ss hss hi (((Classical.choose_spec <| exists_ub_fn ss) rfl.le).le)

theorem lim_rightMonochromatic (c : (Fin (k + 2) ↪o ℕ) → κ) (ss : ℕ ↪ (Fin (k + 1) ↪o ℕ))
    (hss : Monotone (ss · ⊤)) (n : ℕ) :
    RightMonochromatic (fun x ↦ c (RelEmbedding.trans x (lim c hss))) (ss n) := by
  rw [rightMonochromatic_iff_forall']
  intro y x hyx hy'
  have hy := fun i ↦ ((hy' i).trans hyx)
  have hmc := refs_monochromatic c hss (j := max n (ub_fn ss x)) (le_max_left _ _)
  rw [rightMonochromatic_iff_forall'] at hmc
  specialize hmc hyx hy'
  simp only [appendRight_trans] at *
  simp_rw [refs_eq_lim c hss (le_max_right _ _)] at hmc
  convert hmc using 2
  · refine RelEmbedding.ext (Fin.lastCases ?_ fun i ↦ ?_)
    · simp only [appendRight_last]
      rw [refs_eq_lim]
      exact le_max_of_le_right ((ub_fn ss).monotone hyx.le)
    simp only [appendRight_castSucc, RelEmbedding.coe_trans, comp_apply]
    rw [refs_eq_lim]
    exact le_max_of_le_right ((ub_fn ss).monotone (hy i).le)
  refine RelEmbedding.ext (Fin.lastCases (by simp) fun i ↦ ?_)
  simp only [appendRight_castSucc, RelEmbedding.coe_trans, comp_apply]
  rw [refs_eq_lim c hss]
  exact le_max_of_le_right ((ub_fn ss).monotone (hy i).le)

section statements

variable {κ : Sort*} [Finite κ]

/-- Ramsey's theorem for infinite hypergraphs :
  for every colouring `c` of the `k`-subsets of `ℕ` with a finite set of colours,
  there is a subsequence of `ℕ` on which the sets all have the same colour. -/
theorem exists_monochromatic_subsequence_tuple (c : (Fin k ↪o ℕ) → κ) :
    ∃ (c₀ : κ) (g : ℕ ↪o ℕ), ∀ (s : Fin k ↪o ℕ), c (s.trans g) = c₀ := by
  suffices h : ∀ (c : (Fin k ↪o ℕ) → PLift κ),
      ∃ (c₀ : PLift κ) (g : ℕ ↪o ℕ), ∀ (s : Fin k ↪o ℕ), c (s.trans g) = c₀ by
    obtain ⟨⟨c₀⟩, g, h'⟩ := h (fun s ↦ ⟨c s⟩); exact ⟨c₀, g, by simpa using h'⟩
  clear c
  intro c
  induction' k using Nat.recAux with k ih
  · exact ⟨c <| Fin.valOrderEmb 0, RelEmbedding.refl _,
      fun s ↦ congr_arg _ <| RelEmbedding.ext finZeroElim⟩

  have hg₁ : ∃ (g₁ : ℕ ↪o ℕ), ∀ s, RightMonochromatic (fun x ↦ c <| RelEmbedding.trans x g₁) s := by
    induction' k using Nat.recAux with k
    · refine ⟨refineAt c default, fun s ↦ ?_⟩
      rw [Subsingleton.elim s default]
      exact refineAt_rightMonochromatic c default
    have aux : ∃ (e : ℕ ≃ ((Fin (k + 1)) ↪o ℕ)), Monotone (e · ⊤) := exists_enum_set_card k
    obtain ⟨e, he⟩ := aux
    exact ⟨lim c he, fun s ↦ by simpa using lim_rightMonochromatic c e he (e.symm s)⟩

  obtain ⟨g₁, hg₁⟩ := hg₁
  choose c' hc' using hg₁

  obtain ⟨c₀, g₀, hg₀⟩ := ih (c := c')
  refine ⟨c₀, g₀.trans g₁, fun s ↦ ?_⟩

  specialize hc' ((eraseRight s).trans g₀) (g₀ (s (Fin.last _))) (by simp [Fin.castSucc_lt_last])
  rwa [← appendRight_trans, appendRight_eraseRight, hg₀] at hc'

/-- A version of Ramsey's theorem where we are colouring each `s : Finset α` with `s.card = k`
  rather than the equivalent type `Fin k ↪o ℕ`. -/
theorem exists_monochromatic_subsequence_finset {k : ℕ} (c : (s : Finset ℕ) → s.card = k → κ) :
    ∃ (c₀ : κ) (g : ℕ ↪o ℕ), ∀ (s : Finset ℕ) hs, c (s.map g.toEmbedding) (by simpa) = c₀ := by
  set c' : (Fin k ↪o ℕ) → PLift κ := fun s' ↦ ⟨c (Finset.univ.map s'.toEmbedding) (by simp)⟩
  obtain ⟨⟨c₀⟩, g, h⟩ := exists_monochromatic_subsequence_tuple c'
  refine ⟨c₀, g, fun s hs ↦ ?_⟩
  simp only [PLift.up_inj, c'] at h
  convert h (s.orderEmbOfFin hs)
  rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_map]
  simp only [RelEmbedding.coe_toEmbedding, RelEmbedding.coe_trans, Finset.coe_univ, image_univ]
  rw [range_comp, Finset.range_orderEmbOfFin]

/-- A version of `Ramsey.exists_monochromatic_subsequence_finset` where we colour all finsets of
  size less than `k` with a colour from a finite type that can depend on the size.
  The conclusion is that we can find a subsequence on which the sets of each given size are all
  the same colour. -/
theorem exists_strong_monochromatic_subsequence_finset {κ : Fin k → Sort*} [∀ i, Finite (κ i)]
    (cs : (i : Fin k) → (s : Finset ℕ) → (hs : s.card = i) → κ i) :
    ∃ (c₀s : (i : Fin k) → κ i) (g : ℕ ↪o ℕ), ∀ (i : Fin k) (s : Finset ℕ) (hs : s.card = i),
      cs i (s.map g.toEmbedding) (by simpa) = c₀s i := by
  induction' k using Nat.recAux with k ih
  · exact ⟨finZeroElim, RelEmbedding.refl _, finZeroElim⟩
  set cs' : (i : Fin k) → (s : Finset ℕ) → s.card = i → κ (Fin.castSucc i) :=
    fun i s hs ↦ cs (Fin.castSucc i) s (by simpa)
  obtain ⟨c₀s', g', hg'⟩ := ih cs'
  obtain ⟨c₀, g, hg⟩ := exists_monochromatic_subsequence_finset
    (fun (s : Finset ℕ) (hs) ↦ cs (Fin.last k) (s.map g'.toEmbedding) (by simpa))
  refine ⟨Fin.lastCases c₀ c₀s', g.trans g', Fin.lastCases (fun s hs ↦ ?_) (fun i s hs ↦ ?_)⟩
  · specialize hg s (by simpa using hs)
    simp only [Fin.lastCases_last, Finset.map_eq_image, Finset.image_image] at hg ⊢
    exact hg
  simp only [Fin.lastCases_castSucc]
  specialize hg' i (s.map g.toEmbedding) (by simpa)
  simp only [Finset.map_eq_image, RelEmbedding.coe_toEmbedding, RelEmbedding.coe_trans] at hg' ⊢
  simp_rw [Finset.image_image] at hg'
  exact hg'

/-- A specialization of `Ramsey.strong_finset` where the colour type doesn't depend on size. -/
theorem exists_strong_monochromatic_subsequence_finset'
    (cs : (s : Finset ℕ) → (hs : s.card < k) → κ) : ∃ (c₀s : Fin k → κ) (g : ℕ ↪o ℕ),
    ∀ (s : Finset ℕ) (hs : s.card < k), cs (s.map g.toEmbedding) (by simpa) = c₀s ⟨s.card, hs⟩ := by
  set cs' : (i : Fin k) → (s : Finset ℕ) → (hs : s.card = i) → κ :=
    fun i s hs ↦ cs s (by rw [hs]; exact i.2)
  obtain ⟨c₀s, g, hg⟩ := exists_strong_monochromatic_subsequence_finset cs'
  exact ⟨c₀s, g, fun s hs ↦ hg ⟨s.card, hs⟩ s rfl⟩

/-- A version of Ramsey's theorem with no ordered types.
  Given a colouring of the `k`-sets in an infinite type `α` with finitely many colours,
  there is an infinite `s : Set α` whose `k`-subsets all have the same colour. -/
theorem exists_monochromatic_infinite_subset {α : Type*} [Infinite α]
    (c : (s : Finset α) → s.card = k → κ) : ∃ (a : Set α) (c₀ : κ), a.Infinite ∧ ∀ (s : Finset α)
    (hs : s.card = k), (s : Set α) ⊆ a → c s hs = c₀ := by
  classical
  set e := Infinite.natEmbedding α
  obtain ⟨c₀, g, h⟩ := exists_monochromatic_subsequence_finset (fun s hs ↦ c (s.map e) (by simpa))
  refine ⟨range (g.toEmbedding.trans e), c₀, ?_, fun s hs hsr ↦ ?_⟩
  · exact infinite_range_of_injective <| Function.Embedding.injective _
  rw [← image_univ, subset_image_iff] at hsr
  obtain ⟨s', -, hs'⟩ := hsr
  have hs'₁ : s'.Finite := by
    apply Set.Finite.of_finite_image (f := g.toEmbedding.trans e)
    · rw [hs']
      exact s.finite_toSet
    · refine Injective.injOn ?_
      apply Embedding.injective
  have hs'₂ : Finset.map e (Finset.map g.toEmbedding hs'₁.toFinset) = s := by
    apply Finset.coe_injective
    rw [← hs']
    simp [image_image]
  have hs'₃ := congr(Finset.card $hs'₂)
  have := h hs'₁.toFinset (by rw [← hs, ← hs'₃]; simp)
  rw [← this]
  congr
  exact hs'₂.symm

end statements

end Ramsey
