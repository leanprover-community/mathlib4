/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yaël Dillies
-/
import Mathlib.Order.PartialSups
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Nat.SuccPred

/-!
# Making a sequence disjoint

This file defines the way to make a sequence of sets - or, more generally, a map from a partially
ordered set `β` into a (generalized) Boolean algebra `α` - into a *pairwise disjoint* sequence with
the same partial sups.

For a sequence `f : ℕ → α`, this new sequence will be `f 0`, `f 1 \ f 0`, `f 2 \ (f 0 ⊔ f 1) ⋯`.
It is actually unique, as `disjointed_unique` shows.

## Main declarations

* `disjointed f`: The map sending `n` to `f n \ (⨆ m < n, f m)`. We require the domain to be a
  `LocallyFiniteOrderBot` to ensure that the supremum is well defined.
* `partialSups_disjointed`: `disjointed f` has the same partial sups as `f`.
* `disjoint_disjointed`: The elements of `disjointed f` are pairwise disjoint.
* `disjointed_unique`: `disjointed f` is the only pairwise disjoint sequence having the same partial
  sups as `f`.
* `Fintype.sup_disjointed` (for finite `β`) or `iSup_disjointed` (for complete `α`):
  `disjointed f` has the same supremum as `f`. Limiting case of `partialSups_disjointed`.
* `Fintype.exists_disjointed_le`: for any finite family `f : ι → α`, there exists a pairwise
  disjoint family `g : ι → α` which is bounded above by `f` and has the same supremum. This is
  an analogue of `disjointed` for arbitrary finite index types (but without any uniqueness).

We also provide set notation variants of some lemmas.

## TODO

Find a useful statement of `disjointedRec_succ`.
-/

open Finset Order

variable {α β : Type*}

section GeneralizedBooleanAlgebra -- the *target* is a GBA

variable [GeneralizedBooleanAlgebra α]

section Preorder -- the *source* is a preorder

variable [Preorder β] [LocallyFiniteOrderBot β]

/-- The function mapping `n` to `f n \ (⨆ m < n, f m)`. When `β` is a partial order, this is the
unique function `g` having the same `partialSups` as `f` and such that `g m` and `g n` are
disjoint whenever `m < n`.  -/
def disjointed (f : β → α) (n : β) : α := f n \ (Iio n).sup f

lemma disjointed_apply (f : β → α) (n : β) : disjointed f n = f n \ (Iio n).sup f := rfl

lemma disjointed_of_isMin (f : β → α) {n : β} (hn : IsMin n) :
    disjointed f n = f n := by
  have : Iio n = ∅ := by rwa [← Finset.coe_eq_empty, coe_Iio, Set.Iio_eq_empty_iff]
  simp only [disjointed_apply, this, sup_empty, sdiff_bot]

@[simp] lemma disjointed_bot [OrderBot β] (f : β → α) : disjointed f ⊥ = f ⊥ :=
  disjointed_of_isMin _ isMin_bot

theorem disjointed_le_id : disjointed ≤ (id : (β → α) → β → α) :=
  fun _ _ ↦ sdiff_le

theorem disjointed_le (f : β → α) : disjointed f ≤ f :=
  disjointed_le_id f

theorem disjoint_disjointed_of_lt (f : β → α) {m n : β} (h : m < n) :
    Disjoint (disjointed f m) (disjointed f n) :=
  (disjoint_sdiff_self_right.mono_left <| le_sup (mem_Iio.mpr h)).mono_left (disjointed_le f m)

lemma disjointed_eq_self {f : β → α} {n : β} (hf : ∀ m < n, Disjoint (f m) (f n)) :
    disjointed f n = f n := by
  rw [disjointed_apply, sdiff_eq_left, disjoint_iff, sup_inf_distrib_left,
    sup_congr rfl <| fun m hm ↦ disjoint_iff.mp <| (hf _ (mem_Iio.mp hm)).symm]
  exact sup_bot _

/- NB: The original statement for `β = ℕ` was a `def` and worked for `p : α → Sort*`. I couldn't
prove the `Sort*` version for general `β`, but all instances of `disjointedRec` in the library are
for Prop anyway. -/
/--
An induction principle for `disjointed`. To prove something about `disjointed f n`, it's
enough to prove it for `f n` and being able to extend through diffs.
-/
lemma disjointedRec {f : β → α} {p : α → Prop} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
    ∀ ⦃n⦄, p (f n) → p (disjointed f n) := by
  classical
  intro n hpn
  rw [disjointed]
  suffices ∀ (s : Finset β), p (f n \ s.sup f) from this _
  intro s
  induction s using Finset.induction with
  | empty => simpa only [sup_empty, sdiff_bot] using hpn
  | insert ht IH => rw [sup_insert, sup_comm, ← sdiff_sdiff]; exact hdiff IH

end Preorder

section PartialOrder

variable [PartialOrder β] [LocallyFiniteOrderBot β]

@[simp]
theorem partialSups_disjointed (f : β → α) :
    partialSups (disjointed f) = partialSups f := by
  -- This seems to be much more awkward than the case of linear orders, because the supremum
  -- in the definition of `disjointed` can involve multiple "paths" through the poset.
  classical
  -- We argue by induction on the size of `Iio n`.
  suffices ∀ r n (hn : #(Iio n) ≤ r), partialSups (disjointed f) n = partialSups f n from
    OrderHom.ext _ _ (funext fun n ↦ this _ n le_rfl)
  intro r n hn
  induction r generalizing n with
  | zero =>
   -- Base case: `n` is minimal, so `partialSups f n = partialSups (disjointed f) n = f n`.
    simp only [Nat.le_zero, card_eq_zero] at hn
    simp only [partialSups_apply, Iic_eq_cons_Iio, hn, disjointed_apply, sup'_eq_sup, sup_cons,
      sup_empty, sdiff_bot]
  | succ n ih =>
    -- Induction step: first WLOG arrange that `#(Iio n) = r + 1`
    rcases lt_or_eq_of_le hn with hn | hn
    · exact ih _ <| Nat.le_of_lt_succ hn
    simp only [partialSups_apply (disjointed f), Iic_eq_cons_Iio, sup'_eq_sup, sup_cons]
    -- Key claim: we can write `Iio n` as a union of (finitely many) `Ici` intervals.
    have hun : (Iio n).biUnion Iic = Iio n := by
      ext r; simpa using ⟨fun ⟨a, ha⟩ ↦ ha.2.trans_lt ha.1, fun hr ↦ ⟨r, hr, le_rfl⟩⟩
    -- Use claim and `sup_biUnion` to rewrite the supremum in the definition of `disjointed f`
    -- in terms of suprema over `Iic`'s. Then the RHS is a `sup` over `partialSups`, which we
    -- can rewrite via the induction hypothesis.
    rw [← hun, sup_biUnion, sup_congr rfl (g := partialSups f)]
    · simp only [funext (partialSups_apply f), sup'_eq_sup, ← sup_biUnion, hun]
      simp only [disjointed, sdiff_sup_self, Iic_eq_cons_Iio, sup_cons]
    · simp only [partialSups, sup'_eq_sup, OrderHom.coe_mk] at ih ⊢
      refine fun x hx ↦ ih x ?_
      -- Remains to show `∀ x in Iio n, #(Iio x) ≤ r`.
      rw [← Nat.lt_add_one_iff, ← hn]
      apply lt_of_lt_of_le (b := #(Iic x))
      · simpa only [Iic_eq_cons_Iio, card_cons] using Nat.lt_succ_self _
      · refine card_le_card (fun r hr ↦ ?_)
        simp only [mem_Iic, mem_Iio] at hx hr ⊢
        exact hr.trans_lt hx

lemma Fintype.sup_disjointed [Fintype β] (f : β → α) :
    univ.sup (disjointed f) = univ.sup f := by
  classical
  have hun : univ.biUnion Iic = (univ : Finset β) := by
    ext r; simpa only [mem_biUnion, mem_univ, mem_Iic, true_and, iff_true] using ⟨r, le_rfl⟩
  rw [← hun, sup_biUnion, sup_biUnion, sup_congr rfl (fun a _ ↦ ?_)]
  rw [← sup'_eq_sup nonempty_Iic, ← sup'_eq_sup nonempty_Iic,
    ← partialSups_apply, ← partialSups_apply, partialSups_disjointed]

lemma disjointed_partialSups (f : β → α) :
    disjointed (partialSups f) = disjointed f := by
  classical
  ext n
  have step1 : f n \ (Iio n).sup f = partialSups f n \ (Iio n).sup f := by
    rw [sdiff_eq_symm (sdiff_le.trans (le_partialSups f n))]
    simp only [funext (partialSups_apply f), sup'_eq_sup]
    rw [sdiff_sdiff_eq_sdiff_sup (sup_mono Iio_subset_Iic_self), sup_eq_right]
    simp only [Iic_eq_cons_Iio, sup_cons, sup_sdiff_left_self, sdiff_le_iff, le_sup_right]
  simp only [disjointed_apply, step1, funext (partialSups_apply f), sup'_eq_sup, ← sup_biUnion]
  congr 2 with r
  simpa only [mem_biUnion, mem_Iio, mem_Iic] using
    ⟨fun ⟨a, ha⟩ ↦ ha.2.trans_lt ha.1, fun hr ↦ ⟨r, hr, le_rfl⟩⟩

/-- `disjointed f` is the unique map `d : β → α` such that `d` has the same partial sups as `f`,
and `d i` and `d j` are disjoint whenever `i < j`. -/
theorem disjointed_unique {f d : β → α} (hdisj : ∀ {i j : β} (_ : i < j), Disjoint (d i) (d j))
    (hsups : partialSups d = partialSups f) :
    d = disjointed f := by
  rw [← disjointed_partialSups, ← hsups, disjointed_partialSups]
  exact funext fun n ↦ (disjointed_eq_self (fun m hm ↦ hdisj hm)).symm

end PartialOrder

section LinearOrder

/-!
### Linear orders
-/

variable [LinearOrder β] [LocallyFiniteOrderBot β]

theorem disjoint_disjointed (f : β → α) : Pairwise (Disjoint on disjointed f) :=
  (pairwise_disjoint_on _).mpr fun _ _ ↦ disjoint_disjointed_of_lt f

/-- `disjointed f` is the unique sequence that is pairwise disjoint and has the same partial sups
as `f`. -/
theorem disjointed_unique' {f d : β → α} (hdisj : Pairwise (Disjoint on d))
    (hsups : partialSups d = partialSups f) : d = disjointed f :=
  disjointed_unique (fun hij ↦ hdisj hij.ne) hsups

section SuccOrder

variable [SuccOrder β]

lemma disjointed_succ (f : β → α) {n : β} (hn : ¬IsMax n) :
    disjointed f (succ n) = f (succ n) \ partialSups f n := by
  rw [disjointed_apply, partialSups_apply, sup'_eq_sup]
  congr 2 with m
  simpa only [mem_Iio, mem_Iic] using lt_succ_iff_of_not_isMax hn

protected lemma Monotone.disjointed_succ {f : β → α} (hf : Monotone f) {n : β} (hn : ¬IsMax n) :
    disjointed f (succ n) = f (succ n) \ f n := by
  rwa [disjointed_succ, hf.partialSups_eq]

/-- Note this lemma does not require `¬IsMax n`, unlike `disjointed_succ`. -/
lemma Monotone.disjointed_succ_sup {f : β → α} (hf : Monotone f) (n : β) :
    disjointed f (succ n) ⊔ f n = f (succ n) := by
  by_cases h : IsMax n
  · simpa only [succ_eq_iff_isMax.mpr h, sup_eq_right] using disjointed_le f n
  · rw [disjointed_apply]
    have : Iio (succ n) = Iic n := by
      ext; simp only [mem_Iio, lt_succ_iff_eq_or_lt_of_not_isMax h, mem_Iic, le_iff_lt_or_eq,
        Or.comm]
    rw [this, ← sup'_eq_sup, ← partialSups_apply, hf.partialSups_eq,
      sdiff_sup_cancel (hf (le_succ n))]

end SuccOrder

section SuccAddOrder

variable [Add β] [One β] [SuccAddOrder β]

theorem disjointed_add_one [NoMaxOrder β] (f : β → α) (n : β) :
    disjointed f (n + 1) = f (n + 1) \ partialSups f n := by
  simpa only [succ_eq_add_one] using disjointed_succ f (not_isMax n)

protected lemma Monotone.disjointed_add_one_sup {f : β → α} (hf : Monotone f) (n : β) :
    disjointed f (n + 1) ⊔ f n = f (n + 1) := by
  simpa only [succ_eq_add_one n] using hf.disjointed_succ_sup n

protected lemma Monotone.disjointed_add_one [NoMaxOrder β]  {f : β → α} (hf : Monotone f) (n : β) :
    disjointed f (n + 1) = f (n + 1) \ f n := by
  rw [← succ_eq_add_one, hf.disjointed_succ]
  exact not_isMax n

end SuccAddOrder

end LinearOrder

/-!
### Functions on an arbitrary fintype
-/

/-- For any finite family of elements `f : ι → α`, we can find a pairwise-disjoint family `g`
bounded above by `f` and having the same supremum. This is non-canonical, depending on an arbitrary
choice of ordering of `ι`. -/
lemma Fintype.exists_disjointed_le {ι : Type*} [Fintype ι] {f : ι → α} :
    ∃ g, g ≤ f ∧ univ.sup g = univ.sup f ∧ Pairwise (Disjoint on g) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  ·  -- do `ι = ∅` separately since `⊤ : Fin n` isn't defined for `n = 0`
    exact ⟨f, le_rfl, rfl, Subsingleton.pairwise⟩
  let R : ι ≃ Fin _ := equivFin ι
  let f' : Fin _ → α := f ∘ R.symm
  have hf' : f = f' ∘ R := by ext; simp only [Function.comp_apply, Equiv.symm_apply_apply, f']
  refine ⟨disjointed f' ∘ R, ?_, ?_, ?_⟩
  · intro n
    simpa only [hf'] using disjointed_le f' (R n)
  · simpa only [← sup_image, image_univ_equiv, hf'] using sup_disjointed f'
  · exact fun i j hij ↦ disjoint_disjointed f' (R.injective.ne hij)

end GeneralizedBooleanAlgebra

section CompleteBooleanAlgebra

/-! ### Complete Boolean algebras -/

variable [CompleteBooleanAlgebra α]

theorem iSup_disjointed [PartialOrder β] [LocallyFiniteOrderBot β] (f : β → α) :
    ⨆ n, disjointed f n = ⨆ n, f n :=
  iSup_eq_iSup_of_partialSups_eq_partialSups (partialSups_disjointed f)

theorem disjointed_eq_inf_compl [Preorder β] [LocallyFiniteOrderBot β] (f : β → α) (n : β) :
    disjointed f n = f n ⊓ ⨅ i < n, (f i)ᶜ := by
  simp only [disjointed_apply, Finset.sup_eq_iSup, mem_Iio, sdiff_eq, compl_iSup]

end CompleteBooleanAlgebra

section Set

/-! ### Lemmas specific to set-valued functions -/

theorem disjointed_subset [Preorder β] [LocallyFiniteOrderBot β] (f : β → Set α) (n : β) :
    disjointed f n ⊆ f n :=
  disjointed_le f n

theorem iUnion_disjointed [PartialOrder β] [LocallyFiniteOrderBot β] {f : β → Set α} :
    ⋃ n, disjointed f n = ⋃ n, f n :=
  iSup_disjointed f

theorem disjointed_eq_inter_compl [Preorder β] [LocallyFiniteOrderBot β] (f : β → Set α) (n : β) :
    disjointed f n = f n ∩ ⋂ i < n, (f i)ᶜ :=
  disjointed_eq_inf_compl f n

theorem preimage_find_eq_disjointed (s : ℕ → Set α) (H : ∀ x, ∃ n, x ∈ s n)
    [∀ x n, Decidable (x ∈ s n)] (n : ℕ) : (fun x => Nat.find (H x)) ⁻¹' {n} = disjointed s n := by
  ext x
  simp [Nat.find_eq_iff, disjointed_eq_inter_compl]

end Set

section Nat

/-! ### Functions on `ℕ` -/

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α]

@[simp]
theorem disjointed_zero (f : ℕ → α) : disjointed f 0 = f 0 :=
  disjointed_bot f

-- Porting note: `disjointedRec` had a change in universe level.
/-- A recursion principle for `disjointed`. To construct / define something for `disjointed f n`,
it's enough to construct / define it for `f n` and to able to extend through diffs.

Note that this version allows an arbitrary `Sort*`, but requires the domain to be `Nat`, while
the root-level `disjointedRec` allows more general domains but requires `p` to be `Prop`-valued. -/
def Nat.disjointedRec {f : ℕ → α} {p : α → Sort*} (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) :
    ∀ ⦃n⦄, p (f n) → p (disjointed f n)
  | 0 => fun h₀ ↦ disjointed_zero f ▸ h₀
  | n + 1 => fun h => by
    suffices H : ∀ k, p (f (n + 1) \ partialSups f k) from disjointed_add_one f n ▸ H n
    intro k
    induction k with
    | zero => exact hdiff h
    | succ k ih => simpa only [partialSups_add_one, ← sdiff_sdiff_left] using hdiff ih

@[simp]
theorem disjointedRec_zero {f : ℕ → α} {p : α → Sort*}
    (hdiff : ∀ ⦃t i⦄, p t → p (t \ f i)) (h₀ : p (f 0)) :
    Nat.disjointedRec hdiff h₀ = (disjointed_zero f ▸ h₀) :=
  rfl

-- TODO: Find a useful statement of `disjointedRec_succ`.

end GeneralizedBooleanAlgebra

end Nat
