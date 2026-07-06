module

public import Mathlib.Topology.LocallyFinsupp
public import Mathlib.Data.Set.Card

/-!
# Induction on divisors

In this file we develop a sketch of an induction principal for working on divisors (it is sorry
free but in a very messy state). This is more or less `Finsupp.induction`, but instead of proving
goals of the form `p(D) -> p(D + single n P)`, we prove `p(D) -> p(D + single 1 P)` (and ditto for
`-`). This is more convenient for induction with divisors, because adding a single point to a
divisor gives a nice short exact sequence, and adding higher multiples gives something less
convenient. I am convinced something like this is needed, but I am unclear on whether this is the
precise form we want.

TODO: Refactor this in terms of Finsupp.induction
-/

@[expose] public section

namespace Function.locallyFinsupp

open Function Function.locallyFinsuppWithin Set

variable {X : Type*} [TopologicalSpace X] {s : Set X}

open Classical in
/-- Adding an integer multiple of a point `single p 1` (with `p ∈ s`) to a function supported
in `s` keeps the support inside `s`.

Note : I don't think n • single p 1 is a sensible way to spell single p n, we should certainly
write this in the other form and add in a simp lemma
-/
lemma support_add_zsmul_single_subset {D : locallyFinsupp X ℤ} (h : D.support ⊆ s) {p : X}
    (hp : p ∈ s) (n : ℤ) : (D + n • single p 1).support ⊆ s := by
  intro x hx
  by_cases hxp : x = p
  · exact hxp ▸ hp
  · exact h (by simpa [Function.mem_support, single_apply, hxp] using hx)

open Classical in
/-- Adding a point `single p 1` (with `p ∈ s`) to a cycle supported in `s` keeps the support
inside `s`. -/
lemma support_add_single_subset {D : locallyFinsupp X ℤ} (h : D.support ⊆ s) {p : X}
    (hp : p ∈ s) : (D + single p 1).support ⊆ s := by
  simpa using support_add_zsmul_single_subset h hp 1

open Classical in
/-- Subtracting a point `single p 1` (with `p ∈ s`) from a cycle supported in `s` keeps the
support inside `s`. -/
lemma support_sub_single_subset {D : locallyFinsupp X ℤ} (h : D.support ⊆ s) {p : X}
    (hp : p ∈ s) : (D - single p 1).support ⊆ s := by
  simpa [sub_eq_add_neg, neg_one_smul] using support_add_zsmul_single_subset h hp (-1)

open Classical in
/--
Induction principal for `ℤ` valued algebraic cycles on compact spaces whose supports lie in some set
`s`. One of the main applications of this is to allow for induction arguments on Weil divisors,
where the set `s` is the set of codimension one points.

Note: I can't currently think of a good generalization beyond the case of the integers, but I
imagine one might exist.

TODO: Clean up this silly proof
-/
@[elab_as_elim]
theorem inductionOn [CompactSpace X]
    {motive : (D : locallyFinsupp X ℤ) → D.support ⊆ s → Prop}
    (zero : motive 0 (by simp))
    (add : ∀ (E : locallyFinsupp X ℤ) (hE : E.support ⊆ s), motive E hE →
      ∀ (p : X) (hp : p ∈ s), motive (E + single p 1) (support_add_single_subset hE hp))
    (minus : ∀ (E : locallyFinsupp X ℤ) (hE : E.support ⊆ s), motive E hE →
      ∀ (p : X) (hp : p ∈ s), motive (E - single p 1) (support_sub_single_subset hE hp))
    (D : locallyFinsupp X ℤ) (hD : D.support ⊆ s) : motive D hD := by
  -- Transport `motive` along an equality of the underlying functions; the side-condition argument
  -- is irrelevant, so it carries over automatically.
  have mcongr : ∀ {A B : locallyFinsupp X ℤ} (_ : A = B) {hA : A.support ⊆ s}
      {hB : B.support ⊆ s}, motive A hA → motive B hB := by
    rintro A B rfl hA hB m; exact m
  -- From `motive E hE` we can reach `motive (E + n • single q 1) _` for any integer `n`, by
  -- iterating `add`/`minus`.
  have addN : ∀ (E : locallyFinsupp X ℤ) (hE : E.support ⊆ s), motive E hE →
      ∀ (q : X) (hq : q ∈ s) (n : ℤ),
        motive (E + n • single q 1) (support_add_zsmul_single_subset hE hq n) := by
    intro E hE mE q hq n
    induction n using Int.induction_on with
    | zero => exact mcongr (by simp) mE
    | succ i ih =>
        refine mcongr ?_ (add (E + (i : ℤ) • single q 1)
          (support_add_zsmul_single_subset hE hq i) ih q hq)
        rw [add_smul, one_smul, add_assoc]
    | pred i ih =>
        refine mcongr ?_ (minus (E + (-(i : ℤ)) • single q 1)
          (support_add_zsmul_single_subset hE hq _) ih q hq)
        rw [sub_smul, one_smul, add_sub_assoc]
  -- Now induct on the (finite) cardinality of the support.
  suffices H : ∀ (n : ℕ) (E : locallyFinsupp X ℤ) (hE : E.support ⊆ s),
      E.support.ncard = n → motive E hE by exact H _ D hD rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hE hcard
    by_cases hsupp : E.support = ∅
    · -- empty support: `E = 0`.
      have hE0 : E = 0 :=
        DFunLike.coe_injective ((Function.support_eq_empty_iff.mp hsupp).trans coe_zero.symm)
      exact mcongr hE0.symm zero
    · -- nonempty support: clear the coefficient at some point `p`.
      obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hsupp
      have hps : p ∈ s := hE hp
      set E' := E - (E p) • single p 1 with hE'_def
      have hE'_apply : ∀ x, E' x = if x = p then 0 else E x := by
        intro x
        by_cases hxp : x = p
        · subst hxp; simp [hE'_def]
        · simp [hE'_def, hxp]
      have hsub : E'.support ⊆ E.support := by
        intro x hx
        have hx' : E' x ≠ 0 := hx
        by_cases hxp : x = p
        · simp [hE'_apply, hxp] at hx'
        · rw [Function.mem_support]
          rwa [hE'_apply, if_neg hxp] at hx'
      have hpnotin : p ∉ E'.support := by simp [Function.mem_support, hE'_apply]
      have hssub : E'.support ⊂ E.support := hsub.ssubset_of_ne (fun he => hpnotin (he ▸ hp))
      have hE' : E'.support ⊆ s := hsub.trans hE
      have hfinE : E.support.Finite := by
        have := E.locallyFiniteSupport.finite_inter_support_of_isCompact (isCompact_univ (X := X))
        simpa using this
      have hsmaller : E'.support.ncard < n := hcard ▸ Set.ncard_lt_ncard hssub hfinE
      have mE' : motive E' hE' := ih _ hsmaller E' hE' rfl
      have hEeq : E' + (E p) • single p 1 = E := by grind
      exact mcongr hEeq (addN E' hE' mE' p hps (E p))

end Function.locallyFinsupp
