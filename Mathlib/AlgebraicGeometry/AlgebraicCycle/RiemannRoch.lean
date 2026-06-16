import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerChar

namespace Function.locallyFinsupp

open Function Function.locallyFinsuppWithin Set

variable {X : Type*} [TopologicalSpace X] {s : Set X}

open Classical in
/-- Adding an integer multiple of a point mass `single p 1` (with `p ∈ s`) to a function supported
in `s` keeps the support inside `s`. -/
lemma support_add_zsmul_single_subset {D : locallyFinsupp X ℤ} (h : D.support ⊆ s) {p : X}
    (hp : p ∈ s) (n : ℤ) : (D + n • single p 1).support ⊆ s := by
  intro x hx
  by_cases hxp : x = p
  · exact hxp ▸ hp
  · refine h ?_
    have hx' : (D + n • single p 1).toFun x ≠ 0 := hx
    simpa [Function.mem_support, single_apply, hxp] using hx'
open Classical in
/-- Adding a point mass `single p 1` (with `p ∈ s`) to a function supported in `s` keeps the support
inside `s`. -/
lemma support_add_single_subset {D : locallyFinsupp X ℤ} (h : D.support ⊆ s) {p : X}
    (hp : p ∈ s) : (D + single p 1).support ⊆ s := by
  simpa using support_add_zsmul_single_subset h hp 1

open Classical in
/-- Subtracting a point mass `single p 1` (with `p ∈ s`) from a function supported in `s` keeps the
support inside `s`. -/
lemma support_sub_single_subset {D : locallyFinsupp X ℤ} (h : D.support ⊆ s) {p : X}
    (hp : p ∈ s) : (D - single p 1).support ⊆ s := by
  simpa [sub_eq_add_neg, neg_one_smul] using support_add_zsmul_single_subset h hp (-1)

open Classical in
/--
**Induction principle for `ℤ`-valued functions with locally finite support contained in `s`.**

On a compact space, to prove a statement `motive D hD` about every such function `D` (together with
a proof `hD : D.support ⊆ s`), it suffices to prove it for the zero function and to show it is
preserved under adding and subtracting the point masses `single p 1` for `p ∈ s`. As in
`Nat.le_induction`, the motive carries the side condition `hD`, so each branch knows the function it
is handling is still supported in `s` (in particular the leftover `hD` goal does not survive); drive
a goal `motive D hD` with `induction D, hD using Function.locallyFinsupp.inductionOn`.

Note that this is genuinely a statement about `ℤ`-valued functions: the single steps only change a
coefficient by `±1`, so they generate exactly the integer combinations of point masses. -/
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
        · subst hxp; simp [hE'_def, single_apply]
        · simp [hE'_def, single_apply, hxp]
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
      have hEeq : E' + (E p) • single p 1 = E := by rw [hE'_def]; abel
      exact mcongr hEeq (addN E' hE' mE' p hps (E p))

open Classical in
/-- Sanity check that `inductionOn` drives the `induction … using` tactic. -/
example [CompactSpace X] (D : locallyFinsupp X ℤ) (hD : D.support ⊆ s)
    (P : ∀ D : locallyFinsupp X ℤ, D.support ⊆ s → Prop) (h0 : P 0 (by simp))
    (hadd : ∀ E hE p hp, P E hE → P (E + single p 1) (support_add_single_subset hE hp))
    (hsub : ∀ E hE p hp, P E hE → P (E - single p 1) (support_sub_single_subset hE hp)) :
    P D hD := by
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => exact h0
  | add E hE ih p hp => exact hadd E hE p hp ih
  | minus E hE ih p hp => exact hsub E hE p hp ih

end Function.locallyFinsupp

namespace AlgebraicCycle

open AlgebraicGeometry Order CategoryTheory Limits

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (D : AlgebraicCycle X ℤ)

noncomputable def degree : ℤ := ∑ᶠ (x : X), (D x) * (Module.finrank k (X.residueField x))

variable [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]
  (hD : D.support ⊆ {x | coheight x = 1})

/-
These assumptions are a very funny way of spelling that our scheme is proper over k. We can (and
probably should) weaken these assumptions to just be that O_X has these cohomological vanishing
properties.
-/
variable {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ) (_ : D.support ⊆ {x | coheight x = 1}),
        ∀ n, Module.Finite k (lesH (CommRingCat.of k) D.sheaf n))
    (hb₁ : ∀ (D : AlgebraicCycle X ℤ) (_ : D.support ⊆ {x | coheight x = 1}),
        ∀ n, N < n → IsZero (lesH (CommRingCat.of k) D.sheaf n))

/-
This is a funny way of spelling that X is a curve (i.e. it's a scheme where all codimension one
points are closed)
-/
variable (hX : ∀ x : X, coheight x = 1 → ∀ p, x ≤ p → x = p)

theorem riemann_roch (hD : D.support ⊆ {x | coheight x = 1}) : D.sheaf.eulerChar k =
    D.degree k + (0 : AlgebraicCycle X ℤ).sheaf.eulerChar k := by
  classical
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp => sorry
  | minus E hE ih p hp => sorry

end AlgebraicCycle
