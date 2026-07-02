import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerChar
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ExactSequence
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerChar

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
  · refine h ?_
    have hx' : (D + n • single p 1).toFun x ≠ 0 := hx
    simpa [Function.mem_support, single_apply, hxp] using hx'
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

variable {X : Scheme.{u}} (k : Type u) [Field k]
    (D : AlgebraicCycle X ℤ) [X.Over (Spec (CommRingCat.of k))]

noncomputable def degree : ℤ := ∑ᶠ (x : X), (D x) * (Module.finrank k (X.residueField x))

@[simp]
lemma degree_sum (D D' : AlgebraicCycle X ℤ) [CompactSpace X]
    : degree k (D + D') = degree k D + degree k D' := by
  simp [degree]
  ring_nf
  rw [finsum_add_distrib]
  · have :=
      LocallyFiniteSupport.finite_inter_support_of_isCompact D.locallyFiniteSupport
      CompactSpace.isCompact_univ
    simp only [Function.locallyFinsuppWithin.toFun_eq_coe, Set.univ_inter,
      Function.HasFiniteSupport, Function.support_mul] at this ⊢
    exact Set.Finite.inter_of_left this _
  · have :=
      LocallyFiniteSupport.finite_inter_support_of_isCompact D'.locallyFiniteSupport
      CompactSpace.isCompact_univ
    simp only [Function.locallyFinsuppWithin.toFun_eq_coe, Set.univ_inter,
      Function.HasFiniteSupport, Function.support_mul] at this ⊢
    exact Set.Finite.inter_of_left this _

@[simp]
lemma degree_neg (D : AlgebraicCycle X ℤ)
    : degree k (-D) = - degree k D := by simp [degree, finsum_neg_distrib]

@[simp]
lemma degree_minus (D D' : AlgebraicCycle X ℤ) [CompactSpace X]
    : degree k (D - D') = degree k D - degree k D' := by
  have := degree_sum k D (-D')
  simp [-degree_sum] at this
  ring_nf at this
  rw [← this]
  congr

open Function.locallyFinsuppWithin Classical in
@[simp]
lemma degree_single (p : X) {n : ℤ} : degree k (single p n) =
    n * (Module.finrank k (X.residueField p)):= by
  simp only [degree]
  rw [finsum_eq_finsetSum_of_support_subset (s := {p})]
  · simp
  · simp

variable [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]
  (hD : D.support ⊆ {x | coheight x = 1})

/-
These assumptions are a very funny way of spelling that our scheme is proper over k. We can (and
probably should) weaken these assumptions to just be that O_X has these cohomological vanishing
properties.

Note: We do not place any assumptions on the algebraic cycle D. The reason is that Oₓ(D) only
depends on the codimension one part (more or less).

I.e. if D is not effective outside of codimension one, then the sheaf has no sections anywhere.
Otherwise, it is isomorphic to Oₓ(D') for D' the codimension one part of D.

Note: these should probably be typeclasses, and presumably we should just have this hf₁ be ∃ N, ...

Another note: Joel is going to put in some stuff on Cech cohomology, so we should put this stuff
in a form that is a bit more sensible.

Namely, I think it's much more sensible to work with finiteness of H^0 as opposed to directly
using the LES like this.

It's also probably better to only have these hypotheses for O_X, though right now we do not have
what's required to show that O_X is O_X(0) on a normal scheme. I'm not sure if these assumptions
will ever be useful being directly applied to O_X(0).

We can of course sorry away some things - i.e. we should always have a map from O_X to O_X(0) and
we can just sorry that this thing is an isomorphism in the cases we care about
-/
variable {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, Module.Finite k (D.sheaf.H k n))
    (hb₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, N < n → Subsingleton (D.sheaf.H k n))

/-
This is a funny way of spelling that X is a curve (i.e. it's a scheme where all codimension one
points are closed)
-/
--variable (hX : ∀ x : X, coheight x = 1 → ∀ p, x ≤ p → x = p)

/--
`X` has Krull dimension at most `n` if and only if every point of coheight at least `n` is minimal
in the specialization order. Geometrically, this says that the codimension-`n` points are closed.
-/
lemma krullDimLE_iff_coheight_le_implies_eq {X : Type*} [PartialOrder X] {n : ℕ} :
    Order.KrullDimLE n X ↔ (∀ x : X, n ≤ coheight x → ∀ y, y ≤ x → y = x) := by
  rw [Order.krullDimLE_iff]
  constructor
  · -- If `krullDim X ≤ n` and `coheight x ≥ n`, then `x` is minimal: a strict predecessor `y < x`
    -- would extend any chain above `x`, giving `coheight y ≥ coheight x + 1 ≥ n + 1` and hence
    -- `krullDim X ≥ n + 1`, contradicting `krullDim X ≤ n`.
    intro h x hx y hy
    by_contra hne
    -- The specialization order on a scheme is a `Preorder`; it is antisymmetric since schemes are
    -- `T0`, so `y ≤ x` with `y ≠ x` upgrades to `y < x`.
    have hlt : y < x := by
      refine lt_of_le_not_ge hy fun hxy => hne ?_
      --rw [Scheme.le_iff_specializes] at hy hxy
      exact (hy.antisymm hxy)--.eq.symm
    have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ coheight y := by
      have hstep : (n : ℕ∞) + 1 ≤ coheight x + 1 := by gcongr
      rw [Nat.cast_add, Nat.cast_one]
      exact hstep.trans (coheight_add_one_le hlt)
    have h3 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
      le_trans (le_trans (by exact_mod_cast h2) (coheight_le_krullDim y)) h
    have : n + 1 ≤ n := by exact_mod_cast h3
    omega
  · -- Conversely, if `krullDim X > n`, take a chain of length `n + 1`. Its second point `l 1` has a
    -- chain of length `n` above it, so `coheight (l 1) ≥ n`, yet its predecessor `l 0` lies strictly
    -- below it, so `l 1` is not minimal — contradicting the hypothesis.
    intro h
    by_contra hcon
    rw [not_le] at hcon
    have hn1 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ krullDim X := by
      rw [Nat.cast_add, Nat.cast_one]
      exact ENat.WithBot.add_one_le_iff.mpr hcon
    obtain ⟨l, hl⟩ := le_krullDim_iff.mp hn1
    have hidx : 1 < l.length + 1 := by omega
    have hcoh : (n : ℕ∞) ≤ coheight (l ⟨1, hidx⟩) := by
      have hrev := rev_index_le_coheight l ⟨1, hidx⟩
      have hval : ((⟨1, hidx⟩ : Fin (l.length + 1)).rev : ℕ) = n := by
        simp only [Fin.val_rev]; omega
      calc (n : ℕ∞) = (((⟨1, hidx⟩ : Fin (l.length + 1)).rev : ℕ) : ℕ∞) := by rw [hval]
        _ ≤ coheight (l ⟨1, hidx⟩) := by exact_mod_cast hrev
    have h0lt : l ⟨0, by omega⟩ < l ⟨1, hidx⟩ := l.strictMono (by simp [Fin.lt_def])
    exact absurd (h _ hcoh _ h0lt.le) (ne_of_lt h0lt)

/--
Dual form of `krullDimLE_iff_coheight_le_implies_eq`: `X` has Krull dimension at most `n` if and only
if every point of height at least `n` is maximal. Obtained by running the previous lemma on the
order dual `Xᵒᵈ`, where height/coheight and minimal/maximal swap roles.
-/
lemma krullDimLE_iff_height_le_implies_eq {X : Type*} [PartialOrder X] {n : ℕ} :
    Order.KrullDimLE n X ↔ (∀ x : X, n ≤ height x → ∀ y, x ≤ y → y = x) := by
  have : Order.KrullDimLE n X ↔ Order.KrullDimLE n Xᵒᵈ := by
        rw [Order.krullDimLE_iff, Order.krullDimLE_iff, krullDim_orderDual]
  rw [this]
  exact krullDimLE_iff_coheight_le_implies_eq

open AlgebraicCycle.Sheaf Function.locallyFinsuppWithin in
theorem riemann_roch {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, Module.Finite k (lesH (CommRingCat.of k) D.sheaf n))
    (hb₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, N < n → IsZero (lesH (CommRingCat.of k) D.sheaf n))
    (hD : D.support ⊆ {x | coheight x = 1})
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x) : D.sheaf.eulerChar k =
    D.degree k + (0 : AlgebraicCycle X ℤ).sheaf.eulerChar k := by
  classical
  have sfin : ∀ p : X, ∀ n, Module.Finite k (lesH (CommRingCat.of k)
      (skyscraperSheafOfModules p (X.ringCatSheaf) (X.residueField p)) n) := by
    sorry
  have svan : ∀ p : X, ∀ n, 0 < n → IsZero (lesH (CommRingCat.of k)
      (skyscraperSheafOfModules p (X.ringCatSheaf) (X.residueField p)) n) := by
    have := skyscraper_h (X := X) k
    intro p n h
    specialize this p h


    sorry
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp =>
    have : Scheme.Modules.eulerChar k (sheaf (E + Function.locallyFinsuppWithin.single p 1))
      = Scheme.Modules.eulerChar k (sheaf E) + (Module.finrank k (X.residueField p)) := by
      have : IsDiscreteValuationRing (X.presheaf.stalk p) :=
        IsRegularInCodimensionOne.stalk_dvr p hp
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
      have : (E + single p 1) - E = single p 1 := by simp
      let o := twistedClosedSubschemeComplex₂ p hE ϖ hϖ hp this
      have o_exact : o.ShortExact := twistedClosedSubschemeComplex₂_shortExact _ _ _ _ _ _ (hX p hp)
      have : o.X₂.eulerChar k = o.X₁.eulerChar k + o.X₃.eulerChar k := by
        apply eulerChar_additive k o o_exact
        · exact hf₁ E
        · exact hf₁ (E + single p 1)
        · exact sfin p
        · exact hb₁ E
        · exact hb₁ (E + single p 1)
        · -- exact svan p
          sorry
      convert this
      rw [← eulerChar_skyscraper k p]
      /-
      Probably bad?

      TODO: Think of a way of making this rfl automatic.
      -/
      rfl
    simp [this, ih]
    ring
  | minus E hE ih p hp =>
    have : Scheme.Modules.eulerChar k (sheaf (E - Function.locallyFinsuppWithin.single p 1))
      = Scheme.Modules.eulerChar k (sheaf E) -
        (Module.finrank k (X.residueField p)) := by
      have : IsDiscreteValuationRing (X.presheaf.stalk p) :=
        IsRegularInCodimensionOne.stalk_dvr p hp
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
      let o := twistedClosedSubschemeComplex₁ p hE ϖ hϖ hp
        (by simp : E - (E - single p 1) = single p 1)
      have o_exact : o.ShortExact := twistedClosedSubschemeComplex₁_shortExact _ _ _ _ _ _ (hX p hp)
      have : o.X₂.eulerChar k = o.X₁.eulerChar k + o.X₃.eulerChar k := by
        apply eulerChar_additive k o o_exact
        · exact hf₁ (E - single p 1)
        · exact hf₁ E
        · /-
          Here we should give some argument using skyscraper_h
          -/
          sorry
        · exact hb₁ (E - single p 1)
        · exact hb₁ E
        · sorry
      have : o.X₁.eulerChar k = o.X₂.eulerChar k - o.X₃.eulerChar k := by lia
      convert this
      rw [← eulerChar_skyscraper k p]
      rfl
    simp [this, ih]
    ring

end AlgebraicCycle
