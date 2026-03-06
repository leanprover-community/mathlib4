/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
public import Mathlib.Geometry.Manifold.VectorBundle.OrthonormalFrame

/-! # Christoffel symbols for a covariant derivative

Old code for defining the Christoffel symbols of a connection:
it's not clear how much this will be used,
and it would need to be thoroughly updated to compile, given the other modifications made

-/
set_option backward.isDefEq.respectTransparency false

namespace CovariantDerivative

open Bundle Filter Function Module NormedSpace Topology
open scoped ContDiff Manifold

variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {X X' X'' Y Y' Y'' Z Z' : Π x : M, TangentSpace I x}
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)] {x : M}

-- TODO: move this section to `Torsion.lean`
section

--omit [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
--omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

/-- The **Christoffel symbol** of a covariant derivative on a set `U ⊆ M`
with respect to a local frame `(s_i)` on `U`: for each triple `(i, j, k)` of indices,
this is a function `Γᵢⱼᵏ : M → ℝ`, whose value outside of `U` is meaningless. -/
noncomputable def ChristoffelSymbol
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    {U : Set M} {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) : M → ℝ :=
  (LinearMap.piApply (hs.coeff k)) (fun x ↦ f (s i) x (s j x))

-- special case of `foobar` below; needed?
lemma ChristoffelSymbol.sum_eq
    (f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    {U : Set M} {ι : Type*} [Fintype ι] {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j : ι) (hx : x ∈ U) :
    f (s i) x (s j x) = ∑ k, (ChristoffelSymbol I f hs i j k x) • (s k) x := by
  simp only [ChristoffelSymbol, LinearMap.piApply_apply]
  apply hs.coeff_sum_eq _ hx

variable {U : Set M}
  {f g : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {ι : Type*} {s : ι → (x : M) → TangentSpace I x}

-- Note that this result is false if `{s i}` is merely a local frame.
lemma eq_product_apply [Fintype ι]
    (hf : IsCovariantDerivativeOn E f U)
    (hs : IsOrthonormalFrameOn I E n s U)
    (i j k : ι) (hx : x ∈ U) :
    ChristoffelSymbol I f hs.toIsLocalFrameOn i j k x = inner ℝ (f (s i) x (s j x)) (s k x) := by
  -- Choose a linear order on ι: which one really does not matter for our result.
  have : LinearOrder ι := by
    choose r wo using exists_wellOrder _
    exact r
  have : LocallyFiniteOrderBot ι := by sorry
  sorry
  -- was: rw [ChristoffelSymbol, hs.coeff_eq_inner' (f (s i) (s j)) hx k, real_inner_comm]

#exit
-- TODO: the next lines have a number of errors, and would need to be updated

-- Lemma 4.3 in Lee, Chapter 5: first term still missing
lemma foobar [Fintype ι] [FiniteDimensional ℝ E] (hf : IsCovariantDerivativeOn E f U)
    (hs : IsLocalFrameOn I E 1 s U) {x : M} (hx : x ∈ U) :
    f X x (Y x) = ∑ k,
      letI S₁ := ∑ i, ∑ j,
        ((LinearMap.piApply (hs.coeff i)) X) * (LinearMap.piApply (hs.coeff j) Y)
          * (ChristoffelSymbol I f hs i j k)
      letI S₂ : M → ℝ := sorry -- first summand in Leibniz' rule!
      S₁ x • s k x := by
  have hY := hs.coeff_sum_eq Y hx
  -- should this be a separate lemma also?
  have : ∀ x ∈ U, Y x = ∑ i, hs.coeff i x (Y x) • s i x := by
    intro x hx
    apply hs.coeff_sum_eq Y hx
  have : f X x (Y x) = f X (fun x ↦ ∑ i, (hs.coeff i) Y x • s i x) x := by
    -- apply `congr_σ_of_eventuallyEq` from Basic.lean (after restoring it)
    -- want U to be a neighbourhood of x to make this work
    sorry
  rw [this]
  -- straightforward computation: use linearity and Leibniz rule
  sorry

/- TODO: prove some basic properties, such as
- the Christoffel symbols are linear in cov
- if (s_i) is a smooth local frame on U, then cov is smooth on U iff each Christoffel symbol is (?)
- prove a `spec` equality
- deduce: two covariant derivatives are equal iff their Christoffel symbols are equal
-/

lemma _root_.IsCovariantDerivativeOn.congr_of_christoffelSymbol_eq [Fintype ι]
    [FiniteDimensional ℝ E] -- TODO: this is implied by Finite ι, right?
    (hf : IsCovariantDerivativeOn E f U) (hg : IsCovariantDerivativeOn E g U)
    (hs : IsLocalFrameOn I E n s U)
    (hfg : ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I g hs i j k x) :
    ∀ X Y : Π x : M, TangentSpace I x, ∀ x ∈ U, f X x (Y x) = g X x (Y x) := by
  have (i j : ι) : ∀ x ∈ U, f (s i) (s j) x = g (s i) (s j) x := by
    intro x hx
    rw [hs.eq_iff_coeff hx]
    exact fun k ↦ hfg i j k x hx
  intro X Y x hx
  -- use linearity (=formula for f in terms of Christoffel symbols) now, another separate lemma!
  sorry

/-- Two covariant derivatives on `U` are equal on `U` if and only if all of their
covariant derivatives w.r.t. some local frame on `U` are equal on `U`. -/
lemma _root_.IsCovariantDerivativeOn.congr_iff_christoffelSymbol_eq [Fintype ι]
    [FiniteDimensional ℝ E] -- TODO: this is implied by Finite ι, right?
    (hf : IsCovariantDerivativeOn E f U) (hg : IsCovariantDerivativeOn E g U)
    (hs : IsLocalFrameOn I E n s U) :
    (∀ X Y : Π x : M, TangentSpace I x, ∀ x ∈ U, f X x (Y x) = g X x (Y x)) ↔
    ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I g hs i j k x :=
  ⟨fun hfg _i _j _k _x hx ↦ hs.coeff_congr (hfg _ _ _ hx ) ..,
    fun h X Y x hx ↦ hf.congr_of_christoffelSymbol_eq I hg hs h X Y x hx⟩

-- TODO: global version for convenience, with an alias for the interesting direction!

variable (hs : IsLocalFrameOn I E n s U)

lemma christoffelSymbol_zero (U : Set M) {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) : ChristoffelSymbol I 0 hs i j k = 0 := by
  simp [ChristoffelSymbol]

@[simp]
lemma christoffelSymbol_zero_apply (U : Set M) {ι : Type*} {s : ι → (x : M) → TangentSpace I x}
    (hs : IsLocalFrameOn I E n s U) (i j k : ι) (x) : ChristoffelSymbol I 0 hs i j k x = 0 := by
  simp [christoffelSymbol_zero]

end

-- Lemma 4.3 in Lee, Chapter 5: first term still missing
variable {U : Set M} {ι : Type*} [Fintype ι] {s : ι → (x : M) → TangentSpace I x}
  {f : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}

-- XXX: generalise this to any field
variable {I} in
/-- `∇` is torsion-free on `U` if its torsion vanishes at each `x ∈ U` -/
noncomputable def IsTorsionFreeOn
    (cov : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x))
    (U : Set M) : Prop :=
  ∀ x ∈ U, ∀ X Y : Π x : M, TangentSpace I x, IsCovariantDerivativeOn.torsionAux cov X Y x = 0
namespace IsTorsionFreeOn
section changing_set
/-! Changing set
In this changing we change `s` in `IsTorsionFreeOn F f s`.
-/
lemma mono {s t : Set M} (hf : IsTorsionFreeOn f t) (hst : s ⊆ t) :
  IsTorsionFreeOn f s :=
  fun _ hx _ _ ↦ hf _ (hst hx) ..

lemma iUnion {ι : Type*} {s : ι → Set M} (hf : ∀ i, IsTorsionFreeOn f (s i)) :
    IsTorsionFreeOn cov (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, hi⟩, hxsi⟩ X Y
  sorry -- was: exact hf i x (by simp [hi, hxsi]) X Y
end changing_set
end IsTorsionFreeOn

-- errors: omit [IsContMDiffRiemannianBundle I 1 E fun x ↦ TangentSpace I x] in
/-- Let `{s i}` be a local frame on `U` such that `[s i, s j] = 0` on `U` for all `i, j`.
A covariant derivative on `U` is torsion-free on `U` iff for each `x ∈ U`,
the Christoffel symbols `Γᵢⱼᵏ` w.r.t. `{s i}` are symmetric. -/
lemma isTorsionFreeOn_iff_christoffelSymbols [CompleteSpace E] {ι : Type*} [Fintype ι]
    [FiniteDimensional ℝ E] -- TODO: this is implied by Finite ι, right?
    (hf : IsCovariantDerivativeOn E f U)
    {s : ι → (x : M) → TangentSpace I x} (hs : IsLocalFrameOn I E n s U)
    (hs'' : ∀ i j, ∀ x : U, VectorField.mlieBracket I (s i) (s j) x = 0) :
    IsTorsionFreeOn f U ↔
      ∀ i j k, ∀ x ∈ U, ChristoffelSymbol I f hs i j k x = ChristoffelSymbol I f hs j i k x := by
  rw [hf.isTorsionFreeOn_iff_localFrame (n := n) hs]
  have (i j : ι) {x} (hx : x ∈ U) :
      torsion f (s i) (s j) x = f (s i) x (s j x) - f (s j) x (s i x) := by
    simp [torsion, hs'' i j ⟨x, hx⟩]
  peel with i j
  refine ⟨?_, ?_⟩
  · intro h k x hx
    simp only [ChristoffelSymbol]
    apply hs.coeff_congr
    specialize h x hx
    rw [this i j hx, sub_eq_zero] at h
    exact h
  · intro h x hx
    rw [this i j hx, sub_eq_zero, hs.eq_iff_coeff hx]
    exact fun k ↦ h k x hx

-- Exercise 4.2(b) in Lee, Chapter 4
/-- A covariant derivative on `U` is torsion-free on `U` iff for each `x ∈ U` and
any local coordinate frame, the Christoffel symbols `Γᵢⱼᵏ` are symmetric.

TODO: figure out the right quantifiers here!
right now, I just have one fixed coordinate frame... will this do??
-/
lemma isTorsionFree_iff_christoffelSymbols' [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    (hf : IsCovariantDerivativeOn E f U) :
    IsTorsionFreeOn f U ↔
      ∀ x ∈ U,
      -- Let `{s_i}` be the coordinate frame at `x`: this statement is false for arbitrary frames.
      -- TODO: does the following do what I want??
      letI cs := ChristoffelSymbol I f
          (trivializationAt E _ x).isLocalFrameOn_localFrame_baseSet I 1 ((Basis.ofVectorSpace ℝ E))
      ∀ i j k, cs i j k x = cs j i k x := by
  letI t := (trivializationAt E (fun (x : M) ↦ TangentSpace I x))
  have hs (x) :=
    ((Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 (t x))

  -- TODO: check that the Lie bracket of any two coordinate vector fields is zero!
  rw [isTorsionFreeOn_iff_christoffelSymbols (ι := (↑(Basis.ofVectorSpaceIndex ℝ E))) I hf]
  -- issues with quantifier order in the statement... prove both directions separately, at each x?
  repeat sorry

theorem LeviCivitaConnection.christoffelSymbol_symm [FiniteDimensional ℝ E] (x : M) :
    letI t := trivializationAt E (TangentSpace I) x;
    letI hs := t.isLocalFrameOn_localFrame_baseSet I 1 (Basis.ofVectorSpace ℝ E)
    ∀ x', x' ∈ t.baseSet → ∀ (i j k : ↑(Basis.ofVectorSpaceIndex ℝ E)),
      ChristoffelSymbol I (LeviCivitaConnection I M) hs i j k x' =
        ChristoffelSymbol I (LeviCivitaConnection I M) hs j i k x' := by
  by_cases hE : Subsingleton E
  · have (y : M) (X : TangentSpace I y) : X = 0 := by
      have : Subsingleton (TangentSpace I y) := inferInstanceAs (Subsingleton E)
      apply Subsingleton.eq_zero X
    have (X : Π y : M, TangentSpace I y) : X = 0 := sorry
    intro x'' hx'' i j k
    simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
    unfold lcCandidate
    simp only [lcAux, hE, ↓reduceDIte]

    letI t := trivializationAt E (TangentSpace I) x;
    letI hs := (Basis.ofVectorSpace ℝ E).localFrame_isLocalFrameOn_baseSet I 1 t
    have : ChristoffelSymbol I 0 hs i j k = 0 := christoffelSymbol_zero I t.baseSet hs i j k
    -- now, use a congruence result and the first `have`
    sorry
  -- Note that hs is not necessarily an orthonormal frame, so we cannot simply rewrite
  -- the Christoffel symbols as Γᵢⱼᵏ = ⟪∇ᵍ X Y, Z⟫`: however, the result we wants to prove boils
  -- down to proving the same.
  intro x' hx' i j
  set t := trivializationAt E (TangentSpace I) x
  set b := (Basis.ofVectorSpace ℝ E)
  set s := t.localFrame b
  set ι := ↑(Basis.ofVectorSpaceIndex ℝ E)
  -- Same computation as above; extract as lemma!
  let O : (x : M) → TangentSpace I x := fun x ↦ 0
  have need : ∀ i j, VectorField.mlieBracket I (s i) (s j) x' = O x' := sorry
  have aux : ∀ k, ⟪LeviCivitaConnection I M (s i) (s j), (s k)⟫ x'
      = ⟪LeviCivitaConnection I M (s j) (s i), (s k)⟫ x' := by
    intro k
    simp only [LeviCivitaConnection, LeviCivitaConnection_aux]
    unfold lcCandidate
    rw [product_apply, product_apply]
    simp only [lcAux, hE, ↓reduceDIte]
    -- Choose a linear order on ι: which one really does not matter for our result.
    have : LinearOrder ι := by
      choose r wo using exists_wellOrder _
      exact r
    have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have : Nonempty ι := b.index_nonempty
    -- The linear ordering on the indexing set of `b` is only used in this proof,
    -- so our choice does not matter.
    have : LinearOrder ι := by
      choose r wo using exists_wellOrder _
      exact r
    have : Fintype ι := sorry
    -- why does this fail? are there two different orders in play?
    have : LocallyFiniteOrderBot ι := sorry
    have : ∑ k', inner ℝ
      (leviCivitaRhs I (s i) (s j)
          (b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k') x' •
          b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x')
      (s k x') =
       ∑ k', inner ℝ
        (leviCivitaRhs I (s j) (s i)
          (b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k') x' •
          b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x')
        (s k x') := by
      congr with k'
      simp only [leviCivitaRhs]
      set sij := b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k' x'
      rw [inner_smul_left, inner_smul_left]
      congr
      simp [leviCivitaRhs']
      set S := b.orthonormalFrame (trivializationAt E (TangentSpace I) x') k'
      have need' : ∀ i, VectorField.mlieBracket I (s i) S x' = O x' := by
        -- expand the definition of Gram-Schmidt and use need and linearity
        sorry
      have need'' : ∀ i, VectorField.mlieBracket I S (s i) x' = O x' := by
        sorry -- swap and use need', or so
      rw [product_congr_right I (need i j), product_congr_right I (need j i),
        product_congr_right I (need' i), product_congr_right I (need'' i),
        product_congr_right I (need' j), product_congr_right I (need'' j),
        rhs_aux_swap I (s i) (s j), rhs_aux_swap I (s j) S, rhs_aux_swap I S (s i)]
      simp [O]
      abel
    -- now, just rewrite `inner` to take out a sum: same lemma twice
    convert this
    · sorry
    · sorry

  -- deduce the goal from `aux`
  sorry

end CovariantDerivative
