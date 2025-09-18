/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Binomial

/-!
# Vertex operators
In this file we introduce heterogeneous vertex operators using Hahn series.  When `R = ℂ`, `V = W`,
and `Γ = ℤ`, then this is the usual notion of "meromorphic left-moving 2D field".  The notion we use
here allows us to consider composites and scalar-multiply by multivariable Laurent series.
## Definitions
* `HVertexOperator` : An `R`-linear map from an `R`-module `V` to `HahnModule Γ W`.
* The coefficient function as an `R`-linear map.
* Composition of heterogeneous vertex operators - values are Hahn series on lex order product.
## Main results
* Ext
## TODO
* curry for tensor product inputs
* more API to make ext comparisons easier.
* formal variable API, e.g., like the `T` function for Laurent polynomials.
## References

* [R. Borcherds, *Vertex Algebras, Kac-Moody Algebras, and the Monster*][borcherds1986vertex]

-/

noncomputable section

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- A heterogeneous `Γ`-vertex operator over a commutator ring `R` is an `R`-linear map from an
`R`-module `V` to `Γ`-Hahn series with coefficients in an `R`-module `W`. -/
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)

namespace HVertexOperator

section Coeff

open HahnModule

@[ext]
theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

/-- The coefficients of a heterogeneous vertex operator, viewed as a linear map to formal power
series with coefficients in linear maps. -/
@[simps]
def coeff : HVertexOperator Γ R V W →ₗ[R] Γ → V →ₗ[R] W where
  toFun A n := {
    toFun v := ((of R).symm (A v)).coeff n
    map_add' u v := by simp
    map_smul' r v := by simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'

@[ext]
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W →ₗ[R] Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v

/-- Given a coefficient function valued in linear maps satisfying a partially well-ordered support
condition, we produce a heterogeneous vertex operator. -/
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W) (hf : ∀ x : V , (Function.support (f · x)).IsPWO) :
    HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[deprecated (since := "2025-08-30")] alias coeff_add := map_add
@[deprecated (since := "2025-08-30")] alias coeff_smul := map_smul

@[simp]
theorem coeff_of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀ (x : V), (Function.support (fun g => f g x)).IsPWO) : (of_coeff f hf).coeff = f :=
  rfl

@[simp]
theorem of_coeff_coeff (A : HVertexOperator Γ R V W) : of_coeff A.coeff A.coeff_isPWOsupport = A :=
  rfl

end Coeff

section Products

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

open HahnModule

theorem lexComp_support_isPWO (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)
    (u : U) :
    (fun x ↦ (fun (g : Γ' ×ₗ Γ) ↦
      A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1) x u).support.IsPWO := by
  refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
  · refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [Set.image_subset_iff, Function.support_subset_iff, Set.mem_preimage,
      Function.mem_support, Lex.forall, ofLex_toLex, Prod.forall]
    intro _ _ h
    contrapose! h
    simp [h]
  · intro g₁
    simp only [Function.mem_support, ofLex_toLex]
    exact HahnSeries.isPWO_support _

/-- The bilinear composition of two heterogeneous vertex operators, yielding a heterogeneous vertex
operator on the Lex product. Note that the exponent group of the left factor ends up on the right
side of the Lex product. -/
def lexComp : HVertexOperator Γ R V W →ₗ[R] HVertexOperator Γ' R U V →ₗ[R]
    HVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun A := {
    toFun B :=
      of_coeff (fun g ↦ (coeff A (ofLex g).2) ∘ₗ (coeff B (ofLex g).1))
        (fun u ↦ lexComp_support_isPWO A B u)
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem lexComp_apply_apply_coeff (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)
    (g : Γ' ×ₗ Γ) :
    (lexComp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

@[simp]
theorem lexComp_apply_apply_apply_coeff (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)
    (u : U) (g : Γ' ×ₗ Γ) :
    ((HahnModule.of R).symm (lexComp A B u)).coeff g =
      A.coeff (ofLex g).2 (B.coeff (ofLex g).1 u) := by
  rfl

theorem coeff_left_lex_supp.isPWO (A : HVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') (v : V) :
    (Function.support (fun (g : Γ) => (coeff A (toLex (g, g'))) v)).IsPWO := by
  refine Set.IsPWO.mono (Set.PartiallyWellOrderedOn.imageProdLex (A v).isPWO_support') ?_
  simp only [Function.support_subset_iff, ne_eq, Set.mem_image, Function.mem_support]
  exact fun x h ↦ Exists.intro (toLex (x, g')) ⟨h, rfl⟩

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the left
factor, as a linear map. -/
def ResLeft (g' : Γ') : HVertexOperator (Γ' ×ₗ Γ) R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := HVertexOperator.of_coeff (fun g => coeff A (toLex (g', g)))
    (fun v => Set.PartiallyWellOrderedOn.fiberProdLex (A v).isPWO_support' _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coeff_ResLeft (A : HVertexOperator (Γ' ×ₗ Γ) R V W) (g' : Γ') (g : Γ) :
    coeff (ResLeft g' A) g = coeff A (toLex (g', g)) :=
  rfl

/-- The restriction of a heterogeneous vertex operator on a lex product to an element of the right
factor, as a linear map. -/
def ResRight (g' : Γ') :
    HVertexOperator (Γ ×ₗ Γ') R V W →ₗ[R] HVertexOperator Γ R V W where
  toFun A := HVertexOperator.of_coeff (fun g => coeff A (toLex (g, g')))
    (fun v => coeff_left_lex_supp.isPWO A g' v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coeff_ResRight (A : HVertexOperator (Γ ×ₗ Γ') R V W) (g' : Γ') (g : Γ) :
    coeff (ResRight g' A) g = coeff A (toLex (g, g')) := rfl

end Products

section binomialPow

variable {S Γ₁ : Type*} [PartialOrder Γ₁] [CommRing S] [AddCommGroup Γ] [IsOrderedAddMonoid Γ]
[Module S Γ] [AddAction Γ Γ₁] [IsOrderedCancelVAdd Γ Γ₁]

theorem exists_binomialPow_smul_support_bound {g g' : Γ} (g₁ : Γ₁) (h : g < g') (n : S)
    (A : HVertexOperator Γ₁ R V W) (v : V) :
    ∃ (k : ℕ), ∀ (m : ℕ) (_ : k < m),
      (-(n • g) - m • (g' - g)) +ᵥ g₁ ∉ ((HahnModule.of R).symm (A v)).support :=
  Set.PartiallyWellOrderedOn.exists_notMem_of_gt ((HahnModule.of R).symm (A v)).isPWO_support
    fun _ _ hkl ↦ not_le_of_gt <| VAdd.vadd_lt_vadd_of_lt_of_le
      (sub_lt_sub_left (nsmul_lt_nsmul_left (sub_pos.mpr h) hkl) (-(n • g))) <| Preorder.le_refl g₁

variable {Γ : Type*} [LinearOrder Γ] [AddCommGroup Γ] [IsOrderedAddMonoid Γ] [AddAction Γ Γ₁]
[IsOrderedCancelVAdd Γ Γ₁] [BinomialRing S] [Module S W] [Algebra S R] [IsScalarTower S R W]
[Module S Γ]

theorem binomialPow_smul_coeff {g g' : Γ} (g₁ : Γ₁) (h : g < g') (n : S)
    (A : HVertexOperator Γ₁ R V W) (v : V) :
    ((HahnModule.of R).symm (HahnSeries.binomialPow (A := R) g g' (-1 : R) n • A v)).coeff g₁ =
      ∑ᶠ m : ℕ, Int.negOnePow m • Ring.choose n m •
        ((HahnModule.of R).symm (A v)).coeff ((- (n • g) - (m • (g' - g))) +ᵥ g₁) := by
  let f : ℕ → Γ × Γ₁ := fun k ↦  ((n • g) + k • (g' - g), (- (n • g) - (k • (g' - g))) +ᵥ g₁)
  let s := Finset.range <| (exists_binomialPow_smul_support_bound g₁ h n A v).choose + 1
  rw [HahnModule.coeff_smul, finsum_eq_sum_of_support_subset (s := s)]
  · classical
    refine Eq.trans (b := ∑ ij ∈ (Finset.image f s),
      (HahnSeries.binomialPow R g g' (-1) n).coeff ij.1 •
        ((HahnModule.of R).symm (A v)).coeff ij.2) ?_ ?_
    · refine Finset.sum_of_injOn (fun k ↦ k) (Function.Injective.injOn fun ⦃x y⦄ a ↦ a) ?_ ?_ ?_
      · rw [Set.mapsTo_iff_image_subset, Set.image_id', Finset.coe_subset]
        intro ij hij
        obtain ⟨h₁, h₂, h₃⟩ := (Finset.mem_vaddAntidiagonal _ _ _).mp hij
        rw [HahnSeries.mem_support] at h₁
        have hij1 : ∃ k : ℕ, (n • g + k • (g' - g)) = ij.1 := by
          contrapose! h₁
          exact HahnSeries.binomialPow_coeff_eq_zero R h (-1) n h₁
        obtain ⟨k, hk⟩ := hij1
        have hij2 : ij.2 = (-(n • g) - k • (g' - g)) +ᵥ g₁ := by
          rw [← h₃, vadd_vadd, ← hk, sub_add_add_cancel, neg_add_cancel, zero_vadd]
        have : k ∈ s := by
          contrapose! h₂
          rw [Finset.mem_range_succ_iff, not_le] at h₂
          rw [hij2]
          exact (exists_binomialPow_smul_support_bound g₁ h n A v).choose_spec k h₂
        exact Finset.mem_image.mpr (Exists.intro k ⟨this, by simp [f, hk, ← hij2]⟩)
      · intro ij hij hn
        simp only [Set.image_id', Finset.mem_coe, Finset.mem_vaddAntidiagonal, not_and] at hn
        have : ij.1 +ᵥ ij.2 = g₁ := by
          obtain ⟨k, hk₁, hk₂⟩ := Finset.mem_image.mp hij
          simp only [f, Prod.eq_iff_fst_eq_snd_eq] at hk₂
          rw [← hk₂.1, ← hk₂.2, vadd_vadd, add_add_sub_cancel, add_neg_cancel, zero_vadd]
        by_cases h1 : (HahnSeries.binomialPow R g g' (-1) n).coeff ij.1 = 0
        · rw [h1, zero_smul]
        · specialize hn h1
          by_cases h2 : ((HahnModule.of R).symm (A v)).coeff ij.2 = 0
          · rw [h2, smul_zero]
          · exact ((hn h2) this).elim
      · intro ij hij
        simp
    · refine (Finset.sum_of_injOn
      (fun k ↦ ((n • g) + k • (g' - g), (- (n • g) - (k • (g' - g))) +ᵥ g₁))
      (fun k hk l hl hkl ↦ ?_) ?_ ?_ ?_).symm
      · simp only [Prod.mk.injEq, add_right_inj] at hkl
        obtain ⟨hkl1, hkl2⟩ := hkl
        contrapose! hkl1
        obtain hk | eq | hk := lt_trichotomy k l
        · exact ne_of_lt <| nsmul_lt_nsmul_left (sub_pos.mpr h) hk
        · exact (hkl1 eq).elim
        · exact Ne.symm <| ne_of_lt <| nsmul_lt_nsmul_left (sub_pos.mpr h) hk
      · intro k hk
        exact Finset.mem_coe.mpr <| Finset.mem_image_of_mem f hk
      · intro k hk hkn
        rw [Finset.mem_image] at hk
        rw [Set.mem_image] at hkn
        exact (hkn hk).elim
      · intro k hks
        simp only
        rw [HahnSeries.binomialPow_coeff_eq R h (-1) n k, smul_assoc, smul_assoc, one_smul]
        norm_cast
  · refine Function.support_subset_iff'.mpr ?_
    intro k hk
    rw [Finset.mem_coe, Finset.mem_range, Nat.not_lt_eq, Order.add_one_le_iff] at hk
    have := (exists_binomialPow_smul_support_bound g₁ h n A v).choose_spec k hk
    rw [HahnSeries.mem_support, Mathlib.Tactic.PushNeg.not_ne_eq] at this
    rw [this, smul_zero, smul_zero]

omit [Module S W] [IsScalarTower S R W] in
theorem binomialPow_smul_injective {g g' : Γ} (n : S) :
    Function.Injective (HahnSeries.binomialPow (A := R) g g' (-1) n • · :
      HVertexOperator Γ₁ R V W → HVertexOperator Γ₁ R V W) := by
  refine Function.HasLeftInverse.injective ?_
  use (HahnSeries.binomialPow (A := R) g g' (-1) (-n) • ·)
  intro A
  simp only [smul_smul, HahnSeries.binomialPow_add, neg_add_cancel]
  rw [HahnSeries.binomialPow_zero, HahnSeries.single_zero_one, one_smul]

end binomialPow

section Products

open HahnModule

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

/-- The composite of two heterogeneous vertex operators acting on a vector, as an iterated Hahn
series. -/
@[simps]
def compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp only [coeff_apply_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    exact hg' (by simp [hAB])

@[simp]
theorem compHahnSeries_add (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply_apply, HahnSeries.coeff_add', Pi.add_apply]
  rw [← HahnSeries.coeff_add]

@[simp]
theorem compHahnSeries_smul (r : R) (u : U) :
    compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  simp only [compHahnSeries_coeff, map_smul, coeff_apply_apply, HahnSeries.coeff_smul]
  rw [← HahnSeries.coeff_smul]

/-- The composite of two heterogeneous vertex operators, as a heterogeneous vertex operator. -/
@[simps]
def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp [HahnSeries.ofIterate]
  map_smul' := by
    intro r x
    ext g
    simp [HahnSeries.ofIterate]

@[simp]
theorem coeff_comp (g : Γ' ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl
end Products

end HVertexOperator
