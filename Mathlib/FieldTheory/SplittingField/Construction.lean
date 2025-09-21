/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `Polynomial.SplittingField f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `Polynomial.IsSplittingField.algEquiv`: Every splitting field of a polynomial `f` is isomorphic
  to `SplittingField f` and thus, being a splitting field is unique up to isomorphism.

## Implementation details
We construct a `SplittingFieldAux` without worrying about whether the instances satisfy nice
definitional equalities. Then the actual `SplittingField` is defined to be a quotient of a
`MvPolynomial` ring by the kernel of the obvious map into `SplittingFieldAux`. Because the
actual `SplittingField` will be a quotient of a `MvPolynomial`, it has nice instances on it.

-/

noncomputable section

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

open Classical in
/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : K[X]) : K[X] :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else X

theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
  · exact irreducible_X

/-- See note [fact non-instances]. -/
theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩

attribute [local instance] fact_irreducible_factor

theorem factor_dvd_of_not_isUnit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f := by
  by_cases hf2 : f = 0; · rw [hf2]; exact dvd_zero _
  rw [factor, dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_not_isUnit (mt degree_eq_zero_of_isUnit hf)

theorem factor_dvd_of_natDegree_ne_zero {f : K[X]} (hf : f.natDegree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt natDegree_eq_of_degree_eq_some hf)

lemma isCoprime_iff_aeval_ne_zero (f g : K[X]) : IsCoprime f g ↔ ∀ {A : Type v} [CommRing A]
    [IsDomain A] [Algebra K A] (a : A), aeval a f ≠ 0 ∨ aeval a g ≠ 0 := by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hx _ => ?_⟩
  · replace h := @h K _ _ _ 0
    contrapose! h
    rw [h.left, h.right, map_zero, and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
    replace h := not_and_or.mpr <| h <| AdjoinRoot.root x.factor
    simp only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero,
      dvd_mul_of_dvd_left <| factor_dvd_of_not_isUnit hx, true_and, not_true] at h

/-- Divide a polynomial f by `X - C r` where `r` is a root of `f` in a bigger field extension. -/
def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))

theorem X_sub_C_mul_removeFactor (f : K[X]) (hf : f.natDegree ≠ 0) :
    (X - C (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f := by
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  apply (mul_divByMonic_eq_iff_isRoot
    (R := AdjoinRoot f.factor) (a := AdjoinRoot.root f.factor)).mpr
  rw [IsRoot.def, eval_map, hg, eval₂_mul, ← hg, AdjoinRoot.eval₂_root, zero_mul]

theorem natDegree_removeFactor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
  rw [removeFactor, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_map, natDegree_X_sub_C]

theorem natDegree_removeFactor' {f : K[X]} {n : ℕ} (hfn : f.natDegree = n + 1) :
    f.removeFactor.natDegree = n := by rw [natDegree_removeFactor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

It constructs the type, proves that is a field and algebra over the base field.

Uses recursion on the degree.
-/
def SplittingFieldAuxAux (n : ℕ) : ∀ {K : Type u} [Field K], K[X] →
    Σ (L : Type u) (_ : Field L), Algebra K L :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : ℕ) => ∀ {K : Type u} [_inst_4 : Field K], K[X] →
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors. It is the type constructed in `SplittingFieldAuxAux`.
-/
def SplittingFieldAux (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (SplittingFieldAuxAux n f).1

instance SplittingFieldAux.field (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Field (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.1

instance (n : ℕ) {K : Type u} [Field K] (f : K[X]) : Inhabited (SplittingFieldAux n f) :=
  ⟨0⟩

instance SplittingFieldAux.algebra (n : ℕ) {K : Type u} [Field K] (f : K[X]) :
    Algebra K (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.2

namespace SplittingFieldAux

theorem succ (n : ℕ) (f : K[X]) :
    SplittingFieldAux (n + 1) f = SplittingFieldAux n f.removeFactor :=
  rfl

instance algebra''' {n : ℕ} {f : K[X]} :
    Algebra (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n _

instance algebra' {n : ℕ} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFieldAux n.succ f) :=
  SplittingFieldAux.algebra'''

instance algebra'' {n : ℕ} {f : K[X]} : Algebra K (SplittingFieldAux n f.removeFactor) :=
  RingHom.toAlgebra (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor))

instance scalar_tower' {n : ℕ} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_succ (n : ℕ) (f : K[X]) :
    algebraMap K (SplittingFieldAux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor)).comp
        (AdjoinRoot.of f.factor) :=
  rfl

protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n), Splits (algebraMap K <| SplittingFieldAux n f) f :=
  Nat.recOn (motive := fun n => ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n), Splits (algebraMap K <| SplittingFieldAux n f) f) n
    (fun {_} _ _ hf =>
      splits_of_degree_le_one _
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih {K} _ f hf => by
    rw [← splits_id_iff_splits, algebraMap_succ, ← map_map, splits_id_iff_splits,
      ← X_sub_C_mul_removeFactor f fun h => by rw [h] at hf; cases hf]
    exact splits_mul _ (splits_X_sub_C _) (ih _ (natDegree_removeFactor' hf))

theorem adjoin_rootSet (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤ :=
  Nat.recOn (motive := fun n =>
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤)
    n (fun {_} _ _ _hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree ≠ 0 := by intro h; rw [h] at hfn; cases hfn
    have hfn0 : f ≠ 0 := by intro h; rw [h] at hndf; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    classical
    rw [rootSet_def, aroots_def]
    rw [algebraMap_succ, ← map_map, ← X_sub_C_mul_removeFactor _ hndf, Polynomial.map_mul] at hmf0 ⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.toFinset_add,
      Finset.coe_union, Multiset.toFinset_singleton, Finset.coe_singleton,
      Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [Algebra.adjoin_algebraMap K (SplittingFieldAux n f.removeFactor)]
    rw [AdjoinRoot.adjoinRoot_eq_top, Algebra.map_top]
    -- Porting note: was `rw`
    erw [IsScalarTower.adjoin_range_toAlgHom K (AdjoinRoot f.factor)
        (SplittingFieldAux n f.removeFactor)
        (f.removeFactor.rootSet (SplittingFieldAux n f.removeFactor))]
    rw [ih _ (natDegree_removeFactor' hfn), Subalgebra.restrictScalars_top]

instance (f : K[X]) : IsSplittingField K (SplittingFieldAux f.natDegree f) f :=
  ⟨SplittingFieldAux.splits _ _ rfl, SplittingFieldAux.adjoin_rootSet _ _ rfl⟩

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
@[stacks 09HV "The construction of the splitting field."]
def SplittingField (f : K[X]) :=
  MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
deriving Inhabited, CommRing, Algebra K

namespace SplittingField

variable (f : K[X])

variable {S : Type*} [DistribSMul S K] [IsScalarTower S K K] in
deriving instance SMul S for SplittingField f

variable {R : Type*} [CommSemiring R] [Algebra R K] in
deriving instance Algebra R, IsScalarTower R K for SplittingField f

/-- The algebra equivalence with `SplittingFieldAux`,
which we will use to construct the field structure. -/
def algEquivSplittingFieldAux (f : K[X]) : SplittingField f ≃ₐ[K] SplittingFieldAux f.natDegree f :=
  Ideal.quotientKerAlgEquivOfSurjective fun x => ⟨MvPolynomial.X x, by simp⟩

instance instGroupWithZero : GroupWithZero (SplittingField f) :=
  let e := algEquivSplittingFieldAux f
  { inv := fun a ↦ e.symm (e a)⁻¹
    inv_zero := by simp
    mul_inv_cancel := fun a ha ↦ e.injective <| by simp [EmbeddingLike.map_ne_zero_iff.2 ha]
    __ := e.surjective.nontrivial }

instance instField : Field (SplittingField f) where
  __ := inferInstanceAs <| CommRing (SplittingField f)
  __ := instGroupWithZero f
  nnratCast q := algebraMap K _ q
  ratCast q := algebraMap K _ q
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by change algebraMap K _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap K _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
  nnqsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
  qsmul_def q x := Quotient.inductionOn x fun p ↦ congr_arg Quotient.mk'' <| by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

instance instCharZero [CharZero K] : CharZero (SplittingField f) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

instance instCharP (p : ℕ) [CharP K p] : CharP (SplittingField f) p :=
  charP_of_injective_algebraMap (algebraMap K _).injective p

instance instExpChar (p : ℕ) [ExpChar K p] : ExpChar (SplittingField f) p :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p

instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm

@[stacks 09HU "Splitting part"]
protected theorem splits : Splits (algebraMap K (SplittingField f)) f :=
  IsSplittingField.splits f.SplittingField f

variable [Algebra K L] (hb : Splits (algebraMap K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : SplittingField f →ₐ[K] L :=
  IsSplittingField.lift f.SplittingField f hb

theorem adjoin_rootSet : Algebra.adjoin K (f.rootSet (SplittingField f)) = ⊤ :=
  Polynomial.IsSplittingField.adjoin_rootSet _ f

end SplittingField

end SplittingField

namespace IsSplittingField

variable (K L)
variable [Algebra K L]
variable {K}

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

instance [Finite K] (f : K[X]) : Finite f.SplittingField :=
  Module.finite_of_finite K

instance (f : K[X]) : NoZeroSMulDivisors K f.SplittingField :=
  inferInstance

/-- Any splitting field is isomorphic to `SplittingFieldAux f`. -/
def algEquiv (f : K[X]) [h : IsSplittingField K L f] : L ≃ₐ[K] SplittingField f :=
  AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f) <|
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1

end IsSplittingField

end Polynomial
