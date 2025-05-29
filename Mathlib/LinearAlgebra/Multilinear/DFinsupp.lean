/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Sophie Morel
-/
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Finsupp.ToDFinsupp
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Interactions between finitely-supported functions and multilinear maps

## Main definitions

* `MultilinearMap.dfinsupp_ext`
* `MultilinearMap.dfinsuppFamily`, which satisfies
  `dfinsuppFamily f x p = f p (fun i => x i (p i))`.

  This is the finitely-supported version of `MultilinearMap.piFamily`.

  This is useful because all the intermediate results are bundled:

  - `MultilinearMap.dfinsuppFamily f x` is a `DFinsupp` supported by families of indices `p`.
  - `MultilinearMap.dfinsuppFamily f` is a `MultilinearMap` operating on finitely-supported
    functions `x`.
  - `MultilinearMap.dfinsuppFamilyₗ` is a `LinearMap`, linear in the family of multilinear maps `f`.

-/

universe uι uκ uS uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {S : Type uS} {R : Type uR}

namespace MultilinearMap

section Semiring
variable {M : ∀ i, κ i → Type uM} {N : Type uN}

variable [Finite ι] [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [AddCommMonoid N]
variable [∀ i k, Module R (M i k)] [Module R N]

/-- Two multilinear maps from finitely supported functions are equal if they agree on the
generators.

This is a multilinear version of `DFinsupp.lhom_ext'`. -/
@[ext]
theorem dfinsupp_ext [∀ i, DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => DFinsupp.lsingle (p i)) =
      g.compLinearMap (fun i => DFinsupp.lsingle (p i))) : f = g := by
  ext x
  show f (fun i ↦ x i) = g (fun i ↦ x i)
  classical
  cases nonempty_fintype ι
  rw [funext (fun i ↦ Eq.symm (DFinsupp.sum_single (f := x i)))]
  simp_rw [DFinsupp.sum, MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _

end Semiring

section dfinsuppFamily
variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}

section Semiring

variable [DecidableEq ι] [Fintype ι] [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/--
Given a family of indices `κ` and a multilinear map `f p` for each way `p` to select one index from
each family, `dfinsuppFamily f` maps a family of finitely-supported functions (one for each domain
`κ i`) into a finitely-supported function from each selection of indices (with domain `Π i, κ i`).

Strictly this doesn't need multilinearity, only the fact that `f p m = 0` whenever `m i = 0` for
some `i`.

This is the `DFinsupp` version of `MultilinearMap.piFamily`.
-/
@[simps]
def dfinsuppFamily
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun x :=
  { toFun := fun p => f p (fun i => x i (p i))
    support' := (Trunc.finChoice fun i => (x i).support').map fun s => ⟨
      Finset.univ.val.pi (fun i ↦ (s i).val) |>.map fun f i => f i (Finset.mem_univ _),
      fun p => by
        simp only [Multiset.mem_map, Multiset.mem_pi, Finset.mem_val, Finset.mem_univ,
          forall_true_left]
        simp_rw [or_iff_not_imp_right]
        intro h
        push_neg at h
        refine ⟨fun i _ => p i, fun i => (s i).prop _ |>.resolve_right ?_, rfl⟩
        exact mt ((f p).map_coord_zero (m := fun i => x i _) i) h⟩}
  map_update_add' {dec} m i x y := DFinsupp.ext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.add_apply, (f p).map_update_add]
  map_update_smul' {dec} m i c x := DFinsupp.ext fun p => by
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, DFinsupp.smul_apply,
      (f p).map_update_smul]

theorem support_dfinsuppFamily_subset
    [∀ i, DecidableEq (κ i)]
    [∀ i j, (x : M i j) → Decidable (x ≠ 0)] [∀ i, (x : N i) → Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (x : ∀ i, Π₀ j : κ i, M i j) :
    (dfinsuppFamily f x).support ⊆ Fintype.piFinset fun i => (x i).support := by
  intro p hp
  simp only [DFinsupp.mem_support_toFun, dfinsuppFamily_apply_toFun, ne_eq,
    Fintype.mem_piFinset] at hp ⊢
  intro i
  exact mt ((f p).map_coord_zero (m := fun i => x i _) i) hp

/-- When applied to a family of finitely-supported functions each supported on a single element,
`dfinsuppFamily` is itself supported on a single element, with value equal to the map `f` applied
at that point. -/
@[simp]
theorem dfinsuppFamily_single [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    dfinsuppFamily f (fun i => .single (p i) (m i)) = DFinsupp.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [DFinsupp.single_eq_of_ne hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [DFinsupp.single_eq_of_ne hpqi]

/-- When only one member of the family of multilinear maps is nonzero, the result consists only of
the component from that member. -/
@[simp]
theorem dfinsuppFamily_single_left_apply [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) (x : Π i, Π₀ j, M i j) :
    dfinsuppFamily (Pi.single p f) x = DFinsupp.single p (f fun i => x _ (p i)) := by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]

theorem dfinsuppFamily_single_left [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (Pi.single p f) =
      (DFinsupp.lsingle p).compMultilinearMap (f.compLinearMap fun i => DFinsupp.lapply (p i)) :=
  ext <| dfinsuppFamily_single_left_apply _ _

@[simp]
theorem dfinsuppFamily_compLinearMap_lsingle [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (dfinsuppFamily f).compLinearMap (fun i => DFinsupp.lsingle (p i))
      = (DFinsupp.lsingle p).compMultilinearMap (f p) :=
  MultilinearMap.ext <| dfinsuppFamily_single f p

@[simp]
theorem dfinsuppFamily_zero :
    dfinsuppFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) = 0 := by
  ext; simp

@[simp]
theorem dfinsuppFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (f + g) = dfinsuppFamily f + dfinsuppFamily g := by
  ext; simp

@[simp]
theorem dfinsuppFamily_smul
    [Monoid S] [∀ p, DistribMulAction S (N p)] [∀ p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    dfinsuppFamily (s • f) = s • dfinsuppFamily f := by
  ext; simp

end Semiring

section CommSemiring

variable [DecidableEq ι] [Fintype ι] [CommSemiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]

/-- `MultilinearMap.dfinsuppFamily` as a linear map. -/
@[simps]
def dfinsuppFamilyₗ :
    (Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
      →ₗ[R] MultilinearMap R (fun i => Π₀ j : κ i, M i j) (Π₀ t : Π i, κ i, N t) where
  toFun := dfinsuppFamily
  map_add' := dfinsuppFamily_add
  map_smul' := dfinsuppFamily_smul

section
variable {N : Type*} [AddCommMonoid N] [Module R N] [(i : ι) → DecidableEq (κ i)]

variable (R κ) in
/-- The linear equivalence between families indexed by `p : Π i : ι, κ i` of multilinear maps
on the `fun i ↦ M i (p i)` and the space of multilinear map on `fun i ↦ Π₀ j : κ i, M i j`. -/
def fromDFinsuppEquiv :
    ((p : Π i, κ i) → MultilinearMap R (fun i ↦ M i (p i)) N) ≃ₗ[R]
      MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N :=
  LinearEquiv.ofLinear
    ((DFinsupp.lsum ℕ fun _ ↦ .id).compMultilinearMapₗ R ∘ₗ MultilinearMap.dfinsuppFamilyₗ)
    (LinearMap.pi fun p ↦ MultilinearMap.compLinearMapₗ fun i ↦ DFinsupp.lsingle (p i))
    (by ext f x; simp)
    (by ext f p a; simp)

@[simp]
theorem fromDFinsuppEquiv_single
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    fromDFinsuppEquiv κ R f (fun i => DFinsupp.single (p i) (x i)) = f p x := by
  simp [fromDFinsuppEquiv]

/-- Prefer using `fromDFinsuppEquiv_of` where possible. -/
theorem fromDFinsuppEquiv_apply
    [Π i (j : κ i) (x : M i j), Decidable (x ≠ 0)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) N)
    (x : Π i, Π₀ (j : κ i), M i j) :
    fromDFinsuppEquiv κ R f x =
      ∑ p ∈ Fintype.piFinset (fun i ↦ (x i).support), f p (fun i ↦ x i (p i)) := by
  classical
  refine (DFinsupp.sumAddHom_apply _ _).trans ?_
  refine Finset.sum_subset (MultilinearMap.support_dfinsuppFamily_subset _ _) ?_
  simp

@[simp]
theorem fromDFinsuppEquiv_symm_apply (f : MultilinearMap R (fun i ↦ Π₀ j : κ i, M i j) N)
    (p : Π i, κ i) :
    (fromDFinsuppEquiv κ R).symm f p = f.compLinearMap (fun i ↦ DFinsupp.lsingle (p i)) :=
  rfl

end

end CommSemiring

end dfinsuppFamily


section Basis
variable {ι'} {M : ι → Type uM} {N : Type uN}

variable [Fintype ι] [∀ i, Fintype (κ i)] [CommSemiring R]
variable [∀ i, AddCommMonoid (M i)] [AddCommMonoid N]
variable [∀ i, Module R (M i)] [Module R N]

/-- A basis for multilinear maps given a finite basis on each domain and a basis on the codomain. -/
noncomputable def _root_.Basis.multilinearMap (b : ∀ i, Basis (κ i) R (M i)) (b' : Basis ι' R N) :
    Basis ((Π i, κ i) × ι') R (MultilinearMap R M N) where
  repr := by
    classical
    suffices
        MultilinearMap R (fun i => Π₀ j : κ i, R) (Π₀ i : ι', R) ≃ₗ[R]
          Π₀ (x : (Π i, κ i) × ι'), R by
      -- switch to DFinsupp, for a future where `Basis` uses this instead...
      refine ?_ ≪≫ₗ (finsuppLequivDFinsupp R).symm
      let b := fun i => (b i).repr ≪≫ₗ (finsuppLequivDFinsupp R)
      let b' := b'.repr ≪≫ₗ (finsuppLequivDFinsupp R)
      exact b'.congrRightMultilinear R ≪≫ₗ LinearEquiv.congrLeftMultilinear (b · |>.symm) ≪≫ₗ this
    refine (fromDFinsuppEquiv _ _).symm ≪≫ₗ
      LinearEquiv.piCongrRight (fun i => MultilinearMap.piRingEquiv.symm) ≪≫ₗ ?_
    -- some annoying swap between Π and Π₀
    refine ?_ ≪≫ₗ (DFinsupp.domLCongr (Equiv.sigmaEquivProd _ _).symm).symm
    exact DFinsupp.linearEquivFunOnFintype.symm ≪≫ₗ
      (DFinsupp.sigmaCurryLEquiv (M := fun _ _ => R)).symm

theorem _root_.Basis.multilinearMap_apply (b : ∀ i, Basis (κ i) R (M i)) (b' : Basis ι' R N)
    (i : (Π i, κ i) × ι') :
    Basis.multilinearMap b b' i =
      ((LinearMap.id (M := R)).smulRight (b' i.2)).compMultilinearMap (
        MultilinearMap.mkPiRing R ι 1 |>.compLinearMap fun i' => (b i').coord (i.1 i')
      ) := by
  -- TODO: clean this up
  obtain ⟨i, j⟩ := i
  classical
  simp [Basis.multilinearMap, Equiv.sigmaEquivProd]
  set bd' := (finsuppLequivDFinsupp R).symm.trans b'.repr.symm
  set bd := fun i => ((b i).repr ≪≫ₗ (finsuppLequivDFinsupp R)).toLinearMap
  conv_lhs =>
    enter [2, 1, 2, 2, 2]
    tactic =>
      trans DFinsupp.single (β := fun _ => Π₀ _, R) i (DFinsupp.single j (1 : R))
      sorry
  simp [DFinsupp.linearEquivFunOnFintype, LinearEquiv.piCongrRight, MultilinearMap.piRingEquiv,
    MultilinearMap.smulRight,
      LinearMap.smulRight]
  conv_lhs =>
    enter [2]
    simp [LinearMap.compMultilinearMap, Function.comp_def]
    enter [1, 2, i'']
    tactic =>
      trans Pi.single (f := fun _ => _) i (MultilinearMap.mkPiRing R ι (DFinsupp.single j 1)) i''
      sorry
  simp [fromDFinsuppEquiv, dfinsuppFamily_single_left, ← LinearMap.comp_compMultilinearMap,
    LinearEquiv.toLinearMap]
  conv_lhs =>
    enter [2, 1, 1]
    tactic =>
      trans .id
      ext
      simp
  simp [compLinearMap_assoc, bd]
  refine Basis.ext_multilinear b fun v => ?_
  simp [Basis.multilinearMap, Finsupp.linearCombination, MultilinearMap.piRingEquiv]
  sorry

/-- The elements of the basis are the maps which scale `b' ii.2` by the
product of all the `ii.1 ·` coordinates along `b i`. -/
theorem _root_.Basis.multilinearMap_apply_apply (b : ∀ i, Basis (κ i) R (M i)) (b' : Basis ι' R N)
    (ii : (Π i, κ i) × ι') (v) :
    Basis.multilinearMap b b' ii v = (∏ i, (b i).repr (v i) (ii.1 i)) • b' ii.2 := by
  simp [Basis.multilinearMap_apply]

end Basis
end MultilinearMap
