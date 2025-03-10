/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Bases

Further results on bases in modules and vector spaces.

-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace Basis

variable (b : Basis ι R M)

section Coord

theorem coe_sumCoords_eq_finsum : (b.sumCoords : M → R) = fun m => ∑ᶠ i, b.coord i m := by
  ext m
  simp only [Basis.sumCoords, Basis.coord, Finsupp.lapply_apply, LinearMap.id_coe,
    LinearEquiv.coe_coe, Function.comp_apply, Finsupp.coe_lsum, LinearMap.coe_comp,
    finsum_eq_sum _ (b.repr m).finite_support, Finsupp.sum, Finset.finite_toSet_toFinset, id,
    Finsupp.fun_support_eq]

end Coord

protected theorem linearIndependent : LinearIndependent R b :=
  fun x y hxy => by
    rw [← b.repr_linearCombination x, hxy, b.repr_linearCombination y]

protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=
  b.linearIndependent.ne_zero i

section Prod

variable (b' : Basis ι' R M')

/-- `Basis.prod` maps an `ι`-indexed basis for `M` and an `ι'`-indexed basis for `M'`
to an `ι ⊕ ι'`-index basis for `M × M'`.
For the specific case of `R × R`, see also `Basis.finTwoProd`. -/
protected def prod : Basis (ι ⊕ ι') R (M × M') :=
  ofRepr ((b.repr.prod b'.repr).trans (Finsupp.sumFinsuppLEquivProdFinsupp R).symm)

@[simp]
theorem prod_repr_inl (x) (i) : (b.prod b').repr x (Sum.inl i) = b.repr x.1 i :=
  rfl

@[simp]
theorem prod_repr_inr (x) (i) : (b.prod b').repr x (Sum.inr i) = b'.repr x.2 i :=
  rfl

theorem prod_apply_inl_fst (i) : (b.prod b' (Sum.inl i)).1 = b i :=
  b.repr.injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.fst_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inl_injective

theorem prod_apply_inr_fst (i) : (b.prod b' (Sum.inr i)).1 = 0 :=
  b.repr.injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.fst_sumFinsuppLEquivProdFinsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inr_ne_inl

theorem prod_apply_inl_snd (i) : (b.prod b' (Sum.inl i)).2 = 0 :=
  b'.repr.injective <| by
    ext j
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.snd_sumFinsuppLEquivProdFinsupp, LinearEquiv.map_zero,
      Finsupp.zero_apply]
    apply Finsupp.single_eq_of_ne Sum.inl_ne_inr

theorem prod_apply_inr_snd (i) : (b.prod b' (Sum.inr i)).2 = b' i :=
  b'.repr.injective <| by
    ext i
    simp only [Basis.prod, Basis.coe_ofRepr, LinearEquiv.symm_trans_apply, LinearEquiv.prod_symm,
      LinearEquiv.prod_apply, b'.repr.apply_symm_apply, LinearEquiv.symm_symm, repr_self,
      Equiv.toFun_as_coe, Finsupp.snd_sumFinsuppLEquivProdFinsupp]
    apply Finsupp.single_apply_left Sum.inr_injective

@[simp]
theorem prod_apply (i) :
    b.prod b' i = Sum.elim (LinearMap.inl R M M' ∘ b) (LinearMap.inr R M M' ∘ b') i := by
  ext <;> cases i <;>
    simp only [prod_apply_inl_fst, Sum.elim_inl, LinearMap.inl_apply, prod_apply_inr_fst,
      Sum.elim_inr, LinearMap.inr_apply, prod_apply_inl_snd, prod_apply_inr_snd, Function.comp]

end Prod

section NoZeroSMulDivisors

-- Can't be an instance because the basis can't be inferred.
protected theorem noZeroSMulDivisors [NoZeroDivisors R] (b : Basis ι R M) :
    NoZeroSMulDivisors R M :=
  ⟨fun {c x} hcx => by
    exact or_iff_not_imp_right.mpr fun hx => by
      rw [← b.linearCombination_repr x, ← LinearMap.map_smul,
        ← map_zero (linearCombination R b)] at hcx
      have := b.linearIndependent hcx
      rw [smul_eq_zero] at this
      exact this.resolve_right fun hr => hx (b.repr.map_eq_zero_iff.mp hr)⟩

protected theorem smul_eq_zero [NoZeroDivisors R] (b : Basis ι R M) {c : R} {x : M} :
    c • x = 0 ↔ c = 0 ∨ x = 0 :=
  @smul_eq_zero _ _ _ _ _ b.noZeroSMulDivisors _ _

end NoZeroSMulDivisors

section Singleton

theorem basis_singleton_iff {R M : Type*} [Ring R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (ι : Type*) [Unique ι] :
    Nonempty (Basis ι R M) ↔ ∃ x ≠ 0, ∀ y : M, ∃ r : R, r • x = y := by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, b.linearIndependent.ne_zero _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
    refine ⟨ofRepr <| LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single default (w y).choose
        left_inv := fun f => Finsupp.unique_ext ?_
        right_inv := fun y => ?_
        map_add' := fun y z => ?_
        map_smul' := fun c y => ?_ }⟩
    · simp [Finsupp.add_apply, add_smul]
    · simp only [Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [← smul_assoc]
    · refine smul_left_injective _ nz ?_
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).choose_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).choose_spec

end Singleton

variable {v : ι → M} {x y : M}

section Mk

variable (hli : LinearIndependent R v) (hsp : ⊤ ≤ span R (range v))

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : Basis ι R M :=
  .ofRepr
    { hli.repr.comp (LinearMap.id.codRestrict _ fun _ => hsp Submodule.mem_top) with
      invFun := Finsupp.linearCombination _ v
      left_inv := fun x => hli.linearCombination_repr ⟨x, _⟩
      right_inv := fun _ => hli.repr_eq rfl }

@[simp]
theorem mk_repr : (Basis.mk hli hsp).repr x = hli.repr ⟨x, hsp Submodule.mem_top⟩ :=
  rfl

theorem mk_apply (i : ι) : Basis.mk hli hsp i = v i :=
  show Finsupp.linearCombination _ v _ = v i by simp

@[simp]
theorem coe_mk : ⇑(Basis.mk hli hsp) = v :=
  funext (mk_apply _ _)

variable {hli hsp}

/-- Given a basis, the `i`th element of the dual basis evaluates to 1 on the `i`th element of the
basis. -/
theorem mk_coord_apply_eq (i : ι) : (Basis.mk hli hsp).coord i (v i) = 1 :=
  show hli.repr ⟨v i, Submodule.subset_span (mem_range_self i)⟩ i = 1 by simp [hli.repr_eq_single i]

/-- Given a basis, the `i`th element of the dual basis evaluates to 0 on the `j`th element of the
basis if `j ≠ i`. -/
theorem mk_coord_apply_ne {i j : ι} (h : j ≠ i) : (Basis.mk hli hsp).coord i (v j) = 0 :=
  show hli.repr ⟨v j, Submodule.subset_span (mem_range_self j)⟩ i = 0 by
    simp [hli.repr_eq_single j, h]

/-- Given a basis, the `i`th element of the dual basis evaluates to the Kronecker delta on the
`j`th element of the basis. -/
theorem mk_coord_apply [DecidableEq ι] {i j : ι} :
    (Basis.mk hli hsp).coord i (v j) = if j = i then 1 else 0 := by
  rcases eq_or_ne j i with h | h
  · simp only [h, if_true, eq_self_iff_true, mk_coord_apply_eq i]
  · simp only [h, if_false, mk_coord_apply_ne h]

end Mk

section Span

variable (hli : LinearIndependent R v)

/-- A linear independent family of vectors is a basis for their span. -/
protected noncomputable def span : Basis ι R (span R (range v)) :=
  Basis.mk (linearIndependent_span hli) <| by
    intro x _
    have : ∀ i, v i ∈ span R (range v) := fun i ↦ subset_span (Set.mem_range_self _)
    have h₁ : (((↑) : span R (range v) → M) '' range fun i => ⟨v i, this i⟩) = range v := by
      simp only [SetLike.coe_sort_coe, ← Set.range_comp]
      rfl
    have h₂ : map (Submodule.subtype (span R (range v))) (span R (range fun i => ⟨v i, this i⟩)) =
        span R (range v) := by
      rw [← span_image, Submodule.coe_subtype, h₁]
    have h₃ : (x : M) ∈ map (Submodule.subtype (span R (range v)))
        (span R (Set.range fun i => Subtype.mk (v i) (this i))) := by
      rw [h₂]
      apply Subtype.mem x
    rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩
    have h_x_eq_y : x = y := by
      rw [Subtype.ext_iff, ← hy₂]
      simp
    rwa [h_x_eq_y]

protected theorem span_apply (i : ι) : (Basis.span hli i : M) = v i :=
  congr_arg ((↑) : span R (range v) → M) <| Basis.mk_apply _ _ _

end Span

theorem groupSMul_span_eq_top {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → G} :
    Submodule.span R (Set.range (w • v)) = ⊤ := by
  rw [eq_top_iff]
  intro j hj
  rw [← hv] at hj
  rw [Submodule.mem_span] at hj ⊢
  refine fun p hp => hj p fun u hu => ?_
  obtain ⟨i, rfl⟩ := hu
  have : ((w i)⁻¹ • (1 : R)) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • (1 : R)) (hp ⟨i, rfl⟩)
  rwa [smul_one_smul, inv_smul_smul] at this

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`groupSMul` provides the basis corresponding to `w • v`. -/
def groupSMul {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] (v : Basis ι R M) (w : ι → G) : Basis ι R M :=
  Basis.mk (LinearIndependent.group_smul v.linearIndependent w) (groupSMul_span_eq_top v.span_eq).ge

theorem groupSMul_apply {G : Type*} [Group G] [DistribMulAction G R] [DistribMulAction G M]
    [IsScalarTower G R M] [SMulCommClass G R M] {v : Basis ι R M} {w : ι → G} (i : ι) :
    v.groupSMul w i = (w • (v : ι → M)) i :=
  mk_apply (LinearIndependent.group_smul v.linearIndependent w)
    (groupSMul_span_eq_top v.span_eq).ge i

theorem units_smul_span_eq_top {v : ι → M} (hv : Submodule.span R (Set.range v) = ⊤) {w : ι → Rˣ} :
    Submodule.span R (Set.range (w • v)) = ⊤ :=
  groupSMul_span_eq_top hv

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `unitsSMul`
provides the basis corresponding to `w • v`. -/
def unitsSMul (v : Basis ι R M) (w : ι → Rˣ) : Basis ι R M :=
  Basis.mk (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge

theorem unitsSMul_apply {v : Basis ι R M} {w : ι → Rˣ} (i : ι) : unitsSMul v w i = w i • v i :=
  mk_apply (LinearIndependent.units_smul v.linearIndependent w)
    (units_smul_span_eq_top v.span_eq).ge i

variable [CommSemiring R₂] [Module R₂ M]

@[simp]
theorem coord_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (i : ι) :
    (unitsSMul e w).coord i = (w i)⁻¹ • e.coord i := by
  classical
    apply e.ext
    intro j
    trans ((unitsSMul e w).coord i) ((w j)⁻¹ • (unitsSMul e w) j)
    · congr
      simp [Basis.unitsSMul, ← mul_smul]
    simp only [Basis.coord_apply, LinearMap.smul_apply, Basis.repr_self, Units.smul_def,
      map_smul, Finsupp.single_apply]
    split_ifs with h <;> simp [h]

@[simp]
theorem repr_unitsSMul (e : Basis ι R₂ M) (w : ι → R₂ˣ) (v : M) (i : ι) :
    (e.unitsSMul w).repr v i = (w i)⁻¹ • e.repr v i :=
  congr_arg (fun f : M →ₗ[R₂] R₂ => f v) (e.coord_unitsSMul w i)

/-- A version of `unitsSMul` that uses `IsUnit`. -/
def isUnitSMul (v : Basis ι R M) {w : ι → R} (hw : ∀ i, IsUnit (w i)) : Basis ι R M :=
  unitsSMul v fun i => (hw i).unit

theorem isUnitSMul_apply {v : Basis ι R M} {w : ι → R} (hw : ∀ i, IsUnit (w i)) (i : ι) :
    v.isUnitSMul hw i = w i • v i :=
  unitsSMul_apply i

theorem repr_isUnitSMul {v : Basis ι R₂ M} {w : ι → R₂} (hw : ∀ i, IsUnit (w i)) (x : M) (i : ι) :
    (v.isUnitSMul hw).repr x i = (hw i).unit⁻¹ • v.repr x i :=
  repr_unitsSMul _ _ _ _

/-- Any basis is a maximal linear independent set.
-/
theorem maximal [Nontrivial R] (b : Basis ι R M) : b.linearIndependent.Maximal := fun w hi h => by
  -- If `w` is strictly bigger than `range b`,
  apply le_antisymm h
  -- then choose some `x ∈ w \ range b`,
  intro x p
  by_contra q
  -- and write it in terms of the basis.
  have e := b.linearCombination_repr x
  -- This then expresses `x` as a linear combination
  -- of elements of `w` which are in the range of `b`,
  let u : ι ↪ w :=
    ⟨fun i => ⟨b i, h ⟨i, rfl⟩⟩, fun i i' r =>
      b.injective (by simpa only [Subtype.mk_eq_mk] using r)⟩
  simp_rw [Finsupp.linearCombination_apply] at e
  change ((b.repr x).sum fun (i : ι) (a : R) ↦ a • (u i : M)) = ((⟨x, p⟩ : w) : M) at e
  rw [← Finsupp.sum_embDomain (f := u) (g := fun x r ↦ r • (x : M)),
      ← Finsupp.linearCombination_apply] at e
  -- Now we can contradict the linear independence of `hi`
  refine hi.linearCombination_ne_of_not_mem_support _ ?_ e
  simp only [Finset.mem_map, Finsupp.support_embDomain]
  rintro ⟨j, -, W⟩
  simp only [u, Embedding.coeFn_mk, Subtype.mk_eq_mk] at W
  apply q ⟨j, W⟩

end Basis

end Module

section Module

open LinearMap

variable {v : ι → M}
variable [Ring R] [CommRing R₂] [AddCommGroup M]
variable [Module R M] [Module R₂ M]
variable {x y : M}
variable (b : Basis ι R M)

theorem Basis.eq_bot_of_rank_eq_zero [NoZeroDivisors R] (b : Basis ι R M) (N : Submodule R M)
    (rank_eq : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m = 0) :
    N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine ⟨1, fun _ => ⟨x, hx⟩, ?_, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  obtain ⟨_, hi⟩ := i
  simp only [Function.const_apply, Fin.default_eq_zero, Submodule.coe_mk, Finset.univ_unique,
    Function.comp_const, Finset.sum_singleton] at sum_eq
  convert (b.smul_eq_zero.mp sum_eq).resolve_right x_ne

namespace Basis

section Fin

/-- Let `b` be a basis for a submodule `N` of `M`. If `y : M` is linear independent of `N`
and `y` and `N` together span the whole of `M`, then there is a basis for `M`
whose basis vectors are given by `Fin.cons y b`. -/
noncomputable def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : Submodule.span R (Set.range (N.subtype ∘ b)) = N := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).fin_cons' _ _
      (by
        rintro c ⟨x, hx⟩ hc
        rw [span_b] at hx
        exact hli c x hx hc))
    fun x _ => by
      rw [Fin.range_cons, Submodule.mem_span_insert', span_b]
      exact hsp x

@[simp]
theorem coe_mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    (mkFinCons y b hli hsp : Fin (n + 1) → M) = Fin.cons y ((↑) ∘ b) := by
  unfold mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _

/-- Let `b` be a basis for a submodule `N ≤ O`. If `y ∈ O` is linear independent of `N`
and `y` and `N` together span the whole of `O`, then there is a basis for `O`
whose basis vectors are given by `Fin.cons y b`. -/
noncomputable def mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O)
    (b : Basis (Fin n) R N) (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O → M) hx))
    fun z => hsp z z.2

@[simp]
theorem coe_mkFinConsOfLE {n : ℕ} {N O : Submodule R M} (y : M) (yO : y ∈ O) (b : Basis (Fin n) R N)
    (hNO : N ≤ O) (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0)
    (hsp : ∀ z ∈ O, ∃ c : R, z + c • y ∈ N) :
    (mkFinConsOfLE y yO b hNO hli hsp : Fin (n + 1) → O) =
      Fin.cons ⟨y, yO⟩ (Submodule.inclusion hNO ∘ b) :=
  coe_mkFinCons _ _ _ _

/-- The basis of `R × R` given by the two vectors `(1, 0)` and `(0, 1)`. -/
protected def finTwoProd (R : Type*) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm

@[simp]
theorem finTwoProd_zero (R : Type*) [Semiring R] : Basis.finTwoProd R 0 = (1, 0) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]
theorem finTwoProd_one (R : Type*) [Semiring R] : Basis.finTwoProd R 1 = (0, 1) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]
theorem coe_finTwoProd_repr {R : Type*} [Semiring R] (x : R × R) :
    ⇑((Basis.finTwoProd R).repr x) = ![x.fst, x.snd] :=
  rfl

end Fin

end Basis

end Module

section Induction

variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι → M}

/-- If `N` is a submodule with finite rank, do induction on adjoining a linear independent
element to a submodule. -/
def Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M → Sort*)
    (ih : ∀ N : Submodule R M,
      (∀ N' ≤ N, ∀ x ∈ N, (∀ (c : R), ∀ y ∈ N', c • x + y = (0 : M) → c = 0) → P N') → P N)
    (n : ℕ) (N : Submodule R M)
    (rank_le : ∀ {m : ℕ} (v : Fin m → N), LinearIndependent R ((↑) ∘ v : Fin m → M) → m ≤ n) :
    P N := by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N _ x x_mem x_ortho
    exfalso
    rw [mem_bot] at x_mem
    simpa [x_mem] using x_ortho 1 0 N.zero_mem
  induction n generalizing N with
  | zero =>
    suffices N = ⊥ by rwa [this]
    apply Basis.eq_bot_of_rank_eq_zero b _ fun m hv => Nat.le_zero.mp (rank_le _ hv)
  | succ n rank_ih =>
    apply ih
    intro N' N'_le x x_mem x_ortho
    apply rank_ih
    intro m v hli
    refine Nat.succ_le_succ_iff.mp (rank_le (Fin.cons ⟨x, x_mem⟩ fun i => ⟨v i, N'_le (v i).2⟩) ?_)
    convert hli.fin_cons' x _ ?_
    · ext i
      refine Fin.cases ?_ ?_ i <;> simp
    · intro c y hcy
      refine x_ortho c y (Submodule.span_le.mpr ?_ y.2) hcy
      rintro _ ⟨z, rfl⟩
      exact (v z).2

end Induction

/-- An element of a non-unital-non-associative algebra is in the center exactly when it commutes
with the basis elements. -/
lemma Basis.mem_center_iff {A}
    [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [SMulCommClass R A A] [SMulCommClass R R A] [IsScalarTower R A A]
    (b : Basis ι R A) {z : A} :
    z ∈ Set.center A ↔
      (∀ i, Commute (b i) z) ∧ ∀ i j,
        z * (b i * b j) = (z * b i) * b j
          ∧ (b i * z) * b j = b i * (z * b j)
          ∧ (b i * b j) * z = b i * (b j * z) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, ⟨h.3 _ _, h.4 _ _⟩⟩
  · intro h
    rw [center, mem_setOf_eq]
    constructor
    case comm =>
      intro y
      rw [← b.linearCombination_repr y, linearCombination_apply, sum, Finset.sum_mul,
          Finset.mul_sum]
      simp_rw [mul_smul_comm, smul_mul_assoc, (h.1 _).eq]
    case left_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
        Finset.smul_sum, smul_mul_assoc, mul_smul_comm, (h.2 _ _).1,
        (@SMulCommClass.smul_comm R R A)]
      rw [Finset.sum_comm]
    case mid_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, sum, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
          Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, (h.2 _ _).2.1]
    case right_assoc =>
      intro c d
      rw [← b.linearCombination_repr c, ← b.linearCombination_repr d, linearCombination_apply,
          linearCombination_apply, sum, Finsupp.sum, Finset.sum_mul]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
               Finset.smul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, smul_mul_assoc,
               (h.2 _ _).2.2]

section RestrictScalars

variable {S : Type*} [CommRing R] [Ring S] [Nontrivial S] [AddCommGroup M]
variable [Algebra R S] [Module S M] [Module R M]
variable [IsScalarTower R S M] [NoZeroSMulDivisors R S] (b : Basis ι S M)
variable (R)

open Submodule

/-- Let `b` be an `S`-basis of `M`. Let `R` be a CommRing such that `Algebra R S` has no zero smul
divisors, then the submodule of `M` spanned by `b` over `R` admits `b` as an `R`-basis. -/
noncomputable def Basis.restrictScalars : Basis ι R (span R (Set.range b)) :=
  Basis.span (b.linearIndependent.restrict_scalars (smul_left_injective R one_ne_zero))

@[simp]
theorem Basis.restrictScalars_apply (i : ι) : (b.restrictScalars R i : M) = b i := by
  simp only [Basis.restrictScalars, Basis.span_apply]

@[simp]
theorem Basis.restrictScalars_repr_apply (m : span R (Set.range b)) (i : ι) :
    algebraMap R S ((b.restrictScalars R).repr m i) = b.repr m i := by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M →ₗ[S] ι →₀ S).restrictScalars R).domRestrict _
    by exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply, map_one,
    Basis.repr_self, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, LinearMap.domRestrict_apply, LinearEquiv.coe_coe,
    Basis.restrictScalars_apply, LinearMap.coe_restrictScalars]

/-- Let `b` be an `S`-basis of `M`. Then `m : M` lies in the `R`-module spanned by `b` iff all the
coordinates of `m` on the basis `b` are in `R` (see `Basis.mem_span` for the case `R = S`). -/
theorem Basis.mem_span_iff_repr_mem (m : M) :
    m ∈ span R (Set.range b) ↔ ∀ i, b.repr m i ∈ Set.range (algebraMap R S) := by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, b.restrictScalars_repr_apply R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exact smul_mem _ _ (subset_span (Set.mem_range_self i))

end RestrictScalars
