/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Bases of dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.
This file concerns bases on dual vector spaces.

## Main definitions

* Bases:
  * `Basis.toDual` produces the map `M →ₗ[R] Dual R M` associated to a basis for an `R`-module `M`.
  * `Basis.toDualEquiv` is the equivalence `M ≃ₗ[R] Dual R M` associated to a finite basis.
  * `Basis.dualBasis` is a basis for `Dual R M` given a finite basis for `M`.
  * `Module.DualBases e ε` is the proposition that the families `e` of vectors and `ε` of dual
    vectors have the characteristic properties of a basis and a dual.

## Main results

* Bases:
  * `Module.DualBases.basis` and `Module.DualBases.coe_basis`: if `e` and `ε` form a dual pair,
    then `e` is a basis.
  * `Module.DualBases.coe_dualBasis`: if `e` and `ε` form a dual pair,
    then `ε` is a basis.
-/

open Module Dual Submodule LinearMap Function

noncomputable section

namespace Module.Basis

universe u v w uR uM uK uV uι
variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]
variable (b : Basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def toDual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ fun v => b.constr ℕ fun w => if w = v then (1 : R) else 0

theorem toDual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 := by
  rw [toDual, constr_basis b, constr_basis b]
  simp only [eq_comm]

@[simp]
theorem toDual_linearCombination_left (f : ι →₀ R) (i : ι) :
    b.toDual (Finsupp.linearCombination R b f) (b i) = f i := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, LinearMap.sum_apply]
  simp_rw [LinearMap.map_smul, LinearMap.smul_apply, toDual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq', Finsupp.if_mem_support]

@[simp]
theorem toDual_linearCombination_right (f : ι →₀ R) (i : ι) :
    b.toDual (b i) (Finsupp.linearCombination R b f) = f i := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp_rw [LinearMap.map_smul, toDual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq,
    Finsupp.if_mem_support]

theorem toDual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i := by
  rw [← b.toDual_linearCombination_left, b.linearCombination_repr]

theorem toDual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i := by
  rw [← b.toDual_linearCombination_right, b.linearCombination_repr]

theorem coe_toDual_self (i : ι) : b.toDual (b i) = b.coord i := by
  ext
  apply toDual_apply_right

/-- `h.toDualFlip v` is the linear map sending `w` to `h.toDual w v`. -/
def toDualFlip (m : M) : M →ₗ[R] R :=
  b.toDual.flip m

theorem toDualFlip_apply (m₁ m₂ : M) : b.toDualFlip m₁ m₂ = b.toDual m₂ m₁ :=
  rfl

theorem toDual_eq_repr (m : M) (i : ι) : b.toDual m (b i) = b.repr m i :=
  b.toDual_apply_left m i

theorem toDual_eq_equivFun [Finite ι] (m : M) (i : ι) : b.toDual m (b i) = b.equivFun m i := by
  rw [b.equivFun_apply, toDual_eq_repr]

theorem toDual_injective : Injective b.toDual := fun x y h ↦ b.ext_elem_iff.mpr fun i ↦ by
  simp_rw [← toDual_eq_repr]; exact DFunLike.congr_fun h _

theorem toDual_inj (m : M) (a : b.toDual m = 0) : m = 0 :=
  b.toDual_injective (by rwa [map_zero])

theorem toDual_ker : LinearMap.ker b.toDual = ⊥ :=
  ker_eq_bot'.mpr b.toDual_inj

theorem toDual_range [Finite ι] : LinearMap.range b.toDual = ⊤ := by
  refine eq_top_iff'.2 fun f => ?_
  refine ⟨Finsupp.linearCombination R b (Finsupp.equivFunOnFinite.symm fun i => f (b i)),
    b.ext fun i => ?_⟩
  rw [b.toDual_eq_repr _ i, repr_linearCombination b, Finsupp.equivFunOnFinite_symm_apply_toFun]

omit [DecidableEq ι] in
@[simp]
theorem sum_dual_apply_smul_coord [Fintype ι] (f : Module.Dual R M) :
    (∑ x, f (b x) • b.coord x) = f := by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul,
    ← f.map_smul, ← map_sum, Basis.coord_apply, Basis.sum_repr]

section Finite

variable [Finite ι]

/-- A vector space is linearly equivalent to its dual space. -/
def toDualEquiv : M ≃ₗ[R] Dual R M :=
  .ofBijective b.toDual ⟨b.toDual_injective, range_eq_top.mp b.toDual_range⟩

-- `simps` times out when generating this
@[simp]
theorem toDualEquiv_apply (m : M) : b.toDualEquiv m = b.toDual m :=
  rfl

/-- Maps a basis for `V` to a basis for the dual space. -/
def dualBasis : Basis ι R (Dual R M) :=
  b.map b.toDualEquiv

-- We use `j = i` to match `Basis.repr_self`
theorem dualBasis_apply_self (i j : ι) : b.dualBasis i (b j) =
    if j = i then 1 else 0 := by
  convert b.toDual_apply i j using 2
  rw [@eq_comm _ j i]

theorem linearCombination_dualBasis (f : ι →₀ R) (i : ι) :
    Finsupp.linearCombination R b.dualBasis f (b i) = f i := by
  cases nonempty_fintype ι
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype, LinearMap.sum_apply]
  · simp_rw [LinearMap.smul_apply, smul_eq_mul, dualBasis_apply_self, mul_boole,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  · intro
    rw [zero_smul]

@[simp] theorem dualBasis_repr (l : Dual R M) (i : ι) : b.dualBasis.repr l i = l (b i) := by
  rw [← linearCombination_dualBasis b, Basis.linearCombination_repr b.dualBasis l]

theorem dualBasis_apply (i : ι) (m : M) : b.dualBasis i m = b.repr m i :=
  b.toDual_apply_right i m

@[simp]
theorem coe_dualBasis : ⇑b.dualBasis = b.coord := by
  ext i x
  apply dualBasis_apply

@[simp]
theorem toDual_toDual : b.dualBasis.toDual.comp b.toDual = Dual.eval R M := by
  refine b.ext fun i => b.dualBasis.ext fun j => ?_
  rw [LinearMap.comp_apply, toDual_apply_left, coe_toDual_self, ← coe_dualBasis,
    Dual.eval_apply, Basis.repr_self, Finsupp.single_apply, dualBasis_apply_self]

end Finite

theorem dualBasis_equivFun [Finite ι] (l : Dual R M) (i : ι) :
    b.dualBasis.equivFun l i = l (b i) := by rw [Basis.equivFun_apply, dualBasis_repr]

theorem eval_injective {ι : Type*} (b : Basis ι R M) : Function.Injective (Dual.eval R M) := by
  intro m m' eq
  simp_rw [LinearMap.ext_iff, Dual.eval_apply] at eq
  exact b.ext_elem fun i ↦ eq (b.coord i)

theorem eval_ker {ι : Type*} (b : Basis ι R M) : LinearMap.ker (Dual.eval R M) = ⊥ :=
  ker_eq_bot_of_injective (eval_injective b)

theorem eval_range {ι : Type*} [Finite ι] (b : Basis ι R M) :
    LinearMap.range (Dual.eval R M) = ⊤ := by
  classical
    cases nonempty_fintype ι
    rw [← b.toDual_toDual, range_comp, b.toDual_range, Submodule.map_top, toDual_range _]

lemma dualBasis_coord_toDualEquiv_apply [Finite ι] (i : ι) (f : M) :
    b.dualBasis.coord i (b.toDualEquiv f) = b.coord i f := by
  simp [-toDualEquiv_apply, Basis.dualBasis]

lemma coord_toDualEquiv_symm_apply [Finite ι] (i : ι) (f : Module.Dual R M) :
    b.coord i (b.toDualEquiv.symm f) = b.dualBasis.coord i f := by
  simp [Basis.dualBasis]

omit [DecidableEq ι]

/-- `simp` normal form version of `linearCombination_dualBasis` -/
@[simp]
theorem linearCombination_coord [Finite ι] (b : Basis ι R M) (f : ι →₀ R) (i : ι) :
    Finsupp.linearCombination R b.coord f (b i) = f i := by
  haveI := Classical.decEq ι
  rw [← coe_dualBasis, linearCombination_dualBasis]

end CommSemiring

end Module.Basis

section DualBases

variable {R M ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

open Lean.Elab.Tactic in
/-- Try using `Set.toFinite` to dispatch a `Set.Finite` goal. -/
def evalUseFiniteInstance : TacticM Unit := do
  evalTactic (← `(tactic| intros; apply Set.toFinite))

elab "use_finite_instance" : tactic => evalUseFiniteInstance

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
structure Module.DualBases (e : ι → M) (ε : ι → Dual R M) : Prop where
  eval_same : ∀ i, ε i (e i) = 1
  eval_of_ne : Pairwise fun i j ↦ ε i (e j) = 0
  protected total : ∀ {m₁ m₂ : M}, (∀ i, ε i m₁ = ε i m₂) → m₁ = m₂
  protected finite : ∀ m : M, {i | ε i m ≠ 0}.Finite := by use_finite_instance

end DualBases

namespace Module.DualBases

open LinearMap Function

variable {R M ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {e : ι → M} {ε : ι → Dual R M}

/-- The coefficients of `v` on the basis `e` -/
def coeffs (h : DualBases e ε) (m : M) : ι →₀ R where
  toFun i := ε i m
  support := (h.finite m).toFinset
  mem_support_toFun i := by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

@[simp]
theorem coeffs_apply (h : DualBases e ε) (m : M) (i : ι) : h.coeffs m i = ε i m :=
  rfl

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `Finsupp.linearCombination R e l` -/
def lc {ι} (e : ι → M) (l : ι →₀ R) : M :=
  l.sum fun (i : ι) (a : R) => a • e i

theorem lc_def (e : ι → M) (l : ι →₀ R) : lc e l = Finsupp.linearCombination R e l :=
  rfl

open Module

variable (h : DualBases e ε)
include h

theorem dual_lc (l : ι →₀ R) (i : ι) : ε i (DualBases.lc e l) = l i := by
  rw [lc, map_finsuppSum, Finsupp.sum_eq_single i (g := fun a b ↦ (ε i) (b • e a))]
  · simp [h.eval_same, smul_eq_mul]
  · intro q _ q_ne
    simp [h.eval_of_ne q_ne.symm, smul_eq_mul]
  · simp

@[simp]
theorem coeffs_lc (l : ι →₀ R) : h.coeffs (DualBases.lc e l) = l := by
  ext i
  rw [h.coeffs_apply, h.dual_lc]

/-- For any m : M n, \sum_{p ∈ Q n} (ε p m) • e p = m -/
@[simp]
theorem lc_coeffs (m : M) : DualBases.lc e (h.coeffs m) = m := h.total <| by simp [h.dual_lc]

/-- `(h : DualBases e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps repr_apply, simps -isSimp repr_symm_apply]
def basis : Basis ι R M :=
  Basis.ofRepr
    { toFun := coeffs h
      invFun := lc e
      left_inv := lc_coeffs h
      right_inv := coeffs_lc h
      map_add' := fun v w => by
        ext i
        exact (ε i).map_add v w
      map_smul' := fun c v => by
        ext i
        exact (ε i).map_smul c v }

@[simp]
theorem coe_basis : ⇑h.basis = e := by
  ext i
  rw [Basis.apply_eq_iff]
  ext j
  rcases eq_or_ne i j with rfl | hne
  · simp [h.eval_same]
  · simp [hne, h.eval_of_ne hne.symm]

theorem mem_of_mem_span {H : Set ι} {x : M} (hmem : x ∈ Submodule.span R (e '' H)) :
    ∀ i : ι, ε i x ≠ 0 → i ∈ H := by
  intro i hi
  rcases (Finsupp.mem_span_image_iff_linearCombination _).mp hmem with ⟨l, supp_l, rfl⟩
  apply not_imp_comm.mp ((Finsupp.mem_supported' _ _).mp supp_l i)
  rwa [← lc_def, h.dual_lc] at hi

theorem coe_dualBasis [DecidableEq ι] [Finite ι] : ⇑h.basis.dualBasis = ε :=
  funext fun i => h.basis.ext fun j => by simp

end Module.DualBases
