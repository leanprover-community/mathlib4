/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.SesquilinearForm
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.

## Main definitions

* Duals and transposes:
  * `Module.Dual R M` defines the dual space of the `R`-module `M`, as `M →ₗ[R] R`.
  * `Module.dualPairing R M` is the canonical pairing between `Dual R M` and `M`.
  * `Module.Dual.eval R M : M →ₗ[R] Dual R (Dual R)` is the canonical map to the double dual.
  * `Module.Dual.transpose` is the linear map from `M →ₗ[R] M'` to `Dual R M' →ₗ[R] Dual R M`.
  * `LinearMap.dualMap` is `Module.Dual.transpose` of a given linear map, for dot notation.
  * `LinearEquiv.dualMap` is for the dual of an equivalence.
* Bases:
  * `Basis.toDual` produces the map `M →ₗ[R] Dual R M` associated to a basis for an `R`-module `M`.
  * `Basis.toDual_equiv` is the equivalence `M ≃ₗ[R] Dual R M` associated to a finite basis.
  * `Basis.dualBasis` is a basis for `Dual R M` given a finite basis for `M`.
  * `Module.dual_bases e ε` is the proposition that the families `e` of vectors and `ε` of dual
    vectors have the characteristic properties of a basis and a dual.
* Submodules:
  * `Submodule.dualRestrict W` is the transpose `Dual R M →ₗ[R] Dual R W` of the inclusion map.
  * `Submodule.dualAnnihilator W` is the kernel of `W.dualRestrict`. That is, it is the submodule
    of `dual R M` whose elements all annihilate `W`.
  * `Submodule.dualRestrict_comap W'` is the dual annihilator of `W' : Submodule R (Dual R M)`,
    pulled back along `Module.Dual.eval R M`.
  * `Submodule.dualCopairing W` is the canonical pairing between `W.dualAnnihilator` and `M ⧸ W`.
    It is nondegenerate for vector spaces (`subspace.dualCopairing_nondegenerate`).
  * `Submodule.dualPairing W` is the canonical pairing between `Dual R M ⧸ W.dualAnnihilator`
    and `W`. It is nondegenerate for vector spaces (`Subspace.dualPairing_nondegenerate`).
* Vector spaces:
  * `Subspace.dualLift W` is an arbitrary section (using choice) of `Submodule.dualRestrict W`.

## Main results

* Bases:
  * `Module.dualBasis.basis` and `Module.dualBasis.coe_basis`: if `e` and `ε` form a dual pair,
    then `e` is a basis.
  * `Module.dualBasis.coe_dualBasis`: if `e` and `ε` form a dual pair,
    then `ε` is a basis.
* Annihilators:
  * `Module.dualAnnihilator_gc R M` is the antitone Galois correspondence between
    `Submodule.dualAnnihilator` and `Submodule.dualConnihilator`.
  * `LinearMap.ker_dual_map_eq_dualAnnihilator_range` says that
    `f.dual_map.ker = f.range.dualAnnihilator`
  * `LinearMap.range_dual_map_eq_dualAnnihilator_ker_of_subtype_range_surjective` says that
    `f.dual_map.range = f.ker.dualAnnihilator`; this is specialized to vector spaces in
    `LinearMap.range_dual_map_eq_dualAnnihilator_ker`.
  * `Submodule.dualQuotEquivDualAnnihilator` is the equivalence
    `Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator`
  * `Submodule.quotDualCoannihilatorToDual` is the nondegenerate pairing
    `M ⧸ W.dualCoannihilator →ₗ[R] Dual R W`.
    It is an perfect pairing when `R` is a field and `W` is finite-dimensional.
* Vector spaces:
  * `Subspace.dualAnnihilator_dualConnihilator_eq` says that the double dual annihilator,
    pulled back ground `Module.Dual.eval`, is the original submodule.
  * `Subspace.dualAnnihilator_gci` says that `module.dualAnnihilator_gc R M` is an
    antitone Galois coinsertion.
  * `Subspace.quotAnnihilatorEquiv` is the equivalence
    `Dual K V ⧸ W.dualAnnihilator ≃ₗ[K] Dual K W`.
  * `LinearMap.dualPairing_nondegenerate` says that `Module.dualPairing` is nondegenerate.
  * `Subspace.is_compl_dualAnnihilator` says that the dual annihilator carries complementary
    subspaces to complementary subspaces.
* Finite-dimensional vector spaces:
  * `Module.evalEquiv` is the equivalence `V ≃ₗ[K] Dual K (Dual K V)`
  * `Module.mapEvalEquiv` is the order isomorphism between subspaces of `V` and
    subspaces of `Dual K (Dual K V)`.
  * `Subspace.orderIsoFiniteCodimDim` is the antitone order isomorphism between
    finite-codimensional subspaces of `V` and finite-dimensional subspaces of `Dual K V`.
  * `Subspace.orderIsoFiniteDimensional` is the antitone order isomorphism between
    subspaces of a finite-dimensional vector space `V` and subspaces of its dual.
  * `Subspace.quotDualEquivAnnihilator W` is the equivalence
    `(Dual K V ⧸ W.dualLift.range) ≃ₗ[K] W.dualAnnihilator`, where `W.dualLift.range` is a copy
    of `Dual K W` inside `Dual K V`.
  * `Subspace.quotEquivAnnihilator W` is the equivalence `(V ⧸ W) ≃ₗ[K] W.dualAnnihilator`
  * `Subspace.dualQuotDistrib W` is an equivalence
    `Dual K (V₁ ⧸ W) ≃ₗ[K] Dual K V₁ ⧸ W.dualLift.range` from an arbitrary choice of
    splitting of `V₁`.
-/

open Module Submodule

noncomputable section

namespace Module

-- Porting note: max u v universe issues so name and specific below
universe uR uA uM uM' uM''

variable (R : Type uR) (A : Type uA) (M : Type uM)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
abbrev Dual :=
  M →ₗ[R] R

/-- The canonical pairing of a vector space and its algebraic dual. -/
def dualPairing (R M) [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module.Dual R M →ₗ[R] M →ₗ[R] R :=
  LinearMap.id

@[simp]
theorem dualPairing_apply (v x) : dualPairing R M v x = v x :=
  rfl

namespace Dual

instance : Inhabited (Dual R M) := ⟨0⟩

/-- Maps a module M to the dual of the dual of M. See `Module.erange_coe` and
`Module.evalEquiv`. -/
def eval : M →ₗ[R] Dual R (Dual R M) :=
  LinearMap.flip LinearMap.id

@[simp]
theorem eval_apply (v : M) (a : Dual R M) : eval R M v a = a v :=
  rfl

variable {R M} {M' : Type uM'}
variable [AddCommMonoid M'] [Module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`Dual R M' →ₗ[R] Dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] Dual R M' →ₗ[R] Dual R M :=
  (LinearMap.llcomp R M M' R).flip

-- Porting note: with reducible def need to specify some parameters to transpose explicitly
theorem transpose_apply (u : M →ₗ[R] M') (l : Dual R M') : transpose (R := R) u l = l.comp u :=
  rfl

variable {M'' : Type uM''} [AddCommMonoid M''] [Module R M'']

-- Porting note: with reducible def need to specify some parameters to transpose explicitly
theorem transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
    transpose (R := R) (u.comp v) = (transpose (R := R) v).comp (transpose (R := R) u) :=
  rfl

end Dual

section Prod

variable (M' : Type uM') [AddCommMonoid M'] [Module R M']

/-- Taking duals distributes over products. -/
@[simps!]
def dualProdDualEquivDual : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M') :=
  LinearMap.coprodEquiv R

@[simp]
theorem dualProdDualEquivDual_apply (φ : Module.Dual R M) (ψ : Module.Dual R M') :
    dualProdDualEquivDual R M M' (φ, ψ) = φ.coprod ψ :=
  rfl

end Prod

end Module

section DualMap

open Module

universe u v v'

variable {R : Type u} [CommSemiring R] {M₁ : Type v} {M₂ : Type v'}
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dualMap` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def LinearMap.dualMap (f : M₁ →ₗ[R] M₂) : Dual R M₂ →ₗ[R] Dual R M₁ :=
-- Porting note: with reducible def need to specify some parameters to transpose explicitly
  Module.Dual.transpose (R := R) f

lemma LinearMap.dualMap_eq_lcomp (f : M₁ →ₗ[R] M₂) : f.dualMap = f.lcomp R R := rfl

-- Porting note: with reducible def need to specify some parameters to transpose explicitly
theorem LinearMap.dualMap_def (f : M₁ →ₗ[R] M₂) : f.dualMap = Module.Dual.transpose (R := R) f :=
  rfl

theorem LinearMap.dualMap_apply' (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) : f.dualMap g = g.comp f :=
  rfl

@[simp]
theorem LinearMap.dualMap_apply (f : M₁ →ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
theorem LinearMap.dualMap_id : (LinearMap.id : M₁ →ₗ[R] M₁).dualMap = LinearMap.id := by
  ext
  rfl

theorem LinearMap.dualMap_comp_dualMap {M₃ : Type*} [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) : f.dualMap.comp g.dualMap = (g.comp f).dualMap :=
  rfl

/-- If a linear map is surjective, then its dual is injective. -/
theorem LinearMap.dualMap_injective_of_surjective {f : M₁ →ₗ[R] M₂} (hf : Function.Surjective f) :
    Function.Injective f.dualMap := by
  intro φ ψ h
  ext x
  obtain ⟨y, rfl⟩ := hf x
  exact congr_arg (fun g : Module.Dual R M₁ => g y) h

/-- The `Linear_equiv` version of `LinearMap.dualMap`. -/
def LinearEquiv.dualMap (f : M₁ ≃ₗ[R] M₂) : Dual R M₂ ≃ₗ[R] Dual R M₁ where
  __ := f.toLinearMap.dualMap
  invFun := f.symm.toLinearMap.dualMap
  left_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.right_inv x)
  right_inv φ := LinearMap.ext fun x ↦ congr_arg φ (f.left_inv x)

@[simp]
theorem LinearEquiv.dualMap_apply (f : M₁ ≃ₗ[R] M₂) (g : Dual R M₂) (x : M₁) :
    f.dualMap g x = g (f x) :=
  rfl

@[simp]
theorem LinearEquiv.dualMap_refl :
    (LinearEquiv.refl R M₁).dualMap = LinearEquiv.refl R (Dual R M₁) := by
  ext
  rfl

@[simp]
theorem LinearEquiv.dualMap_symm {f : M₁ ≃ₗ[R] M₂} :
    (LinearEquiv.dualMap f).symm = LinearEquiv.dualMap f.symm :=
  rfl

theorem LinearEquiv.dualMap_trans {M₃ : Type*} [AddCommGroup M₃] [Module R M₃] (f : M₁ ≃ₗ[R] M₂)
    (g : M₂ ≃ₗ[R] M₃) : g.dualMap.trans f.dualMap = (f.trans g).dualMap :=
  rfl

theorem Module.Dual.eval_naturality (f : M₁ →ₗ[R] M₂) :
    f.dualMap.dualMap ∘ₗ eval R M₁ = eval R M₂ ∘ₗ f := by
  rfl

@[simp]
lemma Dual.apply_one_mul_eq (f : Dual R R) (r : R) :
    f 1 * r = f r := by
  conv_rhs => rw [← mul_one r, ← smul_eq_mul]
  rw [map_smul, smul_eq_mul, mul_comm]

@[simp]
lemma LinearMap.range_dualMap_dual_eq_span_singleton (f : Dual R M₁) :
    range f.dualMap = R ∙ f := by
  ext m
  rw [Submodule.mem_span_singleton]
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r 1, ?_⟩, fun ⟨r, hr⟩ ↦ ⟨r • LinearMap.id, ?_⟩⟩
  · ext; simp [dualMap_apply', ← hr]
  · ext; simp [dualMap_apply', ← hr]

end DualMap

namespace Basis

universe u v w

open Module Module.Dual Submodule LinearMap Cardinal Function

universe uR uM uK uV uι
variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [DecidableEq ι]
variable (b : Basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def toDual : M →ₗ[R] Module.Dual R M :=
  b.constr ℕ fun v => b.constr ℕ fun w => if w = v then (1 : R) else 0

theorem toDual_apply (i j : ι) : b.toDual (b i) (b j) = if i = j then 1 else 0 := by
  erw [constr_basis b, constr_basis b]
  simp only [eq_comm]

@[simp]
theorem toDual_linearCombination_left (f : ι →₀ R) (i : ι) :
    b.toDual (Finsupp.linearCombination R b f) (b i) = f i := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, _root_.map_sum, LinearMap.sum_apply]
  simp_rw [LinearMap.map_smul, LinearMap.smul_apply, toDual_apply, smul_eq_mul, mul_boole,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Finsupp.not_mem_support_iff.mp h]

@[deprecated (since := "2024-08-29")] alias toDual_total_left := toDual_linearCombination_left

@[simp]
theorem toDual_linearCombination_right (f : ι →₀ R) (i : ι) :
    b.toDual (b i) (Finsupp.linearCombination R b f) = f i := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, _root_.map_sum]
  simp_rw [LinearMap.map_smul, toDual_apply, smul_eq_mul, mul_boole, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finsupp.not_mem_support_iff.mp h]

@[deprecated (since := "2024-08-29")] alias toDual_total_right :=
  toDual_linearCombination_right

theorem toDual_apply_left (m : M) (i : ι) : b.toDual m (b i) = b.repr m i := by
  rw [← b.toDual_linearCombination_left, b.linearCombination_repr]

theorem toDual_apply_right (i : ι) (m : M) : b.toDual (b i) m = b.repr m i := by
  rw [← b.toDual_linearCombination_right, b.linearCombination_repr]

theorem coe_toDual_self (i : ι) : b.toDual (b i) = b.coord i := by
  ext
  apply toDual_apply_right

/-- `h.toDual_flip v` is the linear map sending `w` to `h.toDual w v`. -/
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
  b.toDual_injective (by rwa [_root_.map_zero])

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.ker
theorem toDual_ker : LinearMap.ker b.toDual = ⊥ :=
  ker_eq_bot'.mpr b.toDual_inj

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
theorem toDual_range [Finite ι] : LinearMap.range b.toDual = ⊤ := by
  refine eq_top_iff'.2 fun f => ?_
  let lin_comb : ι →₀ R := Finsupp.equivFunOnFinite.symm fun i => f (b i)
  refine ⟨Finsupp.linearCombination R b lin_comb, b.ext fun i => ?_⟩
  rw [b.toDual_eq_repr _ i, repr_linearCombination b]
  rfl

end CommSemiring

section

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [Fintype ι]
variable (b : Basis ι R M)

@[simp]
theorem sum_dual_apply_smul_coord (f : Module.Dual R M) :
    (∑ x, f (b x) • b.coord x) = f := by
  ext m
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_comm (f _), ← smul_eq_mul, ←
    f.map_smul, ← _root_.map_sum, Basis.coord_apply, Basis.sum_repr]

end

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι]
variable (b : Basis ι R M)

section Finite

variable [Finite ι]

/-- A vector space is linearly equivalent to its dual space. -/
def toDualEquiv : M ≃ₗ[R] Dual R M :=
  .ofBijective b.toDual ⟨ker_eq_bot.mp b.toDual_ker, range_eq_top.mp b.toDual_range⟩

-- `simps` times out when generating this
@[simp]
theorem toDualEquiv_apply (m : M) : b.toDualEquiv m = b.toDual m :=
  rfl

-- Not sure whether this is true for free modules over a commutative ring
/-- A vector space over a field is isomorphic to its dual if and only if it is finite-dimensional:
  a consequence of the Erdős-Kaplansky theorem. -/
theorem linearEquiv_dual_iff_finiteDimensional [Field K] [AddCommGroup V] [Module K V] :
    Nonempty (V ≃ₗ[K] Dual K V) ↔ FiniteDimensional K V := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun h ↦ ⟨(Module.Free.chooseBasis K V).toDualEquiv⟩⟩
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  by_contra!
  apply (lift_rank_lt_rank_dual this).ne
  have := e.lift_rank_eq
  rwa [lift_umax.{uV,uK}, lift_id'.{uV,uK}] at this

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

@[deprecated (since := "2024-08-29")] alias total_dualBasis := linearCombination_dualBasis

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

theorem eval_ker {ι : Type*} (b : Basis ι R M) :
    LinearMap.ker (Dual.eval R M) = ⊥ := by
  rw [ker_eq_bot']
  intro m hm
  simp_rw [LinearMap.ext_iff, Dual.eval_apply, zero_apply] at hm
  exact (Basis.forall_coord_eq_zero_iff _).mp fun i => hm (b.coord i)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
theorem eval_range {ι : Type*} [Finite ι] (b : Basis ι R M) :
    LinearMap.range (Dual.eval R M) = ⊤ := by
  classical
    cases nonempty_fintype ι
    rw [← b.toDual_toDual, range_comp, b.toDual_range, Submodule.map_top, toDual_range _]

section

variable [Module.Finite R M]

instance dual_free [Free R M] : Free R (Dual R M) :=
  Free.of_basis (Free.chooseBasis R M).dualBasis

instance dual_projective [Projective R M] : Projective R (Dual R M) :=
  have ⟨_, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  .of_split f.dualMap g.dualMap (congr_arg dualMap hfg)

instance dual_finite [Projective R M] : Module.Finite R (Dual R M) :=
  have ⟨n, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  have := Finite.of_basis (Free.chooseBasis R <| Fin n → R).dualBasis
  .of_surjective _ (surjective_of_comp_eq_id f.dualMap g.dualMap <| congr_arg dualMap hfg)

end

end CommRing

/-- `simp` normal form version of `linearCombination_dualBasis` -/
@[simp]
theorem linearCombination_coord [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
    (b : Basis ι R M) (f : ι →₀ R) (i : ι) : Finsupp.linearCombination R b.coord f (b i) = f i := by
  haveI := Classical.decEq ι
  rw [← coe_dualBasis, linearCombination_dualBasis]

@[deprecated (since := "2024-08-29")] alias total_coord := linearCombination_coord

theorem dual_rank_eq [CommRing K] [AddCommGroup V] [Module K V] [Finite ι] (b : Basis ι K V) :
    Cardinal.lift.{uK,uV} (Module.rank K V) = Module.rank K (Dual K V) := by
  classical rw [← lift_umax.{uV,uK}, b.toDualEquiv.lift_rank_eq, lift_id'.{uV,uK}]

end Basis

namespace Module

universe uK uV
variable {K : Type uK} {V : Type uV}
variable [CommRing K] [AddCommGroup V] [Module K V] [Projective K V]

open Module Module.Dual Submodule LinearMap Cardinal Basis Module

section

variable (K) (V)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.ker
theorem eval_ker : LinearMap.ker (eval K V) = ⊥ :=
  have ⟨s, hs⟩ := Module.projective_def'.mp ‹Projective K V›
  ker_eq_bot.mpr <| .of_comp (f := s.dualMap.dualMap) <| (ker_eq_bot.mp <|
    Finsupp.basisSingleOne (R := K).eval_ker).comp (injective_of_comp_eq_id s _ hs)

theorem map_eval_injective : (Submodule.map (eval K V)).Injective := by
  apply Submodule.map_injective_of_injective
  rw [← LinearMap.ker_eq_bot]
  exact eval_ker K V

theorem comap_eval_surjective : (Submodule.comap (eval K V)).Surjective := by
  apply Submodule.comap_surjective_of_injective
  rw [← LinearMap.ker_eq_bot]
  exact eval_ker K V

end

section

variable (K)

theorem eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0 := by
  simpa only using SetLike.ext_iff.mp (eval_ker K V) v

theorem eval_apply_injective : Function.Injective (eval K V) :=
  (injective_iff_map_eq_zero' (eval K V)).mpr (eval_apply_eq_zero_iff K)

theorem forall_dual_apply_eq_zero_iff (v : V) : (∀ φ : Module.Dual K V, φ v = 0) ↔ v = 0 := by
  rw [← eval_apply_eq_zero_iff K v, LinearMap.ext_iff]
  rfl

@[simp]
theorem subsingleton_dual_iff :
    Subsingleton (Dual K V) ↔ Subsingleton V := by
  refine ⟨fun h ↦ ⟨fun v w ↦ ?_⟩, fun _ ↦ inferInstance⟩
  rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff K (v - w)]
  intros f
  simp [Subsingleton.elim f 0]

@[simp]
theorem nontrivial_dual_iff :
    Nontrivial (Dual K V) ↔ Nontrivial V := by
  rw [← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton,
    subsingleton_dual_iff]

instance instNontrivialDual [Nontrivial V] : Nontrivial (Dual K V) :=
  (nontrivial_dual_iff K).mpr inferInstance

omit [Projective K V] in
theorem finite_dual_iff [Free K V] : Module.Finite K (Dual K V) ↔ Module.Finite K V := by
  constructor <;> intro h
  · obtain ⟨⟨ι, b⟩⟩ := Free.exists_basis (R := K) (M := V)
    nontriviality K
    obtain ⟨⟨s, span_s⟩⟩ := h
    classical
    haveI := (b.linearIndependent.map' _ b.toDual_ker).finite_of_le_span_finite _ s ?_
    · exact Finite.of_basis b
    · rw [span_s]; apply le_top
  · infer_instance

end

omit [Projective K V]

theorem dual_rank_eq [Free K V] [Module.Finite K V] :
    Cardinal.lift.{uK,uV} (Module.rank K V) = Module.rank K (Dual K V) :=
  (Module.Free.chooseBasis K V).dual_rank_eq

section IsReflexive

open Function

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- A reflexive module is one for which the natural map to its double dual is a bijection.

Any finitely-generated projective module (and thus any finite-dimensional vector space)
is reflexive. See `Module.instIsReflexiveOfFiniteOfProjective`. -/
class IsReflexive : Prop where
  /-- A reflexive module is one for which the natural map to its double dual is a bijection. -/
  bijective_dual_eval' : Bijective (Dual.eval R M)

lemma bijective_dual_eval [IsReflexive R M] : Bijective (Dual.eval R M) :=
  IsReflexive.bijective_dual_eval'

/-- See also `Module.instFiniteDimensionalOfIsReflexive` for the converse over a field. -/
instance (priority := 900) IsReflexive.of_finite_of_free [Module.Finite R M] [Free R M] :
    IsReflexive R M where
  bijective_dual_eval'.left := ker_eq_bot.mp (Free.chooseBasis R M).eval_ker
  bijective_dual_eval'.right := range_eq_top.mp (Free.chooseBasis R M).eval_range

variable [IsReflexive R M]

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
theorem erange_coe : LinearMap.range (eval R M) = ⊤ :=
  range_eq_top.mpr (bijective_dual_eval _ _).2

/-- The bijection between a reflexive module and its double dual, bundled as a `LinearEquiv`. -/
def evalEquiv : M ≃ₗ[R] Dual R (Dual R M) :=
  LinearEquiv.ofBijective _ (bijective_dual_eval R M)

@[simp] lemma evalEquiv_toLinearMap : evalEquiv R M = Dual.eval R M := rfl

@[simp] lemma evalEquiv_apply (m : M) : evalEquiv R M m = Dual.eval R M m := rfl

@[simp] lemma apply_evalEquiv_symm_apply (f : Dual R M) (g : Dual R (Dual R M)) :
    f ((evalEquiv R M).symm g) = g f := by
  set m := (evalEquiv R M).symm g
  rw [← (evalEquiv R M).apply_symm_apply g, evalEquiv_apply, Dual.eval_apply]

@[simp] lemma symm_dualMap_evalEquiv :
    (evalEquiv R M).symm.dualMap = Dual.eval R (Dual R M) := by
  ext; simp

@[simp] lemma Dual.eval_comp_comp_evalEquiv_eq
    {M' : Type*} [AddCommGroup M'] [Module R M'] {f : M →ₗ[R] M'} :
    Dual.eval R M' ∘ₗ f ∘ₗ (evalEquiv R M).symm = f.dualMap.dualMap := by
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq,
    evalEquiv_toLinearMap, eval_naturality]

lemma dualMap_dualMap_eq_iff_of_injective
    {M' : Type*} [AddCommGroup M'] [Module R M'] {f g : M →ₗ[R] M'}
    (h : Injective (Dual.eval R M')) :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g := by
  simp only [← Dual.eval_comp_comp_evalEquiv_eq]
  refine ⟨fun hfg => ?_, fun a ↦ congrArg (Dual.eval R M').comp
    (congrFun (congrArg LinearMap.comp a) (evalEquiv R M).symm.toLinearMap)⟩
  rw [propext (cancel_left h), LinearEquiv.eq_comp_toLinearMap_iff] at hfg
  exact hfg

@[simp] lemma dualMap_dualMap_eq_iff
    {M' : Type*} [AddCommGroup M'] [Module R M'] [IsReflexive R M'] {f g : M →ₗ[R] M'} :
    f.dualMap.dualMap = g.dualMap.dualMap ↔ f = g :=
  dualMap_dualMap_eq_iff_of_injective _ _ (bijective_dual_eval R M').injective

/-- The dual of a reflexive module is reflexive. -/
instance Dual.instIsReflecive : IsReflexive R (Dual R M) :=
  ⟨by simpa only [← symm_dualMap_evalEquiv] using (evalEquiv R M).dualMap.symm.bijective⟩

variable {R M N} in
/-- A direct summand of a reflexive module is reflexive. -/
lemma IsReflexive.of_split (i : N →ₗ[R] M) (s : M →ₗ[R] N) (H : s ∘ₗ i = .id) :
    IsReflexive R N where
  bijective_dual_eval' :=
    ⟨.of_comp (f := i.dualMap.dualMap) <|
      (bijective_dual_eval R M).1.comp (injective_of_comp_eq_id i _ H),
    .of_comp (g := s) <| (surjective_of_comp_eq_id i.dualMap.dualMap s.dualMap.dualMap <|
      congr_arg (dualMap ∘ dualMap) H).comp (bijective_dual_eval R M).2⟩

instance (priority := 900) [Module.Finite R N] [Projective R N] : IsReflexive R N :=
  have ⟨_, f, hf⟩ := Finite.exists_fin' R N
  have ⟨g, H⟩ := projective_lifting_property f .id hf
  .of_split g f H

/-- The isomorphism `Module.evalEquiv` induces an order isomorphism on subspaces. -/
def mapEvalEquiv : Submodule R M ≃o Submodule R (Dual R (Dual R M)) :=
  Submodule.orderIsoMapComap (evalEquiv R M)

@[simp]
theorem mapEvalEquiv_apply (W : Submodule R M) :
    mapEvalEquiv R M W = W.map (Dual.eval R M) :=
  rfl

@[simp]
theorem mapEvalEquiv_symm_apply (W'' : Submodule R (Dual R (Dual R M))) :
    (mapEvalEquiv R M).symm W'' = W''.comap (Dual.eval R M) :=
  rfl

instance _root_.Prod.instModuleIsReflexive [IsReflexive R N] :
    IsReflexive R (M × N) where
  bijective_dual_eval' := by
    let e : Dual R (Dual R (M × N)) ≃ₗ[R] Dual R (Dual R M) × Dual R (Dual R N) :=
      (dualProdDualEquivDual R M N).dualMap.trans
        (dualProdDualEquivDual R (Dual R M) (Dual R N)).symm
    have : Dual.eval R (M × N) = e.symm.comp ((Dual.eval R M).prodMap (Dual.eval R N)) := by
      ext m f <;> simp [e]
    simp only [this, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.dualMap_symm,
      coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    exact (bijective_dual_eval R M).prodMap (bijective_dual_eval R N)

variable {R M N} in
lemma equiv (e : M ≃ₗ[R] N) : IsReflexive R N where
  bijective_dual_eval' := by
    let ed : Dual R (Dual R N) ≃ₗ[R] Dual R (Dual R M) := e.symm.dualMap.dualMap
    have : Dual.eval R N = ed.symm.comp ((Dual.eval R M).comp e.symm.toLinearMap) := by
      ext m f
      exact DFunLike.congr_arg f (e.apply_symm_apply m).symm
    simp only [this, LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.dualMap_symm,
      coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    exact Bijective.comp (bijective_dual_eval R M) (LinearEquiv.bijective _)

instance _root_.MulOpposite.instModuleIsReflexive : IsReflexive R (MulOpposite M) :=
  equiv <| MulOpposite.opLinearEquiv _

instance _root_.ULift.instModuleIsReflexive.{w} : IsReflexive R (ULift.{w} M) :=
  equiv ULift.moduleEquiv.symm

instance instFiniteDimensionalOfIsReflexive (K V : Type*)
    [Field K] [AddCommGroup V] [Module K V] [IsReflexive K V] :
    FiniteDimensional K V := by
  rw [FiniteDimensional, ← rank_lt_aleph0_iff]
  by_contra! contra
  suffices lift (Module.rank K V) < Module.rank K (Dual K (Dual K V)) by
    have heq := lift_rank_eq_of_equiv_equiv (R := K) (R' := K) (M := V) (M' := Dual K (Dual K V))
      (ZeroHom.id K) (evalEquiv K V) bijective_id (fun r v ↦ (evalEquiv K V).map_smul _ _)
    rw [← lift_umax, heq, lift_id'] at this
    exact lt_irrefl _ this
  have h₁ : lift (Module.rank K V) < Module.rank K (Dual K V) := lift_rank_lt_rank_dual contra
  have h₂ : Module.rank K (Dual K V) < Module.rank K (Dual K (Dual K V)) := by
    convert lift_rank_lt_rank_dual <| le_trans (by simpa) h₁.le
    rw [lift_id']
  exact lt_trans h₁ h₂

instance [IsDomain R] : NoZeroSMulDivisors R M := by
  refine (noZeroSMulDivisors_iff R M).mpr ?_
  intro r m hrm
  rw [or_iff_not_imp_left]
  intro hr
  suffices Dual.eval R M m = Dual.eval R M 0 from (bijective_dual_eval R M).injective this
  ext n
  simp only [Dual.eval_apply, map_zero, LinearMap.zero_apply]
  suffices r • n m = 0 from eq_zero_of_ne_zero_of_mul_left_eq_zero hr this
  rw [← LinearMap.map_smul_of_tower, hrm, LinearMap.map_zero]

end IsReflexive

end Module

namespace Submodule

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Submodule R M}

theorem exists_dual_map_eq_bot_of_nmem {x : M} (hx : x ∉ p) (hp' : Free R (M ⧸ p)) :
    ∃ f : Dual R M, f x ≠ 0 ∧ p.map f = ⊥ := by
  suffices ∃ f : Dual R (M ⧸ p), f (p.mkQ x) ≠ 0 by
    obtain ⟨f, hf⟩ := this; exact ⟨f.comp p.mkQ, hf, by simp [Submodule.map_comp]⟩
  rwa [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply,
    ← forall_dual_apply_eq_zero_iff (K := R), not_forall] at hx

theorem exists_dual_map_eq_bot_of_lt_top (hp : p < ⊤) (hp' : Free R (M ⧸ p)) :
    ∃ f : Dual R M, f ≠ 0 ∧ p.map f = ⊥ := by
  obtain ⟨x, hx⟩ : ∃ x : M, x ∉ p := by rw [lt_top_iff_ne_top] at hp; contrapose! hp; ext; simp [hp]
  obtain ⟨f, hf, hf'⟩ := p.exists_dual_map_eq_bot_of_nmem hx hp'
  exact ⟨f, by aesop, hf'⟩

/-- Consider a reflexive module and a set `s` of linear forms. If for any `z ≠ 0` there exists
`f ∈ s` such that `f z ≠ 0`, then `s` spans the whole dual space. -/
theorem span_eq_top_of_ne_zero [IsReflexive R M]
    {s : Set (M →ₗ[R] R)} [Free R ((M →ₗ[R] R) ⧸ (span R s))]
    (h : ∀ z ≠ 0, ∃ f ∈ s, f z ≠ 0) : span R s = ⊤ := by
  by_contra! hn
  obtain ⟨φ, φne, hφ⟩ := exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance
  let φs := (evalEquiv R M).symm φ
  have this f (hf : f ∈ s) : f φs = 0 := by
    rw [← mem_bot R, ← hφ, mem_map]
    exact ⟨f, subset_span hf, (apply_evalEquiv_symm_apply R M f φ).symm⟩
  obtain ⟨x, xs, hx⟩ := h φs (by simp [φne, φs])
  exact hx <| this x xs

variable {ι 𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

open LinearMap Set FiniteDimensional

theorem _root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker [FiniteDimensional 𝕜 E]
    {L : ι → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, LinearMap.ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  by_contra hK
  rcases exists_dual_map_eq_bot_of_nmem hK inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv 𝕜 E).symm φ
  have : K φs = 0 := by
    refine h <| (Submodule.mem_iInf _).2 fun i ↦ (mem_bot 𝕜).1 ?_
    rw [← hφ, Submodule.mem_map]
    exact ⟨L i, Submodule.subset_span ⟨i, rfl⟩, (apply_evalEquiv_symm_apply 𝕜 E _ φ).symm⟩
  simp only [apply_evalEquiv_symm_apply, φs, φne] at this

/-- Given some linear forms $L_1, ..., L_n, K$ over a vector space $E$, if
$\bigcap_{i=1}^n \mathrm{ker}(L_i) \subseteq \mathrm{ker}(K)$, then $K$ is in the space generated
by $L_1, ..., L_n$. -/
theorem _root_.mem_span_of_iInf_ker_le_ker [Finite ι] {L : ι → E →ₗ[𝕜] 𝕜} {K : E →ₗ[𝕜] 𝕜}
    (h : ⨅ i, ker (L i) ≤ ker K) : K ∈ span 𝕜 (range L) := by
  have _ := Fintype.ofFinite ι
  let φ : E →ₗ[𝕜] ι → 𝕜 := LinearMap.pi L
  let p := ⨅ i, ker (L i)
  have p_eq : p = ker φ := (ker_pi L).symm
  let ψ : (E ⧸ p) →ₗ[𝕜] ι → 𝕜 := p.liftQ φ p_eq.le
  have _ : FiniteDimensional 𝕜 (E ⧸ p) := of_injective ψ (ker_eq_bot.1 (ker_liftQ_eq_bot' p φ p_eq))
  let L' i : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ (L i) (iInf_le _ i)
  let K' : (E ⧸ p) →ₗ[𝕜] 𝕜 := p.liftQ K h
  have : ⨅ i, ker (L' i) ≤ ker K' := by
    simp_rw +zetaDelta [← ker_pi, pi_liftQ_eq_liftQ_pi, ker_liftQ_eq_bot' p φ p_eq]
    exact bot_le
  obtain ⟨c, hK'⟩ :=
    (mem_span_range_iff_exists_fun 𝕜).1 (FiniteDimensional.mem_span_of_iInf_ker_le_ker this)
  refine (mem_span_range_iff_exists_fun 𝕜).2 ⟨c, ?_⟩
  conv_lhs => enter [2]; intro i; rw [← p.liftQ_mkQ (L i) (iInf_le _ i)]
  rw [← p.liftQ_mkQ K h]
  ext x
  convert LinearMap.congr_fun hK' (p.mkQ x)
  simp only [L',coeFn_sum, Finset.sum_apply, smul_apply, coe_comp, Function.comp_apply,
    smul_eq_mul]

end Submodule

section DualBases

open Module

variable {R M ι : Type*}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

-- Porting note: replace use_finite_instance tactic
open Lean.Elab.Tactic in
/-- Try using `Set.toFinite` to dispatch a `Set.Finite` goal. -/
def evalUseFiniteInstance : TacticM Unit := do
  evalTactic (← `(tactic| intros; apply Set.toFinite))

elab "use_finite_instance" : tactic => evalUseFiniteInstance

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
structure Module.DualBases (e : ι → M) (ε : ι → Dual R M) : Prop where
  eval_same : ∀ i, ε i (e i) = 1
  eval_of_ne : Pairwise fun i j ↦ ε i (e j) = 0
  protected total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0
  protected finite : ∀ m : M, {i | ε i m ≠ 0}.Finite := by use_finite_instance

end DualBases

namespace Module.DualBases

open Module Module.Dual LinearMap Function

variable {R M ι : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M]
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
  rw [lc, _root_.map_finsupp_sum, Finsupp.sum_eq_single i (g := fun a b ↦ (ε i) (b • e a))]
  -- Porting note: cannot get at •
  -- simp only [h.eval, map_smul, smul_eq_mul]
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
theorem lc_coeffs (m : M) : DualBases.lc e (h.coeffs m) = m := by
  refine eq_of_sub_eq_zero <| h.total fun i ↦ ?_
  simp [LinearMap.map_sub, h.dual_lc, sub_eq_zero]

/-- `(h : DualBases e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps repr_apply, simps (config := .lemmasOnly) repr_symm_apply]
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

theorem coe_dualBasis [DecidableEq ι] [_root_.Finite ι] : ⇑h.basis.dualBasis = ε :=
  funext fun i => h.basis.ext fun j => by simp

end Module.DualBases

namespace Submodule

universe u v w

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {W : Submodule R M}

/-- The `dualRestrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dualRestrict (W : Submodule R M) : Module.Dual R M →ₗ[R] Module.Dual R W :=
  LinearMap.domRestrict' W

theorem dualRestrict_def (W : Submodule R M) : W.dualRestrict = W.subtype.dualMap :=
  rfl

@[simp]
theorem dualRestrict_apply (W : Submodule R M) (φ : Module.Dual R M) (x : W) :
    W.dualRestrict φ x = φ (x : M) :=
  rfl

/-- The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dualAnnihilator {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (W : Submodule R M) : Submodule R <| Module.Dual R M :=
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.ker
  LinearMap.ker W.dualRestrict

@[simp]
theorem mem_dualAnnihilator (φ : Module.Dual R M) : φ ∈ W.dualAnnihilator ↔ ∀ w ∈ W, φ w = 0 := by
  refine LinearMap.mem_ker.trans ?_
  simp_rw [LinearMap.ext_iff, dualRestrict_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

/-- That $\operatorname{ker}(\iota^* : V^* \to W^*) = \operatorname{ann}(W)$.
This is the definition of the dual annihilator of the submodule $W$. -/
theorem dualRestrict_ker_eq_dualAnnihilator (W : Submodule R M) :
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.ker
    LinearMap.ker W.dualRestrict = W.dualAnnihilator :=
  rfl

/-- The `dualAnnihilator` of a submodule of the dual space pulled back along the evaluation map
`Module.Dual.eval`. -/
def dualCoannihilator (Φ : Submodule R (Module.Dual R M)) : Submodule R M :=
  Φ.dualAnnihilator.comap (Module.Dual.eval R M)

@[simp]
theorem mem_dualCoannihilator {Φ : Submodule R (Module.Dual R M)} (x : M) :
    x ∈ Φ.dualCoannihilator ↔ ∀ φ ∈ Φ, (φ x : R) = 0 := by
  simp_rw [dualCoannihilator, mem_comap, mem_dualAnnihilator, Module.Dual.eval_apply]

theorem comap_dualAnnihilator (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualAnnihilator.comap (Module.Dual.eval R M) = Φ.dualCoannihilator := rfl

theorem map_dualCoannihilator_le (Φ : Submodule R (Module.Dual R M)) :
    Φ.dualCoannihilator.map (Module.Dual.eval R M) ≤ Φ.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator Φ).le

variable (R M) in
theorem dualAnnihilator_gc :
    GaloisConnection
      (OrderDual.toDual ∘ (dualAnnihilator : Submodule R M → Submodule R (Module.Dual R M)))
      (dualCoannihilator ∘ OrderDual.ofDual) := by
  intro a b
  induction b using OrderDual.rec
  simp only [Function.comp_apply, OrderDual.toDual_le_toDual, OrderDual.ofDual_toDual]
  constructor <;>
    · intro h x hx
      simp only [mem_dualAnnihilator, mem_dualCoannihilator]
      intro y hy
      have := h hy
      simp only [mem_dualAnnihilator, mem_dualCoannihilator] at this
      exact this x hx

theorem le_dualAnnihilator_iff_le_dualCoannihilator {U : Submodule R (Module.Dual R M)}
    {V : Submodule R M} : U ≤ V.dualAnnihilator ↔ V ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_iff_le

@[simp]
theorem dualAnnihilator_bot : (⊥ : Submodule R M).dualAnnihilator = ⊤ :=
  (dualAnnihilator_gc R M).l_bot

@[simp]
theorem dualAnnihilator_top : (⊤ : Submodule R M).dualAnnihilator = ⊥ := by
  rw [eq_bot_iff]
  intro v
  simp_rw [mem_dualAnnihilator, mem_bot, mem_top, forall_true_left]
  exact fun h => LinearMap.ext h

@[simp]
theorem dualCoannihilator_bot : (⊥ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊤ :=
  (dualAnnihilator_gc R M).u_top

@[mono]
theorem dualAnnihilator_anti {U V : Submodule R M} (hUV : U ≤ V) :
    V.dualAnnihilator ≤ U.dualAnnihilator :=
  (dualAnnihilator_gc R M).monotone_l hUV

@[mono]
theorem dualCoannihilator_anti {U V : Submodule R (Module.Dual R M)} (hUV : U ≤ V) :
    V.dualCoannihilator ≤ U.dualCoannihilator :=
  (dualAnnihilator_gc R M).monotone_u hUV

theorem le_dualAnnihilator_dualCoannihilator (U : Submodule R M) :
    U ≤ U.dualAnnihilator.dualCoannihilator :=
  (dualAnnihilator_gc R M).le_u_l U

theorem le_dualCoannihilator_dualAnnihilator (U : Submodule R (Module.Dual R M)) :
    U ≤ U.dualCoannihilator.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_le U

theorem dualAnnihilator_dualCoannihilator_dualAnnihilator (U : Submodule R M) :
    U.dualAnnihilator.dualCoannihilator.dualAnnihilator = U.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_u_l_eq_l U

theorem dualCoannihilator_dualAnnihilator_dualCoannihilator (U : Submodule R (Module.Dual R M)) :
    U.dualCoannihilator.dualAnnihilator.dualCoannihilator = U.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_l_u_eq_u U

theorem dualAnnihilator_sup_eq (U V : Submodule R M) :
    (U ⊔ V).dualAnnihilator = U.dualAnnihilator ⊓ V.dualAnnihilator :=
  (dualAnnihilator_gc R M).l_sup

theorem dualCoannihilator_sup_eq (U V : Submodule R (Module.Dual R M)) :
    (U ⊔ V).dualCoannihilator = U.dualCoannihilator ⊓ V.dualCoannihilator :=
  (dualAnnihilator_gc R M).u_inf

theorem dualAnnihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R M) :
    (⨆ i : ι, U i).dualAnnihilator = ⨅ i : ι, (U i).dualAnnihilator :=
  (dualAnnihilator_gc R M).l_iSup

theorem dualCoannihilator_iSup_eq {ι : Sort*} (U : ι → Submodule R (Module.Dual R M)) :
    (⨆ i : ι, U i).dualCoannihilator = ⨅ i : ι, (U i).dualCoannihilator :=
  (dualAnnihilator_gc R M).u_iInf

/-- See also `Subspace.dualAnnihilator_inf_eq` for vector subspaces. -/
theorem sup_dualAnnihilator_le_inf (U V : Submodule R M) :
    U.dualAnnihilator ⊔ V.dualAnnihilator ≤ (U ⊓ V).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_sup_eq]
  apply inf_le_inf <;> exact le_dualAnnihilator_dualCoannihilator _

/-- See also `Subspace.dualAnnihilator_iInf_eq` for vector subspaces when `ι` is finite. -/
theorem iSup_dualAnnihilator_le_iInf {ι : Sort*} (U : ι → Submodule R M) :
    ⨆ i : ι, (U i).dualAnnihilator ≤ (⨅ i : ι, U i).dualAnnihilator := by
  rw [le_dualAnnihilator_iff_le_dualCoannihilator, dualCoannihilator_iSup_eq]
  apply iInf_mono
  exact fun i : ι => le_dualAnnihilator_dualCoannihilator (U i)

@[simp]
lemma coe_dualAnnihilator_span (s : Set M) :
    ((span R s).dualAnnihilator : Set (Module.Dual R M)) = {f | s ⊆ LinearMap.ker f} := by
  ext f
  simp only [SetLike.mem_coe, mem_dualAnnihilator, Set.mem_setOf_eq, ← LinearMap.mem_ker]
  exact span_le

@[simp]
lemma coe_dualCoannihilator_span (s : Set (Module.Dual R M)) :
    ((span R s).dualCoannihilator : Set M) = {x | ∀ f ∈ s, f x = 0} := by
  ext x
  have (φ) : x ∈ LinearMap.ker φ ↔ φ ∈ LinearMap.ker (Module.Dual.eval R M x) := by simp
  simp only [SetLike.mem_coe, mem_dualCoannihilator, Set.mem_setOf_eq, ← LinearMap.mem_ker, this]
  exact span_le

end Submodule

namespace Subspace

open Submodule LinearMap

universe u v w

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

@[simp]
theorem dualCoannihilator_top (W : Subspace K V) :
    (⊤ : Subspace K (Module.Dual K W)).dualCoannihilator = ⊥ := by
  rw [dualCoannihilator, dualAnnihilator_top, comap_bot, Module.eval_ker]

@[simp]
theorem dualAnnihilator_dualCoannihilator_eq {W : Subspace K V} :
    W.dualAnnihilator.dualCoannihilator = W := by
  refine le_antisymm (fun v ↦ Function.mtr ?_) (le_dualAnnihilator_dualCoannihilator _)
  simp only [mem_dualAnnihilator, mem_dualCoannihilator]
  rw [← Quotient.mk_eq_zero W, ← Module.forall_dual_apply_eq_zero_iff K]
  push_neg
  refine fun ⟨φ, hφ⟩ ↦ ⟨φ.comp W.mkQ, fun w hw ↦ ?_, hφ⟩
  rw [comp_apply, mkQ_apply, (Quotient.mk_eq_zero W).mpr hw, φ.map_zero]

-- exact elaborates slowly
theorem forall_mem_dualAnnihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) :
    (∀ φ : Module.Dual K V, φ ∈ W.dualAnnihilator → φ v = 0) ↔ v ∈ W := by
  rw [← SetLike.ext_iff.mp dualAnnihilator_dualCoannihilator_eq v, mem_dualCoannihilator]

theorem comap_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator.comap (Module.Dual.eval K V) = W := by
  ext; rw [Iff.comm, ← forall_mem_dualAnnihilator_apply_eq_zero_iff]; simp

theorem map_le_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.map (Module.Dual.eval K V) ≤ W.dualAnnihilator.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator_dualAnnihilator W).ge

/-- `Submodule.dualAnnihilator` and `Submodule.dualCoannihilator` form a Galois coinsertion. -/
def dualAnnihilatorGci (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    GaloisCoinsertion
      (OrderDual.toDual ∘ (dualAnnihilator : Subspace K V → Subspace K (Module.Dual K V)))
      (dualCoannihilator ∘ OrderDual.ofDual) where
  choice W _ := dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl

theorem dualAnnihilator_le_dualAnnihilator_iff {W W' : Subspace K V} :
    W.dualAnnihilator ≤ W'.dualAnnihilator ↔ W' ≤ W :=
  (dualAnnihilatorGci K V).l_le_l_iff

theorem dualAnnihilator_inj {W W' : Subspace K V} :
    W.dualAnnihilator = W'.dualAnnihilator ↔ W = W' :=
  ⟨fun h ↦ (dualAnnihilatorGci K V).l_injective h, congr_arg _⟩

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dualLift W φ` is
an arbitrary extension of `φ` to an element of the dual of `V`.
That is, `dualLift W φ` sends `w ∈ W` to `φ x` and `x` in a chosen complement of `W` to `0`. -/
noncomputable def dualLift (W : Subspace K V) : Module.Dual K W →ₗ[K] Module.Dual K V :=
  (Classical.choose <| W.subtype.exists_leftInverse_of_injective W.ker_subtype).dualMap

variable {W : Subspace K V}

@[simp]
theorem dualLift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) = φ w :=
  congr_arg φ <| DFunLike.congr_fun
    (Classical.choose_spec <| W.subtype.exists_leftInverse_of_injective W.ker_subtype) w

theorem dualLift_of_mem {φ : Module.Dual K W} {w : V} (hw : w ∈ W) : W.dualLift φ w = φ ⟨w, hw⟩ :=
  dualLift_of_subtype ⟨w, hw⟩

@[simp]
theorem dualRestrict_comp_dualLift (W : Subspace K V) : W.dualRestrict.comp W.dualLift = 1 := by
  ext φ x
  simp

theorem dualRestrict_leftInverse (W : Subspace K V) :
    Function.LeftInverse W.dualRestrict W.dualLift := fun x =>
  show W.dualRestrict.comp W.dualLift x = x by
    rw [dualRestrict_comp_dualLift]
    rfl

theorem dualLift_rightInverse (W : Subspace K V) :
    Function.RightInverse W.dualLift W.dualRestrict :=
  W.dualRestrict_leftInverse

theorem dualRestrict_surjective : Function.Surjective W.dualRestrict :=
  W.dualLift_rightInverse.surjective

theorem dualLift_injective : Function.Injective W.dualLift :=
  W.dualRestrict_leftInverse.injective

/-- The quotient by the `dualAnnihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
  (quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans <|
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective

@[simp]
theorem quotAnnihilatorEquiv_apply (W : Subspace K V) (φ : Module.Dual K V) :
    W.quotAnnihilatorEquiv (Submodule.Quotient.mk φ) = W.dualRestrict φ := by
  ext
  rfl

/-- The natural isomorphism from the dual of a subspace `W` to `W.dualLift.range`. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
noncomputable def dualEquivDual (W : Subspace K V) :
    Module.Dual K W ≃ₗ[K] LinearMap.range W.dualLift :=
  LinearEquiv.ofInjective _ dualLift_injective

theorem dualEquivDual_def (W : Subspace K V) :
    W.dualEquivDual.toLinearMap = W.dualLift.rangeRestrict :=
  rfl

@[simp]
theorem dualEquivDual_apply (φ : Module.Dual K W) :
    W.dualEquivDual φ = ⟨W.dualLift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl

section

open FiniteDimensional Module

instance instModuleDualFiniteDimensional [FiniteDimensional K V] :
    FiniteDimensional K (Module.Dual K V) := by
  infer_instance

@[simp]
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V := by
  by_cases h : FiniteDimensional K V
  · classical exact LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
  rw [finrank_eq_zero_of_basis_imp_false, finrank_eq_zero_of_basis_imp_false]
  · exact fun _ b ↦ h (Module.Finite.of_basis b)
  · exact fun _ b ↦ h ((Module.finite_dual_iff K).mp <| Module.Finite.of_basis b)

variable [FiniteDimensional K V]

theorem dualAnnihilator_dualAnnihilator_eq (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator = Module.mapEvalEquiv K V W := by
  have : _ = W := Subspace.dualAnnihilator_dualCoannihilator_eq
  rw [dualCoannihilator, ← Module.mapEvalEquiv_symm_apply] at this
  rwa [← OrderIso.symm_apply_eq]

/-- The quotient by the dual is isomorphic to its dual annihilator. -/
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
noncomputable def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ LinearMap.range W.dualLift) ≃ₗ[K] W.dualAnnihilator :=
  LinearEquiv.quotEquivOfQuotEquiv <| LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual

open scoped Classical in
/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator :=
  let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator
  -- Porting note: this prevents the timeout; ML3 proof preserved below
  -- refine' _ ≪≫ₗ W.quotDualEquivAnnihilator
  -- refine' LinearEquiv.quot_equiv_of_equiv _ (Basis.ofVectorSpace K V).toDualEquiv
  -- exact (Basis.ofVectorSpace K W).toDualEquiv.trans W.dual_equiv_dual

open Module

theorem finrank_add_finrank_dualAnnihilator_eq (W : Subspace K V) :
    finrank K W + finrank K W.dualAnnihilator = finrank K V := by
  rw [← W.quotEquivAnnihilator.finrank_eq (M₂ := dualAnnihilator W),
    add_comm, Submodule.finrank_quotient_add_finrank]

@[simp]
theorem finrank_dualCoannihilator_eq {Φ : Subspace K (Module.Dual K V)} :
    finrank K Φ.dualCoannihilator = finrank K Φ.dualAnnihilator := by
  rw [Submodule.dualCoannihilator, ← Module.evalEquiv_toLinearMap]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)

theorem finrank_add_finrank_dualCoannihilator_eq (W : Subspace K (Module.Dual K V)) :
    finrank K W + finrank K W.dualCoannihilator = finrank K V := by
  rw [finrank_dualCoannihilator_eq, finrank_add_finrank_dualAnnihilator_eq, dual_finrank_eq]

end

end Subspace

open Module

namespace LinearMap

universe uR uM₁ uM₂
variable {R : Type uR} [CommSemiring R] {M₁ : Type uM₁} {M₂ : Type uM₂}
variable [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
variable (f : M₁ →ₗ[R] M₂)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.ker
theorem ker_dualMap_eq_dualAnnihilator_range :
    LinearMap.ker f.dualMap = f.range.dualAnnihilator := by
  ext
  simp_rw [mem_ker, LinearMap.ext_iff, Submodule.mem_dualAnnihilator,
    ← SetLike.mem_coe, range_coe, Set.forall_mem_range]
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
theorem range_dualMap_le_dualAnnihilator_ker :
    LinearMap.range f.dualMap ≤ f.ker.dualAnnihilator := by
  rintro _ ⟨ψ, rfl⟩
  simp_rw [Submodule.mem_dualAnnihilator, mem_ker]
  rintro x hx
  rw [dualMap_apply, hx, map_zero]

end LinearMap

section CommRing

variable {R M M' : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

namespace Submodule

/-- Given a submodule, corestrict to the pairing on `M ⧸ W` by
simultaneously restricting to `W.dualAnnihilator`.

See `Subspace.dualCopairing_nondegenerate`. -/
def dualCopairing (W : Submodule R M) : W.dualAnnihilator →ₗ[R] M ⧸ W →ₗ[R] R :=
  LinearMap.flip <|
    W.liftQ ((Module.dualPairing R M).domRestrict W.dualAnnihilator).flip
      (by
        intro w hw
        ext ⟨φ, hφ⟩
        exact (mem_dualAnnihilator φ).mp hφ w hw)

-- Porting note: helper instance
instance (W : Submodule R M) : FunLike (W.dualAnnihilator) M R where
  coe φ := φ.val
  coe_injective' φ ψ h := by
    ext
    simp only [funext_iff] at h
    exact h _

@[simp]
theorem dualCopairing_apply {W : Submodule R M} (φ : W.dualAnnihilator) (x : M) :
    W.dualCopairing φ (Quotient.mk x) = φ x :=
  rfl

/-- Given a submodule, restrict to the pairing on `W` by
simultaneously corestricting to `Module.Dual R M ⧸ W.dualAnnihilator`.
This is `Submodule.dualRestrict` factored through the quotient by its kernel (which
is `W.dualAnnihilator` by definition).

See `Subspace.dualPairing_nondegenerate`. -/
def dualPairing (W : Submodule R M) : Module.Dual R M ⧸ W.dualAnnihilator →ₗ[R] W →ₗ[R] R :=
  W.dualAnnihilator.liftQ W.dualRestrict le_rfl

@[simp]
theorem dualPairing_apply {W : Submodule R M} (φ : Module.Dual R M) (x : W) :
    W.dualPairing (Quotient.mk φ) x = φ x :=
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
/-- That $\operatorname{im}(q^* : (V/W)^* \to V^*) = \operatorname{ann}(W)$. -/
theorem range_dualMap_mkQ_eq (W : Submodule R M) :
    LinearMap.range W.mkQ.dualMap = W.dualAnnihilator := by
  ext φ
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩
    have := LinearMap.mem_range_self W.mkQ.dualMap ψ
    simpa only [ker_mkQ] using W.mkQ.range_dualMap_le_dualAnnihilator_ker this
  · intro hφ
    exists W.dualCopairing ⟨φ, hφ⟩

/-- Equivalence $(M/W)^* \cong \operatorname{ann}(W)$. That is, there is a one-to-one
correspondence between the dual of `M ⧸ W` and those elements of the dual of `M` that
vanish on `W`.

The inverse of this is `Submodule.dualCopairing`. -/
def dualQuotEquivDualAnnihilator (W : Submodule R M) :
    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=
  LinearEquiv.ofLinear
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.mem_range_self
      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)
    W.dualCopairing (by ext; rfl) (by ext; rfl)

@[simp]
theorem dualQuotEquivDualAnnihilator_apply (W : Submodule R M) (φ : Module.Dual R (M ⧸ W)) (x : M) :
    dualQuotEquivDualAnnihilator W φ x = φ (Quotient.mk x) :=
  rfl

theorem dualCopairing_eq (W : Submodule R M) :
    W.dualCopairing = (dualQuotEquivDualAnnihilator W).symm.toLinearMap :=
  rfl

@[simp]
theorem dualQuotEquivDualAnnihilator_symm_apply_mk (W : Submodule R M) (φ : W.dualAnnihilator)
    (x : M) : (dualQuotEquivDualAnnihilator W).symm φ (Quotient.mk x) = φ x :=
  rfl

theorem finite_dualAnnihilator_iff {W : Submodule R M} [Free R (M ⧸ W)] :
    Module.Finite R W.dualAnnihilator ↔ Module.Finite R (M ⧸ W) :=
  (Finite.equiv_iff W.dualQuotEquivDualAnnihilator.symm).trans (finite_dual_iff R)

open LinearMap in
/-- The pairing between a submodule `W` of a dual module `Dual R M` and the quotient of
`M` by the coannihilator of `W`, which is always nondegenerate. -/
def quotDualCoannihilatorToDual (W : Submodule R (Dual R M)) :
    M ⧸ W.dualCoannihilator →ₗ[R] Dual R W :=
  liftQ _ (flip <| Submodule.subtype _) le_rfl

@[simp]
theorem quotDualCoannihilatorToDual_apply (W : Submodule R (Dual R M)) (m : M) (w : W) :
    W.quotDualCoannihilatorToDual (Quotient.mk m) w = w.1 m := rfl

theorem quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual :=
  LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl)

theorem flip_quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual.flip :=
  fun _ _ he ↦ Subtype.ext <| LinearMap.ext fun m ↦ DFunLike.congr_fun he ⟦m⟧

open LinearMap in
theorem quotDualCoannihilatorToDual_nondegenerate (W : Submodule R (Dual R M)) :
    W.quotDualCoannihilatorToDual.Nondegenerate := by
  rw [Nondegenerate, separatingLeft_iff_ker_eq_bot, separatingRight_iff_flip_ker_eq_bot]
  letI : AddCommGroup W := inferInstance
  simp_rw [ker_eq_bot]
  exact ⟨W.quotDualCoannihilatorToDual_injective, W.flip_quotDualCoannihilatorToDual_injective⟩

end Submodule

namespace LinearMap

open Submodule

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
theorem range_dualMap_eq_dualAnnihilator_ker_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : LinearMap.range f.dualMap = f.ker.dualAnnihilator :=
  ((f.quotKerEquivOfSurjective hf).dualMap.range_comp _).trans f.ker.range_dualMap_mkQ_eq

-- Note, this can be specialized to the case where `R` is an injective `R`-module, or when
-- `f.coker` is a projective `R`-module.
theorem range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f.range.subtype.dualMap) :
    LinearMap.range f.dualMap = f.ker.dualAnnihilator := by
  have rr_surj : Function.Surjective f.rangeRestrict := by
    rw [← range_eq_top, range_rangeRestrict]
  have := range_dualMap_eq_dualAnnihilator_ker_of_surjective f.rangeRestrict rr_surj
  convert this using 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629
  · calc
      _ = range ((range f).subtype.comp f.rangeRestrict).dualMap := by simp
      _ = _ := ?_
    rw [← dualMap_comp_dualMap, range_comp_of_range_eq_top]
    rwa [range_eq_top]
  · apply congr_arg
    exact (ker_rangeRestrict f).symm

theorem ker_dualMap_eq_dualCoannihilator_range (f : M →ₗ[R] M') :
    LinearMap.ker f.dualMap = (Dual.eval R M' ∘ₗ f).range.dualCoannihilator := by
  ext x; simp [LinearMap.ext_iff (f := dualMap f x)]

@[simp]
lemma dualCoannihilator_range_eq_ker_flip (B : M →ₗ[R] M' →ₗ[R] R) :
    (range B).dualCoannihilator = LinearMap.ker B.flip := by
  ext x; simp [LinearMap.ext_iff (f := B.flip x)]

end LinearMap

end CommRing

section VectorSpace

-- Porting note: adding `uK` to avoid timeouts in `dualPairing_eq`
universe uK uV₁ uV₂
variable {K : Type uK} [Field K] {V₁ : Type uV₁} {V₂ : Type uV₂}
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace Module.Dual

variable {f : Module.Dual K V₁}

section
variable (hf : f ≠ 0)
include hf

lemma range_eq_top_of_ne_zero :
    LinearMap.range f = ⊤ := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by contrapose! hf; ext v; simpa using hf v
  rw [eq_top_iff]
  exact fun x _ ↦ ⟨x • (f v)⁻¹ • v, by simp [inv_mul_cancel₀ hv]⟩

variable [FiniteDimensional K V₁]

lemma finrank_ker_add_one_of_ne_zero :
    finrank K (LinearMap.ker f) + 1 = finrank K V₁ := by
  suffices finrank K (LinearMap.range f) = 1 by
    rw [← (LinearMap.ker f).finrank_quotient_add_finrank, add_comm, add_left_inj,
    f.quotKerEquivRange.finrank_eq, this]
  rw [range_eq_top_of_ne_zero hf, finrank_top, finrank_self]

lemma isCompl_ker_of_disjoint_of_ne_bot {p : Submodule K V₁}
    (hpf : Disjoint (LinearMap.ker f) p) (hp : p ≠ ⊥) :
    IsCompl (LinearMap.ker f) p := by
  refine ⟨hpf, codisjoint_iff.mpr <| eq_of_le_of_finrank_le le_top ?_⟩
  have : finrank K ↑(LinearMap.ker f ⊔ p) = finrank K (LinearMap.ker f) + finrank K p := by
    simp [← Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) p, hpf.eq_bot]
  rwa [finrank_top, this, ← finrank_ker_add_one_of_ne_zero hf, add_le_add_iff_left,
    Submodule.one_le_finrank_iff]

end

lemma eq_of_ker_eq_of_apply_eq [FiniteDimensional K V₁] {f g : Module.Dual K V₁} (x : V₁)
    (h : LinearMap.ker f = LinearMap.ker g) (h' : f x = g x) (hx : f x ≠ 0) :
    f = g := by
  let p := K ∙ x
  have hp : p ≠ ⊥ := by aesop
  have hpf : Disjoint (LinearMap.ker f) p := by
    rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro y ⟨hfy : f y = 0, hpy : y ∈ p⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hpy
    have ht : t = 0 := by simpa [hx] using hfy
    simp [ht]
  have hf : f ≠ 0 := by aesop
  ext v
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ᵉ (y ∈ LinearMap.ker f) (z ∈ p), y + z = v := by
    have : v ∈ (⊤ : Submodule K V₁) := Submodule.mem_top
    rwa [← (isCompl_ker_of_disjoint_of_ne_bot hf hpf hp).sup_eq_top, Submodule.mem_sup] at this
  have hy' : g y = 0 := by rwa [← LinearMap.mem_ker, ← h]
  replace hy : f y = 0 := by rwa [LinearMap.mem_ker] at hy
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [h', hy, hy']

end Module.Dual

namespace LinearMap

theorem dualPairing_nondegenerate : (dualPairing K V₁).Nondegenerate :=
  ⟨separatingLeft_iff_ker_eq_bot.mpr ker_id, fun x => (forall_dual_apply_eq_zero_iff K x).mp⟩

theorem dualMap_surjective_of_injective {f : V₁ →ₗ[K] V₂} (hf : Function.Injective f) :
    Function.Surjective f.dualMap := fun φ ↦
  have ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (ker_eq_bot.mpr hf)
  ⟨φ.comp f', ext fun x ↦ congr(φ <| $hf' x)⟩

  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.range
theorem range_dualMap_eq_dualAnnihilator_ker (f : V₁ →ₗ[K] V₂) :
    LinearMap.range f.dualMap = f.ker.dualAnnihilator :=
  range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f <|
    dualMap_surjective_of_injective (range f).injective_subtype

/-- For vector spaces, `f.dualMap` is surjective if and only if `f` is injective -/
@[simp]
theorem dualMap_surjective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Surjective f.dualMap ↔ Function.Injective f := by
  rw [← LinearMap.range_eq_top, range_dualMap_eq_dualAnnihilator_ker,
      ← Submodule.dualAnnihilator_bot, Subspace.dualAnnihilator_inj, LinearMap.ker_eq_bot]

end LinearMap

namespace Subspace

open Submodule

-- Porting note: remove this at some point; this spends a lot of time
-- checking that AddCommGroup structures on V₁ ⧸ W.dualAnnihilator are defEq
-- was much worse with implicit universe variables
theorem dualPairing_eq (W : Subspace K V₁) :
    W.dualPairing = W.quotAnnihilatorEquiv.toLinearMap := by
  ext
  rfl

theorem dualPairing_nondegenerate (W : Subspace K V₁) : W.dualPairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualPairing_eq]
    apply LinearEquiv.ker
  · intro x h
    rw [← forall_dual_apply_eq_zero_iff K x]
    intro φ
    simpa only [Submodule.dualPairing_apply, dualLift_of_subtype] using
      h (Submodule.Quotient.mk (W.dualLift φ))

theorem dualCopairing_nondegenerate (W : Subspace K V₁) : W.dualCopairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualCopairing_eq]
    apply LinearEquiv.ker
  · rintro ⟨x⟩
    simp only [Quotient.quot_mk_eq_mk, dualCopairing_apply, Quotient.mk_eq_zero]
    rw [← forall_mem_dualAnnihilator_apply_eq_zero_iff, SetLike.forall]
    exact id

-- Argument from https://math.stackexchange.com/a/2423263/172988
theorem dualAnnihilator_inf_eq (W W' : Subspace K V₁) :
    (W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator := by
  refine le_antisymm ?_ (sup_dualAnnihilator_le_inf W W')
  let F : V₁ →ₗ[K] (V₁ ⧸ W) × V₁ ⧸ W' := (Submodule.mkQ W).prod (Submodule.mkQ W')
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629 LinearMap.ker
  have : LinearMap.ker F = W ⊓ W' := by simp only [F, LinearMap.ker_prod, ker_mkQ]
  rw [← this, ← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  intro φ
  rw [LinearMap.mem_range]
  rintro ⟨x, rfl⟩
  rw [Submodule.mem_sup]
  obtain ⟨⟨a, b⟩, rfl⟩ := (dualProdDualEquivDual K (V₁ ⧸ W) (V₁ ⧸ W')).surjective x
  obtain ⟨a', rfl⟩ := (dualQuotEquivDualAnnihilator W).symm.surjective a
  obtain ⟨b', rfl⟩ := (dualQuotEquivDualAnnihilator W').symm.surjective b
  use a', a'.property, b', b'.property
  rfl

-- This is also true if `V₁` is finite dimensional since one can restrict `ι` to some subtype
-- for which the infi and supr are the same.
-- The obstruction to the `dualAnnihilator_inf_eq` argument carrying through is that we need
-- for `Module.Dual R (Π (i : ι), V ⧸ W i) ≃ₗ[K] Π (i : ι), Module.Dual R (V ⧸ W i)`, which is not
-- true for infinite `ι`. One would need to add additional hypothesis on `W` (for example, it might
-- be true when the family is inf-closed).
-- TODO: generalize to `Sort`
theorem dualAnnihilator_iInf_eq {ι : Type*} [Finite ι] (W : ι → Subspace K V₁) :
    (⨅ i : ι, W i).dualAnnihilator = ⨆ i : ι, (W i).dualAnnihilator := by
  revert ι
  apply Finite.induction_empty_option
  · intro α β h hyp W
    rw [← h.iInf_comp, hyp _, ← h.iSup_comp]
  · intro W
    rw [iSup_of_empty', iInf_of_isEmpty, sInf_empty, sSup_empty, dualAnnihilator_top]
  · intro α _ h W
    rw [iInf_option, iSup_option, dualAnnihilator_inf_eq, h]

/-- For vector spaces, dual annihilators carry direct sum decompositions
to direct sum decompositions. -/
theorem isCompl_dualAnnihilator {W W' : Subspace K V₁} (h : IsCompl W W') :
    IsCompl W.dualAnnihilator W'.dualAnnihilator := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff] at h ⊢
  rw [← dualAnnihilator_inf_eq, ← dualAnnihilator_sup_eq, h.1, h.2, dualAnnihilator_top,
    dualAnnihilator_bot]
  exact ⟨rfl, rfl⟩

/-- For finite-dimensional vector spaces, one can distribute duals over quotients by identifying
`W.dualLift.range` with `W`. Note that this depends on a choice of splitting of `V₁`. -/
def dualQuotDistrib [FiniteDimensional K V₁] (W : Subspace K V₁) :
    Module.Dual K (V₁ ⧸ W) ≃ₗ[K] Module.Dual K V₁ ⧸ LinearMap.range W.dualLift :=
  W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm

end Subspace

section FiniteDimensional

open Module LinearMap

namespace LinearMap

@[simp]
theorem finrank_range_dualMap_eq_finrank_range (f : V₁ →ₗ[K] V₂) :
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): broken dot notation https://github.com/leanprover/lean4/issues/1629
    finrank K (LinearMap.range f.dualMap) = finrank K (LinearMap.range f) := by
  rw [congr_arg dualMap (show f = (range f).subtype.comp f.rangeRestrict by rfl),
    ← dualMap_comp_dualMap, range_comp,
    range_eq_top.mpr (dualMap_surjective_of_injective (range f).injective_subtype),
    Submodule.map_top, finrank_range_of_inj, Subspace.dual_finrank_eq]
  exact dualMap_injective_of_surjective (range_eq_top.mp f.range_rangeRestrict)

/-- `f.dualMap` is injective if and only if `f` is surjective -/
@[simp]
theorem dualMap_injective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Injective f.dualMap ↔ Function.Surjective f := by
  refine ⟨Function.mtr fun not_surj inj ↦ ?_, dualMap_injective_of_surjective⟩
  rw [← range_eq_top, ← Ne, ← lt_top_iff_ne_top] at not_surj
  obtain ⟨φ, φ0, range_le_ker⟩ := (range f).exists_le_ker_of_lt_top not_surj
  exact φ0 (inj <| ext fun x ↦ range_le_ker ⟨x, rfl⟩)

/-- `f.dualMap` is bijective if and only if `f` is -/
@[simp]
theorem dualMap_bijective_iff {f : V₁ →ₗ[K] V₂} :
    Function.Bijective f.dualMap ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, dualMap_surjective_iff, dualMap_injective_iff, and_comm]

variable {B : V₁ →ₗ[K] V₂ →ₗ[K] K}

@[simp]
lemma dualAnnihilator_ker_eq_range_flip [IsReflexive K V₂] :
    (ker B).dualAnnihilator = range B.flip := by
  change _ = range (B.dualMap.comp (Module.evalEquiv K V₂).toLinearMap)
  rw [← range_dualMap_eq_dualAnnihilator_ker, range_comp_of_range_eq_top _ (LinearEquiv.range _)]

open Function

theorem flip_injective_iff₁ [FiniteDimensional K V₁] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_surjective_iff, ← (evalEquiv K V₁).toEquiv.surjective_comp]; rfl

theorem flip_injective_iff₂ [FiniteDimensional K V₂] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_injective_iff]; exact (evalEquiv K V₂).toEquiv.injective_comp B.dualMap

theorem flip_surjective_iff₁ [FiniteDimensional K V₁] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₂.symm

theorem flip_surjective_iff₂ [FiniteDimensional K V₂] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₁.symm

theorem flip_bijective_iff₁ [FiniteDimensional K V₁] : Bijective B.flip ↔ Bijective B := by
  simp_rw [Bijective, flip_injective_iff₁, flip_surjective_iff₁, and_comm]

theorem flip_bijective_iff₂ [FiniteDimensional K V₂] : Bijective B.flip ↔ Bijective B :=
  flip_bijective_iff₁.symm

end LinearMap

namespace Subspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V)) [FiniteDimensional K W] :
    Function.Bijective W.quotDualCoannihilatorToDual :=
  ⟨W.quotDualCoannihilatorToDual_injective, letI : AddCommGroup W := inferInstance
    flip_injective_iff₂.mp W.flip_quotDualCoannihilatorToDual_injective⟩

theorem flip_quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V))
    [FiniteDimensional K W] : Function.Bijective W.quotDualCoannihilatorToDual.flip :=
  letI : AddCommGroup W := inferInstance
  flip_bijective_iff₂.mpr W.quotDualCoannihilatorToDual_bijective

theorem dualCoannihilator_dualAnnihilator_eq {W : Subspace K (Dual K V)} [FiniteDimensional K W] :
    W.dualCoannihilator.dualAnnihilator = W :=
  let e := (LinearEquiv.ofBijective _ W.flip_quotDualCoannihilatorToDual_bijective).trans
    (Submodule.dualQuotEquivDualAnnihilator _)
  letI : AddCommGroup W := inferInstance
  haveI : FiniteDimensional K W.dualCoannihilator.dualAnnihilator := LinearEquiv.finiteDimensional e
  (eq_of_le_of_finrank_eq W.le_dualCoannihilator_dualAnnihilator e.finrank_eq).symm

theorem finiteDimensional_quot_dualCoannihilator_iff {W : Submodule K (Dual K V)} :
    FiniteDimensional K (V ⧸ W.dualCoannihilator) ↔ FiniteDimensional K W :=
  ⟨fun _ ↦ FiniteDimensional.of_injective _ W.flip_quotDualCoannihilatorToDual_injective,
    fun _ ↦ by
      #adaptation_note /-- https://github.com/leanprover/lean4/pull/4119
      the `Free K W` instance isn't found unless we use `set_option maxSynthPendingDepth 2`, or add
      explicit instances:
      ```
      have := Free.of_divisionRing K ↥W
      have := Basis.dual_finite (R := K) (M := W)
      ```
      -/
      set_option maxSynthPendingDepth 2 in
      exact FiniteDimensional.of_injective _ W.quotDualCoannihilatorToDual_injective⟩

open OrderDual in
/-- For any vector space, `dualAnnihilator` and `dualCoannihilator` gives an antitone order
  isomorphism between the finite-codimensional subspaces in the vector space and the
  finite-dimensional subspaces in its dual. -/
def orderIsoFiniteCodimDim :
    {W : Subspace K V // FiniteDimensional K (V ⧸ W)} ≃o
    {W : Subspace K (Dual K V) // FiniteDimensional K W}ᵒᵈ where
  toFun W := toDual ⟨W.1.dualAnnihilator, Submodule.finite_dualAnnihilator_iff.mpr W.2⟩
  invFun W := ⟨(ofDual W).1.dualCoannihilator,
    finiteDimensional_quot_dualCoannihilator_iff.mpr (ofDual W).2⟩
  left_inv _ := Subtype.ext dualAnnihilator_dualCoannihilator_eq
  right_inv W := have := (ofDual W).2; Subtype.ext dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open OrderDual in
/-- For any finite-dimensional vector space, `dualAnnihilator` and `dualCoannihilator` give
  an antitone order isomorphism between the subspaces in the vector space and the subspaces
  in its dual. -/
def orderIsoFiniteDimensional [FiniteDimensional K V] :
    Subspace K V ≃o (Subspace K (Dual K V))ᵒᵈ where
  toFun W := toDual W.dualAnnihilator
  invFun W := (ofDual W).dualCoannihilator
  left_inv _ := dualAnnihilator_dualCoannihilator_eq
  right_inv _ := dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open Submodule in
theorem dualAnnihilator_dualAnnihilator_eq_map (W : Subspace K V) [FiniteDimensional K W] :
    W.dualAnnihilator.dualAnnihilator = W.map (Dual.eval K V) := by
  let e1 := (Free.chooseBasis K W).toDualEquiv ≪≫ₗ W.quotAnnihilatorEquiv.symm
  haveI := e1.finiteDimensional
  let e2 := (Free.chooseBasis K _).toDualEquiv ≪≫ₗ W.dualAnnihilator.dualQuotEquivDualAnnihilator
  haveI := LinearEquiv.finiteDimensional (V₂ := W.dualAnnihilator.dualAnnihilator) e2
  rw [eq_of_le_of_finrank_eq (map_le_dualAnnihilator_dualAnnihilator W)]
  rw [← (equivMapOfInjective _ (eval_apply_injective K (V := V)) W).finrank_eq, e1.finrank_eq]
  exact e2.finrank_eq

theorem map_dualCoannihilator (W : Subspace K (Dual K V)) [FiniteDimensional K V] :
    W.dualCoannihilator.map (Dual.eval K V) = W.dualAnnihilator := by
  rw [← dualAnnihilator_dualAnnihilator_eq_map, dualCoannihilator_dualAnnihilator_eq]

end Subspace

end FiniteDimensional

end VectorSpace

namespace TensorProduct

variable (R A : Type*) (M : Type*) (N : Type*)
variable {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι] [Fintype κ]

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/-- The canonical linear map from `Dual M ⊗ Dual N` to `Dual (M ⊗ N)`,
sending `f ⊗ g` to the composition of `TensorProduct.map f g` with
the natural isomorphism `R ⊗ R ≃ R`.
-/
def dualDistrib : Dual R M ⊗[R] Dual R N →ₗ[R] Dual R (M ⊗[R] N) :=
  compRight ↑(TensorProduct.lid R R) ∘ₗ homTensorHomMap R M N R R

variable {R M N}

@[simp]
theorem dualDistrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R M N (f ⊗ₜ g) (m ⊗ₜ n) = f m * g n :=
  rfl

end

namespace AlgebraTensorModule
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module A M] [Module R N] [IsScalarTower R A M]

/-- Heterobasic version of `TensorProduct.dualDistrib` -/
def dualDistrib : Dual A M ⊗[R] Dual R N →ₗ[A] Dual A (M ⊗[R] N) :=
  compRight (Algebra.TensorProduct.rid R A A).toLinearMap ∘ₗ homTensorHomMap R A A M N A R

variable {R M N}

@[simp]
theorem dualDistrib_apply (f : Dual A M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R A M N (f ⊗ₜ g) (m ⊗ₜ n) = g n • f m :=
  rfl

end AlgebraTensorModule

variable {R M N}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- An inverse to `TensorProduct.dualDistrib` given bases.
-/
noncomputable def dualDistribInvOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R (M ⊗[R] N) →ₗ[R] Dual R M ⊗[R] Dual R N :=
  -- Porting note: ∑ (i) (j) does not seem to work; applyₗ needs a little help to unify
  ∑ i, ∑ j,
    (ringLmapEquivSelf R ℕ _).symm (b.dualBasis i ⊗ₜ c.dualBasis j) ∘ₗ
      (applyₗ (R := R) (c j)) ∘ₗ (applyₗ (R := R) (b i)) ∘ₗ lcurry R M N R

@[simp]
theorem dualDistribInvOfBasis_apply (b : Basis ι R M) (c : Basis κ R N) (f : Dual R (M ⊗[R] N)) :
    dualDistribInvOfBasis b c f = ∑ i, ∑ j, f (b i ⊗ₜ c j) • b.dualBasis i ⊗ₜ c.dualBasis j := by
  simp [dualDistribInvOfBasis]

-- Porting note: introduced to help with timeout in dualDistribEquivOfBasis
theorem dualDistrib_dualDistribInvOfBasis_left_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistrib R M N) (dualDistribInvOfBasis b c) = LinearMap.id := by
  apply (b.tensorProduct c).dualBasis.ext
  rintro ⟨i, j⟩
  apply (b.tensorProduct c).ext
  rintro ⟨i', j'⟩
  simp only [dualDistrib, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, Basis.coord_apply, Basis.tensorProduct_repr_tmul_apply,
    Basis.repr_self, ne_eq, _root_.map_sum, map_smul, homTensorHomMap_apply, compRight_apply,
    Basis.tensorProduct_apply, coeFn_sum, Finset.sum_apply, smul_apply, LinearEquiv.coe_coe,
    map_tmul, lid_tmul, smul_eq_mul, id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simpa using mul_comm _ _
  all_goals { intros; simp [*] at * }

-- Porting note: introduced to help with timeout in dualDistribEquivOfBasis
theorem dualDistrib_dualDistribInvOfBasis_right_inverse (b : Basis ι R M) (c : Basis κ R N) :
    comp (dualDistribInvOfBasis b c) (dualDistrib R M N) = LinearMap.id := by
  apply (b.dualBasis.tensorProduct c.dualBasis).ext
  rintro ⟨i, j⟩
  simp only [Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp, Function.comp_apply,
    dualDistribInvOfBasis_apply, dualDistrib_apply, Basis.coord_apply, Basis.repr_self,
    ne_eq, id_coe, id_eq]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  all_goals { intros; simp [*] at * }

/-- A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` given bases for `M` and `N`.
It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simps!]
noncomputable def dualDistribEquivOfBasis (b : Basis ι R M) (c : Basis κ R N) :
    Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) := by
  refine LinearEquiv.ofLinear (dualDistrib R M N) (dualDistribInvOfBasis b c) ?_ ?_
  · exact dualDistrib_dualDistribInvOfBasis_left_inverse _ _
  · exact dualDistrib_dualDistribInvOfBasis_right_inverse _ _

variable (R M N)
variable [Module.Finite R M] [Module.Finite R N] [Module.Free R M] [Module.Free R N]

/--
A linear equivalence between `Dual M ⊗ Dual N` and `Dual (M ⊗ N)` when `M` and `N` are finite free
modules. It sends `f ⊗ g` to the composition of `TensorProduct.map f g` with the natural
isomorphism `R ⊗ R ≃ R`.
-/
@[simp]
noncomputable def dualDistribEquiv : Dual R M ⊗[R] Dual R N ≃ₗ[R] Dual R (M ⊗[R] N) :=
  dualDistribEquivOfBasis (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)

end TensorProduct

set_option linter.style.longFile 2000
