/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Perfect pairings of modules

A perfect pairing of two (left) modules may be defined either as:
1. A bilinear map `M × N → R` such that the induced maps `M → Dual R N` and `N → Dual R M` are both
  bijective. It follows from this that both `M` and `N` are reflexive modules.
2. A linear equivalence `N ≃ Dual R M` for which `M` is reflexive. (It then follows that `N` is
  reflexive.)

In this file we provide a `PerfectPairing` definition corresponding to 1 above, together with logic
to connect 1 and 2.

## Main definitions

* `PerfectPairing`
* `PerfectPairing.flip`
* `PerfectPairing.dual`
* `PerfectPairing.toDualLeft`
* `PerfectPairing.toDualRight`
* `LinearEquiv.flip`
* `LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive`
* `LinearEquiv.toPerfectPairing`

-/

open Function Module

noncomputable section

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A perfect pairing of two (left) modules over a commutative ring. -/
structure PerfectPairing extends M →ₗ[R] N →ₗ[R] R where
  bijective_left : Bijective toLinearMap
  bijective_right : Bijective toLinearMap.flip

/-- The underlying bilinear map of a perfect pairing. -/
add_decl_doc PerfectPairing.toLinearMap

variable {R M N}

namespace PerfectPairing

@[deprecated (since := "2025-04-20")] alias toLin := toLinearMap
@[deprecated (since := "2025-04-20")] alias bijectiveLeft := bijective_left
@[deprecated (since := "2025-04-20")] alias bijectiveRight := bijective_right

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear form. -/
def mkOfInjective {K V W : Type*}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (B : V →ₗ[K] W →ₗ[K] K)
    (h : Injective B)
    (h' : Injective B.flip) :
    PerfectPairing K V W where
  toLinearMap := B
  bijective_left := ⟨h, by rwa [← B.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by
    have : FiniteDimensional K W := FiniteDimensional.of_injective B.flip h'
    rwa [← B.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear form. -/
def mkOfInjective' {K V W : Type*}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (B : V →ₗ[K] W →ₗ[K] K)
    (h : Injective B)
    (h' : Injective B.flip) :
    PerfectPairing K V W where
  toLinearMap := B
  bijective_left := ⟨h, by
    have : FiniteDimensional K V := FiniteDimensional.of_injective B h
    rwa [← B.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by rwa [← B.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

instance instFunLike : FunLike (PerfectPairing R M N) M (N →ₗ[R] R) where
  coe f := f.toLinearMap
  coe_injective' x y h := by cases x; cases y; simpa using h

@[simp]
lemma toLinearMap_apply (p : PerfectPairing R M N) (x : M) : p.toLinearMap x = p x := rfl

@[deprecated (since := "2025-04-20")] alias toLin_apply := toLinearMap_apply

@[simp]
lemma mk_apply_apply {f : M →ₗ[R] N →ₗ[R] R} {hl} {hr} {x : M} :
    (⟨f, hl, hr⟩ : PerfectPairing R M N) x = f x :=
  rfl

variable (p : PerfectPairing R M N)

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
protected def flip : PerfectPairing R N M where
  toLinearMap := p.toLinearMap.flip
  bijective_left := p.bijective_right
  bijective_right := p.bijective_left

@[simp]
lemma flip_apply_apply {x : M} {y : N} : p.flip y x = p x y :=
  rfl

@[simp]
lemma flip_flip : p.flip.flip = p :=
  rfl

/-- The linear equivalence from `M` to `Dual R N` induced by a perfect pairing. -/
def toDualLeft : M ≃ₗ[R] Dual R N :=
  LinearEquiv.ofBijective p.toLinearMap p.bijective_left

@[simp]
theorem toDualLeft_apply (a : M) : p.toDualLeft a = p a :=
  rfl

@[simp]
theorem apply_toDualLeft_symm_apply (f : Dual R N) (x : N) : p (p.toDualLeft.symm f) x = f x := by
  have h := LinearEquiv.apply_symm_apply p.toDualLeft f
  rw [toDualLeft_apply] at h
  exact congrFun (congrArg DFunLike.coe h) x

/-- The linear equivalence from `N` to `Dual R M` induced by a perfect pairing. -/
def toDualRight : N ≃ₗ[R] Dual R M :=
  toDualLeft p.flip

@[simp]
theorem toDualRight_apply (a : N) : p.toDualRight a = p.flip a :=
  rfl

@[simp]
theorem apply_apply_toDualRight_symm (x : M) (f : Dual R M) :
    (p x) (p.toDualRight.symm f) = f x := by
  have h := LinearEquiv.apply_symm_apply p.toDualRight f
  rw [toDualRight_apply] at h
  exact congrFun (congrArg DFunLike.coe h) x

theorem toDualLeft_of_toDualRight_symm (x : M) (f : Dual R M) :
    (p.toDualLeft x) (p.toDualRight.symm f) = f x := by
  rw [@toDualLeft_apply]
  exact apply_apply_toDualRight_symm p x f

theorem toDualRight_symm_toDualLeft (x : M) :
    p.toDualRight.symm.dualMap (p.toDualLeft x) = Dual.eval R M x := by
  ext f
  simp only [LinearEquiv.dualMap_apply, Dual.eval_apply]
  exact toDualLeft_of_toDualRight_symm p x f

theorem toDualRight_symm_comp_toDualLeft :
    p.toDualRight.symm.dualMap ∘ₗ (p.toDualLeft : M →ₗ[R] Dual R N) = Dual.eval R M := by
  ext1 x
  exact p.toDualRight_symm_toDualLeft x

theorem bijective_toDualRight_symm_toDualLeft :
    Bijective (fun x => p.toDualRight.symm.dualMap (p.toDualLeft x)) :=
  Bijective.comp (LinearEquiv.bijective p.toDualRight.symm.dualMap)
    (LinearEquiv.bijective p.toDualLeft)

include p in
theorem reflexive_left : IsReflexive R M where
  bijective_dual_eval' := by
    rw [← p.toDualRight_symm_comp_toDualLeft]
    exact p.bijective_toDualRight_symm_toDualLeft

include p in
theorem reflexive_right : IsReflexive R N :=
  p.flip.reflexive_left

instance : EquivLike (PerfectPairing R M N) M (Dual R N) where
  coe p := p.toDualLeft
  inv p := p.toDualLeft.symm
  left_inv p x := LinearEquiv.symm_apply_apply _ _
  right_inv p x := LinearEquiv.apply_symm_apply _ _
  coe_injective' p q h h' := by
    cases p
    cases q
    simp only [mk.injEq]
    ext m n
    simp only [DFunLike.coe_fn_eq] at h
    exact LinearMap.congr_fun (LinearEquiv.congr_fun h m) n

instance : LinearEquivClass (PerfectPairing R M N) R M (Dual R N) where
  map_add p m₁ m₂ := p.toLinearMap.map_add m₁ m₂
  map_smulₛₗ p t m := p.toLinearMap.map_smul t m

include p in
theorem finrank_eq [Module.Finite R M] [Module.Free R M] :
    finrank R M = finrank R N :=
  ((Module.Free.chooseBasis R M).toDualEquiv.trans p.toDualRight.symm).finrank_eq

/-- Given a perfect pairing `p` between `M` and `N`, we say a pair of submodules `U` in `M` and
`V` in `N` are perfectly complementary wrt `p` if their dual annihilators are complementary, using
`p` to identify `M` and `N` with dual spaces. -/
structure IsPerfectCompl (U : Submodule R M) (V : Submodule R N) : Prop where
  isCompl_left : IsCompl U (V.dualAnnihilator.map p.toDualLeft.symm)
  isCompl_right : IsCompl V (U.dualAnnihilator.map p.toDualRight.symm)

namespace IsPerfectCompl

variable {p}
variable {U : Submodule R M} {V : Submodule R N}

protected lemma flip (h : p.IsPerfectCompl U V) :
    p.flip.IsPerfectCompl V U where
  isCompl_left := h.isCompl_right
  isCompl_right := h.isCompl_left

@[simp]
protected lemma flip_iff :
    p.flip.IsPerfectCompl V U ↔ p.IsPerfectCompl U V :=
  ⟨fun h ↦ h.flip, fun h ↦ h.flip⟩

@[simp]
lemma left_top_iff :
    p.IsPerfectCompl ⊤ V ↔ V = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact eq_top_of_isCompl_bot <| by simpa using h.isCompl_right
  · rw [h]
    exact
      { isCompl_left := by simpa using isCompl_top_bot
        isCompl_right := by simpa using isCompl_top_bot }

@[simp]
lemma right_top_iff :
    p.IsPerfectCompl U ⊤ ↔ U = ⊤ := by
  rw [← IsPerfectCompl.flip_iff]
  exact left_top_iff

end IsPerfectCompl

end PerfectPairing

variable [IsReflexive R M]

/-- A reflexive module has a perfect pairing with its dual. -/
@[simps!]
def IsReflexive.toPerfectPairingDual : PerfectPairing R (Dual R M) M where
  toLinearMap := .id
  bijective_left := bijective_id
  bijective_right := bijective_dual_eval R M

@[simp]
lemma IsReflexive.toPerfectPairingDual_apply {f : Dual R M} {x : M} :
    IsReflexive.toPerfectPairingDual (R := R) f x = f x :=
  rfl

variable (e : N ≃ₗ[R] Dual R M)

namespace LinearEquiv

/-- For a reflexive module `M`, an equivalence `N ≃ₗ[R] Dual R M` naturally yields an equivalence
`M ≃ₗ[R] Dual R N`. Such equivalences are known as perfect pairings. -/
def flip : M ≃ₗ[R] Dual R N :=
  (evalEquiv R M).trans e.dualMap

@[simp] lemma coe_toLinearMap_flip : e.flip = (↑e : N →ₗ[R] Dual R M).flip := rfl

@[simp] lemma flip_apply (m : M) (n : N) : e.flip m n = e n m := rfl

lemma symm_flip : e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm := rfl

lemma trans_dualMap_symm_flip : e.trans e.flip.symm.dualMap = Dual.eval R N := by
  ext; simp [symm_flip]

include e in
/-- If `N` is in perfect pairing with `M`, then it is reflexive. -/
lemma isReflexive_of_equiv_dual_of_isReflexive : IsReflexive R N := by
  constructor
  rw [← trans_dualMap_symm_flip e]
  exact LinearEquiv.bijective _

@[simp] lemma flip_flip (h : IsReflexive R N := isReflexive_of_equiv_dual_of_isReflexive e) :
    e.flip.flip = e := by
  ext; rfl

/-- If `M` is reflexive then a linear equivalence `N ≃ Dual R M` is a perfect pairing. -/
def toPerfectPairing : PerfectPairing R N M where
  toLinearMap := e
  bijective_left := e.bijective
  bijective_right := e.flip.bijective

end LinearEquiv

/-- A perfect pairing induces a perfect pairing between dual spaces. -/
def PerfectPairing.dual (p : PerfectPairing R M N) :
    PerfectPairing R (Dual R M) (Dual R N) :=
  let _i := p.reflexive_right
  (p.toDualRight.symm.trans (evalEquiv R N)).toPerfectPairing

namespace Submodule

open LinearEquiv

@[simp]
lemma dualCoannihilator_map_linearEquiv_flip (p : Submodule R M) :
    (p.map e.flip).dualCoannihilator = p.dualAnnihilator.map e.symm := by
  ext; simp [LinearEquiv.symm_apply_eq, Submodule.mem_dualCoannihilator]

@[simp]
lemma map_dualAnnihilator_linearEquiv_flip_symm (p : Submodule R N) :
    p.dualAnnihilator.map e.flip.symm = (p.map e).dualCoannihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← dualCoannihilator_map_linearEquiv_flip, flip_flip]

@[simp]
lemma map_dualCoannihilator_linearEquiv_flip (p : Submodule R (Dual R M)) :
    p.dualCoannihilator.map e.flip = (p.map e.symm).dualAnnihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  suffices (p.map e.symm).dualAnnihilator.map e.flip.symm =
      (p.dualCoannihilator.map e.flip).map e.flip.symm by
    exact (Submodule.map_injective_of_injective e.flip.symm.injective this).symm
  erw [← dualCoannihilator_map_linearEquiv_flip, flip_flip, ← map_comp, ← map_comp]
  simp [-coe_toLinearMap_flip]

@[simp]
lemma dualAnnihilator_map_linearEquiv_flip_symm (p : Submodule R (Dual R N)) :
    (p.map e.flip.symm).dualAnnihilator = p.dualCoannihilator.map e := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← map_dualCoannihilator_linearEquiv_flip, flip_flip]

end Submodule
