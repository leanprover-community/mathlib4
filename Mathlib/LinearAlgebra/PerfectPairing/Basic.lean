/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Yaël Dillies
-/
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Perfect pairings

This file defines perfect pairings of modules.

A perfect pairing of two (left) modules may be defined either as:
1. A bilinear map `M × N → R` such that the induced maps `M → Dual R N` and `N → Dual R M` are both
  bijective. It follows from this that both `M` and `N` are reflexive modules.
2. A linear equivalence `N ≃ Dual R M` for which `M` is reflexive. (It then follows that `N` is
  reflexive.)

In this file we provide a definition `IsPerfPair` corresponding to 1 above, together with logic
to connect 1 and 2.
-/

open Function Module

namespace LinearMap
variable {R K M M' N N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M']
  [AddCommGroup N']

section CommRing
variable [CommRing R] [Module R M] [Module R M'] [Module R N] [Module R N']
  {p : M →ₗ[R] N →ₗ[R] R} {x : M} {y : N}

/-- For a ring `R` and two modules `M` and `N`, a perfect pairing is a bilinear map `M × N → R`
that is bijective in both arguments. -/
@[ext]
class IsPerfPair (p : M →ₗ[R] N →ₗ[R] R) where
  bijective_left (p) : Bijective p
  bijective_right (p) : Bijective p.flip

/-- Given a perfect pairing between `M`and `N`, we may interchange the roles of `M` and `N`. -/
protected lemma IsPerfPair.flip (hp : p.IsPerfPair) : p.flip.IsPerfPair where
  bijective_left := IsPerfPair.bijective_right p
  bijective_right := IsPerfPair.bijective_left p

variable [p.IsPerfPair]

/-- Given a perfect pairing between `M`and `N`, we may interchange the roles of `M` and `N`. -/
instance flip.instIsPerfPair : p.flip.IsPerfPair := .flip ‹_›

variable (p)

/-- Turn a perfect pairing between `M` and `N` into an isomorphism between `M` and the dual of `N`.
-/
noncomputable def toPerfPair : M ≃ₗ[R] Dual R N :=
  .ofBijective { toFun := _, map_add' x y := by simp, map_smul' r x := by simp } <|
    IsPerfPair.bijective_left p

@[simp] lemma toLinearMap_toPerfPair (x : M) : p.toPerfPair x = p x := rfl
@[simp] lemma toPerfPair_apply (x : M) (y : N) : p.toPerfPair x y = p x y := rfl

@[simp] lemma apply_symm_toPerfPair_self (f : Dual R N) : p (p.toPerfPair.symm f) = f :=
  p.toPerfPair.apply_symm_apply f

@[simp] lemma apply_toPerfPair_flip (f : Dual R M) (x : M) : p x (p.flip.toPerfPair.symm f) = f x :=
  congr($(p.flip.apply_symm_toPerfPair_self ..) x)

include p in
lemma _root_.Module.IsReflexive.of_isPerfPair : IsReflexive R M where
  bijective_dual_eval' := by
    convert (p.toPerfPair.trans p.flip.toPerfPair.dualMap.symm).bijective
    ext x f
    simp

include p in
lemma _root_.Module.finrank_of_isPerfPair [Module.Finite R M] [Module.Free R M] :
    finrank R M = finrank R N :=
  ((Module.Free.chooseBasis R M).toDualEquiv.trans p.flip.toPerfPair.symm).finrank_eq

/-- A reflexive module has a perfect pairing with its dual. -/
protected instance IsPerfPair.id [IsReflexive R M] : IsPerfPair (.id (R := R) (M := Dual R M)) where
  bijective_left := bijective_id
  bijective_right := bijective_dual_eval R M

/-- A reflexive module has a perfect pairing with its dual. -/
instance IsPerfPair.dualEval [IsReflexive R M] : IsPerfPair (Dual.eval R M) := .flip .id

instance IsPerfPair.compl₁₂ (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) :
    (p.compl₁₂ eM eN : M' →ₗ[R] N' →ₗ[R] R).IsPerfPair :=
  ⟨((LinearEquiv.congrLeft R R eN).symm.bijective.comp
    (IsPerfPair.bijective_left p)).comp eM.bijective,
    ((LinearEquiv.congrLeft R R eM).symm.bijective.comp
    (IsPerfPair.bijective_right p)).comp eN.bijective⟩

lemma IsPerfPair.congr (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) (q : M' →ₗ[R] N' →ₗ[R] R)
    (H : q.compl₁₂ eM.symm eN.symm = p) : q.IsPerfPair := by
  obtain rfl : q = p.compl₁₂ eM eN := by subst H; ext; simp
  infer_instance

lemma IsPerfPair.of_bijective (p : M →ₗ[R] N →ₗ[R] R) [IsReflexive R N] (h : Bijective p) :
    IsPerfPair p :=
  inferInstanceAs ((LinearMap.id (R := R) (M := Dual R N)).compl₁₂
    (LinearEquiv.ofBijective p h : M →ₗ[R] N →ₗ[R] R)
    (LinearEquiv.refl R N : N →ₗ[R] N)).IsPerfPair

end CommRing

section Field
variable [Field K] [Module K M] [Module K N] {p : M →ₗ[K] N →ₗ[K] K} {x : M} {y : N}

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing. -/
lemma IsPerfPair.of_injective [FiniteDimensional K M] (h : Injective p) (h' : Injective p.flip) :
    p.IsPerfPair where
  bijective_left := ⟨h, by rwa [← p.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by
    have : FiniteDimensional K N := FiniteDimensional.of_injective p.flip h'
    rwa [← p.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing. -/
lemma IsPerfPair.of_injective' [FiniteDimensional K N] (h : Injective p) (h' : Injective p.flip) :
    p.IsPerfPair := .flip <| .of_injective h' h

end Field
end LinearMap

noncomputable section

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A perfect pairing of two (left) modules over a commutative ring. -/
@[deprecated LinearMap.IsPerfPair (since := "2025-05-27")]
structure PerfectPairing extends M →ₗ[R] N →ₗ[R] R where
  bijective_left : Bijective toLinearMap
  bijective_right : Bijective toLinearMap.flip

/-- The underlying bilinear map of a perfect pairing. -/
add_decl_doc PerfectPairing.toLinearMap

variable {R M N}

namespace PerfectPairing

set_option linter.deprecated false in
/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear form. -/
@[deprecated LinearMap.IsPerfPair.of_injective (since := "2025-05-27")]
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

set_option linter.deprecated false in
/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear form. -/
@[deprecated LinearMap.IsPerfPair.of_injective' (since := "2025-05-27")]
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

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2025-05-27")]
instance instFunLike : FunLike (PerfectPairing R M N) M (N →ₗ[R] R) where
  coe f := f.toLinearMap
  coe_injective' x y h := by cases x; cases y; simpa using h

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2025-05-27")]
lemma toLinearMap_apply (p : PerfectPairing R M N) (x : M) : p.toLinearMap x = p x := rfl

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2025-05-27")]
lemma mk_apply_apply {f : M →ₗ[R] N →ₗ[R] R} {hl} {hr} {x : M} :
    (⟨f, hl, hr⟩ : PerfectPairing R M N) x = f x :=
  rfl

set_option linter.deprecated false

variable (p : PerfectPairing R M N)

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
@[deprecated LinearMap.IsPerfPair.flip (since := "2025-05-27")]
protected def flip : PerfectPairing R N M where
  toLinearMap := p.toLinearMap.flip
  bijective_left := p.bijective_right
  bijective_right := p.bijective_left

@[deprecated "No replacement" (since := "2025-05-27")]
lemma flip_apply_apply {x : M} {y : N} : p.flip y x = p x y :=
  rfl

@[deprecated "No replacement" (since := "2025-05-27")]
lemma flip_flip : p.flip.flip = p :=
  rfl

/-- The linear equivalence from `M` to `Dual R N` induced by a perfect pairing. -/
@[deprecated LinearMap.toPerfPair (since := "2025-05-27")]
def toDualLeft : M ≃ₗ[R] Dual R N :=
  LinearEquiv.ofBijective p.toLinearMap p.bijective_left

@[deprecated "No replacement" (since := "2025-05-27")]
theorem toDualLeft_apply (a : M) : p.toDualLeft a = p a :=
  rfl

@[deprecated "No replacement" (since := "2025-05-27")]
theorem apply_toDualLeft_symm_apply (f : Dual R N) (x : N) : p (p.toDualLeft.symm f) x = f x := by
  have h := LinearEquiv.apply_symm_apply p.toDualLeft f
  rw [toDualLeft_apply] at h
  exact congrFun (congrArg DFunLike.coe h) x

/-- The linear equivalence from `N` to `Dual R M` induced by a perfect pairing. -/
@[deprecated LinearMap.toPerfPair (since := "2025-05-27")]
def toDualRight : N ≃ₗ[R] Dual R M :=
  toDualLeft p.flip

@[deprecated "No replacement" (since := "2025-05-27")]
theorem toDualRight_apply (a : N) : p.toDualRight a = p.flip a :=
  rfl

@[deprecated "No replacement" (since := "2025-05-27")]
theorem apply_apply_toDualRight_symm (x : M) (f : Dual R M) :
    (p x) (p.toDualRight.symm f) = f x := by
  have h := LinearEquiv.apply_symm_apply p.toDualRight f
  rw [toDualRight_apply] at h
  exact congrFun (congrArg DFunLike.coe h) x

@[deprecated "No replacement" (since := "2025-05-27")]
theorem toDualLeft_of_toDualRight_symm (x : M) (f : Dual R M) :
    (p.toDualLeft x) (p.toDualRight.symm f) = f x := by
  rw [@toDualLeft_apply]
  exact apply_apply_toDualRight_symm p x f

@[deprecated "No replacement" (since := "2025-05-27")]
theorem toDualRight_symm_toDualLeft (x : M) :
    p.toDualRight.symm.dualMap (p.toDualLeft x) = Dual.eval R M x := by
  ext f
  simp only [LinearEquiv.dualMap_apply, Dual.eval_apply]
  exact toDualLeft_of_toDualRight_symm p x f

@[deprecated "No replacement" (since := "2025-05-27")]
theorem toDualRight_symm_comp_toDualLeft :
    p.toDualRight.symm.dualMap ∘ₗ (p.toDualLeft : M →ₗ[R] Dual R N) = Dual.eval R M := by
  ext1 x
  exact p.toDualRight_symm_toDualLeft x

@[deprecated "No replacement" (since := "2025-05-27")]
theorem bijective_toDualRight_symm_toDualLeft :
    Bijective (fun x => p.toDualRight.symm.dualMap (p.toDualLeft x)) :=
  Bijective.comp (LinearEquiv.bijective p.toDualRight.symm.dualMap)
    (LinearEquiv.bijective p.toDualLeft)

include p in
@[deprecated Module.IsReflexive.of_isPerfPair (since := "2025-05-27")]
theorem reflexive_left : IsReflexive R M where
  bijective_dual_eval' := by
    rw [← p.toDualRight_symm_comp_toDualLeft]
    exact p.bijective_toDualRight_symm_toDualLeft

include p in
@[deprecated Module.IsReflexive.of_isPerfPair (since := "2025-05-27")]
theorem reflexive_right : IsReflexive R N :=
  p.flip.reflexive_left

@[deprecated "No replacement" (since := "2025-05-27")]
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

@[deprecated "No replacement" (since := "2025-05-27")]
instance : LinearEquivClass (PerfectPairing R M N) R M (Dual R N) where
  map_add p m₁ m₂ := p.toLinearMap.map_add m₁ m₂
  map_smulₛₗ p t m := p.toLinearMap.map_smul t m

include p in
@[deprecated Module.finrank_of_isPerfPair (since := "2025-05-27")]
theorem finrank_eq [Module.Finite R M] [Module.Free R M] :
    finrank R M = finrank R N :=
  ((Module.Free.chooseBasis R M).toDualEquiv.trans p.toDualRight.symm).finrank_eq

end PerfectPairing

namespace LinearMap
variable {p : M →ₗ[R] N →ₗ[R] R} [p.IsPerfPair]

variable (p) in
/-- Given a perfect pairing `p` between `M` and `N`, we say a pair of submodules `U` in `M` and
`V` in `N` are perfectly complementary w.r.t. `p` if their dual annihilators are complementary,
using `p` to identify `M` and `N` with dual spaces. -/
structure IsPerfectCompl (U : Submodule R M) (V : Submodule R N) : Prop where
  isCompl_left : IsCompl U (V.dualAnnihilator.map p.toPerfPair.symm)
  isCompl_right : IsCompl V (U.dualAnnihilator.map p.flip.toPerfPair.symm)

namespace IsPerfectCompl
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

end LinearMap

variable [IsReflexive R M]

set_option linter.deprecated false in
/-- A reflexive module has a perfect pairing with its dual. -/
@[deprecated LinearMap.IsPerfPair.id (since := "2025-05-27")]
def IsReflexive.toPerfectPairingDual : PerfectPairing R (Dual R M) M where
  toLinearMap := .id
  bijective_left := bijective_id
  bijective_right := bijective_dual_eval R M

set_option linter.deprecated false in
@[deprecated "No replacement" (since := "2025-05-27")]
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

instance : e.toLinearMap.IsPerfPair where
  bijective_left := e.bijective
  bijective_right := e.flip.bijective

set_option linter.deprecated false in
/-- If `M` is reflexive then a linear equivalence `N ≃ Dual R M` is a perfect pairing. -/
@[deprecated "No replacement" (since := "2025-05-27")]
def toPerfectPairing : PerfectPairing R N M where
  toLinearMap := e
  bijective_left := e.bijective
  bijective_right := e.flip.bijective

end LinearEquiv

set_option linter.deprecated false in
/-- A perfect pairing induces a perfect pairing between dual spaces. -/
@[deprecated "No replacement" (since := "2025-05-27")]
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
