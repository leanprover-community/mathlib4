/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.BaseChange
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

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
 * `PerfectPairing.restrict`
 * `PerfectPairing.restrictScalars`
 * `LinearEquiv.flip`
 * `LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive`
 * `LinearEquiv.toPerfectPairing`

-/

open Function Module

noncomputable section

variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A perfect pairing of two (left) modules over a commutative ring. -/
structure PerfectPairing where
  toLin : M →ₗ[R] N →ₗ[R] R
  bijectiveLeft : Bijective toLin
  bijectiveRight : Bijective toLin.flip

attribute [nolint docBlame] PerfectPairing.toLin

variable {R M N}

namespace PerfectPairing

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear form. -/
def mkOfInjective {K V W : Type*}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (B : V →ₗ[K] W →ₗ[K] K)
    (h : Injective B)
    (h' : Injective B.flip) :
    PerfectPairing K V W where
  toLin := B
  bijectiveLeft := ⟨h, by rwa [← B.flip_injective_iff₁]⟩
  bijectiveRight := ⟨h', by
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
  toLin := B
  bijectiveLeft := ⟨h, by
    have : FiniteDimensional K V := FiniteDimensional.of_injective B h
    rwa [← B.flip_injective_iff₁]⟩
  bijectiveRight := ⟨h', by rwa [← B.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

instance instFunLike : FunLike (PerfectPairing R M N) M (N →ₗ[R] R) where
  coe f := f.toLin
  coe_injective' x y h := by cases x; cases y; simpa using h

@[simp]
lemma toLin_apply (p : PerfectPairing R M N) {x : M} : p.toLin x = p x := by
  rfl

variable (p : PerfectPairing R M N)

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
protected def flip : PerfectPairing R N M where
  toLin := p.toLin.flip
  bijectiveLeft := p.bijectiveRight
  bijectiveRight := p.bijectiveLeft

@[simp]
lemma flip_apply_apply {x : M} {y : N} : p.flip y x = p x y :=
  rfl

@[simp]
lemma flip_flip : p.flip.flip = p :=
  rfl

/-- The linear equivalence from `M` to `Dual R N` induced by a perfect pairing. -/
def toDualLeft : M ≃ₗ[R] Dual R N :=
  LinearEquiv.ofBijective p.toLin p.bijectiveLeft

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

include p in
theorem finrank_eq [Module.Finite R M] [Module.Free R M] :
    finrank R M = finrank R N :=
  ((Module.Free.chooseBasis R M).toDualEquiv.trans p.toDualRight.symm).finrank_eq

private lemma restrict_aux
    {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (i : M' →ₗ[R] M) (j : N' →ₗ[R] N)
    (hM : IsCompl (LinearMap.range i) ((LinearMap.range j).dualAnnihilator.map p.toDualLeft.symm))
    (hN : IsCompl (LinearMap.range j) ((LinearMap.range i).dualAnnihilator.map p.toDualRight.symm))
    (hi : Injective i) (hj : Injective j) :
    Bijective (p.toLin.compl₁₂ i j) := by
  refine ⟨LinearMap.ker_eq_bot.mp <| eq_bot_iff.mpr fun m hm ↦ ?_, fun f ↦ ?_⟩
  · replace hm : i m ∈ (LinearMap.range j).dualAnnihilator.map p.toDualLeft.symm := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      refine ⟨p.toDualLeft (i m), ?_, LinearEquiv.symm_apply_apply _ _⟩
      rintro - ⟨n, rfl⟩
      simpa using LinearMap.congr_fun hm n
    suffices i m ∈ (⊥ : Submodule R M) by simpa [hi] using this
    simpa only [← hM.inf_eq_bot, Submodule.mem_inf] using ⟨LinearMap.mem_range_self i m, hm⟩
  · set F : Module.Dual R N := f ∘ₗ j.linearProjOfIsCompl _ hj hN with hF
    have hF (n : N') : F (j n) = f n := by simp [hF]
    set m : M := p.toDualLeft.symm F with hm
    obtain ⟨-, ⟨m₀, rfl⟩, y, hy, hm'⟩ := Submodule.exists_add_eq_of_codisjoint hM.codisjoint m
    refine ⟨m₀, LinearMap.ext fun n ↦ ?_⟩
    replace hy : (p y) (j n) = 0 := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      simpa only [apply_toDualLeft_symm_apply] using hg _ (LinearMap.mem_range_self j n)
    rw [hm, ← LinearEquiv.symm_apply_eq, map_add, LinearEquiv.symm_symm,
      toDualLeft_apply] at hm'
    simpa [← hF, ← LinearMap.congr_fun hm' (j n)]

/-- The restriction of a perfect pairing to submodules (expressed as injections to provide
definitional control). -/
@[simps]
def restrict {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    (i : M' →ₗ[R] M) (j : N' →ₗ[R] N)
    (hM : IsCompl (LinearMap.range i) ((LinearMap.range j).dualAnnihilator.map p.toDualLeft.symm))
    (hN : IsCompl (LinearMap.range j) ((LinearMap.range i).dualAnnihilator.map p.toDualRight.symm))
    (hi : Injective i) (hj : Injective j) :
    PerfectPairing R M' N' where
  toLin := p.toLin.compl₁₂ i j
  bijectiveLeft := p.restrict_aux i j hM hN hi hj
  bijectiveRight := p.flip.restrict_aux j i hN hM hj hi

section RestrictScalars

open Submodule (span)

/-- If a perfect pairing over a field `L` takes values in a subfield `K` along two `K`-subspaces
whose `L` span is full, then these subspaces induce a `K`-structure in the sense of
[*Algebra I*, Bourbaki : Chapter II, §8.1 Definition 1][bourbaki1989]. -/
lemma exists_basis_basis_of_span_eq_top_of_mem_algebraMap
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Module L M] [Module L N] [Module K M] [Module K N] [IsScalarTower K L M]
    (p : PerfectPairing L M N)
    (M' : Submodule K M) (N' : Submodule K N)
    (hM : span L (M' : Set M) = ⊤)
    (hN : span L (N' : Set N) = ⊤)
    (hp : ∀ᵉ (x ∈ M') (y ∈ N'), p x y ∈ (algebraMap K L).range) :
    ∃ (n : ℕ) (b : Basis (Fin n) L M) (b' : Basis (Fin n) K M'), ∀ i, b i = b' i := by
  classical
  have : IsReflexive L M := p.reflexive_left
  have : IsReflexive L N := p.reflexive_right
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_linearIndependent L (M' : Set M)
  rw [hM] at hv₂
  let b : Basis _ L M := Basis.mk hv₃ <| by rw [← hv₂, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  have : Fintype v := Set.Finite.fintype <| Module.Finite.finite_basis b
  set v' : v → M' := fun i ↦ ⟨i, hv₁ (Subtype.coe_prop i)⟩
  have hv' : LinearIndependent K v' := by
    replace hv₃ := hv₃.restrict_scalars (R := K) <| by
      simp_rw [← Algebra.algebraMap_eq_smul_one]
      exact NoZeroSMulDivisors.algebraMap_injective K L
    rw [show ((↑) : v → M) = M'.subtype ∘ v' from rfl] at hv₃
    exact hv₃.of_comp
  suffices span K (Set.range v') = ⊤ by
    let e := (Module.Finite.finite_basis b).equivFin
    let b' : Basis _ K M' := Basis.mk hv' (by rw [this])
    exact ⟨_, b.reindex e, b'.reindex e, fun i ↦ by simp [b, b']⟩
  suffices span K v = M' by
    apply Submodule.map_injective_of_injective M'.injective_subtype
    rw [Submodule.map_span, ← Set.image_univ, Set.image_image]
    simpa
  refine le_antisymm (Submodule.span_le.mpr hv₁) fun m hm ↦ ?_
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := exists_linearIndependent L (N' : Set N)
  rw [hN] at hw₂
  let bN : Basis _ L N := Basis.mk hw₃ <| by rw [← hw₂, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  have : Fintype w := Set.Finite.fintype <| Module.Finite.finite_basis bN
  have e : v ≃ w := Fintype.equivOfCardEq <| by rw [← Module.finrank_eq_card_basis b,
    ← Module.finrank_eq_card_basis bN, p.finrank_eq]
  let bM := bN.dualBasis.map p.toDualLeft.symm
  have hbM (j : w) (x : M) (hx : x ∈ M') : bM.repr x j = p x (j : N) := by simp [bM, bN]
  have hj (j : w) : bM.repr m j ∈ (algebraMap K L).range := (hbM _ _ hm) ▸ hp m hm j (hw₁ j.2)
  replace hp (i : w) (j : v) :
      (bN.dualBasis.map p.toDualLeft.symm).toMatrix b i j ∈ (algebraMap K L).fieldRange := by
    simp only [Basis.toMatrix, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      toDualLeft_apply, Basis.dualBasis_repr]
    exact hp (b j) (by simpa [b] using hv₁ j.2) (bN i) (by simpa [bN] using hw₁ i.2)
  have hA (i j) : b.toMatrix bM i j ∈ (algebraMap K L).range :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left e _ (by simp) hp i j
  have h_span : span K v = span K (Set.range b) := by simp [b]
  rw [h_span, Basis.mem_span_iff_repr_mem, ← Basis.toMatrix_mulVec_repr bM b m]
  exact fun i ↦ Subring.sum_mem _ fun j _ ↦ Subring.mul_mem _ (hA i j) (hj j)

variable {S : Type*}
  [CommRing S] [Algebra S R] [Module S M] [Module S N] [IsScalarTower S R M] [IsScalarTower S R N]
  [NoZeroSMulDivisors S R] [Nontrivial R]
  {M' N' : Type*} [AddCommGroup M'] [Module S M'] [AddCommGroup N'] [Module S N']
  (i : M' →ₗ[S] M) (j : N' →ₗ[S] N)

/-- An auxiliary definition used to constuct `PerfectPairing.restrictScalars`. -/
private def restrictScalarsAux
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    M' →ₗ[S] N' →ₗ[S] S :=
 LinearMap.restrictScalarsRange i j (Algebra.linearMap S R)
    (NoZeroSMulDivisors.algebraMap_injective S R) p.toLin hp

private lemma restrictScalarsAux_injective
    (hi : Injective i)
    (hN : span R (LinearMap.range j : Set N) = ⊤)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    Injective (p.restrictScalarsAux i j hp) := by
  let f := LinearMap.restrictScalarsRange i j (Algebra.linearMap S R)
      (NoZeroSMulDivisors.algebraMap_injective S R) p.toLin hp
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x (hx : f x = 0) ↦ ?_
  replace hx (n : N) : p (i x) n = 0 := by
    have hn : n ∈ span R (LinearMap.range j : Set N) := hN ▸ Submodule.mem_top
    induction' hn using Submodule.span_induction with z hz
    · obtain ⟨n', rfl⟩ := hz
      simpa [f] using LinearMap.congr_fun hx n'
    · simp
    · rw [← p.toLin_apply, map_add]; aesop
    · rw [← p.toLin_apply, map_smul]; aesop
  rw [← i.map_eq_zero_iff hi, ← p.toLin.map_eq_zero_iff p.bijectiveLeft.injective]
  ext n
  simpa using hx n

private lemma restrictScalarsAux_surjective
    (h : ∀ g : Module.Dual S N', ∃ m,
      (p.toDualLeft (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    Surjective (p.restrictScalarsAux i j hp) := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.mpr fun g : Module.Dual S N' ↦ ?_
  obtain ⟨m, hm⟩ := h g
  refine ⟨m, ?_⟩
  ext n
  apply NoZeroSMulDivisors.algebraMap_injective S R
  change Algebra.linearMap S R _ = _
  simpa [restrictScalarsAux] using LinearMap.congr_fun hm n

/-- Restriction of scalars for a perfect pairing taking values in a subring. -/
def restrictScalars
    (hi : Injective i) (hj : Injective j)
    (hM : span R (LinearMap.range i : Set M) = ⊤)
    (hN : span R (LinearMap.range j : Set N) = ⊤)
    (h₁ : ∀ g : Module.Dual S N', ∃ m,
      (p.toDualLeft (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (h₂ : ∀ g : Module.Dual S M', ∃ n,
      (p.toDualRight (j n)).restrictScalars S ∘ₗ i = Algebra.linearMap S R ∘ₗ g)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap S R).range) :
    PerfectPairing S M' N' :=
  { toLin := p.restrictScalarsAux i j hp
    bijectiveLeft := ⟨p.restrictScalarsAux_injective i j hi hN hp,
      p.restrictScalarsAux_surjective i j h₁ hp⟩
    bijectiveRight := ⟨p.flip.restrictScalarsAux_injective j i hj hM (fun m n ↦ hp n m),
      p.flip.restrictScalarsAux_surjective j i h₂ (fun m n ↦ hp n m)⟩}

/-- Restriction of scalars for a perfect pairing taking values in a subfield. -/
def restrictScalarsField {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Module L M] [Module L N] [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
    [Module K M'] [Module K N']
    (i : M' →ₗ[K] M) (j : N' →ₗ[K] N)
    (hi : Injective i) (hj : Injective j)
    (hM : span L (LinearMap.range i : Set M) = ⊤)
    (hN : span L (LinearMap.range j : Set N) = ⊤)
    (p : PerfectPairing L M N)
    (hp : ∀ m n, p (i m) (j n) ∈ (algebraMap K L).range) :
    PerfectPairing K M' N' := by
  suffices FiniteDimensional K M' from mkOfInjective _ (p.restrictScalarsAux_injective i j hi hN hp)
    (p.flip.restrictScalarsAux_injective j i hj hM (fun m n ↦ hp n m))
  obtain ⟨n, -, b', -⟩ := p.exists_basis_basis_of_span_eq_top_of_mem_algebraMap _ _ hM hN <| by
    rintro - ⟨m, rfl⟩ - ⟨n, rfl⟩
    exact hp m n
  have : FiniteDimensional K (LinearMap.range i) := FiniteDimensional.of_fintype_basis b'
  exact Finite.equiv (LinearEquiv.ofInjective i hi).symm

end RestrictScalars

end PerfectPairing

variable [IsReflexive R M]

/-- A reflexive module has a perfect pairing with its dual. -/
@[simps]
def IsReflexive.toPerfectPairingDual : PerfectPairing R (Dual R M) M where
  toLin := LinearMap.id
  bijectiveLeft := bijective_id
  bijectiveRight := bijective_dual_eval R M

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
@[simps]
def toPerfectPairing : PerfectPairing R N M where
  toLin := e
  bijectiveLeft := e.bijective
  bijectiveRight := e.flip.bijective

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
