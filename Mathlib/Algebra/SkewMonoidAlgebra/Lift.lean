/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Algebra.Equiv
/-!
# Lemmas about different kinds of "lifts" to `SkewMonoidAlgebra`.
-/

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]
variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom [MulSemiringAction G A] [SMulCommClass G k A] (f : A →ₐ[k] B)
  (g : G →* B) (h_comm : ∀ {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra A G →ₐ[k] B where
  __ := liftNCRingHom (f : A →+* B) g h_comm
  commutes' := by simp [liftNCRingHom]

/- Hypotheses needed for `k`-algebra homomorphism from `SkewMonoidAlgebra k G`-/
variable [MulSemiringAction G k] [SMulCommClass G k k]

variable (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
  `SkewMonoidAlgebra k G →ₐ[k] A`. -/
def lift : (G →* A) ≃ (AlgHom k (SkewMonoidAlgebra k G) A) where
  invFun f := (f : SkewMonoidAlgebra k G →* A).comp  (of k G)
  toFun F := by
    apply liftNCAlgHom (Algebra.ofId k A) F
    simp_rw [show ∀ (g : G) (r : k), g • r = r by
        exact fun _ _ ↦ smul_algebraMap _ (algebraMap k k _)]
    exact Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]

variable {k G A}

theorem lift_apply' (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b ↦ algebraMap k A b * F a := rfl

theorem lift_apply (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b ↦ b • F a := by simp [lift_apply', Algebra.smul_def]

theorem lift_def (F : G →* A) : (lift k G A F : SkewMonoidAlgebra k G → A) =
    liftNC ((algebraMap k A : k →+* A) : k →+ A) F := rfl

@[simp]
theorem lift_symm_apply (F : AlgHom k (SkewMonoidAlgebra k G) A) (x : G) :
    (lift k G A).symm F x = F (single x 1) := rfl

theorem lift_of (F : G →* A) (x) : lift k G A F (of k G x) = F x := by
  rw [of_apply, ← lift_symm_apply, Equiv.symm_apply_apply]

@[simp]
theorem lift_single (F : G →* A) (a b) : lift k G A F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

theorem lift_unique' (F : AlgHom k (SkewMonoidAlgebra k G) A) :
    F = lift k G A ((F : SkewMonoidAlgebra k G →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `SkewMonoidAlgebra k G` by
  its values on `F (single a 1)`. -/
theorem lift_unique (F : AlgHom k (SkewMonoidAlgebra k G) A)
    (f : SkewMonoidAlgebra k G) : F f  = f.sum fun a b ↦ b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`mapDomain f` is an algebra homomorphism between their monoid algebras. -/
@[simps!]
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] [MulSemiringAction G A]
    [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A] {f : F}
    (hf : ∀ (a : G) (x : A), a • x = (f a) • x) :
    SkewMonoidAlgebra A G →ₐ[k] SkewMonoidAlgebra A H where
  __ := mapDomainRingHom hf
  commutes' := by simp [mapDomainRingHom]

end lift

section equivMapDomain

variable [AddCommMonoid k]

/-- Given `f : G ≃ H`, we can map `l : SkewMonoidAlgebra k G` to
`equivMapDomain f l : SkewMonoidAlgebra k H` (computably) by mapping the support forwards
and the function backwards. -/
def equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) : SkewMonoidAlgebra k H where
  toFinsupp := ⟨l.support.map f.toEmbedding, fun a ↦ l.coeff (f.symm a), by simp⟩

@[simp]
theorem coeff_equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) (b : H) :
    (equivMapDomain f l).coeff b = l.coeff (f.symm b) :=
  rfl

lemma toFinsupp_equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) :
    (equivMapDomain f l).toFinsupp = Finsupp.equivMapDomain f l.toFinsupp := rfl

theorem equivMapDomain_eq_mapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) :
    equivMapDomain f l = mapDomain f l := by
  apply toFinsupp_injective
  ext x
  simp_rw [toFinsupp_equivMapDomain, Finsupp.equivMapDomain_apply, toFinsupp_mapDomain,
    Finsupp.mapDomain_equiv_apply]

theorem equivMapDomain_trans {G' G'' : Type*} (f : G ≃ G') (g : G' ≃ G'')
    (l : SkewMonoidAlgebra k G) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by
  ext x; rfl

@[simp]
theorem equivMapDomain_refl (l : SkewMonoidAlgebra k G) : equivMapDomain (Equiv.refl _) l = l := by
  ext x; rfl

@[simp]
theorem equivMapDomain_single (f : G ≃ H) (a : G) (b : k) :
    equivMapDomain f (single a b) = single (f a) b := by
  classical
  apply toFinsupp_injective
  simp_rw [toFinsupp_equivMapDomain, single, Finsupp.equivMapDomain_single]

end equivMapDomain

section domCongr

variable {A : Type*}

/-- Given `AddCommMonoid A` and `e : G ≃ H`, `domCongr e` is the corresponding `Equiv` between
`SkewMonoidAlgebra A G` and `SkewMonoidAlgebra A H`. -/
@[simps apply]
def domCongr [AddCommMonoid A] (e : G ≃ H) : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H where
  toFun        := equivMapDomain e
  invFun       := equivMapDomain e.symm
  left_inv v   := by simp [← equivMapDomain_trans]
  right_inv v  := by simp [← equivMapDomain_trans]
  map_add' a b := by simp [equivMapDomain_eq_mapDomain, map_add]

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `domCongr` as a `LinearEquiv`. -/
def domLCongr [Semiring k] [AddCommMonoid A] [Module k A] (e : G ≃ H) :
    SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H :=
  (domCongr e : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H).toLinearEquiv <| by
    simp only [domCongr_apply]
    intro c x
    simp_rw [equivMapDomain_eq_mapDomain, mapDomain_smul]

variable (k A)

variable [Monoid G] [Monoid H] [Semiring A] [CommSemiring k] [Algebra k A] [MulSemiringAction G A]
  [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]

/-- If `e : G ≃* H` is a multiplicative equivalence between two monoids and
 ` ∀ (a : G) (x : A), a • x = (e a) • x`, then `SkewMonoidAlgebra.domCongr e` is an
  algebra equivalence between their skew monoid algebras. -/
def domCongrAlg {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    SkewMonoidAlgebra A G ≃ₐ[k] SkewMonoidAlgebra A H :=
  AlgEquiv.ofLinearEquiv
    (domLCongr e : SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H)
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g ↦ (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul f g he).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

theorem domCongrAlg_toAlgHom {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).toAlgHom = mapDomainAlgHom k A he :=
  AlgHom.ext <| fun _ ↦ equivMapDomain_eq_mapDomain _ _

@[simp] theorem domCongrAlg_apply {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) (h : H) : (domCongrAlg k A he f).coeff h = f.coeff (e.symm h) :=
  rfl

@[simp] theorem domCongr_support {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) : (domCongrAlg k A he f).support = f.support.map e :=
  rfl

@[simp] theorem domCongr_single {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (g : G) (a : A) : domCongrAlg k A he (single g a) = single (e g) a :=
  equivMapDomain_single ..

theorem domCongr_refl :
    domCongrAlg k A  (e := MulEquiv.refl G) (fun _ _ ↦ rfl) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  aesop

@[simp] theorem domCongr_symm {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).symm = domCongrAlg _ _ (fun a x ↦ by rw [he, MulEquiv.apply_symm_apply]) :=
  rfl

end domCongr

section Submodule

variable [Semiring k] [Monoid G] [MulSemiringAction G k]

variable {V : Type*} [AddCommMonoid V] [Module k V] [Module (SkewMonoidAlgebra k G) V]
  [IsScalarTower k (SkewMonoidAlgebra k G) V]

/-- A submodule over `k` which is stable under scalar multiplication by elements of `G` is a
submodule over `SkewMonoidAlgebra k G` -/
def submoduleOfSmulMem (W : Submodule k V) (h : ∀ (g : G) (v : V), v ∈ W → of k G g • v ∈ W) :
    Submodule (SkewMonoidAlgebra k G) V where
  carrier   := W
  zero_mem' := W.zero_mem'
  add_mem'  := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← sum_single f, sum_def, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ ↦ h g v hv

end Submodule

end SkewMonoidAlgebra
