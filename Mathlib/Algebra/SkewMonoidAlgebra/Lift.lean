/-
Copyright (c) 2024 María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Lemmas about different kinds of "lifts" to `SkewMonoidAlgebra`.
-/

noncomputable section

namespace SkewMonoidAlgebra

universe u₁ u₂

variable {k : Type u₁} {G : Type u₂} {H : Type*} {R : Type*}

section lift

variable [CommSemiring k] [Monoid G] [Monoid H] [MulSemiringAction G k] [MulSemiringAction H k]
variable {A : Type*} [Semiring A] [Algebra k A] {B : Type*} [Semiring B] [Algebra k B]
variable [MulSemiringAction G A]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` and
  `∀ {x y}, (f (y • x)) * g y = (g y) * (f x)`.-/
def liftNCAlgHom (f : A →ₐ[k] B) (g : G →* B) (h_comm : ∀ {x y}, (f (y • x)) * g y = (g y) * (f x))
    [SMulCommClass G k A] : AlgHom k (SkewMonoidAlgebra A G) B := by
  use liftNCRingHom (f : A →+* B) g h_comm
  simp [liftNCRingHom]

/- Hypothesis needed for `k`-algebra homomorphism from `SkewMonoidAlgebra k G`-/
variable [SMulCommClass G k k]

/-- A `k`-algebra homomorphism from `SkewMonoidAlgebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
theorem algHom_ext ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄
    (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
    AlgHom.toLinearMap_injective (lhom_ext' fun a => (LinearMap.ext_ring (h a)))

@[ext high]
theorem algHom_ext' ⦃φ₁ φ₂ : AlgHom k (SkewMonoidAlgebra k G) A⦄
    (h : (φ₁ : SkewMonoidAlgebra k G →* A).comp (of k G) =
      (φ₂ : SkewMonoidAlgebra k G →* A).comp (of k G)) :
    φ₁ = φ₂ :=  algHom_ext <| DFunLike.congr_fun h

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
    lift k G A F f = f.sum fun a b => algebraMap k A b * F a := rfl

theorem lift_apply (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b => b • F a := by simp only [lift_apply', Algebra.smul_def]

theorem lift_def (F : G →* A) : ⇑(lift k G A F) =
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
    (f : SkewMonoidAlgebra k G) : F f  = f.sum fun a b => b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

theorem mapDomain_algebraMap {F : Type*} [FunLike F G H] [MonoidHomClass F G H]
    [MulSemiringAction G A] [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]
    (f : F) (r : k) : mapDomain f (algebraMap k (SkewMonoidAlgebra A G) r) =
      algebraMap k (SkewMonoidAlgebra A H) r := by
  simp only [coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`mapDomain f` is an algebra homomorphism between their monoid algebras. -/
@[simps!]
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] [MulSemiringAction G A]
    [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A] {f : F}
    (hf : ∀ (a : G) (x : A), a • x = (f a) • x) :
    SkewMonoidAlgebra A G →ₐ[k] SkewMonoidAlgebra A H where
  __ := mapDomainRingHom hf
  commutes' := mapDomain_algebraMap f

end lift

section equivMapDomain

variable [AddCommMonoid k]

/-- Given `f : G ≃ H`, we can map `l : SkewMonoidAlgebra k G` to
`equivMapDomain f l : SkewMonoidAlgebra k H` (computably) by mapping the support forwards
and the function backwards. -/
def equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) : SkewMonoidAlgebra k H where
  toFinsupp := ⟨l.support.map f.toEmbedding, fun a ↦ l.coeff (f.symm a),
    by simp only [Finset.mem_map_equiv, mem_support_iff, ne_eq, implies_true]⟩

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
  simp only [toFinsupp_equivMapDomain, Finsupp.equivMapDomain_apply, toFinsupp_mapDomain,
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
`SkewMonoidAlgebra A G` and `SkewMonoidAlgebra A H`.-/
@[simps apply]
def domCongr [AddCommMonoid A] (e : G ≃ H) : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H where
  toFun        := equivMapDomain e
  invFun       := equivMapDomain e.symm
  left_inv v   := by simp only [← equivMapDomain_trans, Equiv.self_trans_symm, equivMapDomain_refl]
  right_inv v  := by simp only [← equivMapDomain_trans, Equiv.symm_trans_self, equivMapDomain_refl]
  map_add' a b := by simp only [equivMapDomain_eq_mapDomain, mapDomain_add]

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `domCongr` as a `LinearEquiv`. -/
def domLCongr [Semiring k] [AddCommMonoid A] [Module k A] (e : G ≃ H) :
    SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H :=
  (domCongr e : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H).toLinearEquiv <| by
    simp only [domCongr_apply]
    intro c x
    simp only [equivMapDomain_eq_mapDomain, mapDomain_smul]

variable (k A)

variable [Monoid G] [Monoid H] [Semiring A] [CommSemiring k] [Algebra k A] [MulSemiringAction G A]
  [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]

/-- If `e : G ≃* H` is a multiplicative equivalence between two monoids and
 ` ∀ (a : G) (x : A), a • x = (e a) • x`, then `SkewMonoidAlgebra.domCongr e` is an
  algebra equivalence between their skew monoid algebras. -/
def domCongrAlg  {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    SkewMonoidAlgebra A G ≃ₐ[k] SkewMonoidAlgebra A H :=
  AlgEquiv.ofLinearEquiv
    (domLCongr e : SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H)
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g => (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul f g he).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

theorem domCongrAlg_toAlgHom {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).toAlgHom = mapDomainAlgHom k A he :=
  AlgHom.ext <| fun _ => equivMapDomain_eq_mapDomain _ _

@[simp] theorem domCongrAlg_apply {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) (h : H) : (domCongrAlg k A he f).coeff h = f.coeff (e.symm h) :=
  rfl

@[simp] theorem domCongr_support [MulSemiringAction G A] [MulSemiringAction H A]
    [SMulCommClass G k A] [SMulCommClass H k A] {e : G ≃* H}
    (he : ∀ (a : G) (x : A), a • x = (e a) • x) (f : SkewMonoidAlgebra A G) :
    (domCongrAlg k A he f).support = f.support.map e :=
  rfl

@[simp] theorem domCongr_single [MulSemiringAction G A] [MulSemiringAction H A]
    [SMulCommClass G k A] [SMulCommClass H k A] {e : G ≃* H}
    (he : ∀ (a : G) (x : A), a • x = (e a) • x) (g : G) (a : A) :
    domCongrAlg k A he (single g a) = single (e g) a := equivMapDomain_single _ _ _

theorem domCongr_refl [MulSemiringAction G A] [SMulCommClass G k A] :
    @domCongrAlg k _ _ A _ _ _ _ _ _ _ _ _ (MulEquiv.refl G) (fun _ _ => rfl) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  intro a
  ext
  simp only [domCongrAlg_apply, MulEquiv.refl_symm, MulEquiv.refl_apply, AlgEquiv.coe_refl, id_eq]

@[simp] theorem domCongr_symm [MulSemiringAction G A] [MulSemiringAction H A]
    [SMulCommClass G k A] [SMulCommClass H k A] {e : G ≃* H}
    (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).symm = @domCongrAlg k _ _ A _ _ _ _ _ _ _ _ _ e.symm
      (fun a x => by rw [he, MulEquiv.apply_symm_apply]) := rfl

end domCongr

section erase

variable {M α : Type*}

/--
`erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to `0`.
If `a` is not in the support of `f` then `erase a f = f`.
-/
def erase [AddCommMonoid M] (a : α) (f : SkewMonoidAlgebra M α) : SkewMonoidAlgebra M α where
  toFinsupp :=
    ⟨ haveI := Classical.decEq α
      f.support.erase a,
      fun a' ↦ haveI := Classical.decEq α
        if a' = a then 0 else f.coeff a', by
      classical
      intro a
      simp only [Finset.mem_erase, mem_support_iff, ne_eq]
      split_ifs with h
      · exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩
      · exact and_iff_right h⟩

@[simp]
theorem toFinsupp_erase [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a : α) :
    (f.erase a).toFinsupp = f.toFinsupp.erase a := rfl

@[simp]
theorem support_erase [AddCommMonoid M] [DecidableEq α] {a : α} {f : SkewMonoidAlgebra M α} :
    (f.erase a).support = f.support.erase a := by
  rcases f with ⟨⟩
  ext
  simp only [support, erase, Finsupp.support_erase, Finset.mem_erase, Finsupp.mem_support_iff]

theorem single_add_erase [AddCommMonoid M] (a : α) (f : SkewMonoidAlgebra M α) :
    single a (f.coeff a) + f.erase a = f := by
  apply toFinsupp_injective
  simp only [single, ← toFinsupp_apply, toFinsupp_add, toFinsupp_erase]
  rw [Finsupp.single_add_erase]

@[elab_as_elim]
theorem induction [AddCommMonoid M] {p : SkewMonoidAlgebra M α → Prop}
    (f : SkewMonoidAlgebra M α) (h0 : p 0)
    (ha : ∀ (a b) (f : SkewMonoidAlgebra M α), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
    p f :=
  suffices ∀ (s) (f : SkewMonoidAlgebra M α), f.support = s → p f from this _ _ rfl
  fun s =>
  Finset.cons_induction_on s (fun f hf => by rwa [support_eq_empty.1 hf]) fun a s has ih f hf => by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [single_add_erase] at this
    classical
    apply ha
    · rw [support_erase, Finset.mem_erase]
      exact fun H => H.1 rfl
    · simp only [← mem_support_iff, hf, Finset.mem_cons_self]
    · apply ih _ _
      rw [support_erase, hf, Finset.erase_cons]

variable [Monoid G] [CommSemiring k] {V W : Type*} [AddCommMonoid V] [Module k V]
  [MulSemiringAction G k] [Module (SkewMonoidAlgebra k G) V]
  [IsScalarTower k (SkewMonoidAlgebra k G) V] [AddCommMonoid W] [Module k W]
  [Module (SkewMonoidAlgebra k G) W] [IsScalarTower k (SkewMonoidAlgebra k G) W] (f : V →ₗ[k] W)
  (h : ∀ (g : G) (v : V), f (single g (1 : k) • v) = single g (1 : k) • f v)

/-- Build a `k[G]`-linear map from a `k`-linear map and evidence that it is `G`-equivariant. -/
def equivariantOfLinearOfComm [SMulCommClass G k k] : V →ₗ[SkewMonoidAlgebra k G] W where
  toFun         := f
  map_add'      := map_add _
  map_smul' c v := by
    dsimp only
    refine induction c ?_ ?_
    · simp only [zero_smul, map_zero]
    · intro g r c' _nm _nz w
      dsimp only [RingHom.id_apply] at w ⊢
      simp only [add_smul, f.map_add, w, add_left_inj, single_eq_algebraMap_mul_of, ← smul_smul]
      erw [algebraMap_smul (SkewMonoidAlgebra k G) r, algebraMap_smul (SkewMonoidAlgebra k G) r,
        f.map_smul, h g v, of_apply]

@[simp]
theorem equivariantOfLinearOfComm_apply [SMulCommClass G k k] (v : V) :
    (equivariantOfLinearOfComm f h) v = f v :=
  rfl

end erase

section Submodule

variable [CommSemiring k] [Monoid G] [MulSemiringAction G k]

variable {V : Type*} [AddCommMonoid V]

variable [Module k V] [Module (SkewMonoidAlgebra k G) V] [IsScalarTower k (SkewMonoidAlgebra k G) V]

/-- A submodule over `k` which is stable under scalar multiplication by elements of `G` is a
submodule over `SkewMonoidAlgebra k G`  -/
def submoduleOfSmulMem (W : Submodule k V) (h : ∀ (g : G) (v : V), v ∈ W → of k G g • v ∈ W) :
    Submodule (SkewMonoidAlgebra k G) V where
  carrier   := W
  zero_mem' := W.zero_mem'
  add_mem'  := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← sum_single f, toFinsupp_sum, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ => h g v hv

end Submodule

end SkewMonoidAlgebra

end
