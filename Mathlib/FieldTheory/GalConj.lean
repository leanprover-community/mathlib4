import Mathbin.FieldTheory.PolynomialGaloisGroup

open Polynomial

open scoped Polynomial BigOperators

namespace MulAction

@[to_additive]
instance (α : Type _) {β : Type _} [Monoid α] [Fintype α] [MulAction α β] [DecidableEq β] (b : β) :
    Fintype (orbit α b) :=
  Set.fintypeRange _

@[to_additive]
instance (α : Type _) {β : Type _} [Group α] [Fintype α] [MulAction α β] [DecidableEq β]
    (x : MulAction.orbitRel.Quotient α β) : Fintype x.orbit :=
  Quotient.recOnSubsingleton' x fun a => Set.fintypeRange _

end MulAction

namespace minpoly

theorem eq_of_algHom_eq {K S T : Type _} [Field K] [Ring S] [Ring T] [Algebra K S] [Algebra K T]
    (f : S →ₐ[K] T) (hf : Function.Injective f) {x : S} {y : T} (hx : IsIntegral K x)
    (h : y = f x) : minpoly K x = minpoly K y :=
  minpoly.unique _ _ (minpoly.monic hx)
    (by rw [h, aeval_alg_hom_apply, minpoly.aeval, AlgHom.map_zero]) fun q q_monic root_q =>
    minpoly.min _ _ q_monic (by rwa [h, aeval_alg_hom_apply, map_eq_zero_iff _ hf] at root_q )
#align minpoly.eq_of_alg_hom_eq minpoly.eq_of_algHom_eq

end minpoly

section HEq

universe u₁ u₂ u₃

namespace FunLike

variable {F F' : Sort u₁} {α α' : Sort u₂} {β : α → Sort u₃} {β' : α' → Sort u₃} [i : FunLike F α β]
  [i' : FunLike F' α' β']

theorem ext_hEq {f : F} {f' : F'} (h₁ : F = F') (h₂ : α = α') (h₃ : HEq β β') (h₄ : HEq i i')
    (h : ∀ x x', HEq x x' → HEq (f x) (f' x')) : HEq f f' :=
  by
  cases h₁; cases h₂; cases h₃; cases h₄
  exact hEq_of_eq (FunLike.ext f f' fun x => eq_of_hEq (h x x HEq.rfl))
#align fun_like.ext_heq FunLike.ext_hEq

theorem congr_hEq {f : F} {f' : F'} {x : α} {x' : α'} (h₁ : HEq f f') (h₂ : HEq x x')
    (h₃ : HEq β β') (h₄ : HEq i i') : HEq (f x) (f' x') := by cases h₁; cases h₂; cases h₃;
  cases h₄; rfl
#align fun_like.congr_heq FunLike.congr_hEq

end FunLike

universe u

theorem cast_heq' {α β α' : Sort u} (h : α = β) {a : α} {a' : α'} (h' : HEq a a') :
    HEq (cast h a) a' := by cases h; cases h'; rfl
#align cast_heq' cast_heq'

end HEq

namespace AlgEquiv

variable {R : Type _} [CommSemiring R] {A₁ A₂ : Type _}

variable [Semiring A₁] [Semiring A₂]

variable [Algebra R A₁] [Algebra R A₂]

variable (e : A₁ ≃ₐ[R] A₂)

theorem symm_apply_eq {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
#align alg_equiv.symm_apply_eq AlgEquiv.symm_apply_eq

end AlgEquiv

namespace IntermediateField

variable (F : Type _) [Field F] {E : Type _} [Field E] [Algebra F E] {α : E}

theorem adjoinRootEquivAdjoin_symm_apply_gen (h : IsIntegral F α) :
    (adjoinRootEquivAdjoin F h).symm (AdjoinSimple.gen F α) = AdjoinRoot.root (minpoly F α) := by
  rw [AlgEquiv.symm_apply_eq, adjoin_root_equiv_adjoin_apply_root]
#align intermediate_field.adjoin_root_equiv_adjoin_symm_apply_gen IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen

end IntermediateField

namespace Polynomial

variable {T : Type _} [CommRing T]

noncomputable abbrev aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] : Multiset S :=
  (p.map (algebraMap T S)).roots
#align polynomial.aroots Polynomial.aroots

theorem aroots_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] :
    p.aroots S = (p.map (algebraMap T S)).roots :=
  rfl
#align polynomial.aroots_def Polynomial.aroots_def

theorem aroots_map (p : T[X]) (S) (A) [CommRing S] [IsDomain S] [Algebra T S] [CommRing A]
    [IsDomain A] [Algebra S A] [Algebra T A] [IsScalarTower T S A] :
    (p.map (algebraMap T S)).aroots A = p.aroots A := by
  rw [aroots_def, map_map, ← IsScalarTower.algebraMap_eq T S A]
#align polynomial.aroots_map Polynomial.aroots_map

end Polynomial

section GalConjClasses

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

def IsGalConj.setoid :=
  MulAction.orbitRel (E ≃ₐ[F] E) E
#align is_gal_conj.setoid IsGalConj.setoid

def GalConjClasses :=
  MulAction.orbitRel.Quotient (E ≃ₐ[F] E) E
#align gal_conj_classes GalConjClasses

attribute [local instance] IsGalConj.setoid

variable {E}

def IsGalConj (x y : E) : Prop :=
  (IsGalConj.setoid F E).R x y
#align is_gal_conj IsGalConj

notation:50 -- need to fix the precedence
x " ≈g[" F "] " y => IsGalConj F x y

instance [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (x y : E) : Decidable (x ≈g[F] y) :=
  Fintype.decidableExistsFintype

instance [DecidableEq E] [Fintype (E ≃ₐ[F] E)] : DecidableEq (GalConjClasses F E) :=
  @Quotient.decidableEq _ (IsGalConj.setoid F E) (IsGalConj.decidable F)

namespace IsGalConj

instance : IsEquiv E (IsGalConj F) :=
  Quotient.HasEquiv.Equiv.isEquiv

@[refl]
theorem refl (x : E) : x ≈g[F] x :=
  refl x
#align is_gal_conj.refl IsGalConj.refl

@[symm]
theorem symm {x y : E} : (x ≈g[F] y) → y ≈g[F] x :=
  symm
#align is_gal_conj.symm IsGalConj.symm

@[trans]
theorem trans {x y z : E} : (x ≈g[F] y) → (y ≈g[F] z) → x ≈g[F] z :=
  trans
#align is_gal_conj.trans IsGalConj.trans

end IsGalConj

namespace GalConjClasses

def mk (x : E) : GalConjClasses F E :=
  ⟦x⟧
#align gal_conj_classes.mk GalConjClasses.mk

instance : Zero (GalConjClasses F E) :=
  ⟨mk F 0⟩

theorem zero_def : (0 : GalConjClasses F E) = mk F 0 :=
  rfl
#align gal_conj_classes.zero_def GalConjClasses.zero_def

variable {F}

noncomputable def out (c : GalConjClasses F E) : E :=
  c.out
#align gal_conj_classes.out GalConjClasses.out

@[simp]
theorem eq {x y : E} : mk F x = mk F y ↔ x ≈g[F] y :=
  Quotient.eq'
#align gal_conj_classes.eq GalConjClasses.eq

@[simp]
theorem out_eq (q : GalConjClasses F E) : mk F q.out = q :=
  q.out_eq
#align gal_conj_classes.out_eq GalConjClasses.out_eq

theorem mk_out (x : E) : (mk F x).out ≈ x :=
  Quotient.mk_out x
#align gal_conj_classes.mk_out GalConjClasses.mk_out

theorem mk_eq_iff_out {x : E} {c : GalConjClasses F E} : mk F x = c ↔ x ≈g[F] c.out :=
  Quotient.mk_eq_iff_out
#align gal_conj_classes.mk_eq_iff_out GalConjClasses.mk_eq_iff_out

theorem eq_mk_iff_out {c : GalConjClasses F E} {x : E} : c = mk F x ↔ c.out ≈g[F] x :=
  Quotient.eq_mk_iff_out
#align gal_conj_classes.eq_mk_iff_out GalConjClasses.eq_mk_iff_out

@[simp]
theorem out_equiv_out {c₁ c₂ : GalConjClasses F E} : (c₁.out ≈g[F] c₂.out) ↔ c₁ = c₂ :=
  @Quotient.out_equiv_out _ _ c₁ c₂
#align gal_conj_classes.out_equiv_out GalConjClasses.out_equiv_out

theorem equiv_zero_iff (x : E) : (x ≈g[F] 0) ↔ x = 0 :=
  by
  refine' ⟨fun h => _, fun h => by rw [h]⟩
  cases' h with a ha
  simp_rw [← ha, AlgEquiv.smul_def, map_zero]
#align gal_conj_classes.equiv_zero_iff GalConjClasses.equiv_zero_iff

theorem out_eq_zero_iff (c : GalConjClasses F E) : c.out = 0 ↔ c = 0 := by
  rw [zero_def, eq_mk_iff_out, equiv_zero_iff]
#align gal_conj_classes.out_eq_zero_iff GalConjClasses.out_eq_zero_iff

theorem zero_out : (0 : GalConjClasses F E).out = 0 :=
  (out_eq_zero_iff 0).mpr rfl
#align gal_conj_classes.zero_out GalConjClasses.zero_out

theorem mk_eq_zero_iff (x : E) : mk F x = 0 ↔ x = 0 := by
  rw [mk_eq_iff_out, zero_out, equiv_zero_iff]
#align gal_conj_classes.mk_eq_zero_iff GalConjClasses.mk_eq_zero_iff

theorem mk_zero : mk F (0 : E) = 0 :=
  (mk_eq_zero_iff 0).mpr rfl
#align gal_conj_classes.mk_zero GalConjClasses.mk_zero

def orbit (c : GalConjClasses F E) : Set E :=
  c.orbit
#align gal_conj_classes.orbit GalConjClasses.orbit

instance [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (c : GalConjClasses F E) : Fintype c.orbit :=
  Quotient.recOnSubsingleton' c fun a => Set.fintypeRange _

theorem mem_orbit {x : E} {c : GalConjClasses F E} : x ∈ c.orbit ↔ mk F x = c :=
  MulAction.orbitRel.Quotient.mem_orbit
#align gal_conj_classes.mem_orbit GalConjClasses.mem_orbit

theorem orbit_zero : (0 : GalConjClasses F E).orbit = {0} := by ext; rw [mem_orbit, mk_eq_zero_iff];
  rfl
#align gal_conj_classes.orbit_zero GalConjClasses.orbit_zero

instance : Neg (GalConjClasses F E) :=
  ⟨Quotient.lift (fun x : E => mk F (-x))
      (by
        rintro _ y ⟨f, rfl⟩; rw [Eq]
        use f; change f (-y) = -f y; rw [AlgEquiv.map_neg])⟩

theorem mk_neg (x : E) : mk F (-x) = -mk F x :=
  rfl
#align gal_conj_classes.mk_neg GalConjClasses.mk_neg

instance : InvolutiveNeg (GalConjClasses F E) :=
  { (inferInstance : Neg (GalConjClasses F E)) with
    neg_neg := fun x => by rw [← out_eq x, ← mk_neg, ← mk_neg, neg_neg] }

theorem exist_mem_orbit_add_eq_zero (x y : GalConjClasses F E) :
    (∃ a b : E, (a ∈ x.orbit ∧ b ∈ y.orbit) ∧ a + b = 0) ↔ x = -y :=
  by
  simp_rw [mem_orbit]
  constructor
  · rintro ⟨a, b, ⟨rfl, rfl⟩, h⟩
    rw [← mk_neg, Eq, add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    refine' ⟨-y.out, y.out, _⟩
    simp_rw [mk_neg, out_eq, neg_add_self, eq_self_iff_true, true_and_iff]
#align gal_conj_classes.exist_mem_orbit_add_eq_zero GalConjClasses.exist_mem_orbit_add_eq_zero

variable [IsSeparable F E]

noncomputable def minpoly : GalConjClasses F E → F[X] :=
  Quotient.lift (minpoly F) fun (a b : E) ⟨f, h⟩ =>
    minpoly.eq_of_algHom_eq f.symm.toAlgHom f.symm.Injective (IsSeparable.isIntegral F a)
      (h ▸ (f.symm_apply_apply b).symm)
#align gal_conj_classes.minpoly GalConjClasses.minpoly

theorem minpoly_mk (x : E) : minpoly (mk F x) = minpoly F x :=
  rfl
#align gal_conj_classes.minpoly_mk GalConjClasses.minpoly_mk

theorem minpoly_out (c : GalConjClasses F E) : minpoly F c.out = minpoly c := by
  rw [← c.out_eq, minpoly_mk, c.out_eq]
#align gal_conj_classes.minpoly_out GalConjClasses.minpoly_out

theorem minpoly.monic (c : GalConjClasses F E) : (minpoly c).Monic := by
  rw [← c.out_eq, minpoly_mk]; exact minpoly.monic (IsSeparable.isIntegral F _)
#align gal_conj_classes.minpoly.monic GalConjClasses.minpoly.monic

theorem minpoly.ne_zero (c : GalConjClasses F E) : minpoly c ≠ 0 := by rw [← c.out_eq, minpoly_mk];
  exact minpoly.ne_zero (IsSeparable.isIntegral F _)
#align gal_conj_classes.minpoly.ne_zero GalConjClasses.minpoly.ne_zero

theorem minpoly.irreducible (c : GalConjClasses F E) : Irreducible (minpoly c) := by
  rw [← c.out_eq, minpoly_mk]; exact minpoly.irreducible (IsSeparable.isIntegral F _)
#align gal_conj_classes.minpoly.irreducible GalConjClasses.minpoly.irreducible

theorem minpoly.splits [n : Normal F E] (c : GalConjClasses F E) :
    Splits (algebraMap F E) (minpoly c) := by rw [← c.out_eq, minpoly_mk]; exact n.splits c.out
#align gal_conj_classes.minpoly.splits GalConjClasses.minpoly.splits

theorem minpoly.separable (c : GalConjClasses F E) : Separable (minpoly c) := by
  rw [← c.out_eq, minpoly_mk]; exact IsSeparable.separable F c.out
#align gal_conj_classes.minpoly.separable GalConjClasses.minpoly.separable

theorem minpoly.inj [Normal F E] {c d : GalConjClasses F E} (h : minpoly c = minpoly d) : c = d :=
  by
  let fc := IntermediateField.adjoinRootEquivAdjoin F (IsSeparable.isIntegral F c.out)
  let fd := IntermediateField.adjoinRootEquivAdjoin F (IsSeparable.isIntegral F d.out)
  let congr_f : AdjoinRoot (_root_.minpoly F c.out) ≃ₐ[F] AdjoinRoot (_root_.minpoly F d.out) := by
    rw [minpoly_out, minpoly_out, h]
  have congr_f_apply : ∀ x, HEq (congr_f x) x :=
    by
    intro x; change HEq (congr_f x) ((AlgEquiv.refl : _ ≃ₐ[F] _) x)
    dsimp only [congr_f]
    refine' FunLike.congr_hEq _ HEq.rfl _ _
    · simp_rw [eq_mpr_eq_cast, cast_cast]
      refine' cast_heq' _ (FunLike.ext_hEq _ _ _ _ _)
      any_goals rw [minpoly_out, h]
      rintro x₁ x₂ rfl; rfl
    all_goals rw [minpoly_out, minpoly_out, h]
  let f' := fc.symm.trans (congr_f.trans fd)
  let f := f'.lift_normal E
  rw [← out_equiv_out]
  refine' ⟨f.symm, _⟩
  dsimp only [f, AlgEquiv.smul_def]
  simp_rw [AlgEquiv.symm_apply_eq, ← IntermediateField.AdjoinSimple.algebraMap_gen F c.out, ←
    IntermediateField.AdjoinSimple.algebraMap_gen F d.out, AlgEquiv.liftNormal_commutes]
  apply congr_arg
  simp_rw [f', AlgEquiv.trans_apply, ← fd.symm_apply_eq, fc, fd,
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
  refine' eq_of_hEq (HEq.trans _ (congr_f_apply _).symm)
  rw [minpoly_out, minpoly_out, h]
#align gal_conj_classes.minpoly.inj GalConjClasses.minpoly.inj

theorem minpoly.injective [Normal F E] : Function.Injective (@minpoly F _ E _ _ _) := fun x y =>
  minpoly.inj
#align gal_conj_classes.minpoly.injective GalConjClasses.minpoly.injective

theorem minpoly.nodup_aroots (c : GalConjClasses F E) : ((minpoly c).aroots E).Nodup :=
  nodup_roots (minpoly.separable c).map
#align gal_conj_classes.minpoly.nodup_aroots GalConjClasses.minpoly.nodup_aroots

theorem aeval_minpoly_iff [Normal F E] (x : E) (c : GalConjClasses F E) :
    aeval x (minpoly c) = 0 ↔ mk F x = c := by
  symm; constructor; · rintro rfl; exact minpoly.aeval _ _
  intro h
  apply minpoly.inj
  rw [minpoly_mk, ← minpoly.eq_of_irreducible (minpoly.irreducible c) h]
  rw [(minpoly.monic c).leadingCoeff, inv_one, map_one, mul_one]
#align gal_conj_classes.aeval_minpoly_iff GalConjClasses.aeval_minpoly_iff

theorem rootSet_minpoly_eq_orbit [Normal F E] (c : GalConjClasses F E) :
    (minpoly c).rootSet E = c.orbit := by
  ext x; rw [mem_orbit]
  simp_rw [mem_root_set, aeval_minpoly_iff x c]
  simp [minpoly.ne_zero c]
#align gal_conj_classes.root_set_minpoly_eq_orbit GalConjClasses.rootSet_minpoly_eq_orbit

theorem aroots_minpoly_eq_orbit_val [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) : (minpoly c).aroots E = c.orbit.toFinset.1 :=
  by
  simp_rw [← root_set_minpoly_eq_orbit, root_set_def, Finset.toFinset_coe, Multiset.toFinset_val]
  symm; rw [Multiset.dedup_eq_self]
  exact nodup_roots ((separable_map _).mpr (minpoly.separable c))
#align gal_conj_classes.aroots_minpoly_eq_orbit_val GalConjClasses.aroots_minpoly_eq_orbit_val

theorem orbit_eq_mk_aroots_minpoly [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) : c.orbit.toFinset = ⟨(minpoly c).aroots E, minpoly.nodup_aroots c⟩ :=
  by simpa only [aroots_minpoly_eq_orbit_val]
#align gal_conj_classes.orbit_eq_mk_aroots_minpoly GalConjClasses.orbit_eq_mk_aroots_minpoly

theorem minpoly.map_eq_prod [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) :
    (minpoly c).map (algebraMap F E) = ∏ x in c.orbit.toFinset, (X - C x) :=
  by
  simp_rw [← root_set_minpoly_eq_orbit, Finset.prod_eq_multiset_prod, root_set_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [multiset.dedup_eq_self.mpr (nodup_roots _),
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic.map _ _)]
  · rw [splits_iff_card_roots.mp]; rw [splits_id_iff_splits]; exact minpoly.splits c
  · exact minpoly.monic c
  · exact (minpoly.separable c).map
#align gal_conj_classes.minpoly.map_eq_prod GalConjClasses.minpoly.map_eq_prod

end GalConjClasses

end GalConjClasses
