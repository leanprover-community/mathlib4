/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.NormalClosure

/-!
TODO
-/

theorem Algebra.IsAlgebraic.tower_bot (K L A) [CommRing K] [Field L] [Ring A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [Nontrivial A] [Algebra.IsAlgebraic K A] :
    Algebra.IsAlgebraic K L :=
  ⟨fun x ↦ by
    simpa [isAlgebraic_algebraMap_iff, (algebraMap L A).injective] using
      Algebra.IsAlgebraic.isAlgebraic (R := K) (A := A) (algebraMap _ _ x)⟩

open Polynomial

open scoped Polynomial BigOperators IntermediateField

variable (F E E' : Type*) [Field F] [Field E] [Algebra F E]
  [Field E'] [Algebra F E'] [Algebra E E'] [IsScalarTower F E E']

instance [Algebra.IsAlgebraic F E] : IsAlgClosure F (AlgebraicClosure E) where
  algebraic := .trans (L := E)
  alg_closed := inferInstance

noncomputable abbrev NormalClosure : Type _ := normalClosure F E (AlgebraicClosure E)

noncomputable irreducible_def NormalClosure.algebraAux [n : Normal F E'] :
    NormalClosure F E →+* E' :=
  let alglift : E' →ₐ[F] AlgebraicClosure E := IsAlgClosed.lift
  haveI : Nonempty (E →ₐ[F] AlgebraicClosure E) := ⟨alglift.comp (IsScalarTower.toAlgHom F _ _)⟩
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.tower_bot _ _ E'
  let aux : NormalClosure F E →ₐ[F] E' := IsNormalClosure.lift (K := E) fun x ↦ by
    simpa [minpoly.algebraMap_eq, (algebraMap E E').injective] using n.splits (algebraMap _ _ x)
  let comp : E →ₐ[F] E' := aux.comp (IsScalarTower.toAlgHom _ _ _)
  ((AlgEquiv.ofBijective (comp.liftNormal E') (AlgHom.normal_bijective F _ _ _)).symm.toAlgHom.comp
    aux).toRingHom

noncomputable instance [Normal F E'] : Algebra (NormalClosure F E) E' :=
  (NormalClosure.algebraAux F E E').toAlgebra

instance [Normal F E'] : IsScalarTower E (NormalClosure F E) E' :=
  .of_algebraMap_eq fun x ↦ by
    change _ = NormalClosure.algebraAux _ _ _ _
    simp [NormalClosure.algebraAux_def, AlgEquiv.eq_symm_apply]

instance [Normal F E'] : IsScalarTower F (NormalClosure F E) E' :=
  .of_algebraMap_eq fun x ↦ by
    change _ = NormalClosure.algebraAux _ _ _ _
    simp [NormalClosure.algebraAux_def, AlgEquiv.eq_symm_apply]

def IsGalConj.setoid :=
  (MulAction.orbitRel (NormalClosure F E ≃ₐ[F] NormalClosure F E) (NormalClosure F E)).comap
    (algebraMap E _)

def GalConjClasses :=
  Quotient (IsGalConj.setoid F E)

variable {E}

def IsGalConj (x y : E) : Prop :=
  (IsGalConj.setoid F E).r x y

scoped[IsGalConj] notation:50 x:51 " ≈g[" F "] " y:51 => IsGalConj F x y

variable {F}

open scoped IsGalConj

lemma isGalConj_iff_algebraMap_normalClosure {x y : E} :
    x ≈g[F] y ↔ ∃ f : NormalClosure F E ≃ₐ[F] NormalClosure F E,
      f (algebraMap _ (NormalClosure F E) y) = algebraMap _ (NormalClosure F E) x :=
  Iff.rfl

lemma isGalConj_iff_algebraMap [Normal F E'] {x y : E} :
    x ≈g[F] y ↔ ∃ f : E' ≃ₐ[F] E', f (algebraMap _ E' y) = algebraMap _ E' x := by
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.tower_bot _ _ E'
  rw [isGalConj_iff_algebraMap_normalClosure]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · refine ⟨f.liftNormal _, ?_⟩
    rw [IsScalarTower.algebraMap_apply E (NormalClosure F E) E',
      AlgEquiv.liftNormal_commutes, hf, ← IsScalarTower.algebraMap_apply]
  · refine ⟨f.restrictNormal _, (algebraMap (NormalClosure F E) E').injective ?_⟩
    rwa [AlgEquiv.restrictNormal_commutes, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]

lemma isGalConj_iff [Normal F E] {x y : E} :
    x ≈g[F] y ↔ ∃ f : E ≃ₐ[F] E, f y = x :=
  isGalConj_iff_algebraMap E

variable (F)

namespace IsGalConj

instance decidable [Normal F E] [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (x y : E) :
    Decidable (x ≈g[F] y) :=
  decidable_of_iff _ isGalConj_iff.symm

instance [Normal F E] [DecidableEq E] [Fintype (E ≃ₐ[F] E)] : DecidableEq (GalConjClasses F E) :=
  @Quotient.decidableEq _ (IsGalConj.setoid F E) (IsGalConj.decidable F)

instance : IsEquiv E (IsGalConj F) :=
  letI := IsGalConj.setoid F E
  inferInstanceAs <| IsEquiv E (· ≈ ·)

@[refl]
nonrec theorem refl (x : E) : x ≈g[F] x :=
  refl x

@[symm]
nonrec theorem symm {x y : E} : (x ≈g[F] y) → y ≈g[F] x :=
  symm

@[trans]
nonrec theorem trans {x y z : E} : (x ≈g[F] y) → (y ≈g[F] z) → x ≈g[F] z :=
  _root_.trans

end IsGalConj

namespace GalConjClasses

def mk (x : E) : GalConjClasses F E :=
  ⟦x⟧

instance : Zero (GalConjClasses F E) :=
  ⟨mk F 0⟩

theorem zero_def : (0 : GalConjClasses F E) = mk F 0 :=
  rfl

@[elab_as_elim, cases_eliminator, induction_eliminator]
lemma ind {motive : GalConjClasses F E → Prop} (h : ∀ x : E, motive (mk F x))
    (c : GalConjClasses F E) : motive c :=
  Quotient.ind h c

variable {F}

noncomputable def out (c : GalConjClasses F E) : E :=
  letI := IsGalConj.setoid F E
  Quotient.out c

@[simp]
theorem mk_eq_mk {x y : E} : mk F x = mk F y ↔ x ≈g[F] y := Quotient.eq''

@[simp]
theorem mk_out (q : GalConjClasses F E) : mk F q.out = q :=
  q.out_eq'

theorem out_isGalConj (x : E) :
    (mk F x).out ≈g[F] x :=
  letI := IsGalConj.setoid F E
  Quotient.mk_out x

theorem mk_eq_iff_out {x : E} {c : GalConjClasses F E} : mk F x = c ↔ x ≈g[F] c.out :=
  letI := IsGalConj.setoid F E
  Quotient.mk_eq_iff_out

theorem eq_mk_iff_out {c : GalConjClasses F E} {x : E} : c = mk F x ↔ c.out ≈g[F] x :=
  letI := IsGalConj.setoid F E
  Quotient.eq_mk_iff_out

@[simp]
theorem out_isGalConj_out {c₁ c₂ : GalConjClasses F E} : c₁.out ≈g[F] c₂.out ↔ c₁ = c₂ :=
  @Quotient.out_equiv_out _ _ c₁ c₂

theorem isGalConj_zero_iff (x : E) : x ≈g[F] 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  cases' h with a ha
  simpa [@eq_comm (NormalClosure _ _) 0] using ha

theorem out_eq_zero_iff (c : GalConjClasses F E) : c.out = 0 ↔ c = 0 := by
  rw [zero_def, eq_mk_iff_out, isGalConj_zero_iff]

theorem zero_out : (0 : GalConjClasses F E).out = 0 :=
  (out_eq_zero_iff 0).mpr rfl

theorem mk_eq_zero_iff (x : E) : mk F x = 0 ↔ x = 0 := by
  rw [mk_eq_iff_out, zero_out, isGalConj_zero_iff]

theorem mk_zero : mk F (0 : E) = 0 :=
  (mk_eq_zero_iff 0).mpr rfl

nonrec def orbit (c : GalConjClasses F E) : Set E :=
  mk F ⁻¹' {c}

theorem mem_orbit {x : E} {c : GalConjClasses F E} : x ∈ c.orbit ↔ mk F x = c :=
  Iff.rfl

instance [Normal F E] [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (c : GalConjClasses F E) :
    DecidablePred (· ∈ c.orbit) :=
  fun x ↦ decidable_of_iff (mk F x = c) (by simp [mem_orbit])

instance [Normal F E] [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (c : GalConjClasses F E) :
    Fintype c.orbit :=
  Quotient.recOnSubsingleton' c fun x =>
    .ofFinset ((Finset.univ (α := E ≃ₐ[F] E)).image (· x)) fun _ ↦ by
      simpa [mem_orbit] using isGalConj_iff.symm.trans (by exact mk_eq_mk.symm)

theorem orbit_zero : (0 : GalConjClasses F E).orbit = {0} := by
  ext; rw [mem_orbit, mk_eq_zero_iff, Set.mem_singleton_iff]

instance : Neg (GalConjClasses F E) :=
  ⟨Quotient.lift (fun x ↦ mk F (-x)) (by
    rintro _ y ⟨f, hf⟩
    rw [mk_eq_mk]
    use f
    simp only [map_neg, smul_neg, hf])⟩

theorem mk_neg (x : E) : mk F (-x) = -mk F x :=
  rfl

instance : InvolutiveNeg (GalConjClasses F E) :=
  { (inferInstance : Neg (GalConjClasses F E)) with
    neg_neg := fun x => by rw [← mk_out x, ← mk_neg, ← mk_neg, neg_neg] }

theorem exist_mem_orbit_add_eq_zero (x y : GalConjClasses F E) :
    (∃ a b : E, (a ∈ x.orbit ∧ b ∈ y.orbit) ∧ a + b = 0) ↔ x = -y := by
  simp_rw [mem_orbit]
  constructor
  · rintro ⟨a, b, ⟨rfl, rfl⟩, h⟩
    rw [← mk_neg, mk_eq_mk, add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    refine ⟨-y.out, y.out, ?_⟩
    simp_rw [mk_neg, mk_out, neg_add_cancel, and_self]

protected noncomputable def minpoly : GalConjClasses F E → F[X] :=
  Quotient.lift (minpoly F) fun _ b ⟨f, h⟩ => by
    rw [← minpoly.algebraMap_eq (algebraMap E (NormalClosure F E)).injective,
      ← minpoly.algebraMap_eq (algebraMap E (NormalClosure F E)).injective, ← h]
    exact minpoly.algEquiv_eq f _

theorem minpoly_mk (x : E) : (mk F x).minpoly = minpoly F x :=
  rfl

theorem minpoly_out (c : GalConjClasses F E) : minpoly F c.out = c.minpoly := by
  rw [← c.mk_out, minpoly_mk, c.mk_out]

theorem splits_minpoly [n : Normal F E] (c : GalConjClasses F E) :
    Splits (algebraMap F E) c.minpoly := by
  rw [← c.mk_out, minpoly_mk]
  exact n.splits c.out

variable [Algebra.IsSeparable F E]
-- most lemmas work with Algebra.IsIntegral / Algebra.IsAlgebraic
-- but there isn't a lemma saying these are implied by `IsSeparable`

theorem monic_minpoly (c : GalConjClasses F E) : c.minpoly.Monic := by
  rw [← c.mk_out, minpoly_mk]; exact minpoly.monic (Algebra.IsSeparable.isIntegral F _)

theorem minpoly_ne_zero (c : GalConjClasses F E) : c.minpoly ≠ 0 := by
  rw [← c.mk_out, minpoly_mk]
  exact minpoly.ne_zero (Algebra.IsSeparable.isIntegral F _)

theorem irreducible_minpoly (c : GalConjClasses F E) : Irreducible c.minpoly := by
  rw [← c.mk_out, minpoly_mk]; exact minpoly.irreducible (Algebra.IsSeparable.isIntegral F _)

theorem separable_minpoly (c : GalConjClasses F E) : Separable c.minpoly := by
  rw [← c.mk_out, minpoly_mk]; exact Algebra.IsSeparable.isSeparable F c.out

@[simp]
theorem minpoly_inj {c d : GalConjClasses F E} :
    c.minpoly = d.minpoly ↔ c = d := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  induction' c with x
  induction' d with y
  let fc := IntermediateField.adjoinRootEquivAdjoin F (Algebra.IsSeparable.isIntegral F x)
  let fd := IntermediateField.adjoinRootEquivAdjoin F (Algebra.IsSeparable.isIntegral F y)
  let congr_f {px py : F[X]} (h : px = py) : AdjoinRoot px ≃ₐ[F] AdjoinRoot py :=
    h ▸ AlgEquiv.refl
  change minpoly F x = minpoly F y at h
  let f' := fc.symm.trans ((congr_f h).trans fd)
  let f := f'.liftNormal (NormalClosure F E)
  rw [mk_eq_mk]
  refine ⟨f.symm, ?_⟩
  dsimp only [AlgEquiv.smul_def]
  rw [AlgEquiv.symm_apply_eq]
  conv in x => rw [← IntermediateField.AdjoinSimple.algebraMap_gen F x]
  conv in y => rw [← IntermediateField.AdjoinSimple.algebraMap_gen F y]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    AlgEquiv.liftNormal_commutes]
  apply congr_arg
  simp_rw [f', fc, fd, AlgEquiv.trans_apply, ← fd.symm_apply_eq,
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
  rw [IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
  have {px py} (h : px = py) : AdjoinRoot.root py = congr_f h (AdjoinRoot.root px) := by
    subst h; rfl
  exact this h

theorem minpoly_injective : Function.Injective (@GalConjClasses.minpoly F E _ _ _) := fun _ _ =>
  minpoly_inj.mp

theorem nodup_aroots_minpoly (c : GalConjClasses F E) : (c.minpoly.aroots E).Nodup :=
  nodup_roots c.separable_minpoly.map

theorem aeval_minpoly_iff (x : E) (c : GalConjClasses F E) :
    aeval x c.minpoly = 0 ↔ mk F x = c := by
  symm; constructor
  · rintro rfl; exact minpoly.aeval _ _
  intro h
  rw [← minpoly_inj, minpoly_mk, ← minpoly.eq_of_irreducible c.irreducible_minpoly h]
  rw [c.monic_minpoly.leadingCoeff, inv_one, map_one, mul_one]

theorem rootSet_minpoly_eq_orbit (c : GalConjClasses F E) :
    c.minpoly.rootSet E = c.orbit := by
  ext x; rw [mem_orbit]
  simp_rw [mem_rootSet, aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]

theorem aroots_minpoly_eq_orbit_val (c : GalConjClasses F E) [Fintype c.orbit] :
    c.minpoly.aroots E = c.orbit.toFinset.1 := by
  classical
    simp_rw [← rootSet_minpoly_eq_orbit, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val]
    symm; rw [Multiset.dedup_eq_self]
  exact nodup_roots ((separable_map _).mpr c.separable_minpoly)

theorem orbit_eq_mk_aroots_minpoly (c : GalConjClasses F E) [Fintype c.orbit] :
    c.orbit.toFinset = ⟨c.minpoly.aroots E, c.nodup_aroots_minpoly⟩ := by
  simp only [aroots_minpoly_eq_orbit_val]

theorem minpoly.map_eq_prod [Normal F E] (c : GalConjClasses F E) [Fintype c.orbit] :
    c.minpoly.map (algebraMap F E) = ∏ x in c.orbit.toFinset, (X - C x) := by
  classical
    simp_rw [← rootSet_minpoly_eq_orbit, Finset.prod_eq_multiset_prod, rootSet_def,
      Finset.toFinset_coe, Multiset.toFinset_val]
    rw [Multiset.dedup_eq_self.mpr (nodup_roots _),
      prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Monic.map _ _)]
    · rw [splits_iff_card_roots.mp]; rw [splits_id_iff_splits]; exact c.splits_minpoly
    · exact c.monic_minpoly
    · exact c.separable_minpoly.map

end GalConjClasses
