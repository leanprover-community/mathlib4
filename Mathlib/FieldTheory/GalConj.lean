/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.FieldTheory.Normal

/-!
TODO
-/

open Polynomial

open scoped Polynomial BigOperators IntermediateField

section GalConjClasses

variable (F : Type*) [Field F] (E : Type*) [Field E] [Algebra F E]

def IsGalConj.setoid :=
  MulAction.orbitRel (E ≃ₐ[F] E) E

def GalConjClasses :=
  MulAction.orbitRel.Quotient (E ≃ₐ[F] E) E

variable {E}

def IsGalConj (x y : E) : Prop :=
  (IsGalConj.setoid F E).r x y

scoped[IsGalConj] notation:50 x:51 " ≈g[" F "] " y:51 => IsGalConj F x y

open scoped IsGalConj

namespace IsGalConj

instance decidable [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (x y : E) :
    Decidable (x ≈g[F] y) :=
  Fintype.decidableExistsFintype

instance [DecidableEq E] [Fintype (E ≃ₐ[F] E)] : DecidableEq (GalConjClasses F E) :=
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
  simp_rw [← ha, AlgEquiv.smul_def, map_zero]

theorem out_eq_zero_iff (c : GalConjClasses F E) : c.out = 0 ↔ c = 0 := by
  rw [zero_def, eq_mk_iff_out, isGalConj_zero_iff]

theorem zero_out : (0 : GalConjClasses F E).out = 0 :=
  (out_eq_zero_iff 0).mpr rfl

theorem mk_eq_zero_iff (x : E) : mk F x = 0 ↔ x = 0 := by
  rw [mk_eq_iff_out, zero_out, isGalConj_zero_iff]

theorem mk_zero : mk F (0 : E) = 0 :=
  (mk_eq_zero_iff 0).mpr rfl

nonrec def orbit (c : GalConjClasses F E) : Set E :=
  c.orbit

instance [DecidableEq E] [Fintype (E ≃ₐ[F] E)] (c : GalConjClasses F E) : Fintype c.orbit :=
  Quotient.recOnSubsingleton' c fun _ => Set.fintypeRange _

theorem mem_orbit {x : E} {c : GalConjClasses F E} : x ∈ c.orbit ↔ mk F x = c :=
  MulAction.orbitRel.Quotient.mem_orbit

theorem orbit_zero : (0 : GalConjClasses F E).orbit = {0} := by
  ext; rw [mem_orbit, mk_eq_zero_iff, Set.mem_singleton_iff]

instance : Neg (GalConjClasses F E) :=
  ⟨Quotient.lift (fun x : E => mk F (-x))
      (by
        rintro _ y ⟨f, rfl⟩; rw [mk_eq_mk]
        use f; simp only [smul_neg])⟩

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

noncomputable nonrec def minpoly : GalConjClasses F E → F[X] :=
  Quotient.lift (minpoly F) fun _ b ⟨f, h⟩ => h ▸ minpoly.algEquiv_eq f b

theorem minpoly_mk (x : E) : minpoly (mk F x) = _root_.minpoly F x :=
  rfl

theorem minpoly_out (c : GalConjClasses F E) : _root_.minpoly F c.out = minpoly c := by
  rw [← c.mk_out, minpoly_mk, c.mk_out]

theorem splits_minpoly [n : Normal F E] (c : GalConjClasses F E) :
    Splits (algebraMap F E) (minpoly c) := by rw [← c.mk_out, minpoly_mk]; exact n.splits c.out

variable [Algebra.IsSeparable F E]
-- most lemmas work with Algebra.IsIntegral / Algebra.IsAlgebraic
-- but there isn't a lemma saying these are implied by `IsSeparable`

theorem monic_minpoly (c : GalConjClasses F E) : (minpoly c).Monic := by
  rw [← c.mk_out, minpoly_mk]; exact minpoly.monic (Algebra.IsSeparable.isIntegral F _)

theorem minpoly_ne_zero (c : GalConjClasses F E) : minpoly c ≠ 0 := by
  rw [← c.mk_out, minpoly_mk]
  exact minpoly.ne_zero (Algebra.IsSeparable.isIntegral F _)

theorem irreducible_minpoly (c : GalConjClasses F E) : Irreducible (minpoly c) := by
  rw [← c.mk_out, minpoly_mk]; exact minpoly.irreducible (Algebra.IsSeparable.isIntegral F _)

theorem separable_minpoly (c : GalConjClasses F E) : Separable (minpoly c) := by
  rw [← c.mk_out, minpoly_mk]; exact Algebra.IsSeparable.isSeparable F c.out

theorem minpoly_inj [Normal F E] {c d : GalConjClasses F E} (h : minpoly c = minpoly d) :
    c = d := by
  induction' c with x
  induction' d with y
  let fc := IntermediateField.adjoinRootEquivAdjoin F (Algebra.IsSeparable.isIntegral F x)
  let fd := IntermediateField.adjoinRootEquivAdjoin F (Algebra.IsSeparable.isIntegral F y)
  let congr_f {px py : F[X]} (h : px = py) : AdjoinRoot px ≃ₐ[F] AdjoinRoot py :=
    h ▸ AlgEquiv.refl
  change _root_.minpoly F x = _root_.minpoly F y at h
  let f' := fc.symm.trans ((congr_f h).trans fd)
  let f := f'.liftNormal E
  rw [mk_eq_mk]
  refine ⟨f.symm, ?_⟩
  dsimp only [AlgEquiv.smul_def]
  rw [AlgEquiv.symm_apply_eq]
  conv in x => rw [← IntermediateField.AdjoinSimple.algebraMap_gen F x]
  conv in y => rw [← IntermediateField.AdjoinSimple.algebraMap_gen F y]
  rw [AlgEquiv.liftNormal_commutes]
  apply congr_arg
  simp_rw [f', fc, fd, AlgEquiv.trans_apply, ← fd.symm_apply_eq,
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
  rw [IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen]
  have {px py} (h : px = py) : AdjoinRoot.root py = congr_f h (AdjoinRoot.root px) := by
    subst h; rfl
  exact this h


theorem minpoly_injective [Normal F E] : Function.Injective (@minpoly F _ E _ _) := fun _ _ =>
  minpoly_inj

theorem nodup_aroots_minpoly (c : GalConjClasses F E) : ((minpoly c).aroots E).Nodup :=
  nodup_roots c.separable_minpoly.map

theorem aeval_minpoly_iff [Normal F E] (x : E) (c : GalConjClasses F E) :
    aeval x (minpoly c) = 0 ↔ mk F x = c := by
  symm; constructor
  · rintro rfl; exact minpoly.aeval _ _
  intro h
  apply minpoly_inj
  rw [minpoly_mk, ← minpoly.eq_of_irreducible c.irreducible_minpoly h]
  rw [c.monic_minpoly.leadingCoeff, inv_one, map_one, mul_one]

theorem rootSet_minpoly_eq_orbit [Normal F E] (c : GalConjClasses F E) :
    (minpoly c).rootSet E = c.orbit := by
  ext x; rw [mem_orbit]
  simp_rw [mem_rootSet, aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]

theorem aroots_minpoly_eq_orbit_val [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) : (minpoly c).aroots E = c.orbit.toFinset.1 := by
  simp_rw [← rootSet_minpoly_eq_orbit, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val]
  symm; rw [Multiset.dedup_eq_self]
  exact nodup_roots ((separable_map _).mpr c.separable_minpoly)

theorem orbit_eq_mk_aroots_minpoly [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) :
    c.orbit.toFinset = ⟨(minpoly c).aroots E, c.nodup_aroots_minpoly⟩ := by
  simp only [aroots_minpoly_eq_orbit_val]

theorem minpoly.map_eq_prod [DecidableEq E] [Fintype (E ≃ₐ[F] E)] [Normal F E]
    (c : GalConjClasses F E) :
    (minpoly c).map (algebraMap F E) = ∏ x in c.orbit.toFinset, (X - C x) := by
  simp_rw [← rootSet_minpoly_eq_orbit, Finset.prod_eq_multiset_prod, rootSet_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [Multiset.dedup_eq_self.mpr (nodup_roots _),
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq (Monic.map _ _)]
  · rw [splits_iff_card_roots.mp]; rw [splits_id_iff_splits]; exact c.splits_minpoly
  · exact c.monic_minpoly
  · exact c.separable_minpoly.map

end GalConjClasses

end GalConjClasses
