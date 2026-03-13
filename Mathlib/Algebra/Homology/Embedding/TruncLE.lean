/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.TruncGE

/-!
# The canonical truncation

Given an embedding `e : Embedding c c'` of complex shapes which
satisfies `e.IsTruncLE` and `K : HomologicalComplex C c'`,
we define `K.truncGE' e : HomologicalComplex C c`
and `K.truncLE e : HomologicalComplex C c'` which are the canonical
truncations of `K` relative to `e`.

In order to achieve this, we dualize the constructions from the file
`Embedding.TruncGE`.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Category

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C]

namespace HomologicalComplex

variable (K L M : HomologicalComplex C c') (φ : K ⟶ L) (φ' : L ⟶ M)
  (e : c.Embedding c') [e.IsTruncLE]
  [∀ i', K.HasHomology i'] [∀ i', L.HasHomology i'] [∀ i', M.HasHomology i']

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncLE`. -/
noncomputable def truncLE' : HomologicalComplex C c := (K.op.truncGE' e.op).unop

/-- The isomorphism `(K.truncLE' e).X i ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryLE i` does not hold. -/
noncomputable def truncLE'XIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.X i' :=
  (K.op.truncGE'XIso e.op hi' (by simpa)).symm.unop

/-- The isomorphism `(K.truncLE' e).X i ≅ K.cycles i'` when `e.f i = i'`
and `e.BoundaryLE i` holds. -/
noncomputable def truncLE'XIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE' e).X i ≅ K.cycles i' :=
  (K.op.truncGE'XIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

lemma truncLE'_d_eq {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : ¬ e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫ K.d i' j' ≫
        (K.truncLE'XIso e hj' hj).inv :=
  Quiver.Hom.op_inj (by simpa using K.op.truncGE'_d_eq e.op hij hj' hi' (by simpa))

lemma truncLE'_d_eq_toCycles {i j : ι} (hij : c.Rel i j) {i' j' : ι'}
    (hi' : e.f i = i') (hj' : e.f j = j') (hj : e.BoundaryLE j) :
    (K.truncLE' e).d i j = (K.truncLE'XIso e hi' (e.not_boundaryLE_prev hij)).hom ≫
      K.toCycles i' j' ≫ (K.truncLE'XIsoCycles e hj' hj).inv :=
  Quiver.Hom.op_inj (by
    simpa [truncLE', truncLE'XIso, truncLE'XIsoCycles]
      using K.op.truncGE'_d_eq_fromOpcycles e.op hij hj' hi' (by simpa))

section

variable [HasZeroObject C]

/-- The canonical truncation of a homological complex relative to an embedding
of complex shapes `e` which satisfies `e.IsTruncLE`. -/
noncomputable def truncLE : HomologicalComplex C c' := (K.op.truncGE e.op).unop

/-- The canonical isomorphism `K.truncLE e ≅ (K.truncLE' e).extend e`. -/
noncomputable def truncLEIso : K.truncLE e ≅ (K.truncLE' e).extend e :=
  (unopFunctor C c'.symm).mapIso ((K.truncLE' e).extendOpIso e).symm.op

/-- The isomorphism `(K.truncLE e).X i' ≅ K.X i'` when `e.f i = i'`
and `e.BoundaryLE i` does not hold. -/
noncomputable def truncLEXIso {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : ¬ e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.X i' :=
  (K.op.truncGEXIso e.op hi' (by simpa)).unop.symm

/-- The isomorphism `(K.truncLE e).X i' ≅ K.cycles i'` when `e.f i = i'`
and `e.BoundaryLE i` holds. -/
noncomputable def truncLEXIsoCycles {i : ι} {i' : ι'} (hi' : e.f i = i') (hi : e.BoundaryLE i) :
    (K.truncLE e).X i' ≅ K.cycles i' :=
  (K.op.truncGEXIsoOpcycles e.op hi' (by simpa)).unop.symm ≪≫
    (K.opcyclesOpIso i').unop.symm

end

section

variable {K L M}

/-- The morphism `K.truncLE' e ⟶ L.truncLE' e` induced by a morphism `K ⟶ L`. -/
noncomputable def truncLE'Map : K.truncLE' e ⟶ L.truncLE' e :=
  (unopFunctor C c.symm).map (truncGE'Map ((opFunctor C c').map φ.op) e.op).op

set_option backward.isDefEq.respectTransparency false in
lemma truncLE'Map_f_eq_cyclesMap {i : ι} (hi : e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIsoCycles e h hi).hom ≫ cyclesMap φ i' ≫
        (L.truncLE'XIsoCycles e h hi).inv := by
  apply Quiver.Hom.op_inj
  dsimp [truncLE'Map, truncLE'XIsoCycles]
  rw [assoc, assoc, truncGE'Map_f_eq_opcyclesMap _ e.op (by simpa) h,
    opcyclesOpIso_inv_naturality_assoc, Iso.hom_inv_id_assoc]

lemma truncLE'Map_f_eq {i : ι} (hi : ¬ e.BoundaryLE i) {i' : ι'} (h : e.f i = i') :
    (truncLE'Map φ e).f i =
      (K.truncLE'XIso e h hi).hom ≫ φ.f i' ≫ (L.truncLE'XIso e h hi).inv :=
  Quiver.Hom.op_inj
    (by simpa using truncGE'Map_f_eq ((opFunctor C c').map φ.op) e.op (by simpa) h)

variable (K) in
@[simp]
lemma truncLE'Map_id : truncLE'Map (𝟙 K) e = 𝟙 _ :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGE'Map_id e.op))

@[reassoc, simp]
lemma truncLE'Map_comp : truncLE'Map (φ ≫ φ') e = truncLE'Map φ e ≫ truncLE'Map φ' e :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGE'Map_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

variable [HasZeroObject C]

/-- The morphism `K.truncLE e ⟶ L.truncLE e` induced by a morphism `K ⟶ L`. -/
noncomputable def truncLEMap : K.truncLE e ⟶ L.truncLE e :=
  (unopFunctor C c'.symm).map (truncGEMap ((opFunctor C c').map φ.op) e.op).op

variable (K) in
@[simp]
lemma truncLEMap_id : truncLEMap (𝟙 K) e = 𝟙 _ :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op (K.op.truncGEMap_id e.op))

@[reassoc, simp]
lemma truncLEMap_comp : truncLEMap (φ ≫ φ') e = truncLEMap φ e ≫ truncLEMap φ' e :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (truncGEMap_comp ((opFunctor C c').map φ'.op) ((opFunctor C c').map φ.op) e.op))

end

/-- The canonical morphism `K.truncLE' e ⟶ K.restriction e`. -/
noncomputable def truncLE'ToRestriction : K.truncLE' e ⟶ K.restriction e :=
  (unopFunctor C c.symm).map (K.op.restrictionToTruncGE' e.op).op

/-- `(K.truncLE'ToRestriction e).f i` is an isomorphism when `¬ e.BoundaryLE i`. -/
lemma isIso_truncLE'ToRestriction (i : ι) (hi : ¬ e.BoundaryLE i) :
    IsIso ((K.truncLE'ToRestriction e).f i) := by
  change IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop
  have := K.op.isIso_restrictionToTruncGE' e.op i (by simpa)
  infer_instance

variable {K L} in
@[reassoc (attr := simp)]
lemma truncLE'ToRestriction_naturality :
    truncLE'Map φ e ≫ L.truncLE'ToRestriction e =
      K.truncLE'ToRestriction e ≫ restrictionMap φ e :=
  (unopFunctor C c.symm).congr_map (congr_arg Quiver.Hom.op
    (restrictionToTruncGE'_naturality ((opFunctor C c').map φ.op) e.op))

instance (i : ι) : Mono ((K.truncLE'ToRestriction e).f i) :=
  inferInstanceAs% (Mono ((K.op.restrictionToTruncGE' e.op).f i).unop)

instance [K.IsStrictlySupported e] (i : ι) :
    IsIso ((K.truncLE'ToRestriction e).f i) :=
  inferInstanceAs% (IsIso ((K.op.restrictionToTruncGE' e.op).f i).unop)

section

variable [HasZeroObject C]

/-- The canonical morphism `K.truncLE e ⟶ K` when `e` is an embedding of complex
shapes which satisfy `e.IsTruncLE`. -/
noncomputable def ιTruncLE : K.truncLE e ⟶ K :=
  (unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op

instance (i' : ι') : Mono ((K.ιTruncLE e).f i') :=
  inferInstanceAs% (Mono ((K.op.πTruncGE e.op).f i').unop)

instance : Mono (K.ιTruncLE e) := mono_of_mono_f _ (fun _ => inferInstance)

instance : (K.truncLE e).IsStrictlySupported e := by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs% ((K.op.truncGE e.op).IsStrictlySupported e.op)

variable {K L} in
@[reassoc (attr := simp)]
lemma ιTruncLE_naturality :
    truncLEMap φ e ≫ L.ιTruncLE e = K.ιTruncLE e ≫ φ :=
  (unopFunctor C c'.symm).congr_map (congr_arg Quiver.Hom.op
    (πTruncGE_naturality ((opFunctor C c').map φ.op) e.op))

instance {ι'' : Type*} {c'' : ComplexShape ι''} (e' : c''.Embedding c')
    [K.IsStrictlySupported e'] : (K.truncLE e).IsStrictlySupported e' := by
  rw [← isStrictlySupported_op_iff]
  exact inferInstanceAs% ((K.op.truncGE e.op).IsStrictlySupported e'.op)

instance [K.IsStrictlySupported e] : IsIso (K.ιTruncLE e) :=
  inferInstanceAs% (IsIso ((unopFunctor C c'.symm).map (K.op.πTruncGE e.op).op))

lemma isIso_ιTruncLE_iff : IsIso (K.ιTruncLE e) ↔ K.IsStrictlySupported e :=
  ⟨fun _ ↦ isStrictlySupported_of_iso (asIso (K.ιTruncLE e)) e,
    fun _ ↦ inferInstance⟩

end

end HomologicalComplex

namespace ComplexShape.Embedding

variable (e : Embedding c c') [e.IsTruncLE]
    (C : Type*) [Category* C] [HasZeroMorphisms C] [HasZeroObject C] [CategoryWithHomology C]

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c`. -/
@[simps]
noncomputable def truncLE'Functor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c where
  obj K := K.truncLE' e
  map φ := HomologicalComplex.truncLE'Map φ e

/-- The natural transformation `K.truncGE' e ⟶ K.restriction e` for all `K`. -/
@[simps]
noncomputable def truncLE'ToRestrictionNatTrans :
    e.truncLE'Functor C ⟶ e.restrictionFunctor C where
  app K := K.truncLE'ToRestriction e

/-- Given an embedding `e : Embedding c c'` of complex shapes which satisfy `e.IsTruncLE`,
this is the (canonical) truncation functor
`HomologicalComplex C c' ⥤ HomologicalComplex C c'`. -/
@[simps]
noncomputable def truncLEFunctor :
    HomologicalComplex C c' ⥤ HomologicalComplex C c' where
  obj K := K.truncLE e
  map φ := HomologicalComplex.truncLEMap φ e

/-- The natural transformation `K.ιTruncLE e : K.truncLE e ⟶ K` for all `K`. -/
@[simps]
noncomputable def ιTruncLENatTrans : e.truncLEFunctor C ⟶ 𝟭 _ where
  app K := K.ιTruncLE e

end ComplexShape.Embedding
