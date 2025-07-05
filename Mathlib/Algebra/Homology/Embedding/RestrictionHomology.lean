/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # The homology of a restriction

Under favourable circumstances, we may relate the
homology of `K : HomologicalComplex C c'` in degree `j'` and
that of `K.restriction e` in degree `j` when `e : Embedding c c'`
is an embedding of complex shapes. See `restriction.sc'Iso`
and `restriction.hasHomology`.

-/

open CategoryTheory Category Limits ZeroObject

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

namespace HomologicalComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

namespace restriction

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')

/-- The isomorphism `(K.restriction e).sc' i j k ≅ K.sc' i' j' k'` when
`e` is an embedding of complex shapes, `i'`, `j`, `k`' are the respective
images of `i`, `j`, `k` by `e.f`, `j` is the previous index of `i`, etc. -/
@[simps!]
def sc'Iso : (K.restriction e).sc' i j k ≅ K.sc' i' j' k' :=
  ShortComplex.isoMk (K.restrictionXIso e hi') (K.restrictionXIso e hj') (K.restrictionXIso e hk')
    (by subst hi' hj'; simp [restrictionXIso])
    (by subst hj' hk'; simp [restrictionXIso])

include hi hk hi' hj' hk' hi'' hk'' in
lemma hasHomology [K.HasHomology j'] : (K.restriction e).HasHomology j :=
  ShortComplex.hasHomology_of_iso (K.isoSc' i' j' k' hi'' hk'' ≪≫
    (sc'Iso K e i j k hi' hj' hk' hi'' hk'').symm ≪≫
    ((K.restriction e).isoSc' i j k hi hk).symm)

end restriction

variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
  {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
  [K.HasHomology j'] [(K.restriction e).HasHomology j]

/-- The isomorphism `(K.restriction e).cycles j ≅ K.cycles j'` when `e.f j = j'`
and the successors `k` and `k'` of `j` and `j'` satisfy `e.f k = k'`. -/
noncomputable def restrictionCyclesIso :
    (K.restriction e).cycles j ≅ K.cycles j' where
  hom :=
    K.liftCycles ((K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom) _ hk'' (by
      rw [assoc, ← cancel_mono (K.restrictionXIso e hk').inv, assoc, assoc, ← restriction_d_eq,
        iCycles_d, zero_comp])
  inv :=
    (K.restriction e).liftCycles (K.iCycles j' ≫ (K.restrictionXIso e hj').inv) _ hk (by
      rw [assoc, restriction_d_eq _ _ hj' hk', Iso.inv_hom_id_assoc,
        iCycles_d_assoc, zero_comp])
  hom_inv_id := by simp [← cancel_mono ((K.restriction e).iCycles j)]
  inv_hom_id := by simp [← cancel_mono (K.iCycles j')]

@[reassoc (attr := simp)]
lemma restrictionCyclesIso_hom_iCycles :
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ K.iCycles j' =
      (K.restriction e).iCycles j ≫ (K.restrictionXIso e hj').hom := by
  simp [restrictionCyclesIso]

@[reassoc (attr := simp)]
lemma restrictionCyclesIso_inv_iCycles :
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').inv ≫ (K.restriction e).iCycles j =
      K.iCycles j' ≫ (K.restrictionXIso e hj').inv := by
  simp [restrictionCyclesIso]

/-- The isomorphism `(K.restriction e).opcycles j ≅ K.opcycles j'` when `e.f j = j'`
and the predecessors `i` and `i'` of `j` and `j'` satisfy `e.f i = i'`. -/
noncomputable def restrictionOpcyclesIso :
    (K.restriction e).opcycles j ≅ K.opcycles j' where
  hom :=
    (K.restriction e).descOpcycles ((K.restrictionXIso e hj').hom ≫ K.pOpcycles j') _ hi (by
      rw [restriction_d_eq _ _ hi' hj', assoc, assoc, Iso.inv_hom_id_assoc,
        d_pOpcycles, comp_zero])
  inv :=
    K.descOpcycles ((K.restrictionXIso e hj').inv ≫ (K.restriction e).pOpcycles j) _ hi'' (by
      rw [← cancel_epi (K.restrictionXIso e hi').hom, ← restriction_d_eq_assoc,
        comp_zero, d_pOpcycles])
  hom_inv_id := by simp [← cancel_epi ((K.restriction e).pOpcycles j)]
  inv_hom_id := by simp [← cancel_epi (K.pOpcycles j')]

@[reassoc (attr := simp)]
lemma pOpcycles_restrictionOpcyclesIso_hom :
    (K.restriction e).pOpcycles j ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom =
      (K.restrictionXIso e hj').hom ≫ K.pOpcycles j' := by
  simp [restrictionOpcyclesIso]

@[reassoc (attr := simp)]
lemma pOpcycles_restrictionOpcyclesIso_inv :
    K.pOpcycles j' ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv =
      (K.restrictionXIso e hj').inv ≫ (K.restriction e).pOpcycles j := by
  simp [restrictionOpcyclesIso]

/-- The isomorphism `(K.restriction e).homology j ≅ K.homology j'` when `e.f j = j'`,
the predecessors `i` and `i'` of `j` and `j'` satisfy `e.f i = i'`,
and the successors `k` and `k'` of `j` and `j'` satisfy `e.f k = k'` -/
noncomputable def restrictionHomologyIso :
    (K.restriction e).homology j ≅ K.homology j' :=
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  (K.restriction e).homologyIsoSc' i j k hi hk ≪≫
    ShortComplex.homologyMapIso (restriction.sc'Iso K e i j k hi' hj' hk' hi'' hk'') ≪≫
    (K.homologyIsoSc' i' j' k' hi'' hk'').symm

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma homologyπ_restrictionHomologyIso_hom :
    (K.restriction e).homologyπ j ≫
      (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom =
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫ K.homologyπ j' := by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
    ← cancel_mono (K.sc j').homologyι, assoc, assoc]
  apply (ShortComplex.π_homologyMap_ι _).trans
  dsimp
  rw [comp_id, id_comp]
  apply (K.restrictionCyclesIso_hom_iCycles_assoc e j k hk hj' hk' hk'' _).symm.trans
  congr 1
  symm
  apply ShortComplex.homology_π_ι

@[reassoc]
lemma homologyπ_restrictionHomologyIso_inv :
    K.homologyπ j' ≫ (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv =
      (K.restrictionCyclesIso e j k hk hj' hk' hk'').inv ≫ (K.restriction e).homologyπ j := by
  rw [← cancel_mono (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom,
    assoc, assoc, Iso.inv_hom_id, homologyπ_restrictionHomologyIso_hom, comp_id,
    Iso.inv_hom_id_assoc]

@[reassoc (attr := simp, nolint unusedHavesSuffices)]
lemma restrictionHomologyIso_inv_homologyι :
    (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv ≫
      (K.restriction e).homologyι j =
    K.homologyι j' ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv := by
  have : ((K.restriction e).sc' i j k).HasHomology := by subst hi hk; assumption
  have : (K.sc' i' j' k').HasHomology := by subst hi'' hk''; assumption
  dsimp [restrictionHomologyIso, homologyIsoSc']
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp, assoc,
    ← cancel_epi (K.sc j').homologyπ]
  apply (ShortComplex.π_homologyMap_ι _).trans
  dsimp
  rw [comp_id, id_comp]
  refine ((ShortComplex.homology_π_ι_assoc _ _).trans ?_).symm
  congr 1
  apply pOpcycles_restrictionOpcyclesIso_inv

@[reassoc (attr := simp)]
lemma restrictionHomologyIso_hom_homologyι :
    (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').hom ≫ K.homologyι j' =
      (K.restriction e).homologyι j ≫ (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom := by
  rw [← cancel_epi (K.restrictionHomologyIso e i j k hi hk hi' hj' hk' hi'' hk'').inv,
    Iso.inv_hom_id_assoc, restrictionHomologyIso_inv_homologyι_assoc,
      Iso.inv_hom_id, comp_id]

end HomologicalComplex
