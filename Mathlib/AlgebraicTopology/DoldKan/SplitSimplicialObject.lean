/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!

# Split simplicial objects in preadditive categories

In this file we define a functor `nondegComplex : SimplicialObject.Split C ⥤ ChainComplex C ℕ`
when `C` is a preadditive category with finite coproducts, and get an isomorphism
`toKaroubiNondegComplexFunctorIsoN₁ : nondegComplex ⋙ toKaroubi _ ≅ forget C ⋙ DoldKan.N₁`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


namespace CategoryTheory.SimplicialObject

open AlgebraicTopology Limits Category Preadditive Idempotents Opposite DoldKan Simplicial

namespace Splitting

variable {C : Type*} [Category* C] {X : SimplicialObject C}
  (s : Splitting X)

/-- The projection on a summand of the coproduct decomposition given
by a splitting of a simplicial object. -/
noncomputable def πSummand [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    X.obj Δ ⟶ s.N A.1.unop.len :=
  s.desc Δ (fun B => by
    by_cases h : B = A
    · exact eqToHom (by subst h; rfl)
    · exact 0)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem cofan_inj_πSummand_eq_id [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ s.πSummand A = 𝟙 _ := by
  simp [πSummand]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem cofan_inj_πSummand_eq_zero [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ)
    (h : B ≠ A) : (s.cofan Δ).inj A ≫ s.πSummand B = 0 := by
  dsimp [πSummand]
  rw [ι_desc, dif_neg h.symm]

variable [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
theorem decomposition_id (Δ : SimplexCategoryᵒᵖ) :
    𝟙 (X.obj Δ) = ∑ A : IndexSet Δ, s.πSummand A ≫ (s.cofan Δ).inj A := by
  apply s.hom_ext'
  intro A
  dsimp
  erw [comp_id, comp_sum, Finset.sum_eq_single A, cofan_inj_πSummand_eq_id_assoc]
  · intro B _ h₂
    rw [s.cofan_inj_πSummand_eq_zero_assoc _ _ h₂, zero_comp]
  · simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem σ_comp_πSummand_id_eq_zero {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ s.πSummand (IndexSet.id (op ⦋n + 1⦌)) = 0 := by
  apply s.hom_ext'
  intro A
  dsimp only [SimplicialObject.σ]
  rw [comp_zero, s.cofan_inj_epi_naturality_assoc A (SimplexCategory.σ i).op,
    cofan_inj_πSummand_eq_zero]
  rw [ne_comm]
  change ¬(A.epiComp (SimplexCategory.σ i).op).EqId
  rw [IndexSet.eqId_iff_len_eq]
  have h := SimplexCategory.len_le_of_epi A.e
  dsimp at h ⊢
  lia

set_option backward.isDefEq.respectTransparency false in
/-- If a simplicial object `X` in an additive category is split,
then `PInfty` vanishes on all the summands of `X _⦋n⦌` which do
not correspond to the identity of `⦋n⦌`. -/
theorem cofan_inj_comp_PInfty_eq_zero {X : SimplicialObject C} (s : SimplicialObject.Splitting X)
    {n : ℕ} (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) (hA : ¬A.EqId) :
    (s.cofan _).inj A ≫ PInfty.f n = 0 := by
  rw [SimplicialObject.Splitting.IndexSet.eqId_iff_mono] at hA
  rw [SimplicialObject.Splitting.cofan_inj_eq, assoc, degeneracy_comp_PInfty X n A.e hA, comp_zero]

set_option backward.isDefEq.respectTransparency false in
theorem comp_PInfty_eq_zero_iff {Z : C} {n : ℕ} (f : Z ⟶ X _⦋n⦌) :
    f ≫ PInfty.f n = 0 ↔ f ≫ s.πSummand (IndexSet.id (op ⦋n⦌)) = 0 := by
  constructor
  · intro h
    rcases n with _ | n
    · dsimp at h
      rw [comp_id] at h
      rw [h, zero_comp]
    · have h' := f ≫= PInfty_f_add_QInfty_f (n + 1)
      dsimp at h'
      rw [comp_id, comp_add, h, zero_add] at h'
      rw [← h', assoc, QInfty_f, decomposition_Q, Preadditive.sum_comp, Preadditive.comp_sum,
        Finset.sum_eq_zero]
      intro i _
      simp only [assoc, σ_comp_πSummand_id_eq_zero, comp_zero]
  · intro h
    rw [← comp_id f, assoc, s.decomposition_id, Preadditive.sum_comp, Preadditive.comp_sum,
      Fintype.sum_eq_zero]
    intro A
    by_cases hA : A.EqId
    · dsimp at hA
      subst hA
      rw [assoc, reassoc_of% h, zero_comp]
    · simp only [assoc, s.cofan_inj_comp_PInfty_eq_zero A hA, comp_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem PInfty_comp_πSummand_id (n : ℕ) :
    PInfty.f n ≫ s.πSummand (IndexSet.id (op ⦋n⦌)) = s.πSummand (IndexSet.id (op ⦋n⦌)) := by
  conv_rhs => rw [← id_comp (s.πSummand _)]
  symm
  rw [← sub_eq_zero, ← sub_comp, ← comp_PInfty_eq_zero_iff, sub_comp, id_comp, PInfty_f_idem,
    sub_self]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty (n : ℕ) :
    s.πSummand (IndexSet.id (op ⦋n⦌)) ≫ (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n =
      PInfty.f n := by
  conv_rhs => rw [← id_comp (PInfty.f n)]
  dsimp only [AlternatingFaceMapComplex.obj_X]
  rw [s.decomposition_id, Preadditive.sum_comp]
  rw [Fintype.sum_eq_single (IndexSet.id (op ⦋n⦌)), assoc]
  rintro A (hA : ¬A.EqId)
  rw [assoc, s.cofan_inj_comp_PInfty_eq_zero A hA, comp_zero]

/-- The differentials `s.d i j : s.N i ⟶ s.N j` on nondegenerate simplices of a split
simplicial object are induced by the differentials on the alternating face map complex. -/
@[simp]
noncomputable def d (i j : ℕ) : s.N i ⟶ s.N j :=
  (s.cofan _).inj (IndexSet.id (op ⦋i⦌)) ≫ K[X].d i j ≫ s.πSummand (IndexSet.id (op ⦋j⦌))

set_option backward.isDefEq.respectTransparency false in
theorem ιSummand_comp_d_comp_πSummand_eq_zero (j k : ℕ) (A : IndexSet (op ⦋j⦌)) (hA : ¬A.EqId) :
    (s.cofan _).inj A ≫ K[X].d j k ≫ s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
  rw [A.eqId_iff_mono] at hA
  rw [← assoc, ← s.comp_PInfty_eq_zero_iff, assoc, ← PInfty.comm j k, s.cofan_inj_eq, assoc,
    degeneracy_comp_PInfty_assoc X j A.e hA, zero_comp, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- If `s` is a splitting of a simplicial object `X` in a preadditive category,
`s.nondegComplex` is a chain complex which is given in degree `n` by
the nondegenerate `n`-simplices of `X`. This chain complex should be thought
as the normalized chain complex of `X` because of the isomorphism
`toKaroubiNondegComplexIsoN₁`. -/
@[simps]
noncomputable def nondegComplex : ChainComplex C ℕ where
  X := s.N
  d := s.d
  shape i j hij := by simp only [d, K[X].shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [d, assoc]
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op ⦋j⦌)) ≫ K[X].d j k ≫
        s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
      simp
    rw [s.decomposition_id] at eq
    classical
    rw [Fintype.sum_eq_add_sum_compl (IndexSet.id (op ⦋j⦌)), add_comp, comp_add, assoc,
      Preadditive.sum_comp, Preadditive.comp_sum, Finset.sum_eq_zero, add_zero] at eq
    swap
    · intro A hA
      simp only [Finset.mem_compl, Finset.mem_singleton] at hA
      simp only [assoc, ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ _ hA, comp_zero]
    rw [eq, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The chain complex `s.nondegComplex` attached to a splitting of a simplicial object `X`
becomes isomorphic to the normalized Moore complex `N₁.obj X` defined as a formal direct
factor in the category `Karoubi (ChainComplex C ℕ)`. -/
@[simps]
noncomputable def toKaroubiNondegComplexIsoN₁ :
    (toKaroubi _).obj s.nondegComplex ≅ N₁.obj X where
  hom :=
    { f :=
        { f := fun n => (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n
          comm' := fun i j _ => by
            dsimp
            rw [assoc, assoc, assoc, πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty,
              HomologicalComplex.Hom.comm] }
      comm := by
        ext n
        dsimp
        rw [id_comp, assoc, PInfty_f_idem] }
  inv :=
    { f :=
        { f := fun n => s.πSummand (IndexSet.id (op ⦋n⦌))
          comm' := fun i j _ => by
            dsimp
            slice_rhs 1 1 => rw [← id_comp (K[X].d i j)]
            dsimp only [AlternatingFaceMapComplex.obj_X]
            rw [s.decomposition_id, sum_comp, sum_comp, Finset.sum_eq_single (IndexSet.id (op ⦋i⦌)),
                assoc, assoc]
            · intro A _ hA
              simp only [assoc, s.ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ hA, comp_zero]
            · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff] }
      comm := by
        ext n
        dsimp
        simp only [comp_id, PInfty_comp_πSummand_id] }
  hom_inv_id := by
    ext n
    simp only [assoc, PInfty_comp_πSummand_id, Karoubi.comp_f, HomologicalComplex.comp_f,
      cofan_inj_πSummand_eq_id]
    rfl
  inv_hom_id := by
    ext n
    simp only [πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty, Karoubi.comp_f,
      HomologicalComplex.comp_f, N₁_obj_p, Karoubi.id_f]

@[reassoc (attr := simp)]
lemma toKaroubiNondegComplexIsoN₁_hom_f_PInfty :
    dsimp% s.toKaroubiNondegComplexIsoN₁.hom.f ≫ PInfty =
      s.toKaroubiNondegComplexIsoN₁.hom.f := by
  simpa using s.toKaroubiNondegComplexIsoN₁.hom.comm

@[reassoc (attr := simp)]
lemma toKaroubiNondegComplexIsoN₁_hom_inv_id_f :
    dsimp% s.toKaroubiNondegComplexIsoN₁.hom.f ≫ s.toKaroubiNondegComplexIsoN₁.inv.f = 𝟙 _ := by
  rw [← dsimp% [-Karoubi.comp_f] Karoubi.comp_f s.toKaroubiNondegComplexIsoN₁.hom
    s.toKaroubiNondegComplexIsoN₁.inv, Iso.hom_inv_id]
  simp

/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split epimorphism from the alternating face map complex of `X` to the chain
complex `s.nondegComplex`. -/
noncomputable def toNondegComplex : K[X] ⟶ s.nondegComplex :=
  (fullyFaithfulToKaroubi _).preimage
    ({ f := by exact PInfty } ≫ s.toKaroubiNondegComplexIsoN₁.inv)

/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split monomormphism from the chain complex `s.nondegComplex` to
the alternating face map complex fo `X`. -/
noncomputable def fromNondegComplex : s.nondegComplex ⟶ K[X] :=
  (fullyFaithfulToKaroubi _).preimage
    (s.toKaroubiNondegComplexIsoN₁.hom ≫ { f := PInfty })

@[reassoc (attr := simp)]
lemma PInfty_toNondegComplex : PInfty ≫ s.toNondegComplex = s.toNondegComplex :=
  (toKaroubi _).map_injective (by simp [toNondegComplex])

@[reassoc (attr := simp)]
lemma fromNondegComplex_toNondegComplex :
    s.fromNondegComplex ≫ s.toNondegComplex = 𝟙 _ :=
  (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

@[reassoc]
lemma fromNondegComplex_f (n : ℕ) :
    s.fromNondegComplex.f n = s.ι n ≫ PInfty.f n := by
  simp [fromNondegComplex, fullyFaithfulToKaroubi,
    cofan, IndexSet.id, IndexSet.e]

instance isSplitEpi_toNondegComplex : IsSplitEpi s.toNondegComplex where
  exists_splitEpi := ⟨⟨s.fromNondegComplex, by simp⟩⟩

instance isSplitMono_fromNondegComplex : IsSplitMono s.fromNondegComplex where
  exists_splitMono := ⟨⟨s.toNondegComplex, by simp⟩⟩

@[reassoc (attr := simp)]
lemma toNondegComplex_fromNondegComplex :
    s.toNondegComplex ≫ s.fromNondegComplex = PInfty :=
  (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the homotopy equivalence from the alternating face map complex of `X`
to the chain complex `s.nondegComplex`. -/
@[simps hom inv]
noncomputable def homotopyEquivNondegComplex :
    HomotopyEquiv K[X] s.nondegComplex where
  hom := s.toNondegComplex
  inv := s.fromNondegComplex
  homotopyHomInvId := .trans (.ofEq (by simp)) (homotopyPInftyToId X)
  homotopyInvHomId := .ofEq (by simp)

end Splitting

namespace Split

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- The functor which sends a split simplicial object in a preadditive category to
the chain complex which consists of nondegenerate simplices. -/
@[simps]
noncomputable def nondegComplexFunctor : Split C ⥤ ChainComplex C ℕ where
  obj S := S.s.nondegComplex
  map {S₁ S₂} Φ :=
    { f := Φ.f
      comm' := fun i j _ => by
        dsimp
        erw [← cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋i⦌)),
          ((alternatingFaceMapComplex C).map Φ.F).comm_assoc i j]
        simp only [assoc]
        congr 2
        apply S₁.s.hom_ext'
        intro A
        dsimp [alternatingFaceMapComplex]
        rw [cofan_inj_naturality_symm_assoc Φ A]
        by_cases h : A.EqId
        · dsimp at h
          subst h
          rw [Splitting.cofan_inj_πSummand_eq_id]
          dsimp
          rw [comp_id, Splitting.cofan_inj_πSummand_eq_id_assoc]
        · rw [S₁.s.cofan_inj_πSummand_eq_zero_assoc _ _ (Ne.symm h),
            S₂.s.cofan_inj_πSummand_eq_zero _ _ (Ne.symm h), zero_comp, comp_zero] }

set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism (in `Karoubi (ChainComplex C ℕ)`) between the chain complex
of nondegenerate simplices of a split simplicial object and the normalized Moore complex
defined as a formal direct factor of the alternating face map complex. -/
@[simps!]
noncomputable def toKaroubiNondegComplexFunctorIsoN₁ :
    nondegComplexFunctor ⋙ toKaroubi (ChainComplex C ℕ) ≅ forget C ⋙ DoldKan.N₁ :=
  NatIso.ofComponents (fun S => S.s.toKaroubiNondegComplexIsoN₁) fun Φ => by
    ext n
    dsimp
    simp only [assoc, PInfty_f_idem_assoc]
    erw [← Split.cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋n⦌))]
    rw [PInfty_f_naturality]

end Split

end CategoryTheory.SimplicialObject
