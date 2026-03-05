/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.CohenMacaulay.Catenary
public import Mathlib.RingTheory.CohenMacaulay.Maximal
public import Mathlib.RingTheory.CohenStructureTheorem
public import Mathlib.RingTheory.KoszulComplex.Homotopy

/-!

# Define Complete Intersection Ring

-/

@[expose] public section

open IsLocalRing RingTheory.Sequence

universe u

variable (R : Type u) [CommRing R]

section preliminaries

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 250000 in
--the equiv is a bit complicated
lemma spanFinrank_comap [IsNoetherianRing R] [IsLocalRing R] (x : R)
    (I : Ideal (R ⧸ Ideal.span {x})) (J : Ideal R)
    (eq : J = I.comap (Ideal.Quotient.mk (Ideal.span {x})))
    (mem : x ∈ maximalIdeal R) (nmem : x ∉ maximalIdeal R * J) :
    J.spanFinrank = I.spanFinrank + 1 := by
  have le := (Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr mem
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  let _ := Submodule.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top mem)
  let _ : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
  let S := R ⧸ Ideal.span {x}
  have comapeq : (maximalIdeal S).comap (Ideal.Quotient.mk (Ideal.span {x})) = maximalIdeal R :=
    ((local_hom_TFAE _).out 0 4).mp ‹_›
  have memJ : x ∈ J := by simp [eq]
  let QJ := J ⧸ (maximalIdeal R • (⊤ : Submodule R J))
  let QI := I ⧸ (maximalIdeal S • (⊤ : Submodule S I))
  have hJ : J.spanFinrank = Module.finrank (R ⧸ maximalIdeal R) QJ :=
    spanFinrank_eq_finrank_quotient J J.fg_of_isNoetherianRing
  have hI : I.spanFinrank = Module.finrank (S ⧸ maximalIdeal S) QI :=
    spanFinrank_eq_finrank_quotient I I.fg_of_isNoetherianRing
  let q : R →ₗ[R] S := Submodule.mkQ (Ideal.span {x})
  let qr : J →ₗ[R] I := q.restrict (q := I.restrictScalars R) (le_of_eq eq)
  have le' : (maximalIdeal R • (⊤ : Submodule R I)) ≤
    (maximalIdeal S • (⊤ : Submodule S I)).restrictScalars R := by
    refine Submodule.smul_le.mpr (fun r hr z hz ↦ ?_)
    simpa only [Submodule.restrictScalars_mem] using Submodule.smul_mem_smul
      (map_nonunit (Ideal.Quotient.mk (Ideal.span {x})) r hr) Submodule.mem_top
  let f : QJ →ₗ[R] QI := Submodule.mapQ (p := (maximalIdeal R • (⊤ : Submodule R J)))
      (q := (maximalIdeal S • (⊤ : Submodule S I)).restrictScalars R) qr
      ((Submodule.smul_top_le_comap_smul_top (maximalIdeal R) qr).trans (Submodule.comap_mono le'))
  have surjqr : Function.Surjective qr := by
    intro i
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective i.1
    refine ⟨⟨r, by simp [eq, hr]⟩, SetCoe.ext ?_⟩
    change q r = (i : S)
    simpa [q] using hr
  have surjf : Function.Surjective f := by
    intro y
    obtain ⟨i, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨j, rfl⟩ := surjqr i
    exact ⟨Submodule.Quotient.mk j, Submodule.mapQ_apply _ _ qr j⟩
  let K := Submodule.span (R ⧸ maximalIdeal R)
    {Submodule.mkQ (maximalIdeal R • (⊤ : Submodule R J)) ⟨x, memJ⟩}
  have mkeq1 (z : I) : (Submodule.Quotient.mk z : QI) = 0 ↔ z.1 ∈ maximalIdeal S * I :=
    (Submodule.Quotient.mk_eq_zero _).trans (Submodule.mem_smul_top_iff _ _ z)
  have mkeq2 (w  : J) : (Submodule.Quotient.mk w : QJ) = 0 ↔ w.1 ∈ maximalIdeal R * J :=
    (Submodule.Quotient.mk_eq_zero _).trans (Submodule.mem_smul_top_iff _ _ w)
  have hcomap : (maximalIdeal S * I).comap (Ideal.Quotient.mk (Ideal.span {x})) =
        (maximalIdeal R * J) ⊔ Ideal.span {x} := by
    have mapm : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) = maximalIdeal S := by
      simp only [← comapeq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    have mapJ : J.map (Ideal.Quotient.mk (Ideal.span {x})) = I := by
      simpa [eq] using  (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I)
    simp [← mapm, ← mapJ, ← Ideal.map_mul,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]
  have kereq : (LinearMap.ker f : Set QJ) = K := by
    simp only [K, Submodule.coe_span_eq_span_of_surjective R _ Ideal.Quotient.mk_surjective,
      SetLike.coe_set_eq]
    ext y
    induction y using Submodule.Quotient.induction_on
    rename_i y
    simp only [LinearMap.mem_ker, f]
    change (Submodule.Quotient.mk ⟨(Ideal.Quotient.mk (Ideal.span {x})) y, _⟩ : QI) = 0 ↔
      Submodule.mkQ _ y ∈ _
    simp only [mkeq1, ← Ideal.mem_comap, hcomap, ← Submodule.mem_comap]
    rw [← Set.image_singleton, ← Submodule.map_span, Submodule.comap_map_eq, sup_comm]
    rw [← Submodule.comap_map_eq_of_injective J.subtype_injective (_ ⊔ _)]
    simp [Submodule.map_sup, Submodule.map_subtype_span_singleton, Ideal.submodule_span_eq,
      Submodule.mem_comap, Submodule.subtype_apply]
  let f' : QJ ⧸ K →+ QI := QuotientAddGroup.lift _ f
    (le_of_eq (AddSubgroup.ext (fun x ↦ (congrFun kereq.symm x).to_iff)))
  have bij : Function.Bijective f' := by
    refine ⟨?_, QuotientAddGroup.lift_surjective_of_surjective _ _ surjf _⟩
    rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    induction x using QuotientAddGroup.induction_on
    rename_i x
    have : x ∈ (LinearMap.ker f : Set QJ) := LinearMap.mem_ker.mpr hx
    rw [kereq] at this
    exact AddSubgroup.mem_bot.mpr ((QuotientAddGroup.eq_zero_iff _).mpr this)
  let e : QJ ⧸ K ≃+ QI := AddEquiv.ofBijective f' bij
  let qres : R ⧸ maximalIdeal R →+* S ⧸ maximalIdeal S :=
    ResidueField.map (Ideal.Quotient.mk (Ideal.span {x}))
  have qresbij : Function.Bijective qres :=
    ResidueField.map_bijective_of_surjective _ Ideal.Quotient.mk_surjective
  have (r : R ⧸ maximalIdeal R) (m : QJ ⧸ K) : e (r • m) = qres r • e m := by
    induction m using Submodule.Quotient.induction_on
    induction r using Submodule.Quotient.induction_on
    rename_i j r
    change f (r • j) = qres (Ideal.Quotient.mk (maximalIdeal R) r) • (f j)
    simp only [map_smul]
    rfl
  have rk : Module.rank (R ⧸ maximalIdeal R) (QJ ⧸ K) = Module.rank (S ⧸ maximalIdeal S) QI :=
    rank_eq_of_equiv_equiv qres e qresbij this
  have frk : Module.finrank (R ⧸ maximalIdeal R) (QJ ⧸ K) = Module.finrank
    (S ⧸ maximalIdeal S) QI := by
    simp only [Module.finrank, rk]
  have frk1 : Module.finrank (R ⧸ maximalIdeal R) K = 1 := by
    apply finrank_span_singleton
    simpa [mkeq2] using nmem
  rw [hI, hJ, ← frk, ← frk1, K.finrank_quotient_add_finrank]

set_option backward.isDefEq.respectTransparency false in
lemma preservesHomology_of_flat (S : Type*) [CommRing S] (f : R →+* S) (flat : f.Flat) :
    (ModuleCat.extendScalars f).PreservesHomology := by
  apply ((CategoryTheory.Functor.exact_tfae _).out 1 2).mp (fun T hT ↦ ?_)
  let _ : Module R S := Module.compHom S f
  let _ : Module.Flat R S := flat
  have : Function.Exact (ModuleCat.ExtendScalars.map' f T.f) (ModuleCat.ExtendScalars.map' f T.g) :=
    Module.Flat.lTensor_exact S
      ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT)
  exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr this

open CategoryTheory

lemma CategoryTheory.Functor.mapHomologicalComplex_sc {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).sc i = (K.sc i).map F := rfl

end preliminaries

noncomputable abbrev koszulAlgebra [IsNoetherianRing R] [IsLocalRing R] :=
  koszulComplex.ofList (maximalIdeal R).finite_generators_of_isNoetherian.toFinset.toList

lemma koszulAlgebra.annihilator_homology [IsNoetherianRing R] [IsLocalRing R] (i : ℕ) :
    maximalIdeal R ≤ Module.annihilator R ((koszulAlgebra R).homology i) := by
  apply le_of_eq_of_le _ (koszulComplex.ofList_ideal_annihilator_homology _ i)
  simpa [Ideal.ofList] using (maximalIdeal R).span_generators.symm

noncomputable instance [IsNoetherianRing R] [IsLocalRing R] (i : ℕ) :
    Module (ResidueField R) ((koszulAlgebra R).homology i) :=
  Module.IsTorsionBySet.module (fun x a ↦
    Module.mem_annihilator.mp ((koszulAlgebra.annihilator_homology R i) a.2) x)

noncomputable instance [IsNoetherianRing R] [IsLocalRing R] (i : ℕ) :
    IsScalarTower R (ResidueField R) ((koszulAlgebra R).homology i) :=
  IsScalarTower.of_compHom R (ResidueField R) ((koszulAlgebra R).homology i)

noncomputable instance [IsNoetherianRing R] [IsLocalRing R] (i : ℕ) :
    Module.Finite R ((koszulAlgebra R).X i) := by

  sorry

noncomputable instance [IsNoetherianRing R] [IsLocalRing R] (i : ℕ) :
    Module.Finite (ResidueField R) ((koszulAlgebra R).homology i) := by

  sorry

noncomputable def Epsilon1 [IsNoetherianRing R] [IsLocalRing R] : ℕ :=
  Module.finrank (ResidueField R) ((koszulAlgebra R).homology 1)

section

universe v

set_option backward.isDefEq.respectTransparency false in
lemma epsilon1_eq_of_ringEquiv_aux {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {R' : Type (max u v)} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R'] (e : R ≃+* R') :
    Epsilon1 R = Epsilon1 R' := by
  let l := (maximalIdeal R).finite_generators_of_isNoetherian.toFinset.toList
  let l' := l.map (RingHomClass.toRingHom e)
  have eq1 : Ideal.ofList l = maximalIdeal R := by
    simpa [l, Ideal.ofList] using (maximalIdeal R).span_generators
  have eqmap : Ideal.map (RingHomClass.toRingHom e) (maximalIdeal R) = maximalIdeal R' := by
    have : (maximalIdeal R').comap e = maximalIdeal R := by
      ext
      simp
    simpa [← this] using Ideal.map_comap_eq_self_of_equiv e (maximalIdeal R')
  have eq2 : Ideal.ofList l' = maximalIdeal R' := by
    simp only [l', ← Ideal.map_ofList, eq1, eqmap]
  have len1 : l.length = (maximalIdeal R).spanFinrank := by
    simp only [Finset.length_toList, l, ← Set.ncard_eq_toFinset_card,
      Submodule.FG.generators_ncard (maximalIdeal R).fg_of_isNoetherianRing]
  have len2 : l'.length = (maximalIdeal R').spanFinrank := by
    simp [← spanFinrank_eq_of_ringEquiv e, l', len1]
  let e1 := koszulComplex.baseChange_iso R' e l l' rfl
  obtain ⟨e2⟩ := koszulComplex.nonempty_iso_of_minimal_generators' eq2 len2
  let F := ModuleCat.extendScalars (RingHomClass.toRingHom e)
  let e' : koszulAlgebra R' ≅ (F.mapHomologicalComplex _).obj (koszulAlgebra R) := e2.trans e1
  let h1R := (koszulAlgebra R).homology 1
  let h1R' := (koszulAlgebra R').homology 1
  let _ : F.PreservesHomology := preservesHomology_of_flat R R' (RingHomClass.toRingHom e)
    (RingHom.Flat.of_bijective e.bijective)
  let eh : h1R' ≅ F.obj h1R :=
    (HomologicalComplex.homologyMapIso e' 1).trans (((koszulAlgebra R).sc 1).mapHomologyIso F)
  let _ := (RingHomClass.toRingHom e).toAlgebra
  let eh' : ↑h1R' ≃ₗ[R'] TensorProduct R R' ↑h1R := eh.toLinearEquiv
  simp only [Epsilon1]
  let I := Module.Free.ChooseBasisIndex (ResidueField R) h1R
  let _ : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
  let B : h1R ≃ₗ[ResidueField R] I →₀ ResidueField R :=
    (Module.Free.chooseBasis (ResidueField R) h1R).repr
  rw [B.finrank_eq, Module.finrank_finsupp_self]
  let eres : ResidueField R' ≃ₗ[R'] TensorProduct R R' (ResidueField R) :=
    (Submodule.quotEquivOfEq _ _ eqmap.symm).trans (Ideal.qoutMapEquivTensorQout R')
  let eh'' : h1R' ≃ₗ[ResidueField R'] I →₀ ResidueField R' :=
    (eh'.trans ((((B.restrictScalars R).baseChange R R').trans
    (TensorProduct.finsuppRight R R' R' (ResidueField R) I)).trans
    (Finsupp.mapRange.linearEquiv eres.symm))).extendScalarsOfSurjective residue_surjective
  rw [eh''.finrank_eq, Module.finrank_finsupp_self]

lemma epsilon1_eq_of_ringEquiv {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {R' : Type v} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R'] (e : R ≃+* R') :
    Epsilon1 R = Epsilon1 R' := by
  let R'' := ULift.{v} R
  let e1 : R'' ≃+* R := ULift.ringEquiv
  let _ : IsNoetherianRing R'' := isNoetherianRing_of_ringEquiv R e1.symm
  let _ : IsLocalRing R'' := e1.symm.isLocalRing
  let e2 := e1.trans e
  rw [epsilon1_eq_of_ringEquiv_aux e1.symm, epsilon1_eq_of_ringEquiv_aux e2.symm]

end

section epsilon1

variable [IsNoetherianRing R] [IsLocalRing R]

lemma LinearEquiv.comap_smul_top {S : Type u} [CommRing S] {M N : Type*} [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module S N] (I : Ideal S) (e : M ≃ₗ[S] N) :
    (I • (⊤ : Submodule S N)).comap e.toLinearMap = I • (⊤ : Submodule S M) := by
  apply le_antisymm _ (Submodule.smul_top_le_comap_smul_top I _)
  rw [Submodule.comap_equiv_eq_map_symm, Submodule.map_le_iff_le_comap]
  exact Submodule.smul_top_le_comap_smul_top I _

lemma Ideal.rTensor_mkQ_ker {S : Type u} [CommRing S] {M : Type*} [AddCommGroup M] [Module S M]
    (I : Ideal S) : ((Submodule.mkQ I).rTensor M).ker =
    I • (⊤ : Submodule S (TensorProduct S S M)) := by
  have : I.mkQ.rTensor M = (TensorProduct.quotTensorEquivQuotSMul M I).symm.comp
    ((I • ⊤ : Submodule S M).mkQ.comp (TensorProduct.lid S M).toLinearMap) := by
    rw [eq_comm, LinearEquiv.toLinearMap_symm_comp_eq,
      TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor]
  simp [this, LinearMap.ker_comp, LinearEquiv.comap_smul_top]

noncomputable def LinearMap.kerBaseChangeEquiv {S : Type u} [CommRing S] [IsLocalRing S]
    (I : Ideal S) (ne : I ≠ ⊤) : ((maximalIdeal S).subtype.baseChange (S ⧸ I)).ker ≃ₗ[S]
      (I ⧸ (maximalIdeal S) • (⊤ : Submodule S I)) := by
  let p1 : maximalIdeal S →ₗ[S] (TensorProduct S (S ⧸ I) (maximalIdeal S)) :=
    ((Submodule.mkQ I).rTensor (maximalIdeal S)).comp
    (TensorProduct.lid S (maximalIdeal S)).symm.toLinearMap
  let p2 : S →ₗ[S] (TensorProduct S (S ⧸ I) S) :=
    ((Submodule.mkQ I).rTensor S).comp (TensorProduct.lid S S).symm.toLinearMap
  have comm : (((maximalIdeal S).subtype.baseChange (S ⧸ I)).restrictScalars S).comp p1 =
    p2.comp (maximalIdeal S).subtype := by
    ext
    simp [p1, p2]
  have ker1 : (p2.comp (maximalIdeal S).subtype).ker =
    Submodule.comap (maximalIdeal S).subtype I := by
    simp only [ker_comp, p2, Ideal.rTensor_mkQ_ker, LinearEquiv.comap_smul_top, smul_eq_mul,
      Ideal.mul_top]
  let eI : Submodule.comap (maximalIdeal S).subtype I ≃ₗ[S] I :=
    Submodule.comapSubtypeEquivOfLe (le_maximalIdeal ne)
  have comm2 : (TensorProduct.quotTensorEquivQuotSMul (maximalIdeal S) I).comp p1 =
    (I • (⊤ : Submodule S (maximalIdeal S))).mkQ := by
    ext
    simp [p1]
  have kerp1 : p1.ker = I • (⊤ : Submodule S (maximalIdeal S)) := by
    rw [← (I • (⊤ : Submodule S (maximalIdeal S))).ker_mkQ, ← comm2, LinearEquiv.ker_comp]
  let p1r : Submodule.comap (maximalIdeal S).subtype I →ₗ[S]
    ((maximalIdeal S).subtype.baseChange (S ⧸ I)).ker.restrictScalars S :=
    p1.restrict (fun x ↦ by simp [← ker1, ← comm])
  have surjp1 : Function.Surjective p1 := by
    simpa [p1] using LinearMap.rTensor_surjective _ (Submodule.mkQ_surjective _)
  have surjr : Function.Surjective p1r := by
    intro y
    rcases surjp1 y.1 with ⟨z, hz⟩
    refine ⟨⟨z, ?_⟩, SetCoe.ext hz⟩
    simp [← ker1, ← comm, LinearMap.ker_comp, Submodule.mem_comap, hz]
  let eker : _ ≃ₗ[S] ((maximalIdeal S).subtype.baseChange (S ⧸ I)).ker :=
    p1r.quotKerEquivOfSurjective surjr
  exact eker.symm.trans (Submodule.Quotient.equiv _ _ eI (by
    simp only [ker_restrict, kerp1, Submodule.map_equiv_eq_comap_symm, p1r]
    ext y
    simp [eI, Submodule.mem_smul_top_iff, mul_comm]))

set_option backward.isDefEq.respectTransparency false in
lemma epsilon1_eq_spanFinrank (S : Type u) [CommRing S] [IsRegularLocalRing S] (I : Ideal S)
    (le : I ≤ (maximalIdeal S) ^ 2) :
    letI : IsLocalRing (S ⧸ I) :=
      have : Nontrivial (S ⧸ I) :=
        Submodule.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top Ideal.IsPrime.ne_top'
          (le.trans (Ideal.pow_le_self (Nat.zero_ne_add_one 1).symm)))
      have : IsLocalHom (Ideal.Quotient.mk I) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Epsilon1 (S ⧸ I) = I.spanFinrank := by
  have Ine := ne_top_of_le_ne_top Ideal.IsPrime.ne_top'
    (le.trans (Ideal.pow_le_self (Nat.zero_ne_add_one 1).symm))
  let _ : Nontrivial (S ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr Ine
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have sprkeq : (maximalIdeal (S ⧸ I)).spanFinrank = (maximalIdeal S).spanFinrank :=
    spanFinrank_eq_of_surjective_of_ker_le (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (le_of_eq_of_le Ideal.mk_ker le)
  let l := (maximalIdeal S).finite_generators_of_isNoetherian.toFinset.toList
  have eq1 : Ideal.ofList l = maximalIdeal S := by
    simpa [l, Ideal.ofList] using (maximalIdeal S).span_generators
  have len : l.length = (maximalIdeal S).spanFinrank := by
    simp [l, ← Set.ncard_eq_toFinset_card,
      Submodule.FG.generators_ncard (maximalIdeal S).fg_of_isNoetherianRing]
  have len' : (maximalIdeal (S ⧸ I)).finite_generators_of_isNoetherian.toFinset.toList.length =
    (maximalIdeal (S ⧸ I)).spanFinrank := by
    simp [← Set.ncard_eq_toFinset_card,
      Submodule.FG.generators_ncard (maximalIdeal (S ⧸ I)).fg_of_isNoetherianRing]
  let l' := l.map (Ideal.Quotient.mk I)
  have eq2 : Ideal.ofList l' = maximalIdeal (S ⧸ I) := by
    simp only [l', ← Ideal.map_ofList, eq1]
    have comapeq : (maximalIdeal (S ⧸ I)).comap (Ideal.Quotient.mk I) = maximalIdeal S :=
      ((local_hom_TFAE _).out 0 4).mp ‹_›
    simp [← comapeq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have len'' : l'.length = (maximalIdeal (S ⧸ I)).spanFinrank := by simp [sprkeq, l', l, len]
  let e1 := koszulComplex.baseChange_iso (S ⧸ I) (Ideal.Quotient.mk I) l l' rfl
  obtain ⟨e2⟩ := koszulComplex.nonempty_iso_of_minimal_generators' eq2 len''
  let e : koszulAlgebra (S ⧸ I) ≅
    ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
    _).obj (koszulAlgebra S) := e2.trans e1
  let F := (ModuleCat.extendScalars.{u, u, u} (Ideal.Quotient.mk I))
  have preveq : (ComplexShape.down ℕ).prev 1 = 2 := by simp
  have nexteq : (ComplexShape.down ℕ).next 1 = 0 := by simp
  have preveq' : (ComplexShape.down ℕ).prev 0 = 1 := by simp
  have nexteq' : (ComplexShape.down ℕ).next 0 = 0 := by simp
  let h1 := (koszulAlgebra (S ⧸ I)).homology 1
  change Module.finrank (ResidueField (S ⧸ I)) h1 = _
  let eh := HomologicalComplex.homologyMapIso e 1
  let T := (koszulAlgebra S).sc' 2 1 0
  have T_exact : T.Exact := by
    rw [← (koszulAlgebra S).exactAt_iff' 2 1 0 preveq nexteq]
    apply koszulComplex.exactAt_of_isRegular _ _ 1 Nat.one_ne_zero
    apply isRegular_of_span_eq_maximalIdeal
    · simpa [Ideal.ofList] using (maximalIdeal S).span_generators
    · simp [l, len, IsRegularLocalRing.spanFinrank_maximalIdeal]
  let eh' : h1 ≃ₗ[S⧸ I] (T.map F).homology :=
    (eh.trans (HomologicalComplex.homologyIsoSc' _ 2 1 0 preveq nexteq)).toLinearEquiv
  let e3 : T.X₃ ≃ₗ[S] S := koszulComplex.XZeroLinearEquivRing (Fintype.linearCombination S
    (maximalIdeal S).finite_generators_of_isNoetherian.toFinset.toList.get)
  let f : T.X₁ →ₗ[S] T.X₂ := T.f.hom
  let g : T.X₂ →ₗ[S] T.X₃ := T.g.hom
  let g' : T.X₂ →ₗ[S] S := e3.comp g
  have exac : Function.Exact f g' := by
    simp only [LinearMap.exact_iff, LinearEquiv.ker_comp, f, g']
    exact LinearMap.exact_iff.mp
      ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp T_exact)
  have rangeg' : g'.range = maximalIdeal S := by
    let eh0 : (koszulAlgebra S).homology 0 ≃ₗ[S] T.X₃ ⧸ g.range :=
      (((koszulAlgebra S).isoHomologyι₀.trans
      ((koszulAlgebra S).opcyclesIsoSc' 1 0 0 preveq' nexteq')).trans
      ((koszulAlgebra S).sc' 1 0 0).moduleCatOpcyclesIso).toLinearEquiv
    let eqr : (T.X₃ ⧸ g.range) ≃ₗ[S] S ⧸ g'.range :=
      Submodule.Quotient.equiv _ _ e3 (g.range_comp _).symm
    let E := (koszulComplex.zeroHomologyLinearEquiv l).symm.trans (eh0.trans eqr)
    simpa [Ideal.annihilator_quotient, eq1] using E.annihilator_eq.symm
  let g'r := g'.codRestrict (maximalIdeal S) (by simp [← rangeg'])
  have compeq : (maximalIdeal S).subtype.comp g'r = g' :=
    g'.subtype_comp_codRestrict (maximalIdeal S) (by simp [← rangeg'])
  have exac' : Function.Exact f g'r := by
    rw [LinearMap.exact_iff, g'.ker_codRestrict, ← LinearMap.exact_iff]
    exact exac
  have surj' : Function.Surjective g'r := by
    intro x
    rcases le_of_eq rangeg'.symm x.2 with ⟨y, hy⟩
    exact ⟨y, SetCoe.ext hy⟩
  have surj'' : Function.Surjective (g'r.baseChange (S ⧸ I)) :=
    g'r.lTensor_surjective (S ⧸ I) surj'
  have req : Function.Exact (f.baseChange (S ⧸ I)) (g'r.baseChange (S ⧸ I)) :=
    lTensor_exact (S ⧸ I) exac' surj'
  rw [LinearMap.exact_iff] at req
  have keq : (g.baseChange (S ⧸ I)).ker = (g'.baseChange (S ⧸ I)).ker := by
    simpa [g', LinearMap.baseChange_comp] using ((e3.baseChange S (S ⧸ I)).ker_comp _).symm
  rw [← compeq, LinearMap.baseChange_comp, LinearMap.ker_comp] at keq
  let K := ((maximalIdeal S).subtype.baseChange (S ⧸ I)).ker
  let eK : K ≃ₗ[S] (I ⧸ (maximalIdeal S) • (⊤ : Submodule S I)) :=
    LinearMap.kerBaseChangeEquiv I Ine
  let eh'' : h1 ≃ₗ[S ⧸ I] (g.baseChange (S ⧸ I)).ker ⧸ (T.map F).moduleCatToCycles.range :=
    eh'.trans (T.map F).moduleCatHomologyIso.toLinearEquiv
  let h : (g.baseChange (S ⧸ I)).ker →ₗ[S ⧸ I] K :=
    (g'r.baseChange (S ⧸ I)).restrict (by simp [keq, K])
  have surjh : Function.Surjective h := by
    intro x
    rcases surj'' x.1 with ⟨y, hy⟩
    exact ⟨⟨y, by simp [keq, Submodule.mem_comap, hy]⟩, SetCoe.ext hy⟩
  have kerh : h.ker = (T.map F).moduleCatToCycles.range := by
    change h.ker = ((f.baseChange (S ⧸ I)).codRestrict _ _).range
    simp only [LinearMap.ker_restrict, h]
    ext y
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker]
    rw [← LinearMap.mem_ker, req]
    refine ⟨fun ⟨z, hz⟩ ↦ ⟨z, SetCoe.ext hz⟩, fun h ↦ ?_⟩
    rcases h with ⟨z, hz⟩
    use z
    simp [← hz]
  let eK' : h1 ≃ₗ[S ⧸ I] K :=
    eh''.trans ((Submodule.quotEquivOfEq _ _ kerh.symm).trans (h.quotKerEquivOfSurjective surjh))
  let _ : Module (ResidueField S) (I ⧸ maximalIdeal S • (⊤ : Submodule S I)) :=
    inferInstanceAs (Module (S ⧸ maximalIdeal S) _)
  have rk := rank_eq_of_equiv_equiv (ResidueField.map (Ideal.Quotient.mk I))
    (eK'.toAddEquiv.trans eK.toAddEquiv).symm
    (ResidueField.map_bijective_of_surjective _ Ideal.Quotient.mk_surjective) (fun r m ↦ by
    rcases IsLocalRing.residue_surjective r with ⟨s, hs⟩
    simp only [← hs, AddEquiv.symm_trans_apply]
    change eK'.symm (eK.symm (s • m)) = (Ideal.Quotient.mk I s) • eK'.symm (eK.symm m)
    rw [map_smul eK.symm, ← map_smul eK'.symm]
    rfl)
  have frk : Module.finrank (ResidueField S) (I ⧸ maximalIdeal S • (⊤ : Submodule S I)) =
    Module.finrank (ResidueField (S ⧸ I)) h1 := by
    simp [Module.finrank, rk]
  exact ((spanFinrank_eq_finrank_quotient I I.fg_of_isNoetherianRing).trans frk).symm

set_option backward.isDefEq.respectTransparency false in
lemma epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank_of_surjective (S : Type u)
    [CommRing S] [IsRegularLocalRing S] (R : Type*) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (f : S →+* R) (surj : Function.Surjective f) :
    Epsilon1 R + ringKrullDim S = (RingHom.ker f).spanFinrank + (maximalIdeal R).spanFinrank := by
  obtain ⟨n, hn⟩ : ∃ n, (maximalIdeal R).spanFinrank + n = (maximalIdeal S).spanFinrank :=
    Nat.le.dest (spanFinrank_le_of_surjective (maximalIdeal S).fg_of_isNoetherianRing f surj)
  induction n generalizing S with
  | zero =>
    let e := RingHom.quotientKerEquivOfSurjective surj
    let _ : Nontrivial (S ⧸ RingHom.ker f) := e.nontrivial
    let _ : IsLocalRing (S ⧸ RingHom.ker f) :=
      have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (RingHom.ker f)) Ideal.Quotient.mk_surjective
    simp only [← (isRegularLocalRing_def S).mp ‹_›, ← Nat.cast_add, Nat.cast_inj]
    have : RingHom.ker f ≤ (maximalIdeal S) ^ 2 := by
      intro x hx
      by_contra nmem
      have le : RingHom.ker f ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
      obtain ⟨reg, dim⟩ := quotient_span_singleton S (le hx) nmem
      have : ∀ y ∈ Ideal.span {x}, f y = 0 := by
        intro y hy
        rcases Ideal.mem_span_singleton.mp hy with ⟨z, hz⟩
        simp [hz, RingHom.mem_ker.mp hx]
      have surj' := Ideal.Quotient.lift_surjective_of_surjective _ this surj
      rw [← (isRegularLocalRing_def _).mp reg, ← (isRegularLocalRing_def _).mp ‹_›,
        ← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj] at dim
      absurd spanFinrank_le_of_surjective (maximalIdeal _).fg_of_isNoetherianRing _ surj'
      omega
    rw [spanFinrank_eq_of_surjective_of_ker_le f surj this,
      ← epsilon1_eq_of_ringEquiv e, epsilon1_eq_spanFinrank S _ this]
  | succ n ih =>
    obtain ⟨x, hx, nmem⟩ : ∃ x ∈ RingHom.ker f, x ∉ (maximalIdeal S) ^ 2 := by
      by_contra! mem
      simp [spanFinrank_eq_of_surjective_of_ker_le f surj mem] at hn
    have le : RingHom.ker f ≤ maximalIdeal S := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
    obtain ⟨reg, dim⟩ := quotient_span_singleton S (le hx) nmem
    have eq0 : ∀ y ∈ Ideal.span {x}, f y = 0 := by
      intro y hy
      rcases Ideal.mem_span_singleton.mp hy with ⟨z, hz⟩
      simp [hz, RingHom.mem_ker.mp hx]
    have surj' := Ideal.Quotient.lift_surjective_of_surjective _ eq0 surj
    have dim' := dim
    rw [← (isRegularLocalRing_def _).mp reg, ← (isRegularLocalRing_def _).mp ‹_›,
      ← Nat.cast_one, ← Nat.cast_add, Nat.cast_inj] at dim'
    have ih' := ih (S ⧸ Ideal.span {x}) _ surj' (by omega)
    rw [← dim, ← add_assoc, ih', add_assoc, add_comm _ 1, ← add_assoc, ← Nat.cast_one,
      ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_inj, Nat.add_right_cancel_iff]
    apply (spanFinrank_comap S x _ (RingHom.ker f) _ (le hx) _).symm
    · ext y
      simp
    · simp only [pow_two] at nmem
      exact Not.intro fun a ↦ nmem (Ideal.mul_mono_right le a)

lemma epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (I : Ideal S) (ne : I ≠ ⊤) :
    letI : IsLocalRing (S ⧸ I) :=
      have : Nontrivial (S ⧸ I) :=
        Submodule.Quotient.nontrivial_iff.mpr ne
      have : IsLocalHom (Ideal.Quotient.mk I) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    Epsilon1 (S ⧸ I) + ringKrullDim S = I.spanFinrank + (maximalIdeal (S ⧸ I)).spanFinrank := by
  let _ := Submodule.Quotient.nontrivial_iff.mpr ne
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let _ : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  convert epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank_of_surjective S (S ⧸ I)
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  exact Ideal.mk_ker.symm

set_option backward.isDefEq.respectTransparency false in
lemma AdicCompletion.epsilon1_eq : Epsilon1 (AdicCompletion (maximalIdeal R) R) = Epsilon1 R := by
  let R' := (AdicCompletion (maximalIdeal R) R)
  let flat : Module.Flat R R' := AdicCompletion.flat_of_isNoetherian (maximalIdeal R)
  let l := (maximalIdeal R).finite_generators_of_isNoetherian.toFinset.toList
  let l' := l.map (algebraMap R R')
  have eq1 : Ideal.ofList l = maximalIdeal R := by
    simpa [l, Ideal.ofList] using (maximalIdeal R).span_generators
  have eqmap : maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') :=
    AdicCompletion.maximalIdeal_eq_map
  have eq2 : Ideal.ofList l' = maximalIdeal R' := by
    simp only [← Ideal.map_ofList, eq1, l', R', eqmap]
  have len1 : l.length = (maximalIdeal R).spanFinrank := by
    simp only [Finset.length_toList, l, ← Set.ncard_eq_toFinset_card,
      Submodule.FG.generators_ncard (maximalIdeal R).fg_of_isNoetherianRing]
  have sprkeq : (maximalIdeal R').spanFinrank = (maximalIdeal R).spanFinrank :=
    AdicCompletion.spanFinrank_maximalIdeal_eq
  have len2 : l'.length = (maximalIdeal R').spanFinrank := by
    simp [R', l', sprkeq, len1]
  let e1 := koszulComplex.baseChange_iso _ (algebraMap R R') l l' rfl
  obtain ⟨e2⟩ := koszulComplex.nonempty_iso_of_minimal_generators' eq2 len2
  let F := (ModuleCat.extendScalars (algebraMap R R'))
  let e : koszulAlgebra R' ≅ (F.mapHomologicalComplex _).obj (koszulAlgebra R) := e2.trans e1
  let h1R := (koszulAlgebra R).homology 1
  let h1R' := (koszulAlgebra R').homology 1
  let _ : F.PreservesHomology := preservesHomology_of_flat R R' (algebraMap R R') flat
  let eh : h1R' ≅ F.obj h1R :=
    (HomologicalComplex.homologyMapIso e 1).trans (((koszulAlgebra R).sc 1).mapHomologyIso F)
  let eh' : ↑h1R' ≃ₗ[R'] TensorProduct R R' ↑h1R := eh.toLinearEquiv
  simp only [Epsilon1]
  let I := Module.Free.ChooseBasisIndex (ResidueField R) h1R
  let _ : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
  let B : h1R ≃ₗ[ResidueField R] I →₀ ResidueField R :=
    (Module.Free.chooseBasis (ResidueField R) h1R).repr
  rw [B.finrank_eq, Module.finrank_finsupp_self]
  let eres : ResidueField R' ≃ₗ[R'] TensorProduct R R' (ResidueField R) :=
    (Submodule.quotEquivOfEq _ _ eqmap).trans (Ideal.qoutMapEquivTensorQout R')
  let eh'' : h1R' ≃ₗ[ResidueField R'] I →₀ ResidueField R' :=
    (eh'.trans ((((B.restrictScalars R).baseChange R R').trans
    (TensorProduct.finsuppRight R R' R' (ResidueField R) I)).trans
    (Finsupp.mapRange.linearEquiv eres.symm))).extendScalarsOfSurjective residue_surjective
  rw [eh''.finrank_eq, Module.finrank_finsupp_self]

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
lemma epsilon1_add_ringKrullDim_ge :
    Epsilon1 R + ringKrullDim R ≥ (maximalIdeal R).spanFinrank := by
  rcases exist_isRegularLocalRing_surjective_adicCompletion_ker_le R with ⟨S, _, reg, f, surj, le⟩
  let e := RingHom.quotientKerEquivOfSurjective surj
  let _ : Nontrivial (S ⧸ RingHom.ker f) := e.nontrivial
  let _ : IsLocalRing (S ⧸ RingHom.ker f) :=
    have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk (RingHom.ker f)) Ideal.Quotient.mk_surjective
  rw [← AdicCompletion.epsilon1_eq, ← AdicCompletion.ringKrullDim_eq,
    ← AdicCompletion.spanFinrank_maximalIdeal_eq, ← epsilon1_eq_of_ringEquiv e,
    ← ringKrullDim_eq_of_ringEquiv e, epsilon1_eq_spanFinrank S (RingHom.ker f) le, ge_iff_le]
  apply le_of_eq_of_le _ (add_le_add_left (WithBot.coe_le_coe.mpr
    (Ideal.height_le_spanFinrank _ (RingHom.ker_ne_top f))) (ringKrullDim (S ⧸ RingHom.ker f)))
  rw [Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim _ (RingHom.ker_ne_top f),
    ← (isRegularLocalRing_def S).mp reg, spanFinrank_eq_of_surjective_of_ker_le f surj le]

end epsilon1

variable [IsNoetherianRing R] [IsLocalRing R]

class IsCompleteIntersectionLocalRing extends IsLocalRing R, IsNoetherianRing R where
  ci : Epsilon1 R + ringKrullDim R = (maximalIdeal R).spanFinrank

lemma isCompleteIntersectionLocalRing_def : IsCompleteIntersectionLocalRing R ↔
    Epsilon1 R + ringKrullDim R = (maximalIdeal R).spanFinrank :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma isCompleteIntersectionLocalRing_of_ringEquiv {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {R' : Type*} [CommRing R'] [IsNoetherianRing R'] [IsLocalRing R']
    (e : R ≃+* R') [IsCompleteIntersectionLocalRing R] : IsCompleteIntersectionLocalRing R' := by
  simpa [isCompleteIntersectionLocalRing_def, ← epsilon1_eq_of_ringEquiv e,
    ← ringKrullDim_eq_of_ringEquiv e, ← spanFinrank_eq_of_ringEquiv e]
    using (isCompleteIntersectionLocalRing_def R).mp ‹_›

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
lemma quotient_isCompleteIntersectionLocalRing (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (I : Ideal S) [IsCompleteIntersectionLocalRing (S ⧸ I)] :
    ∃ (rs : List S), I = Ideal.ofList rs ∧ IsRegular S rs := by
  obtain ⟨d, hd⟩ : ∃ (d : ℕ), ringKrullDim (S ⧸ I) = d := by
    generalize hn : ringKrullDim (S ⧸ I) = n
    induction n with
    | bot =>
      absurd hn
      exact ringKrullDim_ne_bot
    | coe n =>
      induction n with
      | top =>
        absurd hn
        exact ringKrullDim_ne_top
      | coe n => exact ⟨n, rfl⟩
  have ne : I ≠ ⊤ :=  Submodule.Quotient.nontrivial_iff.mp inferInstance
  have := epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank S I ne
  rw [← (isCompleteIntersectionLocalRing_def (S ⧸ I)).mp ‹_›,
    add_comm (Epsilon1 (S ⧸ I) : WithBot ℕ∞), add_comm (Epsilon1 (S ⧸ I) : WithBot ℕ∞),
    ← add_assoc, WithBot.add_natCast_cancel,
    ← Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim I ne, hd,
    WithBot.add_natCast_cancel] at this
  let fin := Submodule.FG.finite_generators I.fg_of_isNoetherianRing
  let _ : Fintype I.generators := fin.fintype
  let rs := I.generators.toFinset.toList
  have spaneq : Ideal.ofList rs = I := by
    simpa [Ideal.ofList, rs] using I.span_generators
  use rs
  refine ⟨spaneq.symm, ?_⟩
  have mem : ∀ r ∈ rs, r ∈ maximalIdeal S := by
    intro r hr
    simp only [Finset.mem_toList, Set.mem_toFinset, rs] at hr
    exact le_maximalIdeal ne (Submodule.FG.generators_mem I hr)
  apply isRegular_of_ofList_height_eq_length_of_isCohenMacaulayLocalRing rs mem
  simp only [spaneq, Finset.length_toList, ← Set.ncard_eq_toFinset_card',
    Submodule.FG.generators_ncard I.fg_of_isNoetherianRing, rs]
  rw [← WithBot.coe_inj, this]
  rfl

--set_option backward.isDefEq.respectTransparency false in
attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
lemma quotient_isCompleteIntersectionLocalRing_iff (S : Type u) [CommRing S] [IsRegularLocalRing S]
    (I : Ideal S) (ne : I ≠ ⊤) : IsCompleteIntersectionLocalRing (S ⧸ I) ↔
    ∃ (rs : List S), I = Ideal.ofList rs ∧ IsRegular S rs := by
  refine ⟨fun h ↦ quotient_isCompleteIntersectionLocalRing S I, fun ⟨rs, hrs, reg⟩ ↦ ?_⟩
  let _ : Nontrivial (S ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr ne
  let _ : IsLocalRing (S ⧸ I) :=
    have : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    IsLocalRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have eqht : (I.spanFinrank : WithBot ℕ∞) = I.height := by
    change ((I.spanFinrank : ℕ∞) : WithBot ℕ∞) = _
    classical
    apply WithBot.coe_inj.mpr (le_antisymm _ (Ideal.height_le_spanFinrank _ ne))
    let : CharZero ℕ∞ := instCharZeroENat
    have : Ideal.span (rs.toFinset : Set S) = I := by simp [hrs]
    nth_rw 2 [hrs]
    rw [Ideal.ofList_height_eq_length_of_isWeaklyRegular rs reg.1 (by simpa using reg.2.symm),
      Nat.cast_le, ← this]
    exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite rs.toFinset.finite_toSet)
      (le_of_eq_of_le (Set.ncard_coe_finset rs.toFinset) rs.toFinset_card_le)
  rw [isCompleteIntersectionLocalRing_def,
    ← WithBot.add_natCast_cancel (c := (maximalIdeal S).spanFinrank),
    (isRegularLocalRing_def S).mp ‹_›, add_assoc, add_comm _ (ringKrullDim _), ← add_assoc,
    epsilon1_add_ringKrullDim_eq_spanFinrank_add_spanFinrank _ _ ne,
    add_assoc, add_comm _ (ringKrullDim (S ⧸ I)), ← add_assoc, eqht,
    Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim _ ne, add_comm]

lemma adicCompletion_isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    IsCompleteIntersectionLocalRing (AdicCompletion (maximalIdeal R) R) := by
  simp [isCompleteIntersectionLocalRing_def, AdicCompletion.epsilon1_eq,
    AdicCompletion.spanFinrank_maximalIdeal_eq, AdicCompletion.ringKrullDim_eq]

attribute [local instance] isCohenMacaulayLocalRing_of_isRegularLocalRing in
theorem isCompleteIntersectionLocalRing_iff :
    IsCompleteIntersectionLocalRing R ↔
    ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S)
      (f : S →+* (AdicCompletion (maximalIdeal R) R)) (rs : List S), Function.Surjective f ∧
      RingHom.ker f = Ideal.ofList rs ∧ IsRegular S rs := by
  rw [adicCompletion_isCompleteIntersectionLocalRing_iff]
  refine ⟨fun h ↦ ?_, fun ⟨S, _, regS, f, rs, surj, hrs, reg⟩ ↦ ?_⟩
  · rcases exist_isRegularLocalRing_surjective_adicCompletion R with ⟨S, _, regS, f, surj⟩
    let e := RingHom.quotientKerEquivOfSurjective surj
    let _ : Nontrivial (S ⧸ RingHom.ker f) := e.nontrivial
    let _ : IsLocalRing (S ⧸ RingHom.ker f) :=
      have : IsLocalHom (Ideal.Quotient.mk (RingHom.ker f)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      IsLocalRing.of_surjective (Ideal.Quotient.mk (RingHom.ker f)) Ideal.Quotient.mk_surjective
    let _ := isCompleteIntersectionLocalRing_of_ringEquiv e.symm
    rcases quotient_isCompleteIntersectionLocalRing S (RingHom.ker f) with ⟨rs, hrs⟩
    use S, inferInstance, inferInstance, f, rs
  · let e := RingHom.quotientKerEquivOfSurjective surj
    let _ : IsCompleteIntersectionLocalRing (S ⧸ RingHom.ker f) :=
      (quotient_isCompleteIntersectionLocalRing_iff S _ (RingHom.ker_ne_top f)).mpr ⟨rs, hrs, reg⟩
    exact isCompleteIntersectionLocalRing_of_ringEquiv e
