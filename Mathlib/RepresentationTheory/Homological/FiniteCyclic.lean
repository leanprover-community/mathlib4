import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.Attr.Register

universe v u

open CategoryTheory

namespace Action

variable (V : Type*) [Category V] {G H : Type*} [Monoid G] [Monoid H] (f : G ≃* H)

instance : (res V (f : G →* H)).IsEquivalence :=
  Functor.IsEquivalence.mk' (res V f.symm)
    (NatIso.ofComponents (fun _ => Action.mkIso (Iso.refl _) <| by simp) <| by aesop)
    (NatIso.ofComponents (fun _ => Action.mkIso (Iso.refl _) <| by simp) <| by aesop)

end Action

namespace Rep

open Multiplicative

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
variable (A : Rep k G)

theorem mem_zmultiples_ofMul_iff {G : Type*} [Group G] {x : Additive G} {y : G} :
    x ∈ AddSubgroup.zmultiples (Additive.ofMul y) ↔ x.toMul ∈ Subgroup.zpowers y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, by simp [← hz]⟩, fun ⟨z, hz⟩ => ⟨z, Additive.toMul.injective <| by simp_all⟩⟩

theorem mem_zpowers_ofAdd_iff {G : Type*} [AddGroup G] {x : Multiplicative G} {y : G} :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd y) ↔ x.toAdd ∈ AddSubgroup.zmultiples y :=
  ⟨fun ⟨z, hz⟩ => ⟨z, by simp [← hz]⟩,
   fun ⟨z, hz⟩ => ⟨z, Multiplicative.toAdd.injective <| by simp_all⟩⟩

theorem exists_mulEquiv_of_finite_cyclic (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ∃ e : ULift.{u} (Multiplicative (ZMod (orderOf g))) ≃* G, e ⟨ofAdd 1⟩ = g :=
  match hm : orderOf g with
  | .zero => False.elim <| orderOf_eq_zero_iff.1 hm <| isOfFinOrder_of_finite g
  | .succ m =>
    ⟨MulEquiv.ulift.trans (mulEquivOfOrderOfEq (g := ofAdd 1) (fun x => mem_zpowers_ofAdd_iff.2
      ⟨(toAdd x).1, by simp [ZMod]⟩) hg (by simp_all)), by simp [MulEquiv.ulift]⟩

@[simps]
noncomputable def applyAsHom (g : G) : A ⟶ A where
  hom := ModuleCat.ofHom (A.ρ g)
  comm _ := by ext; simp [← Module.End.mul_apply, ← map_mul, Std.Commutative.comm]

end Rep

namespace AlternatingComplex

open ShortComplex

variable {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
  (A : C) {φ : A ⟶ A} {ψ : A ⟶ A} (hOdd : φ ≫ ψ = 0) (hEven : ψ ≫ φ = 0)

@[simp]
lemma up_odd_add {i j : ℕ} (h : (ComplexShape.up ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

@[simp]
lemma down_odd_add {i j : ℕ} (h : (ComplexShape.down ℕ).Rel i j) : Odd (i + j) := by
  subst h
  norm_num

noncomputable def complex {c : ComplexShape ℕ} [DecidableRel c.Rel]
    (hc : ∀ i j, c.Rel i j → Odd (i + j)) :
    HomologicalComplex C c where
  X n := A
  d i j :=
    if hij : c.Rel i j then
      if hi : Even i then φ
      else ψ
    else 0
  shape i j := by aesop
  d_comp_d' i j k hij hjk := by
    have := hc i j hij
    split_ifs with hi hj hj
    · exact False.elim <| Nat.not_odd_iff_even.2 hi <| by simp_all [Nat.odd_add]
    · assumption
    · assumption
    · exact False.elim <| hj <| by simp_all [Nat.odd_add]

variable {c : ComplexShape ℕ} [DecidableRel c.Rel] (hc : ∀ i j, c.Rel i j → Odd (i + j))

open HomologicalComplex hiding mk

noncomputable def complex.scEvenIso
    {i j k : ℕ} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Even j) :
    (complex A hOdd hEven hc).sc' i j k ≅ mk ψ φ hEven :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [complex, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, right_eq_ite_iff]
      intro hi
      have := hc i j hij
      exact False.elim <| Nat.not_odd_iff_even.2 hi <| by simp_all [Nat.odd_add])
    (by simp_all [complex])

noncomputable def complex.scOddIso
    {i j k : ℕ} (hij : c.Rel i j) (hjk : c.Rel j k) (h : Odd j) :
    (complex A hOdd hEven hc).sc' i j k ≅ mk φ ψ hOdd :=
  isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      simp_all only [complex, dite_eq_ite, Iso.refl_hom, Category.id_comp,
        shortComplexFunctor'_obj_f, ↓reduceIte, Category.comp_id, left_eq_ite_iff]
      intro hi
      have := hc i j hij
      exact False.elim <| Nat.not_even_iff_odd.2 h <| by simp_all [Nat.odd_add])
    (by simp_all [complex])

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma complex.iCycles_comp_norm [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (complex A hOdd hEven hc).iCycles j ≫ φ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso (scEvenIso A hOdd hEven hc hpj hnj  h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, scEvenIso,
    Category.id_comp (X := (complex A hOdd hEven hc).X _)] using (mk ψ φ hEven).iCycles_g

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma complex.iCycles_comp_applyAsHom [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (complex A hOdd hEven hc).iCycles j ≫ ψ = 0 := by
  rw [← cancel_epi (ShortComplex.cyclesMapIso (scOddIso A hOdd hEven hc hpj hnj h)).inv]
  simpa [HomologicalComplex.iCycles, -Preadditive.IsIso.comp_left_eq_zero, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, scOddIso,
    Category.id_comp (X := (complex A hOdd hEven hc).X _)] using (mk φ ψ hOdd).iCycles_g

noncomputable def complex.homologyEvenIso [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Even j) :
    (complex A hOdd hEven hc).homology j ≅ (mk ψ φ hEven).homology :=
  ShortComplex.homologyMapIso (scEvenIso A hOdd hEven hc hpj hnj h)

noncomputable def complex.homologyOddIso [CategoryWithHomology C]
    {j : ℕ} (hpj : c.Rel (c.prev j) j) (hnj : c.Rel j (c.next j)) (h : Odd j) :
    (complex A hOdd hEven hc).homology j ≅ (mk φ ψ hOdd).homology :=
  ShortComplex.homologyMapIso (scOddIso A hOdd hEven hc hpj hnj h)

noncomputable abbrev chainComplex : ChainComplex C ℕ :=
  complex A hOdd hEven (fun _ _ => down_odd_add)

noncomputable abbrev cochainComplex : CochainComplex C ℕ :=
  complex A hEven hOdd (fun _ _ => up_odd_add)

end AlternatingComplex

namespace Rep.finiteCyclicGroup

open ShortComplex

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] (A : Rep k G) (g : G)

noncomputable abbrev chainComplex :=
  AlternatingComplex.chainComplex A (φ := A.norm) (ψ := applyAsHom A g - 𝟙 A)
    (by ext; simp [sub_eq_add_neg]) (by ext; simp [sub_eq_add_neg])

noncomputable abbrev cochainComplex :=
  AlternatingComplex.cochainComplex A (φ := A.norm) (ψ := applyAsHom A g - 𝟙 A)
    (by ext; simp [sub_eq_add_neg]) (by ext; simp [sub_eq_add_neg])

noncomputable abbrev normHomCompSub : ShortComplex (ModuleCat k) :=
  mk A.norm.hom (applyAsHom A g - 𝟙 A).hom (by ext; simp [sub_eq_add_neg])

noncomputable abbrev subCompNormHom : ShortComplex (ModuleCat k) :=
  mk (applyAsHom A g - 𝟙 A).hom A.norm.hom (by ext; simp [sub_eq_add_neg])

noncomputable abbrev moduleCatChainComplex :=
  AlternatingComplex.chainComplex A.V (φ := A.norm.hom) (ψ := (applyAsHom A g - 𝟙 A).hom)
    (by ext; simp [sub_eq_add_neg]) (by ext; simp [sub_eq_add_neg])

noncomputable abbrev moduleCatCochainComplex :=
  AlternatingComplex.cochainComplex A.V (φ := A.norm.hom) (ψ := (applyAsHom A g - 𝟙 A).hom)
    (by ext; simp [sub_eq_add_neg]) (by ext; simp [sub_eq_add_neg])

end finiteCyclicGroup

variable (k : Type u) [CommRing k]

noncomputable abbrev C (n : ℕ) := leftRegular k (ULift <| Multiplicative <| ZMod (n + 1))

variable (n : ℕ)
open Multiplicative

@[simp]
lemma _root_.Multiplicative.ofAdd_down {α : Type u} [Add α] (x : ULift α) :
    (ofAdd x).down = ofAdd x.down := rfl

@[simp]
lemma _root_.Additive.ofMul_down {α : Type u} [Mul α] (x : ULift α) :
    (Additive.ofMul x).down = Additive.ofMul x.down := rfl

open Finsupp

variable {k n} in
lemma coeff_eq_of_mem_ker
    (x : C k n) (hx : (applyAsHom (C k n) ⟨ofAdd 1⟩).hom x - x = 0)
    (i : ULift <| Multiplicative <| ZMod (n + 1)) :
    x i = x 1 := by
  refine i.rec fun i => i.rec fun i => i.inductionOn rfl fun i hi => ?_
  · rw [← hi, ← sub_eq_zero.1 (Finsupp.ext_iff.1 hx ⟨ofAdd i.succ⟩)]
    simp only [applyAsHom_hom, of_ρ, ModuleCat.hom_ofHom, Representation.ofMulAction_apply, ZMod]
    congr
    apply ULift.ext
    simp [← ofAdd_neg, ← ofAdd_add, neg_add_eq_sub, -ofAdd_sub, sub_eq_iff_eq_add]

lemma exactness (x : C k n) (hx : (applyAsHom (C k n) ⟨ofAdd 1⟩).hom x - x = 0) :
    ∃ y : C k n, (C k n).norm.hom y = x := by
  use single 1 (x 1)
  ext j
  simp [Representation.norm, coeff_eq_of_mem_ker _ hx]

lemma norm_apply :
    ConcreteCategory.hom (C k n).norm.hom =
      (LinearMap.lsmul k _).flip ((C k n).norm.hom (single 1 1)) ∘ₗ
      Finsupp.linearCombination _ (fun _ => 1) := by
  ext i : 2
  simpa [Representation.norm] using Finset.sum_bijective _
    (Group.mulRight_bijective i) (by aesop) (by aesop)

lemma coeff_sum_of_norm_eq_zero (x : C k n) (hx : (C k n).norm.hom x = 0) :
    x.linearCombination k (fun _ => (1 : k)) = 0 := by
  rw [norm_apply] at hx
  simpa [norm, Representation.norm] using Finsupp.ext_iff.1 hx 1

lemma norm_eq_zero_of_coeff_sum (x : C k n) (hx : x.linearCombination k (fun _ => (1 : k)) = 0) :
    (C k n).norm.hom x = 0 := by
  rw [norm_apply]
  ext
  simp_all

lemma _root_.Fin.neg_one : -(1 : Fin (n + 1)) = Fin.last n := by
  apply add_right_cancel (b := 1)
  norm_num

lemma _root_.Fin.succ_neg_one : (-(1 : Fin (n + 1))).succ = Fin.last (n + 1) := by
  rw [Fin.neg_one]
  norm_num

lemma _root_.Fin.succ_sub_one (i : Fin n) :
    i.succ - 1 = i.castSucc := by
  rw [sub_eq_iff_eq_add]
  norm_num

@[to_additive]
theorem _root_.Fin.partialProd_of_succ_eq {n : ℕ} {M : Type*} [Monoid M] {f : Fin n → M}
    (j : Fin n) {i : Fin (n + 1)} (hij : j.succ = i) :
    Fin.partialProd f i = Fin.partialProd f (Fin.castSucc j) * f j :=
  hij ▸ Fin.partialProd_succ _ _

@[to_additive]
lemma _root_.Fin.partialProd_castSucc {n : ℕ} {M : Type*} [Monoid M]
    {f : Fin (n + 1) → M} {i : Fin (n + 1)} :
    Fin.partialProd (f ∘ Fin.castSucc) i = Fin.partialProd f i.castSucc := by
  refine i.inductionOn ?_ ?_
  · simp
  · intro i hi
    simp_all [Fin.partialProd_succ]

lemma _root_.Fin.partialSum_last (x : Fin (n + 1) → k) :
    Fin.partialSum x (Fin.last (n + 1)) = ∑ i, x i := by
  induction' n with n hn
  · rw [Fin.partialSum_of_succ_eq 0] <;> simp
  · have := hn (x ∘ Fin.castSucc)
    rw [Fin.partialSum_castSucc] at this
    rw [Fin.partialSum_of_succ_eq (Fin.last (n + 1)) (by aesop),
      Fintype.sum_eq_add_sum_subtype_ne _ (Fin.last (n + 1)), add_comm, this, add_right_inj]
    exact Finset.sum_bijective (fun i => Subtype.mk i.castSucc (Fin.castSucc_ne_last _))
      ⟨fun _ _ _ => by simp_all, fun x => ⟨x.1.castPred x.2, by simp⟩⟩ (by aesop) (by aesop)

lemma exactness₂ (x : C k n) (hx : (C k n).norm.hom x = 0) :
    ∃ y : C k n, (applyAsHom (C k n) ⟨ofAdd 1⟩).hom y - y = x := by
  use Finsupp.equivFunOnFinite.symm
    (-Fin.partialSum (x ∘ ULift.up ∘ ofAdd) ∘ Fin.succ ∘ toAdd ∘ ULift.down)
  ext i
  refine i.rec fun i => i.rec fun i => i.cases ?_ fun i => ?_
  · replace hx : (C k n).norm.hom x 1 = 0 := Finsupp.ext_iff.1 hx 1
    simp only [ofAdd_zero, coe_sub, Pi.sub_apply, equivFunOnFinite_symm_apply_toFun, Pi.neg_apply,
      Function.comp_apply, toAdd_one, Fin.partialSum_of_succ_eq 0, Fin.castSucc_zero,
      Fin.partialSum_zero, zero_add]
    simpa [← neg_eq_zero.2 hx, Representation.norm, Fin.succ_neg_one, Fin.partialSum_last, ZMod]
      using Finset.sum_bijective (ofAdd.trans (Equiv.ulift.symm.trans (MulEquiv.inv _).toEquiv))
        (Equiv.bijective _) (by aesop) (by aesop)
  · have := Fin.partialSum_right_neg (x ∘ ULift.up ∘ ofAdd) i.succ
    simp_all [equivFunOnFinite, neg_add_eq_sub, ZMod, Fin.succ_sub_one, ← Fin.castSucc_succ]

lemma exactness₃ (x : C k n) (hx : x.linearCombination k (fun _ => (1 : k)) = 0) :
    ∃ y : C k n, (applyAsHom (C k n) ⟨ofAdd 1⟩).hom y - y = x := by
  exact exactness₂ _ _ _ (norm_eq_zero_of_coeff_sum _ _ _ hx)

open ZeroObject

namespace finiteCyclicGroup

variable (k : Type u) {G : Type u} [CommRing k] [CommGroup G] [Fintype G] (g : G) (A : Rep k G)

@[simps!]
noncomputable def resolution.π (g : G) :
    chainComplex (leftRegular k G) g ⟶
      (ChainComplex.single₀ (Rep k G)).obj (trivial k G k) :=
  ((chainComplex _ g).toSingle₀Equiv _).symm
    ⟨leftRegularHom _ 1, (leftRegularHomEquiv _).injective <| by
      simp [AlternatingComplex.complex, leftRegularHomEquiv, sub_eq_add_neg]⟩

@[simps!]
noncomputable def resChainComplexLeftRegularIso {G G' : Type u} [CommGroup G] [Fintype G]
    [CommGroup G'] [Fintype G'] (e : G ≃* G') (g : G) (g' : G') (he : e g = g') :
    ((Action.res (ModuleCat k) (e : G →* G')).mapHomologicalComplex _).obj
      (chainComplex (leftRegular k G') g') ≅ chainComplex (leftRegular k G) g :=
  HomologicalComplex.Hom.isoOfComponents (fun n => Action.mkIso
    (mapDomain.linearEquiv _ _ e.symm).toModuleIso fun g =>
    ModuleCat.hom_ext <| lhom_ext' fun _ => by
      ext : 1
      simp [ModuleCat.endRingEquiv, AlternatingComplex.complex, mapDomain.linearEquiv]) <|
    fun i j hij => Action.hom_ext _ _ <| ModuleCat.hom_ext <| Finsupp.lhom_ext' fun x => by
      ext
      subst hij
      by_cases hj : Odd j
      · simpa [if_pos (Nat.even_add_one.2 <| Nat.not_even_iff_odd.2 hj), Representation.norm,
          AlternatingComplex.complex, mapDomain.linearEquiv, Representation.norm] using
          Finset.sum_bijective e e.bijective (by aesop) (by aesop)
      · simp [AlternatingComplex.complex, if_neg (Nat.not_even_iff_odd.2 <| Nat.odd_add_one.2 hj),
          sub_eq_add_neg, mapDomain.linearEquiv, ← he]

open Limits

lemma quasiIso_res_map_π {G G' : Type u} [CommGroup G] [Fintype G]
    [CommGroup G'] [Fintype G'] (e : G ≃* G') (g : G) (g' : G') (he : e g = g')
    [_root_.QuasiIso (resolution.π k g)] :
    _root_.QuasiIso (((Action.res (ModuleCat k) (e : G →* G')).mapHomologicalComplex _).map
      (resolution.π k g')) := by
  let E : Arrow.mk (((Action.res (ModuleCat k) (e : G →* G')).mapHomologicalComplex _).map
      (resolution.π k g')) ≅ Arrow.mk (resolution.π k g) :=
    Arrow.isoMk (resChainComplexLeftRegularIso _ _ _ _ he)
      ((HomologicalComplex.singleMapHomologicalComplex
        (Action.res (ModuleCat k) _) (ComplexShape.down ℕ) 0).app (trivial k _ _)) <| by
      apply HomologicalComplex.to_single_hom_ext
      simpa [resChainComplexLeftRegularIso, AlternatingComplex.complex,
        HomologicalComplex.singleObjXIsoOfEq, mapDomain.linearEquiv]
        using Action.hom_ext _ _ <| ModuleCat.hom_ext <| lhom_ext' fun g => by ext; simp
  exact (_root_.quasiIso_iff_of_arrow_mk_iso _ (finiteCyclicGroup.resolution.π k g) E).2 ‹_›

open ShortComplex Representation

instance resolution.finQuasiIsoAt [h0 : NeZero n] (m : ℕ) :
    QuasiIsoAt (finiteCyclicGroup.resolution.π k <| ULift.up <| ofAdd (1 : ZMod n)) m := by
  induction' n with n hn generalizing h0
  · exfalso
    aesop
  induction' m with m _
  · simp [resolution.π]
    rw [ChainComplex.quasiIsoAt₀_iff, quasiIso_iff_of_zeros' _ rfl rfl rfl]
    constructor
    · apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
      simp
      rw [ShortComplex.moduleCat_exact_iff]
      intro (x : _ →₀ k) hx
      have := exactness₃ k n x (by simpa using hx)
      rcases this with ⟨y, hy⟩
      use y
      simp [AlternatingComplex.complex]
      simp [sub_eq_add_neg] at hy ⊢
      exact hy
    · rw [Rep.epi_iff_surjective]
      intro x
      use single 1 x
      simp [AlternatingComplex.complex, ChainComplex.toSingle₀Equiv]
  · by_cases hm : Odd (m + 1)
    · rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
      apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
      rw [ShortComplex.moduleCat_exact_iff]
      intro (x : _ →₀ k) hx
      have := exactness k n x ?_
      · simp [AlternatingComplex.complex, if_pos (Nat.even_add_one.2 (Nat.not_even_iff_odd.2 hm))]
        exact this
      · simp_all [AlternatingComplex.complex, if_neg (Nat.not_even_iff_odd.2 hm), sub_eq_add_neg]
    · rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      rw [HomologicalComplex.exactAt_iff' _ (m + 2) (m + 1) m (by simp) (by simp)]
      apply (Action.forget (ModuleCat k) _).reflects_exact_of_faithful
      rw [ShortComplex.moduleCat_exact_iff]
      intro (x : _ →₀ k) hx
      have := exactness₂ k n x ?_
      · simp_all [AlternatingComplex.complex,
          if_neg (Nat.not_even_iff_odd.2 <| Nat.odd_add_one.2 hm), sub_eq_add_neg]
      · simp_all [AlternatingComplex.complex]

instance resolution.zModQuasiIso [NeZero n] :
    _root_.QuasiIso (resolution.π k <| ULift.up <| ofAdd (1 : ZMod n)) where
  quasiIsoAt _ := inferInstance

instance {G : Type*} [Group G] [Fintype G] (g : G) : NeZero (orderOf g) where
  out h₀ := orderOf_eq_zero_iff.1 h₀ <| isOfFinOrder_of_finite g

lemma resolution.quasiIso {G : Type u} [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) : _root_.QuasiIso (resolution.π k g) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_finite_cyclic g hg
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (finiteCyclicGroup.resolution.π k g) (Action.res (ModuleCat k)
    (e : (ULift.{u} (Multiplicative (ZMod (orderOf g))) →* G)))).1 <| quasiIso_res_map_π k e _ _ he

@[simps]
noncomputable def resolution
    {G : Type u} [CommGroup G] [Fintype G] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ProjectiveResolution (trivial k G k) where
  complex := chainComplex (leftRegular k G) g
  projective _ := inferInstanceAs <| Projective (leftRegular k G)
  π := resolution.π k g
  quasiIso := resolution.quasiIso k g hg

@[simps!]
noncomputable def homResolutionIso {G : Type u} [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) :
    (resolution k g hg).complex.linearYonedaObj k A ≅ moduleCatCochainComplex A g :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => (leftRegularHomEquiv A).toModuleIso) <| by
    rintro i j ⟨rfl⟩
    ext (x : leftRegular _ _ ⟶ _)
    by_cases hi : Even i
    · have : ¬(Even (i + 1)) := (not_iff_comm.1 Nat.even_add_one.symm).2 hi
      simp [AlternatingComplex.complex, hi, this, sub_eq_add_neg, ← hom_comm_apply x]
    · simp [AlternatingComplex.complex, hi, Nat.even_add_one.2 hi, Representation.norm,
        ← hom_comm_apply x]

open ModuleCat.MonoidalCategory in
@[simps!]
noncomputable def coinvariantsTensorResolutionIso {G : Type u} [CommGroup G] [Fintype G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) :
    (resolution k g⁻¹ ((@Subgroup.zpowers_inv G ..).symm ▸ hg)).complex.coinvariantsTensorObj A ≅
      moduleCatChainComplex A g :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (coinvariantsTprodLeftRegularLEquiv A.ρ).toModuleIso) fun i j h =>
    coinvariantsTensor_hom_ext (LinearMap.ext fun a => lhom_ext' fun g => LinearMap.ext_ring (by
    subst h
    by_cases hj : Even (j + 1)
    · simpa [AlternatingComplex.complex, hj, whiskerLeft_def, coinvariantsTensorMk, whiskerLeft,
        tensorObj_def, ofCoinvariantsTprodLeftRegular, tensorObj, Representation.norm,
        ← Module.End.mul_apply, ← map_mul, mul_comm g⁻¹]
        using Finset.sum_bijective _ (MulEquiv.inv G).bijective (by aesop) (by aesop)
    · simp [AlternatingComplex.complex, sub_eq_add_neg, hj, whiskerLeft_def, coinvariantsTensorMk,
        whiskerLeft, tensorObj_def, tensorObj, ← Module.End.mul_apply, ← map_mul, mul_comm g⁻¹]))

open ShortComplex Limits

variable {k}

noncomputable def groupCohomologyIso₀
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) :
    groupCohomology A 0 ≅ (mk _ (applyAsHom A g - 𝟙 A).hom (zero_comp (X := A.V))).cycles :=
  groupCohomologyIso A 0 (resolution k g hg) ≪≫
  HomologicalComplex.homologyMapIso (homResolutionIso k g hg A) 0 ≪≫
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫
  cyclesMapIso (HomologicalComplex.isoSc' _ 0 0 1 (by simp) (by simp))

noncomputable def groupCohomologyEvenIso
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1)) :
    groupCohomology A (i + 1) ≅ (normHomCompSub A g).homology :=
  groupCohomologyIso A (i + 1) (resolution k g hg) ≪≫
  (HomologicalComplex.homologyMapIso (homResolutionIso k g hg A) (i + 1)) ≪≫
  AlternatingComplex.complex.homologyEvenIso A.V (by ext; simp [sub_eq_add_neg])
    (by ext; simp [sub_eq_add_neg]) (by simp) (by simp) (by simp) hi

open groupCohomology

namespace groupCohomology

noncomputable abbrev πEven
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1)) :
    ModuleCat.of k (LinearMap.ker (applyAsHom A g - 𝟙 A).hom.hom) ⟶
      groupCohomology A (i + 1) :=
    (moduleCatCyclesIso <| normHomCompSub A g).inv ≫
      ShortComplex.homologyπ _ ≫ (groupCohomologyEvenIso g hg A i hi).inv

lemma πEven_eq_zero_iff
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1))
    (x : LinearMap.ker (applyAsHom A g - 𝟙 A).hom.hom) :
    πEven g hg A i hi x = 0 ↔ x.1 ∈ LinearMap.range A.norm.hom.hom := by
  simp [πEven, map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance),
    moduleCatToCycles, -LinearMap.mem_range, LinearMap.range_codRestrict]

lemma πEven_eq_iff {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1))
    (x y : LinearMap.ker (applyAsHom A g - 𝟙 A).hom.hom) :
    πEven g hg A i hi x = πEven g hg A i hi y ↔ x.1 - y.1 ∈ LinearMap.range A.norm.hom.hom := by
  rw [← sub_eq_zero, ← map_sub, πEven_eq_zero_iff]; rfl

noncomputable def groupCohomologyOddIso
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1)) :
    groupCohomology A (i + 1) ≅ (subCompNormHom A g).homology :=
  groupCohomologyIso A (i + 1) (resolution k g hg) ≪≫
  (HomologicalComplex.homologyMapIso (homResolutionIso k g hg A) (i + 1)) ≪≫
  AlternatingComplex.complex.homologyOddIso A.V (by ext; simp [sub_eq_add_neg])
    (by ext; simp [sub_eq_add_neg]) (by simp) (by simp) (by simp) hi

noncomputable abbrev πOdd
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1)) :
    ModuleCat.of k (LinearMap.ker A.norm.hom.hom) ⟶
      groupCohomology A (i + 1) :=
    (moduleCatCyclesIso <| subCompNormHom A g).inv ≫
      ShortComplex.homologyπ _ ≫ (groupCohomologyOddIso g hg A i hi).inv

lemma πOdd_eq_zero_iff
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1))
    (x : LinearMap.ker A.norm.hom.hom) :
    πOdd g hg A i hi x = 0 ↔ x.1 ∈ LinearMap.range (applyAsHom A g - 𝟙 A).hom.hom := by
  simp [πOdd, map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance),
    moduleCatToCycles, -LinearMap.mem_range, LinearMap.range_codRestrict]

lemma πOdd_eq_iff {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1))
    (x y : LinearMap.ker A.norm.hom.hom) :
    πOdd g hg A i hi x = πOdd g hg A i hi y ↔
      x.1 - y.1 ∈ LinearMap.range (applyAsHom A g - 𝟙 A).hom.hom := by
  rw [← sub_eq_zero, ← map_sub, πOdd_eq_zero_iff]; rfl

end groupCohomology

noncomputable def groupHomologyIso₀
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) :
    groupHomology A 0 ≅ (mk (X₃ := A.V) (applyAsHom A g - 𝟙 A).hom _ comp_zero).opcycles :=
  groupHomologyIso A 0 (resolution k g⁻¹ <| (@Subgroup.zpowers_inv G ..).symm ▸ hg) ≪≫
  HomologicalComplex.homologyMapIso (coinvariantsTensorResolutionIso k g hg A) 0 ≪≫
  ChainComplex.isoHomologyι₀ _ ≪≫
  opcyclesMapIso (HomologicalComplex.isoSc' _ 1 0 0 (by simp) (by simp))

noncomputable def groupHomologyEvenIso
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1)) :
    groupHomology A (i + 1) ≅ (subCompNormHom A g).homology :=
  groupHomologyIso A (i + 1) (resolution k g⁻¹ <| (@Subgroup.zpowers_inv G ..).symm ▸ hg) ≪≫
  (HomologicalComplex.homologyMapIso (coinvariantsTensorResolutionIso k g hg A) (i + 1)) ≪≫
  AlternatingComplex.complex.homologyEvenIso A.V (by ext; simp [sub_eq_add_neg])
    (by ext; simp [sub_eq_add_neg]) (by aesop) (by simp) (by simp) hi

namespace groupHomology

noncomputable abbrev πEven
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1)) :
    ModuleCat.of k (LinearMap.ker A.ρ.norm) ⟶
      groupHomology A (i + 1) :=
    (moduleCatCyclesIso <| subCompNormHom A g).inv ≫
      ShortComplex.homologyπ _ ≫ (groupHomologyEvenIso g hg A i hi).inv

lemma πEven_eq_zero_iff
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1))
    (x : LinearMap.ker A.ρ.norm) :
    πEven g hg A i hi x = 0 ↔ x.1 ∈ LinearMap.range (applyAsHom A g - 𝟙 A).hom.hom := by
  simp [πEven, map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance),
    moduleCatToCycles, -LinearMap.mem_range, LinearMap.range_codRestrict]

lemma πEven_eq_iff {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Even (i + 1))
    (x y : LinearMap.ker A.ρ.norm) :
    πEven g hg A i hi x = πEven g hg A i hi y ↔
      x.1 - y.1 ∈ LinearMap.range (applyAsHom A g - 𝟙 A).hom.hom := by
  rw [← sub_eq_zero, ← map_sub, πEven_eq_zero_iff]; rfl

noncomputable def groupHomologyOddIso
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1)) :
    groupHomology A (i + 1) ≅ (normHomCompSub A g).homology :=
  groupHomologyIso A (i + 1) (resolution k g⁻¹ <| (@Subgroup.zpowers_inv G ..).symm ▸ hg) ≪≫
  (HomologicalComplex.homologyMapIso (coinvariantsTensorResolutionIso k g hg A) (i + 1)) ≪≫
  AlternatingComplex.complex.homologyOddIso A.V (by ext; simp [sub_eq_add_neg])
    (by ext; simp [sub_eq_add_neg]) (by aesop) (by simp) (by simp) hi

noncomputable abbrev πOdd
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1)) :
    ModuleCat.of k (LinearMap.ker (applyAsHom A g - 𝟙 A).hom.hom) ⟶
      groupHomology A (i + 1) :=
    (moduleCatCyclesIso <| normHomCompSub A g).inv ≫
      ShortComplex.homologyπ _ ≫ (groupHomologyOddIso g hg A i hi).inv

lemma πOdd_eq_zero_iff
    {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1))
    (x : LinearMap.ker (applyAsHom A g - 𝟙 A).hom.hom) :
    πOdd g hg A i hi x = 0 ↔ x.1 ∈ LinearMap.range A.ρ.norm := by
  simp [πOdd, map_eq_zero_iff _ ((ModuleCat.mono_iff_injective _).1 inferInstance),
    moduleCatToCycles, -LinearMap.mem_range, LinearMap.range_codRestrict]

lemma πOdd_eq_iff {G : Type u} [CommGroup G] [Fintype G] [DecidableEq G] (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (A : Rep k G) (i : ℕ) (hi : Odd (i + 1))
    (x y : LinearMap.ker (applyAsHom A g - 𝟙 A).hom.hom) :
    πOdd g hg A i hi x = πOdd g hg A i hi y ↔
      x.1 - y.1 ∈ LinearMap.range A.ρ.norm := by
  rw [← sub_eq_zero, ← map_sub, πOdd_eq_zero_iff]; rfl

end groupHomology
end finiteCyclicGroup

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

open Additive

-- could move to `RepresentationTheory.Rep` but would have to add imports
/-- Given `L/K` finite and Galois, and `x : Lˣ`, this essentially says
`(∏ σ) • x = N_{L/K}(x)`, where the product is over `σ ∈ Gal(L/K)`. -/
theorem norm_ofAlgebraAutOnUnits_eq (x : Lˣ) :
    (toMul <| toAdditive ((Rep.ofAlgebraAutOnUnits K L).norm.hom
      (toAdditive.symm <| ofMul x))).1 = algebraMap K L (Algebra.norm K (x : L)) := by
  simp [Algebra.norm_eq_prod_automorphisms, Representation.norm]

variable [IsCyclic (L ≃ₐ[K] L)] [DecidableEq (L ≃ₐ[K] L)]

attribute [local instance] IsCyclic.commGroup

theorem hilbert90_again (g : L ≃ₐ[K] L)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : L) (hx : Algebra.norm K x = 1) :
    ∃ y : Lˣ, g y / y = x := by
  let xu : Lˣ := (Algebra.norm_ne_zero_iff.1 <| hx ▸ zero_ne_one.symm).isUnit.unit
  have hx' : algebraMap K L (Algebra.norm K (xu : L)) = _ := congrArg (algebraMap K L) hx
  rw [← norm_ofAlgebraAutOnUnits_eq xu, map_one] at hx'
  have := finiteCyclicGroup.groupCohomology.πOdd_eq_zero_iff g hg
    (ofAlgebraAutOnUnits K L) 0 (by simp) ⟨toAdditive.symm <| ofMul xu, by simp_all⟩
  rcases this.1 (Subsingleton.elim (α := groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) _ _)
    with ⟨y, hy⟩
  use toMul <| toAdditive y
  simpa [xu, sub_eq_add_neg, div_eq_mul_inv, -toAdditive_apply] using
    Units.ext_iff.1 congr(toMul <| toAdditive $hy)

end Rep
