/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Category.Lifting.Defs
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.SeparatedMap

import Mathlib.Tactic.TautoSet

/-!
# Separation

The standard separation axioms in topology can be represented categorically as lifting properties.

Here, we provide the implementations. We provide a systematic `llp`/`rlp` lemma for each separation
axiom, stating that a space satisfies the axiom iff it has the corresponding lifting property,
together with both its directions. If necessary, we then provide simplified versions of one or both
directions, abandoning the explicit lifting property in order to remove redundant hypotheses.

## Notation

While we do not (yet) provide a Lean implementation, in the doc-comments we borrow the notation
from the nCatLab page below. Small finite topologies are given by their specialization preorder,
and maps between them are indicated by the repetition of the same symbol; continuity follows so
long as the maps are monotone w.r.t. specialization. For example, the diagram
```
L ⟶ 0 ⟵ R   |--------->   L ⟶ 0
```
is one way of representing `U2C1ToUPropL`, the continuous map taking the left copy of `UProp` in
`O2C1` to their matching points in `UProp`.

## Main statements

* A space is `T0` iff `Codiscrete2 ⟶ ⊤_ TopCat ⧄ X ⟶ ⊤_ TopCat`.
* A space is `R0` iff `「⊤ ⟶ ⊥」 ⟶ 「⊤ ⟷ ⊥」 ⧄ X ⟶ ⊤_ TopCat`.
* A space is `T1` iff `UProp ⟶ ⊤_ TopCat ⧄ X ⟶ ⊤_ TopCat`.
* A space is `T2` iff every mono `χ : Discrete2 ⟶ X` satisfies `χ ⧄ O2C1 ⟶ ⊤_ TopCat`.
* A space is `T2.5` iff every mono `χ : Discrete2 ⟶ X` satisfies `χ ⧄ O3C2 ⟶ ⊤_ TopCat`.
* A space is regular iff every `χ : ⊤_ TopCat ⟶ X` satisfies
  `χ ⧄「L ⟶ 0 ⟵ (R = ⊤) ⟶ ⊥」 ↦ 「L = 0 = R = ⊤ ⟶ ⊥」`.
* A space is normal iff `⊥_ TopCat ⟶ X ⧄ 「L ⟵ 0 ⟶ M ⟵ 1 ⟶ R」 ↦「L ⟵ 0 = M = 1 ⟶  R」.`
  * Alternatively, let us slightly abuse notation and represent the non-specialization-topology
    `OIC2` as `「L ⟵ [0, 1] ⟶ R」`; then a space is normal iff
    `⊥_ TopCat ⟶ X ⧄ 「L ⟵ [0, 1] ⟶ R」 ↦「L ⟵ 0 = 1 ⟶ R」.`
* A space is completely, or hereditarily, normal iff every open subspace is normal,
  that is, `⊥_ TopCat ⟶ X ⧄  WithBot.map「L ⟵ 0 ⟶ M ⟵ 1 ⟶ R」 ↦「L ⟵ 0 = M = 1 ⟶  R」.`
* A space is perfectly normal iff `⊥_ TopCat ⟶ X ⧄ [0, 1] ↦「0 ⟵ (0, 1) ⟶ 1」.`


## References

* https://ncatlab.org/nlab/show/separation+axioms+in+terms+of+lifting+properties
* [Misha Gavrilovich, *The unreasonable power of the lifting property in elementary mathematics*][gavrilovich2017lifting]

## Tags

Foobars, barfoos
-/

universe w v u
open CategoryTheory TopCat Limits Topology TopologicalSpace Set HasLiftingProperty

@[simp]
lemma Concrete.HasPushout.range_inl_union_range_inr
    {C : Type u} [Category.{v} C] {FC : C → C → Type _} {CC : C → Type w}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]
    [PreservesColimit (span f g) (forget C)] :
    range (pushout.inl f g) ∪ range (pushout.inr f g) = univ := by
  ext x; obtain ⟨y, rfl⟩ | ⟨z, rfl⟩ := Concrete.pushout_exists_rep f g x <;> simp

variable {X : TopCat.{u}}

namespace T0Space

/-- A space `X` is `T0` iff the morphism `terminal.from X` has the right lifting property against
`terminal.from Codiscrete2`. -/
theorem rlp : T0Space X ↔ terminal.from (of Codiscrete2.{u}) ⧄ terminal.from X where
  mp _ :=
  { sq_hasLift {χ _} _ := by
      have hχ : χ .zero = χ .one := by
        by_contra! h!
        obtain ⟨U, Uo, ⟨hxU, hyU⟩ | ⟨hxU, hyU⟩⟩ := exists_isOpen_xor'_mem h!
        all_goals
          have : IsOpen (χ ⁻¹' U) := Uo.preimage χ.continuous
          rw [← mem_preimage] at hxU hyU
          simp only [isOpen_codiscrete, or_false, Set.ne_univ_of_notMem ‹_›] at this
          exact Set.nonempty_of_mem hxU |>.ne_empty this
      apply CommSq.HasLift.mk'; use terminal.homOfElement (χ .zero)
      · ext (_ | _) <;> simp [hχ]
      · exact terminal.hom_ext _ _ }
  mpr h :=
  { t0 x y hxy := by
      have hχ := by
        simpa [TopCat.ext_iff, -CommSq.fac_left, Codiscrete2.forall,
            Unique.eq_default (α := ⊤_ TopCat.{u})]
          using CommSq.fac_left (hsq := h.sq_hasLift
            (f := ofHom <| Codiscrete2.homOfInseparable hxy) (g := 𝟙 _) ⟨by simp⟩)
      exact hχ.1.symm.trans hχ.2 }

instance [T0Space X] : HasLiftingProperty (terminal.from (of Codiscrete2)) (terminal.from X) :=
  rlp.mp ‹_›

/-- A `T0` space `X` descends every morphism from-`Codiscrete2` into one from `⊤_ TopCat.{u}`. -/
noncomputable def desc [T0Space X] (χ : of Codiscrete2 ⟶ X) : ⊤_ TopCat.{u} ⟶ X :=
  CommSq.lift (hsq := (rlp.mp ‹_›).sq_hasLift (f := χ) (g := 𝟙 _) ⟨by simp⟩)

@[simp]
lemma desc_fac [T0Space X] (χ : of Codiscrete2 ⟶ X) :
    terminal.from (of Codiscrete2.{u}) ≫ desc χ = χ :=
  CommSq.fac_left (hsq := (rlp.mp ‹_›).sq_hasLift _)

/-- If every morphism from `Codiscrete2` to a space `X` descends to a morphism from
`⊤_ TopCat.{u}`, then `X` is `T0`. -/
theorem of_desc (lift : (of Codiscrete2 ⟶ X) → (⊤_ TopCat.{u} ⟶ X))
    (fac : ∀ χ : of Codiscrete2 ⟶ X, terminal.from (of Codiscrete2.{u}) ≫ lift χ = χ) :
    T0Space X :=
  rlp.mpr { sq_hasLift {f _} _ := CommSq.HasLift.mk' ⟨lift f, fac f, terminal.hom_ext _ _⟩ }

end T0Space

namespace R0Space

/-- A space `X` is `R0` iff the morphism `terminal.from X` has the right lifting property against
`UProp.homOfSpecializes (CodiscreteTopology.specializes .zero .one)`. -/
theorem rlp : R0Space X ↔
    UProp.desc (X := of Codiscrete2) (CodiscreteTopology.specializes .zero .one) ⧄
      terminal.from X where
  mp _ :=
  { sq_hasLift {ι τ} sq := by
      have := UProp.specializesOfHom ι
      apply CommSq.HasLift.mk'; use ofHom <| Codiscrete2.homOfInseparable this.inseparable
      · ext <;> simp
      · exact terminal.hom_ext _ _ }
  mpr h := {
    specializes_symmetric {x y} hxy := by
      obtain ⟨hx, hy⟩ := by
        simpa [TopCat.ext_iff, -CommSq.fac_left, UProp.forall,
          Unique.eq_default (α := ⊤_ TopCat.{u})]
          using CommSq.fac_left (hsq := h.sq_hasLift
            (f := UProp.desc hxy) (g := terminal.from _) ⟨by simp⟩)
      conv =>
        args
        · rw [← hy]
        · rw [← hx]
      exact Codiscrete2.inseparable (CommSq.lift (hsq := h.sq_hasLift
            (f := UProp.desc hxy) (g := terminal.from _) ⟨by simp⟩)).hom
        |>.specializes'
            }

instance [R0Space X] : HasLiftingProperty
    (UProp.desc (X := of Codiscrete2) (CodiscreteTopology.specializes .zero .one))
    (terminal.from X) :=
  rlp.mp ‹_›

/-- An `R0` space `X` descends every morphism from-`UProp` into one from `of Codiscrete2`. -/
noncomputable def desc [R0Space X] (χ : of UProp ⟶ X) : of Codiscrete2 ⟶ X :=
    CommSq.lift (hsq := (rlp.mp ‹_›).sq_hasLift (f := χ) (g := terminal.from _) ⟨by simp⟩)

@[simp]
lemma desc_fac [R0Space X] (f : of UProp ⟶ X) :
    UProp.desc (X := of _) (CodiscreteTopology.specializes .zero .one) ≫ desc f = f :=
  CommSq.fac_left (hsq := (rlp.mp ‹_›).sq_hasLift _)

/-- If every morphism from `UProp` to a space `X` descends to a morphism from `of Codiscrete2`,
then `X` is `R0`. -/
theorem of_desc (desc : (of UProp ⟶ X) → (of Codiscrete2 ⟶ X))
    (fac : ∀ χ : of UProp ⟶ X,
      UProp.desc (CodiscreteTopology.specializes .zero .one) ≫ desc χ = χ) :
    R0Space X :=
  rlp.mpr { sq_hasLift {f _} _ := CommSq.HasLift.mk' ⟨desc f, fac f, terminal.hom_ext _ _⟩ }

end R0Space

namespace T1Space

/-- A space `X` is `T1` iff the morphism `terminal.from X` has the right lifting property
against `terminal.from UProp`. -/
theorem rlp : T1Space X ↔ terminal.from (of UProp.{u}) ⧄ terminal.from X where
  mp _ :=
  { sq_hasLift {χ _} _ := by
      have hf : χ ⊤ = χ ⊥ := by
        by_contra! h!
        obtain ⟨U, Uo, hU₁, hU₀⟩ := t1Space_iff_exists_open.mp ‹_› h!
        obtain ⟨V, Vo, hV₀, hV₁⟩ := t1Space_iff_exists_open.mp ‹_› h!.symm
        replace Uo : IsOpen (χ ⁻¹' U) := Uo.preimage χ.continuous
        replace Vo : IsOpen (χ ⁻¹' V) := Vo.preimage χ.continuous
        have : χ ⁻¹' V = univ := by
          have : (χ ∘ ULift.up) ⁻¹' V ∈ 𝓝 False := by
            rw [isOpen_iff_mem_nhds] at Vo
            specialize Vo _ hV₀
            rw [preimage_comp]
            convert Filter.preimage_mem_comap (m := ULift.up) Vo
            exact Homeomorph.ulift.symm.nhds_eq_comap _
          rw [preimage_eq_univ_iff, ← EquivLike.range_comp χ Homeomorph.ulift.symm]
          simpa [-EquivLike.range_comp] using this
        exact ne_univ_of_notMem (by simpa using hV₁) this
      apply CommSq.HasLift.mk'; use terminal.homOfElement (χ ⊤)
      · ext <;> simp [hf]
      · exact terminal.hom_ext _ _ }
  mpr h := by
    rw [t1Space_iff_specializes_imp_eq]
    intro x y hxy
    have hχ := by
      simpa [TopCat.ext_iff, -CommSq.fac_left, UProp.forall,
          Unique.eq_default (α := ⊤_ TopCat.{u})]
        using CommSq.fac_left (hsq := h.sq_hasLift
          (f := UProp.desc hxy) (g := 𝟙 _) ⟨by simp⟩)
    simpa using hχ.1.symm.trans hχ.2

instance [T1Space X] : terminal.from (of UProp.{u}) ⧄ (terminal.from X) := rlp.mp ‹_›

/-- A `T1` space `X` lifts every morphism from-`UProp` into one from `⊤_ TopCat.{u}`. -/
noncomputable def lift [T1Space X] (χ : of UProp ⟶ X) : ⊤_ TopCat.{u} ⟶ X :=
  CommSq.lift (hsq := (rlp.mp ‹_›).sq_hasLift (f := χ) (g := 𝟙 _) ⟨by simp⟩)

@[simp]
lemma lift_fac [T1Space X] (χ : of UProp ⟶ X) : terminal.from (of UProp.{u}) ≫ lift χ = χ :=
  CommSq.fac_left (hsq := (rlp.mp ‹_›).sq_hasLift _)

/-- If every morphism from `UProp` to a space `X` lifts to a morphism from `⊤_ TopCat.{u}`,
then `X` is `T1`. -/
theorem of_lift (lift : (of UProp ⟶ X) → (⊤_ TopCat.{u} ⟶ X))
    (fac : ∀ χ : of UProp ⟶ X, terminal.from (of UProp.{u}) ≫ lift χ = χ) : T1Space X :=
  rlp.mpr { sq_hasLift {χ _} _ := CommSq.HasLift.mk' ⟨lift χ, fac χ, terminal.hom_ext _ _⟩ }

end T1Space

namespace T2Space

/-- If every mono `f : of Discrete 2 ⟶ X` can be extended to meet
`ofHom disjointNhdsIndicator : of Discrete 2 ⟶ of O2C1`, then `X` is T2. -/
theorem of_extend (extend : (f : of Discrete2 ⟶ X) → [Mono f] → X ⟶ of O2C1)
    (fac : ∀ (χ : of Discrete2 ⟶ X) [Mono χ], χ ≫ extend χ = ofHom disjointNhdsIndicator) :
    T2Space X where
  t2 x y hxy := by
    let «λ» := Hom.hom <| extend (ofHom <| Discrete2.hom _ _ hxy)
    existsi _, _, O2C1.isOpen_left.preimage «λ».continuous,
      O2C1.isOpen_right.preimage «λ».continuous
    split_ands
    · rw [← Discrete2.hom_zero hxy, ← TopCat.hom_ofHom (Discrete2.hom _ _ hxy)]
      unfold «λ»
      rw [mem_preimage, ← ConcreteCategory.comp_apply, fac]
      simp
    · rw [← Discrete2.hom_one hxy, ← TopCat.hom_ofHom (Discrete2.hom _ _ hxy)]
      unfold «λ»
      rw [mem_preimage, ← ConcreteCategory.comp_apply, fac]
      simp
    · apply Disjoint.preimage; simp


/-- A space `X` is `T2` iff every mono from `Discrete2` to `X` has the left lifting property
against `terminal.from O2C1`.

(In fact, it is sufficient to consider only a specific top morphism in the lifting square;
see `T2Space.of_extend`.) -/
def llp : T2Space X ↔ ∀ (χ : of Discrete2.{u} ⟶ X) [Mono χ], χ ⧄ terminal.from (of O2C1.{u}) where
  mp _ χ _ :=
  { sq_hasLift {ι τ} sq := by
      by_cases h₀ : O2C1.zero ∈ range ι
      · -- reduces to T1
        wlog h₀₀ : ι .zero = .zero generalizing ι χ
        · have h₀₁ : ι .one = .zero := by simpa [Discrete2.exists, h₀₀] using h₀
          have sq' :
              CommSq ((isoOfHomeo Discrete2.swap).inv ≫ ι)
                ((isoOfHomeo Discrete2.swap).inv ≫ χ) (terminal.from (of O2C1.{u})) τ := by
            constructor; exact terminal.hom_ext _ _
          specialize this _ (mono_comp _ χ) sq' (by simpa using h₀) (by simp [h₀₁])
          apply CommSq.HasLift.mk'; use sq'.lift
          · apply IsIso.epi_of_iso (isoOfHomeo Discrete2.swap).inv |>.left_cancellation
            rw [← Category.assoc, sq'.fac_left]
          · exact terminal.hom_ext _ _
        generalize hy : χ .one = y
        have hy₀ : y ≠ χ .zero := by
          rintro rfl
          exact Discrete2.ne <| (TopCat.mono_iff_injective χ).mp ‹_› hy.symm
        obtain ⟨U, Uo, hU₁, hU₀⟩ := t1Space_iff_exists_open.mp inferInstance hy₀
        cases hι₁ : ι .one using O2C1.casesOn' <;> apply CommSq.HasLift.mk' <;>
          [use O2C1.lift isOpen_empty isOpen_empty (by simp), ?_, terminal.hom_ext _ _;
           use O2C1.lift Uo isOpen_empty (by simp), ?_, terminal.hom_ext _ _;
           use O2C1.lift isOpen_empty Uo (by simp), ?_, terminal.hom_ext _ _] <;>
          ext1 <;> simp [h₀₀, hU₁, hU₀, Discrete2.forall, hy, hι₁]
      · wlog h₀ₗ : ι .zero = .left generalizing ι
        · have sq' : CommSq (ι ≫ (isoOfHomeo O2C1.swap).hom) χ (terminal.from _) τ := by
            constructor; exact terminal.hom_ext _ _
          specialize this sq'
            (by simp_intro h; rcases h with ⟨x, h⟩; cases hι : ι x using O2C1.casesOn' <;> simp_all)
            (by
              simp only [isoOfHomeo_hom, TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply,
                ContinuousMap.coe_coe, O2C1.swap_apply]
              cases hι₀ : ι .zero using O2C1.casesOn' <;> simp_all)
          apply CommSq.HasLift.mk'; use sq'.lift ≫ (isoOfHomeo O2C1.swap).inv
          · rw [CommSq.fac_left_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
          · exact terminal.hom_ext _ _
        by_cases hι : ι .zero = ι .one
        · have h₀ᵣ := hι ▸ h₀ₗ
          apply CommSq.HasLift.mk'; use O2C1.lift isOpen_univ isOpen_empty (by simp)
          · ext1 <;> simp [Discrete2.forall, h₀ₗ, h₀ᵣ]
          · exact terminal.hom_ext _ _
        · have h₀ᵣ : ι .one = .right := by
            cases hι₁ : ι .one using O2C1.casesOn'
            · exfalso; exact h₀ <| hι₁ ▸ mem_range_self (f := ι) .one
            · simp [h₀ₗ, hι₁] at hι
            · rfl
          generalize hx : χ .zero = x, hy : χ .one = y
          have hxy : x ≠ y := by
            rintro rfl; exact Discrete2.ne <| (TopCat.mono_iff_injective χ).mp ‹_› (hy ▸ hx)
          obtain ⟨U, V, Uo, Vo, hxU, hyV, hUV⟩ := t2_separation hxy
          apply CommSq.HasLift.mk'; fconstructor
          · exact O2C1.lift Uo Vo hUV
          · ext1 <;>
              simp [Discrete2.forall, hx, hy, h₀ₗ, hxU, h₀ᵣ, hUV.notMem_of_mem_right ‹_›, hyV]
          · exact terminal.hom_ext _ _ }
  mpr h := of_extend (fun χ [_] ↦ CommSq.lift (hsq := h χ |>.sq_hasLift
    (f := ofHom disjointNhdsIndicator) (g := terminal.from _) ⟨by simp⟩ ))
    (fun χ [_] ↦ CommSq.fac_left ⟨by simp⟩)

instance [T2Space X] (χ : of Discrete2.{u} ⟶ X) [Mono χ] :
    HasLiftingProperty χ (terminal.from (of O2C1.{u})) :=
  llp.mp ‹_› χ

open Function in
open scoped Classical in
/-- Alternate characterization: a space `X` is `T2` iff `ContinuousMap.diagonal X`
lifts against `Codiscrete2.hom { N2C1.left }`. -/
theorem llp' : T2Space X ↔
    ofHom (.diagonal X) ⧄ ofHom (Codiscrete2.hom { N2C1.left }) where
  mp _ :=
  { sq_hasLift {ι τ} sq := by
      apply CommSq.HasLift.mk';
      fconstructor
      · refine
          ofHom ⟨extend (ContinuousMap.diagonal X) ι (if τ · = .zero then .right else .left), ?_ ⟩
        rw [N2C1.basis.continuous_iff]
        rintro _ (rfl | rfl)
        · simp
        · have zero_compl : ({N2C1.left, N2C1.right}ᶜ : Set N2C1) = {N2C1.zero} := by
            ext ⟨⟩ <;> simp
          rw [← isClosed_compl_iff, ← preimage_compl, zero_compl,
          IsClosedEmbedding.diagonal.isClosed_iff_preimage_isClosed, ← preimage_comp,
          extend_comp ContinuousMap.diagonal_injective]
          · exact N2C1.isClosed_zero.preimage ι.hom.continuous
          · intro (x, y) h
            contrapose! h
            replace h : ¬∃ z, (ContinuousMap.diagonal X z) = (x, y) := by simpa using h
            simp [extend_apply' _ _ _ h]
            grind
      · rw [← ofHom_comp, ContinuousMap.comp]
        simp [extend_comp ContinuousMap.diagonal_injective]
        rfl
      · ext ⟨x, y⟩
        rcases em (x = y) with (rfl | hxy)
        · rw [show (x, x) = ContinuousMap.diagonal X x by rfl]
          have := (elementwise_of% sq.w) x
          simp at this
          simp [-ContinuousMap.diagonal_apply, ContinuousMap.diagonal_injective.extend_apply]
          simp [this]
        · replace hxy : ¬∃ z, (ContinuousMap.diagonal X z) = (x, y) := by simpa using hxy
          have {z} : ¬z = Codiscrete2.zero ↔ Codiscrete2.one = z := by cases z <;> grind
          simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
            extend_apply' _ _ _ hxy, Codiscrete2.hom_apply, ite_eq_right_iff,
            reduceCtorEq, imp_false, mem_singleton_iff, ULift.down_inj]
          split_ifs with h₀ <;> first | rwa [this] at h₀ | simp_all }
  mpr h := by
    have hsq := h.sq_hasLift (f := ofHom <| .const X N2C1.zero)
      (g := ofHom <| Codiscrete2.hom (diagonal X)ᶜ) ⟨by ext; simp⟩
    let χ := CommSq.lift (hsq := hsq)
    rw [t2_iff_isClosed_diagonal]
    convert N2C1.isClosed_zero.preimage χ.hom.continuous
    ext ⟨x, y⟩
    constructor
    · rintro ⟨⟩
      unfold χ
      have := (elementwise_of% CommSq.fac_left (hsq := hsq)) x
      rw [show (x, x) = ContinuousMap.diagonal X x by rfl]
      simp at this; simp [this]
    · rw [mem_preimage, mem_singleton_iff]
      intro hχ
      have := (elementwise_of% CommSq.fac_right (hsq := hsq)) (x, y)
      apply_fun ofHom (Codiscrete2.hom {N2C1.left}) at hχ
      simp_rw [χ, this] at hχ
      simp [Codiscrete2.ne.symm] at hχ; simp [hχ]


/-- A `T2` space `X` extends every mono from `Discrete2` into one to `O2C1`. -/
noncomputable def extend [T2Space X] (χ : of Discrete2 ⟶ X) [Mono χ] : X ⟶ of O2C1 :=
  CommSq.lift (hsq := (llp.mp ‹_› χ).sq_hasLift
    (f := ofHom disjointNhdsIndicator) (g := terminal.from _) ⟨by simp⟩)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma extend_fac [T2Space X] (χ : of Discrete2 ⟶ X) [Mono χ] :
    χ ≫ extend χ = ofHom disjointNhdsIndicator :=
  CommSq.fac_left (hsq := (llp.mp ‹_› χ).sq_hasLift _)

@[simp]
lemma mem_extend_hom_left [T2Space X] {x y : X} (hxy : x ≠ y) :
    x ∈ (extend (ofHom <| Discrete2.hom x y hxy)).hom ⁻¹' {.left} := by
  simp only [mem_preimage, mem_singleton_iff]
  conv_lhs => enter [2]; rw [← Discrete2.hom_zero hxy, ← TopCat.hom_ofHom (Discrete2.hom x y hxy)]
  rw [extend_fac_apply]

@[simp]
lemma mem_extend_hom_right [T2Space X] {x y : X} (hxy : x ≠ y) :
    y ∈ (extend (ofHom <| Discrete2.hom x y hxy)).hom ⁻¹' {.right} := by
  simp only [mem_preimage, mem_singleton_iff]
  conv_lhs => enter [2]; rw [← Discrete2.hom_one hxy, ← TopCat.hom_ofHom (Discrete2.hom x y hxy)]
  rw [extend_fac_apply]

end T2Space

namespace T25Space

noncomputable def disjointClosedNhdsIndicator :
    C(Discrete2, O3C2) :=
  Discrete2.hom O3C2.left O3C2.right (by simp)

/--
Let `O3C2` be the topology constructed by gluing together two copies of `O2C1` at end points,
and let `ofHom disjointClosedNhdsIndicator : of Discrete2 ⟶ of O3C2` be the map sending
`0` to the left `O2C1`'s left point and `1` to the right `O2C1`'s right point:
```
「L  R」         「L     M      R
      　|-------→   🡖  🡗  🡖  🡗
                      0     1    」
```
If every mono from `Discrete2` to `X` can be extended to meet
`ofHom disjointClosedNhdsIndicator`, then `X` is `T2.5`. -/
lemma of_extend
    (extend : (χ : of Discrete2 ⟶ X) → [Mono χ] → X ⟶ of O3C2)
    (fac : ∀ (χ : of Discrete2 ⟶ X) [Mono χ],
      χ ≫ extend χ = ofHom disjointClosedNhdsIndicator) : T25Space X where
  t2_5 {x y} hxy := by
    rw [Filter.disjoint_iff]
    let χ := ofHom <| Discrete2.hom x y hxy
    let «λ» := Hom.hom <| extend χ
    use «λ» ⁻¹' (closure {O3C2.left}), ?hL, «λ» ⁻¹' (closure {O3C2.right}), ?hR
    case hL | hR =>
      apply Filter.mem_of_superset _ («λ».continuous.closure_preimage_subset _)
      apply Filter.mem_lift' (IsOpen.preimage «λ».continuous _ |>.mem_nhds _)
      · rw [IsLowerSet.isOpen_iff_isLowerSet, IsLowerSet]
        rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> simp
      · have hx : χ .zero = x := by simp [χ]
        have hy : χ .one = y := by simp [χ]
        simp [«λ», ← hx, ← hy, elementwise_of% fac χ, disjointClosedNhdsIndicator, Discrete2.hom]
    apply Disjoint.preimage
    grw [closure_minimal (t := {O3C2.left, O3C2.zero}) (by simp),
    closure_minimal (t := {O3C2.right, O3C2.one}) (by simp)]
    · simp
    all_goals
      rw [IsLowerSet.isClosed_iff_isUpper, IsUpperSet]
      rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> simp

open O3C2 in
lemma O3C2.range_inl : range O3C2.inl.map = {left, zero, mid} := by
  ext x; cases x using O3C2.casesOn' <;> simp [O3C2.inl.map, O2C1.exists]

open O3C2 in
lemma O3C2.range_inr : range O3C2.inr.map = {mid, one, right} := by
  ext x; cases x using O3C2.casesOn' <;> simp [O3C2.inr.map, O2C1.exists]

open scoped Finset Classical in
lemma llp : T25Space X ↔
    ∀ (χ : of Discrete2 ⟶ X) [Mono χ], χ ⧄ terminal.from (of O3C2) where
  mp _ χ [_] :=
  { sq_hasLift {ι τ} sq := by
      -- `O3C2` and `Discrete2` both have 'bilateral' symmetry, so we only need to consider a
      -- quarter of the cases.
      wlog hι_max : (ι .zero).1.ctorIdx + (ι .one).1.ctorIdx < 5 generalizing ι
      · specialize @this (ι ≫ (isoOfHomeo O3C2.flip).hom) ⟨terminal.hom_ext _ _⟩
          (by
            rw [ConcreteCategory.comp_apply]
            rcases hι₀ : ι .zero with ⟨⟨⟩⟩ <;> rcases hι₁ : ι .one with ⟨⟨⟩⟩ <;>
              simp [hι₀, hι₁] at hι_max ⊢ )
        apply CommSq.HasLift.mk'; use CommSq.lift (hsq := this) ≫ (isoOfHomeo O3C2.flip).inv
        · rw [CommSq.fac_left_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        · exact terminal.hom_ext _ _
      wlog hι_mono : toLex (ι .zero) ≤ toLex (ι .one) generalizing ι χ
      · specialize @this ((isoOfHomeo Discrete2.swap).inv ≫ χ) _
          ((isoOfHomeo Discrete2.swap).inv ≫ ι) ⟨terminal.hom_ext _ _⟩
          (by
            rw [ConcreteCategory.comp_apply]
            rcases hι₀ : ι .zero with  ⟨⟨⟩⟩ <;> rcases hι₁ : ι .one with ⟨⟨⟩⟩ <;>
              simp [hι₀, hι₁] at hι_mono hι_max ⊢)
          (by
            rw [ConcreteCategory.comp_apply]
            rcases hι₀ : ι .zero with  ⟨⟨⟩⟩ <;> rcases hι₁ : ι .one with ⟨⟨⟩⟩ <;>
              simp [hι₀, hι₁] at hι_mono hι_max ⊢)
        apply CommSq.HasLift.mk'; use CommSq.lift (hsq := this)
        · apply IsIso.epi_of_iso (isoOfHomeo Discrete2.swap).inv |>.left_cancellation
          rw [← Category.assoc, CommSq.fac_left]
        · exact terminal.hom_ext _ _
      cases hι₀ : ι .zero using O3C2.casesOn' <;> cases hι₁ : ι .one using O3C2.casesOn'
      all_goals try simp [hι₀, hι₁] at hι_max hι_mono; done
      all_goals clear hι_max hι_mono
      case -- reduce to T2
        left.left |
        left.zero | zero.zero |
        left.mid  | zero.mid  | mid.mid  =>
        let πL : of O3C2 ⟶ of O2C1 :=
          O3C2.isPushout.desc (𝟙 _) (ofHom <| .const _ O2C1.right) (by simp)
        have hπL : LeftInvOn O3C2.inl πL (range O3C2.inl.map) := by
          intro z; simp_intro hz [O2C1.exists]
          rcases hz with rfl | rfl | rfl <;>
            (unfold πL; erw [elementwise_of% @O3C2.isPushout.inl_desc]; simp)
        rw [O3C2.range_inl] at hπL
        apply CommSq.HasLift.mk'
        · have sq : CommSq (ι ≫ πL) χ (terminal.from (of O2C1)) τ := by
            constructor; exact terminal.hom_ext _ _
          use sq.lift ≫ O3C2.inl
          · rw [sq.fac_left_assoc]
            ext (_ | _)
            · simpa using hπL.eq (by simp [hι₀])
            · simpa using hπL.eq (by simp [hι₁])
          · exact terminal.hom_ext _ _
      all_goals -- the interesting cases which need `T2.5`
        -- left.right | left.one  =>
        have χ_ne : χ .zero ≠ χ .one := by
          simp [TopCat.mono_iff_injective χ |>.mp inferInstance |>.ne_iff]
        obtain ⟨U, h0U, Uo, V, h1V, Vo, hUV⟩ := exists_open_nhds_disjoint_closure χ_ne
        have codisjoint : (closure V)ᶜ ∪ (closure U)ᶜ = univ := by
          simpa [← compl_inter, disjoint_iff_inter_eq_empty] using hUV.symm
        apply CommSq.HasLift.mk'
        have h0U' : χ .zero ∈ (closure V)ᶜ := hUV.notMem_of_mem_left <| subset_closure h0U
        have h1V' : χ .one ∈ (closure U)ᶜ := hUV.notMem_of_mem_right <| subset_closure h1V
        have := notMem_subset subset_closure h1V'
        have := notMem_subset frontier_subset_closure h1V'
        let squash : of O3C2 ⟶ of O3C2 :=
          ofHom
          { toFun := Function.update (Function.update id O3C2.left (ι .zero)) O3C2.right (ι .one)
            continuous_toFun := by
              rw [← IsLowerSet.monotone_iff_continuous]
              rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ <;> simp [hι₀, hι₁, Z5.spec_iff] }
        use O3C2.liftOpen Uo Vo hUV ≫ squash
        · ext (_ | _) <;> simp +contextual [squash, *]
        · exact terminal.hom_ext _ _ }
  mpr h := of_extend (fun χ [_] ↦ CommSq.lift (hsq := h χ |>.sq_hasLift
    (f := ofHom disjointClosedNhdsIndicator) (g := terminal.from _) ⟨by simp⟩ ))
    (fun χ [_] ↦ CommSq.fac_left ⟨by simp⟩)

instance [T25Space X] (χ : of Discrete2 ⟶ X) [Mono χ] :
    HasLiftingProperty χ (terminal.from (of O3C2)) :=
  llp.mp ‹_› χ

/-- A `T2.5` space `X` extends every mono from `Discrete2` into one to `O3C2`. -/
noncomputable def extend [T25Space X] (χ : of Discrete2 ⟶ X) [Mono χ] : X ⟶ of O3C2 :=
  CommSq.lift (hsq := (llp.mp ‹_› χ).sq_hasLift
    (f := ofHom disjointClosedNhdsIndicator) (g := terminal.from _) ⟨by simp⟩)

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma extend_fac [T25Space X] (χ : of Discrete2 ⟶ X) [Mono χ] :
    χ ≫ extend χ = ofHom disjointClosedNhdsIndicator :=
  CommSq.fac_left (hsq := (llp.mp ‹_› χ).sq_hasLift _)

end T25Space

namespace RegularSpace

@[simp]
noncomputable abbrev O2C2T :=
  pushout (terminal.homOfElement' O2C1.right) (terminal.homOfElement' (⊤ : UProp.{u}))

/-- Let `O2C2T` denote the topology `L ⟶ 0 ⟵ (R = ⊤) ⟶ ⊥` made by gluing together `O2C1` and
`UProp` at `O2C1.right` and `⊤`. Then the image of `O2C1` in `O2C2T` is open. -/
lemma O2C2T.isOpen_range_inl :
    IsOpen (range (pushout.inl (terminal.homOfElement' O2C1.right)
        (terminal.homOfElement' (⊤ : UProp.{u})))) := by
  let χ : O2C2T ⟶ of UProp := pushout.desc isOpen_univ.toHom UProp.isOpen_top.toHom (by symm; simp)
  convert IsOpen.ofHom χ
  ext x
  obtain (⟨(x : O2C1), rfl⟩| ⟨(x : UProp), rfl⟩) := Concrete.pushout_exists_rep _ _ x
  · simp [χ, elementwise_of% @pushout.inl_desc]
  · simpa [χ, ← ConcreteCategory.comp_apply, Concrete.pushout_inl_eq_inr_iff] using eq_comm

/-- Let `O2C2T` denote the topology `L ⟶ 0 ⟵ (R = ⊤) ⟶ ⊥` made by gluing together `O2C1` and
`UProp` at `O2C1.right` and `⊤`. Then the image of `UProp` in `O2C2T` is open. -/
lemma O2C2T.isOpen_range_inr :
    IsOpen (range ⇑(pushout.inr (terminal.homOfElement' O2C1.right)
        (terminal.homOfElement' (⊤ : UProp.{u})))) := by
  let χ : O2C2T ⟶ of UProp :=
    pushout.desc O2C1.isOpen_right.toHom (isOpen_univ.toHom (X := of UProp)) (by simp)
  convert IsOpen.ofHom χ
  ext x
  obtain (⟨(x : O2C1), rfl⟩| ⟨(x : UProp), rfl⟩) := Concrete.pushout_exists_rep _ _ x
  · --simp [χ, elementwise_of% @pushout.inl_desc, ]
    simp_rw [mem_range, eq_comm]
    simpa [elementwise_of% @pushout.inl_desc, χ, Concrete.pushout_inl_eq_inr_iff] using eq_comm
  · simp [χ, ← ConcreteCategory.comp_apply]


open terminal in
/--
Let `O2C2T` denote the topology `L ⟶ 0 ⟵ (R = ⊤) ⟶ ⊥` made by gluing together `O2C1` and
`UProp` at `O2C1.right` and `⊤`. Then given a space `X`, if every completion of the diagram
```
                       「L       R = ⊤
  「L」 |-------------→    🡖   🡗       🡖
  　　　　　　　　　　 　　    0　 __      ⊥」
                                 |
                                 |
                                 |
                                 |
                                 ↓
                             「⊤
    X                            🡖
                                   ⊥」
```
to a commutative square has a lift, `X` is regular. -/
theorem of_lift {X}
    (lift : ∀ (χ : ⊤_ TopCat.{u} ⟶ X) (s : X ⟶ of UProp)
      (sq : CommSq
        (homOfElement' O2C1.left ≫ pushout.inl (homOfElement' O2C1.right) (homOfElement' ⊤))
          χ O2C2T.isOpen_range_inl.toHom s), sq.HasLift) : RegularSpace X where
  regular {s x} sC hxs := by
    rw [Filter.disjoint_iff]
    obtain ⟨η, hL, hR⟩ := by
      refine lift (terminal.homOfElement' x) sC.toHom ?hs |>.exists_lift.some
      fconstructor
      ext; simp [hxs, terminal.homOfElement]
    use η ⁻¹' range (pushout.inr (C := TopCat) _ _), by
      rw [IsOpen.mem_nhdsSet]
      · simp [eq_compl_comm (y := s)] at hR
        simp [hR, Hom.hom, ← preimage_compl]
        gcongr
        simp [compl_subset_iff_union]
      · exact O2C2T.isOpen_range_inr.preimage η.continuous
    use η ⁻¹' {pushout.inl (C := TopCat) _ _ O2C1.left}, by
      rw [IsOpen.mem_nhds_iff]
      · simp at hL; simp [hL]
      · apply IsOpen.preimage η.continuous
        rw [pushout_isOpen_iff]
        split_ands
        · simp [(TopCat.mono_iff_injective (pushout.inl _ _) |>.mp inferInstance),
          ← image_singleton (a := O2C1.left), -image_singleton]
        · convert isOpen_empty
          simp [preimage_singleton_eq_empty, Concrete.pushout_inl_eq_inr_iff,
          @eq_comm _ (pushout.inr (C := TopCat) _ _ _)]
    apply Disjoint.preimage
    simp [Concrete.pushout_inl_eq_inr_iff, @eq_comm _ (pushout.inr (C := TopCat) _ _ _)]

open scoped Classical in
/-- Let `O2C2T` denote the topology `L ⟶ 0 ⟵ (R = ⊤) ⟶ ⊥` made by gluing together `O2C1` and
`UProp` at `O2C1.right` and `⊤`. Then a space `X` is regular iff every morphism `⊤_ TopCat ⟶ X`
picking out some point of `X` has the left lifting property against
`「L ⟶ 0 ⟵ (R = ⊤) ⟶ ⊥」 ↦ 「L = 0 = R = ⊤ ⟶ ⊥」`.

(In fact, it is sufficient to consider only a specific top morphism in the lifting square;
see `RegularSpace.of_lift`.) -/
theorem llp : RegularSpace X ↔ ∀ (χ : ⊤_ TopCat.{u} ⟶ X), χ ⧄ O2C2T.isOpen_range_inl.toHom where
  mp _ χ :=
{ sq_hasLift {ι τ} sq := by
    by_cases hι : ι default = pushout.inl (terminal.homOfElement _) _ O2C1.right
    · have hι' := hι.symm
      rw [Concrete.pushout_inl_eq_inr_iff _ _ |>.mpr
        ⟨default, by rfl, terminal.homOfElement_apply _⟩] at hι
      apply CommSq.HasLift.mk'; use τ ≫ pushout.inr _ _
      · ext x; obtain rfl := Unique.eq_default x
        simp [← sq.w_assoc, hι,
        IsOpen.toHom_apply_of_mem (s := ι ⁻¹' range _) _ (by simpa using ⟨O2C1.right, hι'⟩)]
      · ext; simpa [Concrete.pushout_inl_eq_inr_iff] using eq_comm
    · obtain ⟨_ | _ | _, hy⟩ | ⟨z, hz⟩ := Concrete.pushout_exists_rep _ _ (ι default)
      · have hx : χ default ∉ τ ⁻¹' {⊥} := by simp [← elementwise_of% sq.w, ← hy]
        obtain ⟨_, V, _, Vo, hxU, hsV, hUV⟩ :=
          SeparatedNhds.of_isCompact_isClosed (isCompact_singleton (x := χ default))
            (IsClosed.ofHom τ) (disjoint_singleton_left.mpr hx)
        rw [singleton_subset_iff] at hxU
        have hxV! : χ default ∉ V := hUV.notMem_of_mem_left hxU
        have hxU' : χ default ∈ (τ ⁻¹' {⊥})ᶜ := by
          rw [mem_compl_iff]; exact notMem_subset hsV <| hUV.notMem_of_mem_left hxU
        apply CommSq.HasLift.mk'
        use ofHom <| IsCoherentWith.liftPair (IsClosed.ofHom τ).isOpen_compl Vo
          (by grw [← codisjoint_iff_union_eq_univ, ← hsV]; symm; exact isCompl_compl.codisjoint)
          (.comp (Hom.hom <| pushout.inl (C := TopCat) _ _ )
            <| .comp (O2C1.lift.map isOpen_empty Vo (by simp)) .subtypeVal)
          (.comp (Hom.hom <| pushout.inr (C := TopCat) _ _ ) <| (Hom.hom τ).comp .subtypeVal)
          (by simp +contextual [O2C1.lift_eq_right, Concrete.pushout_inl_eq_inr_iff])
        · ext x; obtain rfl := Unique.eq_default x
          simp [IsCoherentWith.liftPair_apply_of_mem_left hxU', hy,
          O2C1.lift_eq_zero (notMem_empty _) hxV!]
        · ext x
          rcases mem_or_mem_compl (τ ⁻¹' {⊥}) x with (hx | hx)
          · have hx' : τ x = ⊥ := hx
            simp [IsCoherentWith.liftPair_apply_of_mem_right (hsV hx), hx',
            Concrete.pushout_inl_eq_inr_iff]
          · simpa [IsCoherentWith.liftPair_apply_of_mem_left hx] using hx
      · -- `O2C1.left`, the interesting case.
        have hx : χ default ∉ τ ⁻¹' {⊥} := by simp [← elementwise_of% sq.w, ← hy]
        obtain ⟨U, V, Uo, Vo, hxU, hsV, hUV⟩ :=
          SeparatedNhds.of_isCompact_isClosed (isCompact_singleton (x := χ default))
            (IsClosed.ofHom τ) (disjoint_singleton_left.mpr hx)
        rw [singleton_subset_iff] at hxU
        apply CommSq.HasLift.mk'
        use ofHom <| IsCoherentWith.liftPair (IsClosed.ofHom τ).isOpen_compl Vo
          (by grw [← codisjoint_iff_union_eq_univ, ← hsV]; symm; exact isCompl_compl.codisjoint)
          (.comp (Hom.hom <| pushout.inl (C := TopCat) _ _ )
            <| .comp (O2C1.lift.map Uo Vo hUV) .subtypeVal)
          (.comp (Hom.hom <| pushout.inr (C := TopCat) _ _ ) <| (Hom.hom τ).comp .subtypeVal)
          (by simp +contextual [O2C1.lift_eq_right, Concrete.pushout_inl_eq_inr_iff])
        · ext x; obtain rfl := Unique.eq_default x
          have hxV! : χ default ∈ (τ ⁻¹' {⊥})ᶜ := by
            rw [mem_compl_iff]; exact notMem_subset hsV <| hUV.notMem_of_mem_left hxU
          simp [IsCoherentWith.liftPair_apply_of_mem_left hxV!, O2C1.lift_eq_left hxU, ← hy]
        · ext x
          rcases mem_or_mem_compl (τ ⁻¹' {⊥}) x with (hx | hx)
          · have hx' : τ x = ⊥ := hx
            simp [IsCoherentWith.liftPair_apply_of_mem_right (hsV hx), hx',
            Concrete.pushout_inl_eq_inr_iff]
          · simpa [IsCoherentWith.liftPair_apply_of_mem_left hx] using hx
      · symm at hy; contradiction
      · revert z; rw [UProp.forall]; split_ands <;> intro hz
        · rw [← Concrete.pushout_inl_eq_inr_iff _ _ |>.mpr
            ⟨default, by rfl, terminal.homOfElement_apply _⟩] at hz
          symm at hz; contradiction
        · apply CommSq.HasLift.mk'; use τ ≫ pushout.inr _ _
          · ext x; obtain rfl := Unique.eq_default x
            simp [← elementwise_of% sq.w, ← hz]
            congr!
            simp [Concrete.pushout_inl_eq_inr_iff]
          · ext x
            simpa [Concrete.pushout_inl_eq_inr_iff, terminal.homOfElement'_apply O2C1.right _,
            terminal.homOfElement'_apply (⊤ : UProp) _] using eq_comm }
  mpr h := of_lift fun χ s sq ↦ (h χ).sq_hasLift sq

end RegularSpace

namespace NormalSpace

open O2C3 in
noncomputable def indicator : C(O2C3, O1C2) where
  toFun | .left => .left | .right => .right | _ => .one
  continuous_toFun := by
    rw [← IsUpperSet.monotone_iff_continuous]
    rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> simp [O1C2.le_def, Z3.spec_iff]
  -- O1C2.lift.map (U := {O2C3.left}) (V := {O2C3.right})
  --   (by rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]; rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> simp)
  --   (by rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]; rintro ⟨⟩ ⟨⟩ ⟨⟩ <;> simp)
  --   (by simp)
  -- Discrete2.hom O2C3.left O2C3.right (by simp [O2C3.left, O2C3.right, O2C3.ofO3C2])

--todo rotate diagram 90deg
/--
Let `O2C3` be the topology constructed by gluing together two copies of `O1C2` at end points,
and let `ofHom NormalSpace.indicator : O2C3 ⟶ O1C2` be the map
```
「    0       1
    🡗  🡖   🡗  🡖
  L      M       R」
     ---------
         |
         ↓
 「   0 = M = 1
    🡗          🡖
   L             R」
```
 If every arrow from `X` to `O1C2` lifts through `ofHom NormalSpace.indicator`, then `X` is a
 normal space. -/
lemma of_lift
    (lift : (X ⟶ of O1C2) → (X ⟶ of O2C3))
      -- pushout (terminal.homOfElement' O2C1.right) (terminal.homOfElement' O2C1.left))
    (fac : ∀ (χ : X ⟶ of O1C2), lift χ ≫ ofHom indicator = χ) :
    NormalSpace X where
  normal {U V} Uc Tc hUV := by
    unfold SeparatedNhds
    let χ := O1C2.lift Uc Tc hUV
    -- let «λ» : C(X, O2C3) := Hom.hom <| lift χ
    specialize fac χ
    -- simp [TopCat.ext_iff, disjointOpenNhdsIndicator, χ] at fac
    existsi _, _, O2C3.isOpen_nhd_left.preimage (lift χ).continuous,
      O2C3.isOpen_nhd_right.preimage (lift χ).continuous
    split_ands
    · intro x hxs
      have hs : χ x = O1C2.left := by simp [χ, hxs]
      rw [TopCat.ext_iff] at fac; specialize fac x
      simp only [indicator, TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply,
        ContinuousMap.mk_apply, hs] at fac
      split at fac <;> simp_all
    · intro x hxt
      have ht : χ x = O1C2.right := by simp [χ, hxt, hUV.notMem_of_mem_right]
      rw [TopCat.ext_iff] at fac; specialize fac x
      simp only [indicator, TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply,
        ContinuousMap.mk_apply, ht] at fac
      split at fac <;> simp_all
    · apply Disjoint.preimage; simp

--TODO fix diagram
open scoped Finset Classical in
/-- Let `O2C3` be the topology constructed by gluing together two copies of `O1C2` at end points,
and let `ofHom NormalSpace.indicator : O2C3 ⟶ O1C2` be the map
```
「    0       1
    🡗  🡖   🡗  🡖
  L      M       R」
     ---------
         |
         ↓
 「   0 = M = 1
    🡗          🡖
   L             R」
```
Then a space `X` is normal iff `NormalSpace.indicator` has the right lifting property against
the initial morphism `⊥_ TopCat ⟶ X`. -/
lemma rlp : NormalSpace X ↔ initial.to X ⧄ ofHom indicator where
  mp _ :=
  { sq_hasLift {ι τ} sq := by
      obtain ⟨U, V, Uo, Vo, hU, hV, hUV⟩ :=
        NormalSpace.normal (τ ⁻¹' {O1C2.left}) (τ ⁻¹' {O1C2.right})
          (O1C2.isClosed_left.preimage τ.continuous) (O1C2.isClosed_right.preimage τ.continuous)
          (by apply Disjoint.preimage; simp)
      use O2C3.lift hU hV (O1C2.isClosed_left.preimage τ.continuous)
        (O1C2.isClosed_right.preimage τ.continuous) Uo Vo hUV
      · exact initial.hom_ext _ _
      · ext x; cases hx : τ x using O1C2.casesOn'
        rotate_right; focus have hx' := hUV.notMem_of_mem_right <| hV <| mem_singleton_of_eq hx
        all_goals
          simp [O2C3.lift_apply, apply_ite indicator, hx]
          simp [indicator, *] }
  mpr h := of_lift (fun χ ↦ CommSq.lift (hsq := h.sq_hasLift
    (f := initial.to _) (g := χ) ⟨by simp⟩ )) (fun χ ↦ CommSq.fac_right ⟨by simp⟩)

instance [NormalSpace X] : initial.to X ⧄ ofHom indicator := rlp.mp ‹_›

/-- A normal space `X` lifts every morphism to `O1C2` into one to `O2C3`. -/
noncomputable def lift [NormalSpace X] (χ : X ⟶ of O1C2) : X ⟶ of O2C3 :=
  CommSq.lift (hsq := (rlp.mp ‹_›).sq_hasLift (f := initial.to _) (g := χ) ⟨by simp⟩ )


@[reassoc (attr := simp), elementwise (attr := simp)]
lemma lift_fac [NormalSpace X] (χ : X ⟶ of O1C2) :
    lift χ ≫ ofHom indicator = χ :=
  CommSq.fac_right (hsq := (rlp.mp ‹_›).sq_hasLift _)

open scoped unitInterval
open OIC2

/-- Alternative characterization by Urysohn's lemma: if every morphism from a space `X` to `O1C2`
lifts through `OIC2` -- specifically, through the morphism `OIC2.toO1C2` that sends
`0, 0'` to `.left`, `1, 1'` to `.right`, and everything else to `.one` -- then `X` is a normal
space. -/
lemma of_lift_separating
    (lift : (X ⟶ of O1C2) → (X ⟶ of OIC2))
    (fac : ∀ (χ : X ⟶ of O1C2), lift χ ≫ ofHom OIC2.toO1C2 = χ) :
    NormalSpace X := by
  fapply of_lift
    (fun χ ↦ lift χ ≫ O2C3.lift ?hU ?hV OIC2.isClosed_singleton_left OIC2.isClosed_singleton_right
        (isOpen_Iio (a := (⟨0.5, by norm_num⟩ : I)) |>.preimage OIC2.toI.continuous)
        (isOpen_Ioi (a := (⟨0.5, by norm_num⟩ : I)) |>.preimage OIC2.toI.continuous)
        (by apply Disjoint.preimage; simp))
  · intro χ
    conv_rhs => rw [← fac χ]
    rw [Category.assoc]
    congr
    ext (_ | ⟨z, hz₁, hz₂⟩ | _)
    · simp [indicator]
    · simp [apply_ite indicator]; simp [indicator]
    · have : ¬ ((1 : I) < ⟨0.5, by norm_num⟩) := by simp [not_lt, ← Subtype.coe_le_coe]; linarith
      simp [this, indicator]
  · rintro _ (rfl | rfl); simp [← Subtype.coe_lt_coe]; linarith
  · rintro _ (rfl | rfl); simp [← Subtype.coe_lt_coe]; linarith

open scoped Classical Set.Notation in
/-- Alternative characterization by Urysohn's lemma: a space `X` is normal iff
`ofHom OIC2.toO1C2` has the right lifting property against `initial.to X : ⊥_ TopCat ⟶ X`. -/
lemma rlp_separating : NormalSpace X ↔ initial.to X ⧄ ofHom OIC2.toO1C2 where
  mp _ :=
  { sq_hasLift {ι τ} sq := by
      obtain ⟨«λ», h₀, h₁, hI⟩ :=
        exists_continuous_zero_one_of_isClosed (O1C2.isClosed_left.preimage τ.continuous)
          (O1C2.isClosed_right.preimage τ.continuous) (by apply Disjoint.preimage; simp)
      have h₀' : EqOn (Subtype.coind (⇑«λ») hI) 0 (τ ⁻¹' {O1C2.left}) := by
        intro x hx; simp [h₀ hx, Subtype.coind]
      have h₁' : EqOn (Subtype.coind (⇑«λ») hI) 1 (τ ⁻¹' {O1C2.right}) := by
        intro x hx; simp [h₁ hx, Subtype.coind]
      let «λ'» : C(X, OIC2) := OIC2.lift.map
        (O1C2.lift.map (O1C2.isClosed_left.preimage τ.continuous)
          (O1C2.isClosed_right.preimage τ.continuous) (by apply Disjoint.preimage; simp))
        ⟨_, «λ».continuous.subtype_coind hI⟩
        (fun x hx ↦ by simp [ite_eq_iff] at hx; simpa using h₀' hx)
        (fun x hx ↦ by simp [ite_eq_iff] at hx; simpa using h₁' hx.2)
      use ofHom «λ'»
      · exact initial.hom_ext _ _
      · ext x; cases hx : τ x using O1C2.casesOn'
        all_goals simp [toO1C2, ite_eq_iff, «λ'», OIC2.lift.map, hx] }
  mpr h := of_lift_separating (fun χ ↦
    CommSq.lift (hsq := h.sq_hasLift (f := initial.to _) (g := χ) ⟨by simp⟩ ))
    (fun χ ↦ CommSq.fac_right ⟨by simp⟩)

end NormalSpace

namespace CompletelyNormalSpace

def O1C2.quotO2C3 : O2C3 →o O1C2 where
  toFun | .left => .left | .zero | .mid | .one => .one | .right => .right
  monotone' := by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ ⟨⟩ <;> simp [O1C2.le_def, Z3.spec_iff]

lemma _root_.WithBot.some_injective {α} : Function.Injective (WithBot.some : α → WithBot α) :=
  fun x y h ↦ by cases h; rfl

@[reducible] def O1C2B := WithUpperSet (WithBot O1C2)
@[reducible] def O2C3B := WithUpperSet (WithBot O2C3)

noncomputable def indicator : C(O2C3B, O1C2B) :=
  WithUpperSet.map <| OrderHom.withBotMap ⟨NormalSpace.indicator,
    IsUpperSet.monotone_iff_continuous.mpr <| map_continuous _⟩

@[coe] abbrev O1C2B.some (a : O1C2) : O1C2B := WithUpperSet.toUpperSet (WithBot.some a)
@[coe] abbrev O2C3B.some (a : O2C3) : O2C3B := WithUpperSet.toUpperSet (WithBot.some a)

instance : Coe O1C2 O1C2B := ⟨.some⟩
instance : Coe O2C3 O2C3B := ⟨.some⟩

@[simp]
lemma _root_.WithUpperSet.rec_toUpperSet {α} {β : WithUpperSet α → Sort*}
    (h : (a : α) → β (WithUpperSet.toUpperSet a)) (a : α) :
    WithUpperSet.rec h (WithUpperSet.toUpperSet a) = h a :=
  rfl

@[simp] lemma indicator_bot : indicator ⊥ = ⊥ := rfl
@[simp low] lemma indicator_apply {a : O2C3B} :
    indicator a =
      (by
        cases a using WithUpperSet.rec with | _ a =>
        cases a using WithBot.recBotCoe with
        | bot => exact ⊥
        | coe a => cases a using O2C3.casesOn' with
          | left => exact ↑O1C2.left
          | right => exact ↑O1C2.right
          | _ => exact WithUpperSet.toUpperSet ↑O1C2.one) --:=
      -- match a with
      -- | WithUpperSet.toUpperSet' ⊥ => ⊥
      -- | WithUpperSet.toUpperSet' (WithBot.some O2C3.left) => ↑O1C2.left
      -- | WithUpperSet.toUpperSet' (WithBot.some O2C3.right) => ↑O1C2.right
      -- | WithUpperSet.toUpperSet' (WithBot.some _) => WithUpperSet.toUpperSet ↑O1C2.one
      := by
  cases a using WithUpperSet.rec with | _ a =>
  cases a using WithBot.recBotCoe with
  | bot => rfl
  | coe a => cases a using O2C3.casesOn' <;> rfl


lemma O1C2B.isClosed_left_bot : @IsClosed O1C2B _ {↑O1C2.left, ⊥} := by
  rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
  rintro a b h (⟨rfl⟩ | ⟨⟨⟩⟩)
  · cases b using WithUpperSet.rec with | _ b =>
    cases b using WithBot.recBotCoe with
    | bot => simp [O1C2B.some]
    | coe b => cases b <;> simp_all +decide [O1C2B.some, WithUpperSet.toUpperSet_le_iff]
  · simp at h; simp [h]

lemma O1C2B.isClosed_right_bot : @IsClosed O1C2B _ {↑O1C2.right, ⊥} := by
  rw [IsUpperSet.isClosed_iff_isLower, IsLowerSet]
  rintro a b h (⟨rfl⟩ | ⟨⟨⟩⟩)
  · cases b using WithUpperSet.rec with | _ b =>
    cases b using WithBot.recBotCoe with
    | bot => simp [O1C2B.some]
    | coe b => cases b <;> simp_all +decide [O1C2B.some, WithUpperSet.toUpperSet_le_iff]
  · simp at h; simp [h]

lemma O1C2B.continuous_coe : Continuous O1C2B.some :=
  IsUpperSet.WithBot.continuous_coe
-- by
  -- simpa [← IsUpperSet.monotone_iff_continuous] using WithBot.coe_mono

lemma O2C3B.continuous_coe : Continuous O2C3B.some :=
  IsUpperSet.WithBot.continuous_coe

lemma O1C2B.isOpenEmbedding_coe : IsOpenEmbedding O1C2B.some :=
  IsUpperSet.WithBot.isOpenEmbedding_coe

lemma O2C3B.isOpenEmbedding_coe : IsOpenEmbedding O2C3B.some :=
  IsUpperSet.WithBot.isOpenEmbedding_coe

lemma O1C2B.coe_injective : Function.Injective O1C2B.some := WithBot.some_injective
lemma O2C3B.coe_injective : Function.Injective O2C3B.some := WithBot.some_injective

lemma indicator_restrict : indicator.comp ⟨O2C3B.some, O2C3B.continuous_coe⟩ =
    .comp ⟨O1C2B.some, O1C2B.continuous_coe⟩ NormalSpace.indicator := by
  ext (x : O2C3); cases x <;>
    simp [O2C3B.some, O1C2B.some, O2C3.casesOn', NormalSpace.indicator]

lemma of_lift (lift : (X ⟶ of O1C2B) → (X ⟶ of O2C3B))
    (fac : ∀ (χ : X ⟶ of O1C2B), lift χ ≫ ofHom indicator = χ) :
    CompletelyNormalSpace X := by
  apply of_subspaces_normal fun U Uo ↦ ?_
  fapply NormalSpace.of_lift (X := of U)
  · intro χ
    classical let χ' : X ⟶ of O1C2B := ofHom <| IsUpperSet.WithBot.lift Uo (Hom.hom χ)
    refine
      ofHom (ContinuousMap.mapsTo (lift χ') U (range some) ?_ (lift χ').continuous.continuousOn) ≫
      ofHom ⟨Set.rangeSplitting O2C3B.some, O2C3B.isOpenEmbedding_coe.continuous_rangeSplitting⟩
    intro x hx
    have := TopCat.ext_iff.mp (fac χ') x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom] at this
    cases «hλ» : lift χ' x using WithBot.recBotCoe with
    | bot => rw [«hλ», indicator_bot, IsUpperSet.bot_def] at this; simp [χ', hx] at this
    | coe z => exact mem_range_self z
  · intro χ
    extract_lets χ'; specialize fac χ'
    simp_rw [Category.assoc, ← TopCat.ofHom_comp, ContinuousMap.comp]
    ext (x : U) --⟨x, hx⟩
    rw [TopCat.ext_iff] at fac; specialize fac x
    simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, indicator_apply] at fac
    cases hχ' : lift χ' x using WithUpperSet.rec (α := WithBot O2C3) with | _ x =>
    cases x using WithBot.recBotCoe with
    | bot => rw [hχ'] at fac; simp [χ'] at fac
    | coe z =>
      cases z using O2C3.casesOn'
      all_goals
        rw [hχ'] at fac
        simp [χ', O2C3.casesOn'] at fac
        simp [NormalSpace.indicator, MapsTo.restrict, Subtype.map, hχ', ← fac,
        O2C3B.coe_injective.rangeSplitting_apply]

open Set.Notation ContinuousMap Classical in
lemma llp : CompletelyNormalSpace X ↔ initial.to X ⧄ ofHom indicator where
  mp h :=
  { sq_hasLift {ι τ} sq := by
      rw [iff_subspaces_normal] at h
      have rng_some : range O1C2B.some = {⊥}ᶜ := by
        change range WithBot.some = {⊥}ᶜ
        ext x; cases x using WithBot.recBotCoe <;> simp
      let U := τ ⁻¹' range O1C2B.some
      have Uo : IsOpen U := by
        unfold U; rw [rng_some]
        exact IsUpperSet.WithBot.isClosed_singleton_bot.isOpen_compl.preimage τ.continuous
      specialize h U Uo
      let ρ₁ := ContinuousMap.mk _ O1C2B.isOpenEmbedding_coe.continuous_rangeSplitting
      have hρ₁ : comp ⟨O1C2B.some, O1C2B.continuous_coe⟩ ρ₁ = .subtypeVal := by
        ext; simp [ρ₁, apply_rangeSplitting]
      let τ' := h.lift (X := of U) <| ofHom <|
        ρ₁.comp <| (Hom.hom τ).restrictPreimage (range O1C2B.some)
      use ofHom <| IsUpperSet.WithBot.lift Uo (Hom.hom τ')
      · exact initial.hom_ext _ _
      · rsuffices ⟨h₁, h₂⟩ :
          (ofHom subtypeVal ≫ ofHom (IsUpperSet.WithBot.lift Uo (Hom.hom τ'))
            ≫ ofHom indicator : of U ⟶ of O1C2B) = ofHom .subtypeVal ≫ τ ∧
          (ofHom subtypeVal ≫ ofHom (IsUpperSet.WithBot.lift Uo (Hom.hom τ')) ≫ ofHom indicator :
            of ↑Uᶜ ⟶ of O1C2B) = ofHom .subtypeVal ≫ τ
        · ext x; by_cases hx : x ∈ U
          · rw [← Subtype.coe_mk x hx, ← subtypeVal_apply, ← ContinuousMap.comp_apply,
            ← hom_ofHom subtypeVal, ← TopCat.hom_comp, h₁]; rfl
          · rw [← Subtype.coe_mk (p := Uᶜ) x hx, ← subtypeVal_apply, ← ContinuousMap.comp_apply,
            ← hom_ofHom subtypeVal, ← TopCat.hom_comp, h₂]; rfl
        · split_ands
          · simp_rw [← ofHom_comp, ContinuousMap.comp_assoc,
            ← ContinuousMap.restrict_eq, IsUpperSet.WithBot.lift_restrict,
            ← ContinuousMap.comp_assoc, Function.comp_def WithUpperSet.toUpperSet,
            indicator_restrict]
            simp only [ofHom_comp, comp_assoc, ofHom_hom, NormalSpace.lift_fac, Category.assoc,
              ← ofHom_comp ρ₁, hρ₁, τ']
            rw [← ofHom_comp, ContinuousMap.val_comp_restrictPreimage]; rfl
          · simp_rw [← ofHom_comp, ContinuousMap.comp_assoc,
            ← ContinuousMap.restrict_eq, IsUpperSet.WithBot.lift_restrict_compl]
            ext ⟨x, hx⟩; simp [U, rng_some] at hx; simp [hx] }
  mpr h := of_lift (fun χ ↦
    CommSq.lift (hsq := h.sq_hasLift (f := initial.to _) (g := χ) ⟨by simp⟩ ))
    (fun χ ↦ CommSq.fac_right ⟨by simp⟩)

end CompletelyNormalSpace

namespace PerfectlyNormalSpace
open scoped unitInterval

/-- The hom `I ⟶ O1C2` taking `0 → L`, `1 → R` and everything else to `1`. -/
noncomputable def intervalToO1C2 : of (ULift I) ⟶ of O1C2 :=
  O1C2.lift (U := {0}) (V := {1}) isClosed_singleton isClosed_singleton (by simp)

open ContinuousMap Set.Notation in
/-- A space `X` is perfectly normal if any morphism to `O1C2` (encoding two disjoint closed sets)
can be lifted through `I`, the topological interval. -/
lemma of_lift (lift : (X ⟶ of O1C2) → (X ⟶ of (ULift I)))
    (fac : ∀ (χ : X ⟶ of O1C2), lift χ ≫ intervalToO1C2 = χ) : PerfectlyNormalSpace X :=
  have fac₀ χ : (lift χ) ⁻¹' {⟨0⟩} = χ ⁻¹' {O1C2.left} := by
    conv_rhs => rw [← fac χ]
    ext x; simp [intervalToO1C2, ite_eq_iff, ULift.ext_iff]
  have fac₁ χ : (lift χ) ⁻¹' {⟨1⟩} = χ ⁻¹' {O1C2.right} := by
    conv_rhs => rw [← fac χ]
    ext x; simp +contextual [intervalToO1C2, ite_eq_iff, ULift.ext_iff]
  have preimageVal₀ : I ↓∩ {0} = {0} := by ext; simp
  have preimageVal₁ : I ↓∩ {1} = {1} := by ext; simp
  of_precise_separating fun {s t} sC tC disj ↦
    ⟨subtypeVal.comp <| uliftDown.comp <| Hom.hom <| lift (O1C2.lift sC tC disj), by
      simp [preimage_comp, uliftDown, subtypeVal, preimageVal₀, ← Homeomorph.coe_toEquiv,
      ←Homeomorph.ulift.image_symm_eq_preimage]
      simp [Homeomorph.ulift, fac₀], by
      simp [preimage_comp, uliftDown, subtypeVal, preimageVal₁, ← Homeomorph.coe_toEquiv,
      ← Homeomorph.ulift.image_symm_eq_preimage]
      simp [Homeomorph.ulift, fac₁]⟩

/-- A topological space `X` is normal iff its morphism from the initial object
`initial.to : ⊥_ TopCat ⟶ X` has the left lifting property against
`intervalToO1C2 : of (ULift I) ⟶ of O1C2`. -/
lemma llp : PerfectlyNormalSpace X ↔ initial.to X ⧄ intervalToO1C2 where
  mp _ :=
  { sq_hasLift {ι τ} sq := by
      obtain ⟨«λ», h₀, h₁, hI⟩ := exists_precise_continuous_zero_one_of_isClosed
        (O1C2.isClosed_left.preimage τ.continuous) (O1C2.isClosed_right.preimage τ.continuous)
        (by apply Disjoint.preimage; simp)
      use ofHom ⟨_, continuous_uliftUp.comp <| Continuous.subtype_coind «λ».continuous hI⟩
      · exact initial.hom_ext _ _
      · ext x
        cases hx : (τ x : O1C2) using O1C2.casesOn'
        all_goals
          simp [Set.ext_iff, @eq_comm O1C2] at h₀ h₁
          simp [Subtype.coind, intervalToO1C2, ULift.ext_iff, h₀, h₁, Subtype.ext_iff, hx] }
  mpr h := of_lift (fun χ ↦ CommSq.lift (hsq := h.sq_hasLift _) (f := initial.to _) (g := χ)
    ⟨initial.hom_ext _ _⟩) (fun χ ↦ CommSq.fac_right _)

end PerfectlyNormalSpace
