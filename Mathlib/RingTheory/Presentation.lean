/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
import Mathlib.RingTheory.Generators
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.RingHom.Surjective
/-!

# Presentations of algebras

## Main definition

- `Algebra.Presentation`: A presentation of a `R`-algebra `S` is a family of
  generators with
  1. `relations`: The type of relations.
  2. `relation : relations → MvPolynomial vars R`: The assignment of
     each relation to a polynomial in the generators.

## TODO

- define `Hom`s of presentations

-/

universe t w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/--
A presentation of a `R`-algebra `S` is a family of
generators with
1. `relations`: The type of relations.
2. `relation : relations → MvPolynomial vars R`: The assignment of
each relation to a polynomial in the generators.
-/
structure Algebra.Presentation extends Algebra.Generators.{w} R S where
  /-- The type of relations.  -/
  relations : Type t
  /-- The assignment of each relation to a polynomial in the generators. -/
  relation : relations → MvPolynomial vars R
  /-- The relations span the kernel of the canonical map. -/
  ker_algebraMap_eq_span_range_relation :
    RingHom.ker (aeval val) = Ideal.span (Set.range <| relation)

namespace Algebra.Presentation

variable {R S}
variable (P : Presentation.{t, w} R S)

protected abbrev Ideal : Ideal P.Ring := RingHom.ker <| aeval P.val

lemma ideal_eq_span_range_relation : P.Ideal = Ideal.span (Set.range <| P.relation) :=
  P.ker_algebraMap_eq_span_range_relation

lemma algebraMap_relation (i) : aeval P.val (P.relation i) = 0 := by
  rw [← RingHom.mem_ker, ker_algebraMap_eq_span_range_relation]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The polynomial algebra wrt a family of generators module a family of relations. -/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.Ideal

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) P.aeval_val_σ

@[simp]
lemma quotientEquiv_mk (p : P.Ring) : P.quotientEquiv p = algebraMap P.Ring S p :=
  rfl

@[simp]
lemma quotientEquiv_symm (x : S) : P.quotientEquiv.symm x = P.σ x :=
  rfl

/--
Dimension of a presentation defined as the cardinality of the generators
minus the cardinality of the relations.

Note: this definition is completely non-sensical for non-finite presentations and
even then for this to make sense, you should assume that the presentation
is standard smooth.
-/
noncomputable def dimension : ℕ :=
  Nat.card P.vars - Nat.card P.relations

/-- A presentation is called finite if there are only finitely-many
relations and finitely-many relations. -/
class IsFinite (P : Presentation.{t, w} R S) : Prop where
  finite_vars : Finite P.vars
  finite_relations : Finite P.relations

attribute [instance] IsFinite.finite_vars IsFinite.finite_relations

lemma ideal_fg_of_isFinite [P.IsFinite] : P.Ideal.FG := by
  use (Set.finite_range P.relation).toFinset
  simp [ideal_eq_span_range_relation]

/-- If a presentation is finite, the corresponding quotient is
of finite presentation. -/
instance [P.IsFinite] : FinitePresentation R P.Quotient :=
  sorry
  --FinitePresentation.quotient P.ideal_fg_of_isFinite

lemma finitePresentation_of_presentation_of_isFinite [P.IsFinite] :
    FinitePresentation R S :=
  FinitePresentation.equiv (P.quotientEquiv.restrictScalars R)

section Construction

/-
TODO: add constructor for `Presentation` with `Presentation.IsFinite` for
a finitely-presented algebra.
-/

section Localization

variable (r : R) [IsLocalization.Away r S]

noncomputable def auxHom : ((MvPolynomial Unit R) ⧸ (Ideal.span { C r * X () - 1 })) →ₐ[R] S :=
  Ideal.Quotient.liftₐ (Ideal.span { C r * X () - 1})
    (aeval (Generators.localizationAway r).val) <| by
    intro p hp
    refine Submodule.span_induction hp ?_ ?_ ?_ ?_
    · rintro p ⟨q, rfl⟩
      simp
    · simp
    · intro p q hp hq
      simp [hp, hq]
    · intro a x hx
      simp [hx]

@[simp]
lemma auxHom_mk (p : MvPolynomial Unit R) :
    auxHom r p = aeval (S₁ := S) (Generators.localizationAway r).val p :=
  rfl

lemma auxHom_mk' (p : MvPolynomial Unit R) :
    auxHom r ⟦p⟧ = aeval (S₁ := S) (Generators.localizationAway r).val p :=
  rfl

noncomputable def auxInv : S →+* ((MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 }) :=
  letI g : R →+* MvPolynomial Unit R ⧸ (Ideal.span { C r * X () - 1 }) :=
    (Ideal.Quotient.mk _).comp C
  haveI : IsUnit (g r) := by
    simp [g]
    rw [isUnit_iff_exists_inv]
    use (Ideal.Quotient.mk _ <| X ())
    rw [← _root_.map_mul, ← map_one (Ideal.Quotient.mk _)]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact Ideal.mem_span_singleton_self (C r * X () - 1)
  IsLocalization.Away.lift (S := S) r this

lemma auxHom_auxInv : (auxHom r).toRingHom.comp (auxInv r) = RingHom.id S := by
  apply IsLocalization.ringHom_ext (Submonoid.powers r)
  ext x
  simp [auxInv]

lemma auxInv_auxHom : (auxInv r).comp (auxHom (S := S) r).toRingHom = RingHom.id _ := by
  have hf : Function.Surjective (Ideal.Quotient.mk (Ideal.span { C r * X () - 1 })) :=
    Ideal.Quotient.mk_surjective
  rw [← RingHom.cancel_right hf]
  ext x
  simp [auxInv]
  simp [auxInv]
  erw [IsLocalization.lift_mk'_spec]
  simp
  rw [← _root_.map_one (Ideal.Quotient.mk _)]
  erw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  rw [← Ideal.neg_mem_iff]
  simp only [neg_sub]
  exact Ideal.mem_span_singleton_self (C r * X x - 1)

noncomputable def auxEquiv : ((MvPolynomial Unit R) ⧸ Ideal.span { C r * X () - 1 }) ≃ₐ[R] S where
  toFun := auxHom r
  invFun :=
    letI g : R →+* MvPolynomial Unit R ⧸ (Ideal.span { C r * X () - 1 }) :=
      (Ideal.Quotient.mk _).comp C
    haveI : IsUnit (g r) := by
      simp [g]
      rw [isUnit_iff_exists_inv]
      use (Ideal.Quotient.mk _ <| X ())
      rw [← _root_.map_mul, ← map_one (Ideal.Quotient.mk _)]
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact Ideal.mem_span_singleton_self (C r * X () - 1)
    IsLocalization.Away.lift (S := S) r this
  left_inv := by
    intro x
    have := auxInv_auxHom (S := S) r
    have : ((auxInv r).comp (auxHom (S := S) r).toRingHom) x = RingHom.id _ x := by
      exact congrFun (congrArg DFunLike.coe this) x
    simp at this
    exact this
  right_inv := by
    intro s
    have := auxHom_auxInv (S := S) r
    have : ((auxHom r).toRingHom.comp (auxInv r)) s = RingHom.id S s := by
      exact congrFun (congrArg DFunLike.coe this) s
    simp at this
    exact this
  map_mul' := by simp
  map_add' := by simp
  commutes' := by simp

lemma ker_eq_span : RingHom.ker (aeval (S₁ := S) (Generators.localizationAway r).val) =
    Ideal.span { C r * X () - 1 } := by
  let I := (Ideal.span {C r * X () - 1})
  --erw [← Ideal.Quotient.mkₐ_ker R (Ideal.span {C r * X () - 1})]
  --have : (auxEquiv r).comp (Ideal.Quotient.mkₐ_ker R I)
  have : aeval (S₁ := S) (Generators.localizationAway r).val =
      (auxHom r).comp (Ideal.Quotient.mkₐ R I) := by
    symm
    apply Ideal.Quotient.liftₐ_comp
  rw [this]
  erw [← RingHom.comap_ker]
  simp
  show Ideal.comap _ (RingHom.ker (auxEquiv r)) = Ideal.span {C r * X () - 1}
  simp
  rw [← RingHom.ker_eq_comap_bot]
  simp

@[simps relations relation]
noncomputable def localizationAway : Presentation R S where
  toGenerators := Generators.localizationAway r
  relations := Unit
  relation _ := C r * X () - 1
  ker_algebraMap_eq_span_range_relation := by
    simp
    apply ker_eq_span (S := S) r

instance localizationAway_isFinite : (localizationAway r (S := S)).IsFinite where
  finite_vars := inferInstanceAs <| Finite Unit
  finite_relations := inferInstanceAs <| Finite Unit

@[simp]
lemma localizationAway_dimension_zero : (localizationAway r (S := S)).dimension = 0 := by
  simp [Presentation.dimension]
  show Nat.card Unit - 1 = 0
  simp

end Localization

variable {T} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : Presentation S T) (P : Presentation R S)

private noncomputable def comp_relation_aux (r : Q.relations) : MvPolynomial (Q.vars ⊕ P.vars) R :=
  Finsupp.sum (Q.relation r)
    (fun x j ↦ (MvPolynomial.rename Sum.inr <| P.σ j) * monomial (x.mapDomain Sum.inl) 1)

lemma comp_relation_aux_map (r : Q.relations) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val)) (Q.comp_relation_aux P r) = Q.relation r := by
  simp only [comp_relation_aux, Generators.comp_vars, Sum.elim_inl, map_finsupp_sum]
  simp only [_root_.map_mul, aeval_rename, aeval_monomial, Sum.elim_comp_inr, _root_.map_one,
    one_mul]
  nth_rw 2 [← Finsupp.sum_single (Q.relation r)]
  congr
  ext u s m
  congr
  show _ = monomial u s
  simp only [aeval, AlgHom.coe_mk, coe_eval₂Hom]
  rw [monomial_eq, IsScalarTower.algebraMap_eq R S]
  simp only [algebraMap_eq]
  rw [← eval₂_comp_left, ← aeval_def, P.aeval_val_σ]
  congr
  rw [Finsupp.prod_mapDomain_index_inj]
  simp only [Sum.elim_inl]
  exact Sum.inl_injective

lemma comp_aeval_aeval_apply (p : MvPolynomial (Q.vars ⊕ P.vars) R) :
    (aeval (Q.comp P.toGenerators).val) p =
      (aeval Q.val) ((aeval (Sum.elim X (⇑C ∘ P.val))) p) := by
  induction p using MvPolynomial.induction_on with
  | h_C a =>
      simp
      rw [← IsScalarTower.algebraMap_apply]
  | h_X p i h =>
      rw [_root_.map_mul, h, _root_.map_mul, _root_.map_mul]
      congr
      rw [aeval_X, aeval_X]
      match i with
      | Sum.inl i => simp
      | Sum.inr i => simp
  | h_add p q hp hq => simp_rw [_root_.map_add, hp, hq]

lemma comap_span_of_surj {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Surjective f)
    (s : Set S) (t : Set R) (hts : f '' t = s) :
    Ideal.comap f (Ideal.span s) = Ideal.span t ⊔ RingHom.ker f := by
  apply le_antisymm
  · intro x hx
    simp at hx
    let v (x : t) : S := f x
    have : Set.range v = s := by
      rw [← hts]
      exact (Set.image_eq_range f t).symm
    rw [← this] at hx
    rw [Finsupp.mem_ideal_span_range_iff_exists_finsupp] at hx
    obtain ⟨c, hc⟩ := hx
    simp [v] at hc
    have hfa (a : S) : f (Function.invFun f a) = a := Function.rightInverse_invFun hf a
    have : (c.sum fun i a ↦ a * f ↑i) = (c.sum fun i a ↦ f (Function.invFun f a) * f ↑i) := by
      congr
      ext i a
      rw [hfa a]
    rw [this] at hc
    simp_rw [← RingHom.map_mul] at hc
    rw [← map_finsupp_sum] at hc
    rw [← RingHom.sub_mem_ker_iff] at hc
    have : x = x - (c.sum fun i a ↦ Function.invFun f a * ↑i) + (c.sum fun i a ↦ Function.invFun f a * ↑i) := by
      simp
    rw [this]
    apply Ideal.add_mem
    · rw [← Ideal.neg_mem_iff]
      simp
      apply Ideal.mem_sup_right
      assumption
    · apply Ideal.mem_sup_left
      apply Ideal.sum_mem
      rintro x -
      simp
      apply Ideal.mul_mem_left
      apply Ideal.subset_span
      exact x.property
  · apply sup_le
    · rw [Ideal.span_le]
      intro a ha
      simp
      apply Ideal.subset_span
      rw [← hts]
      exact Set.mem_image_of_mem f ha
    · intro x hx
      rw [RingHom.mem_ker] at hx
      simp [hx]

noncomputable abbrev foov : MvPolynomial (Q.vars ⊕ P.vars) R →ₐ[R] MvPolynomial Q.vars S :=
  aeval (Sum.elim X (⇑C ∘ P.val))

lemma foov_surjective : Function.Surjective (Q.foov P) := by
  intro p
  induction' p using MvPolynomial.induction_on with a p q hp hq p i h
  · simp [foov]
    use (rename Sum.inr <| P.σ a)
    rw [aeval_rename]
    simp
    have (p : MvPolynomial P.vars R) :
        aeval (C ∘ P.val) p = (C (aeval P.val p) : MvPolynomial Q.vars S) := by
      induction' p using MvPolynomial.induction_on with a p q hp hq p i h
      · simp
      · simp [hp, hq]
      · simp [h]
    rw [this]
    simp
  · obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    use a + b
    simp
  · obtain ⟨a, rfl⟩ := h
    use (a * X (Sum.inl i))
    simp

lemma foov_image :
    Q.foov P '' (Set.range (Algebra.Presentation.comp_relation_aux Q P)) =
      Set.range Q.relation := by
  ext x
  constructor
  · rintro ⟨y, ⟨a, rfl⟩, rfl⟩
    use a
    rw [comp_relation_aux_map]
  · rintro ⟨y, rfl⟩
    use Q.comp_relation_aux P y
    simp
    rw [comp_relation_aux_map]

noncomputable def foovEquiv :
    MvPolynomial (Q.vars ⊕ P.vars) R ≃ₐ[R] MvPolynomial Q.vars (MvPolynomial P.vars R) :=
  sumAlgEquiv R _ _

lemma foov_eq_comp : Q.foov P =
    (MvPolynomial.mapAlgHom (aeval P.val)).comp (Q.foovEquiv P).toAlgHom := by
  ext i : 1
  match i with
  | Sum.inl i => simp [foovEquiv]
  | Sum.inr i => simp [foovEquiv]

lemma barv_comp :
    (((Q.foovEquiv P).toAlgHom).comp (rename Sum.inr)).toRingHom = C := by
  apply RingHom.ext
  intro x
  induction x using MvPolynomial.induction_on with
  | h_C a => simp
  | h_add p q hp hq =>
      simp
      erw [hp, hq]
  | h_X p n h =>
      simp
      erw [h]
      congr
      simp [foovEquiv]

lemma Ideal.comap_map_ofEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    Ideal.comap e (Ideal.map e I) = I := by
  ext x
  constructor
  · intro hx
    simp_all
    have : x = e.symm (e x) := by simp
    rw [this]
    have : I = Ideal.map e.symm (Ideal.map e I) := by
      show I = Ideal.map e.symm.toRingHom (Ideal.map e.toRingHom I)
      rw [Ideal.map_map]
      simp
    rw [this]
    exact Ideal.mem_map_of_mem e.symm hx
  · intro hx
    simp only [Ideal.mem_comap]
    exact Ideal.mem_map_of_mem e hx

lemma foov_ker :
    RingHom.ker (Q.foov P) = Ideal.map (rename Sum.inr) (RingHom.ker (aeval P.val)) := by
  rw [foov_eq_comp]
  erw [← RingHom.comap_ker]
  erw [MvPolynomial.ker_map]
  simp
  rw [← barv_comp]
  erw [← Ideal.map_map]
  simp
  erw [Ideal.comap_map_ofEquiv]
  rfl

lemma map_toComp_ker (Q : Presentation S T) (P : Presentation R S) :
    P.ker.map (Q.toGenerators.toComp P.toGenerators).toAlgHom.toRingHom = RingHom.ker (Q.toGenerators.ofComp P.toGenerators).toAlgHom := by
  symm
  exact foov_ker Q P

/-- Given presentations of `T` over `S` and of `S` over `R`,
we may construct a presentation of `T` over `R`. -/
@[simps relations, simps (config := .lemmasOnly) relation]
noncomputable def comp : Presentation R T where
  toGenerators := Q.toGenerators.comp P.toGenerators
  relations := Q.relations ⊕ P.relations
  relation := Sum.elim (Q.comp_relation_aux P)
    (fun rp ↦ MvPolynomial.rename Sum.inr <| P.relation rp)
  ker_algebraMap_eq_span_range_relation := by
    apply le_antisymm
    · show RingHom.ker (aeval _) ≤ _
      set f : MvPolynomial _ R →ₐ[R] T := aeval (Q.toGenerators.comp P.toGenerators).val
      set u : MvPolynomial Q.vars S →ₐ[S] T := aeval Q.val
      set v : MvPolynomial (Q.vars ⊕ P.vars) R →ₐ[R] MvPolynomial Q.vars S := Q.foov P
      set f' : MvPolynomial (Q.vars ⊕ P.vars) R →+* T := u.toRingHom.comp v
      have : f.toRingHom = f' := by
        apply RingHom.ext (fun p ↦ ?_)
        simp [f, f', u, v, foov]
        apply Q.comp_aeval_aeval_apply P
      show RingHom.ker f.toRingHom ≤ _
      rw [this]
      simp [f']
      rw [← RingHom.comap_ker]
      erw [ker_algebraMap_eq_span_range_relation]
      let s : Set (MvPolynomial Q.vars S) := Set.range Q.relation
      let t : Set (MvPolynomial (Q.vars ⊕ P.vars) R) :=
        Set.range (Algebra.Presentation.comp_relation_aux Q P)
      have hts : v '' t = s := Q.foov_image P
      have hv : Function.Surjective v := Q.foov_surjective P
      have hvker : RingHom.ker v.toRingHom =
          Ideal.span (Set.range fun rp ↦ (rename Sum.inr) (P.relation rp)) := by
        simp [v]
        erw [foov_ker]
        erw [P.ker_algebraMap_eq_span_range_relation]
        rw [Ideal.map_span]
        congr
        ext
        simp
      rw [comap_span_of_surj v hv s t hts]
      apply sup_le
      · rw [Ideal.span_le]
        intro x hx
        apply Ideal.subset_span
        apply Set.mem_union_left
        exact hx
      · rw [Ideal.span_union]
        erw [hvker]
        apply le_sup_right
    · rw [Ideal.span_le]
      rintro x ⟨y, rfl⟩
      match y with
      | Sum.inl y =>
          simp
          rw [RingHom.mem_ker]
          have : aeval Q.val (Q.relation y) = 0 := by
            rw [← RingHom.mem_ker]
            erw [Q.ker_algebraMap_eq_span_range_relation]
            apply Ideal.subset_span
            exact Set.mem_range_self y
          show (aeval _) (Algebra.Presentation.comp_relation_aux Q P y) = 0
          rw [← this, ← Q.comp_relation_aux_map P]
          apply comp_aeval_aeval_apply
      | Sum.inr y =>
          simp
          rw [RingHom.mem_ker]
          show (aeval _) _ = 0
          erw [aeval_rename]
          have : (Q.toGenerators.comp P.toGenerators).val ∘ Sum.inr = algebraMap S T ∘ P.val := by
            ext j
            simp
          rw [this]
          rw [MvPolynomial.aeval_algebraMap_apply]
          have : aeval P.val (P.relation y) = 0 := by
            rw [← RingHom.mem_ker]
            erw [P.ker_algebraMap_eq_span_range_relation]
            apply Ideal.subset_span
            exact Set.mem_range_self y
          simp [this]

lemma comp_relation_map (r : Q.relations) :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val)) ((Q.comp P).relation (Sum.inl r)) = Q.relation r := by
  simp [comp_relation, comp_relation_aux_map]

instance comp_isFinite [P.IsFinite] [Q.IsFinite] : (Q.comp P).IsFinite where
  finite_vars := inferInstanceAs <| Finite (Q.vars ⊕ P.vars)
  finite_relations := inferInstanceAs <| Finite (Q.relations ⊕ P.relations)

end Construction

open TensorProduct

noncomputable
def Generators.baseChange {R S T} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : Generators R S) : Generators T (T ⊗[R] S) := by
  --apply surjective_stableUnderBaseChange
  apply Generators.ofSurjective (fun x ↦ 1 ⊗ₜ[R] P.val x)
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b =>
    let X := P.σ b
    use a • MvPolynomial.map (algebraMap R T) X
    simp [X]
    rw [aeval_map_algebraMap]
    have : ∀ y : P.Ring,
      aeval (fun x ↦ (1 ⊗ₜ[R] P.val x : T ⊗[R] S)) y = 1 ⊗ₜ aeval (fun x ↦ P.val x) y := by
      intro y
      induction y using MvPolynomial.induction_on with
      | h_C a =>
        rw [aeval_C, aeval_C]
        show algebraMap R T a ⊗ₜ 1 = _
        rw [algebraMap_eq_smul_one, smul_tmul, algebraMap_eq_smul_one]
      | h_add p q hp hq =>
        simp [tmul_add]
        rw [hp, hq]
      | h_X p i hp =>
        rw[_root_.map_mul, hp]
        rw[aeval_X]
        rw[_root_.map_mul, aeval_X]
        simp
    rw [this, P.aeval_val_σ, smul_tmul', smul_eq_mul, mul_one]
  | add x y ex ey =>
    obtain ⟨a, ha⟩ := ex
    obtain ⟨b, hb⟩ := ey
    use (a + b)
    rw[map_add, ha, hb]

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 10000000000
noncomputable
def baseChange {R S T} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (P : Presentation R S) : Presentation T (T ⊗[R] S) where
  __ := Generators.baseChange P.toGenerators
  relations := P.relations
  relation := fun i ↦ MvPolynomial.map (algebraMap R T) (P.relation i)
  ker_algebraMap_eq_span_range_relation := by
    dsimp
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      have H := Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S) P.algebraMap_surjective
      let e := MvPolynomial.algebraTensorAlgEquiv (R := R) (σ := P.vars) (A := T)
      have H' : e.symm x ∈ RingHom.ker (TensorProduct.map (AlgHom.id R T) (IsScalarTower.toAlgHom R P.Ring S)) := by
        rw [RingHom.mem_ker, ← hx]
        clear hx
        induction x using MvPolynomial.induction_on with
        | h_C a =>
          simp only [Generators.algebraMap_apply, algHom_C, TensorProduct.algebraMap_apply,
            id.map_eq_id, RingHom.id_apply, e]
          erw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
          simp
        | h_add p q hp hq =>
          simp only [map_add]
          rw[hp, hq]
        | h_X p i hp =>
          repeat rw[_root_.map_mul]
          rw[hp]
          simp [e]
          sorry
          --rfl
        -- have Z : ∀ x : MvPolynomial (P.vars) (T), (algebraMap (MvPolynomial (foo P.toGenerators).vars T) x =
      erw [H, ker_algebraMap_eq_span_range_relation] at H'
      erw [← Ideal.mem_comap, Ideal.comap_symm, Ideal.map_map, Ideal.map_span, ← Set.range_comp] at H'
      convert H'
      simp
      sorry
      --rfl
    · rw [Ideal.span_le]
      intro x hx
      obtain ⟨y, hy⟩ := hx
      have Z := algebraMap_relation (P) y
      apply_fun TensorProduct.includeRight (R := R) (A := T) at Z
      rw [map_zero] at Z
      sorry
      /-
      show algebraMap _ _ x = 0
      convert Z
      rw [← hy]
      simp
      rw [aeval_map_algebraMap]
      show _ = includeRight _
      erw [map_aeval]
      erw [includeRight.comp_algebraMap]
      rfl
      -/
