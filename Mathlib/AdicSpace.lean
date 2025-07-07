import Mathlib

universe u

open Topology CategoryTheory TopologicalSpace

structure HuberRing.ringOfDefinition (R₀ : Type u) (R : Type u)
    [CommRing R₀] [TopologicalSpace R₀] [IsTopologicalRing R₀]
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] extends Algebra R₀ R where
  emb : IsOpenEmbedding (_root_.algebraMap R₀ R)
  J : Ideal R₀
  fg : J.FG
  adic : IsAdic J

class HuberRing (R : Type u) extends CommRing R, TopologicalSpace R, IsTopologicalRing R where
  pod : ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : TopologicalSpace R₀) (_ : IsTopologicalRing R₀),
    Nonempty (HuberRing.ringOfDefinition R₀ R)

structure IsRingOfIntegralElements (R₀ : Type u) (R : Type u)
    [CommRing R₀] [TopologicalSpace R₀] [HuberRing R] [Algebra R₀ R] : Prop extends
    IsIntegrallyClosedIn R₀ R, IsOpenEmbedding (algebraMap R₀ R) where
  is_power_bounded (r : R₀) : ∀ U ∈ nhds (0 : R), ∃ V ∈ nhds (0 : R),
    ∀ n : ℕ, ∀ v ∈ V, v * (algebraMap R₀ R r) ^ n ∈ U

lemma IsRingOfIntegralElements.isTopologicalRing {R₀ : Type u} {R : Type u}
    [CommRing R₀] [TopologicalSpace R₀] [HuberRing R] [Algebra R₀ R]
    (h : IsRingOfIntegralElements R₀ R) : IsTopologicalRing R₀ where
  continuous_add := by
    rw [h.toIsEmbedding.continuous_iff]
    change Continuous (fun (p : R₀ × R₀) ↦ algebraMap R₀ R (p.1 + p.2))
    simp only [map_add]
    apply Continuous.add
    · apply h.continuous.comp
      exact continuous_fst
    · apply h.continuous.comp
      exact continuous_snd
  continuous_mul := by
    rw [h.toIsEmbedding.continuous_iff]
    change Continuous (fun (p : R₀ × R₀) ↦ algebraMap R₀ R (p.1 * p.2))
    simp only [map_mul]
    apply Continuous.mul
    · apply h.continuous.comp
      exact continuous_fst
    · apply h.continuous.comp
      exact continuous_snd
  continuous_neg := by
    rw [h.toIsEmbedding.continuous_iff]
    change Continuous (fun (p : R₀) ↦ algebraMap R₀ R (-p))
    simp only [map_neg]
    exact h.continuous.neg

structure HuberPair where
  plus : Type u
  carrier : Type u
  [ring : CommRing plus]
  [topologicalSpace : TopologicalSpace plus]
  [huber : HuberRing carrier]
  [algebra : Algebra plus carrier]
  int : IsRingOfIntegralElements plus carrier

namespace HuberPair

instance : CoeSort HuberPair (Type u) where
  coe := carrier

variable (A : HuberPair)

instance : HuberRing A := A.huber

instance : CommRing A.plus := A.ring

instance : TopologicalSpace A.plus := A.topologicalSpace

instance : Algebra A.plus A := A.algebra

instance : IsTopologicalRing A.plus := A.int.isTopologicalRing

end HuberPair

def Spv (R : Type u) [CommRing R] : Type u := ValuativeRel R

def Spv.outΓ₀ {R : Type u} [CommRing R] (v : Spv R) : Type u :=
  letI : ValuativeRel R := v
  ValuativeRel.ValueGroupWithZero R

noncomputable instance {R : Type u} [CommRing R] (v : Spv R) :
    LinearOrderedCommGroupWithZero v.outΓ₀ := by
  dsimp [Spv.outΓ₀]
  infer_instance

noncomputable def Spv.out {R : Type u} [CommRing R] (v : Spv R) : Valuation R (v.outΓ₀) :=
  letI : ValuativeRel R := v
  ValuativeRel.valuation R

noncomputable instance (R : Type u) [CommRing R] :
    CoeFun (Spv R) (fun v ↦ (R → Spv.outΓ₀ v)) where
  coe v := (v.out : R → v.outΓ₀)

noncomputable def Spv.lift {R : Type u} [CommRing R] {X : Type*}
    (f : ∀ ⦃Γ₀ : Type u⦄ [LinearOrderedCommGroupWithZero Γ₀], Valuation R Γ₀ → X) (v : Spv R) : X :=
  f (out v)

def Spv.basicOpen {R : Type u} [CommRing R] (r s : R) : Set (Spv R) :=
  {v | v r ≤ v s ∧ v s ≠ 0}

instance (R : Type u) [CommRing R] : TopologicalSpace (Spv R) :=
  TopologicalSpace.generateFrom {U | ∃ r s, U = Spv.basicOpen r s}

def ValuativeRel.inducedTopology (R : Type u) [CommRing R] [ValuativeRel R] : TopologicalSpace R :=
  let t : TopologicalSpace (ValuativeRel.ValueGroupWithZero R) := {
    IsOpen s := 0 ∉ s ∨ ∃ γ, γ ≠ 0 ∧ {x | x < γ} ⊆ s
    isOpen_univ := Or.inr ⟨1, by simp⟩
    isOpen_inter s t := by
      rintro (hs | ⟨γs, hs⟩) (ht | ⟨γt, ht⟩)
      all_goals try tauto_set
      right
      refine ⟨min γs γt, by simp_all [min_eq_iff], fun _ _ ↦ ⟨?_, ?_⟩⟩
      · apply hs.2
        simp_all
      · apply ht.2
        simp_all
    isOpen_sUnion s hs := by
      simp only [Set.mem_sUnion, not_exists, not_and, ne_eq]
      by_cases h : ∀ x ∈ s, 0 ∉ x
      · simp_all
      right
      push_neg at h
      obtain ⟨x, hx, h₀⟩ := h
      specialize hs x hx
      simp only [h₀, not_true_eq_false, ne_eq, false_or] at hs
      obtain ⟨γ, hγ⟩ := hs
      refine ⟨γ, hγ.1, fun _ _ ↦ ?_⟩
      aesop }
  TopologicalSpace.induced (valuation R) t

class ValuativeRel.IsContinuous (R : Type u) [CommRing R] [ValuativeRel R]
    [t : TopologicalSpace R] : Prop where
  induced_le  : ValuativeRel.inducedTopology R ≤ t

def Spv.IsContinuous {R : Type u} [CommRing R] [t : TopologicalSpace R] (v : Spv R) : Prop :=
  letI : ValuativeRel R := v
  ValuativeRel.IsContinuous R

def ValuativeRel.comap {R S : Type*} [CommRing R] [CommRing S] (v : ValuativeRel S) (f : R →+* S) :
    ValuativeRel R where
  rel x y := f x ≤ᵥ f y
  rel_total x y := by exact rel_total (f x) (f y)
  rel_trans hxy hyz := by apply rel_trans hxy hyz
  rel_add _ _ := by
    simp only [map_add]
    apply rel_add
    all_goals assumption
  rel_mul_right _ _ := by
    simp only [map_mul]
    apply rel_mul_right
    assumption
  rel_mul_cancel {x y z} h₁ h₂ := by
    simp only [map_mul] at h₂
    simp only [map_zero] at h₁
    apply rel_mul_cancel (z := f z)
    all_goals assumption
  not_rel_one_zero := by
    simp only [map_one, map_zero]
    apply not_rel_one_zero

nonrec def Spv.comap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (v : Spv S) : Spv R :=
  v.comap f

section TopRingCat

structure ContinuousRingHom (A B : Type*)
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B] extends A →+* B, C(A, B)

infixr:25 " →ₜ+* " => ContinuousRingHom

section ContinuousRingHom

variable {A B C : Type*}
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [Ring C] [TopologicalSpace C] [IsTopologicalRing C]

instance : FunLike (A →ₜ+* B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨ ⟨ _ , _ ⟩ , _ ⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := g
    congr

instance : RingHomClass (A →ₜ+* B) A B where
  map_add f := f.map_add'
  map_zero f := f.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

instance instContinuousMapClass : ContinuousMapClass (A →ₜ+* B) A B where
  map_continuous f := f.continuous_toFun

def ContinuousRingHom.id (A : Type*) [Ring A] [TopologicalSpace A] [IsTopologicalRing A] :
    A →ₜ+* A := ⟨.id _, by fun_prop⟩

def ContinuousRingHom.comp {A B C : Type*}
    [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [Ring C] [TopologicalSpace C] [IsTopologicalRing C]
    (f : B →ₜ+* C) (g : A →ₜ+* B) : A →ₜ+* C :=
    ⟨f.toRingHom.comp g.toRingHom, (map_continuous f).comp (map_continuous g)⟩

end ContinuousRingHom

structure TopRingCat where
  private mk ::
  carrier : Type u
  [commRing : CommRing carrier]
  [top : TopologicalSpace carrier]
  [topRing : IsTopologicalRing carrier]

attribute [instance] TopRingCat.commRing TopRingCat.top TopRingCat.topRing

initialize_simps_projections TopRingCat (-commRing, -top, -topRing)

namespace TopRingCat

instance : CoeSort (TopRingCat) (Type u) :=
  ⟨TopRingCat.carrier⟩

attribute [coe] TopRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommRingCat`. -/
abbrev of (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] : TopRingCat :=
  ⟨R⟩

lemma coe_of (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    (of R : Type u) = R :=
  rfl

lemma of_carrier (R : TopRingCat.{u}) : of R = R := rfl

variable {R} in
@[ext]
structure Hom (R S : TopRingCat.{u}) where
  private mk ::
  hom' : R →ₜ+* S

instance : Category TopRingCat where
  Hom R S := Hom R S
  id R := ⟨ContinuousRingHom.id R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} TopRingCat (fun R S => R →ₜ+* S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

abbrev Hom.hom {R S : TopRingCat.{u}} (f : Hom R S) :=
  ConcreteCategory.hom (C := TopRingCat) f

abbrev ofHom {R S : Type u}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (f : R →ₜ+* S) : of R ⟶ of S :=
  ConcreteCategory.ofHom (C := TopRingCat) f

def Hom.Simps.hom (R S : TopRingCat) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

def uniformSpace (R : TopRingCat) : UniformSpace R := by
  exact IsTopologicalAddGroup.toUniformSpace _

instance : HasForget₂ TopRingCat CommRingCat where
  forget₂ := {
    obj X := CommRingCat.of X
    map f := CommRingCat.ofHom f.hom }

instance : HasForget₂ TopRingCat TopCat where
  forget₂ := {
    obj X := TopCat.of X
    map f := TopCat.ofHom f.hom }

section Limits

open Limits

universe v t w

instance : HasProducts.{u} TopRingCat.{u} := by
  refine hasProducts_of_limit_fans (fun {J} f ↦ Fan.mk
      (TopRingCat.of.{u} (∀ j, f j))
      (fun b ↦ ofHom ⟨Pi.evalRingHom _ b, (ContinuousMap.eval b).continuous_toFun⟩))
    (fun {J} f ↦ {
      lift c := ⟨Pi.ringHom fun b ↦ (ConcreteCategory.hom (c.π.app ⟨b⟩)).toRingHom, by
        apply continuous_pi
        intro b
        exact (ConcreteCategory.hom (c.π.app ⟨b⟩)).continuous_toFun⟩
      fac s _ := by rfl
      uniq s m h := by
        apply ConcreteCategory.hom_ext
        intro x
        apply funext
        intro y
        specialize h ⟨y⟩
        rw [ConcreteCategory.hom_ext_iff] at h
        exact h x })

def equalizerFork {X Y : TopRingCat.{u}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (TopRingCat.ofHom ⟨(RingHom.eqLocus f.hom.toRingHom g.hom.toRingHom).subtype,
    by continuity⟩) <| by
      apply ConcreteCategory.hom_ext
      intro ⟨x, e⟩
      simpa using e

/-- The equalizer in `CommRingCat` is the equalizer as sets. -/
def equalizerForkIsLimit {X Y : TopRingCat.{u}} (f g : X ⟶ Y) : IsLimit (equalizerFork f g) := by
  fapply Fork.IsLimit.mk'
  intro s
  use ofHom <| ⟨s.ι.hom.toRingHom.codRestrict _
    fun x => (ConcreteCategory.congr_hom s.condition x :), by
      simp only [RingHom.codRestrict, Functor.const_obj_obj, parallelPair_obj_zero,
        RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, OneHom.toFun_eq_coe, OneHom.coe_mk]
      apply Continuous.codRestrict
      exact ContinuousRingHom.continuous_toFun _⟩
  constructor
  · ext
    rfl
  · intro m hm
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    have := congrArg Hom.hom hm
    apply_fun ContinuousRingHom.toRingHom at this
    exact RingHom.congr_fun this x

instance {X Y : TopRingCat.{u}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  ⟨⟨equalizerFork f g, equalizerForkIsLimit f g⟩⟩

instance : HasEqualizers TopRingCat := by
  apply hasEqualizers_of_hasLimit_parallelPair

instance : HasLimits TopRingCat := has_limits_of_hasEqualizers_and_products

end Limits

end TopRingCat

end TopRingCat

section TopAlgCat

structure TopAlgCat (R : Type u) [CommRing R] where
  private mk ::
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  [top : TopologicalSpace carrier]
  [topRing : IsTopologicalRing carrier]

attribute [instance] TopAlgCat.commRing TopAlgCat.top TopAlgCat.topRing TopAlgCat.algebra

initialize_simps_projections TopAlgCat (-commRing, -algebra, -top, -topRing)

namespace TopAlgCat

variable (A : Type u) [CommRing A]

instance : CoeSort (TopAlgCat A) (Type u) :=
  ⟨TopAlgCat.carrier⟩

attribute [coe] TopRingCat.carrier

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. This is the preferred way to construct a term of `CommRingCat`. -/
abbrev of (R : Type u) [CommRing R] [Algebra A R] [TopologicalSpace R] [IsTopologicalRing R] :
    TopAlgCat A :=
  ⟨R⟩

lemma coe_of (R : Type u) [CommRing R] [Algebra A R] [TopologicalSpace R] [IsTopologicalRing R] :
    (of A R : Type u) = R :=
  rfl

lemma of_carrier (R : TopAlgCat.{u} A) : of A R = R := rfl

variable {A} in
@[ext]
structure Hom (R S : TopAlgCat.{u} A) where
  private mk ::
  hom' : R →A[A] S

instance : Category (TopAlgCat A) where
  Hom R S := Hom R S
  id R := ⟨ContinuousAlgHom.id A R⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance : ConcreteCategory.{u} (TopAlgCat A) (fun R S => R →A[A] S) where
  hom := Hom.hom'
  ofHom f := ⟨f⟩

abbrev Hom.hom {R S : TopAlgCat.{u} A} (f : Hom R S) :=
  ConcreteCategory.hom (C := TopAlgCat A) f

abbrev ofHom {R S : Type u}
    [CommRing R] [Algebra A R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [Algebra A S] [TopologicalSpace S] [IsTopologicalRing S] (f : R →A[A] S) :
    of A R ⟶ of A S :=
  ConcreteCategory.ofHom (C := TopAlgCat A) f

def Hom.Simps.hom (R S : TopAlgCat A) (f : Hom R S) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

open Limits

instance : HasForget₂ (TopAlgCat A) TopRingCat where
  forget₂ := {
    obj X := TopRingCat.of X
    map f := TopRingCat.ofHom ⟨f.hom.toRingHom, f.hom.cont⟩ }

end TopAlgCat

end TopAlgCat

open TopCat

def TopCat.Presheaf.forgetToRing {X : TopCat.{u}} (ℱ : X.Presheaf TopRingCat) :
    X.Presheaf CommRingCat :=
  ℱ ⋙ forget₂ TopRingCat CommRingCat

def spa (A : HuberPair) : Type u :=
  {v : Spv A // v.IsContinuous ∧ ∀ r : A.plus, v (algebraMap A.plus A r) ≤ 1}

instance {A : HuberPair} : CoeOut (spa A) (Spv A) := ⟨Subtype.val⟩

noncomputable instance {A : HuberPair} :
    CoeFun (spa A) (fun (v : spa A) ↦ (A → Spv.outΓ₀ (v : Spv A))) where
  coe v := ((v : Spv A).out : A → (v : Spv A).outΓ₀)

section TopologicalSpace

namespace spa

structure rationalOpenData (A : HuberPair) where
  s : A
  T : Finset A
  isOpen : IsOpen ((Ideal.span (T : Set A)) : Set A)

def rationalOpenData.openSet {A : HuberPair} (r : rationalOpenData A) : Set (spa A) :=
  {v | (∀ t ∈ r.T, (v t ≤ v r.s)) ∧ (v r.s ≠ 0)}

instance (A : HuberPair) : Preorder (rationalOpenData A) where
  le r s := r.openSet ⊆ s.openSet
  le_refl _ := by tauto_set
  le_trans := by tauto_set
  lt_iff_le_not_ge := by tauto_set

def rationalBasis (A : HuberPair) : Set (Set (spa A)) :=
  {U | ∃ r : rationalOpenData A, U = r.openSet}

instance (A : HuberPair) : TopologicalSpace (spa A) :=
  TopologicalSpace.generateFrom (spa.rationalBasis A)

lemma rationalOpenData.openSet_isOpen {A : HuberPair} (r : rationalOpenData A) :
    IsOpen r.openSet := by
  apply isOpen_generateFrom_of_mem
  simp [rationalBasis]

end spa

end TopologicalSpace

section Presheaf

namespace spa

end spa

def HuberRing.Away {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (_T : Set R) (s : R) : Type u := Localization.Away s

namespace HuberRing.Away

variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

instance (T : Set R) (s : R) : CommRing (HuberRing.Away T s) := by
  dsimp [HuberRing.Away]
  infer_instance

instance (T : Set R) (s : R) : Module R (HuberRing.Away T s) := by
  dsimp [HuberRing.Away]
  infer_instance

instance (T : Set R) (s : R) : Algebra R (HuberRing.Away T s) := by
  dsimp [HuberRing.Away]
  infer_instance

variable (T : Set R) (s : R)

end HuberRing.Away

namespace spa

variable {A : HuberPair.{u}} (r : rationalOpenData A)

def rationalOpenData.Localization := HuberRing.Away r.T r.s

def rationalOpenData.invSelf : r.Localization := Localization.Away.invSelf r.s

instance : CommRing r.Localization := by
  dsimp [rationalOpenData.Localization]
  infer_instance

instance : Algebra A r.Localization := by
  dsimp [rationalOpenData.Localization]
  infer_instance

def ringSubgroupsBasisFamily : OpenAddSubgroup A → AddSubgroup r.Localization :=
  let D : Subring r.Localization := Subring.closure
    ((fun x ↦ r.invSelf * x) '' (algebraMap A r.Localization '' (r.T : Set A)))
  fun U ↦ (Submodule.span (D : Type u) (algebraMap A r.Localization '' U)).toAddSubgroup

def ringSubgroupsBasis : RingSubgroupsBasis (ringSubgroupsBasisFamily r) where
  inter := by sorry
  mul := by sorry
  leftMul := by sorry
  rightMul := by sorry

instance : TopologicalSpace r.Localization :=
  (spa.ringSubgroupsBasis r).topology

instance : IsTopologicalRing r.Localization := inferInstance

instance : UniformSpace r.Localization :=
  IsTopologicalAddGroup.toUniformSpace r.Localization

instance : IsUniformAddGroup r.Localization :=
  isUniformAddGroup_of_addCommGroup

instance : UniformContinuousConstSMul A r.Localization where
  uniformContinuous_const_smul c := by
    let f : r.Localization →+ r.Localization := {
      toFun x := c • x
      map_zero' := by simp
      map_add' := by simp }
    change UniformContinuous f
    apply uniformContinuous_addMonoidHom_of_continuous
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, f, Algebra.smul_def]
    continuity

noncomputable
instance : CommRing (UniformSpace.Completion r.Localization) :=
  UniformSpace.Completion.commRing _

noncomputable
instance : Algebra A (UniformSpace.Completion r.Localization) :=
  UniformSpace.Completion.algebra _ _

instance : IsTopologicalRing (UniformSpace.Completion r.Localization) :=
  inferInstance

open UniformSpace

lemma rationalOpenData.le_iff_exists_unique {A : HuberPair} (r s : rationalOpenData A) :
    r ≤ s ↔ Nonempty (Unique (Completion s.Localization →A[A] Completion r.Localization)) := by
  sorry

noncomputable def rationalOpenData.uniqueOfLE
    {A : HuberPair} (r s : rationalOpenData A) (h : r ≤ s) :
    Unique (Completion s.Localization →A[A] Completion r.Localization) :=
  ((rationalOpenData.le_iff_exists_unique r s).mp h).some

attribute [-instance] UniformSpace.Completion.ring

noncomputable def rationalOpenData.topAlgHomOfLE
    {A : HuberPair} (r s : rationalOpenData A) (h : r ≤ s) :
    Completion s.Localization →A[A] Completion r.Localization :=
  letI := uniqueOfLE r s h
  default

lemma rationalOpenData.topAlgHom_eq {A : HuberPair} (r s : rationalOpenData A) (h : r ≤ s)
    (f : Completion s.Localization →A[A] Completion r.Localization) :
    rationalOpenData.topAlgHomOfLE r s h = f := by
  letI := uniqueOfLE r s h
  exact Subsingleton.elim _ _

end spa

open UniformSpace

noncomputable def spa.presheafOnRationalOpenDataAlg (A : HuberPair) :
    (rationalOpenData A)ᵒᵖ ⥤  TopAlgCat A where
  obj r := TopAlgCat.of A (Completion r.unop.Localization)
  map h := TopAlgCat.ofHom A (rationalOpenData.topAlgHomOfLE _ _ h.unop.1.1)
  map_id _ := by
    apply ConcreteCategory.ext
    apply rationalOpenData.topAlgHom_eq
  map_comp _ _ := by
    apply ConcreteCategory.ext
    apply rationalOpenData.topAlgHom_eq

noncomputable def spa.presheafOnRationalOpenData (A : HuberPair) :
    (rationalOpenData A)ᵒᵖ ⥤  TopRingCat :=
  presheafOnRationalOpenDataAlg A ⋙ forget₂ _ _

def spa.rationalOpenDataToOpens (A : HuberPair) : rationalOpenData A ⥤ Opens (spa A) where
  obj r := ⟨r.openSet, r.openSet_isOpen⟩
  map h := h

noncomputable def spa.presheaf (A : HuberPair.{u}) : Presheaf TopRingCat.{u} (of (spa A)) :=
  (rationalOpenDataToOpens A).op.pointwiseRightKanExtension (spa.presheafOnRationalOpenData A)

end Presheaf

section Valuation

def spa.stalk_valuation (A : HuberPair) (x : of (spa A)) :
    Spv (((spa.presheaf A).forgetToRing).stalk x) :=
  sorry

end Valuation

open AlgebraicGeometry Opposite

structure PreValuedRingedSpace extends PresheafedSpace TopRingCat where
  valuation : ∀ x : carrier, Spv (presheaf.forgetToRing.stalk x)

def PreValuedRingedSpace.forgetToRing (X : PreValuedRingedSpace.{u}) :
    PresheafedSpace CommRingCat.{u} :=
  (forget₂ TopRingCat CommRingCat).mapPresheaf.obj X.toPresheafedSpace

instance PreValuedRingedSpace.coeCarrier :
    CoeOut PreValuedRingedSpace TopCat where coe X :=
  X.carrier

instance PreValuedRingedSpace.coeSort : CoeSort PreValuedRingedSpace Type* where
  coe X := X.1

def PreValuedRingedSpace.toTopCat (X : PreValuedRingedSpace.{u}) : TopCat.{u} :=
  of X

instance : Category.{u} PreValuedRingedSpace.{u} :=
  InducedCategory.category PreValuedRingedSpace.toPresheafedSpace

attribute [local instance] TopRingCat.uniformSpace

instance (X : TopCat) (P : TopCat.Presheaf TopRingCat X) (U : Opens X) :
    TopologicalSpace (P.forgetToRing.obj (op U)) :=
  inferInstanceAs (TopologicalSpace (P.obj (op U)))

structure PreLVCRS extends PresheafedSpace TopRingCat where
  complete (U : Opens carrier) : CompleteSpace (presheaf.obj (op U))
  isLocalRing (x : carrier) : presheaf.forgetToRing.stalk x
  valuation (x : carrier) : Spv (presheaf.forgetToRing.stalk x)
  valuation_continuous (U : Opens carrier) (x : carrier) (hx : x ∈ U) :
    ((valuation x).comap (presheaf.forgetToRing.germ U x hx).hom').IsContinuous
  supp_maximal (x : carrier) : Ideal.IsMaximal (valuation x).out.supp

instance PreLVCRS.coeCarrier :
    CoeOut PreLVCRS TopCat where coe X :=
  X.carrier

instance PreLVCRS.coeSort : CoeSort PreLVCRS Type* where
  coe X := X.1

structure LVCRS extends SheafedSpace TopRingCat where
  complete (U : Opens carrier) : CompleteSpace (presheaf.obj (op U))
  isLocalRing (x : carrier) : presheaf.forgetToRing.stalk x
  valuation (x : carrier) : Spv (presheaf.forgetToRing.stalk x)
  valuation_continuous (U : Opens carrier) (x : carrier) (hx : x ∈ U) :
    ((valuation x).comap (presheaf.forgetToRing.germ U x hx).hom').IsContinuous
  supp_maximal (x : carrier) : Ideal.IsMaximal (valuation x).out.supp

def LVCRS.toPreLVCRS (X : LVCRS.{u}) : PreLVCRS.{u} where
  toPresheafedSpace := X.toPresheafedSpace
  valuation := X.valuation
  supp_maximal := X.supp_maximal
  complete := X.complete
  valuation_continuous := X.valuation_continuous
  isLocalRing := X.isLocalRing

instance LVCRS.coeCarrier :
    CoeOut LVCRS TopCat where coe X :=
  X.carrier

instance LVCRS.coeSort : CoeSort LVCRS Type* where
  coe X := X.1

def LVCRS.toPreValuedRingedSpace (X : LVCRS.{u}) : PreValuedRingedSpace.{u} where
  toPresheafedSpace := X.toPresheafedSpace
  valuation := X.valuation

noncomputable def PreValuedRingedSpace.restrictStalkMap {U : TopCat.{u}}
    (X : PreValuedRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) (x : U) :
    X.toPresheafedSpace.presheaf.forgetToRing.stalk (f x) ⟶
    (X.toPresheafedSpace.restrict h).presheaf.forgetToRing.stalk x :=
  (PresheafedSpace.Hom.stalkMap (PresheafedSpace.ofRestrict X.forgetToRing h) x)

noncomputable def PreValuedRingedSpace.restrictStalkMapInv {U : TopCat.{u}}
    (X : PreValuedRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) (x : U) :
    (X.toPresheafedSpace.restrict h).presheaf.forgetToRing.stalk x ⟶
      X.toPresheafedSpace.presheaf.forgetToRing.stalk (f x) :=
  inv (PresheafedSpace.Hom.stalkMap (PresheafedSpace.ofRestrict X.forgetToRing h) x)

def PreValuedRingedSpace.restrict {U : TopCat.{u}} (X : PreValuedRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) : PreValuedRingedSpace where
  toPresheafedSpace := X.toPresheafedSpace.restrict h
  valuation x := by
    refine ValuativeRel.ofValuation ((X.valuation (f x)).valuation.comap ?_)
    exact ConcreteCategory.hom (X.restrictStalkMapInv h x)

def PreLVCRS.restrict {U : TopCat.{u}} (X : PreLVCRS.{u})
    {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f) : PreLVCRS where
  toPresheafedSpace := X.toPresheafedSpace.restrict h
  complete := sorry
  isLocalRing := sorry
  valuation := sorry
  valuation_continuous := sorry
  supp_maximal := sorry
  -- valuation x := by
  --   refine ValuativeRel.ofValuation ((X.valuation (f x)).valuation.comap ?_)
  --   exact ConcreteCategory.hom (X.restrictStalkMapInv h x)

noncomputable def Spa (A : HuberPair.{u}) : PreLVCRS.{u} where
  carrier := of (spa A)
  presheaf := spa.presheaf A
  complete := sorry
  isLocalRing := sorry
  valuation := spa.stalk_valuation A
  valuation_continuous := sorry
  supp_maximal := sorry

open TopologicalSpace

noncomputable def PreLVCRS.Hom.stalkMap {X Y : PreLVCRS.{u}}
    (f : X.toPresheafedSpace ⟶ Y.toPresheafedSpace) (x : X) :=
  PresheafedSpace.Hom.stalkMap
    ((Functor.mapPresheaf (forget₂ TopRingCat.{u} CommRingCat.{u})).map f) x

structure PreLVCRS.Hom (X Y : PreLVCRS.{u}) where
  hom : X.toPresheafedSpace ⟶ Y.toPresheafedSpace
  -- isLocal (x : X) : IsLocalHom (PreLVCRS.Hom.stalkMap hom x).hom'
  -- follows from `valuedCondition`
  valuativeCondition (x : X) : (X.valuation x).comap (PreLVCRS.Hom.stalkMap hom x).hom' =
    (Y.valuation (hom.base x))

@[simps]
def PreLVCRS.Hom.id (X : PreLVCRS.{u}) : PreLVCRS.Hom X X where
  hom := 𝟙 _
  valuativeCondition x := by
    dsimp [stalkMap]
    erw [AlgebraicGeometry.PresheafedSpace.stalkMap.id]
    rfl

@[simps]
def PreLVCRS.Hom.comp {X Y Z : PreLVCRS.{u}} (f : PreLVCRS.Hom X Y) (g : PreLVCRS.Hom Y Z) :
    PreLVCRS.Hom X Z where
  hom := f.hom ≫ g.hom
  valuativeCondition x := by
    sorry

-- def PreLVCRS.Hom.c {X Y : PreLVCRS.{u}} (f : PreLVCRS.Hom X Y) :

instance : Category.{u} PreLVCRS.{u} where
  Hom := PreLVCRS.Hom
  id := PreLVCRS.Hom.id
  comp := PreLVCRS.Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

def LVCRS.IsAdicSpace (X : LVCRS.{u}) : Prop :=
  ∀ x : X, ∃ (U : OpenNhds x) (A : HuberPair.{u}),
    (Nonempty (Spa.{u} A ≅ (X.toPreLVCRS.restrict U.isOpenEmbedding)))

structure AdicSpace extends LVCRS where
  isAdic : toLVCRS.IsAdicSpace

namespace AdicSpace

@[ext]
structure Hom (X Y : AdicSpace.{u}) extends
    PreLVCRS.Hom X.toPreLVCRS Y.toPreLVCRS where

def Hom.comp {X Y Z : AdicSpace.{u}} (f : X.Hom Y) (g : Y.Hom Z) : X.Hom Z where
  __ := PreLVCRS.Hom.comp f.1 g.1

def Hom.id (X : AdicSpace.{u}) : X.Hom X where
  __ := PreLVCRS.Hom.id X.toPreLVCRS

instance : Category.{u} AdicSpace.{u} where
  Hom := AdicSpace.Hom
  id := Hom.id
  comp := Hom.comp

def forgetToPreLVCRS : AdicSpace.{u} ⥤ PreLVCRS.{u} where
  obj X := X.toPreLVCRS
  map {X Y} f := f.1

def PreLVCRS.forgetToPresheafedSpace : PreLVCRS.{u} ⥤ PresheafedSpace TopRingCat.{u} where
  obj X := X.toPresheafedSpace
  map f := f.hom

def forgetToPresheafedSpace : AdicSpace.{u} ⥤ PresheafedSpace TopRingCat.{u} :=
  forgetToPreLVCRS ⋙ PreLVCRS.forgetToPresheafedSpace

abbrev PreLVCRS.IsOpenImmersion : MorphismProperty PreLVCRS := fun _ _ f ↦
  PresheafedSpace.IsOpenImmersion (PreLVCRS.forgetToPresheafedSpace.map f)

abbrev IsOpenImmersion : MorphismProperty AdicSpace := fun _ _ f ↦
  PreLVCRS.IsOpenImmersion (forgetToPreLVCRS.map f)

def Hom.base {X Y : AdicSpace.{u}} (f : X ⟶ Y) : X.1.carrier ⟶ Y.1.carrier :=
  f.1.1.1

instance : CoeSort AdicSpace.{u} (Type u) where
  coe X := X.1.1

abbrev Opens (X : AdicSpace.{u}) := TopologicalSpace.Opens X.1

scoped[AdicSpace] notation3 "Γ(" X ", " U ")" =>
  (PresheafedSpace.presheaf (PreLVCRS.toPresheafedSpace
    (LVCRS.toPreLVCRS (AdicSpace.toLVCRS X)))).obj
    (op (α := AdicSpace.Opens _) U)

variable {X Y : AdicSpace.{u}}

def Opens.adicSpace (U : X.Opens) : AdicSpace.{u} :=
  sorry

instance : CoeOut X.Opens AdicSpace.{u} where
  coe U := U.adicSpace

def Opens.ι (U : X.Opens) : (U : AdicSpace.{u}) ⟶ X :=
  sorry

def Opens.preimage (f : X ⟶ Y) (U : Y.Opens) : X.Opens :=
  U.comap f.hom.base.1

def Hom.restrict (f : X ⟶ Y) (U : Y.Opens) : (U.preimage f : AdicSpace.{u}) ⟶ U :=
  sorry

@[reassoc (attr := simp)]
lemma Hom.restrict_ι (f : X ⟶ Y) (U : Y.Opens) :
    f.restrict U ≫ U.ι = (U.preimage f).ι ≫ f :=
  sorry

end AdicSpace

open CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type*} [Category C]
variable {D : Type*} [Category D]

def mapSheaf (F : C ⥤ D)
    [∀ X : SheafedSpace C, (Opens.grothendieckTopology X).HasSheafCompose F] :
    SheafedSpace C ⥤ SheafedSpace D where
  obj X :=
    { carrier := X.carrier
      presheaf := X.presheaf ⋙ F
      IsSheaf := GrothendieckTopology.HasSheafCompose.isSheaf _ X.IsSheaf }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  map_id X := by
    ext U
    · rfl
    · simp
  map_comp f g := by
    ext U
    · rfl
    · simp

variable (F : C ⥤ D) [∀ X : SheafedSpace C, (Opens.grothendieckTopology X).HasSheafCompose F]

@[simp]
theorem mapSheaf_obj_X (X : SheafedSpace C) :
    (F.mapSheaf.obj X : TopCat) = (X : TopCat) :=
  rfl

@[simp]
theorem mapSheaf_obj_presheaf (X : SheafedSpace C) :
    (F.mapSheaf.obj X).presheaf = X.presheaf ⋙ F :=
  rfl

@[simp]
theorem mapSheaf_map_f {X Y : SheafedSpace C} (f : X ⟶ Y) :
    (F.mapSheaf.map f).base = f.base :=
  rfl

@[simp]
theorem mapSheaf_map_c {X Y : SheafedSpace C} (f : X ⟶ Y) :
    (F.mapSheaf.map f).c = whiskerRight f.c F :=
  rfl

end Functor

end CategoryTheory
