import Mathlib.CategoryTheory.GaloisCategories.EssSurj
import Mathlib.CategoryTheory.GaloisCategories.ContAction
import Mathlib.Topology.Algebra.OpenSubgroup

universe u v w

open CategoryTheory Limits Functor

namespace Galois

variable {C : Type u} [Category.{u, u} C] (F : C ⥤ FintypeCat.{u})
  [PreGaloisCategory C] [FibreFunctor F]

instance (X : Action FintypeCat (MonCat.of (Aut F))) : TopologicalSpace X.V := ⊥

lemma stabilizer_open' (X : Action FintypeCat (MonCat.of (Aut F)))
    [ContinuousSMul (Aut F) X.V] (x : X.V) :
    IsOpen (MulAction.stabilizer (Aut F) x : Set (Aut F)) := by
  let q (g : Aut F) : Aut F × X.V := (g, x)
  have : Continuous q := by
    continuity
  let h (p : Aut F × X.V) : X.V := p.1 • p.2
  have : Continuous h := continuous_smul
  let p (g : Aut F) : X.V := g • x
  have : p ⁻¹' {x} = MulAction.stabilizer (Aut F) x := rfl
  rw [←this]
  apply IsOpen.preimage
  show Continuous (h ∘ q)
  apply Continuous.comp
  assumption
  assumption
  trivial

instance (H : Subgroup (Aut F)) : MulAction (Aut F) (Aut F ⧸ H) := inferInstance

lemma connected_as_quotient (X : Action FintypeCat (MonCat.of (Aut F))) [ConnectedObject X]
    [ContinuousSMul (Aut F) X.V] :
    ∃ (U : OpenSubgroup (Aut F)),
    Nonempty (X ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) := by
  have : Nonempty ((forget₂ _ FintypeCat).obj X) := nonempty_fibre_of_connected X
  obtain ⟨x : X.V⟩ := this
  have : MulAction.IsPretransitive (Aut F) X.V :=
    Action.pretransitive_of_connected (Aut F) X
  let e : X.V ≃ Aut F ⧸ MulAction.stabilizer (Aut F) x := by
    trans
    exact (Equiv.Set.univ X.V).symm
    trans
    apply Equiv.setCongr
    exact (MulAction.orbit_eq_univ (Aut F) x).symm
    exact MulAction.orbitEquivQuotientStabilizer (Aut F) x
  let U : OpenSubgroup (Aut F) := ⟨MulAction.stabilizer (Aut F) x, stabilizer_open' F X x⟩
  use U
  let inst : Fintype (Aut F ⧸ U.toSubgroup) := fintypeQuotient F U
  let u : Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup) ≅ X := by
    apply Action.mkIso
    swap
    exact (FintypeCat.equivEquivIso e.symm)
    intro (σ : Aut F)
    ext (a : Aut F ⧸ MulAction.stabilizer (Aut F) x)
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep a
    rw [←hτ]
    show ((MulAction.orbitEquivQuotientStabilizer (Aut F) x).symm ⟦σ * τ⟧) =
      X.ρ σ ((MulAction.orbitEquivQuotientStabilizer (Aut F) x).symm ⟦τ⟧)
    erw [MulAction.orbitEquivQuotientStabilizer_symm_apply,
      MulAction.orbitEquivQuotientStabilizer_symm_apply]
    rw [←smul_smul]
    rfl
  constructor
  exact u.symm

lemma decomp_sum_quotients (X : Action FintypeCat (MonCat.of (Aut F)))
    [ContinuousSMul (Aut F) X.V] :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → OpenSubgroup (Aut F))
    (_ : (∐ fun i => Action.ofMulAction' (Aut F) (Aut F ⧸ (f i).toSubgroup)) ≅ X), True := by
  obtain ⟨ι, hf, f, u, hc⟩ := hasDecompConnectedComponents' (forget₂ _ FintypeCat) X
  use ι
  use hf
  have (i : ι) : ContinuousSMul (Aut F) (f i).V := by
    constructor
    let r : f i ⟶ X := Sigma.ι f i ≫ u.hom
    have : Mono (Sigma.ι f i) := by
      have : Fintype ι := Fintype.ofFinite ι
      exact mono_coprod_inclusion (forget₂ _ FintypeCat)
        ⟨colimit.cocone (Discrete.functor f), colimit.isColimit _⟩ i
    have : Mono r := by
      apply mono_comp
    let r' : (f i).V → X.V := r.hom
    let r'' (p : Aut F × (f i).V) : Aut F × X.V := (p.1, r' p.2)
    have : Continuous r'' := by
      continuity
    let q (p : Aut F × X.V) : X.V := X.ρ p.1 p.2
    let q' (p : Aut F × (f i).V) : (f i).V := (f i).ρ p.1 p.2
    have heq : q ∘ r'' = r' ∘ q' := by
      ext (p : Aut F × (f i).V)
      show (r.hom ≫ X.ρ p.1) p.2 = ((f i).ρ p.1 ≫ r.hom) p.2
      rw [r.comm]
    have : Function.Injective r' := by
      apply (@monomorphismIffInducesInjective _ _ (forget₂ _ FintypeCat) _ _ _ _ r).mp
      apply mono_comp
    have : Continuous q := continuous_smul
    have : Continuous r'' := by continuity
    have : Continuous r' := by continuity
    let t₁ : TopologicalSpace (Aut F × (f i).V) := inferInstance
    let t₂ : TopologicalSpace (f i).V := ⊥
    let t₃ : TopologicalSpace (f i).V := TopologicalSpace.induced r' ⊥
    show @Continuous _ _ t₁ t₂ q'
    have : t₃ = t₂ := by
      show t₃ = ⊥
      have : t₃ ≤ ⊥ := by
        intro s _
        use r' '' s
        constructor
        trivial
        apply Set.preimage_image_eq s
        assumption
      exact le_bot_iff.mp this
    rw [←this]
    have : Continuous (r' ∘ q') := by
      rw [←heq]
      apply Continuous.comp
      assumption
      assumption
    exact continuous_induced_rng.mpr this
  have (i : ι) : ∃ (U : OpenSubgroup (Aut F))
    (_ : (f i) ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)), True := by
    obtain ⟨U, ⟨u⟩⟩ := connected_as_quotient F (f i)
    use U
    use u
  choose g ui _ using this
  use g
  use (Sigma.mapIso ui).symm ≪≫ u

instance : PreservesFiniteCoproducts (H F) := by
  constructor
  intro ι _
  have : PreservesColimitsOfShape (Discrete ι) (H F ⋙ forget₂ _ FintypeCat) := by
    show PreservesColimitsOfShape (Discrete ι) F
    infer_instance
  exact Action.preservesColimitOfShapeOfPreserves FintypeCat (MonCat.of (Aut F)) (H F) this

lemma ess_surj_of_cont (X : Action FintypeCat (MonCat.of (Aut F)))
    [ContinuousSMul (Aut F) X.V] : ∃ A : C, Nonempty ((H F).obj A ≅ X) := by
  obtain ⟨ι, hfin, f, u, _⟩ := decomp_sum_quotients F X
  have (i : ι) :
    ∃ (A : C)
    (_ : (H F).obj A ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ (f i).toSubgroup)),
    True := by
      obtain ⟨X, ⟨v⟩⟩ := ess_surj_of_quotient_by_open F (f i)
      use X
      use v
  choose g gu _ using this
  let v : (∐ fun i => (H F).obj (g i)) ≅
      ∐ fun i => Action.ofMulAction' (Aut F) (Aut F ⧸ (f i).toSubgroup) :=
    Sigma.mapIso gu
  let A : C := ∐ g
  use A
  have : Fintype ι := Fintype.ofFinite ι
  let i : (H F).obj A ≅ ∐ fun i => (H F).obj (g i) := PreservesCoproduct.iso (H F) g
  constructor
  exact i ≪≫ v ≪≫ u

instance (X : Action FintypeCat (MonCat.of (Aut F))) :
    TopologicalSpace ((forget FintypeCat).obj X.V) := by
  show TopologicalSpace X.V
  infer_instance

instance : TopologicalSpace (MonCat.of (Aut F)) := by
  show TopologicalSpace (Aut F)
  infer_instance

def Hc : C ⥤ ContAction FintypeCat (MonCat.of (Aut F)) := by
  apply FullSubcategory.lift
  swap
  exact H F
  intro X
  show ContinuousSMul (Aut F) (F.obj X)
  infer_instance

instance : Faithful (Hc F) := by apply instFaithfulFullSubcategoryCategoryLift

noncomputable instance : Full (Hc F) := by apply instFullFullSubcategoryCategoryLift

instance : EssSurj (Hc F) := by
  constructor
  intro ⟨X, hc⟩
  have : ContinuousSMul (Aut F) X.V := hc
  let G : ContAction FintypeCat (MonCat.of (Aut F)) ⥤ Action FintypeCat (MonCat.of (Aut F)) :=
    fullSubcategoryInclusion (cont FintypeCat (MonCat.of (Aut F)))
  have : Full G := FullSubcategory.full (cont _ _)
  have : Faithful G := FullSubcategory.faithful (cont _ _)
  have : Hc F ⋙ G = H F := rfl
  obtain ⟨A, ⟨u : G.obj ((Hc F).obj A) ≅ G.obj ⟨X, hc⟩⟩⟩ := ess_surj_of_cont F X
  use A
  constructor
  exact preimageIso G u

noncomputable instance fibreFunctorInducesEquivalence :
    IsEquivalence (Hc F) :=
  Equivalence.ofFullyFaithfullyEssSurj (Hc F)

#print axioms fibreFunctorInducesEquivalence
