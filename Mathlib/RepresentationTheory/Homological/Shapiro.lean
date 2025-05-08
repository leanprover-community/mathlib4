import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Coinvariants

set_option trace.profiler true

universe v u
open Finsupp
namespace Representation

variable (k : Type*) (G : Type*)

noncomputable abbrev rightRegular [CommSemiring k] [Group G] : Representation k G (G →₀ k) :=
  (ofMulAction k Gᵐᵒᵖ G).comp (MulEquiv.inv' G)

section idfk
section
variable {k G H : Type*} [CommSemiring k] [Group G] [Group H]
  (φ : G →* H) {α A B : Type*}
  [AddCommMonoid A] [Module k A] (ρ : Representation k G A)
  [AddCommMonoid B] [Module k B] (τ : Representation k G B)

abbrev res (f : G →* H) (ρ : Representation k H A) : Representation k G A := ρ.comp f

@[simps]
def idfk : Submodule k (H → A) where
  carrier := {f : H → A | ∀ (g : G) (h : H), f (φ g * h) = ρ g (f h) }
  add_mem' _ _ _ _ := by simp_all
  zero_mem' := by simp
  smul_mem' _ _ _ := by simp_all

@[simps]
def coind : Representation k H (idfk φ ρ) where
  toFun h := (LinearMap.funLeft _ _ (· * h)).restrict fun x hx g h₁ => by
    simpa [mul_assoc] using hx g (h₁ * h)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp [mul_assoc]

end

variable {k G H : Type*} [CommRing k] [Group G] [Group H] {α A B : Type*} (φ : G →* H)
  [AddCommGroup A] [Module k A] (ρ : Representation k G A)
  [AddCommGroup B] [Module k B] (τ : Representation k G B)

abbrev indV := coinvariants (V := TensorProduct k (H →₀ k) A)
  (Representation.tprod ((leftRegular k H).comp φ) ρ)

noncomputable abbrev indMk (h : H) : A →ₗ[k] indV φ ρ :=
  coinvariantsMk _ ∘ₗ TensorProduct.mk k _ _ (single h 1)
/-
@[simp]
lemma indMk_apply (h : H) (a : A) :
    indMk φ ρ h a = coinvariantsMk _ (single h 1 ⊗ₜ[k] a) := by
  rfl
-/
@[ext]
lemma indV_hom_ext {f g : indV φ ρ →ₗ[k] B}
    (hfg : ∀ h : H, f ∘ₗ indMk φ ρ h = g ∘ₗ indMk φ ρ h) : f = g :=
  coinvariants_hom_ext <| TensorProduct.ext <| Finsupp.lhom_ext' fun h =>
    LinearMap.ext_ring <| hfg h

@[simps]
noncomputable def ind : Representation k H (indV φ ρ) where
  toFun h := coinvariantsMap _ _ ((lmapDomain k k fun x => x * h⁻¹).rTensor _)
    fun _ => by ext; simp [mul_assoc]
  map_one' := by ext; simp [indV, indMk]
  map_mul' _ _ := by ext; simp [indV, indMk, mul_assoc]

lemma ind_indMk (h₁ h₂ : H) (a : A) :
    ind φ ρ h₁ (indMk _ _ h₂ a) = indMk _ _ (h₂ * h₁⁻¹) a := by
  simp

end idfk
end Representation
open CategoryTheory
namespace Rep

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (φ : G →* H) (A : Rep k G)

@[simps]
noncomputable def coind2Aux :
    Representation k H ((Action.res _ φ).obj (leftRegular k H) ⟶ A) where
  toFun h := {
    toFun f := (Action.res _ φ).map ((leftRegularHomEquiv (leftRegular k H)).symm (single h 1)) ≫ f
    map_add' _ _ := by rfl
    map_smul' _ _ := by rfl }
  map_one' := by
    ext x : 3
    refine lhom_ext' fun _ => LinearMap.ext_ring ?_
    simp [leftRegularHomEquiv_symm_apply (leftRegular k H)]
  map_mul' _ _ := by
    ext x : 3
    refine lhom_ext' fun _ => LinearMap.ext_ring ?_
    simp [leftRegularHomEquiv_symm_apply (leftRegular k H), mul_assoc]

noncomputable abbrev coind2 : Rep k H := Rep.of (coind2Aux φ A)

noncomputable abbrev coind : Rep k H := Rep.of (A.ρ.coind φ)

@[ext]
lemma coind2_ext {A : Rep k G} {f g : coind2 φ A}
    (hfg : ∀ h, f.hom (single h 1) = g.hom (single h 1)) : f = g :=
  Action.Hom.ext <| ModuleCat.hom_ext <| lhom_ext' fun h => LinearMap.ext_ring <| hfg h

@[simps]
noncomputable def coindVIso : A.ρ.idfk φ ≃ₗ[k] ((Action.res _ φ).obj (leftRegular k H) ⟶ A) where
  toFun f := {
    hom := ModuleCat.ofHom <| linearCombination _ f.1
    comm g := ModuleCat.hom_ext <| lhom_ext' fun _ => LinearMap.ext_ring <| by
      simp [ModuleCat.endRingEquiv, f.2 g] }
  map_add' _ _ := coind2_ext φ fun _ => by simp
  map_smul' _ _ := coind2_ext φ fun _ => by simp
  invFun f := {
    val h := f.hom (single h 1)
    property g h := by have := (hom_comm_apply f g (single h 1)).symm; simp_all [Rep.res_obj_ρ φ] }
  left_inv x := by simp
  right_inv x := coind2_ext φ fun _ => by simp

@[simps! hom_hom_hom inv_hom_hom]
noncomputable def coindIso : coind φ A ≅ coind2 φ A :=
  Action.mkIso (coindVIso φ A).toModuleIso fun h => by
    ext
    simp [ModuleCat.endRingEquiv, leftRegularHomEquiv_symm_apply (leftRegular k H)]

noncomputable abbrev ind : Rep k H := Rep.of (A.ρ.ind φ)

variable {A : Rep k G} {B : Rep k H} {f g : ind φ A ⟶ B} (h : H)

open CategoryTheory

@[simps]
noncomputable def coindMap {A B : Rep k G} (f : A ⟶ B) : coind φ A ⟶ coind φ B where
  hom := ModuleCat.ofHom <| (f.hom.hom.compLeft H).restrict
    fun x h y z => by simp [h y z, hom_comm_apply]
  comm _ := by ext; simp [ModuleCat.endRingEquiv]

@[simps]
noncomputable def coind2Map {A B : Rep k G} (f : A ⟶ B) : coind2 φ A ⟶ coind2 φ B where
  hom := ModuleCat.ofHom <| Linear.rightComp k _ f
  comm h := by ext; simp [ModuleCat.endRingEquiv]

@[simps]
noncomputable def indMap {A B : Rep k G} (f : A ⟶ B) : ind φ A ⟶ ind φ B where
  hom := ModuleCat.ofHom <| Representation.coinvariantsMap _ _
    (LinearMap.lTensor (H →₀ k) f.hom.hom) fun g => by ext; simp [hom_comm_apply]
  comm _ := by
    ext
    simp [ModuleCat.endRingEquiv]

open CategoryTheory

variable (k) in
@[simps obj map]
noncomputable def coindFunctor : Rep k G ⥤ Rep k H where
  obj A := coind φ A
  map f := coindMap φ f

variable (k) in
@[simps obj map]
noncomputable def coind2Functor : Rep k G ⥤ Rep k H where
  obj A := coind2 φ A
  map f := coind2Map φ f

@[simps!]
noncomputable def coindFunctorIso : coindFunctor k φ ≅ coind2Functor k φ :=
  NatIso.ofComponents (coindIso φ) fun _ => by
    simp only [coindFunctor_obj, coind2Functor_obj]
    ext
    simp

variable (k) in
@[simps obj map]
noncomputable abbrev indFunctor : Rep k G ⥤ Rep k H where
  obj A := ind φ A
  map f := indMap φ f
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simps]
noncomputable def resCoindHomLEquiv (B : Rep k H) (A : Rep k G) :
    ((Action.res _ φ).obj B ⟶ A) ≃ₗ[k] (B ⟶ coind φ A) where
  toFun f := {
    hom := ModuleCat.ofHom <| (LinearMap.pi fun h => f.hom.hom ∘ₗ Rep.ρ B h).codRestrict _
      fun _ _ _ => by simpa using hom_comm_apply f _ _
    comm _ := by ext; simp [ModuleCat.endRingEquiv] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := {
    hom := ModuleCat.ofHom (LinearMap.proj 1 ∘ₗ ((Rep.ρ A).idfk φ).subtype ∘ₗ f.hom.hom)
    comm g := by
      ext x
      have := ((f.hom x).2 g 1).symm
      have := hom_comm_apply f (φ g) x
      simp_all }
  left_inv := by intro; ext; simp
  right_inv z := by ext; have := hom_comm_apply z; simp_all

variable (k) in
@[simps! counit_app_hom_hom unit_app_hom_hom]
noncomputable abbrev resCoindAdjunction : Action.res _ φ ⊣ coindFunctor k φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv X Y := (resCoindHomLEquiv φ X Y).toEquiv
    homEquiv_naturality_left_symm := by intros; rfl
    homEquiv_naturality_right := by intros; ext; rfl }

noncomputable instance : Limits.PreservesLimits (coindFunctor k φ) :=
  (resCoindAdjunction k φ).rightAdjoint_preservesLimits

noncomputable instance : Limits.PreservesColimits (Action.res (ModuleCat k) φ) :=
  (resCoindAdjunction k φ).leftAdjoint_preservesColimits

open Representation

variable (A) (B : Rep k H)

@[simps]
noncomputable def indResHomLEquiv :
    (ind φ A ⟶ B) ≃ₗ[k] (A ⟶ (Action.res _ φ).obj B) where
  toFun f := {
    hom := ModuleCat.ofHom (f.hom.hom ∘ₗ indMk φ A.ρ 1)
    comm g := by
      ext x
      have := (hom_comm_apply f (φ g) (indMk φ A.ρ 1 x)).symm
      simp_all [← coinvariantsMk_inv_tmul] }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := {
    hom := ModuleCat.ofHom <| Representation.coinvariantsLift _ (TensorProduct.lift <|
      lift _ _ _ fun h => B.ρ h⁻¹ ∘ₗ f.hom.hom) fun _ => by ext; have := hom_comm_apply f; simp_all
    comm h := by ext; simp [ModuleCat.endRingEquiv] }
  left_inv f := by
    ext h a
    simpa using (hom_comm_apply f h⁻¹ (indMk φ A.ρ 1 a)).symm
  right_inv _ := by ext; simp

set_option maxHeartbeats 0 in
variable (k) in
open TensorProduct in
@[simps! unit_app_hom_hom counit_app_hom_hom]
noncomputable abbrev indResAdjunction : indFunctor k φ ⊣ Action.res _ φ :=
  Adjunction.mkOfHomEquiv {
    homEquiv A B := (indResHomLEquiv φ A B).toEquiv
    homEquiv_naturality_left_symm _ _ := by ext; simp
    homEquiv_naturality_right := by intros; rfl }

open Finsupp

noncomputable instance : Limits.PreservesColimits (indFunctor k φ) :=
  (indResAdjunction k φ).leftAdjoint_preservesColimits

noncomputable instance : Limits.PreservesLimits (Action.res (ModuleCat k) φ) :=
  (indResAdjunction k φ).rightAdjoint_preservesLimits

variable {S : Subgroup G} [DecidableRel (QuotientGroup.rightRel S)]

noncomputable def indToCoindAux (A : Rep k S) (g : G) : A →ₗ[k] (G → A) :=
  LinearMap.pi (fun g₁ => if h : (QuotientGroup.rightRel S).r g₁ g then
    A.ρ ⟨g₁ * g⁻¹, by rcases h with ⟨s, rfl⟩; exact mul_inv_cancel_right s.1 g ▸ s.2⟩ else 0)

@[simp]
lemma indToCoindAux_self {A : Rep k S} (g : G) (a : A) :
    indToCoindAux A g a g = a := by
  rw [indToCoindAux, LinearMap.pi_apply, dif_pos]
  · simp [← S.1.one_def]
  · rfl

lemma indToCoindAux_of_not_rel
    {A : Rep k S} (g g₁ : G) (a : A) (h : ¬(QuotientGroup.rightRel S).r g₁ g) :
    indToCoindAux A g a g₁ = 0 := by
  simp [indToCoindAux, dif_neg h]

@[simp]
lemma indToCoindAux_mul_snd {A : Rep k S} (g g₁ : G) (a : A) (s : S) :
    indToCoindAux A g a (s * g₁) = A.ρ s (indToCoindAux A g a g₁) := by
  rcases em ((QuotientGroup.rightRel S).r g₁ g) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s * s₁, mul_assoc ..⟩, dif_pos ⟨s₁, rfl⟩]
    simp [S.1.smul_def, smul_eq_mul, mul_assoc, ← S.1.mul_def]
  · rw [indToCoindAux_of_not_rel _ _ _ h, indToCoindAux_of_not_rel, map_zero]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s⁻¹ * s₁, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
lemma indToCoindAux_mul_fst {A : Rep k S} (g₁ g₂ : G) (a : A) (s : S) :
     indToCoindAux A (s * g₁) (A.ρ s a) g₂ = indToCoindAux A g₁ a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s₁, rfl⟩ | h
  · simp only [indToCoindAux, LinearMap.pi_apply]
    rw [dif_pos ⟨s₁ * s⁻¹, by simp [S.1.smul_def, smul_eq_mul, mul_assoc]⟩, dif_pos ⟨s₁, rfl⟩,
      ← LinearMap.mul_apply, ← map_mul]
    congr
    ext
    simp [S.1.smul_def, mul_assoc]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s₁, hs₁⟩ => ⟨s₁ * s, by simp_all [S.1.smul_def, mul_assoc]⟩) h

@[simp]
lemma indToCoindAux_snd_mul_inv {A : Rep k S} (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A g₁ a (g₂ * g₃⁻¹) = indToCoindAux A (g₁ * g₃) a g₂ := by
  rcases em ((QuotientGroup.rightRel S).r (g₂ * g₃⁻¹) g₁) with ⟨s, hs⟩ | h
  · simp [S.1.smul_def, mul_assoc, ← eq_mul_inv_iff_mul_eq.1 hs]
  · rw [indToCoindAux_of_not_rel (h := h), indToCoindAux_of_not_rel]
    exact mt (fun ⟨s, hs⟩ => ⟨s, by simpa [S.1.smul_def, eq_mul_inv_iff_mul_eq, mul_assoc]⟩) h

@[simp]
lemma indToCoindAux_fst_mul_inv {A : Rep k S} (g₁ g₂ g₃ : G) (a : A) :
    indToCoindAux A (g₁ * g₂⁻¹) a g₃ = indToCoindAux A g₁ a (g₃ * g₂) := by
  simpa using (indToCoindAux_snd_mul_inv g₁ g₃ g₂⁻¹ a).symm

@[simp]
lemma indToCoindAux_comm {A B : Rep k S} (f : A ⟶ B) (g₁ g₂ : G) (a : A) :
    indToCoindAux B g₁ (f.hom a) g₂ = f.hom (indToCoindAux A g₁ a g₂) := by
  rcases em ((QuotientGroup.rightRel S).r g₂ g₁) with ⟨s, rfl⟩ | h
  · simp [S.1.smul_def, hom_comm_apply]
  · simp [indToCoindAux_of_not_rel (h := h)]

noncomputable abbrev indToCoind (A : Rep k S) :
    ind S.subtype A →ₗ[k] coind S.subtype A :=
  Representation.coinvariantsLift _ (TensorProduct.lift <| linearCombination _ fun g =>
    LinearMap.codRestrict _ (indToCoindAux A g) fun _ _ _ => by simp) fun _ => by ext; simp

variable [Fintype (G ⧸ S)]

@[simps]
noncomputable def coindToInd (A : Rep k S) : coind S.subtype A →ₗ[k] ind S.subtype A where
  toFun f := ∑ g : Quotient (QuotientGroup.rightRel S), Quotient.liftOn g (fun g =>
    indMk S.subtype _ g (f.1 g)) fun g₁ g₂ ⟨s, (hs : _ * _ = _)⟩ =>
      (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq s
        (single g₂ 1 ⊗ₜ[k] f.1 g₂) _ <| by have := f.2 s g₂; simp_all
  map_add' _ _ := by simpa [← Finset.sum_add_distrib, TensorProduct.tmul_add] using
      Finset.sum_congr rfl fun z _ => Quotient.inductionOn z fun _ => by simp
  map_smul' _ _ := by simpa [Finset.smul_sum] using Finset.sum_congr rfl fun z _ =>
    Quotient.inductionOn z fun _ => by simp

omit [DecidableRel (QuotientGroup.rightRel S)] in
lemma coindToInd_of_support_subset_orbit {A : Rep k S} (g : G) (f : coind S.subtype A)
    (hx : f.1.support ⊆ MulAction.orbit S g) :
    coindToInd A f = indMk S.subtype _ g (f.1 g) := by
  rw [coindToInd_apply, Finset.sum_eq_single ⟦g⟧]
  · simp
  · intro b _ hb
    induction b using Quotient.inductionOn with | h b =>
    have : f.1 b = 0 := by
      simp_all only [Function.support_subset_iff, ne_eq, Quotient.eq]
      contrapose! hx
      use b, hx, hb
    simp_all
  · simp

@[simps! hom_hom_hom inv_hom_hom]
noncomputable def indCoindIso (A : Rep k S) : ind S.subtype A ≅ coind S.subtype A :=
  Action.mkIso ({
    hom := ModuleCat.ofHom <| indToCoind A
    inv := ModuleCat.ofHom <| coindToInd A
    hom_inv_id := by
      ext g a
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
        LinearMap.coe_restrictScalars]
      rw [coindToInd_of_support_subset_orbit g]
      · simp
      · simp only [Function.support_subset_iff]
        intro x hx
        contrapose! hx
        simpa using indToCoindAux_of_not_rel (h := hx) ..
    inv_hom_id := by
      ext f g
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        coindToInd_apply A, map_sum, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      rw [Finset.sum_eq_single ⟦g⟧]
      · simp
      · intro b _ hb
        induction b using Quotient.inductionOn with | h b =>
        simpa using indToCoindAux_of_not_rel b g (f.1 b) (mt Quotient.sound hb.symm)
      · simp }) fun g => by ext; simp [ModuleCat.endRingEquiv]

variable (k S)

@[simps! hom_app inv_app]
noncomputable def indCoindNatIso : indFunctor k S.subtype ≅ coindFunctor k S.subtype :=
  NatIso.ofComponents indCoindIso fun f => by simp only [coindFunctor_obj]; ext; simp

@[simps! counit_app_hom_hom unit_app_hom_hom]
noncomputable def resIndAdjunction : Action.res _ S.subtype ⊣ indFunctor k S.subtype :=
  (resCoindAdjunction k S.subtype).ofNatIsoRight (indCoindNatIso k S).symm

@[simp]
lemma resIndAdjunction_homEquiv_apply
    {B : Rep k S} (f : (Action.res _ S.subtype).obj A ⟶ B) :
    (resIndAdjunction k S).homEquiv _ _ f =
      resCoindHomLEquiv S.subtype A B f ≫ (indCoindIso B).inv := by
  simp only [resIndAdjunction, Adjunction.ofNatIsoRight, resCoindAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simp]
lemma resIndAdjunction_homEquiv_symm_apply
    {B : Rep k S} (f : A ⟶ (indFunctor k S.subtype).obj B) :
    ((resIndAdjunction k S).homEquiv _ _).symm f =
      (resCoindHomLEquiv S.subtype A B).symm (f ≫ (indCoindIso B).hom) := by
  simp only [resIndAdjunction, Adjunction.ofNatIsoRight, resCoindAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simps! counit_app_hom_hom unit_app_hom_hom]
noncomputable def coindResAdjunction : coindFunctor k S.subtype ⊣ Action.res _ S.subtype :=
  (indResAdjunction k S.subtype).ofNatIsoLeft (indCoindNatIso k S)

@[simp]
lemma coindResAdjunction_homEquiv_apply {B : Rep k S} (f : coind S.subtype B ⟶ A) :
    (coindResAdjunction k S).homEquiv _ _ f =
      indResHomLEquiv S.subtype B A ((indCoindIso B).hom ≫ f) := by
  simp only [coindResAdjunction, Adjunction.ofNatIsoLeft, indResAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

@[simp]
lemma coindResAdjunction_homEquiv_symm_apply
    {B : Rep k S} (f : B ⟶ (Action.res _ S.subtype).obj A) :
    ((coindResAdjunction k S).homEquiv _ _).symm f =
      (indCoindIso B).inv ≫ (indResHomLEquiv S.subtype B A).symm f := by
  simp only [coindResAdjunction, Adjunction.ofNatIsoLeft, indResAdjunction,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

noncomputable instance : Limits.PreservesLimits (indFunctor k S.subtype) :=
  (resIndAdjunction k S).rightAdjoint_preservesLimits

noncomputable instance : Limits.PreservesColimits (coindFunctor k S.subtype) :=
  (coindResAdjunction k S).leftAdjoint_preservesColimits

instance (B : Rep k G) [Projective B] : Projective ((Action.res _ S.subtype).obj B) :=
  (resIndAdjunction k S).map_projective B ‹_›

instance (B : Rep k G) [Injective B] : Injective ((Action.res _ S.subtype).obj B) :=
  (coindResAdjunction k S).map_injective B ‹_›

variable {k}

@[simps]
noncomputable def resMapProjectiveResolution (P : ProjectiveResolution (trivial k G k)) :
    ProjectiveResolution (trivial k S k) where
  complex := ((Action.res _ S.subtype).mapHomologicalComplex _).obj P.complex
  projective _ := inferInstanceAs <| Projective <| (Action.res _ S.subtype).obj _
  hasHomology _ := inferInstance
  π := ((Action.res _ S.subtype).mapHomologicalComplex _).map P.π ≫
    (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
  quasiIso := inferInstance

section groupCohomology

variable {S}

noncomputable def linearYonedaObjResMapProjectiveResolutionIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep k S) :
    (resMapProjectiveResolution S P).complex.linearYonedaObj k A ≅
      P.complex.linearYonedaObj k (coind S.subtype A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (resCoindHomLEquiv _ _ _).toModuleIso) fun _ _ _ =>
      ModuleCat.hom_ext (LinearMap.ext fun f => Action.Hom.ext <| by ext; simp [hom_comm_apply])

noncomputable def _root_.groupCohomologyIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep k G) (n : ℕ) :
    groupCohomology A n ≅ (P.complex.linearYonedaObj k A).homology n :=
  groupCohomologyIsoExt A n ≪≫ P.isoExt _ _

noncomputable def shapiro
    (P : ProjectiveResolution (trivial k G k) := barResolution k G) (A : Rep k S) (n : ℕ) :
    groupCohomology A n ≅ groupCohomology (coind S.subtype A) n :=
  groupCohomologyIso (resMapProjectiveResolution S P) A n ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso
      (linearYonedaObjResMapProjectiveResolutionIso P A) ≪≫
    (groupCohomologyIso P (coind S.subtype A) n).symm

end groupCohomology
section groupHomology

variable {S}

variable (P : Rep k G) (A : Rep k S) (g : G)

#check (coinvariantsTensorMk A ((Action.res _ S.subtype).obj P)).compl₂ (P.ρ g)

noncomputable def coinvariantsTensorIndHom (P : Rep k G) (A : Rep k S) :
    ((coinvariantsTensor k G).obj (ind S.subtype A)).obj P ⟶
      ((coinvariantsTensor k S).obj A).obj ((Action.res _ S.subtype).obj P) :=
  ModuleCat.ofHom <| Representation.coinvariantsLift _ (TensorProduct.lift <|
    Representation.coinvariantsLift _ (TensorProduct.lift <| Finsupp.lift _ _ _
      fun g => ((coinvariantsTensorMk A ((Action.res _ S.subtype).obj P)).compl₂ (P.ρ g)))
        fun s => by
          ext g x y
          simpa using (Submodule.Quotient.eq (augmentationSubmodule (A.ρ.tprod
            (ρ ((Action.res (ModuleCat k) S.subtype).obj P))))).2
            (mem_augmentationSubmodule_of_eq s (x ⊗ₜ[k] P.ρ g y) _ rfl)) fun g => by
          simp only [MonoidalCategory.tensorLeft_obj,
            ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
            ModuleCat.MonoidalCategory.tensorObj, Action.instMonoidalCategory_tensorObj_V]
          ext
          simp

omit [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)] in
lemma coinvariantsTensorIndHom_mk_tmul_indMk {P : Rep k G} {A : Rep k S}
    (g : G) (x : A) (y : P) :
    coinvariantsTensorIndHom P A (coinvariantsTensorMk _ _ (indMk S.subtype _ g x) y) =
      coinvariantsTensorMk _ _ x (P.ρ g y) := by
  simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndHom, coinvariantsTensorMk]

noncomputable def coinvariantsTensorIndInv (P : Rep k G) (A : Rep k S) :
    ((coinvariantsTensor k S).obj A).obj ((Action.res _ S.subtype).obj P) ⟶
      ((coinvariantsTensor k G).obj (ind S.subtype A)).obj P :=
  ModuleCat.ofHom <| Representation.coinvariantsLift _ (TensorProduct.lift <|
      (coinvariantsTensorMk (ind S.subtype A) P) ∘ₗ indMk _ _ 1)
    fun s => by
      simp only [MonoidalCategory.tensorLeft_obj,
        ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
        ModuleCat.MonoidalCategory.tensorObj, Action.instMonoidalCategory_tensorObj_V]
      ext x y
      simpa using (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq
        (ρ := ((A.ρ.ind S.subtype).tprod P.ρ)) s (indMk S.subtype A.ρ (1 : G) x ⊗ₜ[k] y) _
        (by simp [← coinvariantsMk_inv_tmul])

omit [DecidableRel (QuotientGroup.rightRel S)] [Fintype (G ⧸ S)] in
lemma coinvariantsTensorIndInv_mk_tmul_indMk {P : Rep k G} {A : Rep k S}
    (x : A) (y : P) :
    coinvariantsTensorIndInv P A (coinvariantsTensorMk _ _ x y) =
      coinvariantsTensorMk _ _ (indMk S.subtype _ 1 x) y := by
  simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
    ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk]

set_option maxHeartbeats 0 in
@[simps]
noncomputable def coinvariantsTensorIndIso (P : Rep k G) (A : Rep k S) :
    ((coinvariantsTensor k G).obj (ind S.subtype A)).obj P ≅
      ((coinvariantsTensor k S).obj A).obj ((Action.res _ S.subtype).obj P) where
  hom := coinvariantsTensorIndHom P A
  inv := coinvariantsTensorIndInv P A
  hom_inv_id := by
    ext g a p
    simpa [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
      ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom] using (coinvariantsMk_eq_iff ((A.ρ.ind S.subtype).tprod P.ρ)).2 <|
        mem_augmentationSubmodule_of_eq g (indMk S.subtype _ g a ⊗ₜ[k] p) _ <| by simp
  inv_hom_id := by
    ext
    simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj,
      ModuleCat.MonoidalCategory.tensorObj, coinvariantsTensorIndInv, coinvariantsTensorMk,
      coinvariantsTensorIndHom, coinvariantsTensorIndInv]

set_option maxHeartbeats 0 in
@[simps!]
noncomputable def indCompCoinvariantsTensorNatIso (P : Rep k G) :
    indFunctor k S.subtype ⋙ (coinvariantsTensor k G).flip.obj P ≅
      (coinvariantsTensor k S).flip.obj ((Action.res _ S.subtype).obj P) :=
  NatIso.ofComponents (fun A => coinvariantsTensorIndIso P A) fun {X Y} f => by
    simp only [Functor.comp_obj, Functor.flip_obj_obj]
    ext g x p
    simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj, coinvariantsTensorMk,
      ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_whiskerRight, coinvariantsTensorIndHom,
      ModuleCat.MonoidalCategory.tensorObj, ModuleCat.MonoidalCategory.whiskerRight,
      coinvariantsMap]

@[simps!]
noncomputable def coinvariantsTensorResMapProjectiveResolutionIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep k S) :
    (((coinvariantsTensor k S).obj A).mapHomologicalComplex _).obj
        (resMapProjectiveResolution S P).complex ≅
      (((coinvariantsTensor k G).obj (ind S.subtype A)).mapHomologicalComplex _).obj P.complex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (coinvariantsTensorIndIso (P.complex.X n) A).symm) fun _ _ h =>
    coinvariantsTensor_hom_ext <| by
      ext a p
      simp [ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorObj, coinvariantsTensorMk,
        ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_whiskerLeft, coinvariantsMap,
        ModuleCat.MonoidalCategory.tensorObj, ModuleCat.MonoidalCategory.whiskerLeft,
        coinvariantsTensorIndInv, h]

variable [DecidableEq G]

noncomputable def _root_.groupHomologyIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep k G) (n : ℕ) :
    groupHomology A n ≅ ((((coinvariantsTensor k G).obj A).mapHomologicalComplex _).obj
      P.complex).homology n :=
  groupHomologyIsoTor A n ≪≫ P.isoLeftDerivedObj ((coinvariantsTensor k G).obj A) n

noncomputable def shapiro2
    (P : ProjectiveResolution (trivial k G k) := barResolution k G) (A : Rep k S) (n : ℕ) :
    groupHomology A n ≅ groupHomology (ind S.subtype A) n :=
  groupHomologyIso (resMapProjectiveResolution S P) A n ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso
      (coinvariantsTensorResMapProjectiveResolutionIso P A) ≪≫
    (groupHomologyIso P (ind S.subtype A) n).symm

end groupHomology
end Rep
