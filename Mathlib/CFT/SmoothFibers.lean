import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Smooth.Local
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.TensorProduct.Quotient

noncomputable section

universe u

open TensorProduct IsLocalRing

section

namespace Algebra

variable
  {R S A P : Type*} [CommRing R] [CommRing A]
  [CommRing S] [Algebra R S] [CommRing P] [Algebra R P] [Algebra P S]
  [Algebra S A] [Algebra P A] [IsScalarTower P S A]
  [IsScalarTower R P S]
  (h₁ : Function.Surjective (algebraMap P S)) (h' : (RingHom.ker (algebraMap P S)).FG)

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

def Extension.contangentEquiv (P : Extension.{u} R S) :
    S ⊗[P.Ring] P.ker ≃ₗ[S] P.Cotangent := by
  refine .ofBijective (Cotangent.mk.liftBaseChange _) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective P.Ring P.ker S P.algebraMap_surjective x
    simp only [mk_apply, LinearMap.liftBaseChange_tmul, one_smul, Cotangent.mk_eq_zero_iff,
      pow_two] at hx ⊢
    refine Submodule.smul_induction_on' (p := fun x (hx : x ∈ P.ker * P.ker) ↦
      (1 : S) ⊗ₜ[P.Ring] (⟨x, Ideal.mul_le_right hx⟩ : P.ker) = 0) (hx := hx) ?_ ?_
    · intro r hr s hs
      trans (r • 1) ⊗ₜ[P.Ring] ⟨s, hs⟩
      · rw [smul_tmul]; rfl
      · simp_all [Algebra.smul_def]
    · intro a ha b hb ha' hb'
      convert congr($ha' + $hb')
      rw [← tmul_add]
      rfl
  · intro x
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    exact ⟨1 ⊗ₜ x, by simp⟩

variable (R S A P) in
def cotangentComplexBaseChange : A ⊗[P] RingHom.ker (algebraMap P S) →ₗ[A] A ⊗[P] Ω[P⁄R] :=
  LinearMap.liftBaseChange _ (KaehlerDifferential.kerToTensor _ _ _ ∘ₗ Submodule.inclusion
    (by rw [IsScalarTower.algebraMap_eq P S A]; intro; aesop))

variable (R S A) in
lemma cotangentComplexBaseChange_eq_lTensor_cotangentComplex (P : Extension.{u} R S)
    [Algebra P.Ring A] [IsScalarTower P.Ring S A] :
  cotangentComplexBaseChange R S A P.Ring =
    AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R] ∘ₗ
      P.cotangentComplex.baseChange A ∘ₗ
      ((AlgebraTensorModule.cancelBaseChange P.Ring S A A P.ker).symm ≪≫ₗ
        P.contangentEquiv.baseChange (A := A)) := by
  ext x
  simp [LinearEquiv.baseChange, Extension.contangentEquiv, cotangentComplexBaseChange]

variable (R S A) in
lemma lTensor_cotangentComplex_eq_cotangentComplexBaseChange (P : Extension.{u} R S)
    [Algebra P.Ring A] [IsScalarTower P.Ring S A] :
  P.cotangentComplex.baseChange A =
    (AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R]).symm ∘ₗ
      cotangentComplexBaseChange R S A P.Ring ∘ₗ
      ((AlgebraTensorModule.cancelBaseChange P.Ring S A A P.ker).symm ≪≫ₗ
        P.contangentEquiv.baseChange (A := A)).symm := by
  apply LinearMap.coe_injective
  dsimp
  rw [LinearEquiv.eq_symm_comp, ← LinearEquiv.comp_symm_eq]
  exact congr(($(cotangentComplexBaseChange_eq_lTensor_cotangentComplex R S A P) : _ → _)).symm

def Extension.tensorCotangentEquiv (P : Extension.{u} R S)
    [Algebra P.Ring A] [IsScalarTower P.Ring S A] :
    A ⊗[S] P.Cotangent ≃ₗ[A] A ⊗[P.Ring] P.ker :=
  P.contangentEquiv.symm.baseChange (A := A) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange P.Ring S A A ↥P.ker

def Extension.tensorCotangentSpaceEquiv (P : Extension.{u} R S)
    [Algebra P.Ring A] [IsScalarTower P.Ring S A] :
    A ⊗[S] P.CotangentSpace ≃ₗ[A] A ⊗[P.Ring] Ω[P.Ring⁄R] :=
  AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R]

theorem FormallySmooth.iff_injective_cotangentComplexBaseChange
    {R S P : Type*} [CommRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S]
    [FormallySmooth R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (cotangentComplexBaseChange R S 𝓀[S] P) := by
  let P' : Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq h₁ }
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P' h₂]
  rw [cotangentComplexBaseChange_eq_lTensor_cotangentComplex R S 𝓀[S] P']
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange P'.Ring S 𝓀[S] 𝓀[S]
    Ω[P'.Ring⁄R]).comp_injective _).symm
  refine (((AlgebraTensorModule.cancelBaseChange P'.Ring S _ _ P'.ker).symm ≪≫ₗ
    P'.contangentEquiv.baseChange (A := 𝓀[S])).injective_comp _).symm

theorem FormallySmooth.iff_injective_cotangentComplexBaseChange_of_field
    {R S P K : Type*} [CommRing R] [Field K]
    [CommRing S] [IsLocalRing S] [Algebra R S] [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [Algebra S K] [Algebra P K] [IsScalarTower P S K]
    [FormallySmooth R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG)
    (h₃ : 𝓂[S] ≤ RingHom.ker (algebraMap S K)) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (cotangentComplexBaseChange R S K P) := by
  let f : 𝓀[S] →ₐ[S] K := Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) h₃
  let := f.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower P 𝓀[S] K := .to₁₃₄ _ S _ _
  rw [FormallySmooth.iff_injective_cotangentComplexBaseChange h₁ h₂,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective 𝓀[S] K]
  have : (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).toLinearMap ∘ₗ
      (cotangentComplexBaseChange R S 𝓀[S] P).baseChange K ∘ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.toLinearMap =
      (cotangentComplexBaseChange R S K P) := by
    ext; simp [cotangentComplexBaseChange]
  rw [← this]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).comp_injective _).symm
  exact ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.injective_comp _).symm

end Algebra

attribute [local irreducible] KaehlerDifferential in
def KaehlerDifferential.tensorKaehlerEquiv' (R S A B : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B]
    [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B] [h : Algebra.IsPushout R S A B] :
    B ⊗[A] Ω[A⁄R] ≃ₗ[B] Ω[B⁄S] := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  let e₁ : B ⊗[A] Ω[A⁄R] ≃ₗ[A] Ω[A⁄R] ⊗[R] S :=
    AlgebraTensorModule.congr (Algebra.IsPushout.equiv R A S B).symm.toLinearEquiv (.refl _ _)
      ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange ..
  let e₂ : B ⊗[A] Ω[A⁄R] ≃ₗ[R] Ω[B⁄S] :=
    e₁.restrictScalars R ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquiv R S A B).restrictScalars R
  refine { __ := e₂, map_smul' := ?_ }
  intro m x
  obtain ⟨m, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective m
  dsimp
  induction m with
  | zero => simp
  | add x y _ _ => simp only [add_smul, map_add, *]
  | tmul a b =>
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *]
  | tmul x y =>
  obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective x
  induction x with
  | zero => simp
  | add x y _ _ => simp only [smul_add, map_add, *, add_tmul]
  | tmul x z =>
  suffices b • z • a • x • KaehlerDifferential.map R S A B y =
      (algebraMap A B a * algebraMap S B b) • z • x • KaehlerDifferential.map R S A B y by
    simpa [e₂, e₁, smul_tmul', Algebra.IsPushout.equiv_tmul, ← mul_smul,
      Algebra.IsPushout.equiv_symm_algebraMap_left, Algebra.IsPushout.equiv_symm_algebraMap_right]
  simp only [← mul_smul, ← @algebraMap_smul S _ B, ← @algebraMap_smul A _ B]
  ring_nf

attribute [local irreducible] KaehlerDifferential in
@[simp]
lemma KaehlerDifferential.tensorKaehlerEquiv'_tmul_D (R S A B : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B]
    [Algebra S B] [IsScalarTower R A B] [IsScalarTower R S B] [h : Algebra.IsPushout R S A B]
    (b a) :
    tensorKaehlerEquiv' R S A B (b ⊗ₜ D _ _ a) = b • D S B (algebraMap A B a) := by
  have : Algebra.IsPushout R A S B := .symm inferInstance
  obtain ⟨b, rfl⟩ := (Algebra.IsPushout.equiv R A S B).surjective b
  induction b with
  | zero => simp
  | add x y _ _ => simp only [map_add, *, add_tmul, add_smul]
  | tmul a' s =>
  trans s • a' • D S B (algebraMap A B a)
  · dsimp [tensorKaehlerEquiv']; simp
  · simp [Algebra.IsPushout.equiv_tmul, mul_smul, smul_comm]

attribute [local irreducible] KaehlerDifferential in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma KaehlerDifferential.tensorKaehlerEquiv'_symm_D_tmul (R S A : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
    (s a) :
    (tensorKaehlerEquiv' R S A (S ⊗[R] A)).symm (D _ _ (s ⊗ₜ a)) = algebraMap _ _ s ⊗ₜ D _ _ a := by
  apply (tensorKaehlerEquiv' R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv'_tmul_D]
  change _ = algebraMap S (S ⊗[R] A) s • D S (S ⊗[R] A) (1 ⊗ₜ a)
  rw [algebraMap_smul, ← Derivation.map_smul, smul_tmul', smul_eq_mul, mul_one]

attribute [local irreducible] KaehlerDifferential in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma KaehlerDifferential.tensorKaehlerEquiv'_symm_D_tmul' (R S A : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [CommRing A] [Algebra R A]
    (s a) :
    (tensorKaehlerEquiv' R S A (A ⊗[R] S)).symm (D _ _ (a ⊗ₜ s)) = algebraMap _ _ s ⊗ₜ D _ _ a := by
  apply (tensorKaehlerEquiv' R S A _).symm_apply_eq.mpr ?_
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tensorKaehlerEquiv'_tmul_D]
  change _ = algebraMap S (A ⊗[R] S) s • D S (A ⊗[R] S) (a ⊗ₜ 1)
  rw [algebraMap_smul, ← Derivation.map_smul, Algebra.smul_def,
    Algebra.TensorProduct.right_algebraMap_apply]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

namespace Algebra

local notation "𝓀[" R "]" => ResidueField R
local notation "𝓂[" R "]" => maximalIdeal R

variable {R S P : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [CommRing P] [Algebra R P]

open LinearMap in
/--
Diagram
                         0
     Q ⊗ K -> Q ⊗ M -> Q ⊗ N -> 0
0 -> P ⊗ K -> P ⊗ M -> P ⊗ N
     A ⊗ K -> A ⊗ M
       0        0
-/
lemma _root_.LinearMap.lTensor_injective_of_exact_of_flat
    {M N A K : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [AddCommGroup A] [AddCommGroup K] [Module R K] [Module R A] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (g : K →ₗ[R] M) (hg : Function.Injective g)
    (H : Function.Exact g f) :
    Function.Injective (g.lTensor A) := by
  let P := A →₀ R
  let π : P →ₗ[R] A := Finsupp.linearCombination R fun a ↦ a
  have hπ : Function.Surjective π := Finsupp.linearCombination_surjective _ Function.surjective_id
  let Q := LinearMap.ker π
  have := SnakeLemma.exact_δ'_left (Q.subtype.rTensor K) (Q.subtype.rTensor M) (Q.subtype.rTensor N)
    (g.lTensor Q) (f.lTensor Q) (lTensor_exact _ H hf) (g.lTensor P) (f.lTensor P)
    (lTensor_exact _ H hf) (by simp) (by simp) (K₃ := Unit) 0
    (by simpa using Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective)
    (π.rTensor K) (rTensor_exact _ (exact_subtype_ker_map π) hπ) (π.rTensor M)
    (rTensor_exact _ (exact_subtype_ker_map π) hπ) (lTensor_surjective Q hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hg) (g.lTensor A)
    (by simp) (rTensor_surjective _ hπ)
  rw [Subsingleton.elim (SnakeLemma.δ' ..) 0] at this
  simpa using this

def _root_.LinearMap.tensorKerEquivOfSurjective
    {M N A : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [AddCommGroup A] [Module R A] [Module.Flat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    LinearMap.ker (f.lTensor A) ≃ₗ[R] A ⊗[R] LinearMap.ker f := by
  refine .ofEq _ _ ?_ ≪≫ₗ (LinearEquiv.ofInjective _ (LinearMap.lTensor_injective_of_exact_of_flat
    f hf _ (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map _))).symm
  rw [LinearMap.exact_iff.mp (lTensor_exact _ (LinearMap.exact_subtype_ker_map _) hf)]

variable [Algebra P S] [IsScalarTower R P S]

variable [IsLocalRing R] [IsLocalRing S] [FormallySmooth R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG)
    [Module.Flat R S] [Algebra.FormallySmooth 𝓀[R] (𝓀[R] ⊗[R] S)]

attribute [local instance] TensorProduct.rightAlgebra in
def kerTensorProductEquivTensorTensorKer {A : Type*} [CommRing A] [Algebra R A] :
    (RingHom.ker (Algebra.TensorProduct.map (.id A A)
      (IsScalarTower.toAlgHom R P S))) ≃ₗ[A ⊗[R] P]
      (A ⊗[R] P) ⊗[P] (RingHom.ker (algebraMap P S)) := by
  let φ : A ⊗[R] P →ₐ[A] A ⊗[R] S :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ePp : A ⊗[R] P ≃ₐ[P] P ⊗[R] A := { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₃ : (RingHom.ker φ) ≃ₗ[R] A ⊗[R] (RingHom.ker (algebraMap P S)) :=
    (LinearMap.tensorKerEquivOfSurjective (IsScalarTower.toAlgHom R P S).toLinearMap
      h₁).restrictScalars R
  let e₄' : (RingHom.ker φ) ≃ₗ[R] (A ⊗[R] P) ⊗[P] (RingHom.ker (algebraMap P S)) :=
    e₃ ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ P _ _).symm.restrictScalars R ≪≫ₗ
      (AlgebraTensorModule.congr (.refl P _) ePp.symm.toLinearEquiv).restrictScalars R ≪≫ₗ
      (_root_.TensorProduct.comm _ _ _).restrictScalars R
  let e₄ : (A ⊗[R] P) ⊗[P] (RingHom.ker (algebraMap P S)) ≃ₗ[A ⊗[R] P] (RingHom.ker φ) :=
    { __ := e₄'.symm, map_smul' r' x := by
        dsimp
        induction x with
        | zero => simp only [smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, LinearEquiv.map_add, *]
        | tmul x y =>
        induction x with
        | zero => simp only [zero_tmul, smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, add_tmul, LinearEquiv.map_add, *]
        | tmul x z =>
        induction r' with
        | zero => simp only [zero_smul, LinearEquiv.map_zero]
        | add x y _ _ => simp only [add_smul, LinearEquiv.map_add, *]
        | tmul r s =>
        rw [smul_tmul']
        ext1
        dsimp [e₄', ePp, φ]
        change ((r * x) ⊗ₜ[R] ((s * z) * y.1)) = (r ⊗ₜ[R] s) * (x ⊗ₜ[R] (z * y.1))
        rw [TensorProduct.tmul_mul_tmul, mul_assoc] }
  exact e₄.symm

attribute [local instance] TensorProduct.rightAlgebra in
omit [IsLocalRing R]
  [IsLocalRing S]
  [FormallySmooth R P]
  [Module.Free P Ω[P⁄R]]
  [Module.Finite P Ω[P⁄R]]
  [FormallySmooth 𝓀[R] (𝓀[R] ⊗[R] S)] in
@[simp]
lemma kerTensorProductEquivTensorTensorKer_symm_apply {A : Type*} [CommRing A] [Algebra R A]
    (x y z) :
    ((kerTensorProductEquivTensorTensorKer (R := R) (A := A) h₁).symm ((x ⊗ₜ y) ⊗ₜ z)).1 =
      x ⊗ₜ (y * z.1) := rfl

include h₁ h₂ in
set_option synthInstance.maxHeartbeats 0 in
set_option maxHeartbeats 0 in
attribute [local irreducible] KaehlerDifferential in
lemma FormallySmooth.of_formallySmooth_fiber_aux
    [IsLocalHom (algebraMap R S)] : Algebra.FormallySmooth R S := by
  let Sp := 𝓀[R] ⊗[R] S
  let Pp := 𝓀[R] ⊗[R] P
  let φ : Pp →ₐ[𝓀[R]] Sp := Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let : Algebra S Sp := TensorProduct.rightAlgebra
  let : Algebra P Pp := TensorProduct.rightAlgebra
  have : IsScalarTower R S Sp := .of_algebraMap_eq' TensorProduct.includeRight.comp_algebraMap.symm
  have : IsScalarTower R P Pp := .of_algebraMap_eq' TensorProduct.includeRight.comp_algebraMap.symm
  let ψ : Sp →ₐ[R] 𝓀[S] := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom _ _ _)
    (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _
  algebraize [φ.toRingHom, (φ.toRingHom.comp (algebraMap P Pp)), ψ.toRingHom,
    ψ.toRingHom.comp φ.toRingHom]
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  have : IsScalarTower P S Sp := .of_algebraMap_eq' rfl
  have : IsScalarTower S Sp 𝓀[S] := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, ψ, Sp]
  have : IsScalarTower P Sp 𝓀[S] := .to₁₃₄ _ S _ _
  have : IsScalarTower P Pp 𝓀[S] := .to₁₂₄ _ _ Sp _
  let ePp : Pp ≃ₐ[P] P ⊗[R] 𝓀[R] := { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₀ : Ω[Pp⁄𝓀[R]] ≃ₗ[Pp] Pp ⊗[P] Ω[P⁄R] :=
    (KaehlerDifferential.tensorKaehlerEquiv' R 𝓀[R] P Pp).symm
  have : Module.Free Pp Ω[Pp⁄𝓀[R]] := .of_equiv e₀.symm
  have : Module.Finite Pp Ω[Pp⁄𝓀[R]] := .of_surjective e₀.symm.toLinearMap e₀.symm.surjective
  let eSp : Sp ≃ₐ[S] S ⧸ 𝓂[R].map (algebraMap R S) :=
    .trans { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
      (TensorProduct.quotIdealMapEquivTensorQuot _ _).symm
  have : Nontrivial Sp := by
    rw [eSp.nontrivial_congr, Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 0 2 rfl rfl).mp inferInstance).trans_lt
      (inferInstanceAs 𝓂[S].IsMaximal).ne_top.lt_top).ne
  have : IsLocalRing Sp :=
    .of_surjective' (algebraMap S _) (TensorProduct.mk_surjective _ _ _ residue_surjective)
  let e₂ : 𝓀[S] ⊗[Pp] Ω[Pp⁄𝓀[R]] ≃ₗ[S] 𝓀[S] ⊗[P] Ω[P⁄R] :=
    (AlgebraTensorModule.congr (.refl 𝓀[S] _) e₀).restrictScalars S ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange P Pp Sp 𝓀[S] Ω[P⁄R]).restrictScalars S
  let e₄ : (RingHom.ker φ) ≃ₗ[Pp] Pp ⊗[P] (RingHom.ker (algebraMap P S)) :=
    kerTensorProductEquivTensorTensorKer h₁
  let e₅ : 𝓀[S] ⊗[Pp] (RingHom.ker φ) ≃ₗ[S] 𝓀[S] ⊗[P] (RingHom.ker (algebraMap P S)) :=
    (AlgebraTensorModule.congr (.refl 𝓀[S] 𝓀[S]) e₄).restrictScalars S ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange P Pp Sp 𝓀[S] _).restrictScalars S
  have h₁' : Function.Surjective φ := LinearMap.lTensor_surjective _ h₁
  have h₂' : (RingHom.ker φ).FG := by
    suffices Module.Finite Pp (RingHom.ker φ) from (Submodule.fg_top _).mp this.1
    have : Module.Finite P (RingHom.ker (algebraMap P S)) := ⟨(Submodule.fg_top _).mpr h₂⟩
    exact .of_surjective e₄.symm.toLinearMap e₄.symm.surjective
  have h₃ : 𝓂[Sp] ≤ RingHom.ker ψ := by
    intro x hx
    obtain ⟨x, rfl⟩ := eSp.symm.surjective x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap 𝓀[R] 𝓀[S] 1 * IsScalarTower.toAlgHom R S 𝓀[S] x = 0
    contrapose! hx
    replace hx : IsUnit x := by simpa using hx
    simpa using hx.map _
  rw [Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange (P := P) h₁ h₂]
  have := (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_of_field
    (R := 𝓀[R]) (S := Sp) (K := 𝓀[S]) (P := Pp) h₁' h₂' h₃).mp inferInstance
  convert (e₂.injective.comp this).comp e₅.symm.injective
  ext x
  dsimp
  induction x with
  | zero => simp only [map_zero]
  | add x y _ _ => simp only [map_add, *]
  | tmul x y =>
  dsimp [e₅, e₄, e₂, cotangentComplexBaseChange, TensorProduct.one_def, Pp, smul_tmul']
  rw [kerTensorProductEquivTensorTensorKer_symm_apply]
  dsimp [e₀]
  rw [KaehlerDifferential.tensorKaehlerEquiv'_symm_D_tmul]
  dsimp
  simp [← TensorProduct.one_def]

lemma FormallySmooth.of_formallySmooth_fiber_of_isLocalRing
    (P : Type*) [CommRing P] [Algebra R P] [Algebra P S] (M : Submonoid P)
    [IsLocalization M S] [Algebra.FinitePresentation R P] -- essentially of finite presentation
    [IsScalarTower R P S]
    [IsLocalHom (algebraMap R S)] : Algebra.FormallySmooth R S := by
  classical
  obtain ⟨n, f₀, hf₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstanceAs (Algebra.FiniteType R P))
  let M' := M.comap f₀
  let P' := Localization M'
  let fP : P' →ₐ[R] S := IsLocalization.liftAlgHom (M := M')
      (f := (IsScalarTower.toAlgHom R P S).comp f₀) fun x ↦ by
    simpa using IsLocalization.map_units (M := M) _ ⟨f₀ x.1, x.2⟩
  have hf₁ : Function.Surjective fP := by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := hf₀ x
    obtain ⟨s, rfl⟩ := hf₀ s
    refine ⟨IsLocalization.mk' (M := M') _ x ⟨s, hs⟩, ?_⟩
    simp [fP, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.liftRight]
  have hfP : (RingHom.ker fP).FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective _ hf₀
    convert this.map (algebraMap _ P')
    refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ by simp_all [fP])
    intro x hx
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M' x
    obtain ⟨a, ha, e⟩ : ∃ a ∈ M, a * f₀ x = 0 := by
      simpa [fP, IsLocalization.lift_mk', IsLocalization.map_eq_zero_iff M] using hx
    obtain ⟨a, rfl⟩ := hf₀ a
    rw [IsLocalization.mk'_mem_map_algebraMap_iff]
    exact ⟨a, ha, by simpa⟩
  let := fP.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' fP.comp_algebraMap.symm
  have : FormallyEtale (MvPolynomial (Fin n) R) P' := .of_isLocalization M'
  have : FormallySmooth R P' := .comp _ (MvPolynomial (Fin n) R) _
  have : Module.Free P' Ω[P'⁄R] :=
    .of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) P')
  exact FormallySmooth.of_formallySmooth_fiber_aux (R := R) (S := S) hf₁ hfP

set_option maxHeartbeats 0 in
lemma Smooth.of_formallySmooth_fiber {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    (H : ∀ (I : Ideal R) [I.IsPrime], FormallySmooth I.ResidueField (I.Fiber S)) :
    Algebra.Smooth R S := by
  refine ⟨smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q ↦ ?_), ‹_›⟩
  let p := q.asIdeal.under R
  let Rp := Localization.AtPrime p
  let Sp := Localization (algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q.asIdeal
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using IsLocalization.map_units (M := q.asIdeal.primeCompl) Sq ⟨algebraMap _ _ x, hx⟩)
  let := f.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (algebraMapSubmonoid Sp q.asIdeal.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  have : FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : FormallySmooth 𝓀[Rp] (𝓀[Rp] ⊗[R] S) := inferInstance
  have : FormallySmooth 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) := by
    have : FormallySmooth S Sq := .of_isLocalization q.asIdeal.primeCompl
    let : Algebra S (𝓀[Rp] ⊗[R] S) := TensorProduct.rightAlgebra
    have : FormallySmooth 𝓀[Rp] ((𝓀[Rp] ⊗[R] S) ⊗[S] Sq) :=
      .comp _ (𝓀[Rp] ⊗[R] S) _
    let e : 𝓀[Rp] ⊗[R] S ≃ₐ[S] S ⊗[R] 𝓀[Rp] :=
      { __ := TensorProduct.comm _ _ _, commutes' _ := rfl }
    let e' : (𝓀[Rp] ⊗[R] S) ⊗[S] Sq ≃ₐ[R] 𝓀[Rp] ⊗[Rp] Sq :=
      ((TensorProduct.comm _ _ _).restrictScalars R).trans <|
      ((TensorProduct.congr (.refl (R := S)) e).restrictScalars R).trans <|
      ((TensorProduct.cancelBaseChange _ _ S _ _).restrictScalars R).trans <|
      (TensorProduct.comm _ _ _).trans (TensorProduct.equivOfCompatibleSMul _ _ _ _)
    have : e'.toAlgHom.comp (IsScalarTower.toAlgHom R p.ResidueField _) =
        IsScalarTower.toAlgHom _ _ _ := by ext
    let e'' : (𝓀[Rp] ⊗[R] S) ⊗[S] Sq ≃ₐ[𝓀[Rp]] 𝓀[Rp] ⊗[Rp] Sq :=
      { __ := e', commutes' r := congr($this r) }
    exact .of_equiv e''
  have := FormallySmooth.of_formallySmooth_fiber_of_isLocalRing
    (R := Rp) (S := Sq) (P := Sp) (algebraMapSubmonoid _ q.asIdeal.primeCompl)
  have : FormallySmooth R Rp := .of_isLocalization p.primeCompl
  exact .comp R Rp Sq

attribute [local instance] Ideal.Quotient.field in
lemma formallyEtale_iff_formallyUnramified_of_field
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [EssFiniteType K A] :
    FormallyEtale K A ↔ FormallyUnramified K A := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  have := FormallyUnramified.isReduced_of_field K A
  have := FormallyUnramified.finite_of_free K A
  have : IsArtinianRing A := .of_finite K A
  let e : A ≃ₐ[K] ((I : MaximalSpectrum A) → A ⧸ I.asIdeal) :=
    { __ := IsArtinianRing.equivPi A, commutes' r := rfl }
  have (I : MaximalSpectrum A) : FormallyEtale K (A ⧸ I.asIdeal) := by
    rw [FormallyEtale.iff_isSeparable, ← FormallyUnramified.iff_isSeparable]
    infer_instance
  exact .of_equiv e.symm

lemma Etale.of_formallyUnramified_of_flat {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S] [FormallyUnramified R S] :
    Etale R S := by
  suffices Smooth R S from ⟨⟨inferInstance, inferInstance⟩, ‹_›⟩
  refine Smooth.of_formallySmooth_fiber fun I hI ↦ ?_
  have := formallyEtale_iff_formallyUnramified_of_field.mpr
    (inferInstanceAs (FormallyUnramified I.ResidueField (I.Fiber S)))
  infer_instance

end Algebra
