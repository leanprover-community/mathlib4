import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

universe v u v₁ v₂ u₁ u₂

open CategoryTheory

instance : HasForget₂ RingCat.{u} Ab.{u} where
  forget₂ :=
    { obj := fun R ↦ AddCommGrp.of R
      map := fun f ↦ AddMonoidHom.mk' f (by simp) }
  forget_comp := rfl

instance : HasForget₂ CommRingCat.{u} Ab.{u} := HasForget₂.trans _ RingCat.{u} _

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  {F : C ⥤ D}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] -- is it automatic?
  [Functor.IsContinuous.{u} F J K]
  (M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)

def Derivation : Type _ := M.val.Derivation (F := F) φ.val

namespace Derivation

variable {M φ}

def postcomp (d : M.Derivation φ) {N} (f : M ⟶ N) : N.Derivation φ :=
  PresheafOfModules.Derivation.postcomp d f.val

@[simps val_app]
def abSheafHom (d : M.Derivation φ) [K.HasSheafCompose (forget₂ CommRingCat.{u} Ab.{u})] :
  (sheafCompose K (forget₂ CommRingCat Ab)).obj R ⟶ (toSheaf _).obj M where
  val :=
    { app := fun _ ↦ d.d
      naturality := fun _ _ f ↦ by ext; apply d.d_map }

end Derivation

instance : AddCommGroup (M.Derivation φ) :=
  inferInstanceAs (AddCommGroup (M.val.Derivation (F := F) φ.val))

def derivationFunctor :
    SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⥤ Ab :=
  forget _ ⋙ PresheafOfModules.derivationFunctor.{u} (F := F) φ.val

lemma derivationFunctor_obj
    (M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)) :
    (derivationFunctor φ).obj M = AddCommGrp.of (M.Derivation φ) := rfl

variable {M} in
@[simp]
lemma derivationFunctor_map (d : M.Derivation φ) {N} (f : M ⟶ N) :
    (derivationFunctor φ).map f d = d.postcomp f := rfl

namespace Derivation

variable {M φ} (d : M.Derivation φ)

structure Universal where
  desc {M' : SheafOfModules _} (d' : M'.Derivation φ) : M ⟶ M'
  fac {M' : SheafOfModules _} (d' : M'.Derivation φ) : d.postcomp (desc d') = d' := by aesop_cat
  postcomp_injective {M' : SheafOfModules _}
    {φ φ' : M ⟶ M'} (h : d.postcomp φ = d.postcomp φ') : φ = φ' := by aesop_cat

end Derivation

class HasDifferentials : Prop where
  exists_universal_derivation : ∃ (M : SheafOfModules _)
    (d : M.Derivation φ), Nonempty d.Universal

variable {M φ} in
lemma Derivation.Universal.hasDifferentials {d : M.Derivation φ} (hd : d.Universal) :
    HasDifferentials φ := ⟨_, _, ⟨hd⟩⟩

section

variable {M φ} (h : (derivationFunctor φ ⋙ CategoryTheory.forget _).CorepresentableBy M)

def ofCorepresentableBy : M.Derivation φ := h.homEquiv (𝟙 _)

lemma ofCorepresentableBy_postcomp {M' : SheafOfModules _} (f : M ⟶ M') :
    (ofCorepresentableBy h).postcomp f = h.homEquiv f := by
  simpa using (h.homEquiv_comp f (𝟙 _)).symm

def universalOfCorepresentableBy : (ofCorepresentableBy h).Universal where
  desc d := h.homEquiv.symm d
  fac {M'} d := by
    rw [ofCorepresentableBy_postcomp]
    apply Equiv.apply_symm_apply
  postcomp_injective H :=
    h.homEquiv.injective (by simpa only [ofCorepresentableBy_postcomp] using H)

end

end SheafOfModules

namespace PresheafOfModules

namespace Derivation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  {F : C ⥤ D}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] -- is it automatic?
  [Functor.IsContinuous.{u} F J K]
  {φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R}
  {M₀ : PresheafOfModules.{u} (R.val ⋙ forget₂ _ _)}
  {M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R)}
  (d₀ : M₀.Derivation (F := F) φ.val)
  (hd₀ : d₀.Universal) (α : M₀ ⟶ M.val)

def sheafify : M.Derivation φ := d₀.postcomp α

variable {d₀}

def Universal.sheafify [IsLocallyInjective K α] [IsLocallySurjective K α] :
    (d₀.sheafify α).Universal := by
  have := hd₀
  sorry

end Derivation

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  {F : C ⥤ D}
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] -- is it automatic?
  [Functor.IsContinuous.{u} F J K]
  (M : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R))
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)
  [K.WEqualsLocallyBijective AddCommGrp.{u}]
  [HasWeakSheafify K AddCommGrp.{u}]

instance [PresheafOfModules.HasDifferentials (F := F) φ.val] :
    SheafOfModules.HasDifferentials φ := by
  let M₀ := PresheafOfModules.relativeDifferentials (F := F) φ.val
  let α : R.val ⋙ forget₂ _ _ ⟶ ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R).val := 𝟙 _
  let adj := PresheafOfModules.sheafificationAdjunction α
  let β : M₀ ⟶ ((PresheafOfModules.sheafification α).obj M₀).val := adj.unit.app M₀
  have hd₀ := PresheafOfModules.universalUniversalDerivation (F := F) φ.val
  have : PresheafOfModules.IsLocallyInjective K β := by
    apply GrothendieckTopology.instIsLocallyInjectiveToSheafify -- to be cleaned up
  have : PresheafOfModules.IsLocallySurjective K β := by
    apply GrothendieckTopology.instIsLocallySurjectiveToSheafify -- to be cleaned up
  exact (PresheafOfModules.Derivation.Universal.sheafify hd₀ β).hasDifferentials

end SheafOfModules
