/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The presheaf of differentials

In this file, we define the type `M.Derivation φ` of derivations
with values in a presheaf of `R`-modules `M` relative to
a morphism of `φ : S ⟶ F.op ⋙ R` of presheaves of commutative rings
over categories `C` and `D` that are related by a functor `F : C ⥤ D`.
We formalize the notion of universal derivation.

Geometrically, if `f : X ⟶ S` is a morphisms of schemes (or more generally
a morphism of commutative ringed spaces), we would like to apply
these definitions in the case where `F` is the pullback functors from
open subsets of `S` to open subsets of `X` and `φ` is the
morphism $O_S ⟶ f_* O_X$.

In order to prove that there exists a universal derivation, the target
of which shall be called the presheaf of relative differentials of `φ`,
we first study the case where `F` is the identity functor.
In this case where we have a morphism of presheaves of commutative
rings `φ' : S' ⟶ R`, we construct a derivation
`DifferentialsConstruction.derivation'` which is universal.
Then, the general case (TODO) shall be obtained by observing that
derivations for `S ⟶ F.op ⋙ R` identify to derivations
for `S' ⟶ R` where `S'` is the pullback by `F` of the presheaf of
commutative rings `S` (the data is the same: it suffices
to show that the two vanishing conditions `d_app` are equivalent).

-/

universe v u v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

namespace PresheafOfModules

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {G : D ⥤ E}
  {S' R : Dᵒᵖ ⥤ CommRingCat.{u}} {T : Eᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
  (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

/-- Given a morphism of presheaves of commutative rings `φ : S ⟶ F.op ⋙ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`. -/
@[ext]
structure Derivation where
  /-- the underlying additive map `R.obj X →+ M.obj X` of a derivation -/
  d {X : Dᵒᵖ} : R.obj X →+ M.obj X
  d_mul {X : Dᵒᵖ} (a b : R.obj X) : d (a * b) = a • d b + b • d a := by aesop_cat
  d_map {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    d (R.map f x) = M.map f (d x) := by aesop_cat
  d_app {X : Cᵒᵖ} (a : S.obj X) : d (φ.app X a) = 0 := by aesop_cat

namespace Derivation

-- Note: `d_app` cannot be a simp lemma because `dsimp` would
-- simplify the composition of functors `R ⋙ forget₂ _ _`
attribute [simp] d_mul d_map

section AddCommGroup

instance : Zero (M.Derivation φ) where
  zero := { d := 0 }

@[simp] lemma zero_d_apply {X : Dᵒᵖ} (x : R.obj X) :
    (0 : M.Derivation φ).d x = 0 := rfl

variable {M φ}

instance : Neg (M.Derivation φ) where
  neg d :=
    { d := -d.d
      d_mul := fun a b ↦ by dsimp; simp only [d_mul, smul_neg]; abel
      d_app := by intros; dsimp; rw [neg_eq_zero]; apply d_app }

@[simp] lemma neg_d_apply (d : M.Derivation φ) {X : Dᵒᵖ} (x : R.obj X) :
    (-d).d x = -d.d x := rfl

instance : Add (M.Derivation φ) where
  add d₁ d₂ :=
    { d := d₁.d + d₂.d
      d_mul := by intros; dsimp; simp only [d_mul, smul_add]; abel
      d_map := by simp
      d_app := fun _ ↦ by
        dsimp
        erw [d_app, d_app, add_zero] }

@[simp] lemma add_d_apply (d d' : M.Derivation φ) {X : Dᵒᵖ} (x : R.obj X) :
    (d + d').d x = d.d x + d'.d x := rfl

instance : Sub (M.Derivation φ) where
  sub d₁ d₂ :=
    { d := d₁.d - d₂.d
      d_mul := by intros; dsimp; simp only [d_mul, smul_sub]; abel
      d_map := by simp
      d_app := fun _ ↦ by
        dsimp
        erw [d_app, d_app, sub_zero] }

@[simp] lemma sub_d_apply (d d' : M.Derivation φ) {X : Dᵒᵖ} (x : R.obj X) :
    (d - d').d x = d.d x - d'.d x := rfl

instance : AddCommGroup (M.Derivation φ) where
  add_assoc _ _ _ := by ext; dsimp; rw [add_assoc]
  zero_add _ := by ext; dsimp; rw [zero_add]
  add_zero _ := by ext; dsimp; rw [add_zero]
  neg_add_cancel _ := by ext; dsimp; rw [neg_add_cancel]
  add_comm _ _ := by ext; dsimp; rw [add_comm]
  sub_eq_add_neg _ _ := by ext; dsimp; rw [sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

end AddCommGroup

variable {M N φ}

lemma congr_d {d d' : M.Derivation φ} (h : d = d') {X : Dᵒᵖ} (b : R.obj X) :
    d.d b = d'.d b := by rw [h]

variable (d : M.Derivation φ)

@[simp] lemma d_one (X : Dᵒᵖ) : d.d (X := X) 1 = 0 := by
  simpa using d.d_mul (X := X) 1 1

lemma d_zsmul (n : ℤ) {X : Dᵒᵖ} (x : R.obj X) : d.d (n • x) = n • d.d x := by
  rw [map_zsmul]

@[simp]
lemma d_int_eq_zero (X : Dᵒᵖ) (n : ℤ) : d.d (X := X) n = 0 := by
  trans d.d (n • 1)
  · simp
  · rw [d_zsmul, d_one, zsmul_zero]

@[simp]
lemma d_ulift_int_eq_zero (X : Dᵒᵖ) (f : CommRingCat.of (ULift.{u} ℤ) ⟶ R.obj X)
    (n : ULift.{u} ℤ) :
    d.d (X := X) (f n) = 0 := by
  obtain rfl := CommRingCat.isInitial.hom_ext f
    ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
  apply d_int_eq_zero

/-- The postcomposition of a derivation by a morphism of presheaves of modules. -/
@[simps! d_apply]
def postcomp (f : M ⟶ N) : N.Derivation φ where
  d := (f.app _).hom.toAddMonoidHom.comp d.d
  d_map {X Y} g x := by simpa using naturality_apply f g (d.d x)
  d_app {X} a := by
    dsimp
    erw [d_app, map_zero]

variable (N) in
@[simp]
lemma postcomp_zero : d.postcomp (0 : _ ⟶ N) = 0 := rfl

lemma postcomp_comp {P : PresheafOfModules.{v} (R ⋙ forget₂ _ _ )} (f : M ⟶ N) (g : N ⟶ P) :
    d.postcomp (f ≫ g) = (d.postcomp f).postcomp g := rfl

/-- The universal property that a derivation `d : M.Derivation φ` must
satisfy so that the presheaf of modules `M` can be considered as the presheaf of
(relative) differentials of a presheaf of commutative rings `φ : S ⟶ F.op ⋙ R`. -/
structure Universal where
  /-- An absolyte derivation of `M'` descends as a morphism `M ⟶ M'`. -/
  desc {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : M ⟶ M'
  fac {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : d.postcomp (desc d') = d' := by aesop_cat
  postcomp_injective {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    {φ φ' : M ⟶ M'} (h : d.postcomp φ = d.postcomp φ') : φ = φ' := by aesop_cat

attribute [simp] Universal.fac

instance : Subsingleton d.Universal where
  allEq h₁ h₂ := by
    suffices ∀ {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
      (d' : M'.Derivation φ), h₁.desc d' = h₂.desc d' by
        cases h₁
        cases h₂
        simp only [Universal.mk.injEq]
        ext : 2
        apply this
    intro M' d'
    apply h₁.postcomp_injective
    simp

namespace Universal

variable {d} (hd : d.Universal)

@[simp]
lemma desc_postcomp {M' : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') : hd.desc (d.postcomp f) = f :=
  hd.postcomp_injective (by simp)

@[simps]
def homEquiv {M' : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat)} :
    (M ⟶ M') ≃ M'.Derivation φ where
  toFun f := d.postcomp f
  invFun d' := hd.desc d'
  left_inv f := by simp
  right_inv d' := by simp

lemma homEquiv_comp {M' M'' : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat)}
    (f : M ⟶ M') (g : M' ⟶ M'') :
    hd.homEquiv (f ≫ g) = (hd.homEquiv f).postcomp g := rfl

end Universal

end Derivation

/-- The property that there exists a universal derivation for
a morphism of presheaves of commutative rings `S ⟶ F.op ⋙ R`. -/
class HasDifferentials : Prop where
  exists_universal_derivation : ∃ (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
      (d : M.Derivation φ), Nonempty d.Universal

lemma Derivation.Universal.hasDifferentials {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    {d : M.Derivation φ} (hd : d.Universal) : HasDifferentials φ :=
  ⟨_ ,_, ⟨hd⟩⟩

section

variable [HasDifferentials φ]

noncomputable def relativeDifferentials : PresheafOfModules.{u} (R ⋙ forget₂ _ _) :=
  (HasDifferentials.exists_universal_derivation (φ := φ)).choose

noncomputable def universalDerivation : (relativeDifferentials φ).Derivation φ :=
  (HasDifferentials.exists_universal_derivation (φ := φ)).choose_spec.choose

noncomputable def universalUniversalDerivation : (universalDerivation φ).Universal :=
  (HasDifferentials.exists_universal_derivation (φ := φ)).choose_spec.choose_spec.some

end

/--  Given a morphism of presheaf of commutative rings `φ : S ⟶ F.op ⋙ R`,
this is functor which sends a presheaf of modules `M` to the abelian group `M.Derivation φ`. -/
@[simps obj]
def derivationFunctor :
    PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat) ⥤ Ab where
  obj M := AddCommGrp.of (M.Derivation φ)
  map f := AddMonoidHom.mk' (fun d ↦ d.postcomp f) (by aesop_cat)

@[simp]
lemma derivationFunctor_map_apply
    {M N : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat)} (f : M ⟶ N)
    (d : M.Derivation φ) :
    DFunLike.coe (α := M.Derivation φ) (β := fun _ ↦ N.Derivation φ)
      ((derivationFunctor φ).map f) d = d.postcomp f := rfl

namespace Derivation

variable {M φ}

namespace Universal

@[simps]
def corepresentableBy {d : M.Derivation φ} (hd : d.Universal) :
    (derivationFunctor.{v} φ ⋙ forget _).CorepresentableBy M where
  homEquiv := hd.homEquiv
  homEquiv_comp _ _ := hd.homEquiv_comp _ _

end Universal

variable (h : (derivationFunctor.{v} φ ⋙ forget _).CorepresentableBy M)

def ofCorepresentableBy : M.Derivation φ := h.homEquiv (𝟙 _)

lemma ofCorepresentableBy_postcomp {M' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} (f : M ⟶ M') :
    (ofCorepresentableBy h).postcomp f = h.homEquiv f := by
  simpa using (h.homEquiv_comp f (𝟙 _)).symm

def universalOfCorepresentableBy : (ofCorepresentableBy h).Universal where
  desc d := h.homEquiv.symm d
  fac {M'} d := by
    rw [ofCorepresentableBy_postcomp]
    apply Equiv.apply_symm_apply
  postcomp_injective H :=
    h.homEquiv.injective (by simpa only [ofCorepresentableBy_postcomp] using H)

end Derivation

/-- Given a morphism of presheaves of commutative rings `φ : S ⟶ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`. -/
abbrev Derivation' : Type _ := M.Derivation (F := 𝟭 D) φ'

namespace Derivation'

variable {M φ'}

@[simp]
nonrec lemma d_app (d : M.Derivation' φ') {X : Dᵒᵖ} (a : S'.obj X) :
    d.d (φ'.app X a) = 0 :=
  d.d_app _

/-- The derivation relative to the morphism of commutative rings `φ'.app X` induced by
a derivation relative to a morphism of presheaves of commutative rings. -/
noncomputable def app (d : M.Derivation' φ') (X : Dᵒᵖ) : (M.obj X).Derivation (φ'.app X) :=
  ModuleCat.Derivation.mk (fun b ↦ d.d b)

@[simp]
lemma app_apply (d : M.Derivation' φ') {X : Dᵒᵖ} (b : R.obj X) :
    (d.app X).d b = d.d b := rfl

section

variable (d : ∀ (X : Dᵒᵖ), (M.obj X).Derivation (φ'.app X))

/-- Given a morphism of presheaves of commutative rings `φ'`, this is the
in derivation `M.Derivation' φ'` that is given by a compatible family of derivations
with values in the modules `M.obj X` for all `X`. -/
def mk (d_map : ∀ ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
    (d Y).d ((R.map f) x) = (M.map f) ((d X).d x)) : M.Derivation' φ' where
  d {X} := AddMonoidHom.mk' (d X).d (by simp)

variable (d_map : ∀ ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
      (d Y).d ((R.map f) x) = (M.map f) ((d X).d x))

@[simp]
lemma mk_app (X : Dᵒᵖ) : (mk d d_map).app X = d X := rfl

/-- Constructor for `Derivation.Universal` in the case `F` is the identity functor. -/
def Universal.mk {d : M.Derivation' φ'}
    (desc : ∀ {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (_ : M'.Derivation' φ'), M ⟶ M')
    (fac : ∀ {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      (d' : M'.Derivation' φ'), d.postcomp (desc d') = d')
    (postcomp_injective : ∀ {M' : PresheafOfModules (R ⋙ forget₂ _ _)}
      {α β : M ⟶ M'}, d.postcomp α = d.postcomp β → α = β) : d.Universal where
  desc := desc
  fac := fac
  postcomp_injective := postcomp_injective

end

end Derivation'

namespace DifferentialsConstruction

/-- The presheaf of relative differentials of a morphism of presheaves of
commutative rings. -/
@[simps (config := .lemmasOnly)]
noncomputable def relativeDifferentials' :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj X := CommRingCat.KaehlerDifferential (φ'.app X)
  -- Have to hint `g' := R.map f` below, or it gets unfolded weirdly.
  map f := CommRingCat.KaehlerDifferential.map (g' := R.map f) (φ'.naturality f)
  -- Without `dsimp`, `ext` doesn't pick up the right lemmas.
  map_id _ := by dsimp; ext; simp
  map_comp _ _ := by dsimp; ext; simp

attribute [simp] relativeDifferentials'_obj

@[simp]
lemma relativeDifferentials'_map_d {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    DFunLike.coe (α := CommRingCat.KaehlerDifferential (φ'.app X))
      (β := fun _ ↦ CommRingCat.KaehlerDifferential (φ'.app Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((relativeDifferentials' φ').map f))
        (CommRingCat.KaehlerDifferential.d x) =
        CommRingCat.KaehlerDifferential.d (R.map f x) :=
  CommRingCat.KaehlerDifferential.map_d (φ'.naturality f) _

/-- The universal derivation. -/
noncomputable def derivation' : (relativeDifferentials' φ').Derivation' φ' :=
  Derivation'.mk (fun X ↦ CommRingCat.KaehlerDifferential.D (φ'.app X))
    (fun _ _ f x ↦ (relativeDifferentials'_map_d φ' f x).symm)

/-- The derivation `Derivation' φ'` is universal. -/
noncomputable def isUniversal' : (derivation' φ').Universal :=
  Derivation'.Universal.mk
    (fun {M'} d' ↦
      { app := fun X ↦ (d'.app X).desc
        naturality := fun {X Y} f ↦ CommRingCat.KaehlerDifferential.ext (fun b ↦ by
          dsimp
          rw [ModuleCat.Derivation.desc_d, Derivation'.app_apply]
          erw [relativeDifferentials'_map_d φ' f]
          rw [ModuleCat.Derivation.desc_d]
          dsimp
          rw [Derivation.d_map]
          dsimp) })
    (fun {M'} d' ↦ by
      ext X b
      apply ModuleCat.Derivation.desc_d)
    (fun {M} α β h ↦ by
      ext1 X
      exact CommRingCat.KaehlerDifferential.ext (Derivation.congr_d h))

instance : HasDifferentials (F := 𝟭 D) φ' := (isUniversal' φ').hasDifferentials

end DifferentialsConstruction

section

variable {φ M} {dφ : M.Derivation φ} (hdφ : dφ.Universal)
  {ψ : R ⟶ G.op ⋙ T} {φψ : S ⟶ (F ⋙ G).op ⋙ T} (fac : φψ = φ ≫ whiskerLeft F.op ψ)
  {P : PresheafOfModules.{v} (T ⋙ forget₂ _ _)}

namespace Derivation

@[simps]
def induced {M' : PresheafOfModules.{v} (T ⋙ forget₂ _ _)}
    (d : M'.Derivation ψ) : M'.Derivation φψ where
  d := d.d
  d_mul := by simp
  d_map := by simp
  d_app _ := by subst fac; apply d.d_app

local notation "pushforwardψ" =>
  pushforward (F := G) (R := T ⋙ forget₂ _ _) (φ := whiskerRight ψ (forget₂ _ RingCat))

local notation "pullbackψ" =>
  pullback (F := G) (R := T ⋙ forget₂ _ _) (φ := whiskerRight ψ (forget₂ _ RingCat))

local notation "adjunctionψ" =>
  (pullbackPushforwardAdjunction
    (F := G) (R := T ⋙ forget₂ _ _) (φ := whiskerRight ψ (forget₂ _ RingCat)))

variable (dφψ : P.Derivation φψ)

protected noncomputable def pushforward : ((pushforwardψ).obj P).Derivation φ where
  d := AddMonoidHom.mk' (fun a ↦ dφψ.d (ψ.app _ a)) (by simp)
  d_mul {X} a b := by
    dsimp
    rw [map_mul, dφψ.d_mul]
    rfl
  d_map {X Y} f a :=
    (congr_arg dφψ.d (congr_fun ((forget _).congr_map (ψ.naturality f)) a)).trans
      (dφψ.d_map _ _)
  d_app a := by subst fac; exact dφψ.d_app a

lemma pushforward_d_apply (Y : Dᵒᵖ) (a : R.obj Y) :
    (Derivation.pushforward fac dφψ).d a = dφψ.d (ψ.app _ a) := rfl

lemma pushforward_postcomp {P' : PresheafOfModules.{v} (T ⋙ forget₂ _ _)} (α : P ⟶ P') :
    Derivation.pushforward fac (dφψ.postcomp α) =
      (Derivation.pushforward fac dφψ).postcomp ((pushforwardψ).map α) := rfl

@[simp]
lemma pushforward_induced {M' : PresheafOfModules.{v} (T ⋙ forget₂ _ _)} (d : M'.Derivation ψ) :
    Derivation.pushforward fac (induced fac d) = 0 := by
  ext X a
  apply d.d_app

namespace Universal

noncomputable def pushforwardMap : M ⟶ (pushforwardψ).obj P :=
  hdφ.desc (Derivation.pushforward fac dφψ)

variable [(pushforward (F := G) (R := T ⋙ forget₂ _ _)
  (whiskerRight ψ (forget₂ _ RingCat))).IsRightAdjoint]

noncomputable def pullbackMap : (pullbackψ).obj M ⟶ P :=
  ((adjunctionψ).homEquiv M P).symm (hdφ.pushforwardMap fac dφψ)

lemma homEquiv_pullbackMap_comp
    {P' : PresheafOfModules.{v} (T ⋙ forget₂ _ _)} (α : P ⟶ P') :
    (((adjunctionψ).homEquiv _ _) (hdφ.pullbackMap fac dφψ ≫ α)) =
      hdφ.homEquiv.symm (Derivation.pushforward fac (dφψ.postcomp α)) := by
  apply hdφ.homEquiv.injective
  dsimp only [pullbackMap, pushforwardMap, pushforward_postcomp]
  simp only [homEquiv_apply, homEquiv_symm_apply, PresheafOfModules.Derivation.Universal.fac,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, postcomp_comp]

@[simp]
lemma pullbackMap_comp_eq_zero_iff
    {P' : PresheafOfModules.{v} (T ⋙ forget₂ _ _)} (α : P ⟶ P') :
    hdφ.pullbackMap fac dφψ ≫ α = 0 ↔
      Derivation.pushforward fac (dφψ.postcomp α) = 0 := by
  rw [← EmbeddingLike.apply_eq_iff_eq ((adjunctionψ).homEquiv M P'),
    ← EmbeddingLike.apply_eq_iff_eq hdφ.homEquiv, homEquiv_pullbackMap_comp]
  simp only [homEquiv_symm_apply, homEquiv_apply, PresheafOfModules.Derivation.Universal.fac]
  rfl

variable {hdφ fac dφψ}
  {c : CokernelCofork (hdφ.pullbackMap fac dφψ)} (hc : IsColimit c) (hdφψ : dφψ.Universal)

namespace corepresentableByOfIsColimitCokernelCofork

variable {M' : PresheafOfModules.{v} (T ⋙ forget₂ _ _)}

@[simps]
noncomputable def homEquivToFun (f : c.pt ⟶ M') : M'.Derivation ψ where
  d := (dφψ.postcomp (c.π ≫ f)).d
  d_map := by simp
  d_mul := by simp
  d_app := congr_d ((pullbackMap_comp_eq_zero_iff hdφ fac dφψ (c.π ≫ f)).1 (by simp))

noncomputable def homEquivInvFun (d : M'.Derivation ψ) : c.pt ⟶ M' :=
  (CokernelCofork.IsColimit.desc' hc (hdφψ.desc (Derivation.induced fac d)) (by simp)).1

@[simp]
lemma π_homEquivInvFun (d : M'.Derivation ψ) :
    c.π ≫ homEquivInvFun hc hdφψ d = hdφψ.desc (Derivation.induced fac d) :=
  (CokernelCofork.IsColimit.desc' _ _ _).2

@[simp]
lemma homEquiv_left_inv (f : c.pt ⟶ M') :
    homEquivInvFun hc hdφψ (homEquivToFun f) = f := by
  apply Cofork.IsColimit.hom_ext hc
  rw [π_homEquivInvFun]
  apply hdφψ.postcomp_injective
  rw [PresheafOfModules.Derivation.Universal.fac]
  ext
  dsimp

@[simp]
lemma homEquiv_right_inv (d : M'.Derivation ψ) :
    homEquivToFun (homEquivInvFun hc hdφψ d) = d := by
  ext : 2
  simp

end corepresentableByOfIsColimitCokernelCofork

open corepresentableByOfIsColimitCokernelCofork in
noncomputable def corepresentableByOfIsColimitCokernelCofork :
    (derivationFunctor ψ ⋙ forget _).CorepresentableBy c.pt where
  homEquiv {M'} :=
    { toFun := homEquivToFun
      invFun := homEquivInvFun hc hdφψ
      left_inv := fun _ ↦ by simp
      right_inv := fun _ ↦ by simp }
  homEquiv_comp _ _ := rfl

noncomputable def ofIsColimitCokernelCofork :
    (ofCorepresentableBy (corepresentableByOfIsColimitCokernelCofork hc hdφψ)).Universal :=
  universalOfCorepresentableBy (corepresentableByOfIsColimitCokernelCofork hc hdφψ)

end Universal

end Derivation

lemma hasDifferentials_of_tower
    [HasDifferentials φ] [HasDifferentials φψ]
    [(pushforward.{u} (F := G) (R := T ⋙ forget₂ _ _)
      (whiskerRight ψ (forget₂ _ RingCat))).IsRightAdjoint]
    (fac : φψ = φ ≫ whiskerLeft F.op ψ) :
    HasDifferentials ψ :=
  ⟨cokernel (Derivation.Universal.pullbackMap
    (universalUniversalDerivation φ) fac _), _,
      ⟨Derivation.Universal.ofIsColimitCokernelCofork (colimit.isColimit _)
        (universalUniversalDerivation φψ)⟩⟩

end

def absoluteDerivationEquiv
    (φ : (Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ F.op ⋙ R)
    {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} :
    M.Derivation φ ≃ M.Derivation (F := 𝟭 D)
      (S := (Functor.const Dᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))) (R := R)
      { app := fun X ↦ CommRingCat.isInitial.{u}.to _ } where
  toFun d :=
    { d := d.d
      d_mul := by simp
      d_map := by simp
      d_app := by simp }
  invFun d :=
    { d := d.d
      d_mul := by simp
      d_map := by simp
      d_app := by simp }
  left_inv _ := rfl
  right_inv _ := rfl

def absoluteDerivationUniversalEquiv
    (φ : (Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ F.op ⋙ R)
    (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
    (d : M.Derivation (F := 𝟭 D)
      (S := (Functor.const Dᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ))) (R := R)
      { app := fun X ↦ CommRingCat.isInitial.{u}.to _ }) :
    d.Universal ≃ ((absoluteDerivationEquiv φ).symm d).Universal where
  toFun hd :=
    { desc := fun d' ↦ hd.desc (absoluteDerivationEquiv φ d')
      fac := fun d' ↦ (absoluteDerivationEquiv φ).injective
        (hd.fac (absoluteDerivationEquiv φ d'))
      postcomp_injective :=
        fun h ↦ hd.postcomp_injective ((absoluteDerivationEquiv φ).symm.injective h) }
  invFun hd :=
    { desc := fun d' ↦ hd.desc ((absoluteDerivationEquiv φ).symm d')
      fac := fun d' ↦ (absoluteDerivationEquiv φ).symm.injective
        (hd.fac ((absoluteDerivationEquiv φ).symm d'))
      postcomp_injective :=
        fun h ↦ hd.postcomp_injective ((absoluteDerivationEquiv φ).injective h) }
  left_inv := fun _ ↦ Subsingleton.elim _ _
  right_inv := fun _ ↦ Subsingleton.elim _ _

instance hasAbsoluteDifferentials
    (φ : (Functor.const Cᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ F.op ⋙ R) :
    HasDifferentials φ :=
  ((absoluteDerivationUniversalEquiv φ _ _) (universalUniversalDerivation _)).hasDifferentials

instance hasDifferentials
    [(pushforward.{u} (F := F) (R := R ⋙ forget₂ _ _)
      (whiskerRight φ (forget₂ _ RingCat))).IsRightAdjoint] : HasDifferentials φ := by
  let φ₀ : (Functor.const _).obj (CommRingCat.of (ULift.{u} ℤ)) ⟶ S :=
    { app := fun X ↦ CommRingCat.isInitial.{u}.to _ }
  exact hasDifferentials_of_tower (F := 𝟭 C) (φ := φ₀) (ψ := φ) (fac := rfl)

-- TODO: deduce the exact (cokernel) sequence of a tower from
-- Derivation.Universal.ofIsColimitCokernelCofork

end PresheafOfModules
