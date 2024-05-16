import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.OneHypercover

universe w v₃ v₁ v₂ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C₀ : Type u₁} [Category.{v₁} C₀] {C : Type u₂} [Category.{v₂} C]
  (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C)
  {A : Type u₃} [Category.{v₃} A]

namespace Functor

structure PreOneHypercoverDenseData (S : C) where
  I₀ : Type w
  X (i : I₀) : C₀
  f (i : I₀) : F.obj (X i) ⟶ S
  I₁ (i₁ i₂ : I₀) : Type w
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C₀
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

namespace PreOneHypercoverDenseData

attribute [reassoc] w

variable {F}
variable {X : C} (data : F.PreOneHypercoverDenseData X)

@[simps]
def toPreOneHypercover : PreOneHypercover X where
  I₀ := data.I₀
  X i := F.obj (data.X i)
  f i := data.f i
  I₁ := data.I₁
  Y _ _ j := F.obj (data.Y j)
  p₁ _ _ j := F.map (data.p₁ j)
  p₂ _ _ j := F.map (data.p₂ j)
  w := data.w

/-- The sigma type of all `data.I₁ i₁ i₂` for `⟨i₁, i₂⟩ : data.I₀ × data.I₀`. -/
abbrev I₁' : Type w := Sigma (fun (i : data.I₀ × data.I₀) => data.I₁ i.1 i.2)

@[simps]
def multicospanIndex (P : C₀ᵒᵖ ⥤ A) : MulticospanIndex A where
  L := data.I₀
  R := data.I₁'
  fstTo j := j.1.1
  sndTo j := j.1.2
  left i := P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

@[simps]
def sieve₁₀ {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂) :
    Sieve W₀ where
  arrows Z₀ g := ∃ (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

end PreOneHypercoverDenseData

structure OneHypercoverDenseData (S : C) extends PreOneHypercoverDenseData.{w} F S where
  mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ ∈ J S
  mem₁ (i₁ i₂ : I₀) ⦃W : C⦄ (p₁ : W ⟶ F.obj (X i₁)) (p₂ : W ⟶ F.obj (X i₂))
    (w : p₁ ≫ f i₁ = p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.toPreOneHypercover.sieve₁ p₁ p₂ ∈ J W
  mem₁₀ (i₁ i₂ : I₀) ⦃W₀ : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂)
    (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ ∈ J₀ W₀

namespace OneHypercoverDenseData

variable {F}
variable {X : C} (data : F.OneHypercoverDenseData J₀ J X)

@[simps toPreOneHypercover]
def toOneHypercover : J.OneHypercover X where
  toPreOneHypercover := data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

end OneHypercoverDenseData

class IsOneHypercoverDense extends IsContinuous.{v₃} F J₀ J,
    F.IsCocontinuous J₀ J : Prop where
  nonempty_oneHypercoverDenseData (X : C) :
    Nonempty (OneHypercoverDenseData.{w} F J₀ J X)

variable [IsOneHypercoverDense.{w, v₃} F J₀ J]

noncomputable def oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J₀ J X :=
  (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some

namespace IsOneHypercoverDense

lemma restriction_map_injective {P Q : Cᵒᵖ ⥤ A} {f g : P ⟶ Q} (hQ : Presheaf.IsSheaf J Q)
    (h : ∀ (X₀ : C₀), f.app (Opposite.op (F.obj X₀)) = g.app (Opposite.op (F.obj X₀))) :
    f = g := by
  ext X
  apply Presheaf.IsSheaf.hom_ext_ofArrows hQ _
    ((F.oneHypercoverDenseData J₀ J X.unop).toOneHypercover).mem₀
  intro i
  dsimp
  simp only [← NatTrans.naturality, h]

section

variable {P Q : Cᵒᵖ ⥤ A} (f₀ : F.op ⋙ P ⟶ F.op ⋙ Q) (hQ : Presheaf.IsSheaf J Q)

namespace restriction_map_surjective

noncomputable def app (X : Cᵒᵖ) : P.obj X ⟶ Q.obj X :=
  (((F.oneHypercoverDenseData J₀ J X.unop).toOneHypercover).isLimitMultifork ⟨Q, hQ⟩).lift
    (Multifork.ofι _ (P := P.obj X) (fun i =>
      P.map ((F.oneHypercoverDenseData J₀ J X.unop).f i).op ≫ f₀.app _) (fun j => by
        dsimp at j ⊢
        simp only [assoc]
        erw [← NatTrans.naturality, ← NatTrans.naturality]
        dsimp
        rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
        congr 2
        apply Quiver.Hom.unop_inj
        apply (F.oneHypercoverDenseData J₀ J X.unop).w))

@[reassoc (attr := simp)]
lemma app_fac (X : Cᵒᵖ) (i : (F.oneHypercoverDenseData J₀ J X.unop).I₀) :
    app F J₀ J f₀ hQ X ≫ Q.map ((F.oneHypercoverDenseData J₀ J X.unop).f i).op =
      P.map ((F.oneHypercoverDenseData J₀ J X.unop).f i).op ≫ f₀.app _ :=
  IsLimit.fac _ _ (WalkingMulticospan.left i)

set_option pp.universes true
@[simp]
lemma naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) [F.Full] :
    P.map f ≫ app F J₀ J f₀ hQ Y = app F J₀ J f₀ hQ X ≫ Q.map f :=
  hQ.hom_ext_ofArrows _ (F.oneHypercoverDenseData J₀ J Y.unop).mem₀ (fun i => by
    dsimp at i ⊢
    rw [assoc, assoc, app_fac]
    apply (F.op_comp_isSheaf J₀ J ⟨_, hQ⟩).hom_ext ⟨_, F.cover_lift J₀ J
      (J.pullback_stable ((F.oneHypercoverDenseData J₀ J Y.unop).f i ≫ f.unop)
      (F.oneHypercoverDenseData J₀ J X.unop).mem₀)⟩
    rintro ⟨Z, a, W, b, c, ha, fac⟩
    obtain ⟨i', rfl, hc⟩ := ha.exists
    dsimp at hc
    rw [id_comp] at hc
    subst hc
    replace fac := congr_arg Quiver.Hom.op fac
    dsimp at b fac ⊢
    rw [assoc] at fac
    rw [assoc, assoc, assoc, assoc, ← Q.map_comp, ← Q.map_comp, ← fac, Q.map_comp, app_fac_assoc]
    obtain ⟨b, rfl⟩ := F.map_surjective b
    erw [← f₀.naturality b.op, ← f₀.naturality a.op]
    dsimp
    simp only [← P.map_comp_assoc, fac])

@[simp]
lemma app_obj (X₀ : C₀) [F.Full] :
    app F J₀ J f₀ hQ (Opposite.op (F.obj X₀)) = f₀.app (Opposite.op X₀) :=
  hQ.hom_ext_ofArrows _ (F.oneHypercoverDenseData J₀ J _).mem₀ (fun i => by
    dsimp
    rw [app_fac]
    simpa using f₀.naturality (F.preimage ((F.oneHypercoverDenseData J₀ J (F.obj X₀)).f i)).op)

end restriction_map_surjective

open restriction_map_surjective in
lemma restriction_map_surjective [F.Full] :
    ∃ (f : P ⟶ Q), whiskerLeft F.op f = f₀ :=
   ⟨{ app := app F J₀ J f₀ hQ }, by ext; dsimp; simp⟩

end

instance faithful_sheafPushforwardContinuous :
    (F.sheafPushforwardContinuous A J₀ J).Faithful  where
  map_injective {P G} f g h := by
    ext1
    apply restriction_map_injective F J₀ J G.cond
    intro X₀
    exact congr_app (Prefunctor.congr_map (sheafToPresheaf _ _).toPrefunctor h) (Opposite.op X₀)

instance full_sheafPushforwardContinuous [F.Full] :
    (F.sheafPushforwardContinuous A J₀ J).Full where
  map_surjective {P Q} f := by
    obtain ⟨f₀, hf₀⟩ := restriction_map_surjective F J₀ J ((sheafToPresheaf _ _).map f) Q.cond
    exact ⟨⟨f₀⟩, by ext1; exact hf₀⟩

variable [HasLimitsOfSize.{w, w} A] [F.Full]

namespace essSurj_sheafPushforwardContinuous

variable (P₀ : C₀ᵒᵖ ⥤ A) (hP₀ : Presheaf.IsSheaf J₀ P₀)

noncomputable abbrev extensionObj (X : Cᵒᵖ) : A :=
  multiequalizer ((F.oneHypercoverDenseData J₀ J X.unop).multicospanIndex P₀)

variable {P₀}

variable (P₀) in
noncomputable def extensionObjRestrict' {X : Cᵒᵖ} {Y₀ : C₀} (f : F.obj Y₀ ⟶ X.unop)
    (hf : ∃ (i : (F.oneHypercoverDenseData J₀ J X.unop).I₀)
      (a : Y₀ ⟶ (F.oneHypercoverDenseData J₀ J X.unop).X i),
        F.map a ≫ (F.oneHypercoverDenseData J₀ J X.unop).f i = f) :
    extensionObj F J₀ J P₀ X ⟶ P₀.obj (Opposite.op Y₀) :=
  Multiequalizer.ι _ _ ≫ P₀.map hf.choose_spec.choose.op

lemma extensionObjRestrict'_eq {X : Cᵒᵖ} {Y₀ : C₀} (f : F.obj Y₀ ⟶ X.unop)
    (i : (F.oneHypercoverDenseData J₀ J X.unop).I₀)
    (a : Y₀ ⟶ (F.oneHypercoverDenseData J₀ J X.unop).X i)
    (fac : F.map a ≫ (F.oneHypercoverDenseData J₀ J X.unop).f i = f) :
    extensionObjRestrict' F J₀ J P₀ f ⟨i, a, fac⟩ =
      Multiequalizer.ι ((F.oneHypercoverDenseData J₀ J X.unop).multicospanIndex P₀) i ≫
        P₀.map a.op := by
  have hf : ∃ (i : (F.oneHypercoverDenseData J₀ J X.unop).I₀)
    (a : Y₀ ⟶ (F.oneHypercoverDenseData J₀ J X.unop).X i),
    F.map a ≫ (F.oneHypercoverDenseData J₀ J X.unop).f i = f := ⟨i, a, fac⟩
  obtain ⟨i', a', fac', h'⟩ : ∃ (i' : (F.oneHypercoverDenseData J₀ J X.unop).I₀)
    (a' : Y₀ ⟶ (F.oneHypercoverDenseData J₀ J X.unop).X i')
    (_ : F.map a' ≫ (F.oneHypercoverDenseData J₀ J X.unop).f i' = f),
      extensionObjRestrict' F J₀ J P₀ f hf =
        (by exact Multiequalizer.ι _ _) ≫ P₀.map a'.op := by
    exact ⟨hf.choose, hf.choose_spec.choose, hf.choose_spec.choose_spec, rfl⟩
  apply hP₀.hom_ext ⟨_, (F.oneHypercoverDenseData J₀ J X.unop).mem₁₀ i i' a a' (fac.trans fac'.symm)⟩
  rintro ⟨W₀, g, hg⟩
  dsimp
  obtain ⟨j, c, ha, ha'⟩ := hg
  simp only [h', assoc, ← P₀.map_comp, ← op_comp, ha, ha']
  simp only [op_comp, P₀.map_comp]
  exact (Multiequalizer.condition_assoc
    ((F.oneHypercoverDenseData J₀ J X.unop).multicospanIndex P₀) ⟨⟨i, i'⟩, j⟩ _).symm

noncomputable def extensionObjRestrict {X : Cᵒᵖ} {Y₀ : C₀} (f : F.obj Y₀ ⟶ X.unop) :
    extensionObj F J₀ J P₀ X ⟶ P₀.obj (Opposite.op Y₀) :=
  hP₀.amalgamate (⟨_, F.cover_lift J₀ J
    (J.pullback_stable f (F.oneHypercoverDenseData J₀ J X.unop).mem₀)⟩)
    (fun ⟨W₀, g, hg⟩ => extensionObjRestrict' F J₀ J P₀ (F.map g ≫ f) (by
      obtain ⟨_, a, _, ⟨i⟩, fac⟩ := hg
      obtain ⟨a, rfl⟩ := F.map_surjective a
      exact ⟨_, _, fac⟩)) (by
        rintro ⟨Y₁, Y₂, Z, p₁, p₂, q₁, q₂, hq₁, hq₂, w⟩
        obtain ⟨_, a₁, b₁, h₁, fac₁⟩ := hq₁
        obtain ⟨_, a₂, b₂, h₂, fac₂⟩ := hq₂
        obtain ⟨i₁, rfl, hi₁⟩ := h₁.exists
        obtain ⟨i₂, rfl, hi₂⟩ := h₂.exists
        dsimp at hi₁ hi₂
        rw [id_comp] at hi₁ hi₂
        subst hi₁ hi₂
        obtain ⟨a₁, rfl⟩ := F.map_surjective a₁
        obtain ⟨a₂, rfl⟩ := F.map_surjective a₂
        dsimp
        rw [extensionObjRestrict'_eq F J₀ J hP₀ (F.map q₁ ≫ f) i₁ a₁ fac₁,
          extensionObjRestrict'_eq F J₀ J hP₀ (F.map q₂ ≫ f) i₂ a₂ fac₂,
          assoc, assoc, ← P₀.map_comp, ← P₀.map_comp]
        apply hP₀.hom_ext ⟨_, (F.oneHypercoverDenseData J₀ J X.unop).mem₁₀ i₁ i₂
            (p₁ ≫ a₁) (p₂ ≫ a₂) (by
              simp only [F.map_comp, assoc, fac₁, fac₂]
              simp only [← F.map_comp_assoc, w])⟩
        rintro ⟨T, g, hg⟩
        obtain ⟨j, b, w₁, w₂⟩ := hg
        dsimp
        simp only [assoc, ← P₀.map_comp, ← op_comp, w₁, w₂]
        simp only [op_comp, P₀.map_comp]
        apply Multiequalizer.condition_assoc
          ((F.oneHypercoverDenseData J₀ J X.unop).multicospanIndex P₀) ⟨⟨i₁, i₂⟩, j⟩)

noncomputable def extensionObjRestrict_map_eq_extensionObjRestrict'
    {X : Cᵒᵖ} {Y₀ W₀ : C₀} (f : F.obj Y₀ ⟶ X.unop)
    (g : Opposite.op Y₀ ⟶ Opposite.op W₀) (i : (F.oneHypercoverDenseData J₀ J X.unop).I₀)
    (a : W₀ ⟶ (F.oneHypercoverDenseData J₀ J X.unop).X i)
    (fac : F.map a ≫ (F.oneHypercoverDenseData J₀ J X.unop).f i = F.map g.unop ≫ f) :
    extensionObjRestrict F J₀ J hP₀ f ≫ P₀.map g =
      extensionObjRestrict' F J₀ J P₀ (F.map g.unop ≫ f) ⟨i, a, fac⟩ :=
  hP₀.amalgamate_map _ _ _ ⟨W₀, g.unop, by exact ⟨_, _, _, ⟨i⟩, fac⟩⟩

lemma extensionObjRestrict_eq_π {X : Cᵒᵖ} (i : (F.oneHypercoverDenseData J₀ J X.unop).I₀) :
    extensionObjRestrict F J₀ J hP₀ ((F.oneHypercoverDenseData J₀ J X.unop).f i) =
      Multiequalizer.ι ((F.oneHypercoverDenseData J₀ J X.unop).multicospanIndex P₀) i := by
  have eq := extensionObjRestrict_map_eq_extensionObjRestrict' F J₀ J hP₀
      ((F.oneHypercoverDenseData J₀ J X.unop).f i) (𝟙 _) i (𝟙 _) (by simp)
  dsimp at eq
  simp only [map_id, comp_id, id_comp] at eq
  rw [eq, extensionObjRestrict'_eq F J₀ J hP₀ _ i (𝟙 _) (by simp)]
  simp

@[reassoc (attr := simp)]
def extensionObjRestrict_map {X : Cᵒᵖ} {Y₀ Z₀ : C₀} (f : F.obj Y₀ ⟶ X.unop)
    (g : Opposite.op Y₀ ⟶ Opposite.op Z₀) :
    extensionObjRestrict F J₀ J hP₀ f ≫ P₀.map g =
      extensionObjRestrict F J₀ J hP₀ (F.map g.unop ≫ f) :=
  hP₀.hom_ext ⟨_, F.cover_lift J₀ J (J.pullback_stable (F.map g.unop ≫ f)
    (F.oneHypercoverDenseData J₀ J X.unop).mem₀)⟩ _ _ (by
      rintro ⟨T, a, ha⟩
      obtain ⟨W, b, c, ⟨i⟩, fac⟩ := ha
      obtain ⟨b, rfl⟩ := F.map_surjective b
      dsimp at a g i fac ⊢
      rw [assoc, ← P₀.map_comp, extensionObjRestrict_map_eq_extensionObjRestrict'
          F J₀ J hP₀ f (g ≫ a.op) i b (by simpa using fac),
        extensionObjRestrict_map_eq_extensionObjRestrict' F J₀ J hP₀
          (F.map g.unop ≫ f) a.op i b (by simpa using fac)]
      simp
      )

noncomputable def extensionMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    extensionObj F J₀ J P₀ X ⟶ extensionObj F J₀ J P₀ Y :=
  Multiequalizer.lift _ _ (fun i => extensionObjRestrict F J₀ J hP₀
    ((F.oneHypercoverDenseData J₀ J Y.unop).f i ≫ f.unop)) (by
      rintro ⟨⟨i₁, i₂⟩, j⟩
      simp [PreOneHypercoverDenseData.w_assoc])

@[reassoc (attr := simp)]
lemma extensionMap_restrict {X Y : Cᵒᵖ} (f : X ⟶ Y) {X₀ : C₀} (g : F.obj X₀ ⟶ Y.unop) :
    extensionMap F J₀ J hP₀ f ≫ extensionObjRestrict F J₀ J hP₀ g =
      extensionObjRestrict F J₀ J hP₀ (g ≫ f.unop) := by
  sorry

variable {F J₀ J} in
lemma extensionObj_hom_ext {X : Cᵒᵖ} {T : A} {f g : T ⟶ extensionObj F J₀ J P₀ X}
    (h : ∀ (Y₀ : C₀) (φ : F.obj Y₀ ⟶ X.unop),
      f ≫ extensionObjRestrict F J₀ J hP₀ φ = g ≫ extensionObjRestrict F J₀ J hP₀ φ) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ (fun i => by rw [← extensionObjRestrict_eq_π _ _ _ hP₀, h])

@[simps]
noncomputable def extension : Cᵒᵖ ⥤ A where
  obj X := extensionObj F J₀ J P₀ X
  map f := extensionMap F J₀ J hP₀ f
  map_id X := extensionObj_hom_ext hP₀ (by aesop_cat)
  map_comp f g := extensionObj_hom_ext hP₀ (by aesop_cat)

instance (X₀ : C₀) : IsIso (extensionObjRestrict F J₀ J hP₀ (𝟙 (F.obj X₀))) := sorry

noncomputable def extensionIsoApp (X₀ : C₀ᵒᵖ) :
    extensionObj F J₀ J P₀ (F.op.obj X₀) ≅ P₀.obj X₀ :=
  asIso (extensionObjRestrict F J₀ J hP₀ (𝟙 (F.obj X₀.unop)))

noncomputable def extensionIso : F.op ⋙ extension F J₀ J hP₀ ≅ P₀ :=
  NatIso.ofComponents (fun X₀ => asIso (extensionObjRestrict F J₀ J hP₀ (𝟙 (F.obj X₀.unop))))

lemma extension_isSheaf : Presheaf.IsSheaf J (extension F J₀ J hP₀) := sorry

end essSurj_sheafPushforwardContinuous

open essSurj_sheafPushforwardContinuous in
instance essSurj_sheafPushforwardContinuous :
    (F.sheafPushforwardContinuous A J₀ J).EssSurj where
  mem_essImage F₀ := ⟨⟨_, extension_isSheaf F J₀ J F₀.cond⟩,
    ⟨(sheafToPresheaf _ _).preimageIso (extensionIso F J₀ J F₀.cond)⟩⟩

instance isEquivalence_sheafPushforwardContinuous [F.Full] :
    (F.sheafPushforwardContinuous A J₀ J).IsEquivalence where

end IsOneHypercoverDense

end Functor

end CategoryTheory
