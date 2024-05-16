import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.OneHypercover

universe w v₃ v₁ v₂ u₁ u₂ u₃

namespace CategoryTheory

open Category Limits

variable {C₀ : Type u₁} [Category.{v₁} C₀] {C : Type u₂} [Category.{v₂} C]
  (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C)
  (A : Type u₃) [Category.{v₃} A]

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

end PreOneHypercoverDenseData

structure OneHypercoverDenseData (S : C) extends F.PreOneHypercoverDenseData S where
  mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ ∈ J S
  mem₁ (i₁ i₂ : I₀) ⦃W : C⦄ (p₁ : W ⟶ F.obj (X i₁)) (p₂ : W ⟶ F.obj (X i₂))
    (w : p₁ ≫ f i₁ = p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.toPreOneHypercover.sieve₁ p₁ p₂ ∈ J W

namespace OneHypercoverDenseData

variable {F}
variable {X : C} (data : F.OneHypercoverDenseData J X)

@[simps toPreOneHypercover]
def toOneHypercover : J.OneHypercover X where
  toPreOneHypercover := data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

end OneHypercoverDenseData

class IsOneHypercoverDense extends IsContinuous.{v₃} F J₀ J,
    F.IsCocontinuous J₀ J : Prop where
  nonempty_oneHypercoverDenseData (X : C) :
    Nonempty (F.OneHypercoverDenseData J X)

variable [IsOneHypercoverDense.{v₃} F J₀ J]

noncomputable def oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J X :=
  (IsOneHypercoverDense.nonempty_oneHypercoverDenseData J₀ X).some

namespace IsOneHypercoverDense

variable {A}

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

instance essSurj_sheafPushforwardContinuous :
    (F.sheafPushforwardContinuous A J₀ J).EssSurj := sorry

instance isEquivalence_sheafPushforwardContinuous [F.Full] :
    (F.sheafPushforwardContinuous A J₀ J).IsEquivalence where

end IsOneHypercoverDense

end Functor

end CategoryTheory
