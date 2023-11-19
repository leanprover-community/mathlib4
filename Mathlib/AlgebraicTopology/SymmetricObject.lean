import Mathlib.AlgebraicTopology.SplitSimplicialObject
import Mathlib.AlgebraicTopology.CechNerve
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.GroupTheory.Perm.Basic

universe v u

open CategoryTheory Category Limits

def NonemptyFintypeCat :=
  CategoryTheory.FullSubcategory (fun (X : FintypeCat.{u}) ↦ Nonempty X)

namespace NonemptyFintypeCat

instance : CoeSort NonemptyFintypeCat.{u} (Type u) where
  coe X := X.1.1

def of (X : Type u) [Fintype X] [Nonempty X] :
    NonemptyFintypeCat.{u} :=
  ⟨⟨X, inferInstance⟩, inferInstance⟩

@[simps!]
instance : Category NonemptyFintypeCat.{u} := by
  dsimp [NonemptyFintypeCat]
  infer_instance

@[ext]
lemma hom_ext {X Y : NonemptyFintypeCat.{u}} {f g : X ⟶ Y}
    (h : ∀ (x : X), f x = g x) : f = g := funext h

end NonemptyFintypeCat

@[simps]
def SimplexCategory.toNonemptyFintypeCat :
    SimplexCategory ⥤ NonemptyFintypeCat.{0} where
  obj Δ := NonemptyFintypeCat.of (Fin (Δ.len + 1))
  map f x := f.toOrderHom x

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

def SymmetricObject := NonemptyFintypeCat.{0}ᵒᵖ ⥤ C

namespace SymmetricObject

@[simps!]
instance category : Category (SymmetricObject C) := by
  dsimp only [SymmetricObject]
  infer_instance

def toSimplicialObjectFunctor :
    SymmetricObject C ⥤ SimplicialObject C :=
  (whiskeringLeft _ _ _).obj SimplexCategory.toNonemptyFintypeCat.op

variable {C}

abbrev toSimplicialObject (X : SymmetricObject C) : SimplicialObject C :=
  (toSimplicialObjectFunctor C).obj X

def rep (X : SymmetricObject C) (A : NonemptyFintypeCat) :
  Equiv.Perm A →* Aut (X.obj (Opposite.op A)) where
  toFun g :=
    { hom := X.map (Quiver.Hom.op (g⁻¹).1)
      inv := X.map (Quiver.Hom.op g.1)
      hom_inv_id := by
        rw [← X.map_comp, ← X.map_id]
        congr
        apply Quiver.Hom.unop_inj
        ext
        simp
      inv_hom_id := by
        rw [← X.map_comp, ← X.map_id]
        congr
        apply Quiver.Hom.unop_inj
        ext
        simp }
  map_one' := by
    ext
    apply X.map_id
  map_mul' g₁ g₂ := by
    ext
    dsimp [Aut.Aut_mul_def]
    rw [← X.map_comp]
    rfl

variable [HasFiniteCoproducts C]

/-structure Splitting (X : SymmetricObject C) where
  s : SimplicialObject.Splitting X.toSimplicialObject
  rep (n : ℕ) : Equiv.Perm (Fin (n + 1)) →* Aut (s.N n)
  Z : ℕ → C
  i : ∀ (n : ℕ), Z n ⟶ s.N n
  hi : ∀ (n : ℕ),
    IsColimit (Cofan.mk (s.N n) (fun (g : Equiv.Perm (Fin (n + 1))) => i n ≫ (rep n g).hom))
  d₀ : ∀ (n : ℕ), Z (n + 1) ⟶ Z n
  hd₀ : ∀ (n : ℕ), d₀ n ≫ i n ≫ s.ι n =
    i (n + 1) ≫ s.ι (n + 1) ≫ X.toSimplicialObject.δ (0 : Fin (n + 2)) -/

end SymmetricObject

namespace SymmetricObject

variable {C I : Type*} [Category C]

section

variable {S : C} {X : I → C} (f : ∀ i, X i ⟶ S)

abbrev HasCechObjectWidePullbacks :=
  ∀ (A : NonemptyFintypeCat.{0}) (φ : A → I),
    HasWidePullback S (fun a => X (φ a)) (fun a => f (φ a))

variable [HasCechObjectWidePullbacks f]

abbrev HasCechObjectCoproducts :=
  ∀ (A : NonemptyFintypeCat.{0}), HasCoproduct
    (fun (φ : A → I) => widePullback S (fun a => X (φ a)) (fun a => f (φ a)))

noncomputable def cechObjectSummand {A : NonemptyFintypeCat.{0}} (φ : A → I) :=
  widePullback S (fun b => X (φ b)) (fun b => f (φ b))

noncomputable def cechObjectSummandBase {A : NonemptyFintypeCat.{0}} (φ : A → I) :
    cechObjectSummand f φ ⟶ S :=
  WidePullback.base _

noncomputable def cechObjectSummandπ {A : NonemptyFintypeCat.{0}}
    (φ : A → I) (a : A) (i : I) (h : φ a = i) :
    cechObjectSummand f φ ⟶ X i := WidePullback.π _ a ≫ eqToHom (by subst h; rfl)

@[reassoc (attr := simp)]
lemma cechObjectSummandπ_f {A : NonemptyFintypeCat.{0}}
    (φ : A → I) (a : A) (i : I) (h : φ a = i) :
    cechObjectSummandπ f φ a i h ≫ f i = cechObjectSummandBase f φ := by
  subst h
  dsimp [cechObjectSummandπ, cechObjectSummandBase]
  simp only [comp_id, WidePullback.π_arrow]

noncomputable def cechObjectSummandMap {A B : NonemptyFintypeCat.{0}}
    (g : A ⟶ B) (φ : B → I) (ψ : A → I) (h : φ.comp g = ψ) :
    cechObjectSummand f φ ⟶ cechObjectSummand f ψ :=
  WidePullback.lift (cechObjectSummandBase _ _)
    (fun a => cechObjectSummandπ f φ (g a) (ψ a) (by subst h; rfl)) (by simp)

@[reassoc]
lemma cechObjectMap_π {A B : NonemptyFintypeCat.{0}}
    (g : A ⟶ B) (φ : B → I) (ψ : A → I) (h : φ.comp g = ψ) (a : A) (i : I)
    (h' : ψ a = i) (b : B) (h'' : g a = b) :
    (cechObjectSummandMap f g φ ψ h) ≫ cechObjectSummandπ f ψ a i h' =
      cechObjectSummandπ f φ b i (by rw [← h'', ← h', ← h]; rfl) := by
  subst h h' h''
  dsimp [cechObjectSummandMap, cechObjectSummandπ]
  simp

@[ext]
lemma cechObjectSummand_ext {A : NonemptyFintypeCat.{0}} {φ : A → I} {Z : C}
    {α β : Z ⟶ cechObjectSummand f φ}
    (h : ∀ (a : A) (i : I) (h : φ a = i),
      α ≫ cechObjectSummandπ f φ a i h = β ≫ cechObjectSummandπ f φ a i h) : α = β := by
  apply WidePullback.hom_ext
  · intro a
    simpa [cechObjectSummandπ] using h a _ rfl
  · have a : A := Nonempty.some A.2
    change α ≫ cechObjectSummandBase f φ = β ≫ cechObjectSummandBase f φ
    simp only [← cechObjectSummandπ_f f φ a _ rfl, reassoc_of% (h a _ rfl)]

@[simp]
lemma cechObjectSummandMap_id {A : NonemptyFintypeCat.{0}} (φ : A → I) :
    cechObjectSummandMap f (𝟙 A) φ φ rfl = 𝟙 _ := by
  ext a i h
  rw [id_comp, cechObjectMap_π f (𝟙 A) φ φ rfl a i h a rfl]

lemma cechObjectSummandMap_comp {A₁ A₂ A₃ : NonemptyFintypeCat.{0}}
    (g₁ : A₁ → A₂) (g₂ : A₂ → A₃) (g₁₂ : A₁ → A₃) (h : g₁₂ = g₂.comp g₁)
    (φ₃ : A₃ → I) (φ₂ : A₂ → I) (φ₁ : A₁ → I) (h' : φ₃.comp g₂ = φ₂)
    (h'' : φ₂.comp g₁ = φ₁) :
    cechObjectSummandMap f g₁₂ φ₃ φ₁ (by subst h' h'' h; rfl) =
      cechObjectSummandMap f g₂ φ₃ φ₂ h' ≫ cechObjectSummandMap f g₁ φ₂ φ₁ h'' := by
  subst h
  ext a _ rfl
  rw [assoc, cechObjectMap_π f g₁ φ₂ φ₁ h'' a _ rfl _ rfl,
    cechObjectMap_π f g₂ φ₃ φ₂ h' (g₁ a) (φ₁ a) (by rw [← h'']; rfl) _ rfl,
    cechObjectMap_π f (g₂.comp g₁) φ₃ φ₁ (by rw [← h'', ← h']; rfl) a _ rfl (g₂ (g₁ a)) rfl]

variable [HasCechObjectCoproducts f]

instance {A : NonemptyFintypeCat.{0}}  :
    HasCoproduct (fun (φ : A → I) => cechObjectSummand f φ) := by
  dsimp [cechObjectSummand]
  infer_instance

noncomputable def cechObjectObj (A : NonemptyFintypeCat.{0}) : C :=
  ∐ (fun (φ : A → I) => cechObjectSummand f φ)

noncomputable def ιCechObjectObj {A : NonemptyFintypeCat.{0}} (φ : A → I) :
    cechObjectSummand f φ ⟶ cechObjectObj f A :=
  Sigma.ι _ φ

noncomputable def cechObjectMap {A B : NonemptyFintypeCat.{0}} (g : A ⟶ B) :
    cechObjectObj f B ⟶ cechObjectObj f A :=
  Sigma.desc (fun φ => cechObjectSummandMap f g φ _ rfl ≫ ιCechObjectObj f _)

@[reassoc]
lemma ι_cechObjectMap {A B : NonemptyFintypeCat.{0}} (g : A ⟶ B) (φ : B → I) (ψ : A → I)
    (h : φ.comp g = ψ) :
    ιCechObjectObj f φ ≫ cechObjectMap f g =
      cechObjectSummandMap f g φ ψ h ≫ ιCechObjectObj f ψ := by
  subst h
  dsimp only [ιCechObjectObj, cechObjectMap]
  simp

@[ext]
lemma cechObjectObj_ext {A : NonemptyFintypeCat.{0}} {Z : C}
    {α β : cechObjectObj f A ⟶ Z}
    (h : ∀ (φ : A → I), ιCechObjectObj f φ ≫ α = ιCechObjectObj f φ ≫ β) :
    α = β :=
  Sigma.hom_ext _ _ (fun _ => h _)

@[simps!]
noncomputable def cechObject  : SymmetricObject C where
  obj A := cechObjectObj f A.unop
  map {A₁ A₂} g := cechObjectMap f g.unop
  map_id A := by
    ext φ
    dsimp
    rw [comp_id, ι_cechObjectMap f (𝟙 A.unop) φ φ rfl, cechObjectSummandMap_id, id_comp]
  map_comp := by
    rintro ⟨A₁⟩ ⟨A₂⟩ ⟨A₃⟩ ⟨f₁ : A₂ ⟶ A₁⟩ ⟨f₂ : A₃ ⟶ A₂⟩
    ext (φ : A₁ → I)
    change ιCechObjectObj f φ ≫ cechObjectMap f (f₂ ≫ f₁) =
      ιCechObjectObj f φ ≫ cechObjectMap f f₁ ≫ cechObjectMap f f₂
    rw [ι_cechObjectMap f (f₂ ≫ f₁) φ ((φ.comp f₁).comp f₂) rfl,
      cechObjectSummandMap_comp f f₂ f₁ (f₂ ≫ f₁) rfl φ _ _ rfl rfl, assoc,
      ι_cechObjectMap_assoc f f₁ φ _ rfl, ι_cechObjectMap f f₂ (φ.comp f₁) _ rfl]

end

section

variable {S : C} {X : Unit → C} (f : ∀ i, X i ⟶ S)
  [HasCechObjectWidePullbacks f] [HasCechObjectCoproducts f]
  [H : ∀ (n : ℕ), HasWidePullback (Arrow.mk (f ())).right
    (fun (_ : Fin (n + 1)) ↦ (Arrow.mk (f ())).left) fun _ ↦ (Arrow.mk (f ())).hom]

/-noncomputable def cechObjectToSimplicialObjectIsoApp (Δ : SimplexCategory) :
    (cechObject f).toSimplicialObject.obj (Opposite.op Δ) ≅
      (Arrow.cechNerve (Arrow.mk (f Unit.unit))).obj (Opposite.op Δ) where

noncomputable def cechObjectToSimplicialObjectIso :
    (cechObject f).toSimplicialObject ≅ Arrow.cechNerve (Arrow.mk (f Unit.unit)) :=
  NatIso.ofComponents (fun Δ => cechObjectToSimplicialObjectIsoApp f Δ.unop) (sorry)-/

end

end SymmetricObject

end CategoryTheory
