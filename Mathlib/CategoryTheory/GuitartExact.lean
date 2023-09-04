import Mathlib.CategoryTheory.Limits.Final

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

section

variable {T}

abbrev StructuredArrow.mk' {X₂ : C₂} (X₁ : C₁) (g : X₂ ⟶ T.obj X₁) : StructuredArrow X₂ T :=
  StructuredArrow.mk g

theorem StructuredArrow.cases {X₂ : C₂} (f : StructuredArrow X₂ T) :
    ∃ (X₁ : C₁) (g : X₂ ⟶ T.obj X₁), f = mk g := ⟨_, _, eq_mk f⟩

theorem StructuredArrow.hom_cases {X₂ : C₂} {f g : StructuredArrow X₂ T} (φ : f ⟶ g) :
    ∃ (ψ : f.right ⟶ g.right) (hψ : f.hom ≫ T.map ψ = g.hom),
      φ = StructuredArrow.homMk ψ hψ := ⟨φ.right, StructuredArrow.w φ, rfl⟩

abbrev CostructuredArrow.mk' {X₂ : C₂} (X₁ : C₁) (g : T.obj X₁ ⟶ X₂) : CostructuredArrow T X₂ :=
  CostructuredArrow.mk g

theorem CostructuredArrow.cases {X₂ : C₂} (f : CostructuredArrow T X₂) :
    ∃ (X₁ : C₁) (g :T.obj X₁ ⟶ X₂), f = mk g := ⟨_, _, eq_mk f⟩

theorem CostructuredArrow.hom_cases {X₂ : C₂} {f g : CostructuredArrow T X₂} (φ : f ⟶ g) :
    ∃ (ψ : f.left ⟶ g.left) (hψ : T.map ψ ≫ g.hom = f.hom),
      φ = CostructuredArrow.homMk ψ hψ := ⟨φ.left, CostructuredArrow.w φ, rfl⟩

end

def TwoSquare := T ⋙ R ⟶ L ⋙ B

namespace TwoSquare

variable {T L R B}

@[ext]
lemma ext (w w' : TwoSquare T L R B) (h : ∀ (X : C₁), w.app X = w'.app X) : w = w' :=
  NatTrans.ext _ _ (funext h)

variable (w : TwoSquare T L R B)

@[simps!]
def costructuredArrowRightwards (X₃ : C₃) :
    CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃) :=
  CostructuredArrow.post L B X₃ ⋙ Comma.mapLeft _ w ⋙
    CostructuredArrow.pre T R (B.obj X₃)

@[simps!]
def structuredArrowDownwards (X₂ : C₂) :
    StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B :=
  StructuredArrow.post X₂ T R ⋙ Comma.mapRight _ w ⋙
    StructuredArrow.pre (R.obj X₂) L B

section

variable {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃)

abbrev JRightwards :=
  StructuredArrow (CostructuredArrow.mk g) (costructuredArrowRightwards w X₃)

abbrev JDownwards :=
  CostructuredArrow (structuredArrowDownwards w X₂) (StructuredArrow.mk g)

section

variable {g}

@[simps!]
def JDownwards.mk
    (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃) (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
      w.JDownwards g :=
  CostructuredArrow.mk' (StructuredArrow.mk a) (StructuredArrow.homMk b (by simpa using comm))

lemma JDownwards.cases
    (f : w.JDownwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃) (comm : R.map a ≫ w.app X₁ ≫ B.map b = g),
      f = mk w X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := CostructuredArrow.cases f
  obtain ⟨X₁, a, rfl⟩ := g.cases
  obtain ⟨b, hb, rfl⟩ := StructuredArrow.hom_cases φ
  exact ⟨X₁, a, b, by simpa using hb, rfl⟩

@[simps!]
def JRightwards.mk
    (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃) (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
      w.JRightwards g :=
  StructuredArrow.mk' (CostructuredArrow.mk b) (CostructuredArrow.homMk a comm)

lemma JRightwards.cases
    (f : w.JRightwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃) (comm : R.map a ≫ w.app X₁ ≫ B.map b = g),
      f = mk w X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := StructuredArrow.cases f
  obtain ⟨X₁, b, rfl⟩ := g.cases
  obtain ⟨a, ha, rfl⟩ := CostructuredArrow.hom_cases φ
  exact ⟨X₁, a, b, by simpa using ha, rfl⟩

end

namespace EquivalenceJ

@[simps]
def functor : JRightwards w g ⥤ JDownwards w g where
  obj f := CostructuredArrow.mk
      (StructuredArrow.homMk f.right.hom (by simpa using CostructuredArrow.w f.hom) :
      (structuredArrowDownwards w X₂).obj
        (StructuredArrow.mk f.hom.left) ⟶ StructuredArrow.mk g)
  map {f₁ f₂} φ :=
    CostructuredArrow.homMk (StructuredArrow.homMk φ.right.left
      (by dsimp; rw [← StructuredArrow.w φ]; rfl))
      (by ext; exact CostructuredArrow.w φ.right)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simps]
def inverse : JDownwards w g ⥤ JRightwards w g where
  obj f := StructuredArrow.mk
      (CostructuredArrow.homMk f.left.hom (by simpa using StructuredArrow.w f.hom) :
    CostructuredArrow.mk g ⟶
      (costructuredArrowRightwards w X₃).obj (CostructuredArrow.mk f.hom.right))
  map {f₁ f₂} φ := StructuredArrow.homMk (CostructuredArrow.homMk φ.left.right
    (by dsimp; rw [← CostructuredArrow.w φ]; rfl))
    (by ext; exact StructuredArrow.w φ.left)
  map_id _ := rfl
  map_comp _ _ := rfl

end EquivalenceJ

def equivalenceJ :
  JRightwards w g ≌ JDownwards w g where
  functor := EquivalenceJ.functor w g
  inverse := EquivalenceJ.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp X := by ext; dsimp; simp

lemma isConnected_JRightwards_iff :
    IsConnected (JRightwards w g) ↔
      IsConnected (JDownwards w g) := by
  constructor
  · intro
    exact isConnected_of_equivalent (equivalenceJ w g)
  · intro
    exact isConnected_of_equivalent (equivalenceJ w g).symm

end

class GuitartExact : Prop where
  isConnected' {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) :
    IsConnected (JRightwards w g)

lemma guitartExact_iff_isConnected_rightwards :
    GuitartExact w ↔ ∀ {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (JRightwards w g) := by
  constructor
  · intro h
    exact h.isConnected'
  · intro h
    exact ⟨h⟩

lemma guitartExact_iff_isConnected_downwards :
    GuitartExact w ↔ ∀ {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (JDownwards w g) := by
  simp only [guitartExact_iff_isConnected_rightwards,
    isConnected_JRightwards_iff]

instance [hw : GuitartExact w] {X₃ : C₃} (g : CostructuredArrow R (B.obj X₃)) :
    IsConnected (StructuredArrow g (costructuredArrowRightwards w X₃)) := by
  rw [guitartExact_iff_isConnected_rightwards] at hw
  apply hw

instance [hw : GuitartExact w] {X₂ : C₂} (g : StructuredArrow (R.obj X₂) B) :
    IsConnected (CostructuredArrow (structuredArrowDownwards w X₂) g) := by
  rw [guitartExact_iff_isConnected_downwards] at hw
  apply hw

lemma guitartExact_iff_final :
    GuitartExact w ↔ ∀ (X₃ : C₃), (costructuredArrowRightwards w X₃).Final :=
  ⟨fun _ _ => ⟨fun _ => inferInstance⟩, fun _ => ⟨fun _ => inferInstance⟩⟩

instance [hw : GuitartExact w] (X₃ : C₃) :
    (costructuredArrowRightwards w X₃).Final := by
  rw [guitartExact_iff_final] at hw
  apply hw

lemma guitartExact_iff_initial :
    GuitartExact w ↔ ∀ (X₂ : C₂), (structuredArrowDownwards w X₂).Initial := by
  refine' ⟨fun _ _ => ⟨fun _ => inferInstance⟩, _⟩
  rw [guitartExact_iff_isConnected_downwards]
  intro h
  intros
  infer_instance

instance [hw : GuitartExact w] (X₂ : C₂) :
    (structuredArrowDownwards w X₂).Initial := by
  rw [guitartExact_iff_initial] at hw
  apply hw

instance [IsEquivalence L] [IsEquivalence R] [IsIso w] : GuitartExact w := by
  rw [guitartExact_iff_initial]
  intro X₂
  have := StructuredArrow.isEquivalencePost X₂ T R
  have : IsEquivalence (Comma.mapRight _ w : StructuredArrow (R.obj X₂) _ ⥤ StructuredArrow (R.obj X₂) _) :=
    IsEquivalence.ofEquivalence (Comma.mapRightIso _ (asIso w))
  have := StructuredArrow.isEquivalencePre (R.obj X₂) L B
  dsimp only [structuredArrowDownwards]
  infer_instance

@[simps!]
def whiskerVertical {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄} (α : L ⟶ L') (β : R' ⟶ R) :
    TwoSquare T L' R' B :=
  whiskerLeft _ β ≫ w ≫ whiskerRight α _

namespace GuitartExact

lemma whiskerVertical [w.GuitartExact] {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄}
    (α : L ≅ L') (β : R ≅ R') : (w.whiskerVertical α.hom β.inv).GuitartExact := by
  rw [guitartExact_iff_initial]
  intro X₂
  let e : structuredArrowDownwards (w.whiskerVertical α.hom β.inv) X₂ ≅
      w.structuredArrowDownwards X₂ ⋙ (StructuredArrow.mapIso (β.app X₂) ).functor :=
    NatIso.ofComponents (fun f => StructuredArrow.isoMk (α.symm.app f.right) (by
      dsimp
      simp only [NatTrans.naturality_assoc, assoc, NatIso.cancel_natIso_inv_left, ← B.map_comp,
        Iso.hom_inv_id_app, B.map_id, comp_id])) (by aesop_cat)
  rw [Functor.initial_natIso_iff e]
  infer_instance

@[simp]
lemma whiskerVertical_iff {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄}
    (α : L ≅ L') (β : R ≅ R') :
    (w.whiskerVertical α.hom β.inv).GuitartExact ↔ w.GuitartExact := by
  constructor
  · intro h
    convert whiskerVertical (w.whiskerVertical α.hom β.inv) α.symm β.symm
    ext X₁
    simp only [Functor.comp_obj, Iso.symm_hom, Iso.symm_inv,
      whiskerVertical_app, assoc, Iso.hom_inv_id_app_assoc,
      ← B.map_comp, Iso.hom_inv_id_app, B.map_id, comp_id]
  · intro h
    exact whiskerVertical w α β

instance [w.GuitartExact] {L' : C₁ ⥤ C₃} {R' : C₂ ⥤ C₄} (α : L ⟶ L') (β : R' ⟶ R)
    [IsIso α] [IsIso β] : (w.whiskerVertical α β).GuitartExact :=
  whiskerVertical w (asIso α) (asIso β).symm

end GuitartExact

end TwoSquare

end CategoryTheory
