import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RepresentationTheory.Rep

universe v u


open CategoryTheory ShortComplex Limits

namespace CategoryTheory.ShortComplex
section

variable {C : Type*} [Category C] [HasZeroMorphisms C]

@[ext high]
lemma RightHomologyData.Q_hom_ext {S : ShortComplex C} {Z : C} (X : RightHomologyData S)
    (f g : X.Q ⟶ Z) (h : X.p ≫ f = X.p ≫ g) : f = g :=
  (cancel_epi X.p).1 h

@[ext high]
lemma LeftHomologyData.K_hom_ext {S : ShortComplex C} {Z : C} (X : LeftHomologyData S)
    (f g : Z ⟶ X.K) (h : f ≫ X.i = g ≫ X.i) : f = g :=
  (cancel_mono X.i).1 h

@[ext high]
lemma RightHomologyData.H_hom_ext {S : ShortComplex C} {Z : C} (X : RightHomologyData S)
    (f g : Z ⟶ X.H) (h : f ≫ X.ι = g ≫ X.ι) : f = g :=
  (cancel_mono X.ι).1 h

@[ext high]
lemma LeftHomologyData.H_hom_ext {S : ShortComplex C} {Z : C} (X : LeftHomologyData S)
    (f g : X.H ⟶ Z) (h : X.π ≫ f = X.π ≫ g) : f = g :=
  (cancel_epi X.π).1 h

@[simps!]
def rightHomologyMapData' {X Y : ShortComplex C} (φ : X ⟶ Y)
    (h₁ : RightHomologyData X) (h₂ : RightHomologyData Y) :
    RightHomologyMapData φ h₁ h₂ := by
  let φQ : h₁.Q ⟶ h₂.Q := h₁.descQ (φ.τ₂ ≫ h₂.p) (by rw [← φ.comm₁₂_assoc, h₂.wp, comp_zero])
  have commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by
    rw [← cancel_epi h₁.p, RightHomologyData.p_descQ_assoc, Category.assoc,
      RightHomologyData.p_g', φ.comm₂₃, RightHomologyData.p_g'_assoc]
  let φH : h₁.H ⟶ h₂.H := h₂.liftH (h₁.ι ≫ φQ)
    (by rw [Category.assoc, commg', RightHomologyData.ι_g'_assoc, zero_comp])
  exact ⟨φQ, φH, by simp [φQ], commg', by simp [φH]⟩

end
end CategoryTheory.ShortComplex

section

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F₁ F₂ F₃ : C ⥤ D} [F₁.PreservesZeroMorphisms] [F₂.PreservesZeroMorphisms]
  [F₃.PreservesZeroMorphisms] (S : F₁ ⟶ F₂) (T : F₂ ⟶ F₃) (h : S ≫ T = 0)

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.ShortComplex.mapNatTrans_id {X : ShortComplex C} :
    X.mapNatTrans (𝟙 F₁) = 𝟙 (X.map F₁) := by
  ext <;> simp [← NatTrans.comp_app]

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.ShortComplex.mapNatTrans_zero {X : ShortComplex C} :
    X.mapNatTrans (0 : F₁ ⟶ F₂) = 0 := by
  ext <;> simp [← NatTrans.comp_app]

@[reassoc (attr := simp)]
theorem _root_.CategoryTheory.ShortComplex.mapNatTrans_comp {X : ShortComplex C} :
    X.mapNatTrans (S ≫ T) = X.mapNatTrans S ≫ X.mapNatTrans T := by ext <;> simp

noncomputable def _root_.CategoryTheory.ShortComplex.isLimit_ofι_mapNatTrans
    [HasLimitsOfShape WalkingParallelPair D] (H : IsLimit (KernelFork.ofι S h))
    (X : ShortComplex C) :
    IsLimit (F := (parallelPair (X.mapNatTrans T) 0))
      (KernelFork.ofι (X.mapNatTrans S) <| by ext <;> simp_all [← NatTrans.comp_app]) := by
  refine isLimitOfIsLimitπ _ ?_ ?_ ?_ <;>
  exact (KernelFork.isLimitMapConeEquiv _ _).symm <|
    (KernelFork.ofι S h).isLimitMapConeEquiv _ ((evaluation_preservesLimit _ _).1 H).some

noncomputable def _root_.CategoryTheory.ShortComplex.isColimit_ofπ_mapNatTrans
    [HasColimitsOfShape WalkingParallelPair D] (H : IsColimit (CokernelCofork.ofπ T h))
    (X : ShortComplex C) :
    IsColimit (F := (parallelPair (X.mapNatTrans S) 0))
      (CokernelCofork.ofπ (X.mapNatTrans T) <| by ext <;> simp_all [← NatTrans.comp_app]) := by
  refine isColimitOfIsColimitπ _ ?_ ?_ ?_ <;>
  exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm <|
    (CokernelCofork.ofπ T h).isColimitMapCoconeEquiv _ ((evaluation_preservesColimit _ _).1 H).some

end

theorem _root_.CategoryTheory.ShortComplex.HomologyData.descQ_liftK
    {C : Type*} [Category C] [HasZeroMorphisms C] {S T : ShortComplex C}
    (SH : RightHomologyData S) (TH : LeftHomologyData T) (φ : S.X₂ ⟶ T.X₂)
    (hf : S.f ≫ φ = 0) (hg : φ ≫ T.g = 0) :
    SH.descQ (TH.liftK φ hg) (by ext; simpa) = TH.liftK (SH.descQ φ hf) (by ext; simpa) := by
  ext; simp

namespace CategoryTheory.Iso

variable {R : Type*} [Ring R] (X Y : ModuleCat R) (f : X ≅ Y)

@[simp]
lemma toLinearEquiv_toLinearMap : f.toLinearEquiv = f.hom.hom := rfl

end CategoryTheory.Iso
namespace HomologicalComplex

variable {C : Type*} [Category C]

section

variable [Preadditive C] {ι : Type*} (c : ComplexShape ι) (n : ι) [CategoryWithHomology C]

instance : (cyclesFunctor C c n).Additive where
  map_add := by simp [← cancel_mono (iCycles _ _)]

instance : (opcyclesFunctor C c n).Additive where
  map_add := by simp [← cancel_epi (pOpcycles _ _)]

instance : (cyclesFunctor C c n).Additive where
  map_add := by simp [← cancel_mono (iCycles _ _)]

instance : (homologyFunctor C c n).Additive where
  map_add := by simp [← cancel_epi (homologyπ _ _)]

end
section

variable [Abelian C] {ι : Type*} (c : ComplexShape ι) (n : ι)

instance : PreservesFiniteLimits (cyclesFunctor C c n) := by
  · have := ((HomologicalComplex.cyclesFunctor C c n).preservesFiniteLimits_tfae.out 0 3).1
    exact this fun X hX =>
      haveI := hX.2
      ⟨HomologicalComplex.cycles_left_exact _ hX.1 _, by simp; infer_instance⟩

instance : PreservesFiniteColimits (opcyclesFunctor C c n) := by
  · have := ((HomologicalComplex.opcyclesFunctor C c n).preservesFiniteColimits_tfae.out 0 3).1
    exact this fun X hX =>
      haveI := hX.3
      ⟨HomologicalComplex.opcycles_right_exact _ hX.1 _, by simp; infer_instance⟩

end
end HomologicalComplex
namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category C] [Abelian C]

@[ext]
theorem SnakeInput.hom_ext {S₁ S₂ : SnakeInput C} (f g : S₁ ⟶ S₂) (h₀ : f.f₀ = g.f₀)
    (h₁ : f.f₁ = g.f₁) (h₂ : f.f₂ = g.f₂) (h₃ : f.f₃ = g.f₃) : f = g := by
  cases f; cases g; simp_all

/-- Produce an isomorphism of snake inputs from an isomorphism between each row that make the
obvious diagram commute. -/
@[simps]
def SnakeInput.isoMk {S₁ S₂ : SnakeInput C} (f₀ : S₁.L₀ ≅ S₂.L₀) (f₁ : S₁.L₁ ≅ S₂.L₁)
    (f₂ : S₁.L₂ ≅ S₂.L₂) (f₃ : S₁.L₃ ≅ S₂.L₃) (comm₀₁ : f₀.hom ≫ S₂.v₀₁ = S₁.v₀₁ ≫ f₁.hom)
    (comm₁₂ : f₁.hom ≫ S₂.v₁₂ = S₁.v₁₂ ≫ f₂.hom) (comm₂₃ : f₂.hom ≫ S₂.v₂₃ = S₁.v₂₃ ≫ f₃.hom) :
    S₁ ≅ S₂ where
  hom := ⟨f₀.hom, f₁.hom, f₂.hom, f₃.hom, comm₀₁, comm₁₂, comm₂₃⟩
  inv := ⟨f₀.inv, f₁.inv, f₂.inv, f₃.inv, (CommSq.horiz_inv ⟨comm₀₁⟩).w,
    (CommSq.horiz_inv ⟨comm₁₂⟩).w, (CommSq.horiz_inv ⟨comm₂₃⟩).w⟩
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp

end CategoryTheory.ShortComplex
section

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] (F G : C ⥤ D)
  [F.Additive] [G.Additive] {X : ShortComplex C} (hX : ShortExact X)
  [PreservesFiniteColimits F] [PreservesFiniteLimits G]
  (T : F ⟶ G) (R : Type u) [CommRing R]

/--
Given additive functors of abelian categories `F, G : C ⥤ D` which are right and left exact
respectively, then applying a natural transformation `T : F ⟶ G` to a short exact sequence `X` in
`C` gives us a commutative diagram
```
     F(X₁) ⟶ F(X₂) ⟶ F(X₃) ⟶ 0
      |         |         |
0 ⟶ G(X₁) ⟶ G(X₂) ⟶ G(X₃)
```
with exact rows. Along with a choice of kernel and cokernel of the vertical arrows, this defines a
`SnakeInput D`, and hence also a connecting homomorphism `δ : Ker(T(X₃)) ⟶ Coker(T(X₁))`.
-/
@[simps]
noncomputable def CategoryTheory.ShortComplex.natTransSnakeInput {K C : ShortComplex D}
    (T : X.map F ⟶ X.map G) {ι : K ⟶ X.map F} (hι : ι ≫ T = 0)
    (hK : IsLimit <| KernelFork.ofι ι hι) {π : X.map G ⟶ C} (hπ : T ≫ π = 0)
    (hC : IsColimit <| CokernelCofork.ofπ π hπ) :
    SnakeInput D where
  L₀ := K
  L₁ := X.map F
  L₂ := X.map G
  L₃ := C
  v₀₁ := ι
  v₁₂ := T
  v₂₃ := π
  w₀₂ := hι
  w₁₃ := hπ
  h₀ := hK
  h₃ := hC
  L₁_exact := by have := (F.preservesFiniteColimits_tfae.out 3 0).1; exact (this ‹_› X hX).1
  epi_L₁_g := by have := (F.preservesFiniteColimits_tfae.out 3 0).1; exact (this ‹_› X hX).2
  L₂_exact := by have := (G.preservesFiniteLimits_tfae.out 3 0).1; exact (this ‹_› X hX).1
  mono_L₂_f := by have := (G.preservesFiniteLimits_tfae.out 3 0).1; exact (this ‹_› X hX).2


namespace CategoryTheory.ShortComplex

variable {R : Type u} [CommRing R] (S : ShortComplex (ModuleCat.{v} R))

@[simps! Q H p_hom ι_hom]
def moduleCatRightHomologyData : RightHomologyData S where
  Q := ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom)
  H := ModuleCat.of R <| LinearMap.ker <| (LinearMap.range S.f.hom).liftQ S.g.hom <|
    LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 S.zero
  p := ModuleCat.ofHom <| Submodule.mkQ _
  ι := ModuleCat.ofHom <| Submodule.subtype _
  wp := by ext; exact (Submodule.Quotient.mk_eq_zero _).2 <| Set.mem_range_self _
  hp := ModuleCat.cokernelIsColimit _
  wι := by ext; simp
  hι := ModuleCat.kernelIsLimit <| ModuleCat.ofHom _

@[simp]
lemma moduleCatRightHomologyData_descQ {M : ModuleCat R} (φ : S.X₂ ⟶ M) (hf : S.f ≫ φ = 0) :
    (S.moduleCatRightHomologyData.descQ φ hf).hom =
      (LinearMap.range S.f.hom).liftQ φ.hom
      (LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 hf) := rfl

@[simp]
lemma moduleCatRightHomologyData_liftH {M : ModuleCat R}
    (φ : M ⟶ S.moduleCatRightHomologyData.Q) (h : φ ≫ S.moduleCatRightHomologyData.g' = 0) :
    (S.moduleCatRightHomologyData.liftH φ h).hom =
      φ.hom.codRestrict _ (fun m => by simpa using congr($h m)) := rfl

@[simp]
lemma moduleCatLeftHomologyData_descH {M : ModuleCat R} (φ : S.moduleCatLeftHomologyData.K ⟶ M)
    (h : S.moduleCatLeftHomologyData.f' ≫ φ = 0) :
    (S.moduleCatLeftHomologyData.descH φ h).hom =
      (LinearMap.range <| ModuleCat.Hom.hom _).liftQ
      φ.hom (LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 h) := rfl

@[simp]
lemma moduleCatLeftHomologyData_liftK {M : ModuleCat R} (φ : M ⟶ S.X₂)
    (h : φ ≫ S.g = 0) :
    (S.moduleCatLeftHomologyData.liftK φ h).hom =
      φ.hom.codRestrict _ (fun m => by simpa using congr($h m)) := rfl

/-- Given a short complex `S` of modules, this is the isomorphism between
the abstract `S.opcycles` of the homology API and the more concrete description as
`S.X₂ / LinearMap.range S.f.hom`. -/
noncomputable def moduleCatOpcyclesIso :
    S.opcycles ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.moduleCatRightHomologyData.opcyclesIso

@[reassoc (attr := simp, elementwise)]
lemma pOpcycles_moduleCatOpcyclesIso_hom :
    S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom = S.moduleCatRightHomologyData.p :=
  S.moduleCatRightHomologyData.pOpcycles_comp_opcyclesIso_hom

@[reassoc (attr := simp, elementwise)]
lemma p_moduleCatOpcyclesIso_inv :
    S.moduleCatRightHomologyData.p ≫ S.moduleCatOpcyclesIso.inv = S.pOpcycles :=
  S.moduleCatRightHomologyData.p_comp_opcyclesIso_inv

example {M N : ModuleCat R} (f : M ⟶ N) (hf : Function.Bijective f.hom) :
    IsIso f := by exact (ConcreteCategory.isIso_iff_bijective f).mpr hf

def moduleCatHomologyDataHom :
    S.moduleCatLeftHomologyData.H ⟶ S.moduleCatRightHomologyData.H :=
  S.moduleCatRightHomologyData.liftH (S.moduleCatLeftHomologyData.descH
    (S.moduleCatLeftHomologyData.i ≫ S.moduleCatRightHomologyData.p) <| by simp) <| by
      simp [← cancel_epi S.moduleCatLeftHomologyData.π]

@[reassoc (attr := simp)]
lemma moduleCatHomologyDataHom_comp_ι :
    S.moduleCatHomologyDataHom ≫ S.moduleCatRightHomologyData.ι =
      S.moduleCatLeftHomologyData.descH
      (S.moduleCatLeftHomologyData.i ≫ S.moduleCatRightHomologyData.p) (by simp) := by
  simp [moduleCatHomologyDataHom]

instance : IsIso S.moduleCatHomologyDataHom :=
  (ConcreteCategory.isIso_iff_bijective _).2 <| by
    constructor
    · refine (injective_iff_map_eq_zero _).2 fun x =>
        Submodule.Quotient.induction_on _ x fun x hx => (Submodule.Quotient.mk_eq_zero _).2 ?_
      let ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 <| Subtype.ext_iff.1 hx
      exact ⟨y, Subtype.ext hy⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | @H x =>
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩

@[simps]
noncomputable def moduleCatHomologyData : HomologyData S where
  left := moduleCatLeftHomologyData S
  right := moduleCatRightHomologyData S
  iso := asIso S.moduleCatHomologyDataHom
  comm := by simp

end CategoryTheory.ShortComplex
end
namespace Representation
section Subrepresentation

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
@[simps]
def subrepresentation (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G W where
  toFun g := (ρ g).restrict <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Subrepresentation

section Quotient

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
@[simps]
def quotient (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G (V ⧸ W) where
  toFun g := Submodule.mapQ _ _ (ρ g) <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

end Quotient
end Representation
namespace Rep

variable {k G : Type u} [CommRing k] [Monoid G] (A : Rep k G)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
noncomputable abbrev subrepresentation (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G :=
  Rep.of (A.ρ.subrepresentation W le_comap)

noncomputable def ker {X Y : Rep k G} (f : X ⟶ Y) : Rep k G :=
  subrepresentation X (LinearMap.ker f.hom.hom) fun g x hx => by
    simp_all [hom_comm_apply f g x]

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps]
def subtype (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A where
  hom := ModuleCat.ofHom W.subtype
  comm _ := rfl

-- idk if the le_comap thing should be a class
abbrev kerSubtype {X Y : Rep k G} (f : X ⟶ Y) : ker f ⟶ X :=
  subtype X (LinearMap.ker f.hom.hom) fun g x hx => by simp_all [hom_comm_apply f g x]

noncomputable instance instKerIsLimit {X Y : Rep k G} (f : X ⟶ Y) :
    IsLimit (KernelFork.ofι (f := f) (subtype X _ _ : ker f ⟶ X) <|
      Action.Hom.ext <| ModuleCat.hom_ext <| LinearMap.comp_ker_subtype _) :=
  isLimitOfReflects (Action.forget _ _) <| by
    refine (ModuleCat.kernelIsLimit <| f.hom).equivOfNatIsoOfIso ?_ _ _ ?_
    · exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _))
        (by rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl)
    · exact Cones.ext (Iso.refl _) (by rintro (_ | _) <;> rfl)

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`.-/
noncomputable abbrev quotient (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G :=
  Rep.of (A.ρ.quotient W le_comap)

noncomputable abbrev coker {X Y : Rep k G} (f : X ⟶ Y) :=
  quotient Y (LinearMap.range f.hom.hom) fun g y ⟨x, hx⟩ =>
    ⟨X.ρ g x, by simp_all [hom_comm_apply f g x]⟩

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps]
def mkQ (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap where
  hom := ModuleCat.ofHom <| Submodule.mkQ _
  comm _ := rfl

abbrev cokerMkQ {X Y : Rep k G} (f : X ⟶ Y) : Y ⟶ coker f :=
  mkQ Y (LinearMap.range f.hom.hom) fun g y ⟨x, hx⟩ =>
    ⟨X.ρ g x, by simp_all [hom_comm_apply f g x]⟩

noncomputable instance instCokerIsColimit {X Y : Rep k G} (f : X ⟶ Y) :
    IsColimit (CokernelCofork.ofπ (f := f) (mkQ Y _ _ : Y ⟶ coker f) <|
      Action.Hom.ext <| ModuleCat.hom_ext <| LinearMap.range_mkQ_comp _) :=
  isColimitOfReflects (Action.forget _ _) <| by
    refine (ModuleCat.cokernelIsColimit <| f.hom).equivOfNatIsoOfIso ?_ _ _ ?_
    · exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _))
        (by rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl)
    · exact Cocones.ext (Iso.refl _) (by rintro (_ | _) <;> rfl)

end Rep
