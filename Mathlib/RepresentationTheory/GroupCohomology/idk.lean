import Mathlib.RepresentationTheory.GroupCohomology.LongExactSequence

universe v u


open CategoryTheory ShortComplex Limits

section

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D] (F G : C ⥤ D)
  [F.Additive] [G.Additive] (X : ShortComplex C) (hX : ShortExact X)
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
    (ι : K ⟶ X.map F) (hι : ι ≫ X.mapNatTrans T = 0) (hK : IsLimit <| KernelFork.ofι ι hι)
    (π : X.map G ⟶ C) (hπ : X.mapNatTrans T ≫ π = 0) (hC : IsColimit <| CokernelCofork.ofπ π hπ) :
    SnakeInput D where
  L₀ := K
  L₁ := X.map F
  L₂ := X.map G
  L₃ := C
  v₀₁ := ι
  v₁₂ := X.mapNatTrans T
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

@[simps (config := .lemmasOnly)]
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

end CategoryTheory.ShortComplex
end

namespace groupCohomology
suppress_compilation
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

abbrev H0ι : H0 A ⟶ A.V := ModuleCat.ofHom <| Submodule.subtype _

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

noncomputable section

set_option maxHeartbeats 0
variable (k G) in
@[simps]
noncomputable def oneCocyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := ModuleCat.of k (oneCocycles X)
  map f := mapOneCocycles (MonoidHom.id G) f
  map_id _ := cyclesMap'_id (moduleCatLeftHomologyData _)
  map_comp _ _ := rfl

variable (k G) in
@[simps]
noncomputable def twoCocyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := ModuleCat.of k (twoCocycles X)
  map f := mapTwoCocycles (MonoidHom.id G) f
  map_id _ := cyclesMap'_id (moduleCatLeftHomologyData _)
  map_comp _ _ := rfl

instance : (oneCocyclesFunctor k G).Additive where
instance : PreservesFiniteLimits (oneCocyclesFunctor k G) :=
  letI : ∀ {X Y : Rep k G} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (oneCocyclesFunctor k G) := by
    intro X Y f
    sorry
  Functor.preservesFiniteLimits_of_preservesKernels _

instance : (twoCocyclesFunctor k G).Additive where
instance : PreservesFiniteLimits (twoCocyclesFunctor k G) :=
  letI : ∀ {X Y : Rep k G} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (twoCocyclesFunctor k G) := by
    intro X Y f
    sorry
  Functor.preservesFiniteLimits_of_preservesKernels _

omit hX in
theorem congr {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : (Action.res _ f₁).obj A ⟶ B} {T : Type*}
    (F : (f : G →* H) → (φ : (Action.res _ f).obj A ⟶ B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

variable (k G) in
@[simps]
noncomputable def H1Functor : Rep k G ⥤ ModuleCat k where
  obj X := H1 X
  map f := H1Map (MonoidHom.id G) f
  map_comp _ _ := by rw [← H1Map_comp, congr (MonoidHom.id_comp _) H1Map]; rfl

variable (k G) in
@[simps]
noncomputable def H2Functor : Rep k G ⥤ ModuleCat k where
  obj X := H2 X
  map f := H2Map (MonoidHom.id G) f
  map_comp _ _ := by rw [← H2Map_comp, congr (MonoidHom.id_comp _) H2Map]; rfl

@[simps]
def H0ιNatTrans : Rep.invariantsFunctor k G ⟶ Action.forget _ _ where
  app X := H0ι X

@[simps]
def H1πNatTrans : oneCocyclesFunctor k G ⟶ H1Functor k G where
  app X := H1π X

@[simps]
def H2πNatTrans : twoCocyclesFunctor k G ⟶ H2Functor k G where
  app X := H2π X

instance : (H1Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := by rw [← cancel_epi (H1π _)]; rfl

instance : (H2Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := by rw [← cancel_epi (H2π _)]; rfl

@[simps]
def dZeroNatTrans : Action.forget _ _ ⟶ oneCocyclesFunctor k G where
  app X := (shortComplexH1 X).moduleCatLeftHomologyData.f'
  naturality X Y f := by
    simp only [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 Y)).i,
      Category.assoc, LeftHomologyData.f'_i, oneCocyclesFunctor_map,
      f'_cyclesMap', Action.forget_obj, Action.forget_map, mapShortComplexH1_τ₁]

variable (k G) in
@[simps]
def oneOpcyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := (shortComplexH1 X).moduleCatRightHomologyData.Q
  map f := opcyclesMap' (mapShortComplexH1 (MonoidHom.id G) f) _ _
  map_id _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl
  map_comp _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

instance : (oneOpcyclesFunctor k G).Additive where
  map_add := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

instance : PreservesFiniteColimits (oneOpcyclesFunctor k G) := sorry

variable (k G) in
@[simps]
def H1ιNatTrans : H1Functor k G ⟶ oneOpcyclesFunctor k G where
  app X := ModuleCat.ofHom <| Submodule.mapQ _ _ (Submodule.subtype _)
    fun x ⟨y, hy⟩ => ⟨y, Subtype.ext_iff.1 hy⟩
  naturality _ _ _ := by rw [← cancel_epi (H1π _)]; rfl

variable (k G) in
@[simps]
def dOneNatTrans : oneOpcyclesFunctor k G ⟶ twoCocyclesFunctor k G where
  app X := (shortComplexH2 X).moduleCatLeftHomologyData.liftK
    ((shortComplexH1 X).moduleCatRightHomologyData.descQ (ModuleCat.ofHom <| dOne X) <|
    ModuleCat.hom_ext <| dOne_comp_dZero _) <| ModuleCat.hom_ext <|
    Submodule.linearMap_qext _ <| dTwo_comp_dOne _
  naturality _ _ _ := by
    simpa [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 _)).i,
      ← cancel_epi (moduleCatRightHomologyData _).p, -moduleCatLeftHomologyData_K,
      -moduleCatLeftHomologyData_i] using (mapShortComplexH1 (MonoidHom.id G) _).comm₂₃

def snakeInput₀ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput
    (Action.forget _ _) (oneCocyclesFunctor k G) X hX dZeroNatTrans
    (X.mapNatTrans <| H0ιNatTrans) (by apply hom_ext <;>
      exact (cancel_mono (shortComplexH1 _).moduleCatLeftHomologyData.i).1 <|
        ModuleCat.hom_ext <| dZero_comp_subtype _) sorry (X.mapNatTrans H1πNatTrans)
        (by apply hom_ext <;>
          exact ModuleCat.hom_ext <| LinearMap.ext fun _ => (Submodule.Quotient.mk_eq_zero _).2
          <| Set.mem_range_self _) <| sorry

def snakeInput₁ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput
    (oneOpcyclesFunctor k G) (twoCocyclesFunctor k G) X hX (dOneNatTrans k G)
    (X.mapNatTrans <| H1ιNatTrans k G) (by
      apply hom_ext <;>
      rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 _)).i,
        ← cancel_epi (H1π _)] <;>
      exact ModuleCat.hom_ext <| LinearMap.ext oneCocycles.dOne_apply) sorry
    (X.mapNatTrans H2πNatTrans)
    (by apply hom_ext <;> rw [← cancel_epi (moduleCatRightHomologyData (shortComplexH1 _)).p] <;>
        exact ModuleCat.hom_ext <| LinearMap.ext fun _ => (Submodule.Quotient.mk_eq_zero _).2
        <| Set.mem_range_self _) sorry


def δZero : H0 X.X₃ ⟶ H1 X.X₁ := (snakeInput₀ hX).δ
def δOne : H1 X.X₃ ⟶ H2 X.X₁ := (snakeInput₁ hX).δ

theorem δZero_apply_aux (y : X.X₂) (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    dOne X.X₁ x = 0 := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH1 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  have := congr($(dOne_comp_dZero X.X₂) y)
  simp_all [shortComplexH1, LinearMap.compLeft]

theorem δZero_apply (z : X.X₃) (hz : z ∈ X.X₃.ρ.invariants) (y : X.X₂) (hy : X.g.hom y = z)
    (x : G → X.X₁) (hx : X.f.hom ∘ x = dZero X.X₂ y) :
    δZero hX ⟨z, hz⟩ = H1π X.X₁ ⟨x, δZero_apply_aux hX y x hx⟩ :=
  (snakeInput₀ hX).δ_apply ⟨z, hz⟩ y ⟨x, δZero_apply_aux hX y x hx⟩ (by exact hy) (Subtype.ext hx)

theorem δOne_apply_aux (y : G → X.X₂) (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    dTwo X.X₁ x = 0 := by
  apply Function.Injective.comp_left ((Rep.mono_iff_injective X.f).1 hX.2)
  have := congr($((mapShortComplexH2 (MonoidHom.id G) X.f).comm₂₃.symm) x)
  have := congr($(dTwo_comp_dOne X.X₂) y)
  simp_all [shortComplexH2, LinearMap.compLeft]

theorem δOne_apply (z : oneCocycles X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δOne hX (H1π X.X₃ z) = H2π X.X₁ ⟨x, δOne_apply_aux hX y x hx⟩ :=
  (snakeInput₁ hX).δ_apply (H1π _ z) (Submodule.mkQ _ y) ⟨x, δOne_apply_aux hX y x hx⟩
    congr(Submodule.Quotient.mk $hy) (Subtype.ext hx)

instance : (oneCocyclesFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := rfl

instance : (H1Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

end
end groupCohomology
