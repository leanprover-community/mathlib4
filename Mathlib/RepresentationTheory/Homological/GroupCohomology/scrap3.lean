import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

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

@[simps Q H p ι]
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

abbrev φQhom {X Y : ShortComplex (ModuleCat R)} (f : X ⟶ Y) :
    X.X₂ ⧸ LinearMap.range X.f.hom →ₗ[R] Y.X₂ ⧸ LinearMap.range Y.f.hom :=
  Submodule.mapQ _ _ f.τ₂.hom fun _ ⟨y, hy⟩ => ⟨f.τ₁ y, hy ▸ congr($f.comm₁₂ y)⟩

set_option trace.profiler true in
@[simps φQ φH]
def moduleCatRightHomologyMapData {X Y : ShortComplex (ModuleCat R)} (f : X ⟶ Y) :
    RightHomologyMapData f (moduleCatRightHomologyData X) (moduleCatRightHomologyData Y) where
  φQ := ModuleCat.ofHom <| φQhom f
  φH := ModuleCat.ofHom <| LinearMap.restrict (φQhom f) fun x =>
    Submodule.Quotient.induction_on _ x fun x hx => by have := congr($f.comm₂₃ x); simp_all only
      [LinearMap.mem_ker, Submodule.liftQ_apply, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, map_zero, Submodule.mapQ_apply]
  commp := ModuleCat.hom_ext <| by simp only [moduleCatRightHomologyData_Q,
    moduleCatRightHomologyData_p, φQhom, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    Submodule.mapQ_mkQ]
  commg' := by
    simp only [← cancel_epi X.moduleCatRightHomologyData.p, moduleCatRightHomologyData_Q, φQhom,
      moduleCatRightHomologyData_p, ← Category.assoc, ← ModuleCat.ofHom_comp, Submodule.mapQ_mkQ]
    simp only [ModuleCat.ofHom_comp, ModuleCat.of_coe, ModuleCat.ofHom_hom, ←
      moduleCatRightHomologyData_p, Category.assoc, RightHomologyData.p_g', f.comm₂₃]
  commι := ModuleCat.hom_ext <| LinearMap.ext fun ⟨x, hx⟩ => by
    induction x using Submodule.Quotient.induction_on with | @H x =>
    simp only [moduleCatRightHomologyData_Q, moduleCatRightHomologyData_H,
      moduleCatRightHomologyData_ι, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
      Submodule.coe_subtype, Function.comp_apply, LinearMap.restrict_coe_apply,
      Submodule.mapQ_apply]
-- man why do things keep being slow latelyyyy

@[simps]
noncomputable def moduleCatHomologyData : HomologyData S where
  left := moduleCatLeftHomologyData S
  right := moduleCatRightHomologyData S
  iso := (LinearEquiv.ofBijective
    (Submodule.liftQ _ ((Submodule.mkQ _).restrict fun x hx => hx) fun ⟨x, hx⟩ ⟨y, hy⟩ =>
      Subtype.ext <| (Submodule.Quotient.mk_eq_zero _).2 ⟨y, Subtype.ext_iff.1 hy⟩)
    ⟨(injective_iff_map_eq_zero _).2 <| fun x => Submodule.Quotient.induction_on _ x fun x hx =>
      (Submodule.Quotient.mk_eq_zero _).2 <|
      let ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).1 <| Subtype.ext_iff.1 hx
      ⟨y, Subtype.ext hy⟩,
    fun ⟨x, hx⟩ => by
      induction x using Submodule.Quotient.induction_on with | @H x =>
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩⟩).toModuleIso
  comm := rfl

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

namespace groupHomology
suppress_compilation
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)

open CategoryTheory ShortComplex

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
  {X : ShortComplex (Rep k G)} (hX : ShortExact X)

include hX

noncomputable section

set_option maxHeartbeats 0
variable (k G) in
@[simps]
noncomputable def oneCyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := ModuleCat.of k (oneCycles X)
  map f := mapOneCycles (MonoidHom.id G) f
  map_id _ := by simp [mapOneCycles, shortComplexH1, oneCycles]
  map_comp _ _ := by simp only [mapOneCycles]; rw [← cyclesMap'_comp, ← mapShortComplexH1_id_comp]

variable (k G) in
@[simps]
noncomputable def twoCyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := ModuleCat.of k (twoCycles X)
  map f := mapTwoCycles (MonoidHom.id G) f
  map_id _ := by simp [mapTwoCycles, shortComplexH2, twoCycles]
  map_comp _ _ := by simp only [mapTwoCycles]; rw [← cyclesMap'_comp, ← mapShortComplexH2_id_comp]
#exit
def oneCyclesKerLequiv {X Y : Rep k G} (f : X ⟶ Y) :
    oneCycles (Rep.ker f) ≃ₗ[k] LinearMap.ker ((oneCyclesFunctor k G).map f).hom where
 /- toFun x := ⟨⟨Subtype.val ∘ x,
    LinearMap.mem_ker.2 <| congr(Subtype.val ∘ $(LinearMap.mem_ker.1 x.2))⟩,
    oneCycles_ext fun g => (x g).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ⟨fun g => ⟨x.1.1 g, congr_fun congr(Subtype.val $(LinearMap.mem_ker.1 x.2)) g⟩,
    LinearMap.mem_ker.2 <| funext fun g => Subtype.ext <| funext_iff.1 x.1.2 g⟩
  left_inv _ := rfl
  right_inv _ := rfl-/

abbrev twoCyclesKerLequiv {X Y : Rep k G} (f : X ⟶ Y) :
    twoCycles (Rep.ker f) ≃ₗ[k] LinearMap.ker ((twoCyclesFunctor k G).map f).hom :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict _ ((twoCyclesFunctor k G).map (Rep.kerSubtype f)).hom fun x =>
      twoCycles_ext fun g h => (x (g, h)).2)
    (LinearMap.codRestrict _ (LinearMap.pi fun g => LinearMap.restrict
      (LinearMap.proj g ∘ₗ Submodule.subtype _) fun _ hx => funext_iff.1 (Subtype.ext_iff.1 hx) g)
      fun x => LinearMap.mem_ker.2 <| funext fun g => Subtype.ext <| funext_iff.1 x.1.2 g) rfl rfl

instance : (oneCyclesFunctor k G).Additive where

instance : PreservesFiniteLimits (oneCyclesFunctor k G) :=
  letI : ∀ {X Y : Rep k G} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (oneCyclesFunctor k G) := by
    intro X Y f
    apply preservesLimit_of_preserves_limit_cone (Rep.instKerIsLimit _)
    refine (ModuleCat.kernelIsLimit <| ((oneCyclesFunctor k G).map f)).equivOfNatIsoOfIso
      ?_ _ _ ?_
    · exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _))
        (by rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl)
    · exact Cones.ext (oneCyclesKerLequiv f).symm.toModuleIso (by rintro (_ | _) <;> rfl)
  Functor.preservesFiniteLimits_of_preservesKernels _

instance : (twoCyclesFunctor k G).Additive where

instance : PreservesFiniteLimits (twoCyclesFunctor k G) :=
  letI : ∀ {X Y : Rep k G} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) (twoCyclesFunctor k G) := by
    intro X Y f
    apply preservesLimit_of_preserves_limit_cone (Rep.instKerIsLimit _)
    refine (ModuleCat.kernelIsLimit <| ((twoCyclesFunctor k G).map f)).equivOfNatIsoOfIso
      ?_ _ _ ?_
    · exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _))
        (by rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl)
    · exact Cones.ext (twoCyclesKerLequiv f).symm.toModuleIso (by rintro (_ | _) <;> rfl)
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

variable (k G) in
@[simps]
def H0ιNatTrans : Rep.invariantsFunctor k G ⟶ Action.forget _ _ where
  app X := H0ι X

instance : Mono (H0ιNatTrans k G) where
  right_cancellation {Z} f g h := by
    ext X : 2
    have := congr(NatTrans.app $h X)
    rw [← cancel_mono (H0ι X)]
    exact this

variable (k G) in
@[simps]
def H1πNatTrans : oneCyclesFunctor k G ⟶ H1Functor k G where
  app X := H1π X

variable (k G) in
@[simps]
def H2πNatTrans : twoCyclesFunctor k G ⟶ H2Functor k G where
  app X := H2π X

instance : (H1Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := by rw [← cancel_epi (H1π _)]; rfl

instance : (H2Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := by rw [← cancel_epi (H2π _)]; rfl

variable (k G) in
@[simps]
def dZeroNatTrans : Action.forget _ _ ⟶ oneCyclesFunctor k G where
  app X := (shortComplexH1 X).moduleCatLeftHomologyData.f'
  naturality X Y f := by
    simp only [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 Y)).i,
      Category.assoc, LeftHomologyData.f'_i, oneCyclesFunctor_map,
      f'_cyclesMap', Action.forget_obj, Action.forget_map, mapShortComplexH1_τ₁]

variable (k G) in
@[simps]
def oneOpcyclesFunctor : Rep k G ⥤ ModuleCat k where
  obj X := (shortComplexH1 X).moduleCatRightHomologyData.Q
  map f := (moduleCatRightHomologyMapData (mapShortComplexH1 (MonoidHom.id G) f)).φQ
  map_id _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl
  map_comp _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

instance : (oneOpcyclesFunctor k G).Additive where
  map_add := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

abbrev oneOpcyclesCokerLequiv {X Y : Rep k G} (f : X ⟶ Y) :
    (_ ⧸ oneBoundaries (Rep.coker f)) ≃ₗ[k]
      _ ⧸ LinearMap.range ((oneOpcyclesFunctor k G).map f).hom :=
  (LinearEquiv.ofBijective (Submodule.liftQ _
    ((oneOpcyclesFunctor k G).map <| Rep.cokerMkQ _).hom <| by
      rintro x ⟨y, rfl⟩; exact Submodule.Quotient.induction_on _ y fun y =>
      ((Submodule.Quotient.mk_eq_zero _).2 ⟨0, funext fun g => Eq.symm <|
      (Submodule.Quotient.eq _).2 ⟨y g, by simp only [shortComplexH1, map_zero, sub_zero]; rfl⟩⟩))
    ⟨(injective_iff_map_eq_zero _).2 fun a => Submodule.Quotient.induction_on _ a fun x =>
      Submodule.Quotient.induction_on _ x fun x hx => by
        rcases (Submodule.Quotient.mk_eq_zero _).1 hx with ⟨y, hy⟩
        induction y using Submodule.Quotient.induction_on with | @H y =>
        choose z hz using fun g => (Submodule.Quotient.eq _).1 (funext_iff.1 hy g)
        exact (Submodule.Quotient.mk_eq_zero _).2 ⟨-Submodule.Quotient.mk z, Eq.symm <|
          (Submodule.Quotient.eq _).2 ⟨y, funext fun g => by
          simpa using (add_eq_of_eq_sub' (hz g)).symm⟩⟩,
    fun x => Submodule.Quotient.induction_on _ x fun x => by
      choose y hy using Submodule.mkQ_surjective (LinearMap.range f.hom.hom)
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk fun g => y (x g)),
        (Submodule.Quotient.eq _).2 ⟨0, funext fun g => by simp_all [shortComplexH1]⟩⟩⟩).symm

instance : PreservesFiniteColimits (oneOpcyclesFunctor k G) :=
  letI : ∀ {X Y : Rep k G} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) (oneOpcyclesFunctor k G) := by
    intro X Y f
    apply preservesColimit_of_preserves_colimit_cocone (Rep.instCokerIsColimit _)
    refine (ModuleCat.cokernelIsColimit <| ((oneOpcyclesFunctor k G).map f)).equivOfNatIsoOfIso
      ?_ _ _ ?_
    · exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _)) (by
        rintro (_ | _) (_ | _) ⟨_⟩ <;> exact ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl)
    · exact Cocones.ext (oneOpcyclesCokerLequiv f).symm.toModuleIso (by
        rintro (_ | _) <;> exact ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl)
  Functor.preservesFiniteColimits_of_preservesCokernels _

variable (k G) in
@[simps]
def H1ιNatTrans : H1Functor k G ⟶ oneOpcyclesFunctor k G where
  app X := ModuleCat.ofHom <| Submodule.mapQ _ _ (Submodule.subtype _)
    fun x ⟨y, hy⟩ => ⟨y, Subtype.ext_iff.1 hy⟩
  naturality _ _ _ := by rw [← cancel_epi (H1π _)]; rfl

variable (X) in
omit hX in
@[simp]
lemma mapNatTrans_dZero_comp_mapNatTrans_H1π :
    X.mapNatTrans (dZeroNatTrans k G) ≫ X.mapNatTrans (H1πNatTrans k G) = 0 := by
  ext : 3 <;> exact (Submodule.Quotient.mk_eq_zero _).2 <| Set.mem_range_self _

variable (X) in
omit hX in
@[simp]
lemma mapNatTrans_H0ι_comp_mapNatTrans_dZero :
    X.mapNatTrans (H0ιNatTrans k G) ≫ X.mapNatTrans (dZeroNatTrans k G) = 0 := by
  ext : 1 <;> exact (cancel_mono (shortComplexH1 _).moduleCatLeftHomologyData.i).1 <|
    ModuleCat.hom_ext <| dZero_comp_subtype _

variable (k G) in
@[simps]
def dOneNatTrans : oneOpcyclesFunctor k G ⟶ twoCyclesFunctor k G where
  app X := (shortComplexH2 X).moduleCatLeftHomologyData.liftK
    ((shortComplexH1 X).moduleCatRightHomologyData.descQ (ModuleCat.ofHom <| dOne X) <|
    ModuleCat.hom_ext <| dOne_comp_dZero _) <| ModuleCat.hom_ext <|
    Submodule.linearMap_qext _ <| dTwo_comp_dOne _
  naturality _ _ _ := by
    simpa [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 _)).i,
      ← cancel_epi (moduleCatRightHomologyData _).p, -moduleCatLeftHomologyData_K,
      -moduleCatLeftHomologyData_i] using (mapShortComplexH1 (MonoidHom.id G) _).comm₂₃

variable (X) in
omit hX in
@[simp]
lemma mapNatTrans_dOne_comp_mapNatTrans_H2π :
    X.mapNatTrans (dOneNatTrans k G) ≫ X.mapNatTrans (H2πNatTrans k G) = 0 := by
  ext : 1 <;>
  rw [← cancel_epi (moduleCatRightHomologyData (shortComplexH1 _)).p] <;>
  ext <;>
  exact (Submodule.Quotient.mk_eq_zero _).2 <| Set.mem_range_self _

variable (X) in
omit hX in
@[simp]
lemma mapNatTrans_H1ι_comp_mapNatTrans_dOne :
    X.mapNatTrans (H1ιNatTrans k G) ≫ X.mapNatTrans (dOneNatTrans k G) = 0 := by
  ext : 1 <;>
  rw [← cancel_epi (H1π _), ← cancel_mono (shortComplexH2 _).moduleCatLeftHomologyData.i] <;>
  ext <;>
  exact oneCycles.dOne_apply _

omit hX in
lemma ker_shortComplexH1_f'_hom_eq_invariants (A : Rep k G) :
    LinearMap.ker (shortComplexH1 A).moduleCatLeftHomologyData.f'.hom = A.ρ.invariants := by
  show LinearMap.ker (LinearMap.codRestrict _ _ _) = _
  rw [LinearMap.ker_codRestrict]
  exact dZero_ker_eq_invariants _

variable (X) in
def isLimitOfιMapNatTransH0ι :
    IsLimit (F := (parallelPair (X.mapNatTrans <| dZeroNatTrans k G) 0))
      (KernelFork.ofι (X.mapNatTrans (H0ιNatTrans k G))
      (mapNatTrans_H0ι_comp_mapNatTrans_dZero _)) := by
  refine isLimitOfIsLimitπ _
    ((ModuleCat.kernelIsLimit <| (dZeroNatTrans k G).app X.X₁).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.kernelIsLimit <| (dZeroNatTrans k G).app X.X₂).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.kernelIsLimit <| (dZeroNatTrans k G).app X.X₃).equivOfNatIsoOfIso ?_ _ _ ?_) <;>
  try { exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _)) (by
        rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl) } <;>
  exact Cones.ext (LinearEquiv.ofEq _ _ <| ker_shortComplexH1_f'_hom_eq_invariants _).toModuleIso
    (by rintro (_ | _) <;> rfl)

variable (X) in
def isColimitOfπMapNatTransH1π :
    IsColimit (F := (parallelPair (X.mapNatTrans <| dZeroNatTrans k G) 0))
      (CokernelCofork.ofπ (X.mapNatTrans <| H1πNatTrans k G)
        (mapNatTrans_dZero_comp_mapNatTrans_H1π _)) := by
  refine isColimitOfIsColimitπ _
    ((ModuleCat.cokernelIsColimit ((dZeroNatTrans k G).app X.X₁)).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.cokernelIsColimit ((dZeroNatTrans k G).app X.X₂)).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.cokernelIsColimit ((dZeroNatTrans k G).app X.X₃)).equivOfNatIsoOfIso ?_ _ _ ?_) <;>
  try { exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _)) (by
      rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl) } <;>
  exact Cocones.ext (Iso.refl _) (by rintro (_ | _) <;> rfl)

variable (X) in
def isLimitOfιMapNatTransH1ι :
    IsLimit (F := (parallelPair (X.mapNatTrans <| dOneNatTrans k G) 0))
      (KernelFork.ofι (X.mapNatTrans (H1ιNatTrans k G))
      (mapNatTrans_H1ι_comp_mapNatTrans_dOne _)) := by
  refine isLimitOfIsLimitπ _
    ((ModuleCat.kernelIsLimit <| (dOneNatTrans k G).app X.X₁).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.kernelIsLimit <| (dOneNatTrans k G).app X.X₂).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.kernelIsLimit <| (dOneNatTrans k G).app X.X₃).equivOfNatIsoOfIso ?_ _ _ ?_) <;>
  try { exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _)) (by
        rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl) } <;>
  exact Cones.ext ((LinearEquiv.ofEq _ _ (Submodule.ext fun x => Subtype.ext_iff)).toModuleIso ≪≫
    (shortComplexH1 _).moduleCatHomologyData.iso.symm) (by rintro (_ | _) <;>
      exact (Iso.inv_comp_eq _).1 <| ModuleCat.hom_ext <| Submodule.linearMap_qext _ rfl)

variable (X) in
def isColimitOfπMapNatTransH2π :
    IsColimit (F := (parallelPair (X.mapNatTrans <| dOneNatTrans k G) 0))
      (CokernelCofork.ofπ (X.mapNatTrans <| H2πNatTrans k G)
        (mapNatTrans_dOne_comp_mapNatTrans_H2π _)) := by
  refine isColimitOfIsColimitπ _
    ((ModuleCat.cokernelIsColimit ((dOneNatTrans k G).app X.X₁)).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.cokernelIsColimit ((dOneNatTrans k G).app X.X₂)).equivOfNatIsoOfIso ?_ _ _ ?_)
    ((ModuleCat.cokernelIsColimit ((dOneNatTrans k G).app X.X₃)).equivOfNatIsoOfIso ?_ _ _ ?_) <;>
  try { exact NatIso.ofComponents (WalkingParallelPair.rec (Iso.refl _) (Iso.refl _)) (by
      rintro (_ | _) (_ | _) ⟨_⟩ <;> rfl) } <;>
  exact Cocones.ext (LinearEquiv.toModuleIso <| Submodule.quotEquivOfEq _ _ <| by
      show LinearMap.range ((Submodule.liftQ _ _ _).codRestrict _ _) =
        LinearMap.range (LinearMap.codRestrict _ _ _)
      simp [LinearMap.range_codRestrict, Submodule.range_liftQ, shortComplexH2])
    (by rintro (_ | _) <;> rfl)

def snakeInput₀ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput
    (Action.forget _ _) (oneCyclesFunctor k G) X hX (dZeroNatTrans k G)
    (X.mapNatTrans <| H0ιNatTrans k G) (mapNatTrans_H0ι_comp_mapNatTrans_dZero _)
      (isLimitOfιMapNatTransH0ι X) (X.mapNatTrans <| H1πNatTrans k G)
        (mapNatTrans_dZero_comp_mapNatTrans_H1π _) <| isColimitOfπMapNatTransH1π _

def snakeInput₁ : SnakeInput (ModuleCat k) :=
  CategoryTheory.ShortComplex.natTransSnakeInput (oneOpcyclesFunctor k G) (twoCyclesFunctor k G)
    X hX (dOneNatTrans k G) (X.mapNatTrans <| H1ιNatTrans k G)
    (mapNatTrans_H1ι_comp_mapNatTrans_dOne _) (isLimitOfιMapNatTransH1ι X)
    (X.mapNatTrans <| H2πNatTrans k G) (mapNatTrans_dOne_comp_mapNatTrans_H2π _) <|
      isColimitOfπMapNatTransH2π _


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

theorem δOne_apply (z : oneCycles X.X₃) (y : G → X.X₂) (hy : X.g.hom ∘ y = z)
    (x : G × G → X.X₁) (hx : X.f.hom ∘ x = dOne X.X₂ y) :
    δOne hX (H1π X.X₃ z) = H2π X.X₁ ⟨x, δOne_apply_aux hX y x hx⟩ :=
  (snakeInput₁ hX).δ_apply (H1π _ z) (Submodule.mkQ _ y) ⟨x, δOne_apply_aux hX y x hx⟩
    congr(Submodule.Quotient.mk $hy) (Subtype.ext hx)

instance : (oneCyclesFunctor k G).PreservesZeroMorphisms where
  map_zero _ _ := rfl

instance : (H1Functor k G).PreservesZeroMorphisms where
  map_zero _ _ := ModuleCat.hom_ext <| Submodule.linearMap_qext _ <| rfl

end
end groupHomology
