/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is
the equalizer of `f` and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

The basic definitions are
* `kernel : (X ⟶ Y) → C`

* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts, we prove
* `kernel.ιZeroIsIso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.ofMono`: the kernel of a monomorphism is the zero object
* `kernel.liftMono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.isLimitConeZeroCone`: if our category has a zero object, then the map from the zero
  object is a kernel map of any monomorphism
* `kernel.ιOfZero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

and the corresponding dual statements.

## Future work
* TODO: connect this with existing work in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

@[expose] public section


noncomputable section

universe v v₂ u u' u₂

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable [HasZeroMorphisms C]

/-- A morphism `f` has a kernel if the functor `ParallelPair f 0` has a limit. -/
@[to_dual /-- A morphism `f` has a cokernel if the functor `ParallelPair f 0` has a colimit. -/]
abbrev HasKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasLimit (parallelPair f 0)

variable {X Y : C} (f : X ⟶ Y)

section

/-- A kernel fork is just a fork where the second morphism is a zero morphism. -/
@[to_dual /-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/]
abbrev KernelFork :=
  Fork f 0

variable {f}

@[to_dual (attr := reassoc (attr := simp))]
theorem KernelFork.condition (s : KernelFork f) : Fork.ι s ≫ f = 0 := by
  rw [Fork.condition, HasZeroMorphisms.comp_zero]

to_dual_name_hint Epi Mono, π ι, Lift Desc

@[to_dual app_zero]
theorem KernelFork.app_one (s : KernelFork f) : s.π.app one = 0 := by
  simp

/-- A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`. -/
@[to_dual /-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/]
abbrev KernelFork.ofι {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : KernelFork f :=
  Fork.ofι ι <| by rw [w, HasZeroMorphisms.comp_zero]

@[to_dual (attr := simp)]
theorem KernelFork.ι_ofι {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) :
    Fork.ι (KernelFork.ofι ι w) = ι := rfl

section

attribute [local aesop safe cases] WalkingParallelPair WalkingParallelPairHom

/-- Every kernel fork `s` is isomorphic (actually, equal) to `fork.ofι (fork.ι s) _`. -/
@[to_dual
/-- Every cokernel cofork `s` is isomorphic (actually, equal) to `cofork.ofπ (cofork.π s) _`. -/]
def isoOfι (s : Fork f 0) : s ≅ Fork.ofι (Fork.ι s) (Fork.condition s) :=
  Cone.ext (Iso.refl _) <| by aesop

/-- If `ι = ι'`, then `fork.ofι ι _` and `fork.ofι ι' _` are isomorphic. -/
@[to_dual
/-- If `π = π'`, then `CokernelCofork.of_π π _` and `CokernelCofork.of_π π' _` are isomorphic. -/]
def ofιCongr {P : C} {ι ι' : P ⟶ X} {w : ι ≫ f = 0} (h : ι = ι') :
    KernelFork.ofι ι w ≅ KernelFork.ofι ι' (by rw [← h, w]) :=
  Cone.ext (Iso.refl _)

/-- If `F` is an equivalence, then applying `F` to a diagram indexing a (co)kernel of `f` yields
the diagram indexing the (co)kernel of `F.map f`. -/
def compNatIso {D : Type u'} [Category.{v} D] [HasZeroMorphisms D] (F : C ⥤ D) [F.IsEquivalence] :
    parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
  let app (j : WalkingParallelPair) :
      (parallelPair f 0 ⋙ F).obj j ≅ (parallelPair (F.map f) 0).obj j :=
    match j with
    | zero => Iso.refl _
    | one => Iso.refl _
  NatIso.ofComponents app <| by rintro ⟨i⟩ ⟨j⟩ <;> rintro (g | g) <;> aesop

end

insert_to_dual_translation CategoryTheory.Limits.KernelFork.IsLimit
  CategoryTheory.Limits.CokernelCofork.IsColimit

/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies `k ≫ f = 0`, then there is some
`l : W ⟶ s.X` such that `l ≫ fork.ι s = k`. -/
@[to_dual
/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
`l : s.X ⟶ W` such that `cofork.π s ≫ l = k`. -/]
def KernelFork.IsLimit.lift' {s : KernelFork f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = 0) : { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
  ⟨hs.lift <| KernelFork.ofι _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[to_dual
/-- This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/]
def isLimitAux (t : KernelFork f) (lift : ∀ s : KernelFork f, s.pt ⟶ t.pt)
    (fac : ∀ s : KernelFork f, lift s ≫ t.ι = s.ι)
    (uniq : ∀ (s : KernelFork f) (m : s.pt ⟶ t.pt) (_ : m ≫ t.ι = s.ι), m = lift s) : IsLimit t :=
  { lift
    fac := fun s j => by
      cases j
      · exact fac s
      · simp
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.zero) }

/-- This is a more convenient formulation to show that a `KernelFork` constructed using
`KernelFork.ofι` is a limit cone.
-/
@[to_dual
/-- This is a more convenient formulation to show that a `CokernelCofork` constructed using
`CokernelCofork.ofπ` is a limit cone.
-/]
def KernelFork.IsLimit.ofι {W : C} (g : W ⟶ X) (eq : g ≫ f = 0)
    (lift : ∀ {W' : C} (g' : W' ⟶ X) (_ : g' ≫ f = 0), W' ⟶ W)
    (fac : ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0), lift g' eq' ≫ g = g')
    (uniq :
      ∀ {W' : C} (g' : W' ⟶ X) (eq' : g' ≫ f = 0) (m : W' ⟶ W) (_ : m ≫ g = g'), m = lift g' eq') :
    IsLimit (KernelFork.ofι g eq) :=
  isLimitAux _ (fun s => lift s.ι s.condition) (fun s => fac s.ι s.condition) fun s =>
    uniq s.ι s.condition

/-- This is a more convenient formulation to show that a `KernelFork` of the form
`KernelFork.ofι i _` is a limit cone when we know that `i` is a monomorphism. -/
@[to_dual (rename := i → p)
/-- This is a more convenient formulation to show that a `CokernelCofork` of the form
`CokernelCofork.ofπ p _` is a colimit cocone when we know that `p` is an epimorphism. -/]
def KernelFork.IsLimit.ofι' {X Y K : C} {f : X ⟶ Y} (i : K ⟶ X) (w : i ≫ f = 0)
    (h : ∀ {A : C} (k : A ⟶ X) (_ : k ≫ f = 0), { l : A ⟶ K // l ≫ i = k}) [hi : Mono i] :
    IsLimit (KernelFork.ofι i w) :=
  ofι _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_mono i, (h k hk).2, hm])

/-- Every kernel of `f` induces a kernel of `f ≫ g` if `g` is mono. -/
@[to_dual isCokernelEpiComp
/-- Every cokernel of `f` induces a cokernel of `g ≫ f` if `g` is epi. -/]
def isKernelCompMono {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g] {h : X ⟶ Z}
    (hh : h = f ≫ g) : IsLimit (KernelFork.ofι c.ι (by simp [hh]) : KernelFork h) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : KernelFork f := Fork.ofι s.ι (by rw [← cancel_mono g]; simp [← hh, s.condition])
    let l := KernelFork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

@[to_dual isCokernelEpiComp_desc]
theorem isKernelCompMono_lift {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g]
    {h : X ⟶ Z} (hh : h = f ≫ g) (s : KernelFork h) :
    (isKernelCompMono i g hh).lift s = i.lift (Fork.ofι s.ι (by
      rw [← cancel_mono g, Category.assoc, ← hh]
      simp)) := rfl

/-- Every kernel of `f ≫ g` is also a kernel of `f`, as long as `c.ι ≫ f` vanishes. -/
@[to_dual
/-- Every cokernel of `g ≫ f` is also a cokernel of `f`, as long as `f ≫ c.π` vanishes. -/]
def isKernelOfComp {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : KernelFork h} (i : IsLimit c)
    (hf : c.ι ≫ f = 0) (hfg : f ≫ g = h) : IsLimit (KernelFork.ofι c.ι hf) :=
  Fork.IsLimit.mk _ (fun s => i.lift (KernelFork.ofι s.ι (by simp [← hfg])))
    (fun s => by simp only [KernelFork.ι_ofι, Fork.IsLimit.lift_ι]) fun s m h => by
    apply Fork.IsLimit.hom_ext i; simpa using h

/-- `X` identifies to the kernel of a zero map `X ⟶ Y`. -/
@[to_dual /-- `X` identifies to the cokernel of a zero map `Y ⟶ X`. -/]
def KernelFork.IsLimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsLimit (KernelFork.ofι (𝟙 X) (show 𝟙 X ≫ f = 0 by rw [hf, comp_zero])) :=
  KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => Category.comp_id _)
    (fun _ _ _ hb => by simp only [← hb, Category.comp_id])

/-- Any zero object identifies to the kernel of a given monomorphisms. -/
@[to_dual /-- Any zero object identifies to the cokernel of a given epimorphisms. -/]
def KernelFork.IsLimit.ofMonoOfIsZero {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hf : Mono f) (h : IsZero c.pt) : IsLimit c :=
  isLimitAux _ (fun _ => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)

@[to_dual]
lemma KernelFork.IsLimit.isIso_ι {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hc : IsLimit c) (hf : f = 0) : IsIso c.ι := isIso_limit_cone_parallelPair_of_eq hf hc

/-- If `c` is a limit kernel fork for `g : X ⟶ Y`, `e : X ≅ X'` and `g' : X' ⟶ Y` is a morphism,
then there is a limit kernel fork for `g'` with the same point as `c` if for any
morphism `φ : W ⟶ X`, there is an equivalence `φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0`. -/
@[to_dual none]
def KernelFork.isLimitOfIsLimitOfIff {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
    {X' Y' : C} (g' : X' ⟶ Y') (e : X ≅ X')
    (iff : ∀ ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') (c.ι ≫ e.hom) (by simp [← iff])) :=
  KernelFork.IsLimit.ofι _ _
    (fun s hs ↦ hc.lift (KernelFork.ofι (ι := s ≫ e.inv)
      (by rw [iff, Category.assoc, Iso.inv_hom_id_assoc, hs])))
    (fun s hs ↦ by simp)
    (fun s hs m hm ↦ Fork.IsLimit.hom_ext hc (by simpa [← cancel_mono e.hom] using hm))

/-- If `c` is a limit kernel fork for `g : X ⟶ Y`, and `g' : X ⟶ Y'` is another morphism,
then there is a limit kernel fork for `g'` with the same point as `c` if for any
morphism `φ : W ⟶ X`, there is an equivalence `φ ≫ g = 0 ↔ φ ≫ g' = 0`. -/
@[to_dual
/-- If `c` is a colimit cokernel cofork for `g : Y ⟶ X`, and `g' : Y' ⟶ X` is another
morphism, then there is a colimit cokernel cofork for `g'` with the same point as `c` if for any
morphism `φ : X ⟶ W`, there is an equivalence `g ≫ φ = 0 ↔ g' ≫ φ = 0`. -/]
def KernelFork.isLimitOfIsLimitOfIff' {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
    {Y' : C} (g' : X ⟶ Y')
    (iff : ∀ ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') c.ι (by simp [← iff])) :=
  IsLimit.ofIsoLimit (isLimitOfIsLimitOfIff hc g' (Iso.refl _) (by simpa using iff))
    (Fork.ext (Iso.refl _))

@[to_dual]
lemma KernelFork.IsLimit.isZero_of_mono {X Y : C} {f : X ⟶ Y}
    {c : KernelFork f} (hc : IsLimit c) [Mono f] : IsZero c.pt := by
  have := Fork.IsLimit.mono hc
  rw [IsZero.iff_id_eq_zero, ← cancel_mono c.ι, ← cancel_mono f, Category.assoc,
    Category.assoc, c.condition, comp_zero, zero_comp]

end

namespace KernelFork

variable {f} {X' Y' : C} {f' : X' ⟶ Y'}

/-- The morphism between points of kernel forks induced by a morphism
in the category of arrows. -/
@[to_dual (reorder := kf hf' kf')
/-- The morphism between points of cokernel coforks induced by a morphism
in the category of arrows. -/]
def mapOfIsLimit (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') : kf.pt ⟶ kf'.pt :=
  hf'.lift (KernelFork.ofι (kf.ι ≫ φ.left) (by simp))

@[to_dual (attr := reassoc (attr := simp)) π_mapOfIsColimit]
lemma mapOfIsLimit_ι (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') :
    kf.mapOfIsLimit hf' φ ≫ kf'.ι = kf.ι ≫ φ.left :=
  hf'.fac _ _

/-- The isomorphism between points of limit kernel forks induced by an isomorphism
in the category of arrows. -/
@[to_dual (attr := simps)
/-- The isomorphism between points of limit cokernel coforks induced by an isomorphism
in the category of arrows. -/]
def mapIsoOfIsLimit {kf : KernelFork f} {kf' : KernelFork f'}
    (hf : IsLimit kf) (hf' : IsLimit kf')
    (φ : Arrow.mk f ≅ Arrow.mk f') : kf.pt ≅ kf'.pt where
  hom := kf.mapOfIsLimit hf' φ.hom
  inv := kf'.mapOfIsLimit hf φ.inv
  hom_inv_id := Fork.IsLimit.hom_ext hf (by simp)
  inv_hom_id := Fork.IsLimit.hom_ext hf' (by simp)

end KernelFork

section

variable [HasKernel f]

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
@[to_dual /-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/]
abbrev kernel (f : X ⟶ Y) [HasKernel f] : C :=
  equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
@[to_dual /-- The map from the target of `f` to `cokernel f`. -/]
abbrev kernel.ι : kernel f ⟶ X :=
  equalizer.ι f 0

@[to_dual (attr := simp)]
theorem equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f := rfl

@[to_dual (attr := reassoc (attr := simp))]
theorem kernel.condition : kernel.ι f ≫ f = 0 :=
  KernelFork.condition _

/-- The kernel built from `kernel.ι f` is limiting. -/
@[to_dual /-- The cokernel built from `cokernel.π f` is colimiting. -/]
def kernelIsKernel : IsLimit (Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
via `kernel.lift : W ⟶ kernel f`. -/
@[to_dual
/-- Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `cokernel.π f`
via `cokernel.desc : cokernel f ⟶ W`. -/]
abbrev kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
  (kernelIsKernel f).lift (KernelFork.ofι k h)

@[to_dual (attr := reassoc (attr := simp)) π_desc]
theorem kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
  (kernelIsKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

@[to_dual (attr := simp)]
theorem kernel.lift_zero {W : C} {h} : kernel.lift f (0 : W ⟶ X) h = 0 := by
  ext; simp only [equalizer_as_kernel, lift_ι, zero_comp]

@[to_dual]
instance kernel.lift_mono {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [Mono k] : Mono (kernel.lift f k h) :=
  ⟨fun {Z} g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [Category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
`l ≫ kernel.ι f = k`. -/
@[to_dual
/-- Any morphism `k : X ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
`cokernel.π f ≫ l = k`. -/]
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : { l : W ⟶ kernel f // l ≫ kernel.ι f = k } :=
  ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

/-- A commuting square induces a morphism of kernels. -/
@[to_dual /-- A commuting square induces a morphism of cokernels. -/]
abbrev kernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])

@[to_dual (attr := simp)]
lemma kernel.map_id {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
    (w : f ≫ q = 𝟙 _ ≫ f) : kernel.map f f (𝟙 _) q w = 𝟙 _ := by
  cat_disch

@[to_dual]
instance {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') [IsIso p] [Mono q] :
    IsIso (kernel.map _ _ _ _ w) :=
  ⟨kernel.lift _ (kernel.ι f' ≫ inv p) (by simp [← cancel_mono q, w]),
    by cat_disch, by cat_disch⟩

/-- Given a commutative diagram
```
    X --f--> Y --g--> Z
    |        |        |
    |        |        |
    v        v        v
    X' -f'-> Y' -g'-> Z'
```
with horizontal arrows composing to zero,
then we obtain a commutative square
```
   X ---> kernel g
   |         |
   |         | kernel.map
   |         |
   v         v
   X' --> kernel g'
```
-/
@[to_dual map_desc
/-- Given a commutative diagram
```
    X <--f-- Y <--g-- Z
    ∧        ∧        ∧
    |        |        |
    |        |        |
    X' <-f'- Y' <-g'- Z'
```
with horizontal arrows composing to zero,
then we obtain a commutative square
```
   cokernel f <--- Z
   ∧               ∧
   | cokernel.map  |
   |               |
   |               |
   cokernel f' <-- Z'
```
-/]
theorem kernel.lift_map {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') [HasKernel g'] (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y')
    (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' := by
  ext; simp [h₁]

@[to_dual (attr := simp)]
lemma kernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f']
    (q : Y ⟶ Y') (w : f ≫ q = 0 ≫ f') : kernel.map f f' 0 q w = 0 := by
  cat_disch

/-- A commuting square of isomorphisms induces an isomorphism of kernels. -/
@[to_dual (attr := simps)
/-- A commuting square of isomorphisms induces an isomorphism of cokernels. -/]
def kernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') : kernel f ≅ kernel f' where
  hom := kernel.map f f' p.hom q.hom w
  inv :=
    kernel.map f' f p.inv q.inv
      (by
        refine (cancel_mono q.hom).1 ?_
        simp [w])

/-- Every kernel of the zero morphism is an isomorphism -/
@[to_dual /-- The cokernel of the zero morphism is an isomorphism -/]
instance kernel.ι_zero_isIso : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _

@[to_dual]
theorem eq_zero_of_epi_kernel [Epi (kernel.ι f)] : f = 0 :=
  (cancel_epi (kernel.ι f)).1 (by simp)

/-- The kernel of a zero morphism is isomorphic to the source. -/
@[to_dual cokernelZeroIsoTarget
/-- The cokernel of a zero morphism is isomorphic to the target. -/]
def kernelZeroIsoSource : kernel (0 : X ⟶ Y) ≅ X :=
  equalizer.isoSourceOfSelf 0

@[to_dual (attr := simp) cokernelZeroIsoTarget_inv]
theorem kernelZeroIsoSource_hom : kernelZeroIsoSource.hom = kernel.ι (0 : X ⟶ Y) := rfl

@[to_dual (attr := simp) cokernelZeroIsoTarget_hom]
theorem kernelZeroIsoSource_inv :
    kernelZeroIsoSource.inv = kernel.lift (0 : X ⟶ Y) (𝟙 X) (by simp) := by
  ext
  simp [kernelZeroIsoSource]

/-- If two morphisms are known to be equal, then their kernels are isomorphic. -/
@[to_dual]
def kernelIsoOfEq {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) : kernel f ≅ kernel g :=
  HasLimit.isoOfNatIso (by rw [h])

@[to_dual (attr := simp)]
theorem kernelIsoOfEq_refl {h : f = f} : kernelIsoOfEq h = Iso.refl (kernel f) := by
  ext
  simp [kernelIsoOfEq]

@[to_dual (attr := reassoc (attr := simp)) π_comp_cokernelIsoOfEq_inv]
theorem kernelIsoOfEq_hom_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).hom ≫ kernel.ι g = kernel.ι f := by
  subst h; simp

@[to_dual (attr := reassoc (attr := simp)) π_comp_cokernelIsoOfEq_hom]
theorem kernelIsoOfEq_inv_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).inv ≫ kernel.ι _ = kernel.ι _ := by
  subst h; simp

@[to_dual (attr := reassoc (attr := simp)) cokernelIsoOfEq_inv_comp_desc]
theorem lift_comp_kernelIsoOfEq_hom {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).hom = kernel.lift _ e (by simp [← h, he]) := by
  subst h; simp

@[to_dual (attr := reassoc (attr := simp)) cokernelIsoOfEq_hom_comp_desc]
theorem lift_comp_kernelIsoOfEq_inv {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).inv = kernel.lift _ e (by simp [h, he]) := by
  cases h; simp

@[to_dual (attr := simp)]
theorem kernelIsoOfEq_trans {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g)
    (w₂ : g = h) : kernelIsoOfEq w₁ ≪≫ kernelIsoOfEq w₂ = kernelIsoOfEq (w₁.trans w₂) := by
  cases w₁; simp

variable {f}

@[to_dual]
theorem kernel_not_epi_of_ne_zero (w : f ≠ 0) : ¬Epi (kernel.ι f) := fun _ =>
  w (eq_zero_of_epi_kernel f)

@[deprecated (since := "2026-10-13")] alias kernel_not_epi_of_nonzero := kernel_not_epi_of_ne_zero

@[to_dual]
theorem kernel_not_iso_of_ne_zero (w : f ≠ 0) : IsIso (kernel.ι f) → False := fun _ =>
  kernel_not_epi_of_ne_zero w inferInstance

@[deprecated (since := "2026-10-13")] alias kernel_not_iso_of_nonzero := kernel_not_iso_of_ne_zero

@[to_dual hasCokernel_epi_comp]
instance hasKernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mono g] :
    HasKernel (f ≫ g) :=
  ⟨⟨{   cone := _
        isLimit := isKernelCompMono (limit.isLimit _) g rfl }⟩⟩

/-- When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`. -/
@[to_dual (attr := simps) cokernelEpiComp
/-- When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`. -/]
def kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] :
    kernel (f ≫ g) ≅ kernel f where
  hom :=
    kernel.lift _ (kernel.ι _)
      (by
        rw [← cancel_mono g]
        simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)

-- TODO the remainder of this section has obvious generalizations to `HasEqualizer f g`.
@[to_dual hasCokernel_comp_iso]
instance hasKernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    HasKernel (f ≫ g) where
  exists_limit :=
    ⟨{  cone := KernelFork.ofι (kernel.ι g ≫ inv f) (by simp)
        isLimit := isLimitAux _ (fun s => kernel.lift _ (s.ι ≫ f) (by simp))
            (by simp) fun s (m : _ ⟶ kernel _) w => by
          simp_rw [← w]
          apply equalizer.hom_ext
          simp }⟩

/-- When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`. -/
@[to_dual (attr := simps) cokernelCompIsIso
/-- When `f` is an isomorphism, the cokernel of `g ≫ f` is isomorphic to the cokernel of `g`. -/]
def kernelIsIsoComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    kernel (f ≫ g) ≅ kernel g where
  hom := kernel.lift _ (kernel.ι _ ≫ f) (by simp)
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp)

@[deprecated (since := "2026-07-03")] alias kernel.congr := kernelIsoOfEq

@[to_dual]
lemma isZero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f] :
    IsZero (kernel f) :=
  KernelFork.IsLimit.isZero_of_mono (c := KernelFork.ofι _ (kernel.condition f))
    (kernelIsKernel f)

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The morphism from the zero object determines a cone on a kernel diagram -/
@[to_dual (attr := simps! pt)
/-- The morphism to the zero object determines a cocone on a cokernel diagram -/]
def kernel.zeroKernelFork : KernelFork f :=
  KernelFork.ofι (0 : 0 ⟶ X) zero_comp

@[to_dual (attr := simp)]
lemma kernel.zeroKernelFork_ι : (kernel.zeroKernelFork f).ι = 0 := rfl

/-- The map from the zero object is a kernel of a monomorphism -/
@[to_dual /-- The morphism to the zero object is a cokernel of an epimorphism -/]
def kernel.isLimitConeZeroCone [Mono f] : IsLimit (kernel.zeroKernelFork f) :=
  Fork.IsLimit.mk _ (fun _ => 0)
    (fun s => by
      rw [zero_comp]
      refine (zero_of_comp_mono f ?_).symm
      exact KernelFork.condition _)
    fun _ _ _ => zero_of_to_zero _

/-- The kernel of a monomorphism is isomorphic to the zero object -/
@[to_dual /-- The cokernel of an epimorphism is isomorphic to the zero object -/]
def kernel.ofMono [HasKernel f] [Mono f] : kernel f ≅ 0 :=
  Functor.mapIso (Cone.forget _) <|
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)

/-- The kernel morphism of a monomorphism is a zero morphism -/
@[to_dual /-- The cokernel morphism of an epimorphism is a zero morphism -/]
theorem kernel.ι_of_mono [HasKernel f] [Mono f] : kernel.ι f = 0 :=
  zero_of_source_iso_zero _ (kernel.ofMono f)

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `0 : 0 ⟶ X` is a kernel of `f`. -/
@[to_dual
/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : X ⟶ 0` is a cokernel of `g`. -/]
def zeroKernelOfCancelZero {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0) :
    IsLimit (KernelFork.ofι (0 : 0 ⟶ X) (show 0 ≫ f = 0 by simp)) :=
  Fork.IsLimit.mk _ (fun _ => 0) (fun s => by rw [hf _ _ (KernelFork.condition s), zero_comp])
    fun s m _ => by apply HasZeroObject.to_zero_ext

end HasZeroObject

section Transport

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport an `IsKernel` across isomorphisms. -/
def IsKernel.ofIso {X' Y' : C} {f' : X' ⟶ Y'} {s : KernelFork f} (hs : IsLimit s)
    (s' : KernelFork f') (eX : X ≅ X') (eY : Y ≅ Y') (e : s.pt ≅ s'.pt)
    (H : eX.hom ≫ f' = f ≫ eY.hom) (H' : e.hom ≫ s'.ι = s.ι ≫ eX.hom) :
    IsLimit s' :=
  let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
  IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α s).symm hs) <|
    Cone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, any kernel of `f` is a kernel of `l`. -/
def IsKernel.ofCompIso {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) {s : KernelFork f}
    (hs : IsLimit s) :
    IsLimit
      (KernelFork.ofι (Fork.ι s) <| show Fork.ι s ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
  Fork.IsLimit.mk _ (fun s => hs.lift <| KernelFork.ofι (Fork.ι s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Fork.IsLimit.hom_ext hs
      simpa using h

/-- If `i` is an isomorphism such that `l ≫ i.hom = f`, the kernel of `f` is a kernel of `l`. -/
def kernel.ofCompIso [HasKernel f] {Z : C} (l : X ⟶ Z) (i : Z ≅ Y) (h : l ≫ i.hom = f) :
    IsLimit
      (KernelFork.ofι (kernel.ι f) <| show kernel.ι f ≫ l = 0 by simp [← i.comp_inv_eq.2 h.symm]) :=
  IsKernel.ofCompIso f l i h <| limit.isLimit _

/-- If `s` is any limit kernel cone over `f` and if `i` is an isomorphism such that
`i.hom ≫ s.ι = l`, then `l` is a kernel of `f`. -/
def IsKernel.isoKernel {Z : C} (l : Z ⟶ X) {s : KernelFork f} (hs : IsLimit s) (i : Z ≅ s.pt)
    (h : i.hom ≫ Fork.ι s = l) : IsLimit (KernelFork.ofι l <| show l ≫ f = 0 by simp [← h]) :=
  IsLimit.ofIsoLimit hs <|
    Cone.ext i.symm fun j => by
      cases j
      · exact (Iso.eq_inv_comp i).2 h
      · dsimp; rw [← h]; simp

/-- If `i` is an isomorphism such that `i.hom ≫ kernel.ι f = l`, then `l` is a kernel of `f`. -/
def kernel.isoKernel [HasKernel f] {Z : C} (l : Z ⟶ X) (i : Z ≅ kernel f)
    (h : i.hom ≫ kernel.ι f = l) :
    IsLimit (@KernelFork.ofι _ _ _ _ _ f _ l <| by simp [← h]) :=
  IsKernel.isoKernel f l (limit.isLimit _) i h

end Transport

section

/-- The kernel morphism of a zero morphism is an isomorphism -/
@[to_dual /-- The cokernel morphism of a zero morphism is an isomorphism -/]
theorem kernel.ι_of_zero {f : X ⟶ Y} [HasKernel f] (eq : f = 0) :
    IsIso (kernel.ι f) := equalizer.ι_of_eq eq

end

@[deprecated (since := "2026-11-03")] alias CokernelCofork.π_eq_zero := CokernelCofork.app_zero

/-- If `c` is a colimit cokernel cofork for `f : X ⟶ Y`, `e : Y ≅ Y'` and `f' : X' ⟶ Y` is a
morphism, then there is a colimit cokernel cofork for `f'` with the same point as `c` if for any
morphism `φ : Y ⟶ W`, there is an equivalence `f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0`. -/
@[to_dual none]
def CokernelCofork.isColimitOfIsColimitOfIff {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) {X' Y' : C} (f' : X' ⟶ Y') (e : Y' ≅ Y)
    (iff : ∀ ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') (e.hom ≫ c.π) (by simp [← iff])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun s hs ↦ hc.desc (CokernelCofork.ofπ (π := e.inv ≫ s)
      (by rw [iff, e.hom_inv_id_assoc, hs])))
    (fun s hs ↦ by simp)
    (fun s hs m hm ↦ Cofork.IsColimit.hom_ext hc (by simpa [← cancel_epi e.hom] using hm))

@[deprecated (since := "2026-10-13")]
alias cokernel_not_mono_of_nonzero := cokernel_not_mono_of_ne_zero

@[deprecated (since := "2026-10-13")]
alias cokernel_not_iso_of_nonzero := cokernel_not_iso_of_ne_zero

@[deprecated (since := "2026-07-03")] alias cokernel.congr := cokernelIsoOfEq

section MonoFactorisation

variable {f}

@[simp]
theorem MonoFactorisation.kernel_ι_comp [HasKernel f] (F : MonoFactorisation f) :
    kernel.ι f ≫ F.e = 0 := by
  rw [← cancel_mono F.m, zero_comp, Category.assoc, F.fac, kernel.condition]

end MonoFactorisation

section HasImage

/-- The cokernel of the image inclusion of a morphism `f` is isomorphic to the cokernel of `f`.

(This result requires that the factorisation through the image is an epimorphism.
This holds in any category with equalizers.)
-/
@[simps]
def cokernelImageι {X Y : C} (f : X ⟶ Y) [HasImage f] [HasCokernel (image.ι f)] [HasCokernel f]
    [Epi (factorThruImage f)] : cokernel (image.ι f) ≅ cokernel f where
  hom :=
    cokernel.desc _ (cokernel.π f)
      (by
        have w := cokernel.condition f
        conv at w =>
          lhs
          congr
          rw [← image.fac f]
        rw [← HasZeroMorphisms.comp_zero (Limits.factorThruImage f), Category.assoc,
          cancel_epi] at w
        exact w)
  inv :=
    cokernel.desc _ (cokernel.π _)
      (by
        conv =>
          lhs
          congr
          rw [← image.fac f]
        rw [Category.assoc, cokernel.condition, HasZeroMorphisms.comp_zero])

section

variable (f : X ⟶ Y) [HasKernel f] [HasImage f] [HasKernel (factorThruImage f)]

/-- The kernel of the morphism `X ⟶ image f` is just the kernel of `f`. -/
def kernelFactorThruImage : kernel (factorThruImage f) ≅ kernel f :=
  (kernelCompMono (factorThruImage f) (image.ι f)).symm ≪≫ (kernelIsoOfEq (by simp))

@[reassoc (attr := simp)]
theorem kernelFactorThruImage_hom_comp_ι :
    (kernelFactorThruImage f).hom ≫ kernel.ι f = kernel.ι (factorThruImage f) := by
  simp [kernelFactorThruImage]

@[reassoc (attr := simp)]
theorem kernelFactorThruImage_inv_comp_ι :
    (kernelFactorThruImage f).inv ≫ kernel.ι (factorThruImage f) = kernel.ι f := by
  simp [kernelFactorThruImage]

end

end HasImage

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
@[to_dual /-- The cokernel of the kernel of a monomorphism is an isomorphism -/]
instance kernel.of_cokernel_of_epi [HasCokernel f] [HasKernel (cokernel.π f)] [Epi f] :
    IsIso (kernel.ι (cokernel.π f)) :=
  equalizer.ι_of_eq <| cokernel.π_of_epi f

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : Y ⟶ 0` is a cokernel of `f`. -/
def zeroCokernelOfZeroCancel {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) :
    IsColimit (CokernelCofork.ofπ (0 : Y ⟶ 0) (show f ≫ 0 = 0 by simp)) :=
  Cofork.IsColimit.mk _ (fun _ => 0)
    (fun s => by rw [hf _ _ (CokernelCofork.condition s), comp_zero]) fun s m _ => by
      apply HasZeroObject.from_zero_ext

end HasZeroObject

section Transport

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then any cokernel of `f` is a cokernel of
`l`. -/
def IsCokernel.ofIsoComp {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) {s : CokernelCofork f}
    (hs : IsColimit s) :
    IsColimit
      (CokernelCofork.ofπ (Cofork.π s) <| show l ≫ Cofork.π s = 0 by simp [i.eq_inv_comp.2 h]) :=
  Cofork.IsColimit.mk _ (fun s => hs.desc <| CokernelCofork.ofπ (Cofork.π s) <| by simp [← h])
    (fun s => by simp) fun s m h => by
      apply Cofork.IsColimit.hom_ext hs
      simpa using h

/-- If `i` is an isomorphism such that `i.hom ≫ l = f`, then the cokernel of `f` is a cokernel of
`l`. -/
def cokernel.ofIsoComp [HasCokernel f] {Z : C} (l : Z ⟶ Y) (i : X ≅ Z) (h : i.hom ≫ l = f) :
    IsColimit
      (CokernelCofork.ofπ (cokernel.π f) <|
        show l ≫ cokernel.π f = 0 by simp [i.eq_inv_comp.2 h]) :=
  IsCokernel.ofIsoComp f l i h <| colimit.isColimit _

/-- If `s` is any colimit cokernel cocone over `f` and `i` is an isomorphism such that
`s.π ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def IsCokernel.cokernelIso {Z : C} (l : Y ⟶ Z) {s : CokernelCofork f} (hs : IsColimit s)
    (i : s.pt ≅ Z) (h : Cofork.π s ≫ i.hom = l) :
    IsColimit (CokernelCofork.ofπ l <| show f ≫ l = 0 by simp [← h]) :=
  IsColimit.ofIsoColimit hs <|
    Cocone.ext i fun j => by
      cases j
      · dsimp; rw [← h]; simp
      · exact h

set_option backward.isDefEq.respectTransparency.types false in
/-- Transport an `IsCokernel` across isomorphisms. -/
def IsCokernel.ofIso {X' Y' : C} {f' : X' ⟶ Y'} {s : CokernelCofork f} (hs : IsColimit s)
    (s' : CokernelCofork f') (eX : X ≅ X') (eY : Y ≅ Y') (e : s.pt ≅ s'.pt)
    (H : eX.hom ≫ f' = f ≫ eY.hom) (H' : eY.hom ≫ s'.π = s.π ≫ e.hom) :
    IsColimit s' :=
  let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
  IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv α.symm s).symm hs) <|
    Cocone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

/-- If `i` is an isomorphism such that `cokernel.π f ≫ i.hom = l`, then `l` is a cokernel of `f`. -/
def cokernel.cokernelIso [HasCokernel f] {Z : C} (l : Y ⟶ Z) (i : cokernel f ≅ Z)
    (h : cokernel.π f ≫ i.hom = l) :
    IsColimit (@CokernelCofork.ofπ _ _ _ _ _ f _ l <| by simp [← h]) :=
  IsCokernel.cokernelIso f l (colimit.isColimit _) i h

end Transport

section Comparison

variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
variable (G : C ⥤ D) [Functor.PreservesZeroMorphisms G]

/-- The comparison morphism for the kernel of `f`.
This is an isomorphism iff `G` preserves the kernel of `f`; see
`Mathlib/CategoryTheory/Limits/Preserves/Shapes/Kernels.lean`
-/
@[to_dual /-- The comparison morphism for the cokernel of `f`. -/]
def kernelComparison [HasKernel f] [HasKernel (G.map f)] : G.obj (kernel f) ⟶ kernel (G.map f) :=
  kernel.lift _ (G.map (kernel.ι f))
    (by simp only [← G.map_comp, kernel.condition, Functor.map_zero])

@[to_dual (attr := reassoc (attr := simp)) π_comp_cokernelComparison]
theorem kernelComparison_comp_ι [HasKernel f] [HasKernel (G.map f)] :
    kernelComparison f G ≫ kernel.ι (G.map f) = G.map (kernel.ι f) :=
  kernel.lift_ι _ _ _

@[to_dual (attr := reassoc (attr := simp)) cokernelComparison_map_desc]
theorem map_lift_kernelComparison [HasKernel f] [HasKernel (G.map f)] {Z : C} {h : Z ⟶ X}
    (w : h ≫ f = 0) :
    G.map (kernel.lift _ h w) ≫ kernelComparison f G =
      kernel.lift _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) := by
  ext; simp [← G.map_comp]

@[to_dual (attr := reassoc) cokernel_map_comp_cokernelComparison]
theorem kernelComparison_comp_kernel_map {X' Y' : C} [HasKernel f] [HasKernel (G.map f)]
    (g : X' ⟶ Y') [HasKernel g] [HasKernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernelComparison f G ≫
        kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (kernel.map f g p q hpq) ≫ kernelComparison g G :=
  kernel.lift_map _ _ (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (kernel.lift_ι _ _ _).symm) _

end Comparison

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C]

/-- `HasKernels` represents the existence of kernels for every morphism. -/
class HasKernels : Prop where
  has_limit : ∀ {X Y : C} (f : X ⟶ Y), HasKernel f := by infer_instance

/-- `HasCokernels` represents the existence of cokernels for every morphism. -/
@[to_dual]
class HasCokernels : Prop where
  has_colimit : ∀ {X Y : C} (f : X ⟶ Y), HasCokernel f := by infer_instance

attribute [instance 100] HasKernels.has_limit HasCokernels.has_colimit

@[to_dual]
instance (priority := 100) hasKernels_of_hasEqualizers [HasEqualizers C] : HasKernels C where

section HasKernels
variable [HasKernels C]

/-- The kernel of an arrow is natural. -/
@[to_dual (attr := simps, implicit_reducible) coker /-- The cokernel of an arrow is natural. -/]
noncomputable def ker : Arrow C ⥤ C where
  obj f := kernel f.hom
  map {f g} u := kernel.lift _ (kernel.ι _ ≫ u.left) (by simp)

/-- The kernel inclusion is natural. -/
@[to_dual (attr := simps) /-- The cokernel projection is natural. -/]
def ker.ι : ker (C := C) ⟶ Arrow.leftFunc where app f := kernel.ι _

@[to_dual (attr := reassoc (attr := simp))]
lemma ker.condition : ι C ≫ Arrow.leftToRight = 0 := by cat_disch

end HasKernels

end CategoryTheory.Limits
