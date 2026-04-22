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
* `kernel.ι_zero_isIso`: a kernel map of a zero morphism is an isomorphism
* `kernel.eq_zero_of_epi_kernel`: if `kernel.ι f` is an epimorphism, then `f = 0`
* `kernel.ofMono`: the kernel of a monomorphism is the zero object
* `kernel.lift_mono`: the lift of a monomorphism `k : W ⟶ X` such that `k ≫ f = 0`
  is still a monomorphism
* `kernel.isLimitConeZeroCone`: if our category has a zero object, then the map from the zero
  object is a kernel map of any monomorphism
* `kernel.ι_of_zero`: `kernel.ι (0 : X ⟶ Y)` is an isomorphism

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
abbrev HasKernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasLimit (parallelPair f 0)

/-- A morphism `f` has a cokernel if the functor `ParallelPair f 0` has a colimit. -/
abbrev HasCokernel {X Y : C} (f : X ⟶ Y) : Prop :=
  HasColimit (parallelPair f 0)

variable {X Y : C} (f : X ⟶ Y)

section

/-- A kernel fork is just a fork where the second morphism is a zero morphism. -/
abbrev KernelFork :=
  Fork f 0

variable {f}

@[reassoc (attr := simp)]
theorem KernelFork.condition (s : KernelFork f) : Fork.ι s ≫ f = 0 := by
  rw [Fork.condition, HasZeroMorphisms.comp_zero]

set_option backward.isDefEq.respectTransparency false in
theorem KernelFork.app_one (s : KernelFork f) : s.π.app one = 0 := by
  simp

/-- A morphism `ι` satisfying `ι ≫ f = 0` determines a kernel fork over `f`. -/
abbrev KernelFork.ofι {Z : C} (ι : Z ⟶ X) (w : ι ≫ f = 0) : KernelFork f :=
  Fork.ofι ι <| by rw [w, HasZeroMorphisms.comp_zero]

@[simp]
theorem KernelFork.ι_ofι {X Y P : C} (f : X ⟶ Y) (ι : P ⟶ X) (w : ι ≫ f = 0) :
    Fork.ι (KernelFork.ofι ι w) = ι := rfl

section

attribute [local aesop safe cases] WalkingParallelPair WalkingParallelPairHom

/-- Every kernel fork `s` is isomorphic (actually, equal) to `Fork.ofι (Fork.ι s) _`. -/
def isoOfι (s : Fork f 0) : s ≅ Fork.ofι (Fork.ι s) (Fork.condition s) :=
  Cone.ext (Iso.refl _) <| by aesop

/-- If `ι = ι'`, then `Fork.ofι ι _` and `Fork.ofι ι' _` are isomorphic. -/
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

/-- If `s` is a limit kernel fork and `k : W ⟶ X` satisfies `k ≫ f = 0`, then there is some
`l : W ⟶ s.pt` such that `l ≫ Fork.ι s = k`. -/
def KernelFork.IsLimit.lift' {s : KernelFork f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : k ≫ f = 0) : { l : W ⟶ s.pt // l ≫ Fork.ι s = k } :=
  ⟨hs.lift <| KernelFork.ofι _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a kernel fork is a limit cone. It
only asks for a proof of facts that carry any mathematical content -/
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
def KernelFork.IsLimit.ofι' {X Y K : C} {f : X ⟶ Y} (i : K ⟶ X) (w : i ≫ f = 0)
    (h : ∀ {A : C} (k : A ⟶ X) (_ : k ≫ f = 0), { l : A ⟶ K // l ≫ i = k}) [hi : Mono i] :
    IsLimit (KernelFork.ofι i w) :=
  ofι _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_mono i, (h k hk).2, hm])

set_option backward.isDefEq.respectTransparency false in
/-- Every kernel of `f` induces a kernel of `f ≫ g` if `g` is mono. -/
def isKernelCompMono {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g] {h : X ⟶ Z}
    (hh : h = f ≫ g) : IsLimit (KernelFork.ofι c.ι (by simp [hh]) : KernelFork h) :=
  Fork.IsLimit.mk' _ fun s =>
    let s' : KernelFork f := Fork.ofι s.ι (by rw [← cancel_mono g]; simp [← hh, s.condition])
    let l := KernelFork.IsLimit.lift' i s'.ι s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Fork.IsLimit.hom_ext i; rw [Fork.ι_ofι] at hm; rw [hm]; exact l.2.symm⟩

theorem isKernelCompMono_lift {c : KernelFork f} (i : IsLimit c) {Z} (g : Y ⟶ Z) [hg : Mono g]
    {h : X ⟶ Z} (hh : h = f ≫ g) (s : KernelFork h) :
    (isKernelCompMono i g hh).lift s = i.lift (Fork.ofι s.ι (by
      rw [← cancel_mono g, Category.assoc, ← hh]
      simp)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every kernel of `f ≫ g` is also a kernel of `f`, as long as `c.ι ≫ f` vanishes. -/
def isKernelOfComp {W : C} (g : Y ⟶ W) (h : X ⟶ W) {c : KernelFork h} (i : IsLimit c)
    (hf : c.ι ≫ f = 0) (hfg : f ≫ g = h) : IsLimit (KernelFork.ofι c.ι hf) :=
  Fork.IsLimit.mk _ (fun s => i.lift (KernelFork.ofι s.ι (by simp [← hfg])))
    (fun s => by simp only [KernelFork.ι_ofι, Fork.IsLimit.lift_ι]) fun s m h => by
    apply Fork.IsLimit.hom_ext i; simpa using h

/-- `X` identifies to the kernel of a zero map `X ⟶ Y`. -/
def KernelFork.IsLimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsLimit (KernelFork.ofι (𝟙 X) (show 𝟙 X ≫ f = 0 by rw [hf, comp_zero])) :=
  KernelFork.IsLimit.ofι _ _ (fun x _ => x) (fun _ _ => Category.comp_id _)
    (fun _ _ _ hb => by simp only [← hb, Category.comp_id])

/-- Any zero object identifies to the kernel of a given monomorphisms. -/
def KernelFork.IsLimit.ofMonoOfIsZero {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hf : Mono f) (h : IsZero c.pt) : IsLimit c :=
  isLimitAux _ (fun _ => 0) (fun s => by rw [zero_comp, ← cancel_mono f, zero_comp, s.condition])
    (fun _ _ _ => h.eq_of_tgt _ _)

lemma KernelFork.IsLimit.isIso_ι {X Y : C} {f : X ⟶ Y} (c : KernelFork f)
    (hc : IsLimit c) (hf : f = 0) : IsIso c.ι := isIso_limit_cone_parallelPair_of_eq hf hc

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a limit kernel fork for `g : X ⟶ Y`, `e : X ≅ X'` and `g' : X' ⟶ Y` is a morphism,
then there is a limit kernel fork for `g'` with the same point as `c` if for any
morphism `φ : W ⟶ X`, there is an equivalence `φ ≫ g = 0 ↔ φ ≫ e.hom ≫ g' = 0`. -/
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
def KernelFork.isLimitOfIsLimitOfIff' {X Y : C} {g : X ⟶ Y} {c : KernelFork g} (hc : IsLimit c)
    {Y' : C} (g' : X ⟶ Y')
    (iff : ∀ ⦃W : C⦄ (φ : W ⟶ X), φ ≫ g = 0 ↔ φ ≫ g' = 0) :
    IsLimit (KernelFork.ofι (f := g') c.ι (by simp [← iff])) :=
  IsLimit.ofIsoLimit (isLimitOfIsLimitOfIff hc g' (Iso.refl _) (by simpa using iff))
    (Fork.ext (Iso.refl _))

lemma KernelFork.IsLimit.isZero_of_mono {X Y : C} {f : X ⟶ Y}
    {c : KernelFork f} (hc : IsLimit c) [Mono f] : IsZero c.pt := by
  have := Fork.IsLimit.mono hc
  rw [IsZero.iff_id_eq_zero, ← cancel_mono c.ι, ← cancel_mono f, Category.assoc,
    Category.assoc, c.condition, comp_zero, zero_comp]

end

namespace KernelFork

variable {f} {X' Y' : C} {f' : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between points of kernel forks induced by a morphism
in the category of arrows. -/
def mapOfIsLimit (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') : kf.pt ⟶ kf'.pt :=
  hf'.lift (KernelFork.ofι (kf.ι ≫ φ.left) (by simp))

@[reassoc (attr := simp)]
lemma mapOfIsLimit_ι (kf : KernelFork f) {kf' : KernelFork f'} (hf' : IsLimit kf')
    (φ : Arrow.mk f ⟶ Arrow.mk f') :
    kf.mapOfIsLimit hf' φ ≫ kf'.ι = kf.ι ≫ φ.left :=
  hf'.fac _ _

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between points of limit kernel forks induced by an isomorphism
in the category of arrows. -/
@[simps]
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
abbrev kernel (f : X ⟶ Y) [HasKernel f] : C :=
  equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
abbrev kernel.ι : kernel f ⟶ X :=
  equalizer.ι f 0

@[simp]
theorem equalizer_as_kernel : equalizer.ι f 0 = kernel.ι f := rfl

@[reassoc (attr := simp)]
theorem kernel.condition : kernel.ι f ≫ f = 0 :=
  KernelFork.condition _

/-- The kernel built from `kernel.ι f` is limiting. -/
def kernelIsKernel : IsLimit (Fork.ofι (kernel.ι f) ((kernel.condition f).trans comp_zero.symm)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Fork.ext (Iso.refl _) (by simp))

/-- Given any morphism `k : W ⟶ X` satisfying `k ≫ f = 0`, `k` factors through `kernel.ι f`
via `kernel.lift : W ⟶ kernel f`. -/
abbrev kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
  (kernelIsKernel f).lift (KernelFork.ofι k h)

@[reassoc (attr := simp)]
theorem kernel.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : kernel.lift f k h ≫ kernel.ι f = k :=
  (kernelIsKernel f).fac (KernelFork.ofι k h) WalkingParallelPair.zero

@[simp]
theorem kernel.lift_zero {W : C} {h} : kernel.lift f (0 : W ⟶ X) h = 0 := by
  ext; simp

instance kernel.lift_mono {W : C} (k : W ⟶ X) (h : k ≫ f = 0) [Mono k] : Mono (kernel.lift f k h) :=
  ⟨fun {Z} g g' w => by
    replace w := w =≫ kernel.ι f
    simp only [Category.assoc, kernel.lift_ι] at w
    exact (cancel_mono k).1 w⟩

/-- Any morphism `k : W ⟶ X` satisfying `k ≫ f = 0` induces a morphism `l : W ⟶ kernel f` such that
`l ≫ kernel.ι f = k`. -/
def kernel.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : { l : W ⟶ kernel f // l ≫ kernel.ι f = k } :=
  ⟨kernel.lift f k h, kernel.lift_ι _ _ _⟩

/-- A commuting square induces a morphism of kernels. -/
abbrev kernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f ≫ p) (by simp [← w])

@[simp]
lemma kernel.map_id {X Y : C} (f : X ⟶ Y) [HasKernel f] (q : Y ⟶ Y)
    (w : f ≫ q = 𝟙 _ ≫ f) : kernel.map f f (𝟙 _) q w = 𝟙 _ := by
  cat_disch

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
theorem kernel.lift_map {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel g] (w : f ≫ g = 0)
    (f' : X' ⟶ Y') (g' : Y' ⟶ Z') [HasKernel g'] (w' : f' ≫ g' = 0) (p : X ⟶ X') (q : Y ⟶ Y')
    (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    kernel.lift g f w ≫ kernel.map g g' q r h₂ = p ≫ kernel.lift g' f' w' := by
  ext; simp [h₁]

@[simp]
lemma kernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') [HasKernel f] [HasKernel f']
    (q : Y ⟶ Y') (w : f ≫ q = 0 ≫ f') : kernel.map f f' 0 q w = 0 := by
  cat_disch

/-- A commuting square of isomorphisms induces an isomorphism of kernels. -/
@[simps]
def kernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasKernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') : kernel f ≅ kernel f' where
  hom := kernel.map f f' p.hom q.hom w
  inv :=
    kernel.map f' f p.inv q.inv
      (by
        refine (cancel_mono q.hom).1 ?_
        simp [w])

/-- Every kernel of the zero morphism is an isomorphism -/
instance kernel.ι_zero_isIso : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _

theorem eq_zero_of_epi_kernel [Epi (kernel.ι f)] : f = 0 :=
  (cancel_epi (kernel.ι f)).1 (by simp)

/-- The kernel of a zero morphism is isomorphic to the source. -/
def kernelZeroIsoSource : kernel (0 : X ⟶ Y) ≅ X :=
  equalizer.isoSourceOfSelf 0

@[simp]
theorem kernelZeroIsoSource_hom : kernelZeroIsoSource.hom = kernel.ι (0 : X ⟶ Y) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem kernelZeroIsoSource_inv :
    kernelZeroIsoSource.inv = kernel.lift (0 : X ⟶ Y) (𝟙 X) (by simp) := by
  ext
  simp [kernelZeroIsoSource]

/-- If two morphisms are known to be equal, then their kernels are isomorphic. -/
def kernelIsoOfEq {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) : kernel f ≅ kernel g :=
  HasLimit.isoOfNatIso (by rw [h])

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem kernelIsoOfEq_refl {h : f = f} : kernelIsoOfEq h = Iso.refl (kernel f) := by
  ext
  simp [kernelIsoOfEq]

@[reassoc (attr := simp)]
theorem kernelIsoOfEq_hom_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).hom ≫ kernel.ι g = kernel.ι f := by
  subst h; simp

@[reassoc (attr := simp)]
theorem kernelIsoOfEq_inv_comp_ι {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g) :
    (kernelIsoOfEq h).inv ≫ kernel.ι _ = kernel.ι _ := by
  subst h; simp

@[reassoc (attr := simp)]
theorem lift_comp_kernelIsoOfEq_hom {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).hom = kernel.lift _ e (by simp [← h, he]) := by
  subst h; simp

@[reassoc (attr := simp)]
theorem lift_comp_kernelIsoOfEq_inv {Z} {f g : X ⟶ Y} [HasKernel f] [HasKernel g] (h : f = g)
    (e : Z ⟶ X) (he) :
    kernel.lift _ e he ≫ (kernelIsoOfEq h).inv = kernel.lift _ e (by simp [h, he]) := by
  cases h; simp

@[simp]
theorem kernelIsoOfEq_trans {f g h : X ⟶ Y} [HasKernel f] [HasKernel g] [HasKernel h] (w₁ : f = g)
    (w₂ : g = h) : kernelIsoOfEq w₁ ≪≫ kernelIsoOfEq w₂ = kernelIsoOfEq (w₁.trans w₂) := by
  cases w₁; simp

variable {f}

theorem kernel_not_epi_of_nonzero (w : f ≠ 0) : ¬Epi (kernel.ι f) := fun _ =>
  w (eq_zero_of_epi_kernel f)

theorem kernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (kernel.ι f) → False := fun _ =>
  kernel_not_epi_of_nonzero w inferInstance

instance hasKernel_comp_mono {X Y Z : C} (f : X ⟶ Y) [HasKernel f] (g : Y ⟶ Z) [Mono g] :
    HasKernel (f ≫ g) :=
  ⟨⟨{   cone := _
        isLimit := isKernelCompMono (limit.isLimit _) g rfl }⟩⟩

/-- When `g` is a monomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `f`.
-/
@[simps]
def kernelCompMono {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] :
    kernel (f ≫ g) ≅ kernel f where
  hom :=
    kernel.lift _ (kernel.ι _)
      (by
        rw [← cancel_mono g]
        simp)
  inv := kernel.lift _ (kernel.ι _) (by simp)

instance hasKernel_iso_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    HasKernel (f ≫ g) where
  exists_limit :=
    ⟨{  cone := KernelFork.ofι (kernel.ι g ≫ inv f) (by simp)
        isLimit := isLimitAux _ (fun s => kernel.lift _ (s.ι ≫ f) (by simp))
            (by simp) fun s (m : _ ⟶ kernel _) w => by
          simp_rw [← w]
          apply equalizer.hom_ext
          simp }⟩

/-- When `f` is an isomorphism, the kernel of `f ≫ g` is isomorphic to the kernel of `g`.
-/
@[simps]
def kernelIsIsoComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [HasKernel g] :
    kernel (f ≫ g) ≅ kernel g where
  hom := kernel.lift _ (kernel.ι _ ≫ f) (by simp)
  inv := kernel.lift _ (kernel.ι _ ≫ inv f) (by simp)

/-- Equal maps have isomorphic kernels. -/
@[simps] def kernel.congr {X Y : C} (f g : X ⟶ Y) [HasKernel f] [HasKernel g]
    (h : f = g) : kernel f ≅ kernel g where
  hom := kernel.lift _ (kernel.ι f) (by simp [← h])
  inv := kernel.lift _ (kernel.ι g) (by simp [h])

lemma isZero_kernel_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] [HasKernel f] :
    IsZero (kernel f) :=
  KernelFork.IsLimit.isZero_of_mono (c := KernelFork.ofι _ (kernel.condition f))
    (kernelIsKernel f)

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The morphism from the zero object determines a cone on a kernel diagram -/
@[simps! pt]
def kernel.zeroKernelFork : KernelFork f :=
  KernelFork.ofι (0 : 0 ⟶ X) zero_comp

@[simp]
lemma kernel.zeroKernelFork_ι : (kernel.zeroKernelFork f).ι = 0 := rfl

/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.isLimitConeZeroCone [Mono f] : IsLimit (kernel.zeroKernelFork f) :=
  Fork.IsLimit.mk _ (fun _ => 0)
    (fun s => by
      rw [zero_comp]
      refine (zero_of_comp_mono f ?_).symm
      exact KernelFork.condition _)
    fun _ _ _ => zero_of_to_zero _

/-- The kernel of a monomorphism is isomorphic to the zero object -/
def kernel.ofMono [HasKernel f] [Mono f] : kernel f ≅ 0 :=
  Functor.mapIso (Cone.forget _) <|
    IsLimit.uniqueUpToIso (limit.isLimit (parallelPair f 0)) (kernel.isLimitConeZeroCone f)

/-- The kernel morphism of a monomorphism is a zero morphism -/
theorem kernel.ι_of_mono [HasKernel f] [Mono f] : kernel.ι f = 0 :=
  zero_of_source_iso_zero _ (kernel.ofMono f)

/-- If `g ≫ f = 0` implies `g = 0` for all `g`, then `0 : 0 ⟶ X` is a kernel of `f`. -/
def zeroKernelOfCancelZero {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Z ⟶ X) (_ : g ≫ f = 0), g = 0) :
    IsLimit (KernelFork.ofι (0 : 0 ⟶ X) (show 0 ≫ f = 0 by simp)) :=
  Fork.IsLimit.mk _ (fun _ => 0) (fun s => by rw [hf _ _ (KernelFork.condition s), zero_comp])
    fun s m _ => by dsimp; apply HasZeroObject.to_zero_ext

end HasZeroObject

section Transport

/-- Transport an `IsKernel` across isomorphisms. -/
def IsKernel.ofIso {X' Y' : C} {f' : X' ⟶ Y'} {s : KernelFork f} (hs : IsLimit s)
    (s' : KernelFork f') (eX : X ≅ X') (eY : Y ≅ Y') (e : s.pt ≅ s'.pt)
    (H : eX.hom ≫ f' = f ≫ eY.hom) (H' : e.hom ≫ s'.ι = s.ι ≫ eX.hom) :
    IsLimit s' :=
  let α : parallelPair f 0 ≅ parallelPair f' 0 := parallelPairIsoMk eX eY H.symm (by simp)
  IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv α s).symm hs) <|
    Cone.ext e (by rintro (_ | _) <;> simp [α, ← H'])

set_option backward.isDefEq.respectTransparency false in
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

variable (X Y)

/-- The kernel morphism of a zero morphism is an isomorphism -/
theorem kernel.ι_of_zero : IsIso (kernel.ι (0 : X ⟶ Y)) :=
  equalizer.ι_of_self _

end

section

/-- A cokernel cofork is just a cofork where the second morphism is a zero morphism. -/
abbrev CokernelCofork :=
  Cofork f 0

variable {f}

@[reassoc (attr := simp)]
theorem CokernelCofork.condition (s : CokernelCofork f) : f ≫ s.π = 0 := by
  rw [Cofork.condition, zero_comp]

set_option backward.isDefEq.respectTransparency false in
theorem CokernelCofork.π_eq_zero (s : CokernelCofork f) : s.ι.app zero = 0 := by
  simp

/-- A morphism `π` satisfying `f ≫ π = 0` determines a cokernel cofork on `f`. -/
abbrev CokernelCofork.ofπ {Z : C} (π : Y ⟶ Z) (w : f ≫ π = 0) : CokernelCofork f :=
  Cofork.ofπ π <| by rw [w, zero_comp]

@[simp]
theorem CokernelCofork.π_ofπ {X Y P : C} (f : X ⟶ Y) (π : Y ⟶ P) (w : f ≫ π = 0) :
    Cofork.π (CokernelCofork.ofπ π w) = π :=
  rfl

/-- Every cokernel cofork `s` is isomorphic (actually, equal) to `Cofork.ofπ (Cofork.π s) _`. -/
def isoOfπ (s : Cofork f 0) : s ≅ Cofork.ofπ (Cofork.π s) (Cofork.condition s) :=
  Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

/-- If `π = π'`, then `CokernelCofork.ofπ π _` and `CokernelCofork.ofπ π' _` are isomorphic. -/
def ofπCongr {P : C} {π π' : Y ⟶ P} {w : f ≫ π = 0} (h : π = π') :
    CokernelCofork.ofπ π w ≅ CokernelCofork.ofπ π' (by rw [← h, w]) :=
  Cocone.ext (Iso.refl _) fun j => by cases j <;> cat_disch

/-- If `s` is a colimit cokernel cofork, then every `k : Y ⟶ W` satisfying `f ≫ k = 0` induces
`l : s.pt ⟶ W` such that `Cofork.π s ≫ l = k`. -/
def CokernelCofork.IsColimit.desc' {s : CokernelCofork f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : f ≫ k = 0) : { l : s.pt ⟶ W // Cofork.π s ≫ l = k } :=
  ⟨hs.desc <| CokernelCofork.ofπ _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a cokernel cofork is a colimit cocone.
It only asks for a proof of facts that carry any mathematical content -/
def isColimitAux (t : CokernelCofork f) (desc : ∀ s : CokernelCofork f, t.pt ⟶ s.pt)
    (fac : ∀ s : CokernelCofork f, t.π ≫ desc s = s.π)
    (uniq : ∀ (s : CokernelCofork f) (m : t.pt ⟶ s.pt) (_ : t.π ≫ m = s.π), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j => by
      cases j
      · simp
      · exact fac s
    uniq := fun s m w => uniq s m (w Limits.WalkingParallelPair.one) }

/-- This is a more convenient formulation to show that a `CokernelCofork` constructed using
`CokernelCofork.ofπ` is a colimit cocone.
-/
def CokernelCofork.IsColimit.ofπ {Z : C} (g : Y ⟶ Z) (eq : f ≫ g = 0)
    (desc : ∀ {Z' : C} (g' : Y ⟶ Z') (_ : f ≫ g' = 0), Z ⟶ Z')
    (fac : ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0), g ≫ desc g' eq' = g')
    (uniq :
      ∀ {Z' : C} (g' : Y ⟶ Z') (eq' : f ≫ g' = 0) (m : Z ⟶ Z') (_ : g ≫ m = g'), m = desc g' eq') :
    IsColimit (CokernelCofork.ofπ g eq) :=
  isColimitAux _ (fun s => desc s.π s.condition) (fun s => fac s.π s.condition) fun s =>
    uniq s.π s.condition

/-- This is a more convenient formulation to show that a `CokernelCofork` of the form
`CokernelCofork.ofπ p _` is a colimit cocone when we know that `p` is an epimorphism. -/
def CokernelCofork.IsColimit.ofπ' {X Y Q : C} {f : X ⟶ Y} (p : Y ⟶ Q) (w : f ≫ p = 0)
    (h : ∀ {A : C} (k : Y ⟶ A) (_ : f ≫ k = 0), { l : Q ⟶ A // p ≫ l = k}) [hp : Epi p] :
    IsColimit (CokernelCofork.ofπ p w) :=
  ofπ _ _ (fun {_} k hk => (h k hk).1) (fun {_} k hk => (h k hk).2) (fun {A} k hk m hm => by
    rw [← cancel_epi p, (h k hk).2, hm])

set_option backward.isDefEq.respectTransparency false in
/-- Every cokernel of `f` induces a cokernel of `g ≫ f` if `g` is epi. -/
def isCokernelEpiComp {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) :
    IsColimit (CokernelCofork.ofπ c.π (by rw [hh]; simp) : CokernelCofork h) :=
  Cofork.IsColimit.mk' _ fun s =>
    let s' : CokernelCofork f :=
      Cofork.ofπ s.π
        (by
          apply hg.left_cancellation
          rw [← Category.assoc, ← hh, s.condition]
          simp)
    let l := CokernelCofork.IsColimit.desc' i s'.π s'.condition
    ⟨l.1, l.2, fun hm => by
      apply Cofork.IsColimit.hom_ext i; rw [Cofork.π_ofπ] at hm; rw [hm]; exact l.2.symm⟩

@[simp]
theorem isCokernelEpiComp_desc {c : CokernelCofork f} (i : IsColimit c) {W} (g : W ⟶ X) [hg : Epi g]
    {h : W ⟶ Y} (hh : h = g ≫ f) (s : CokernelCofork h) :
    (isCokernelEpiComp i g hh).desc s =
      i.desc
        (Cofork.ofπ s.π
          (by
            rw [← cancel_epi g, ← Category.assoc, ← hh]
            simp)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Every cokernel of `g ≫ f` is also a cokernel of `f`, as long as `f ≫ c.π` vanishes. -/
def isCokernelOfComp {W : C} (g : W ⟶ X) (h : W ⟶ Y) {c : CokernelCofork h} (i : IsColimit c)
    (hf : f ≫ c.π = 0) (hfg : g ≫ f = h) : IsColimit (CokernelCofork.ofπ c.π hf) :=
  Cofork.IsColimit.mk _ (fun s => i.desc (CokernelCofork.ofπ s.π (by simp [← hfg])))
    (fun s => by simp only [CokernelCofork.π_ofπ, Cofork.IsColimit.π_desc]) fun s m h => by
      apply Cofork.IsColimit.hom_ext i
      simpa using h

/-- `Y` identifies to the cokernel of a zero map `X ⟶ Y`. -/
def CokernelCofork.IsColimit.ofId {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
    IsColimit (CokernelCofork.ofπ (𝟙 Y) (show f ≫ 𝟙 Y = 0 by rw [hf, zero_comp])) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun x _ => x) (fun _ _ => Category.id_comp _)
    (fun _ _ _ hb => by simp only [← hb, Category.id_comp])

/-- Any zero object identifies to the cokernel of a given epimorphisms. -/
def CokernelCofork.IsColimit.ofEpiOfIsZero {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hf : Epi f) (h : IsZero c.pt) : IsColimit c :=
  isColimitAux _ (fun _ => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)

lemma CokernelCofork.IsColimit.isIso_π {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hc : IsColimit c) (hf : f = 0) : IsIso c.π :=
  isIso_colimit_cocone_parallelPair_of_eq hf hc

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a colimit cokernel cofork for `f : X ⟶ Y`, `e : Y' ≅ Y` and `f' : X' ⟶ Y'` is a
morphism, then there is a colimit cokernel cofork for `f'` with the same point as `c` if for any
morphism `φ : Y ⟶ W`, there is an equivalence `f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0`. -/
def CokernelCofork.isColimitOfIsColimitOfIff {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) {X' Y' : C} (f' : X' ⟶ Y') (e : Y' ≅ Y)
    (iff : ∀ ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ e.hom ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') (e.hom ≫ c.π) (by simp [← iff])) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun s hs ↦ hc.desc (CokernelCofork.ofπ (π := e.inv ≫ s)
      (by rw [iff, e.hom_inv_id_assoc, hs])))
    (fun s hs ↦ by simp)
    (fun s hs m hm ↦ Cofork.IsColimit.hom_ext hc (by simpa [← cancel_epi e.hom] using hm))

/-- If `c` is a colimit cokernel cofork for `f : X ⟶ Y`, and `f' : X' ⟶ Y` is another
morphism, then there is a colimit cokernel cofork for `f'` with the same point as `c` if for any
morphism `φ : Y ⟶ W`, there is an equivalence `f ≫ φ = 0 ↔ f' ≫ φ = 0`. -/
def CokernelCofork.isColimitOfIsColimitOfIff' {X Y : C} {f : X ⟶ Y} {c : CokernelCofork f}
    (hc : IsColimit c) {X' : C} (f' : X' ⟶ Y)
    (iff : ∀ ⦃W : C⦄ (φ : Y ⟶ W), f ≫ φ = 0 ↔ f' ≫ φ = 0) :
    IsColimit (CokernelCofork.ofπ (f := f') c.π (by simp [← iff])) :=
  IsColimit.ofIsoColimit (isColimitOfIsColimitOfIff hc f' (Iso.refl _) (by simpa using iff))
    (Cofork.ext (Iso.refl _))

lemma CokernelCofork.IsColimit.isZero_of_epi {X Y : C} {f : X ⟶ Y}
    {c : CokernelCofork f} (hc : IsColimit c) [Epi f] : IsZero c.pt := by
  have := Cofork.IsColimit.epi hc
  rw [IsZero.iff_id_eq_zero, ← cancel_epi c.π, ← cancel_epi f,
    c.condition_assoc, comp_zero, comp_zero, zero_comp]

end

namespace CokernelCofork

variable {f} {X' Y' : C} {f' : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/-- The morphism between points of cokernel coforks induced by a morphism
in the category of arrows. -/
def mapOfIsColimit {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
    (φ : Arrow.mk f ⟶ Arrow.mk f') : cc.pt ⟶ cc'.pt :=
  hf.desc (CokernelCofork.ofπ (φ.right ≫ cc'.π) (by
    erw [← Arrow.w_assoc φ, condition, comp_zero]))

@[reassoc (attr := simp)]
lemma π_mapOfIsColimit {cc : CokernelCofork f} (hf : IsColimit cc) (cc' : CokernelCofork f')
    (φ : Arrow.mk f ⟶ Arrow.mk f') :
    cc.π ≫ mapOfIsColimit hf cc' φ = φ.right ≫ cc'.π :=
  hf.fac _ _

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between points of colimit cokernel coforks induced by an isomorphism
in the category of arrows. -/
@[simps]
def mapIsoOfIsColimit {cc : CokernelCofork f} {cc' : CokernelCofork f'}
    (hf : IsColimit cc) (hf' : IsColimit cc')
    (φ : Arrow.mk f ≅ Arrow.mk f') : cc.pt ≅ cc'.pt where
  hom := mapOfIsColimit hf cc' φ.hom
  inv := mapOfIsColimit hf' cc φ.inv
  hom_inv_id := Cofork.IsColimit.hom_ext hf (by simp)
  inv_hom_id := Cofork.IsColimit.hom_ext hf' (by simp)

end CokernelCofork

section

variable [HasCokernel f]

/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
abbrev cokernel : C :=
  coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
abbrev cokernel.π : Y ⟶ cokernel f :=
  coequalizer.π f 0

@[simp]
theorem coequalizer_as_cokernel : coequalizer.π f 0 = cokernel.π f :=
  rfl

@[reassoc (attr := simp)]
theorem cokernel.condition : f ≫ cokernel.π f = 0 :=
  CokernelCofork.condition _

/-- The cokernel built from `cokernel.π f` is colimiting. -/
def cokernelIsCokernel :
    IsColimit (Cofork.ofπ (cokernel.π f) ((cokernel.condition f).trans zero_comp.symm)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cofork.ext (Iso.refl _))

/-- Given any morphism `k : Y ⟶ W` such that `f ≫ k = 0`, `k` factors through `cokernel.π f`
via `cokernel.desc : cokernel f ⟶ W`. -/
abbrev cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
  (cokernelIsCokernel f).desc (CokernelCofork.ofπ k h)

@[reassoc (attr := simp)]
theorem cokernel.π_desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    cokernel.π f ≫ cokernel.desc f k h = k :=
  (cokernelIsCokernel f).fac (CokernelCofork.ofπ k h) WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma colimit_ι_zero_cokernel_desc {C : Type*} [Category* C]
    [HasZeroMorphisms C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) [HasCokernel f] :
    colimit.ι (parallelPair f 0) WalkingParallelPair.zero ≫ cokernel.desc f g h = 0 := by
  rw [(colimit.w (parallelPair f 0) WalkingParallelPairHom.left).symm]
  simp

@[simp]
theorem cokernel.desc_zero {W : C} {h} : cokernel.desc f (0 : Y ⟶ W) h = 0 := by
  ext; simp

instance cokernel.desc_epi {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) [Epi k] :
    Epi (cokernel.desc f k h) :=
  ⟨fun {Z} g g' w => by
    replace w := cokernel.π f ≫= w
    simp only [cokernel.π_desc_assoc] at w
    exact (cancel_epi k).1 w⟩

/-- Any morphism `k : Y ⟶ W` satisfying `f ≫ k = 0` induces `l : cokernel f ⟶ W` such that
`cokernel.π f ≫ l = k`. -/
def cokernel.desc' {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) :
    { l : cokernel f ⟶ W // cokernel.π f ≫ l = k } :=
  ⟨cokernel.desc f k h, cokernel.π_desc _ _ _⟩

/-- A commuting square induces a morphism of cokernels. -/
abbrev cokernel.map {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') : cokernel f ⟶ cokernel f' :=
  cokernel.desc f (q ≫ cokernel.π f') (by
    have : f ≫ q ≫ π f' = p ≫ f' ≫ π f' := by
      simp only [← Category.assoc]
      apply congrArg (· ≫ π f') w
    simp [this])

instance {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ⟶ X') (q : Y ⟶ Y')
    (w : f ≫ q = p ≫ f') [Epi p] [IsIso q] :
    IsIso (cokernel.map _ _ _ _ w) :=
  ⟨cokernel.desc _ (inv q ≫ cokernel.π f) (by simp [← cancel_epi p, ← reassoc_of% w]),
    by cat_disch, by cat_disch⟩

@[simp]
lemma cokernel.map_id {X Y : C} (f : X ⟶ Y) [HasCokernel f] (q : X ⟶ X)
    (w : f ≫ 𝟙 _ = q ≫ f) : cokernel.map f f q (𝟙 _) w = 𝟙 _ := by
  cat_disch

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
   cokernel f ---> Z
   |               |
   | cokernel.map  |
   |               |
   v               v
   cokernel f' --> Z'
```
-/
theorem cokernel.map_desc {X Y Z X' Y' Z' : C} (f : X ⟶ Y) [HasCokernel f] (g : Y ⟶ Z)
    (w : f ≫ g = 0) (f' : X' ⟶ Y') [HasCokernel f'] (g' : Y' ⟶ Z') (w' : f' ≫ g' = 0) (p : X ⟶ X')
    (q : Y ⟶ Y') (r : Z ⟶ Z') (h₁ : f ≫ q = p ≫ f') (h₂ : g ≫ r = q ≫ g') :
    cokernel.map f f' p q h₁ ≫ cokernel.desc f' g' w' = cokernel.desc f g w ≫ r := by
  ext; simp [h₂]

@[simp]
lemma cokernel.map_zero {X Y X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y')
    [HasCokernel f] [HasCokernel f'] (q : X ⟶ X') (w : f ≫ 0 = q ≫ f') :
    cokernel.map f f' q 0 w = 0 := by
  cat_disch

/-- A commuting square of isomorphisms induces an isomorphism of cokernels. -/
@[simps]
def cokernel.mapIso {X' Y' : C} (f' : X' ⟶ Y') [HasCokernel f'] (p : X ≅ X') (q : Y ≅ Y')
    (w : f ≫ q.hom = p.hom ≫ f') : cokernel f ≅ cokernel f' where
  hom := cokernel.map f f' p.hom q.hom w
  inv := cokernel.map f' f p.inv q.inv (by
          refine (cancel_mono q.hom).1 ?_
          simp [w])

/-- The cokernel of the zero morphism is an isomorphism -/
instance cokernel.π_zero_isIso : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _

theorem eq_zero_of_mono_cokernel [Mono (cokernel.π f)] : f = 0 :=
  (cancel_mono (cokernel.π f)).1 (by simp)

/-- The cokernel of a zero morphism is isomorphic to the target. -/
def cokernelZeroIsoTarget : cokernel (0 : X ⟶ Y) ≅ Y :=
  coequalizer.isoTargetOfSelf 0

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem cokernelZeroIsoTarget_hom :
    cokernelZeroIsoTarget.hom = cokernel.desc (0 : X ⟶ Y) (𝟙 Y) (by simp) := by
  ext; simp [cokernelZeroIsoTarget]

@[simp]
theorem cokernelZeroIsoTarget_inv : cokernelZeroIsoTarget.inv = cokernel.π (0 : X ⟶ Y) :=
  rfl

/-- If two morphisms are known to be equal, then their cokernels are isomorphic. -/
def cokernelIsoOfEq {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel f ≅ cokernel g :=
  HasColimit.isoOfNatIso (by simp [h]; rfl)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem cokernelIsoOfEq_refl {h : f = f} : cokernelIsoOfEq h = Iso.refl (cokernel f) := by
  ext; simp [cokernelIsoOfEq]

@[reassoc (attr := simp)]
theorem π_comp_cokernelIsoOfEq_hom {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π f ≫ (cokernelIsoOfEq h).hom = cokernel.π g := by
  cases h; simp

@[reassoc (attr := simp)]
theorem π_comp_cokernelIsoOfEq_inv {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g) :
    cokernel.π _ ≫ (cokernelIsoOfEq h).inv = cokernel.π _ := by
  cases h; simp

@[reassoc (attr := simp)]
theorem cokernelIsoOfEq_hom_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).hom ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [h, he]) := by
  cases h; simp

@[reassoc (attr := simp)]
theorem cokernelIsoOfEq_inv_comp_desc {Z} {f g : X ⟶ Y} [HasCokernel f] [HasCokernel g] (h : f = g)
    (e : Y ⟶ Z) (he) :
    (cokernelIsoOfEq h).inv ≫ cokernel.desc _ e he = cokernel.desc _ e (by simp [← h, he]) := by
  cases h; simp

@[simp]
theorem cokernelIsoOfEq_trans {f g h : X ⟶ Y} [HasCokernel f] [HasCokernel g] [HasCokernel h]
    (w₁ : f = g) (w₂ : g = h) :
    cokernelIsoOfEq w₁ ≪≫ cokernelIsoOfEq w₂ = cokernelIsoOfEq (w₁.trans w₂) := by
  cases w₁; simp

variable {f}

theorem cokernel_not_mono_of_nonzero (w : f ≠ 0) : ¬Mono (cokernel.π f) := fun _ =>
  w (eq_zero_of_mono_cokernel f)

theorem cokernel_not_iso_of_nonzero (w : f ≠ 0) : IsIso (cokernel.π f) → False := fun _ =>
  cokernel_not_mono_of_nonzero w inferInstance

-- TODO the remainder of this section has obvious generalizations to `HasCoequalizer f g`.
instance hasCokernel_comp_iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    HasCokernel (f ≫ g) where
  exists_colimit :=
    ⟨{  cocone := CokernelCofork.ofπ (inv g ≫ cokernel.π f) (by simp)
        isColimit :=
          isColimitAux _
            (fun s =>
              cokernel.desc _ (g ≫ s.π) (by rw [← Category.assoc, CokernelCofork.condition]))
            (by simp) fun s (m : cokernel _ ⟶ _) w => by
            simp_rw [← w]
            apply coequalizer.hom_ext
            simp }⟩

/-- When `g` is an isomorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `f`.
-/
@[simps]
def cokernelCompIsIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCokernel f] [IsIso g] :
    cokernel (f ≫ g) ≅ cokernel f where
  hom := cokernel.desc _ (inv g ≫ cokernel.π f) (by simp)
  inv := cokernel.desc _ (g ≫ cokernel.π (f ≫ g)) (by rw [← Category.assoc, cokernel.condition])

instance hasCokernel_epi_comp {X Y : C} (f : X ⟶ Y) [HasCokernel f] {W} (g : W ⟶ X) [Epi g] :
    HasCokernel (g ≫ f) :=
  ⟨⟨{   cocone := _
        isColimit := isCokernelEpiComp (colimit.isColimit _) g rfl }⟩⟩

/-- When `f` is an epimorphism, the cokernel of `f ≫ g` is isomorphic to the cokernel of `g`.
-/
@[simps]
def cokernelEpiComp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [Epi f] [HasCokernel g] :
    cokernel (f ≫ g) ≅ cokernel g where
  hom := cokernel.desc _ (cokernel.π g) (by simp)
  inv :=
    cokernel.desc _ (cokernel.π (f ≫ g))
      (by
        rw [← cancel_epi f, ← Category.assoc]
        simp)

/-- Equal maps have isomorphic cokernels. -/
@[simps] def cokernel.congr {X Y : C} (f g : X ⟶ Y) [HasCokernel f] [HasCokernel g]
    (h : f = g) : cokernel f ≅ cokernel g where
  hom := cokernel.desc _ (cokernel.π g) (by simp [h])
  inv := cokernel.desc _ (cokernel.π f) (by simp [← h])

lemma isZero_cokernel_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] [HasCokernel f] :
    IsZero (cokernel f) :=
  CokernelCofork.IsColimit.isZero_of_epi (c := CokernelCofork.ofπ _ (cokernel.condition f))
    (cokernelIsCokernel f)

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
@[simps! pt]
def cokernel.zeroCokernelCofork : CokernelCofork f :=
    CokernelCofork.ofπ (0 : Y ⟶ 0) comp_zero

@[simp]
lemma cokernel.zeroCokernelCofork_π : (cokernel.zeroCokernelCofork f).π = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The morphism to the zero object is a cokernel of an epimorphism -/
def cokernel.isColimitCoconeZeroCocone [Epi f] : IsColimit (cokernel.zeroCokernelCofork f) :=
  Cofork.IsColimit.mk _ (fun _ => 0)
    fun _ => by simp [zero_of_epi_comp f _]
    fun _ _ _ => zero_of_from_zero _

/-- The cokernel of an epimorphism is isomorphic to the zero object -/
def cokernel.ofEpi [HasCokernel f] [Epi f] : cokernel f ≅ 0 :=
  Functor.mapIso (Cocone.forget _) <|
    IsColimit.uniqueUpToIso (colimit.isColimit (parallelPair f 0))
      (cokernel.isColimitCoconeZeroCocone f)

/-- The cokernel morphism of an epimorphism is a zero morphism -/
theorem cokernel.π_of_epi [HasCokernel f] [Epi f] : cokernel.π f = 0 :=
  zero_of_target_iso_zero _ (cokernel.ofEpi f)

end HasZeroObject

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
  (kernelCompMono (factorThruImage f) (image.ι f)).symm ≪≫ (kernel.congr _ _ (by simp))

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

section

variable (X Y)

/-- The cokernel of a zero morphism is an isomorphism -/
theorem cokernel.π_of_zero : IsIso (cokernel.π (0 : X ⟶ Y)) :=
  coequalizer.π_of_self _

end

section HasZeroObject

variable [HasZeroObject C]

open ZeroObject

/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
instance kernel.of_cokernel_of_epi [HasCokernel f] [HasKernel (cokernel.π f)] [Epi f] :
    IsIso (kernel.ι (cokernel.π f)) :=
  equalizer.ι_of_eq <| cokernel.π_of_epi f

/-- The cokernel of the kernel of a monomorphism is an isomorphism -/
instance cokernel.of_kernel_of_mono [HasKernel f] [HasCokernel (kernel.ι f)] [Mono f] :
    IsIso (cokernel.π (kernel.ι f)) :=
  coequalizer.π_of_eq <| kernel.ι_of_mono f

/-- If `f ≫ g = 0` implies `g = 0` for all `g`, then `0 : Y ⟶ 0` is a cokernel of `f`. -/
def zeroCokernelOfZeroCancel {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) (g : Y ⟶ Z) (_ : f ≫ g = 0), g = 0) :
    IsColimit (CokernelCofork.ofπ (0 : Y ⟶ 0) (show f ≫ 0 = 0 by simp)) :=
  Cofork.IsColimit.mk _ (fun _ => 0)
    (fun s => by rw [hf _ _ (CokernelCofork.condition s), comp_zero]) fun s m _ => by
      apply HasZeroObject.from_zero_ext

end HasZeroObject

section Transport

set_option backward.isDefEq.respectTransparency false in
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
def kernelComparison [HasKernel f] [HasKernel (G.map f)] : G.obj (kernel f) ⟶ kernel (G.map f) :=
  kernel.lift _ (G.map (kernel.ι f))
    (by simp only [← G.map_comp, kernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]
theorem kernelComparison_comp_ι [HasKernel f] [HasKernel (G.map f)] :
    kernelComparison f G ≫ kernel.ι (G.map f) = G.map (kernel.ι f) :=
  kernel.lift_ι _ _ _

@[reassoc (attr := simp)]
theorem map_lift_kernelComparison [HasKernel f] [HasKernel (G.map f)] {Z : C} {h : Z ⟶ X}
    (w : h ≫ f = 0) :
    G.map (kernel.lift _ h w) ≫ kernelComparison f G =
      kernel.lift _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) := by
  ext; simp [← G.map_comp]

@[reassoc]
theorem kernelComparison_comp_kernel_map {X' Y' : C} [HasKernel f] [HasKernel (G.map f)]
    (g : X' ⟶ Y') [HasKernel g] [HasKernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    kernelComparison f G ≫
        kernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) =
      G.map (kernel.map f g p q hpq) ≫ kernelComparison g G :=
  kernel.lift_map _ _ (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, kernel.condition, G.map_zero]) _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (kernel.lift_ι _ _ _).symm) _

/-- The comparison morphism for the cokernel of `f`. -/
def cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel (G.map f) ⟶ G.obj (cokernel f) :=
  cokernel.desc _ (G.map (coequalizer.π _ _))
    (by simp only [← G.map_comp, cokernel.condition, Functor.map_zero])

@[reassoc (attr := simp)]
theorem π_comp_cokernelComparison [HasCokernel f] [HasCokernel (G.map f)] :
    cokernel.π (G.map f) ≫ cokernelComparison f G = G.map (cokernel.π _) :=
  cokernel.π_desc _ _ _

@[reassoc (attr := simp)]
theorem cokernelComparison_map_desc [HasCokernel f] [HasCokernel (G.map f)] {Z : C} {h : Y ⟶ Z}
    (w : f ≫ h = 0) :
    cokernelComparison f G ≫ G.map (cokernel.desc _ h w) =
      cokernel.desc _ (G.map h) (by simp only [← G.map_comp, w, Functor.map_zero]) := by
  ext; simp [← G.map_comp]

@[reassoc]
theorem cokernel_map_comp_cokernelComparison {X' Y' : C} [HasCokernel f] [HasCokernel (G.map f)]
    (g : X' ⟶ Y') [HasCokernel g] [HasCokernel (G.map g)] (p : X ⟶ X') (q : Y ⟶ Y')
    (hpq : f ≫ q = p ≫ g) :
    cokernel.map (G.map f) (G.map g) (G.map p) (G.map q) (by rw [← G.map_comp, hpq, G.map_comp]) ≫
        cokernelComparison _ G =
      cokernelComparison _ G ≫ G.map (cokernel.map f g p q hpq) :=
  cokernel.map_desc _ _ (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _
    (by rw [← G.map_comp, cokernel.condition, G.map_zero]) _ _ _ _
    (by simp only [← G.map_comp]; exact G.congr_map (cokernel.π_desc _ _ _))

end Comparison

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C]

/-- `HasKernels` represents the existence of kernels for every morphism. -/
class HasKernels : Prop where
  has_limit : ∀ {X Y : C} (f : X ⟶ Y), HasKernel f := by infer_instance

/-- `HasCokernels` represents the existence of cokernels for every morphism. -/
class HasCokernels : Prop where
  has_colimit : ∀ {X Y : C} (f : X ⟶ Y), HasCokernel f := by infer_instance

attribute [instance 100] HasKernels.has_limit HasCokernels.has_colimit

instance (priority := 100) hasKernels_of_hasEqualizers [HasEqualizers C] : HasKernels C where

instance (priority := 100) hasCokernels_of_hasCoequalizers [HasCoequalizers C] :
    HasCokernels C where

section HasKernels
variable [HasKernels C]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of an arrow is natural. -/
@[simps]
noncomputable def ker : Arrow C ⥤ C where
  obj f := kernel f.hom
  map {f g} u := kernel.lift _ (kernel.ι _ ≫ u.left) (by simp)

/-- The kernel inclusion is natural. -/
@[simps] def ker.ι : ker (C := C) ⟶ Arrow.leftFunc where app f := kernel.ι _

@[reassoc (attr := simp)] lemma ker.condition : ι C ≫ Arrow.leftToRight = 0 := by cat_disch

end HasKernels

section HasCokernels
variable [HasCokernels C]

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of an arrow is natural. -/
@[simps]
noncomputable def coker : Arrow C ⥤ C where
  obj f := cokernel f.hom
  map {f g} u := cokernel.desc _ (u.right ≫ cokernel.π _) (by simp [← Arrow.w_assoc u])

/-- The cokernel projection is natural. -/
@[simps] def coker.π : Arrow.rightFunc ⟶ coker (C := C) where app f := cokernel.π _

@[reassoc (attr := simp)] lemma coker.condition : Arrow.leftToRight ≫ π C = 0 := by cat_disch

end HasCokernels
end CategoryTheory.Limits
