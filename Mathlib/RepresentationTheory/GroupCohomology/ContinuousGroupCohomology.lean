import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Tactic

-- import CFT.Continuous._0_ContinuousAddMonoidHom
-- import CFT.Continuous.«_0.4_const_and_map»
-- import CFT.Continuous.«_0.6_ContinuousMaps»

/-
# Foundations of continuous cohomology 1.

In this file, `G` is a non-empty topological space.
Given a Topological additive commutative group `M`, we define a sequence of
topological additive commutative groups `ContinuousMultiMaps G M n` recursively:

`0 ↦ C(G,M)`
`1 ↦ C(G,C(G,M))`
`2 ↦ C(G,C(G,C(G,M)))`, etc.

This sequence is abbreviated `𝓒(G,M,n)`.

We define "coboundary" maps `d G M n : 𝓒(G,M,n) →ₜ+ 𝓒(G,M,n+1)`, abbreviated `∂`
or `∂[n]` when the other variables are implicit in the context.
We prove that the sequence is exact.

Given a map `φ : M →ₜ+ N`, we define a sequence of maps

  `MultiMap.map G φ n : 𝓒(G,M,n) →ₜ+ 𝓒(G,N,n)`,

and we prove that these commute with the coboundary maps.

Given `ι : C(H,G)`, we define a sequence of maps

  `ContinuousMultiMaps.comap M ι n : 𝓒(G,M,n) →ₜ+ 𝓒(H,M,n)`

There maps are abbreviated `ι*(M,n)`. We prove that `ι*(M,n)` commutes with the coboundary maps.

# In Progress :
Show that the functor `𝓒(G,_,n)` takes exact sequences of strong morphisms in `M` to exact
sequences of strong morphisms.

# ToDo
Construct `𝓒(G,M,_)` as a complex in the catergory of topological additive commuttive groups.
-/

variable (G M : Type _) [TopologicalSpace G] [TopologicalSpace M]

-- instance : TopologicalAddGroup M := TopAddCommGroup.toTopologicalAddGroup
-- instance : TopAddCommGroup C(G,M) := ⟨inferInstance⟩

def ContinuousMultiMaps_aux : ℕ → Σ α : Type _, TopologicalSpace α
  | 0 => ⟨C(G,M),inferInstance⟩
  | n + 1 =>
    let _ := (ContinuousMultiMaps_aux n).2
    ⟨C(G,(ContinuousMultiMaps_aux n).1),inferInstance⟩

abbrev ContinuousMultiMaps (n : ℕ) : Type _ := (ContinuousMultiMaps_aux G M n).1
notation "𝓒(" G "," M "," n ")" => ContinuousMultiMaps G M n

instance (n : ℕ) : TopologicalSpace 𝓒(G,M,n) := (ContinuousMultiMaps_aux G M n).2
instance : FunLike 𝓒(G,M,0) G M := inferInstanceAs (FunLike C(G,M) G M)
instance (n : ℕ) : FunLike 𝓒(G,M,n+1) G 𝓒(G,M,n) := inferInstanceAs (FunLike C(G,𝓒(G,M,n)) _ _)

lemma ContinuousMultiMaps_zero : 𝓒(G,M,0) = C(G,M) := rfl

lemma ContinuousMultiMaps_succ (n : ℕ) : 𝓒(G,M,n+1) = C(G,𝓒(G,M,n)) := rfl

@[ext] lemma ContinuousMultiMaps.ext {f f' : 𝓒(G,M,0)} (h : ∀ x : G, f x = f' x) : f = f' :=
  ContinuousMap.ext h

@[ext] lemma ContinuousMultiMaps.ext' {n : ℕ}{f f' : 𝓒(G,M,n+1)}
    (h : ∀ x : G, f x = f' x) : f = f' := DFunLike.coe_injective (funext h)

variable [AddCommGroup M] [TopologicalAddGroup M]

def ContinuousMultiMaps_aux' (n : ℕ) :
    Σ (_ : AddCommGroup 𝓒(G,M,n)), Inhabited (TopologicalAddGroup 𝓒(G,M,n)) := by
  induction n with
  | zero =>
    use inferInstanceAs (AddCommGroup C(G,M))
    constructor
    exact inferInstanceAs (TopologicalAddGroup C(G,M))
  | succ n ih =>
    let _ := ih.1
    obtain ⟨_⟩ := ih.2
    use inferInstanceAs (AddCommGroup C(G,𝓒(G,M,n)))
    constructor
    exact inferInstanceAs (TopologicalAddGroup C(G,𝓒(G,M,n)))

instance (n : ℕ) : AddCommGroup 𝓒(G,M,n) := (ContinuousMultiMaps_aux' G M n).1
instance (n : ℕ) : TopologicalAddGroup 𝓒(G,M,n) := (ContinuousMultiMaps_aux' G M n).2.default

instance (R : Type) [SMul R M] [ContinuousConstSMul R M] :
    ContinuousConstSMul R C(G,M) where
  continuous_const_smul r := ContinuousMap.continuous_postcomp ⟨_,continuous_const_smul r⟩

variable (R : Type) [CommRing R] [Module R M] [ContinuousConstSMul R M]

def ContinuousMultiMaps.module_aux :
    ∀ n, (_ : Module R 𝓒(G,M,n)) × Inhabited (ContinuousConstSMul R 𝓒(G,M,n))
  | 0 => ⟨inferInstanceAs (Module R C(G,M)),⟨inferInstanceAs (ContinuousConstSMul R C(G,M))⟩⟩
  | n + 1 => by
    obtain ⟨_,⟨_⟩⟩ := module_aux n
    exact ⟨inferInstanceAs (Module R C(G,_)),⟨inferInstanceAs (ContinuousConstSMul R C(G,_))⟩⟩

instance (n : ℕ) : Module R 𝓒(G,M,n) := (ContinuousMultiMaps.module_aux G M R n).fst
instance (n : ℕ) : ContinuousConstSMul R 𝓒(G,M,n) :=
  (ContinuousMultiMaps.module_aux G M R n).snd.default

namespace ContinuousLinearMap

variable {G M R}

def constL : M →L[R] C(G,M) where
  toFun := ContinuousMap.const G
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  cont := ContinuousMap.continuous_const'

lemma constL_apply₂ (m : M) (x : G) : constL (G := G) (R := R) m x = m := rfl

variable {N : Type _} [TopologicalSpace N] [AddCommGroup N] [TopologicalAddGroup N]
  [Module R N] [ContinuousConstSMul R N]
variable {L : Type _} [TopologicalSpace L] [AddCommGroup L] [TopologicalAddGroup L]
  [Module R L] [ContinuousConstSMul R L]

def mapL : (M →L[R] N) →ₗ[R] (C(G,M) →L[R] C(G,N)) where
  toFun φ := {
    toFun f := ContinuousMap.comp φ f
    map_add' f₁ f₂ := by
      ext
      simp only [ContinuousMap.comp_apply, ContinuousMap.add_apply, ContinuousMap.coe_coe, map_add]
    map_smul' r f := by
      ext
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_smul, Pi.smul_apply,
        ContinuousMap.coe_coe, map_smul, RingHom.id_apply, ContinuousMap.coe_comp,
        Function.comp_apply]
    cont := ContinuousMap.continuous_postcomp (φ : C(M,N))
  }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma mapL_comp (φ : M →L[R] N) (ψ : N →L[R] L) : (ψ ∘L φ).mapL (G := G) = ψ.mapL ∘L φ.mapL := rfl

lemma mapL_comp_constL (φ : M →L[R] N) : φ.mapL (G := G) ∘L constL = constL ∘L φ := rfl


end ContinuousLinearMap

namespace ContinuousMultiMap
open ContinuousLinearMap
open _root_.LinearMap hiding sub_comp comp_sub coe_comp

variable {G M R}
--def const {n : ℕ} : 𝓒(G,M,n) →L[R] 𝓒(G,M,n + 1) := constL G 𝓒(G,M,n) R

variable {N : Type _} [TopologicalSpace N] [AddCommGroup N] [TopologicalAddGroup N]
  [Module R N] [ContinuousConstSMul R N]

-- def map {N : Type _} [TopologicalSpace N] [AddCommGroup N] [TopologicalAddGroup N]
--     [Module R N] [ContinuousConstSMul R N] {m n : ℕ} :
--     (𝓒(G,M,m) →L[R] 𝓒(G,N,n)) →ₗ[R] (𝓒(G,M,m+1) →L[R] 𝓒(G,N,n+1)) := mapL G _ R

-- lemma map_comp_const (m n : ℕ) (f : 𝓒(G,M,m) →L[R] 𝓒(G,N,n)) : map f ∘L const = const ∘L f := rfl

variable (G M R)
/--
The differential `d G M n : 𝓒(G,M,n) →ₜ+ 𝓒(G,M,n+1)`.
-/
def d : ∀ n, 𝓒(G,M,n) →L[R] 𝓒(G,M,n+1)
  | 0     => by
    change C(G,M) →L[R] C(G,C(G,M))
    exact constL - constL (M := M).mapL
  | n + 1 => constL - (d n).mapL

lemma d_zero : d G M R 0 = constL - constL (M := M).mapL := rfl

lemma d_succ (n : ℕ) : d G M R (n + 1) = constL - (d G M R n).mapL := rfl

lemma d_comp_d (n : ℕ) : (d G M R n.succ).comp (d G M R n) = 0 :=
by
  induction n with
  | zero =>
    rw [d_succ, sub_comp]
    nth_rw 3 [d_zero]
    rw [comp_sub, ←sub_add, mapL_comp_constL, sub_self, zero_add]
    rw [d_zero, map_sub, sub_comp, sub_eq_zero]
    rfl
  | succ _ ih =>
    rw [d_succ]
    nth_rw 2 [d_succ]
    rw [comp_sub, sub_comp, sub_comp, ←mapL_comp, ih, mapL_comp_constL, map_zero, sub_zero,
      d_succ, comp_sub, ←sub_add, sub_self, zero_add, sub_self]

/--
The sequence of continuous linear maps `d G M R n : 𝓒(G,M,n) →L[R] 𝓒(G,M,n+1)` is exact.
-/
lemma d_exact [Inhabited G] (n : ℕ) :
    ker (d G M R (n +1)).toLinearMap = range (d G M R n).toLinearMap := by
  apply le_antisymm
  · intro f hf
    use f default
    rw [mem_ker, d_succ] at hf
    have : (constL (R := R) f) (default : G) = (mapL (d G M R n) f) default
    · congr 1
      rw [←sub_eq_zero]
      exact hf
    rw [constL_apply₂] at this
    nth_rw 2 [this]
    rfl
  · rw [range_le_ker_iff, ←coe_comp, d_comp_d, coe_zero]



end ContinuousMultiMap

/-

open ContinuousAddMonoidHom


/--
The differential `d G M n : 𝓒(G,M,n) →ₜ+ 𝓒(G,M,n+1)`.
-/
def d : ∀ n, 𝓒(G,M,n) →ₜ+ 𝓒(G,M,n+1)
  | 0     => constₜ - mapₜ (constₜ (A := M))
  | n + 1 => constₜ - mapₜ (d n)

lemma d_zero : d G M 0 = constₜ - mapₜ (constₜ (A := M)) := rfl

lemma d_succ (n : ℕ) : d G M (n + 1) = constₜ - mapₜ (d G M n) := rfl

lemma d_comp_d (n : ℕ) : (d G M n.succ).comp (d G M n) = 0 :=
by
  induction n with
  | zero =>
    rw [d_succ, sub_comp, d_zero]
    nth_rw 2 [comp_sub]
    rw [mapₜ_comp_constₜ, map_sub, sub_sub_cancel, sub_comp, sub_eq_zero]
    rfl
  | succ _ ih =>
    rw [d_succ]
    nth_rw 2 [d_succ]
    rw [comp_sub, sub_comp, sub_comp, ←mapₜ_comp, ih, mapₜ_comp_constₜ, map_zero, sub_zero,
      d_succ, comp_sub, ←sub_add, sub_self, zero_add, sub_self]

/--
The sequence of maps `d G M _ : 𝓒(G,M,n) → 𝓒(G,M,n+1)` is exact.
-/
lemma d_exact [Inhabited G] (n : ℕ) : (d G M n.succ).ker = (d G M n).range := by
  apply le_antisymm
  · intro f hf
    use f default
    rw [AddMonoidHom.mem_ker, d_succ, coe_sub, AddMonoidHom.sub_apply, sub_eq_zero] at hf
    have : (constₜ f) (default : G) = (mapₜ (d G M n) f) default := by congr 1
    rw [constₜ_apply₂] at this
    nth_rw 2 [this]
    rfl
  · rw [range_le_ker_iff, d_comp_d]

---------------------------

section ContinuousMultiMaps.map
variable {N L : Type _} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]
variable [AddCommGroup L] [TopologicalSpace L] [TopologicalAddGroup L]
variable {M}

/--
Functoriality of `ContinuousMultiMaps G M n` in `M`.
-/
def ContinuousMultiMaps.map : ∀ n : ℕ, (M →ₜ+ N) →+ (𝓒(G,M,n) →ₜ+ 𝓒(G,N,n))
| 0     => mapₜ
| n + 1 => mapₜ (A := 𝓒(G,M,n)) (B := 𝓒(G,N,n)).comp (map n)

@[simp] lemma ContinuousMultiMaps.map_zero : map G 0 (M := M) (N := N) = mapₜ := rfl

@[simp] lemma ContinuousMultiMaps.map_zero_apply (φ : M →ₜ+ N) : map G 0 φ = mapₜ φ := rfl

lemma ContinuousMultiMaps.map_succ (n : ℕ) :
    map G (n + 1) = mapₜ (X := G) (A := 𝓒(G,M,n)) (B := 𝓒(G,N,n)).comp (map G n) := rfl

lemma ContinuousMultiMaps.map_succ_apply (n : ℕ) (φ : M →ₜ+ N) :
    map G (n + 1) φ = mapₜ (map G n φ) := rfl

lemma ContinuousMultiMaps.map_id (n : ℕ) :
    map G n (ContinuousAddMonoidHom.id M) = ContinuousAddMonoidHom.id _ := by
  induction n with
  | zero        => rfl
  | succ n ih   => rw [map_succ_apply,ih]; rfl

lemma ContinuousMultiMaps.map_comp (φ : M →ₜ+ N) (ψ : N →ₜ+ L) (n : ℕ) :
    map G n (ψ.comp φ) = (map G n ψ).comp (map G n φ) := by
  induction n with
  | zero        => rfl
  | succ n ih   => rw [map_succ_apply, map_succ_apply, map_succ_apply, ih, mapₜ_comp]

/--
`ContinuousMultiMaps.map` is a map of complexes.
-/
lemma ContinuousMultiMaps.map_comp_d (φ : M →ₜ+ N) (n : ℕ) :
    (map G (n+1) φ).comp (d G M n) = (d G N n).comp (map G n φ) := by
  induction n with
  | zero =>
    rw [d_zero, comp_sub, map_succ_apply, mapₜ_comp_constₜ, d_zero, sub_comp]
    rfl
  | succ n ih =>
    rw [map_succ_apply, d_succ, comp_sub, d_succ, mapₜ_comp_constₜ, sub_comp, ←mapₜ_comp, ih]
    rfl

end ContinuousMultiMaps.map

--------------------------------------

section ContinuousMultiMaps.comap

variable {H : Type _} [TopologicalSpace H] (ι : C(H,G))
variable {G M}


def ContinuousMap.pullback : C(G,M) →ₜ+ C(H,M) where
  toAddMonoidHom := ι.compAddMonoidHom'
  continuous_toFun  := continuous_precomp _

lemma ContinuousMap.pullback_id :
    pullback (ContinuousMap.id G) = ContinuousAddMonoidHom.id C(G,M) := rfl

lemma ContinuousMap.pullback_comp {H' : Type _} [TopologicalSpace H'] (ι' : C(H',H)) :
    pullback (M := M) (ι.comp ι') = (pullback ι').comp (pullback ι) := rfl

lemma ContinuousMap.pullback_comp_mapₜ {N : Type _} [AddCommGroup N] [TopologicalSpace N]
    [TopologicalAddGroup N] (φ : M →ₜ+ N) :
    (pullback ι).comp (mapₜ φ) = (mapₜ φ).comp (pullback ι) := rfl

open ContinuousMap (pullback pullback_comp_mapₜ)

variable (M)
/--
Functoriality of `ContinuousMultiMaps G M` in `G`, generalizing the inflation and
restriction maps.
-/
def ContinuousMultiMaps.comap : ∀ n : ℕ, 𝓒(G,M,n) →ₜ+ 𝓒(H,M,n)
  | 0      =>  pullback ι
  | n + 1  =>  (mapₜ (comap n)).comp (pullback (M := 𝓒(G,M,n)) ι)

notation ι"*("M","n")" => ContinuousMultiMaps.comap M ι n

lemma ContinuousMultiMaps.comap_zero : ι*(M,0) = pullback ι := rfl

lemma ContinuousMultiMaps.comap_succ : ι*(M,n+1) = (mapₜ (ι*(M,n))).comp (pullback ι) := rfl

lemma ContinuousMultiMaps.coe_comap_zero : (comap M ι 0).toAddMonoidHom = ι.compAddMonoidHom' := rfl

lemma ContinuousMultiMaps.coe_comap_succ : (comap M ι (n + 1)).toAddMonoidHom
    = (mapₜ (comap M ι n)).toAddMonoidHom.comp ι.compAddMonoidHom' := rfl

lemma ContinuousMultiMaps.comap_zero_apply (f : 𝓒(G,M,0)) : comap M ι 0 f = f.comp ι := rfl

lemma ContinuousMultiMaps.comap_zero_apply₂ (f : 𝓒(G,M,0)) (x : H) : comap M ι 0 f x = f (ι x) :=
  rfl

lemma ContinuousMultiMaps.comap_succ_apply (f : 𝓒(G,M,n + 1)) :
    comap M ι (n + 1) f = mapₜ (A := 𝓒(G,M,n)) (B := 𝓒(H,M,n)) (comap M ι n) (f.comp ι) := rfl

lemma ContinuousMultiMaps.comap_succ_apply₂ (f : 𝓒(G,M,n + 1)) (x : H) :
    comap M ι (n + 1) f x = comap M ι n (f (ι x)) := rfl

lemma ContinuousMultiMaps.comap_id : (ContinuousMap.id G)*(M,n) = ContinuousAddMonoidHom.id _ := by
  induction n with
  | zero      => rfl
  | succ _ ih => rw [comap_succ, ih]; rfl

lemma ContinuousMultiMaps.comap_comp [TopologicalSpace H'] (ι' : C(H',H)) :
    (ι.comp ι')*(M,n) = ι'*(M,n).comp (ι*(M,n)) := by
  induction n with
  | zero      => rfl
  | succ _ ih => rw [comap_succ,ih]; rfl

/--
`ContinuousMultiMaps.comap M (ι : H → G)` is a map of complexes.
-/
lemma ContinuousMultiMaps.comap_comp_d (n : ℕ) :
    ι*(M,n+1).comp (d G M n) = (d H M n).comp (ι*(M,n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [comap_succ, d_succ, d_succ, sub_comp, comp_sub]
    congr 1
    rw [comp_assoc, pullback_comp_mapₜ, ←comp_assoc, ←mapₜ_comp, ih]
    rfl

/--
The maps of complexes `comap _ _ ι` and `map _ _ φ` commute.
-/
lemma ContinuousMultiMaps.comap_comp_map [AddCommGroup N] [TopologicalSpace N]
    [TopologicalAddGroup N] (φ : M →ₜ+ N) :
    ι*(N,n).comp (map G n φ) = (map H n φ).comp (ι*(M,n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (mapₜ (ι*(N,n).comp (map G n φ))).comp ι.pullback = _
    rw [ih]
    rfl

end ContinuousMultiMaps.comap
-/
