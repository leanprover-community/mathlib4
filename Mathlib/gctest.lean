import Mathlib.RepresentationTheory.Rep

/-
Used 428694 heartbeats, which is greater than the current maximum of 200000.-/
count_heartbeats in
set_option trace.profiler true in
set_option profiler true in
set_option pp.proofs.withType false in
theorem Rep.ihom_coev_app_hom' : ∀ {k G : Type} [CommRing k] [Group G] (A B : Rep k G),
  (CategoryTheory.NatTrans.app (CategoryTheory.ihom.coev A) B).hom =
    LinearMap.flip (TensorProduct.mk k (CoeSort.coe A) ↑((CategoryTheory.Functor.id (Rep k G)).obj B).V) :=
fun {k G} [CommRing k] [Group G] A B ↦ LinearMap.ext fun x ↦ LinearMap.ext fun x_1 ↦ rfl
