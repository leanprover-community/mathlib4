import Mathlib.HahnEmbedding.Hahn
import Mathlib.HahnEmbedding.Divisible


noncomputable def hahn_embedding (M: Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]:
    M →+o HahnSeries ({A : archimedeanClass M // A ≠ 0}) ℝ :=
  (HahnSeries.embDomainAddMonoidHom (DivisibleCompletion.classIso_without_zero M).symm.toOrderEmbedding).comp
    ((hahn_embedding_of_divisible _).comp
    (DivisibleCompletion.orderAddMonoidHom M))

theorem hahn_embedding_injective (M: Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]:
    Function.Injective (hahn_embedding M) :=
  (HahnSeries.embDomainAddMonoidHom_injective _).comp
    ((hahn_embedding_of_divisible_injective _).comp
    (DivisibleCompletion.orderAddMonoidHom_injective M))
