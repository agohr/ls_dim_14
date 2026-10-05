import Mathlib.LinearAlgebra.Dimension.LinearMap

/-! A small exact tangent-range cancellation lemma for the closed-centralizer
factor. It is purely linear algebra: no dimension count, topology, or source
theorem is hidden here. -/

namespace QuaternionicSymmetry.LinearMapSurjectiveFactor

theorem surjective_of_injective_comp_range_eq
    {R U V W : Type*} [Semiring R]
    [AddCommMonoid U] [Module R U]
    [AddCommMonoid V] [Module R V]
    [AddCommMonoid W] [Module R W]
    (i : V →ₗ[R] W) (f : U →ₗ[R] V)
    (hi : Function.Injective i)
    (hRange : LinearMap.range (i.comp f) = LinearMap.range i) :
    Function.Surjective f := by
  intro v
  have hv : i v ∈ LinearMap.range i := ⟨v, rfl⟩
  rw [← hRange] at hv
  obtain ⟨u, hu⟩ := hv
  refine ⟨u, hi ?_⟩
  exact hu

end QuaternionicSymmetry.LinearMapSurjectiveFactor
