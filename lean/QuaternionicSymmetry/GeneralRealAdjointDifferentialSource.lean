import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Lee's real adjoint-derivative theorem (BG-L9)

Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 20.24
and Theorem 20.27, printed pp. 534--535 (PDF pp. 551--552): for the actual
conjugation `C_g(h)=g*h*g⁻¹`, `Ad_g=d(C_g)_1`, and the differential of the
adjoint orbit at identity is `[u,v]` with Lee's left-invariant convention.
This source concerns arbitrary finite-dimensional real Lie groups, not a
project-specific torus, weight, root, or complex Lie comparison. -/

namespace QuaternionicSymmetry.GeneralRealAdjointDifferentialSource

open scoped Manifold ContDiff
noncomputable section

/-- Literal real adjoint orbit in a supplied real Lie atlas. -/
def adjointOrbitReal {V G : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Group G] [TopologicalSpace G] [ChartedSpace V G]
    [IsManifold 𝓘(ℝ,V) ∞ G] [LieGroup 𝓘(ℝ,V) ∞ G]
    (v : GroupLieAlgebra 𝓘(ℝ,V) G) (g : G) : V :=
  (mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (fun h : G => g * h * g⁻¹) 1) v

/-- The precise general real theorem used as the only Lee BG-L9 input.
The differentiability clause makes later use of the manifold chain rule
explicit; it is part of smoothness of the actual adjoint map. -/
def LeeRealAdjointDifferentialSource : Prop :=
  ∀ {V G : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
    [ChartedSpace V G] [IsManifold 𝓘(ℝ,V) ∞ G]
    [LieGroup 𝓘(ℝ,V) ∞ G],
    letI : ENat.LEInfty (minSmoothness ℝ 3) := by
      simpa only [minSmoothness_of_isRCLikeNormedField] using
        (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))
    ∀ (v : GroupLieAlgebra 𝓘(ℝ,V) G),
      MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbitReal v) 1 ∧
      ∀ (u : GroupLieAlgebra 𝓘(ℝ,V) G),
        mfderiv 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbitReal v) 1 u = ⁅u,v⁆

end
end QuaternionicSymmetry.GeneralRealAdjointDifferentialSource
