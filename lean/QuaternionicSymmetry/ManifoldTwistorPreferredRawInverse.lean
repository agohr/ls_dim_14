import QuaternionicSymmetry.ManifoldTwistorPreferredRawCoordinates

/-! The inverse preferred tangent-coordinate equivalence has the same raw
base–sphere formula, established once for arbitrary quaternionic data. -/

namespace QuaternionicSymmetry.ManifoldTwistorPreferredRawInverse
open ManifoldTwistorPreferredRawCoordinates
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem preferredTangentEquiv_symm_apply_raw
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (z : SphereBundleTotal Q)
    (w : E × verticalSubmodule (coefficientSphereHomeomorph.symm z.2)) :
    (preferredTangentEquiv Q z).symm w =
      (rawPreferredEquiv (E := E) z.2).symm w := rfl

end
end QuaternionicSymmetry.ManifoldTwistorPreferredRawInverse
