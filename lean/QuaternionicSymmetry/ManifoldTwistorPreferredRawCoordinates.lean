import QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

/-! The preferred tangent-coordinate equivalence is a raw base–sphere
coordinate formula. Its only geometric-sphere input is the second coordinate;
no metric or connection record enters its value. -/

namespace QuaternionicSymmetry.ManifoldTwistorPreferredRawCoordinates
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

/-- The coordinate-only preferred tangent equivalence for any raw sphere
coefficient, independent of the quaternionic metric data. -/
def rawPreferredEquiv (a : geometricSphere) :
    (E × EuclideanSpace ℝ (Fin 2)) ≃ₗ[ℝ]
      E × verticalSubmodule (coefficientSphereHomeomorph.symm a) :=
  LinearEquiv.prodCongr (LinearEquiv.refl ℝ E)
    (sphereTangentVerticalEquiv (coefficientSphereHomeomorph.symm a))

/-- The actual twistor preferred map is exactly the raw coordinate map.
This is proved for a generic metric, before any homothety is substituted. -/
theorem preferredTangentEquiv_apply_raw
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (z : SphereBundleTotal Q) (v : E × EuclideanSpace ℝ (Fin 2)) :
    preferredTangentEquiv Q z v = rawPreferredEquiv (E := E) z.2 v := rfl

end
end QuaternionicSymmetry.ManifoldTwistorPreferredRawCoordinates
