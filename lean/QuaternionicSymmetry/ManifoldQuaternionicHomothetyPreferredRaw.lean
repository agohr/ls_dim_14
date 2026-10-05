import QuaternionicSymmetry.ManifoldTwistorPreferredRawCoordinates
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCore

/-! Metric homothety changes neither the value of the preferred tangent
coordinate map nor the raw two-sphere coefficient. The comparison is made
through the already checked generic raw-coordinate formula. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyPreferredRaw
open ManifoldQuaternionicHomothetyReduction
open ManifoldTwistorPreferredRawCoordinates
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem preferredTangentEquiv_rescale_apply (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    preferredTangentEquiv (rescaleMetric Q s hs) z v =
      preferredTangentEquiv Q z v := by
  calc
    _ = rawPreferredEquiv (E := E) z.2 v :=
      preferredTangentEquiv_apply_raw (rescaleMetric Q s hs) z v
    _ = _ := (preferredTangentEquiv_apply_raw Q z v).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyPreferredRaw
