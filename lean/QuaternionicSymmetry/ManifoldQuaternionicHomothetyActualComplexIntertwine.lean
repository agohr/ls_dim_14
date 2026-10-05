import QuaternionicSymmetry.ManifoldQuaternionicHomothetyPointwiseComplex
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyDerivativeAccessor

/-! Actual global twistor almost-complex intertwining under constant
homothety. Both operators were independently constructed; the derivative is
the actual `mfderiv` of the smooth homothety diffeomorphism, not a transported
replacement. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualComplexIntertwine
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyPointwiseComplex
open ManifoldQuaternionicHomothetyDerivativeAccessor
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem tangentComplex_rescale_intertwine (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    homothetyTwistorDerivative Q s hs z
      (tangentComplex (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) z v) =
      tangentComplex Q D (sphereTotalDiffeomorph Q s hs z)
        (homothetyTwistorDerivative Q s hs z v) := by
  calc
    _ = tangentComplex (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) z v :=
      homothetyTwistorDerivative_apply Q s hs z _
    _ = tangentComplex Q D (sphereTotalDiffeomorph Q s hs z) v :=
      tangentComplex_at_homothety_point Q D s hs z v
    _ = _ :=
      congrArg
        (fun w : E × EuclideanSpace ℝ (Fin 2) =>
          tangentComplex Q D (sphereTotalDiffeomorph Q s hs z) w)
        (homothetyTwistorDerivative_apply Q s hs z v).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyActualComplexIntertwine
