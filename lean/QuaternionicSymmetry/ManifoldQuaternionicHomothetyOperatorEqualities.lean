import QuaternionicSymmetry.ManifoldQuaternionicHomothetyPointwiseComplex
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyDerivativeAccessor

/-! The actual twistor homothety derivative is the identity linear map in
the independently constructed source and target real tangent coordinates. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyOperatorEqualities
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

theorem derivative_eq_id (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    homothetyTwistorDerivative Q s hs z = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro v
  exact homothetyTwistorDerivative_apply Q s hs z v

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyOperatorEqualities
