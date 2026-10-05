import QuaternionicSymmetry.ManifoldTwistorRawGlobalComplexFormula
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorLocal

/-! Constant metric homothety preserves the actual raw global twistor
operator at each independently typed base/chart/sphere coordinate. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawComplex
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorLocal
open ManifoldTwistorRawGlobalComplexFormula
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem rawTwistorComplex_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : geometricSphere) :
    rawTwistorComplex (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) p y hy a =
      rawTwistorComplex Q D p y hy a := by
  unfold rawTwistorComplex
  rw [localTwistorComplex_rescale]

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawComplex
