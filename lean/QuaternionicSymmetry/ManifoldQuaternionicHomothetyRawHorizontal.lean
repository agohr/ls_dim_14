import QuaternionicSymmetry.ManifoldTwistorRawHorizontalCoefficient
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorLocal

/-! The raw connection-horizontal coefficient is unchanged by constant
metric rescaling; this is the contact-plane kernel comparison before any
dependent total-space tangent identification. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawHorizontal
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorLocal
open ManifoldTwistorRawHorizontalCoefficient
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem rawHorizontalCoefficient_rescale (s : ℝ) (hs : s ≠ 0)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target)
    (a : geometricSphere) :
    rawHorizontalCoefficient (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) p y hy a =
        rawHorizontalCoefficient Q D p y hy a := by
  unfold rawHorizontalCoefficient
  rw [connectionSplit_rescale Q D s hs p y hy
    (coefficientSphereHomeomorph.symm a)]

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawHorizontal
