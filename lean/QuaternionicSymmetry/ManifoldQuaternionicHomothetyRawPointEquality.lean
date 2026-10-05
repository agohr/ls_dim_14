import QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawComplex
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorSmooth

/-! The raw complex operator agrees at the separately typed source and
target points of the genuine homothety twistor diffeomorphism. This is the
point-level bridge before any tangent-bundle derivative is mentioned. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawPointEquality
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyRawComplex
open ManifoldTwistorRawGlobalComplexFormula
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem rawTwistorComplex_at_homothety_point
    (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    rawTwistorComplex (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) z.1
      (extChartAt 𝓘(ℝ,E) z.1 z.1)
      ((extChartAt 𝓘(ℝ,E) z.1).map_source (mem_extChartAt_source z.1)) z.2 =
    rawTwistorComplex Q D (sphereTotalDiffeomorph Q s hs z).1
      (extChartAt 𝓘(ℝ,E) (sphereTotalDiffeomorph Q s hs z).1
        (sphereTotalDiffeomorph Q s hs z).1)
      ((extChartAt 𝓘(ℝ,E) (sphereTotalDiffeomorph Q s hs z).1).map_source
        (mem_extChartAt_source (sphereTotalDiffeomorph Q s hs z).1))
      (sphereTotalDiffeomorph Q s hs z).2 := by
  have hb : (sphereTotalDiffeomorph Q s hs z).1 = z.1 :=
    sphereTotalDiffeomorph_proj Q s hs z
  have ha : (sphereTotalDiffeomorph Q s hs z).2 = z.2 :=
    congrArg (fun w : SphereBundleTotal Q => w.2)
      (sphereTotalDiffeomorph_apply Q s hs z)
  rw [hb, ha]
  exact rawTwistorComplex_rescale Q D s hs z.1
    (extChartAt 𝓘(ℝ,E) z.1 z.1)
    ((extChartAt 𝓘(ℝ,E) z.1).map_source
      (mem_extChartAt_source z.1)) z.2

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawPointEquality
