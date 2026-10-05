import QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawPointEquality

/-! Pointwise equality of the independently built twistor almost-complex
operators at the two correctly typed endpoints of the homothety map. This
does not yet mention a manifold derivative. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyPointwiseComplex
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyRawPointEquality
open ManifoldTwistorRawGlobalComplexFormula
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

theorem tangentComplex_at_homothety_point (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    tangentComplex (rescaleMetric Q s hs) (rescaleConnection Q D s hs) z v =
      tangentComplex Q D (sphereTotalDiffeomorph Q s hs z) v := by
  calc
    _ = rawTwistorComplex (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) z.1
        (extChartAt 𝓘(ℝ,E) z.1 z.1)
        ((extChartAt 𝓘(ℝ,E) z.1).map_source
          (mem_extChartAt_source z.1)) z.2 v :=
      tangentComplex_apply_raw (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) z v
    _ = rawTwistorComplex Q D (sphereTotalDiffeomorph Q s hs z).1
        (extChartAt 𝓘(ℝ,E) (sphereTotalDiffeomorph Q s hs z).1
          (sphereTotalDiffeomorph Q s hs z).1)
        ((extChartAt 𝓘(ℝ,E) (sphereTotalDiffeomorph Q s hs z).1).map_source
          (mem_extChartAt_source (sphereTotalDiffeomorph Q s hs z).1))
        (sphereTotalDiffeomorph Q s hs z).2 v :=
      congrArg (fun L => L v) (rawTwistorComplex_at_homothety_point Q D s hs z)
    _ = _ := (tangentComplex_apply_raw Q D
      (sphereTotalDiffeomorph Q s hs z) v).symm

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyPointwiseComplex
