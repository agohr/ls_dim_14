import QuaternionicSymmetry.ManifoldQuaternionicHomothetyRawComplex
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyExplicitDerivative

/-! The independently defined actual global twistor almost-complex
operators are intertwined by the derivative of the genuine smooth
homothety diffeomorphism. The proof passes through a common raw coordinate
formula; it never coerces a point of the rescaled bundle to the original
bundle in a theorem type. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyGlobalComplexIntertwine
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyExplicitDerivative
open ManifoldQuaternionicHomothetyRawComplex
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

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

theorem tangentComplex_rescale_intertwine (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    (@mfderiv ℝ _ _ _ _ _ _ (J (E := E))
      (SphereBundleTotal (rescaleMetric Q s hs))
      (sphereCore (rescaleMetric Q s hs)).toTopologicalSpace
      (coreCharts (sphereCore (rescaleMetric Q s hs)))
      _ _ _ _ _ (J (E := E)) (SphereBundleTotal Q)
      (sphereCore Q).toTopologicalSpace (coreCharts (sphereCore Q))
      (sphereTotalDiffeomorph Q s hs) z
      (tangentComplex (rescaleMetric Q s hs)
        (rescaleConnection Q D s hs) z v)) =
      tangentComplex Q D (sphereTotalDiffeomorph Q s hs z)
        ((@mfderiv ℝ _ _ _ _ _ _ (J (E := E))
          (SphereBundleTotal (rescaleMetric Q s hs))
          (sphereCore (rescaleMetric Q s hs)).toTopologicalSpace
          (coreCharts (sphereCore (rescaleMetric Q s hs)))
          _ _ _ _ _ (J (E := E)) (SphereBundleTotal Q)
          (sphereCore Q).toTopologicalSpace (coreCharts (sphereCore Q))
          (sphereTotalDiffeomorph Q s hs) z) v) := by
  rw [sphereTotalDiffeomorph_mfderiv_apply Q s hs z
    (tangentComplex (rescaleMetric Q s hs)
      (rescaleConnection Q D s hs) z v)]
  rw [sphereTotalDiffeomorph_mfderiv_apply Q s hs z v]
  rw [tangentComplex_apply_raw (rescaleMetric Q s hs)
    (rescaleConnection Q D s hs) z v]
  rw [tangentComplex_apply_raw Q D (sphereTotalDiffeomorph Q s hs z) v]
  have hb : (sphereTotalDiffeomorph Q s hs z).1 = z.1 :=
    sphereTotalDiffeomorph_proj Q s hs z
  have ha : (sphereTotalDiffeomorph Q s hs z).2 = z.2 :=
    congrArg (fun w : SphereBundleTotal Q => w.2)
      (sphereTotalDiffeomorph_apply Q s hs z)
  rw [hb, ha]
  exact congrArg (fun L => L v)
    (rawTwistorComplex_rescale Q D s hs z.1
      (extChartAt 𝓘(ℝ,E) z.1 z.1)
      ((extChartAt 𝓘(ℝ,E) z.1).map_source
        (mem_extChartAt_source z.1)) z.2)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyGlobalComplexIntertwine
