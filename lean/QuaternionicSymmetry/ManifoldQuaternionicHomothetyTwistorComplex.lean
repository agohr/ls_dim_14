import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorCharts
import QuaternionicSymmetry.ManifoldQuaternionicHomothetyExplicitDerivative

/-! Constant homothety preserves the actual global twistor almost-complex
operator under the already constructed smooth identity diffeomorphism. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorComplex

open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyConnection
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyTwistorCore
open ManifoldQuaternionicHomothetyTwistorLocal
open ManifoldQuaternionicHomothetyExplicitDerivative
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

/-- The preferred coefficient is literally the same sphere coordinate
before and after constant homothety. -/
theorem preferredCoefficient_rescale (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph.symm
        (sphereTotalDiffeomorph Q s hs z).2 =
      ManifoldTwistorCoefficientSphere.coefficientSphereHomeomorph.symm z.2 := by
  rw [sphereTotalDiffeomorph_apply]

/-- The preferred tangent-coordinate equivalence has no metric scaling:
both source and target use the same underlying base–sphere coordinates. -/
theorem preferredTangentEquiv_rescale (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    preferredTangentEquiv (rescaleMetric Q s hs) z =
      preferredTangentEquiv Q z := rfl

/-- The two independently defined global twistor operators agree pointwise
under the common coordinate carrier. This is separate from the derivative
statement below. -/
theorem tangentComplex_rescale (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    tangentComplex (rescaleMetric Q s hs) (rescaleConnection Q D s hs) z =
      tangentComplex Q D z := by
  unfold tangentComplex
  rw [preferredTangentEquiv_rescale Q s hs z]
  rw [localTwistorComplex_rescale]

/-- The local operator equality is promoted to the actual smooth twistor
tangent bundles via the identity diffeomorphism, with no transported
definition of either operator. -/
theorem tangentComplex_rescale_intertwine
    (s : ℝ) (hs : s ≠ 0)
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
  rw [sphereTotalDiffeomorph_apply]
  exact congrArg (fun L => L v) (tangentComplex_rescale Q D s hs z)

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorComplex
