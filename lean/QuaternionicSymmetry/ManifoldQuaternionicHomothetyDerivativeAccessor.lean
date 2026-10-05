import QuaternionicSymmetry.ManifoldQuaternionicHomothetyExplicitDerivative

/-! A compact name for the *actual* derivative of the smooth homothety
twistor diffeomorphism, with distinct source and target core atlases explicit.
No derivative or manifold structure is transported by definition. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyDerivativeAccessor
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldQuaternionicHomothetyExplicitDerivative
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- Exactly `mfderiv` of the genuine sphere-total-space diffeomorphism,
with the two independently constructed core atlases fixed explicitly. -/
def homothetyTwistorDerivative (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs)) :
    (E × EuclideanSpace ℝ (Fin 2)) →L[ℝ]
      (E × EuclideanSpace ℝ (Fin 2)) :=
  @mfderiv ℝ _ _ _ _ _ _ (J (E := E))
    (SphereBundleTotal (rescaleMetric Q s hs))
    (sphereCore (rescaleMetric Q s hs)).toTopologicalSpace
    (coreCharts (sphereCore (rescaleMetric Q s hs)))
    _ _ _ _ _ (J (E := E)) (SphereBundleTotal Q)
    (sphereCore Q).toTopologicalSpace (coreCharts (sphereCore Q))
    (sphereTotalDiffeomorph Q s hs) z

theorem homothetyTwistorDerivative_apply (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    homothetyTwistorDerivative Q s hs z v = v :=
  sphereTotalDiffeomorph_mfderiv_apply Q s hs z v

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyDerivativeAccessor
