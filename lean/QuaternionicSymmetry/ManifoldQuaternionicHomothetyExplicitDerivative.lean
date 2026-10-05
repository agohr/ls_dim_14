import QuaternionicSymmetry.ManifoldQuaternionicHomothetyTwistorSmooth

/-! Isolated explicit-instance probe for the derivative of the genuine
homothety twistor identity diffeomorphism. The source and target share a
carrier type but have separately constructed charted-space instances. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHomothetyExplicitDerivative
open ManifoldQuaternionicHomothetyReduction
open ManifoldQuaternionicHomothetyTwistorCore
open ManifoldQuaternionicHomothetyTwistorSmooth
open ManifoldTwistorSphereCore ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- The explicit charted-space instance of an abstract two-sphere core. This
keeps source and target atlases distinct when their carrier types coincide. -/
def coreCharts (Z : FiberBundleCore (atlas E M) M geometricSphere) :
    ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2))) Z.TotalSpace := by
  letI : TopologicalSpace Z.TotalSpace := Z.toTopologicalSpace
  letI : FiberBundle geometricSphere Z.Fiber := Z.fiberBundle
  letI : ChartedSpace (M × geometricSphere) Z.TotalSpace :=
    FiberBundle.chartedSpace'
  letI : ChartedSpace (ModelProd E geometricSphere) Z.TotalSpace := inferInstance
  letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (M × geometricSphere) := inferInstance
  exact ChartedSpace.comp _ (M × geometricSphere) _

/-- The abstract-core atlas used in the explicit derivative statement is
literally the independently constructed actual twistor charted space. -/
theorem coreCharts_sphere_eq
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) :
    coreCharts (sphereCore Q) =
      (inferInstance : ChartedSpace
        (ModelProd E (EuclideanSpace ℝ (Fin 2))) (SphereBundleTotal Q)) := rfl

private theorem abstract_core_identity_derivative
    (Z W : FiberBundleCore (atlas E M) M geometricSphere) (h : W = Z)
    (z : W.TotalSpace) (v : E × EuclideanSpace ℝ (Fin 2)) :
    (@mfderiv ℝ _ _ _ _ _ _ (J (E := E))
      W.TotalSpace W.toTopologicalSpace (coreCharts W)
      _ _ _ _ _ (J (E := E)) Z.TotalSpace Z.toTopologicalSpace (coreCharts Z)
      (id : W.TotalSpace → Z.TotalSpace) z) v = v := by
  cases h
  simp

/-- The actual derivative, with source and target charted instances fixed
explicitly, is identity in the common Euclidean tangent model. -/
theorem sphereTotalDiffeomorph_mfderiv_apply
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) (s : ℝ) (hs : s ≠ 0)
    (z : SphereBundleTotal (rescaleMetric Q s hs))
    (v : E × EuclideanSpace ℝ (Fin 2)) :
    (@mfderiv ℝ _ _ _ _ _ _ (J (E := E))
      (SphereBundleTotal (rescaleMetric Q s hs))
      (sphereCore (rescaleMetric Q s hs)).toTopologicalSpace
      (coreCharts (sphereCore (rescaleMetric Q s hs)))
      _ _ _ _ _ (J (E := E)) (SphereBundleTotal Q)
      (sphereCore Q).toTopologicalSpace (coreCharts (sphereCore Q))
      (sphereTotalDiffeomorph Q s hs) z) v = v := by
  change (@mfderiv ℝ _ _ _ _ _ _ (J (E := E))
      (SphereBundleTotal (rescaleMetric Q s hs))
      (sphereCore (rescaleMetric Q s hs)).toTopologicalSpace
      (coreCharts (sphereCore (rescaleMetric Q s hs)))
      _ _ _ _ _ (J (E := E)) (SphereBundleTotal Q)
      (sphereCore Q).toTopologicalSpace (coreCharts (sphereCore Q))
      (id : SphereBundleTotal (rescaleMetric Q s hs) → SphereBundleTotal Q) z) v = v
  exact abstract_core_identity_derivative (sphereCore Q)
    (sphereCore (rescaleMetric Q s hs)) (sphereCore_rescale Q s hs) z v

end
end QuaternionicSymmetry.ManifoldQuaternionicHomothetyExplicitDerivative
