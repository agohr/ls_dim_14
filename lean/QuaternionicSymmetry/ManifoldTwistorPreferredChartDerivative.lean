import QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

/-! The preferred bundle trivialization identifies tangent directions at a
twistor point with the base–sphere product tangent by its actual manifold
derivative. This identifies the chart model used for the pointwise operator
with the differentiable sphere-bundle atlas. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev productModel := (𝓘(ℝ,E)).prod (𝓡 2)

local instance : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
    (SphereBundleTotal Q) := by
  letI : ChartedSpace (ModelProd E (EuclideanSpace ℝ (Fin 2)))
      (M × geometricSphere) := inferInstance
  exact ChartedSpace.comp _ (M × geometricSphere) _

/-- The actual manifold derivative of the preferred total-space
trivialization is the identity on the product tangent model. Its fiber
coordinate at the center is the original geometric sphere point. -/
theorem preferredTriv_mfderiv (z : SphereBundleTotal Q) :
    mfderiv (M := SphereBundleTotal Q) (M' := M × geometricSphere)
      (productModel (E := E)) (productModel (E := E))
      (((sphereCore Q).localTriv (achart E z.1) :
        SphereBundleTotal Q → M × geometricSphere)) z =
        ContinuousLinearMap.id ℝ
          (TangentSpace (productModel (E := E)) z) := by
  have htriv : HasMFDerivAt (M := SphereBundleTotal Q)
      (M' := M × geometricSphere) (productModel (E := E))
      (productModel (E := E))
      (((sphereCore Q).localTriv (achart E z.1) :
        SphereBundleTotal Q → M × geometricSphere)) z
      (ContinuousLinearMap.id ℝ _) := by
    change HasMFDerivAt (productModel (E := E)) (productModel (E := E))
      (chartAt (M × geometricSphere) z) z (ContinuousLinearMap.id ℝ _)
    constructor
    · exact ((sphereCore Q).localTriv (achart E z.1)).continuousOn.continuousAt
        (((sphereCore Q).localTriv (achart E z.1)).open_source.mem_nhds
          ((sphereCore Q).mem_baseSet_at z.1))
    · apply (hasFDerivWithinAt_id _ (Set.range (productModel (E := E)))).congr_of_eventuallyEq
      · filter_upwards [extChartAt_target_mem_nhdsWithin
          (I := productModel (E := E)) z] with y hy
        exact writtenInExtChartAt_chartAt_comp z hy
      · exact writtenInExtChartAt_chartAt_comp z
          ((extChartAt (productModel (E := E)) z).map_source
            (mem_extChartAt_source z))
  exact htriv.mfderiv

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
