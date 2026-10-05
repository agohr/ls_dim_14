import QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChart

/-! The fixed-coordinate inverse at a preferred center is the inverse
of the genuine independent projective-manifold chart, after the checked
one-complex-coordinate linear equivalence. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartInverse

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectivePreferredChart
  FourDimensionalHalfSpinProjectiveGlobalPointwiseAHS
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveAllCoreChartDomain
  ComplexProjectiveTopology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem preferred_fixedChartInv_eq_extChartAt_symm (z : SpinorBundleTotal Q)
    (yw : ℍ × ℂ) :
    fixedProjectiveChartInv Q z.1 (preferredProjectiveChartIndex z.2) yw =
      (extChartAt productModel z).symm
        (projectiveTangentModelEquiv.symm yw) := by
  change fixedProjectiveChartInv Q z.1
      (preferredProjectiveChartIndex z.2) yw =
      (chartAt (ModelProd ℍ (Fin 1 → ℂ)) z).symm
        (projectiveTangentModelEquiv.symm yw)
  rw [chartAt_comp, FiberBundle.chartedSpace'_chartAt]
  rw [OpenPartialHomeomorph.coe_trans_symm]
  simp only [Function.comp_apply, prodChartedSpace_chartAt]
  rw [OpenPartialHomeomorph.prod_symm]
  rw [OpenPartialHomeomorph.prod_apply]
  change
    ((projectiveSpinorCore Q).localTriv (achart ℍ z.1)).toOpenPartialHomeomorph.symm
      ((extChartAt 𝓘(ℝ, ℍ) z.1).symm yw.1,
        indexedSourcePoint (preferredProjectiveChartIndex z.2) yw.2) =
    ((projectiveSpinorCore Q).localTriv (achart ℍ z.1)).toOpenPartialHomeomorph.symm
      ((extChartAt 𝓘(ℝ, ℍ) z.1).symm yw.1,
        (chartAt (Fin 1 → ℂ)
          (((projectiveSpinorCore Q).localTriv (achart ℍ z.1)) z).2).symm
          (scalarFiberEquiv.symm yw.2))
  rw [preferred_localTriv Q z]
  rw [scalarFiberEquiv_symm_apply]
  rw [selected_projective_chart]
  congr 1
  generalize hi : preferredProjectiveChartIndex z.2 = i
  fin_cases i
  · apply Prod.ext
    · rfl
    · exact affineSpinorPoint_eq_projectiveChart yw.2
  · rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectivePreferredFixedChartInverse
