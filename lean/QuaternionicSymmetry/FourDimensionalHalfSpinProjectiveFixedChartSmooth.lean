import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartAtlasSource

/-! Every fixed base/CP¹ affine chart is C∞ on its genuine open source,
because it is exactly a chart of the independent projective-spinor manifold
followed by the checked linear scalar-coordinate equivalence. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartSmooth

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartAsAtlas
  FourDimensionalHalfSpinProjectiveFixedChartAtlasSource
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveFixedChartPole
  FourDimensionalHalfSpinProjectiveScalarFiber
  FourDimensionalHalfSpinProjectiveManifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)

theorem fixedProjectiveChart_smoothOn (p : M) (i : Fin 2) :
    ContMDiffOn productModel 𝓘(ℝ, ℍ × ℂ) ∞
      (fixedProjectiveChart Q p i) (fixedChartSource Q p i) := by
  rw [fixedChartSource_eq_poleAtlas_source Q p i]
  have hchart : ContMDiffOn productModel
      𝓘(ℝ, ℍ × (Fin 1 → ℂ)) ∞
      (extChartAt productModel (chartPole Q p i))
      (extChartAt productModel (chartPole Q p i)).source := by
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := productModel) (x := chartPole Q p i))
  have h := projectiveTangentModelEquiv.toContinuousLinearMap.contMDiff.comp_contMDiffOn
    hchart
  exact h.congr (by
    intro w hw
    simpa only [Function.comp_apply] using fixedChart_eq_poleAtlas Q p i w)

theorem fixedProjectiveChart_smoothAt (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i) :
    ContMDiffAt productModel 𝓘(ℝ, ℍ × ℂ) ∞
      (fixedProjectiveChart Q p i) z :=
  (fixedProjectiveChart_smoothOn Q p i).contMDiffAt
    ((fixedChartSource_isOpen Q p i).mem_nhds hz)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartSmooth
