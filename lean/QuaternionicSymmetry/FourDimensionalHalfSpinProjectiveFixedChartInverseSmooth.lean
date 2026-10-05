import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartSmooth

/-! The explicit fixed affine-coordinate inverse is smooth on the true
target of the independent pole-centered atlas chart. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth

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

theorem fixedProjectiveChartInv_smoothAt (p : M) (i : Fin 2)
    (yw : ℍ × ℂ)
    (hy : projectiveTangentModelEquiv.symm yw ∈
      (extChartAt productModel (chartPole Q p i)).target) :
    ContMDiffAt 𝓘(ℝ, ℍ × ℂ) productModel ∞
      (fixedProjectiveChartInv Q p i) yw := by
  have hlin : ContMDiffAt 𝓘(ℝ, ℍ × ℂ)
      𝓘(ℝ, ℍ × (Fin 1 → ℂ)) ∞
      projectiveTangentModelEquiv.symm yw :=
    projectiveTangentModelEquiv.symm.contDiff.contMDiff.contMDiffAt
  have hchart : ContMDiffAt 𝓘(ℝ, ℍ × (Fin 1 → ℂ))
      productModel ∞
      (extChartAt productModel (chartPole Q p i)).symm
      (projectiveTangentModelEquiv.symm yw) :=
    (contMDiffOn_extChartAt_symm (I := productModel) (x := chartPole Q p i)).contMDiffAt
      ((isOpen_extChartAt_target (I := productModel) (x := chartPole Q p i)).mem_nhds hy)
  have h := hchart.comp yw hlin
  have hfun : fixedProjectiveChartInv Q p i =
      (fun v => (extChartAt productModel (chartPole Q p i)).symm
        (projectiveTangentModelEquiv.symm v)) := by
    funext v
    exact fixedChartInv_eq_poleAtlas Q p i v
  simpa only [hfun, Function.comp_def] using h

theorem fixedProjectiveChartInv_smoothAt_actual (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i) :
    ContMDiffAt 𝓘(ℝ, ℍ × ℂ) productModel ∞
      (fixedProjectiveChartInv Q p i)
      (fixedProjectiveChart Q p i z) := by
  apply fixedProjectiveChartInv_smoothAt Q p i
  rw [fixedChart_eq_poleAtlas Q p i z]
  simp only [projectiveTangentModelEquiv.symm_apply_apply]
  exact (extChartAt productModel (chartPole Q p i)).map_source
    ((fixedChartSource_eq_poleAtlas_source Q p i) ▸ hz)

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth
