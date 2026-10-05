import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartScalarBundleSmooth

/-! Smooth tangent coordinates from every actual fixed projective chart,
using its genuine manifold tangent map and the standard smooth tangent
bundle/model-space homeomorphism. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentCoordinates

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartSmooth
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveManifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev ScalarModel := ℍ × ℂ

def fixedTangentCoordinates (p : M) (i : Fin 2)
    (t : TangentBundle productModel (SpinorBundleTotal Q)) :
    ScalarModel × ScalarModel :=
  tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ScalarModel)
    (tangentMap productModel 𝓘(ℝ, ScalarModel)
      (fixedProjectiveChart Q p i) t)

theorem fixedTangentCoordinates_apply (p : M) (i : Fin 2)
    (t : TangentBundle productModel (SpinorBundleTotal Q)) :
    fixedTangentCoordinates Q p i t =
      (fixedProjectiveChart Q p i t.1,
        mfderiv productModel 𝓘(ℝ, ScalarModel)
          (fixedProjectiveChart Q p i) t.1 t.2) := rfl

theorem fixedTangentCoordinates_smoothOn (p : M) (i : Fin 2) :
    ContMDiffOn productModel.tangent
      (𝓘(ℝ, ScalarModel).prod 𝓘(ℝ, ScalarModel)) ∞
      (fixedTangentCoordinates Q p i)
      ((fun t : TangentBundle productModel (SpinorBundleTotal Q) => t.1) ⁻¹'
        fixedChartSource Q p i) := by
  let s := fixedChartSource Q p i
  have hs : IsOpen s := fixedChartSource_isOpen Q p i
  have hwithin : ContMDiffOn productModel.tangent
      (𝓘(ℝ, ScalarModel)).tangent ∞
      (tangentMapWithin productModel 𝓘(ℝ, ScalarModel)
        (fixedProjectiveChart Q p i) s)
      ((fun t : TangentBundle productModel (SpinorBundleTotal Q) => t.1) ⁻¹' s) :=
    (fixedProjectiveChart_smoothOn Q p i).contMDiffOn_tangentMapWithin
      (by simp) hs.uniqueMDiffOn
  have hmap : ContMDiffOn productModel.tangent
      (𝓘(ℝ, ScalarModel)).tangent ∞
      (tangentMap productModel 𝓘(ℝ, ScalarModel)
        (fixedProjectiveChart Q p i))
      ((fun t : TangentBundle productModel (SpinorBundleTotal Q) => t.1) ⁻¹' s) := by
    apply hwithin.congr
    intro t ht
    simp only [tangentMapWithin, tangentMap]
    rw [mfderivWithin_of_mem_nhds (hs.mem_nhds ht)]
  have hmodel : ContMDiff (𝓘(ℝ, ScalarModel)).tangent
      (𝓘(ℝ, ScalarModel).prod 𝓘(ℝ, ScalarModel)) ∞
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ScalarModel)) :=
    contMDiff_tangentBundleModelSpaceHomeomorph
  simpa only [chartedSpaceSelf_prod] using hmodel.comp_contMDiffOn hmap

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentCoordinates
