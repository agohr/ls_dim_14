import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentCoordinates

/-! Smooth inverse tangent coordinates on the independently constructed
projective atlas target. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentInverse

open scoped Quaternion Manifold ContDiff
open FourDimensionalHalfSpinProjectiveFixedChartTangentCoordinates
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveManifold

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev ScalarModel := ℍ × ℂ

def fixedTangentCoordinatesInv (p : M) (i : Fin 2)
    (r : ScalarModel × ScalarModel) :
    TangentBundle productModel (SpinorBundleTotal Q) :=
  tangentMap 𝓘(ℝ, ScalarModel) productModel
    (fixedProjectiveChartInv Q p i)
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ScalarModel)).symm r)

theorem fixedTangentCoordinatesInv_smoothOn (p : M) (i : Fin 2) :
    ContMDiffOn (𝓘(ℝ, ScalarModel).prod 𝓘(ℝ, ScalarModel))
      productModel.tangent ∞ (fixedTangentCoordinatesInv Q p i)
      {r | r.1 ∈ fixedChartTarget Q p i} := by
  let s := fixedChartTarget Q p i
  have hs : IsOpen s := fixedChartTarget_isOpen Q p i
  have hwithin : ContMDiffOn (𝓘(ℝ, ScalarModel)).tangent productModel.tangent ∞
      (tangentMapWithin 𝓘(ℝ, ScalarModel) productModel
        (fixedProjectiveChartInv Q p i) s)
      ((fun t : TangentBundle 𝓘(ℝ, ScalarModel) ScalarModel => t.1) ⁻¹' s) :=
    (fixedChartInv_smoothOn Q p i).contMDiffOn_tangentMapWithin
      (by simp) hs.uniqueMDiffOn
  have hmap : ContMDiffOn (𝓘(ℝ, ScalarModel)).tangent productModel.tangent ∞
      (tangentMap 𝓘(ℝ, ScalarModel) productModel
        (fixedProjectiveChartInv Q p i))
      ((fun t : TangentBundle 𝓘(ℝ, ScalarModel) ScalarModel => t.1) ⁻¹' s) := by
    apply hwithin.congr
    intro t ht
    simp only [tangentMapWithin, tangentMap]
    rw [mfderivWithin_of_mem_nhds (hs.mem_nhds ht)]
  have hinv : ContMDiff
      (𝓘(ℝ, ScalarModel).prod 𝓘(ℝ, ScalarModel))
      (𝓘(ℝ, ScalarModel)).tangent ∞
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ScalarModel)).symm :=
    contMDiff_tangentBundleModelSpaceHomeomorph_symm
  have hmaps : Set.MapsTo
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ScalarModel)).symm
      {r | r.1 ∈ s}
      ((fun t : TangentBundle 𝓘(ℝ, ScalarModel) ScalarModel => t.1) ⁻¹' s) := by
    intro r hr
    simpa only [Set.mem_preimage, tangentBundleModelSpaceHomeomorph_coe_symm,
      Function.comp_apply, Prod.fst] using hr
  simpa only [chartedSpaceSelf_prod] using hmap.comp hinv.contMDiffOn hmaps

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentInverse
