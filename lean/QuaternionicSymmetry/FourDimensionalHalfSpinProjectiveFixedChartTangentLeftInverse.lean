import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentInverse

/-! Genuine inverse identity for tangent coordinates over the full source of
any fixed projective chart; the derivative is the actual manifold `mfderiv`. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentLeftInverse

open scoped Quaternion Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectiveFixedChartTangentCoordinates
  FourDimensionalHalfSpinProjectiveFixedChartTangentInverse
  FourDimensionalHalfSpinProjectiveFixedChartSmooth
  FourDimensionalHalfSpinProjectiveFixedChartInverseSmooth
  FourDimensionalHalfSpinProjectiveFixedChartGerm
  FourDimensionalHalfSpinProjectiveFixedChartLeftInverse
  FourDimensionalHalfSpinProjectiveFixedChartTarget
  FourDimensionalHalfSpinProjectiveFixedChartCore
  FourDimensionalHalfSpinProjectiveManifold
  FourDimensionalHalfSpinProjectiveCore
  ManifoldQuaternionicReduction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℍ M]
  [IsManifold 𝓘(ℝ, ℍ) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, ℍ)) (M := M) (n := ∞))

private abbrev productModel := 𝓘(ℝ, ℍ).prod 𝓘(ℝ, Fin 1 → ℂ)
private abbrev ScalarModel := ℍ × ℂ

theorem fixedTangentCoordinatesInv_left (p : M) (i : Fin 2)
    (z : SpinorBundleTotal Q) (hz : z ∈ fixedChartSource Q p i)
    (v : TangentSpace productModel z) :
    fixedTangentCoordinatesInv Q p i (fixedTangentCoordinates Q p i ⟨z,v⟩) =
      (⟨z,v⟩ : TangentBundle productModel (SpinorBundleTotal Q)) := by
  let f := fixedProjectiveChart Q p i
  let g := fixedProjectiveChartInv Q p i
  have hF : MDifferentiableAt productModel 𝓘(ℝ, ScalarModel) f z :=
    (fixedProjectiveChart_smoothAt Q p i z hz).mdifferentiableAt (by simp)
  have hG : MDifferentiableAt 𝓘(ℝ, ScalarModel) productModel g (f z) :=
    (fixedProjectiveChartInv_smoothAt_actual Q p i z hz).mdifferentiableAt (by simp)
  have hEq : (g ∘ f) =ᶠ[𝓝 z] id :=
    fixedProjectiveChartInv_left_eventually Q p i z hz
  have hDer := Filter.EventuallyEq.mfderiv_eq
    (I := productModel) (I' := productModel) hEq
  rw [mfderiv_comp z hG hF, mfderiv_id] at hDer
  have hPoint : g (f z) = z := by
    have hp : z.1 ∈ (extChartAt 𝓘(ℝ, ℍ) p).source := by
      have hp' := ((projectiveSpinorCore Q).mem_localTriv_source (achart ℍ p) z).mp hz.1
      rw [← (projectiveSpinorCore Q).baseSet_at] at hp'
      simpa only [projectiveSpinorCore,
        ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart,
        ← extChartAt_source 𝓘(ℝ, ℍ)] using hp'
    exact fixedProjectiveChartInv_left Q p i z hp hz.2
  change tangentMap 𝓘(ℝ, ScalarModel) productModel g
    ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ScalarModel)).symm
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ScalarModel)
        (tangentMap productModel 𝓘(ℝ, ScalarModel) f ⟨z,v⟩))) = _
  rw [Homeomorph.symm_apply_apply]
  apply Bundle.TotalSpace.ext
  · exact hPoint
  · apply heq_of_eq
    change (mfderiv 𝓘(ℝ, ScalarModel) productModel g (f z))
      ((mfderiv productModel 𝓘(ℝ, ScalarModel) f z) v) = v
    exact congrArg (fun L : TangentSpace productModel z →L[ℝ]
      TangentSpace productModel (g (f z)) => L v) hDer

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveFixedChartTangentLeftInverse
