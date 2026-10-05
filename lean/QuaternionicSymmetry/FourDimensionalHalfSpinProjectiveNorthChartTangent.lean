import QuaternionicSymmetry.QuaternionicNormalizerSphereTangentCovariance
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthMFDeriv

/-! The true north projective tangent model agrees with the `[1:z]`
affine coordinate tangent, including the differential of chart inverse. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartTangent

open scoped Manifold ContDiff Topology
open FourDimensionalHalfSpinProjectiveNorthChartAt
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveMobiusAction
  ComplexProjectiveTopology

noncomputable section

theorem north_chart_mfderiv :
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
      (projectiveChart 1 0) (affineSpinorPoint 0) =
        ContinuousLinearMap.id ℝ (Fin 1 → ℂ) := by
  rw [← north_chartAt]
  simp only [mfderiv, mfld_simps]
  have hmd : MDifferentiableAt 𝓘(ℝ, Fin 1 → ℂ)
      𝓘(ℝ, Fin 1 → ℂ)
      (chartAt (Fin 1 → ℂ) (affineSpinorPoint 0))
      (affineSpinorPoint 0) :=
    ((mdifferentiable_chart (I := 𝓘(ℝ, Fin 1 → ℂ))
      (affineSpinorPoint 0)).mdifferentiableAt
      (mem_chart_source _ _))
  rw [if_pos hmd, fderivWithin_univ]
  have heq :
      ((chartAt (Fin 1 → ℂ) (affineSpinorPoint 0)) ∘
        (chartAt (Fin 1 → ℂ) (affineSpinorPoint 0)).symm) =ᶠ[𝓝 (0 : Fin 1 → ℂ)] id := by
    filter_upwards [(chartAt (Fin 1 → ℂ) (affineSpinorPoint 0)).open_target.mem_nhds
      (by rw [north_chartAt, projectiveChart_target]; trivial)] with w hw
    exact (chartAt (Fin 1 → ℂ) (affineSpinorPoint 0)).right_inv hw
  rw [north_chart_coordinate]
  rw [heq.fderiv_eq]
  simp

theorem north_chart_inverse_mfderiv :
    mfderiv 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, Fin 1 → ℂ)
      (projectiveChart 1 0).symm (0 : Fin 1 → ℂ) =
        ContinuousLinearMap.id ℝ (Fin 1 → ℂ) := by
  have htarget : (0 : Fin 1 → ℂ) ∈ (projectiveChart 1 0).target := by
    rw [projectiveChart_target]
    trivial
  have h := ((mdifferentiable_chart (I := 𝓘(ℝ, Fin 1 → ℂ))
    (affineSpinorPoint 0))).comp_symm_deriv (by
      simpa only [north_chartAt] using htarget)
  have hp0 : (projectiveChart 1 0).symm (0 : Fin 1 → ℂ) =
      affineSpinorPoint 0 := by
    rw [affineSpinorPoint_eq_projectiveChart]
    congr 1
    funext i
    fin_cases i
    simp
  rw [north_chartAt, hp0, north_chart_mfderiv] at h
  simpa only [ContinuousLinearMap.id_comp] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartTangent
