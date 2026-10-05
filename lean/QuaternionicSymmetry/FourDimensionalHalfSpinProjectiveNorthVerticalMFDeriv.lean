import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartTangent
import QuaternionicSymmetry.FourDimensionalHalfSpinAntipodalVerticalSign

/-! The explicit affine north sign is stated on the true manifold
differential into the independently smooth sphere. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthVerticalMFDeriv

open scoped Manifold
open FourDimensionalHalfSpinProjectiveNorthChartTangent
  FourDimensionalHalfSpinProjectiveNorthMFDeriv
  FourDimensionalHalfSpinProjectiveNorthChartDerivative
  FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinProjectiveNormalizerTransitive
  FourDimensionalHalfSpinProjectiveMobiusAction
  FourDimensionalHalfSpinHopfProjectiveSmooth
  ManifoldTwistorCoefficientSphere
  ManifoldTwistorVerticalComplex
  FourDimensionalTwistorHomogeneousFiber
  ComplexProjectiveTopology

noncomputable section

local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

theorem north_hopf_sphere_mfderiv :
    (sphereTangentMap (coefficientSphereHomeomorph north)).comp
      (mfderiv 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) projectiveHopfGeometric
        (affineSpinorPoint 0)) = northEuclideanDifferential := by
  have h := north_mfderiv_chain
  rw [north_chart_inverse_mfderiv] at h
  simp only [ContinuousLinearMap.comp_id] at h
  have hp0 : (projectiveChart 1 0).symm (0 : Fin 1 → ℂ) =
      affineSpinorPoint 0 := by
    rw [affineSpinorPoint_eq_projectiveChart]
    congr 1
    funext i
    fin_cases i
    simp
  rw [hp0] at h
  have hs : projectiveHopfGeometric (affineSpinorPoint 0) =
      coefficientSphereHomeomorph north := by
    simp [projectiveHopfGeometric, projectiveHopf_affineZero]
  rw [hs] at h
  exact h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthVerticalMFDeriv
