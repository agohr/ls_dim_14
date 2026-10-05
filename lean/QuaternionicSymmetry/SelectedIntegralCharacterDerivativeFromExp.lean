import QuaternionicSymmetry.SelectedIntegralCharacterDerivativeNonzero
import QuaternionicSymmetry.SelectedTorusCoordinateCurveSmooth

/-! The selected-atlas coordinate exponential smoothness discharges the
only analytic hypothesis in nonvanishing of a literal nonzero integral
character's identity differential. -/

namespace QuaternionicSymmetry.SelectedIntegralCharacterDerivativeFromExp

open SelectedIntegralCharacterDerivativeNonzero
open SelectedTorusCoordinateCurveSmooth
open TorusWeightCoordinateExponentialDerivative
open SelectedTorusCompactExponentialSmooth
open SelectedIntegralCharacterSmooth
open ManifoldQuaternionicTorusAction
open GeneralClosedSubgroupLieSource GeneralSmoothMapSource
open scoped Manifold ContDiff
noncomputable section

theorem weightCharacter_mfderiv_ne_zero_of_exp
    {r d : ℕ} (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hManifold : letI := hChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hLie : letI := hChart
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hExp : letI := hChart
      ContMDiff 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ) ∞ (circleExpPi r)) :
    letI := hChart
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    apply hμ
    funext i
    simpa using not_exists.mp h i
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hManifold
  have hχ : MDifferentiableAt 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 :=
    (weightCharacter_complex_contMDiff μ hChart hManifold hLie
      hClosed hImm hLee).mdifferentiableAt (by simp)
  have hCurve : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ)
      (coordinateCircleExp i) 0 :=
    (coordinateCircleExp_smooth_of_exp i hChart hExp).mdifferentiableAt (by simp)
  exact weightCharacter_mfderiv_ne_zero_of_coordinateCurve
    μ i hi hChart hManifold hχ hCurve

end
end QuaternionicSymmetry.SelectedIntegralCharacterDerivativeFromExp
