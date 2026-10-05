import QuaternionicSymmetry.TorusWeightCoordinateExponentialDerivative
import QuaternionicSymmetry.SelectedIntegralCharacterSmooth

/-! A nonzero integral character has nonzero identity differential in
any selected real torus atlas where the literal coordinate circle
exponential is differentiable. The latter is already proved for the
BG-L3 selected atlas by the compact-inclusion immersion route. -/

namespace QuaternionicSymmetry.SelectedIntegralCharacterDerivativeNonzero

open TorusWeightCoordinateExponentialDerivative
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

theorem weightCharacter_mfderiv_ne_zero_of_coordinateCurve
    {r d : ℕ} (μ : Fin r → ℤ) (i : Fin r) (hi : μ i ≠ 0)
    (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hManifold : letI := hChart
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r))
    (hχ : letI := hChart
      MDifferentiableAt 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
        (fun t : Torus r => (weightCharacter μ t : ℂ)) 1)
    (hCurve : letI := hChart
      MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ)
        (coordinateCircleExp i) 0) :
    letI := hChart
    mfderiv 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      (fun t : Torus r => (weightCharacter μ t : ℂ)) 1 ≠ 0 := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (Torus r) := hManifold
  let χ : Torus r → ℂ := fun t => (weightCharacter μ t : ℂ)
  have hχ0 : MDifferentiableAt 𝓘(ℝ,Fin d → ℝ) 𝓘(ℝ,ℂ)
      χ (coordinateCircleExp i 0) := by
    simpa only [χ, coordinateCircleExp_zero] using hχ
  have hcomp := mfderiv_comp (I := 𝓘(ℝ,ℝ))
    (I' := 𝓘(ℝ,Fin d → ℝ)) (I'' := 𝓘(ℝ,ℂ))
    (x := (0 : ℝ)) hχ0 hCurve
  rw [coordinateCircleExp_zero] at hcomp
  have hderiv : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℂ)
      (χ ∘ coordinateCircleExp i) 0 = coordinateCharacterDerivative μ i := by
    rw [mfderiv_eq_fderiv]
    exact (character_curve_hasFDerivAt_zero μ i).fderiv
  intro hzero
  rw [hzero, ContinuousLinearMap.zero_comp] at hcomp
  exact coordinateCharacterDerivative_ne_zero μ i hi
    (hderiv.symm.trans hcomp)

end
end QuaternionicSymmetry.SelectedIntegralCharacterDerivativeNonzero
