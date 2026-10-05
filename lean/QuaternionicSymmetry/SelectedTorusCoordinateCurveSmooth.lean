import QuaternionicSymmetry.SelectedTorusCompactExponentialSmooth
import QuaternionicSymmetry.TorusWeightCoordinateExponentialDerivative

/-! Each literal one-coordinate circle exponential is smooth in any
selected torus atlas for which the full coordinate exponential has
already been proved smooth. -/

namespace QuaternionicSymmetry.SelectedTorusCoordinateCurveSmooth

open SelectedTorusCompactExponentialSmooth
open TorusWeightCoordinateExponentialDerivative
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

def coordinateLine {r : ℕ} (i : Fin r) (t : ℝ) : Fin r → ℝ :=
  Pi.single i t

theorem coordinateLine_smooth {r : ℕ} (i : Fin r) :
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin r → ℝ) ∞ (coordinateLine i) := by
  apply ContDiff.contMDiff
  apply (contDiff_pi).2
  intro j
  by_cases h : j = i
  · subst j
    simpa only [coordinateLine, Pi.single_eq_same] using
      (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ))
  · simpa only [coordinateLine, Pi.single_eq_of_ne h] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))

theorem coordinateCircleExp_eq {r : ℕ} (i : Fin r) :
    coordinateCircleExp i = circleExpPi r ∘ coordinateLine i := by
  classical
  funext t j
  by_cases h : j = i
  · subst j
    simp [coordinateCircleExp, circleExpPi, coordinateLine]
  · simp [coordinateCircleExp, circleExpPi, coordinateLine, h]

theorem coordinateCircleExp_smooth_of_exp
    {r d : ℕ} (i : Fin r)
    (hChart : ChartedSpace (Fin d → ℝ) (Torus r))
    (hExp : letI := hChart
      ContMDiff 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin d → ℝ) ∞ (circleExpPi r)) :
    letI := hChart
    ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,Fin d → ℝ) ∞
      (coordinateCircleExp i) := by
  letI : ChartedSpace (Fin d → ℝ) (Torus r) := hChart
  rw [coordinateCircleExp_eq]
  exact hExp.comp (coordinateLine_smooth i)

end
end QuaternionicSymmetry.SelectedTorusCoordinateCurveSmooth
