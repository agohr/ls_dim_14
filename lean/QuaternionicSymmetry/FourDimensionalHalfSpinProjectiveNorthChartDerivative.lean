import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthDerivative
import QuaternionicSymmetry.FourDimensionalHalfSpinHopfProjectiveSmooth

/-! The north-point Hopf derivative in the genuine affine chart of the
independently constructed projective spinor manifold. This is a real
Fréchet derivative of the actual chart composition, not yet an equality of
manifold tangent maps. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartDerivative

open FourDimensionalHalfSpinProjectiveNorthDerivative
  FourDimensionalHalfSpinHopfNorthDerivative
  FourDimensionalHalfSpinHopfProjectiveSmooth
  FourDimensionalHalfSpinHopfProjectiveDescent
  ComplexProjectiveTopology

noncomputable section

def affineEval : (Fin 1 → ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℂ) 0

def northChartDifferential : (Fin 1 → ℂ) →L[ℝ] (Fin 3 → ℝ) :=
  northDifferential.comp affineEval

theorem projectiveHopf_chart_coordinates (w : Fin 1 → ℂ) :
    (projectiveHopf ((projectiveChart 1 0).symm w)).1 =
      northCoordinates (w 0) := by
  have hw : w = ![w 0] := by
    funext i
    fin_cases i
    rfl
  rw [hw, ← affineSpinorPoint_eq_projectiveChart]
  exact projectiveHopf_affine_coordinates (w 0)

theorem projectiveHopf_chart_hasFDerivAt_north :
    HasFDerivAt
      (fun w : Fin 1 → ℂ =>
        (projectiveHopf ((projectiveChart 1 0).symm w)).1)
      northChartDifferential 0 := by
  have houter : HasFDerivAt northCoordinates northDifferential
      (affineEval (0 : Fin 1 → ℂ)) := by
    simpa using northCoordinates_hasFDerivAt_zero
  have h := houter.comp (0 : Fin 1 → ℂ) affineEval.hasFDerivAt
  convert h using 1
  · funext w
    exact projectiveHopf_chart_coordinates w

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveNorthChartDerivative
