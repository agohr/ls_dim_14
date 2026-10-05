import QuaternionicSymmetry.SelectedTorusCompactExponentialLift
import QuaternionicSymmetry.ComplexTorusRealChartDerivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The real derivative of the literal compact coordinate exponential at
zero is the injective map `a ↦ (i*a_i)_i` in the existing open chart. -/

namespace QuaternionicSymmetry.SelectedTorusCompactExponentialDerivative

open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open SelectedTorusCompactExponentialSmooth
open scoped Manifold ContDiff
noncomputable section

def imaginaryCoordinateMap (r : ℕ) :
    (Fin r → ℝ) →L[ℝ] (Fin r → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (Complex.I • Complex.ofRealCLM).comp
      (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ)

theorem imaginaryCoordinateMap_apply (r : ℕ) (a : Fin r → ℝ) (i : Fin r) :
    imaginaryCoordinateMap r a i = Complex.I * (a i : ℂ) := by
  simp [imaginaryCoordinateMap, mul_comm]

theorem imaginaryCoordinateMap_injective (r : ℕ) :
    Function.Injective (imaginaryCoordinateMap r) := by
  intro a b hab
  funext i
  have hi := congrFun hab i
  rw [imaginaryCoordinateMap_apply, imaginaryCoordinateMap_apply] at hi
  have h := (mul_left_cancel₀ Complex.I_ne_zero hi)
  exact_mod_cast h

theorem compactExp_ambient_hasFDerivAt_zero (r : ℕ) :
    HasFDerivAt (fun a : Fin r → ℝ =>
      torusVal r (compactInclusion r (circleExpPi r a)))
      (imaginaryCoordinateMap r) 0 := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hArg : HasFDerivAt
      (fun a : Fin r → ℝ => Complex.I * (a i : ℂ))
      ((Complex.I • Complex.ofRealCLM).comp
        (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ)) 0 := by
    exact ((Complex.I • Complex.ofRealCLM).comp
      (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ)).hasFDerivAt
  have hExp := hArg.cexp
  convert hExp using 1
  · funext a
    simp [torusVal, compactInclusion, circleExpPi,
      Circle.coe_exp, mul_comm]
  · simp [imaginaryCoordinateMap]

end
end QuaternionicSymmetry.SelectedTorusCompactExponentialDerivative
