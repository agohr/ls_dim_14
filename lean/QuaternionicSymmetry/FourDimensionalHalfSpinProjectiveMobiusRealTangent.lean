import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusAction
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! The real tangent derivative of each holomorphic Möbius chart action
is the complex-linear multiplication used in the projective connection
overlap law. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusRealTangent

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeChart
  FourDimensionalHalfSpinProjectiveMobiusDerivative

noncomputable section

theorem mobius_real_fderiv (G : Mat2) (z w : ℂ)
    (hden : chartDen G z ≠ 0) :
    fderiv ℝ (mobius G) z w = deriv (mobius G) z * w := by
  have hc := mobius_hasDerivAt G z hden
  have hreal := hc.hasFDerivAt.restrictScalars ℝ
  have h := congrArg (fun T : ℂ →L[ℝ] ℂ => T w) hreal.fderiv
  convert h using 1
  · simp [hc.deriv]
    ring

theorem mobius_real_fderiv_complex (G : Mat2) (z w : ℂ)
    (hden : chartDen G z ≠ 0) :
    fderiv ℝ (mobius G) z (Complex.I * w) =
      Complex.I * fderiv ℝ (mobius G) z w := by
  rw [mobius_real_fderiv G z (Complex.I * w) hden,
    mobius_real_fderiv G z w hden]
  ring

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusRealTangent
