import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveAffineCoefficientSmooth

/-! Smooth ambient antipodal-Hopf coefficients in the two scalar affine
coordinates actually used by the independent projective local tensors. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartCoefficientSmooth

open scoped ContDiff
open FourDimensionalHalfSpinProjectiveAffineCoefficientSmooth
  FourDimensionalHalfSpinHopfSphere
  FourDimensionalHalfSpinAntipodalVerticalSign
  ComplexProjectiveTopology
  ManifoldTwistorSphereBundle

noncomputable section

def chartAntipodalVector (i : Fin 2) (z : ℂ) : Fin 3 → ℝ :=
  affineAntipodalVector i ![z]

theorem chartAntipodalVector_smooth (i : Fin 2) :
    ContDiff ℝ ∞ (chartAntipodalVector i) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ => (![z] : Fin 1 → ℂ)) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    simpa using (contDiff_id : ContDiff ℝ ∞ (id : ℂ → ℂ))
  exact (affineAntipodalVector_smooth i).comp h

theorem chartAntipodalVector_zero (z : ℂ) :
    chartAntipodalVector 0 z =
      (antipodalCoefficient (hopfSphere ![1,z] (by simp))).1 := by
  rw [chartAntipodalVector, affineAntipodalVector_eq_hopf]
  congr 1

theorem chartAntipodalVector_one (z : ℂ) :
    chartAntipodalVector 1 z =
      (antipodalCoefficient (hopfSphere ![z,1] (by simp))).1 := by
  rw [chartAntipodalVector, affineAntipodalVector_eq_hopf]
  congr 1

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChartCoefficientSmooth
