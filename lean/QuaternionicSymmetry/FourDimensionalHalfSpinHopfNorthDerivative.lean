import QuaternionicSymmetry.FourDimensionalHalfSpinHopfChartFormula
import Mathlib.LinearAlgebra.CrossProduct

/-! The real differential of the literal north affine Hopf coordinate map.
The sign is recorded before comparing with either vertical complex convention. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthDerivative

open FourDimensionalHalfSpinHopfChartFormula

noncomputable section

private theorem normSq_hasFDerivAt_zero :
    HasFDerivAt (fun z : ℂ => Complex.normSq z) (0 : ℂ →L[ℝ] ℝ) 0 := by
  have hre : HasFDerivAt (fun z : ℂ => z.re) Complex.reCLM 0 :=
    Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ => z.im) Complex.imCLM 0 :=
    Complex.imCLM.hasFDerivAt
  have h := (hre.mul hre).add (him.mul him)
  simpa [Complex.normSq_apply, pow_two] using h

def northCoordinates (z : ℂ) : Fin 3 → ℝ :=
  ![(1 + Complex.normSq z)⁻¹ * (1 - Complex.normSq z),
    (1 + Complex.normSq z)⁻¹ * (-2 * z.im),
    (1 + Complex.normSq z)⁻¹ * (-2 * z.re)]

def northDifferential : ℂ →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![(0 : ℂ →L[ℝ] ℝ),
    (-2 : ℝ) • Complex.imCLM, (-2 : ℝ) • Complex.reCLM]

private theorem reciprocal_hasFDerivAt_zero :
    HasFDerivAt (fun z : ℂ => (1 + Complex.normSq z)⁻¹)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
  have hden : HasFDerivAt (fun z : ℂ => 1 + Complex.normSq z)
      (0 : ℂ →L[ℝ] ℝ) 0 := by
    have h := (hasFDerivAt_const (1 : ℝ) (0 : ℂ)).add
      normSq_hasFDerivAt_zero
    convert h using 1
    simp
  have hinv : HasFDerivAt (fun x : ℝ => x⁻¹)
      (ContinuousLinearMap.toSpanSingleton ℝ (-(1 : ℝ)))
      (1 + Complex.normSq (0 : ℂ)) := by
    simpa using (hasFDerivAt_inv (by norm_num : (1 : ℝ) ≠ 0))
  have h := hinv.comp 0 hden
  simpa using h

theorem northCoordinates_hasFDerivAt_zero :
    HasFDerivAt northCoordinates northDifferential 0 := by
  have ht := normSq_hasFDerivAt_zero
  have hr := reciprocal_hasFDerivAt_zero
  change HasFDerivAt (fun z i => northCoordinates z i)
    (ContinuousLinearMap.pi ![(0 : ℂ →L[ℝ] ℝ),
      (-2 : ℝ) • Complex.imCLM, (-2 : ℝ) • Complex.reCLM]) 0
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · have hn : HasFDerivAt (fun z : ℂ => 1 - Complex.normSq z)
        (0 : ℂ →L[ℝ] ℝ) 0 := by
      simpa using (hasFDerivAt_const (1 : ℝ) (0 : ℂ)).sub ht
    have h := hr.mul hn
    simpa [northCoordinates, northDifferential] using h
  · have him : HasFDerivAt (fun z : ℂ => -2 * z.im)
        ((-2 : ℝ) • Complex.imCLM) 0 := by
      simpa using Complex.imCLM.hasFDerivAt.const_mul (-2 : ℝ)
    have h := hr.mul him
    convert h using 1
    simp
  · have hre : HasFDerivAt (fun z : ℂ => -2 * z.re)
        ((-2 : ℝ) • Complex.reCLM) 0 := by
      simpa using Complex.reCLM.hasFDerivAt.const_mul (-2 : ℝ)
    have h := hr.mul hre
    convert h using 1
    simp

theorem northCoordinates_eq_actualHopf (z : ℂ) :
    northCoordinates z =
      (FourDimensionalHalfSpinHopfSphere.hopfSphere
        (affineZeroSpinor z) (affineZero_nonzero z)).1 :=
  (affineZero_hopfCoefficients z).symm

theorem actualHopfNorth_hasFDerivAt_zero :
    HasFDerivAt
      (fun z : ℂ =>
        (FourDimensionalHalfSpinHopfSphere.hopfSphere
          (affineZeroSpinor z) (affineZero_nonzero z)).1)
      northDifferential 0 := by
  convert northCoordinates_hasFDerivAt_zero using 1
  funext z
  exact (northCoordinates_eq_actualHopf z).symm

/-- The checked north affine Hopf derivative reverses the standard complex
rotation and the sphere's quaternionic cross-product rotation at `i`. -/
theorem northDifferential_anti_complex (w : ℂ) :
    northDifferential (Complex.I * w) =
      -crossProduct (Pi.basisFun ℝ (Fin 3) 0) (northDifferential w) := by
  ext i
  fin_cases i <;>
    simp [northDifferential, crossProduct, Pi.basisFun_apply,
      Complex.mul_re, Complex.mul_im]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinHopfNorthDerivative
