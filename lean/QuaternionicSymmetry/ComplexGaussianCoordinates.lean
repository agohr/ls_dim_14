import QuaternionicSymmetry.ComplexGaussianVariable
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Norm

/-! Polynomial coordinates for the concrete complex Gaussian variables. -/

namespace QuaternionicSymmetry.ComplexGaussianCoordinates

open MvPolynomial

noncomputable section

variable {κ : Type*}

def coordinate (j : κ) : MvPolynomial (κ × Fin 2) ℂ :=
  MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
    (MvPolynomial.X (j, 0) + MvPolynomial.C Complex.I * MvPolynomial.X (j, 1))

def conjugateCoordinate (j : κ) : MvPolynomial (κ × Fin 2) ℂ :=
  MvPolynomial.C ((Real.sqrt 2 : ℂ)⁻¹) *
    (MvPolynomial.X (j, 0) - MvPolynomial.C Complex.I * MvPolynomial.X (j, 1))

private def evalReal (ω : κ × Fin 2 → ℝ) : (κ × Fin 2) → ℂ :=
  fun p => algebraMap ℝ ℂ (ω p)

theorem eval_coordinate (ω : κ → Fin 2 → ℝ) (j : κ) :
    MvPolynomial.eval (evalReal (fun p => ω p.1 p.2)) (coordinate j) =
      ComplexGaussianVariable.standardComplex (fun k => ω j k) := by
  simp [coordinate, evalReal, ComplexGaussianVariable.standardComplex]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      div_eq_mul_inv]
    ring
  · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      div_eq_mul_inv]
    ring

theorem eval_conjugateCoordinate (ω : κ → Fin 2 → ℝ) (j : κ) :
    MvPolynomial.eval (evalReal (fun p => ω p.1 p.2)) (conjugateCoordinate j) =
      (starRingEnd ℂ)
        (ComplexGaussianVariable.standardComplex (fun k => ω j k)) := by
  simp [conjugateCoordinate, evalReal, ComplexGaussianVariable.standardComplex]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      div_eq_mul_inv]
    ring
  · simp only [Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      div_eq_mul_inv]
    ring

theorem eval_coordinate_mul_conjugateCoordinate
    (ω : κ → Fin 2 → ℝ) (j : κ) :
    MvPolynomial.eval (evalReal (fun p => ω p.1 p.2))
        (coordinate j * conjugateCoordinate j) =
      ((‖ComplexGaussianVariable.standardComplex (fun k => ω j k)‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_mul, eval_coordinate, eval_conjugateCoordinate,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

end
end QuaternionicSymmetry.ComplexGaussianCoordinates
