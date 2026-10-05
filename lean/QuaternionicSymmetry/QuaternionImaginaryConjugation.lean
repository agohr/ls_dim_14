import Mathlib.Analysis.Quaternion

/-! A source-free algebraic fact needed to descend the concrete
three-dimensional imaginary quaternion plane through Sp(1) isotropy. -/

namespace QuaternionicSymmetry.QuaternionImaginaryConjugation

open scoped Quaternion

theorem re_mul_comm (a b : ℍ) : (a * b).re = (b * a).re := by
  simp only [Quaternion.re_mul]
  ring

/-- Quaternionic inner conjugation preserves the real part. -/
theorem re_conjugation (q r : ℍ) (hq : q ≠ 0) :
    (q * r * q⁻¹).re = r.re := by
  calc
    (q * r * q⁻¹).re = (q⁻¹ * (q * r)).re := re_mul_comm _ _
    _ = ((q⁻¹ * q) * r).re := by rw [mul_assoc]
    _ = r.re := by rw [inv_mul_cancel₀ hq, one_mul]

/-- In particular the pure-imaginary three-plane is preserved by
conjugation by every nonzero quaternion. -/
theorem imaginary_conjugation (q r : ℍ) (hq : q ≠ 0) (hr : r.re = 0) :
    (q * r * q⁻¹).re = 0 := by
  rw [re_conjugation q r hq, hr]

end QuaternionicSymmetry.QuaternionImaginaryConjugation
