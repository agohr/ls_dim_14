import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGaugeAlgebra

/-! The homogeneous gauge identity in a genuine CP¹ affine coordinate:
the determinant is the Möbius derivative, and the varying-frame term is
the projectivized derivative of the frame matrix. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGaugeChart

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeAlgebra

noncomputable section

def chartDen (G : Mat2) (z : ℂ) : ℂ := G 0 0 + G 0 1 * z
def chartNum (G : Mat2) (z : ℂ) : ℂ := G 1 0 + G 1 1 * z
def mobius (G : Mat2) (z : ℂ) : ℂ := chartNum G z / chartDen G z

theorem projectiveCross_affine (A : Mat2) (v : Spinor) (hv : v 0 ≠ 0) :
    (v 0) ^ 2 * affineGenerator A (v 1 / v 0) =
      projectiveCross (A *ᵥ v) v := by
  simp [affineGenerator, projectiveCross, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  field_simp
  ring

theorem chartDen_eq (G : Mat2) (z : ℂ) :
    (G *ᵥ ![1, z]) 0 = chartDen G z := by
  simp [chartDen, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem chartNum_eq (G : Mat2) (z : ℂ) :
    (G *ᵥ ![1, z]) 1 = chartNum G z := by
  simp [chartNum, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem projectiveCross_affineUnit (B : Mat2) (z : ℂ) :
    projectiveCross (B *ᵥ ![1, z]) ![1, z] =
      affineGenerator B z := by
  simp [projectiveCross, affineGenerator, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- The exact affine numerator gauge law, with the actual variable-frame
term retained.  This is the chain-rule identity before division by the
nonzero chart denominator. -/
theorem affine_gauge_numerator (G A B C : Mat2) (z : ℂ)
    (hG : G * B = A * G + C) (hden : chartDen G z ≠ 0) :
    Matrix.det G * affineGenerator B z =
      (chartDen G z) ^ 2 * affineGenerator A (mobius G z) +
        projectiveCross (C *ᵥ ![1, z]) (G *ᵥ ![1, z]) := by
  have h := projectiveCross_gauge G A B C ![1, z] hG
  rw [projectiveCross_affineUnit] at h
  have hw0 : (G *ᵥ ![1, z]) 0 ≠ 0 := by
    rwa [chartDen_eq]
  rw [← projectiveCross_affine A (G *ᵥ ![1, z]) hw0] at h
  simpa only [chartDen_eq, chartNum_eq, mobius] using h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGaugeChart
