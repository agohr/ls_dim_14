import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGeneratorSmooth

/-! Homogeneous-coordinate determinant identities underlying the CP¹
connection gauge law.  Everything is for literal complex matrices and
spinors; no sphere transport or global spin trivialization is used. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGaugeAlgebra

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator

noncomputable section

abbrev Spinor := Fin 2 → ℂ

def projectiveCross (u v : Spinor) : ℂ := u 1 * v 0 - u 0 * v 1

theorem projectiveCross_add_left (u v w : Spinor) :
    projectiveCross (u + v) w =
      projectiveCross u w + projectiveCross v w := by
  simp [projectiveCross, Pi.add_apply]
  ring

theorem projectiveCross_matrix (G : Mat2) (u v : Spinor) :
    projectiveCross (G *ᵥ u) (G *ᵥ v) =
      Matrix.det G * projectiveCross u v := by
  simp [projectiveCross, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Matrix.det_fin_two]
  ring

/-- If `G B = A G + C`, the infinitesimal projective action obeys the
precise numerator identity for a varying change of spinor frame. -/
theorem projectiveCross_gauge (G A B C : Mat2) (v : Spinor)
    (hG : G * B = A * G + C) :
    Matrix.det G * projectiveCross (B *ᵥ v) v =
      projectiveCross (A *ᵥ (G *ᵥ v)) (G *ᵥ v) +
        projectiveCross (C *ᵥ v) (G *ᵥ v) := by
  rw [← projectiveCross_matrix G (B *ᵥ v) v]
  have hvec : G *ᵥ (B *ᵥ v) =
      A *ᵥ (G *ᵥ v) + C *ᵥ v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hG, Matrix.add_mulVec]
  rw [hvec, projectiveCross_add_left]

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGaugeAlgebra
