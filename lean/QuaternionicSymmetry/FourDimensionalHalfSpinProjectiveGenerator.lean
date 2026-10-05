import QuaternionicSymmetry.FourDimensionalHalfSpinMatrixConnection
import QuaternionicSymmetry.FourDimensionalHalfSpinProjective
import QuaternionicSymmetry.ComplexProjectiveAffineTopology

/-! The infinitesimal action of a genuine complex two-by-two connection
matrix in the standard affine chart of CP¹. This polynomial comes from the
Fréchet derivative of the actual homogeneous-coordinate ratio; it is not a
transported sphere vector field. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGenerator

open scoped Matrix
open FourDimensionalHalfSpinProjective
  ComplexProjectiveTopology

noncomputable section

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

def affineGenerator (A : Mat2) (z : ℂ) : ℂ :=
  A 1 0 + (A 1 1 - A 0 0) * z - A 0 1 * z ^ 2

def affineLinearFlow (A : Mat2) (z t : ℂ) : ℂ :=
  let v : Fin 2 → ℂ := ![1, z]
  (v 1 + t * (A *ᵥ v) 1) / (v 0 + t * (A *ᵥ v) 0)

def perturbedSpinor (A : Mat2) (z t : ℂ) : Fin 2 → ℂ :=
  ![1, z] + t • (A *ᵥ ![1, z])

/-- The rational flow is literally the existing CP¹ affine coordinate of
the projectivized matrix deformation, wherever its denominator is nonzero. -/
theorem affineLinearFlow_eq_projectiveRatio (A : Mat2) (z t : ℂ)
    (hden : perturbedSpinor A z t 0 ≠ 0) :
    affineRatio 1 0
      ⟨Projectivization.mk ℂ (perturbedSpinor A z t)
          (by
            intro h
            have h0 := congrFun h 0
            exact hden (by simpa using h0)),
        (mem_affineDomain_mk 1 0 (perturbedSpinor A z t)
          (by
            intro h
            have h0 := congrFun h 0
            exact hden (by simpa using h0))).2 hden⟩ 1 =
      affineLinearFlow A z t := by
  rw [affineRatio_mk 1 0 1 _ _ hden]
  simp [affineLinearFlow, perturbedSpinor]

/-- The chart-coordinate vector field is the derivative of the true
homogeneous-coordinate matrix action at the identity. -/
theorem affineLinearFlow_hasDerivAt (A : Mat2) (z : ℂ) :
    HasDerivAt (affineLinearFlow A z) (affineGenerator A z) 0 := by
  let v : Fin 2 → ℂ := ![1, z]
  have hn : HasDerivAt (fun t : ℂ => v 1 + t * (A *ᵥ v) 1)
      ((A *ᵥ v) 1) 0 := by
    convert (hasDerivAt_const 0 (v 1)).add
      ((hasDerivAt_id (0 : ℂ)).mul_const ((A *ᵥ v) 1)) using 1 <;> simp
  have hd : HasDerivAt (fun t : ℂ => v 0 + t * (A *ᵥ v) 0)
      ((A *ᵥ v) 0) 0 := by
    convert (hasDerivAt_const 0 (v 0)).add
      ((hasDerivAt_id (0 : ℂ)).mul_const ((A *ᵥ v) 0)) using 1 <;> simp
  have hquot := hn.div hd (by simp [v])
  convert hquot using 1
  · simp [affineGenerator, v, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGenerator
