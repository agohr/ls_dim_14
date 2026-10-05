import QuaternionicSymmetry.QuaternionicLine
import QuaternionicSymmetry.QuaternionicStructure

open scoped Quaternion
open Quaternion

namespace QuaternionicSymmetry
namespace QuaternionicLine

noncomputable section

open QuaternionicSymmetry

/-- The abstract quaternionic structure on the concrete real quaternion line,
with the actions given by right multiplication by `i` and `j`. -/
def structureOnLine : QuaternionicStructure ℍ where
  I := rightI
  J := rightJ
  I_sq := rightI_sq_apply
  J_sq := rightJ_sq_apply
  I_J_anti := rightI_rightJ_apply

/-- For these right actions the canonical third complex structure is minus
right multiplication by `k`; the frame at `1` is therefore `(1,i,j,-k)`. -/
theorem structureOnLine_K_apply (x : ℍ) : structureOnLine.K x = -rightK x := by
  change (x * unitJ) * unitI = -(x * unitK)
  rw [mul_assoc, unitJ_mul_unitI, mul_neg]

/-- Every imaginary left multiplication is skew-adjoint and commutes with the
chosen quaternionic right actions. -/
theorem leftAction_mem_structureOnLine_skewCentralizer (a b c : ℝ) :
    leftAction a b c ∈ structureOnLine.skewCentralizer := by
  rw [QuaternionicStructure.mem_skewCentralizer_iff]
  exact ⟨leftAction_skew_adjoint a b c,
    leftAction_commutes_rightI a b c, leftAction_commutes_rightJ a b c⟩


noncomputable section
open QuaternionicSymmetry

private theorem quaternion_coordinate_decomposition (x : ℍ) :
    x = (x.re : ℍ) + x.imI • unitI + x.imJ • unitJ + x.imK • unitK := by
  ext <;> simp [unitI, unitJ, unitK]

/-- A real-linear map commuting with the two right quaternionic generators is
left multiplication by its value at `1`. -/
theorem eq_leftMul_of_commutes (A : ℍ →ₗ[ℝ] ℍ)
    (hI : ∀ x : ℍ, A (rightI x) = rightI (A x))
    (hJ : ∀ x : ℍ, A (rightJ x) = rightJ (A x)) :
    A = LinearMap.mulLeft ℝ (A 1) := by
  have hAi : A unitI = A 1 * unitI := by
    simpa [rightI_apply] using hI 1
  have hAj : A unitJ = A 1 * unitJ := by
    simpa [rightJ_apply] using hJ 1
  have hAk : A unitK = A 1 * unitK := by
    have h := hI (rightJ 1)
    simp only [rightI_apply, rightJ_apply, one_mul, unitJ_mul_unitI,
      map_neg] at h
    rw [hAj] at h
    rw [mul_assoc, unitJ_mul_unitI, mul_neg] at h
    exact neg_inj.mp h
  apply LinearMap.ext
  intro x
  rw [quaternion_coordinate_decomposition x]
  have hreal : A (x.re : ℍ) = A 1 * (x.re : ℍ) := by
    calc
      A (x.re : ℍ) = A (x.re • (1 : ℍ)) := by simp [Algebra.smul_def]
      _ = x.re • A 1 := by rw [map_smul]
      _ = A 1 * (x.re : ℍ) := by
        rw [Algebra.smul_def]
        exact Algebra.commutes x.re (A 1)
  simp only [map_add, map_smul, LinearMap.mulLeft_apply, hAi, hAj, hAk, hreal]

end

/-- Conversely, the skew-adjoint part of the centralizer is exactly the
three-dimensional imaginary left-multiplication span. -/
theorem eq_leftAction_of_mem (A : ℍ →ₗ[ℝ] ℍ)
    (hA : A ∈ structureOnLine.skewCentralizer) :
    A = leftAction (A 1).imI (A 1).imJ (A 1).imK := by
  have h := (QuaternionicStructure.mem_skewCentralizer_iff structureOnLine A).mp hA
  have hre : (A 1).re = 0 := by
    have hs := h.1 1 1
    have hs' : (A 1).re = -(A 1).re := by
      simpa [Quaternion.inner_def] using hs
    linarith
  have hleft := eq_leftMul_of_commutes A h.2.1 h.2.2
  have himag : imaginary (A 1).imI (A 1).imJ (A 1).imK = A 1 := by
    ext <;> simp [imaginary, unitI, unitJ, unitK, hre]
  calc
    A = LinearMap.mulLeft ℝ (A 1) := hleft
    _ = LinearMap.mulLeft ℝ (imaginary (A 1).imI (A 1).imJ (A 1).imK) := by
      rw [himag]
    _ = leftAction (A 1).imI (A 1).imJ (A 1).imK := rfl

end
end QuaternionicLine
end QuaternionicSymmetry
