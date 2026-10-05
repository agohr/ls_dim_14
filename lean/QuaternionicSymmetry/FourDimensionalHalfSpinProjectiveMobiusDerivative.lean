import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveGaugeChart

/-! Exact one-complex-variable derivatives of the Möbius coordinate action
and its varying-frame term. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusDerivative

open scoped Matrix
open FourDimensionalHalfSpinProjectiveGenerator
  FourDimensionalHalfSpinProjectiveGaugeAlgebra
  FourDimensionalHalfSpinProjectiveGaugeChart

noncomputable section

def varyingMobius (G C : Mat2) (z t : ℂ) : ℂ :=
  (chartNum G z + t * chartNum C z) /
    (chartDen G z + t * chartDen C z)

theorem mobius_hasDerivAt (G : Mat2) (z : ℂ)
    (hden : chartDen G z ≠ 0) :
    HasDerivAt (mobius G) (Matrix.det G / (chartDen G z) ^ 2) z := by
  have hn : HasDerivAt (chartNum G) (G 1 1) z := by
    convert (hasDerivAt_const z (G 1 0)).add
      ((hasDerivAt_id z).mul_const (G 1 1)) using 1 <;>
      simp [chartNum, mul_comm]
    funext w
    simp [chartNum, mul_comm]
  have hd : HasDerivAt (chartDen G) (G 0 1) z := by
    convert (hasDerivAt_const z (G 0 0)).add
      ((hasDerivAt_id z).mul_const (G 0 1)) using 1 <;>
      simp [chartDen, mul_comm]
    funext w
    simp [chartDen, mul_comm]
  have hquot := hn.div hd hden
  convert hquot using 1
  · simp [Matrix.det_fin_two, chartDen, chartNum]
    ring

theorem varyingMobius_hasDerivAt (G C : Mat2) (z : ℂ)
    (hden : chartDen G z ≠ 0) :
    HasDerivAt (varyingMobius G C z)
      (projectiveCross (C *ᵥ ![1, z]) (G *ᵥ ![1, z]) /
        (chartDen G z) ^ 2) 0 := by
  have hn : HasDerivAt
      (fun t : ℂ => chartNum G z + t * chartNum C z)
      (chartNum C z) 0 := by
    convert (hasDerivAt_const 0 (chartNum G z)).add
      ((hasDerivAt_id (0 : ℂ)).mul_const (chartNum C z)) using 1 <;> simp
  have hd : HasDerivAt
      (fun t : ℂ => chartDen G z + t * chartDen C z)
      (chartDen C z) 0 := by
    convert (hasDerivAt_const 0 (chartDen G z)).add
      ((hasDerivAt_id (0 : ℂ)).mul_const (chartDen C z)) using 1 <;> simp
  have hquot := hn.div hd (by simpa using hden)
  convert hquot using 1
  · simp [projectiveCross, chartDen, chartNum, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring

/-- Möbius chain rule for the projective connection gauge law.  The
last derivative is the change of projective coordinate caused by the
moving local spin frame. -/
theorem affine_gauge_chain (G A B C : Mat2) (z : ℂ)
    (hG : G * B = A * G + C) (hden : chartDen G z ≠ 0) :
    deriv (mobius G) z * affineGenerator B z =
      affineGenerator A (mobius G z) +
        deriv (varyingMobius G C z) 0 := by
  rw [(mobius_hasDerivAt G z hden).deriv,
    (varyingMobius_hasDerivAt G C z hden).deriv]
  have h := affine_gauge_numerator G A B C z hG hden
  calc
    Matrix.det G / (chartDen G z) ^ 2 * affineGenerator B z =
        (Matrix.det G * affineGenerator B z) / (chartDen G z) ^ 2 := by ring
    _ = ((chartDen G z) ^ 2 * affineGenerator A (mobius G z) +
          projectiveCross (C *ᵥ ![1, z]) (G *ᵥ ![1, z])) /
          (chartDen G z) ^ 2 := by rw [h]
    _ = affineGenerator A (mobius G z) +
        projectiveCross (C *ᵥ ![1, z]) (G *ᵥ ![1, z]) /
          (chartDen G z) ^ 2 := by
      field_simp

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveMobiusDerivative
