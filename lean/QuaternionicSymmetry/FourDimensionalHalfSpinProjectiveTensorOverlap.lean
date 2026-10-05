import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveChiralityOverlap

/-! Exact algebraic gluing criterion for the independent projective
almost-complex tensor.  The hypotheses are the three geometric overlap
checks: base chirality, horizontal connection, and vertical holomorphicity.
The subsequent actual atlas specialization must prove each from its
constructed transition, not assume them as an AHS conclusion. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveTensorOverlap

open scoped Quaternion
open FourDimensionalHalfSpinProjectiveLocalAHS

noncomputable section

def tangentTransition (T : ℍ →ₗ[ℝ] ℍ) (F : ℍ →ₗ[ℝ] ℂ)
    (H : ℂ →ₗ[ℝ] ℂ) : (ℍ × ℂ) →ₗ[ℝ] (ℍ × ℂ) where
  toFun v := (T v.1, F v.1 + H v.2)
  map_add' v w := by
    apply Prod.ext
    · simp [map_add]
    · simp [map_add]
      abel
  map_smul' c v := by
    apply Prod.ext
    · simp [map_smul]
    · change F (c • v.1) + H (c • v.2) =
        c • (F v.1 + H v.2)
      rw [map_smul, map_smul, smul_add]

theorem graphComplex_overlap
    (Jp Jq T : ℍ →ₗ[ℝ] ℍ) (Kp Kq F : ℍ →ₗ[ℝ] ℂ)
    (H : ℂ →ₗ[ℝ] ℂ)
    (hbase : ∀ u, T (Jp u) = Jq (T u))
    (hvert : ∀ w, H (Complex.I * w) = Complex.I * H w)
    (hhoriz : ∀ u, F u + H (-(Kp u)) = -(Kq (T u)))
    (v : ℍ × ℂ) :
    tangentTransition T F H (graphComplex Jp Kp v) =
      graphComplex Jq Kq (tangentTransition T F H v) := by
  apply Prod.ext
  · exact hbase v.1
  · change F (Jp v.1) +
        H (Complex.I * (v.2 + Kp v.1) - Kp (Jp v.1)) =
      Complex.I * (F v.1 + H v.2 + Kq (T v.1)) -
        Kq (Jq (T v.1))
    have hp := hhoriz (Jp v.1)
    have h := hhoriz v.1
    rw [map_sub, hvert, map_add, map_neg] at *
    rw [hbase] at hp
    linear_combination hp - Complex.I * h

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveTensorOverlap
