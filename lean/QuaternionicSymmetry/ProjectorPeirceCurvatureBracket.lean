import QuaternionicSymmetry.ProjectorPeirceTangentProjection

/-! Algebraic identification of the curvature obtained from the Peirce
projection derivative with the double commutator on genuine tangent blocks. -/

namespace QuaternionicSymmetry.ProjectorPeirceCurvatureBracket

open ProjectorPeirceTangentProjection

variable {A : Type*} [Ring A]

def tangentPartDerivative (P X Z : A) : A :=
  X * Z + Z * X - 2 • (X * Z * P + P * Z * X)

def commutator (X Y : A) : A := X * Y - Y * X

theorem derivative_commutator_eq_double_commutator
    (P X Y Z : A) (hP : P * P = P)
    (hX : P * X + X * P = X)
    (hY : P * Y + Y * P = Y)
    (hZ : P * Z + Z * P = Z) :
    tangentPartDerivative P X (tangentPartDerivative P Y Z) -
      tangentPartDerivative P Y (tangentPartDerivative P X Z) =
        commutator (commutator X Y) Z := by
  have hPX : P * X = X - X * P := by exact (eq_sub_iff_add_eq).2 hX
  have hPY : P * Y = Y - Y * P := by exact (eq_sub_iff_add_eq).2 hY
  have hPZ : P * Z = Z - Z * P := by exact (eq_sub_iff_add_eq).2 hZ
  have hPX' (T : A) : P * (X * T) = (X - X * P) * T := by
    rw [← mul_assoc, hPX]
  have hPY' (T : A) : P * (Y * T) = (Y - Y * P) * T := by
    rw [← mul_assoc, hPY]
  have hPZ' (T : A) : P * (Z * T) = (Z - Z * P) * T := by
    rw [← mul_assoc, hPZ]
  simp only [tangentPartDerivative, commutator, two_nsmul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc]
  simp only [hPX', hPY', hPZ', hPX, hPY, hP,
    mul_sub, sub_mul, mul_assoc]
  noncomm_ring

end QuaternionicSymmetry.ProjectorPeirceCurvatureBracket
