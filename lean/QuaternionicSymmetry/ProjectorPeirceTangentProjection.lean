import Mathlib.Tactic

/-! Algebraic Peirce projection for the tangent equation of a genuine
idempotent matrix orbit. This is the ambient candidate for differentiating
the projector immersion; no curvature identification is assumed. -/

namespace QuaternionicSymmetry.ProjectorPeirceTangentProjection

noncomputable section

variable {A : Type*} [Ring A]

def tangentPart (P X : A) : A := P * X + X * P - 2 • (P * X * P)

theorem tangentPart_tangent (P X : A) (hP : P * P = P) :
    P * tangentPart P X + tangentPart P X * P = tangentPart P X := by
  simp only [tangentPart, two_nsmul, mul_add, add_mul, mul_sub, sub_mul,
    ← mul_assoc]
  rw [mul_assoc X P P, hP, mul_assoc (P * X) P P, hP]
  abel

theorem tangentPart_eq_self_of_tangent (P X : A)
    (hP : P * P = P) (hX : P * X + X * P = X) : tangentPart P X = X := by
  have hPX : P * X * P = 0 := by
    have h := congrArg (fun Y : A => P * Y * P) hX
    have hh : P * X * P + P * X * P = P * X * P := by
      simp only [mul_add, add_mul] at h
      rw [← mul_assoc P P X, hP,
        mul_assoc P (X * P) P, mul_assoc X P P, hP] at h
      simpa only [← mul_assoc P X P] using h
    have hh' : P * X * P + P * X * P = P * X * P + 0 := by
      simpa using hh
    exact add_left_cancel hh'
  simp [tangentPart, hX, hPX]

theorem tangentPart_idempotent (P X : A) (hP : P * P = P) :
    tangentPart P (tangentPart P X) = tangentPart P X :=
  tangentPart_eq_self_of_tangent P (tangentPart P X) hP
    (tangentPart_tangent P X hP)

end
end QuaternionicSymmetry.ProjectorPeirceTangentProjection
