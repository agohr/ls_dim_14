import QuaternionicSymmetry.ProjectorPeirceCurvatureBracket

/-! Nonvanishing of a matrix commutator is preserved by actual invertible
conjugation. This is the algebraic transport needed from the explicit base
quotient tangent pair to every point of its transitive orbit. -/

namespace QuaternionicSymmetry.ProjectorCommutatorConjugation

open ProjectorPeirceCurvatureBracket

variable {A : Type*} [Ring A]

theorem commutator_conjugate (U V X Y : A)
    (hVU : V * U = 1) :
    ProjectorPeirceCurvatureBracket.commutator (U * X * V) (U * Y * V) =
      U * ProjectorPeirceCurvatureBracket.commutator X Y * V := by
  simp only [ProjectorPeirceCurvatureBracket.commutator, mul_sub, sub_mul]
  simp only [mul_assoc]
  rw [← mul_assoc V U (Y * V), hVU, one_mul,
    ← mul_assoc V U (X * V), hVU, one_mul]

theorem commutator_conjugate_ne_zero (U V X Y : A)
    (hVU : V * U = 1) (hUV : U * V = 1)
    (h : ProjectorPeirceCurvatureBracket.commutator X Y ≠ 0) :
    ProjectorPeirceCurvatureBracket.commutator (U * X * V) (U * Y * V) ≠ 0 := by
  rw [commutator_conjugate U V X Y hVU]
  intro hz
  have hh := congrArg (fun Z : A => V * Z * U) hz
  have hK : V * (U * ProjectorPeirceCurvatureBracket.commutator X Y * V) * U =
      ProjectorPeirceCurvatureBracket.commutator X Y := by
    calc
      _ = (V * U) * ProjectorPeirceCurvatureBracket.commutator X Y * (V * U) := by
        simp only [mul_assoc]
      _ = _ := by rw [hVU]; simp
  have hh' : V * (U * ProjectorPeirceCurvatureBracket.commutator X Y * V) * U = 0 := by
    simpa only [mul_zero, zero_mul] using hh
  rw [hK] at hh'
  exact h hh'

end QuaternionicSymmetry.ProjectorCommutatorConjugation
