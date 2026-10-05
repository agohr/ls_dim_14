import QuaternionicSymmetry.ComplexProjectiveDiagonalIdealAutomorphism

/-! The diagonal substitutions are honest ring automorphisms of the
homogeneous coordinate polynomial ring. Ideal preservation is in the
preceding leaf; this does not identify an analytic image with a scheme. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalGradedRingAction

open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalVanishingIdeal
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

theorem diagonalSubstitution_comp_inv
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    (diagonalSubstitution μ z).comp (diagonalSubstitution μ z⁻¹) =
      RingHom.id (MvPolynomial (Fin (d + 1)) ℂ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [diagonalSubstitution]
  · intro i
    simp [diagonalSubstitution, ← mul_assoc]
    simp [← map_mul]

theorem diagonalSubstitution_inv_comp
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    (diagonalSubstitution μ z⁻¹).comp (diagonalSubstitution μ z) =
      RingHom.id (MvPolynomial (Fin (d + 1)) ℂ) := by
  convert diagonalSubstitution_comp_inv μ z⁻¹ using 1 <;> simp

def diagonalRingEquiv
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    MvPolynomial (Fin (d + 1)) ℂ ≃+*
      MvPolynomial (Fin (d + 1)) ℂ :=
  RingEquiv.ofHomInv (diagonalSubstitution μ z)
    (diagonalSubstitution μ z⁻¹)
    (diagonalSubstitution_comp_inv μ z)
    (diagonalSubstitution_inv_comp μ z)

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalGradedRingAction
