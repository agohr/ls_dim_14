import QuaternionicSymmetry.ComplexProjectiveDiagonalCoordinateQuotient

/-! Actual identity/multiplication laws and ℂ-algebra structure of the
coordinate-polynomial pullback. The torus is commutative, so contravariant
pullback composition has the same written multiplication order. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalCoordinateActionCoherence

open ComplexProjectiveDiagonalAction ComplexProjectiveDiagonalVanishingIdeal
open TorusLaurentRepresentation
noncomputable section

variable {r d : ℕ}

def diagonalAlgHom
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    MvPolynomial (Fin (d + 1)) ℂ →ₐ[ℂ]
      MvPolynomial (Fin (d + 1)) ℂ :=
  MvPolynomial.aeval (fun i =>
    MvPolynomial.C (complexWeightCharacter (μ i) z : ℂ) * MvPolynomial.X i)

theorem diagonalAlgHom_toRingHom
    (μ : Fin (d + 1) → Fin r → ℤ) (z : ComplexTorus r) :
    (diagonalAlgHom μ z).toRingHom = diagonalSubstitution μ z := rfl

theorem diagonalSubstitution_one
    (μ : Fin (d + 1) → Fin r → ℤ) :
    diagonalSubstitution μ 1 =
      RingHom.id (MvPolynomial (Fin (d + 1)) ℂ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [diagonalSubstitution]
  · intro i
    simp [diagonalSubstitution]

theorem diagonalSubstitution_mul
    (μ : Fin (d + 1) → Fin r → ℤ) (z w : ComplexTorus r) :
    diagonalSubstitution μ (z * w) =
      (diagonalSubstitution μ z).comp (diagonalSubstitution μ w) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [diagonalSubstitution]
  · intro i
    simp [diagonalSubstitution, mul_assoc, mul_left_comm, mul_comm]

def diagonalPolynomialAction
    (μ : Fin (d + 1) → Fin r → ℤ) :
    ComplexTorus r →* (MvPolynomial (Fin (d + 1)) ℂ →+*
      MvPolynomial (Fin (d + 1)) ℂ) where
  toFun := diagonalSubstitution μ
  map_one' := diagonalSubstitution_one μ
  map_mul' := diagonalSubstitution_mul μ

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalCoordinateActionCoherence
