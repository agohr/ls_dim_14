import QuaternionicSymmetry.CompactSymplecticQuaternionicProjector
import QuaternionicSymmetry.QuaternionicMatrixModel

/-! Quaternionic compatibility of every actual symplectic projector orbit
point, using the checked unitary-symplectic/anti-linear commutation
equivalence from `QuaternionicMatrixModel`. -/

namespace QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit

open Matrix CompactSymplecticHaar CompactSymplecticProjectiveQuotient
open CompactSymplecticProjectorOrbit
open CompactSymplecticQuaternionicProjector
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- The coordinate projector is real under entrywise complex conjugation. -/
theorem firstPairProjector_map_star (n : ℕ) :
    (firstPairProjector n).map star = firstPairProjector n := by
  classical
  simp [firstPairProjector]

/-- Every point of the actual compact-symplectic projector orbit is an
orthogonal projector onto a quaternionic-invariant complex two-plane.
The equation is the matrix form of commuting with `v ↦ J·conj(v)`. -/
theorem orbitProjector_commutes_quaternionicJ (n : ℕ)
    (u : CompactSymplecticHaar.Group (n + 1)) :
    orbitProjector n u * standardJ (n + 1) =
      standardJ (n + 1) * (orbitProjector n u).map star := by
  let P := firstPairProjector n
  let J := standardJ (n + 1)
  let U : Matrix _ _ ℂ := u.1.1
  let V : Matrix _ _ ℂ := (u⁻¹).1.1
  have hu : U * J = J * U.map star :=
    (QuaternionicMatrixModel.unitary_mem_stabilizer_iff_commutes_J (n + 1) u.1).mp u.2
  have hv : V * J = J * V.map star :=
    (QuaternionicMatrixModel.unitary_mem_stabilizer_iff_commutes_J (n + 1) (u⁻¹).1).mp
      (u⁻¹).2
  have hp : P * J = J * P := firstPairProjector_commutes_standardJ n
  have hpr : P.map star = P := firstPairProjector_map_star n
  have hpr' : P.map (starRingEnd ℂ) = P := hpr
  rw [orbitProjector_eq_mul_inverse]
  change U * P * V * J = J * (U * P * V).map star
  calc
    U * P * V * J = U * P * (V * J) := by simp [mul_assoc]
    _ = U * P * (J * V.map star) := by rw [hv]
    _ = U * (P * J) * V.map star := by simp [mul_assoc]
    _ = U * (J * P) * V.map star := by rw [hp]
    _ = (U * J) * (P * V.map star) := by simp [mul_assoc]
    _ = (J * U.map star) * (P * V.map star) := by rw [hu]
    _ = J * (U.map star * P * V.map star) := by simp [mul_assoc]
    _ = J * (U * P * V).map star := by
      change J * (U.map (starRingEnd ℂ) * P * V.map (starRingEnd ℂ)) =
        J * (U * P * V).map (starRingEnd ℂ)
      rw [Matrix.map_mul, Matrix.map_mul, hpr']

end
end QuaternionicSymmetry.CompactSymplecticQuaternionicOrbit
