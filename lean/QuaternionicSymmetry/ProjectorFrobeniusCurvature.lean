import QuaternionicSymmetry.ProjectorPeirceCurvatureBracket
import QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

/-! Frobenius positivity for the actual matrix double-commutator
curvature expression. These are finite-matrix identities, independent of any
assumed model curvature. -/

namespace QuaternionicSymmetry.ProjectorFrobeniusCurvature

open Matrix CompactSymplecticProjectorAmbientMetric
open ProjectorPeirceCurvatureBracket
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ

theorem frobenius_mul_right (n : ℕ) (K Y X : Mat n) :
    frobeniusPairing n (K * Y) X = frobeniusPairing n K (X * Yᴴ) := by
  unfold frobeniusPairing
  rw [Matrix.conjTranspose_mul]
  rw [mul_assoc, Matrix.trace_mul_comm Yᴴ (Kᴴ * X), mul_assoc]

theorem frobenius_mul_left (n : ℕ) (Y K X : Mat n) :
    frobeniusPairing n (Y * K) X = frobeniusPairing n K (Yᴴ * X) := by
  unfold frobeniusPairing
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]

theorem frobenius_double_commutator_eq_commutator_square
    (n : ℕ) (X Y : Mat n) (hY : Yᴴ = Y) :
    frobeniusPairing n (commutator (commutator X Y) Y) X =
      frobeniusPairing n (commutator X Y) (commutator X Y) := by
  let K := commutator X Y
  change frobeniusPairing n (K * Y - Y * K) X =
    frobeniusPairing n K (X * Y - Y * X)
  have hleft : frobeniusPairing n (K * Y - Y * K) X =
      frobeniusPairing n (K * Y) X - frobeniusPairing n (Y * K) X := by
    simp [frobeniusPairing, Matrix.conjTranspose_sub, Matrix.sub_mul,
      Matrix.trace_sub]
  have hright : frobeniusPairing n K (X * Y - Y * X) =
      frobeniusPairing n K (X * Y) - frobeniusPairing n K (Y * X) := by
    simp [frobeniusPairing, Matrix.mul_sub, Matrix.trace_sub]
  rw [hleft, hright, frobenius_mul_right, frobenius_mul_left, hY]

theorem frobenius_double_commutator_nonneg
    (n : ℕ) (X Y : Mat n) (hY : Yᴴ = Y) :
    0 ≤ frobeniusPairing n (commutator (commutator X Y) Y) X := by
  rw [frobenius_double_commutator_eq_commutator_square n X Y hY]
  exact frobeniusPairing_self_nonneg n _

end
end QuaternionicSymmetry.ProjectorFrobeniusCurvature
