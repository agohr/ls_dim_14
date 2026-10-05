import QuaternionicSymmetry.OrbitalDiagonalMomentPolynomial

/-! The actual diagonal Haar moment is polynomial in the left spectrum as
well, with arbitrary fixed right matrix. -/

namespace QuaternionicSymmetry.OrbitalDiagonalLeftMomentPolynomial

open Matrix MeasureTheory CompactSymplecticHaar OrbitalDiagonalSpectra
open OrbitalDiagonalMomentPolynomial

noncomputable section
set_option maxHeartbeats 200000

def leftPairingLinear {n : ℕ}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : CompactSymplecticHaar.Group n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ →ₗ[ℝ] ℝ where
  toFun B := halfTrace (standardJ n) B X g
  map_add' B C := by
    simp [halfTrace, Matrix.add_mul, Matrix.trace_add, add_div]
  map_smul' t B := by
    simp [halfTrace, Matrix.trace_smul]
    ring

def leftCoordinates {n : ℕ}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : CompactSymplecticHaar.Group n) (i : Fin n) : ℝ :=
  halfTrace (standardJ n) (hermitianDiagonal (Pi.single i 1)) X g

theorem continuous_leftCoordinates {n : ℕ}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (i : Fin n) :
    Continuous (fun g => leftCoordinates X g i) :=
  continuous_halfTrace _ _ _

theorem halfTrace_leftDiagonal_eq_sum {n : ℕ}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : CompactSymplecticHaar.Group n) (x : Fin n → ℝ) :
    halfTrace (standardJ n) (hermitianDiagonal x) X g =
      ∑ i, leftCoordinates X g i * x i := by
  have hx : x = ∑ i : Fin n, x i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    funext j
    simp [Pi.single_apply]
  change ((leftPairingLinear X g).comp (diagonalLinear n)) x = _
  conv_lhs => rw [hx]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change x i * leftCoordinates X g i = leftCoordinates X g i * x i
  exact mul_comm _ _

def leftMomentPolynomial {n : ℕ}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  CompactMomentPolynomial.moment (probability (standardJ n))
    (leftCoordinates X) (2*k)

theorem eval_leftMomentPolynomial {n : ℕ}
    (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (k : ℕ) (x : Fin n → ℝ) :
    (leftMomentPolynomial X k).eval x =
      evenMoment (standardJ n) (hermitianDiagonal x) X k := by
  rw [leftMomentPolynomial,
    CompactMomentPolynomial.eval_moment _ _
      (continuous_pi (continuous_leftCoordinates X))]
  simp only [evenMoment, halfTrace_leftDiagonal_eq_sum]

end
end QuaternionicSymmetry.OrbitalDiagonalLeftMomentPolynomial
