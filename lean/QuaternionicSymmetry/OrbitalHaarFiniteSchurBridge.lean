import QuaternionicSymmetry.OrbitalOddFiniteSchurBridge
import QuaternionicSymmetry.ForresterDiagonalInput

/-! Under the stated diagonal source formula, the checked finite Schur
coefficient is the actual normalized compact-symplectic Haar moment. -/

namespace QuaternionicSymmetry.OrbitalHaarFiniteSchurBridge

open OrbitalOddFiniteSchurBridge OrbitalOddDeterminantBase
open CompactSymplecticHaar OrbitalDiagonalSpectra ForresterDiagonalInput

noncomputable section

theorem diagonal_evenMoment_finiteSchur
    (hsource : ForresterDiagonalFormula) (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (x y : Fin (m+6) → ℚ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hΔ : oddVandermonde x * oddVandermonde y ≠ 0) :
    evenMoment (standardJ (m+6))
      (hermitianDiagonal (fun i => (x i : ℝ)))
      (hermitianDiagonal (fun i => (y i : ℝ))) k /
        ((2*k).factorial : ℝ) =
      ((∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        QuarticOrbitalEleven.factorialRho (m+6) lam *
          OrbitalOddSchurWeightOne.schurEvalOnSquares x lam *
            OrbitalOddSchurWeightOne.schurEvalOnSquares y lam : ℚ) : ℝ) := by
  have hsourceCoeff := diagonal_coefficient hsource (n := m+6)
    (by omega) x y hx hy hΔ k
  have hformal := sourceFullFormalOddKernel_coeff_finiteSchur m k hm hk x y
  have hformalR := congrArg (fun q : ℚ => (q : ℝ)) hformal
  push_cast at hformalR
  rw [hformalR] at hsourceCoeff
  have hΔR : ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast hΔ
  apply (mul_left_cancel₀ hΔR)
  simpa only [Rat.cast_mul, Rat.cast_sum] using hsourceCoeff

/-- The actual diagonal Haar moment is the evaluation of the existing finite
type-C orbital polynomial at the squared spectrum's power sums. The sole
external premise is the source's explicit diagonal integral formula. -/
theorem diagonal_evenMoment_orbital
    (hsource : ForresterDiagonalFormula) (m k : ℕ) (hm : 5 ≤ m)
    (hk : k ≤ 6) (a : List ℕ) (x y : Fin (m+6) → ℚ)
    (hpower : ∀ i : Fin 6,
      FiniteTypeCSchurSix.powerSum a (i.val+1) =
        ∑ j : Fin (m+6), (x j ^ 2) ^ (i.val+1))
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hΔ : oddVandermonde x * oddVandermonde y ≠ 0) :
    (4 : ℝ)^k *
      (evenMoment (standardJ (m+6))
        (hermitianDiagonal (fun i => (x i : ℝ)))
        (hermitianDiagonal (fun i => (y i : ℝ))) k /
          ((2*k).factorial : ℝ)) =
      ((MvPolynomial.aeval
        (fun i : Fin 6 => ∑ j : Fin (m+6), (y j ^ 2) ^ (i.val+1))
        (FiniteTypeCSchurSix.orbital (m+6) k a) : ℚ) : ℝ) := by
  rw [diagonal_evenMoment_finiteSchur hsource m k hm hk x y hx hy hΔ]
  rw [orbital_aeval_eq_schur_sum (m+6) k a x y hpower]
  push_cast
  ring

end
end QuaternionicSymmetry.OrbitalHaarFiniteSchurBridge
