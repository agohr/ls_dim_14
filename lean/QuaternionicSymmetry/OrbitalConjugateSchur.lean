import QuaternionicSymmetry.CompactSymplecticTraceInvariants
import QuaternionicSymmetry.OrbitalRealDiagonalSchurContinuation
import QuaternionicSymmetry.OrbitalInterleavedBridge

/-!
The diagonal moment identity transported along actual compact symplectic
conjugations. The right side is expressed intrinsically by matrix trace
powers. Existence of these diagonalizations is a separate spectral theorem.
-/

namespace QuaternionicSymmetry.OrbitalConjugateSchur

open Matrix CompactSymplecticHaar CompactSymplecticTraceInvariants
  OrbitalDiagonalSpectra OrbitalRealSchurPolynomial
  OrbitalRealDiagonalSchurContinuation OrbitalInterleavedBridge

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def matrixSchurValue (X : Matrix κ κ ℂ) (lam : List ℕ) : ℝ :=
  MvPolynomial.aeval (fun i : Fin 6 => evenTracePower X (i.val + 1))
    (FiniteTypeCSchurSix.schur lam)

theorem matrixSchurValue_conjugate (J : Matrix κ κ ℂ) (u : stabilizer J)
    (X : Matrix κ κ ℂ) (lam : List ℕ) :
    matrixSchurValue (conjugate J u X) lam = matrixSchurValue X lam := by
  simp only [matrixSchurValue, evenTracePower_conjugate]

theorem matrixSchurValue_diagonal {n : ℕ} (x : Fin n → ℝ) (lam : List ℕ) :
    matrixSchurValue (hermitianDiagonal x) lam = realSchurValue x lam := by
  simp only [matrixSchurValue, evenTracePower_diagonal, realSchurValue]

/-- Intrinsic trace-power version of the moment identity for matrices with
explicit symplectic diagonalizations. The sole analytic input is the literal
interleaved diagonal source formula; the conjugations and normalizations are
proved here and in the imported modules. -/
theorem evenMoment_finiteSchur_of_diagonalizations
    (hsource : LiteralInterleavedFormula) (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (B X : Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (x y : Fin (m+6) → ℝ) (u v : CompactSymplecticHaar.Group (m+6))
    (hB : B = conjugate (standardJ (m+6)) u (hermitianDiagonal x))
    (hX : X = conjugate (standardJ (m+6)) v (hermitianDiagonal y)) :
    evenMoment (standardJ (m+6)) B X k / ((2*k).factorial : ℝ) =
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
          matrixSchurValue B lam * matrixSchurValue X lam := by
  rw [hB, hX, evenMoment_conjugate_left, evenMoment_conjugate_right]
  simp only [matrixSchurValue_conjugate, matrixSchurValue_diagonal]
  exact diagonal_evenMoment_finiteSchur_allReal
    (literal_implies_grouped hsource) m k hm hk x y

end
end QuaternionicSymmetry.OrbitalConjugateSchur
