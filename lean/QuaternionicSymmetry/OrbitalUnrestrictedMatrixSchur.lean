import QuaternionicSymmetry.OrbitalSymplecticSpectral
import QuaternionicSymmetry.OrbitalConjugateSchur

/-! The finite Haar-Schur identity for arbitrary Hermitian anti-self-dual
matrix arguments, via the checked compact symplectic spectral theorem. -/

namespace QuaternionicSymmetry.OrbitalUnrestrictedMatrixSchur

open QuaternionicMatrixModel OrbitalSymplecticSpectral
open OrbitalConjugateSchur CompactSymplecticHaar
open OrbitalInterleavedBridge

noncomputable section

theorem evenMoment_finiteSchur
    (hsource : LiteralInterleavedFormula) (m k : ℕ)
    (hm : 5 ≤ m) (hk : k ≤ 6)
    (B X : Matrix (Fin (m+6) ⊕ Fin (m+6))
      (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hB : HermitianAntiSelfDual B) (hX : HermitianAntiSelfDual X) :
    evenMoment (standardJ (m+6)) B X k / ((2*k).factorial : ℝ) =
      ∑ lam ∈ (FiniteTypeCSchurSix.partitions k).toFinset,
        (QuarticOrbitalEleven.factorialRho (m+6) lam : ℝ) *
          matrixSchurValue B lam * matrixSchurValue X lam := by
  obtain ⟨x, u, hu⟩ := exists_symplectic_diagonalization hB
  obtain ⟨y, v, hv⟩ := exists_symplectic_diagonalization hX
  exact evenMoment_finiteSchur_of_diagonalizations
    hsource m k hm hk B X x y u v hu hv

end
end QuaternionicSymmetry.OrbitalUnrestrictedMatrixSchur
