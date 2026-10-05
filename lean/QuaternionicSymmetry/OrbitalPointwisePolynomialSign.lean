import QuaternionicSymmetry.OrbitalMatrixPolynomialBridge
import QuaternionicSymmetry.FiniteSchurWeightedScaling
import QuaternionicSymmetry.OrbitalSymplecticSpectral

/-! The finite orbital polynomial has the signed pointwise quaternionic
positive ray once actual matrix diagonalizations are supplied. Its variables
are the real parts of trace powers in the complexified even-form algebra. -/

namespace QuaternionicSymmetry.OrbitalPointwisePolynomialSign

open Matrix Module CompactSymplecticHaar OrbitalDiagonalSpectra
  OrbitalInterleavedBridge OrbitalIntegerSpectrumRealization
  MatrixTracePolynomial OrbitalMatrixPolynomialBridge QuaternionicFundamental
  HyperholomorphicExterior FiniteSchurWeightedScaling

noncomputable section

variable {β ι V : Type*} [Fintype β] [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem orbital_mem_positiveRay_of_diagonalizableCombinations
    (hsource : LiteralInterleavedFormula) (m k : ℕ) (hm : 5 ≤ m) (hk : k ≤ 6)
    (a : List ℕ) (ha : a.length ≤ m+6)
    (A : β → Matrix (Fin (m+6) ⊕ Fin (m+6)) (Fin (m+6) ⊕ Fin (m+6)) ℂ)
    (hdiag : ∀ t : β → ℝ, ∃ (y : Fin (m+6) → ℝ)
      (v : CompactSymplecticHaar.Group (m+6)),
      matrixCombination A t = conjugate (standardJ (m+6)) v (hermitianDiagonal y))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (η : β → E V)
    (hη : ∀ b, η b ∈ formSpace Q c) (hkQ : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (MvPolynomial.aeval (fun i : Fin 6 =>
        signedTracePower (complexifiedMatrix A η) (i.val + 1))
        (FiniteTypeCSchurSix.orbital (m+6) k a) *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) := by
  let B := hermitianDiagonal (sqrtSpectrum (m+6) a)
  have hB : B = conjugate (standardJ (m+6)) 1
      (hermitianDiagonal (sqrtSpectrum (m+6) a)) := by simp [conjugate, B]
  have h := finiteOrbitalPolynomial_mem_positiveRay hsource m k hm hk B A
    (sqrtSpectrum (m+6) a) 1 hB hdiag Q c η hη hkQ
  have heval : MvPolynomial.aeval η (finiteOrbitalPolynomial B A k) =
      MvPolynomial.aeval (fun i : Fin 6 =>
        MvPolynomial.aeval η (tracePowerPolynomial A (i.val + 1)))
        (FiniteTypeCSchurSix.orbital (m+6) k a) := by
    rw [finiteOrbitalPolynomial_sqrtSpectrum a ha A k]
    exact MvPolynomial.comp_aeval_apply
      (fun i : Fin 6 => tracePowerPolynomial A (i.val + 1))
      ((MvPolynomial.aeval η).restrictScalars ℚ)
      (FiniteTypeCSchurSix.orbital (m+6) k a)
  rw [heval, ← orbital_sign _ (m+6) k hk a] at h
  simpa only [signedTracePower, aeval_tracePowerPolynomial] using h

theorem matrixCombination_HermitianAntiSelfDual {n : ℕ}
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (A b)) (t : β → ℝ) :
    QuaternionicMatrixModel.HermitianAntiSelfDual (matrixCombination A t) := by
  have hreal : matrixCombination A t = ∑ b, t b • A b := by
    ext i j
    simp [matrixCombination, Matrix.sum_apply]
  rw [hreal]
  exact (QuaternionicMatrixModel.hermitianAntiSelfDualSubmodule n).sum_mem
    (fun b _ => (QuaternionicMatrixModel.hermitianAntiSelfDualSubmodule n).smul_mem
      (t b) (hA b))

/-- Pointwise orbital positivity in the actual even-form algebra through
weight six, for every matrix rank at least eleven. Matrix diagonalization,
the scalar moment identity, and nilpotent continuation are all discharged.
The only literature premise is the precisely stated scalar source formula. -/
theorem orbital_mem_positiveRay
    (hsource : LiteralInterleavedFormula) (n k : ℕ) (hn : 11 ≤ n) (hk : k ≤ 6)
    (a : List ℕ) (ha : a.length ≤ n)
    (A : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : ∀ b, QuaternionicMatrixModel.HermitianAntiSelfDual (A b))
    (Q : QuaternionicStructure V) (c : Basis ι ℝ V) (η : β → E V)
    (hη : ∀ b, η b ∈ formSpace Q c) (hkQ : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (topForm Q c)
      (MvPolynomial.aeval (fun i : Fin 6 =>
        signedTracePower (complexifiedMatrix A η) (i.val + 1))
        (FiniteTypeCSchurSix.orbital n k a) *
        QuaternionicFundamental.form Q c ^ (Q.quaternionicDimension - k)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  exact orbital_mem_positiveRay_of_diagonalizableCombinations hsource m k
    (by omega) hk a ha A
    (fun t => OrbitalSymplecticSpectral.exists_symplectic_diagonalization
      (matrixCombination_HermitianAntiSelfDual A hA t)) Q c η hη hkQ

end
end QuaternionicSymmetry.OrbitalPointwisePolynomialSign
