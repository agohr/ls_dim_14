import QuaternionicSymmetry.FixedTraceGram
import QuaternionicSymmetry.SymplecticTraceProjection

/-! Fixed symplectic trace probes for a numerical PSD covariance on a family
of Hermitian anti-self-dual matrices. -/

namespace QuaternionicSymmetry.FixedSymplecticTraceGram

open Matrix QuaternionicMatrixModel SymplecticTraceProjection
open scoped ComplexOrder MatrixOrder

noncomputable section

variable {n : ℕ} {β S : Type*} [Fintype β] [CommRing S] [Algebra ℝ S]

/-- The Gram probes can be chosen in the actual compact-symplectic spectral
class. They depend on the numerical PSD matrix and the matrix family, but not
on the coefficient algebra element `η`. -/
theorem psd_fixed_symplectic_covariance_squares
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, HermitianAntiSelfDual (B b)) :
    ∃ P : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × Fin 2 →
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      (∀ q, HermitianAntiSelfDual (P q)) ∧
      ∀ η : β → S,
        CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η =
          ∑ q, (∑ b, algebraMap ℝ S
            (Matrix.trace (P q * B b)).re * η b) ^ 2 := by
  obtain ⟨P, hP, hsq⟩ := FixedTraceGram.psd_fixed_covariance_squares
    (S := S) A B hA (fun b => (hB b).1)
  let J := CompactSymplecticHaar.standardJ n
  refine ⟨fun q => antiProjection J (P q),
    fun q => antiProjection_HermitianAntiSelfDual (P q) (hP q), ?_⟩
  intro η
  rw [hsq η]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [trace_antiProjection_of_HermitianAntiSelfDual (P q) (B b) (hB b)]

/-- Choose spectral-class Gram probes from the numerical PSD matrix once;
the same probes work for every anti-self-dual matrix family, including every
symplectic conjugate of a curvature family. -/
theorem psd_fixed_symplectic_covariance_squares_all_families
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (hA : A.PosSemidef) :
    ∃ P : (Fin n ⊕ Fin n) × (Fin n ⊕ Fin n) × Fin 2 →
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ,
      (∀ q, HermitianAntiSelfDual (P q)) ∧
      ∀ (B : β → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ),
        (∀ b, HermitianAntiSelfDual (B b)) → ∀ η : β → S,
          CovariancePolynomial.quadratic (MatrixMoments.covarianceMatrix A B) η =
            ∑ q, (∑ b, algebraMap ℝ S
              (Matrix.trace (P q * B b)).re * η b) ^ 2 := by
  obtain ⟨P, hP, hsq⟩ := FixedTraceGram.psd_fixed_covariance_squares_all_families
    (β := β) (S := S) A hA
  let J := CompactSymplecticHaar.standardJ n
  refine ⟨fun q => antiProjection J (P q),
    fun q => antiProjection_HermitianAntiSelfDual (P q) (hP q), ?_⟩
  intro B hB η
  rw [hsq B (fun b => (hB b).1) η]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [trace_antiProjection_of_HermitianAntiSelfDual (P q) (B b) (hB b)]

end
end QuaternionicSymmetry.FixedSymplecticTraceGram
