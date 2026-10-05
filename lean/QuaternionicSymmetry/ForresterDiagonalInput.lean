import QuaternionicSymmetry.OrbitalDiagonalSpectra

/-!
Explicit diagonal specialization of the registered literature input:
Forrester--Ipsen--Liu--Zhang, arXiv:1711.10691v1, Eq. (1.8), with constants
from (1.5)--(1.6). Complex coordinates are grouped as the first and second
entries of the quaternionic blocks. The measure is normalized Haar measure.

`ForresterDiagonalFormula` is a proposition supplied as a theorem argument,
not a Lean axiom. Its only assertion is the source's scalar integral formula
on positive nondegenerate diagonal spectra. Parameter scaling, passage to
Hermitian arguments, analytic continuation through zero, and coefficient
extraction are proved below. Extension to arbitrary symplectic conjugacy
classes and degenerate spectra is a further obligation.
-/

namespace QuaternionicSymmetry.ForresterDiagonalInput

open Matrix MeasureTheory CompactSymplecticHaar OrbitalSourceConventions
  OrbitalDiagonalSpectra OrbitalAnalyticOddKernel OrbitalOddDeterminantBase
  OrbitalHaarPositiveParameter OrbitalHaarCoefficientExtraction

noncomputable section

/-- The precise scalar diagonal instance of Eq. (1.8). In particular the
source uses the adjoint of the second anti-Hermitian matrix. -/
def ForresterDiagonalFormula : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (x y : Fin n → ℝ),
    (∀ i, 0 < x i) → (∀ i, 0 < y i) →
    realOddVandermonde x * realOddVandermonde y ≠ 0 →
    (∫ g : CompactSymplecticHaar.Group n,
      Real.exp ((Matrix.trace (antiHermitianDiagonal x *
        (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) *
        (antiHermitianDiagonal y)ᴴ *
        (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᴴ)).re / 2)
      ∂probability (standardJ n)) =
      (sourceConstant n : ℝ) * realSourceDeterminant x y /
        (realOddVandermonde x * realOddVandermonde y)

theorem diagonal_positive_quotient (hsource : ForresterDiagonalFormula)
    {n : ℕ} (hn : 0 < n) (x y : Fin n → ℚ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hΔ : oddVandermonde x * oddVandermonde y ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    exponentialIntegral (standardJ n)
      (hermitianDiagonal (fun i => (x i : ℝ)))
      (hermitianDiagonal (fun i => (y i : ℝ))) t =
      (sourceConstant n : ℝ) * (sourceDeterminant x y : ℝ → ℝ) t /
        (t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ)) := by
  have hΔreal : realOddVandermonde (fun i => t * (x i : ℝ)) *
      realOddVandermonde (fun i => (y i : ℝ)) =
      t ^ (n ^ 2) * ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) := by
    rw [realOddVandermonde_scale, realOddVandermonde_rat, realOddVandermonde_rat]
    push_cast
    ring
  have h := hsource n hn (fun i => t * (x i : ℝ)) (fun i => (y i : ℝ))
    (fun i => mul_pos ht (by exact_mod_cast hx i))
    (fun i => by change 0 < (y i : ℝ); exact_mod_cast hy i)
    (by
      rw [hΔreal]
      exact mul_ne_zero (pow_ne_zero _ (ne_of_gt ht)) (by exact_mod_cast hΔ))
  rw [hΔreal, realSourceDeterminant_rat_scale] at h
  simp_rw [source_halfTrace_eq _ _ _ (antiHermitianDiagonal_conjTranspose _),
    hermitianArgument_antiHermitianDiagonal, halfTrace_diagonal_scale] at h
  exact h

/-- The scalar source formula yields the actual Haar Taylor coefficient,
with the exact factorial and odd-determinant normalizer. -/
theorem diagonal_coefficient (hsource : ForresterDiagonalFormula)
    {n : ℕ} (hn : 0 < n) (x y : Fin n → ℚ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hΔ : oddVandermonde x * oddVandermonde y ≠ 0) (k : ℕ) :
    ((oddVandermonde x * oddVandermonde y : ℚ) : ℝ) *
      (evenMoment (standardJ n)
        (hermitianDiagonal (fun i => (x i : ℝ)))
        (hermitianDiagonal (fun i => (y i : ℝ))) k /
        ((2 * k).factorial : ℝ)) =
      (sourceConstant n : ℝ) *
        ((PowerSeries.coeff (n ^ 2 + 2 * k)
          (OrbitalOddFormalKernel.sourceFullFormalOddKernel x y).det : ℚ) : ℝ) :=
  coefficient_of_positive_quotient x y _ _ _ hΔ
    (diagonal_positive_quotient hsource hn x y hx hy hΔ) k

end
end QuaternionicSymmetry.ForresterDiagonalInput
