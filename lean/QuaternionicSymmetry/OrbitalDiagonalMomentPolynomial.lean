import QuaternionicSymmetry.OrbitalRegularPolynomialContinuation

/-! Actual diagonal Haar moments as polynomials, followed by universal
continuation from the source's positive regular rational spectral region. -/

namespace QuaternionicSymmetry.OrbitalDiagonalMomentPolynomial

open Matrix MeasureTheory CompactSymplecticHaar OrbitalDiagonalSpectra
  OrbitalRegularPolynomialContinuation OrbitalOddDeterminantBase

noncomputable section

def diagonalLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ]
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ where
  toFun := hermitianDiagonal
  map_add' x y := by
    ext i j
    simp only [hermitianDiagonal, Matrix.add_apply, Matrix.diagonal_apply, Pi.add_apply]
    split_ifs <;> cases i <;> simp [add_comm]
  map_smul' t x := by
    change hermitianDiagonal (fun i => t * x i) = t • hermitianDiagonal x
    rw [hermitianDiagonal_scale]
    ext i j
    simp

def pairingLinear {n : ℕ} (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : CompactSymplecticHaar.Group n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ →ₗ[ℝ] ℝ where
  toFun X := halfTrace (standardJ n) B X g
  map_add' X Y := by
    simp [halfTrace, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, add_div]
  map_smul' t X := by
    simp [halfTrace, Matrix.trace_smul]
    ring

def coordinates {n : ℕ} (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : CompactSymplecticHaar.Group n) (i : Fin n) : ℝ :=
  halfTrace (standardJ n) B (hermitianDiagonal (Pi.single i 1)) g

theorem continuous_coordinates {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (i : Fin n) :
    Continuous (fun g => coordinates B g i) :=
  continuous_halfTrace _ _ _

theorem halfTrace_diagonal_eq_sum {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)
    (g : CompactSymplecticHaar.Group n) (x : Fin n → ℝ) :
    halfTrace (standardJ n) B (hermitianDiagonal x) g =
      ∑ i, coordinates B g i * x i := by
  have hx : x = ∑ i : Fin n, x i • (Pi.single i 1 : Fin n → ℝ) := by
    funext j
    simp [Pi.single_apply]
  change ((pairingLinear B g).comp (diagonalLinear n)) x = _
  conv_lhs => rw [hx]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  change x i * coordinates B g i = coordinates B g i * x i
  exact mul_comm _ _

def momentPolynomial {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) :
    MvPolynomial (Fin n) ℝ :=
  CompactMomentPolynomial.moment (probability (standardJ n)) (coordinates B) (2 * k)

theorem eval_momentPolynomial {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ) (x : Fin n → ℝ) :
    (momentPolynomial B k).eval x =
      evenMoment (standardJ n) B (hermitianDiagonal x) k := by
  rw [momentPolynomial, CompactMomentPolynomial.eval_moment _ _ (continuous_pi (continuous_coordinates B))]
  simp only [evenMoment, halfTrace_diagonal_eq_sum]

/-- A moment formula on positive rational simple spectra determines the
actual moment polynomial, including at zero or repeated spectral values. -/
theorem momentPolynomial_eq_of_regular {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ x : Fin n → ℚ, (∀ i, 0 < x i) → oddVandermonde x ≠ 0 →
      evenMoment (standardJ n) B (hermitianDiagonal (fun i => (x i : ℝ))) k =
        p.eval (fun i => (x i : ℝ))) : momentPolynomial B k = p := by
  apply polynomial_eq_of_positive_nondegenerate
  intro x hx hΔ
  rw [eval_momentPolynomial]
  exact hp x hx hΔ

/-- Evaluation in any real commutative algebra, including the even exterior
algebra with nilpotents, uses no spectral nondegeneracy assumptions. -/
theorem average_eq_aeval_of_regular {n : ℕ}
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) (k : ℕ)
    (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ x : Fin n → ℚ, (∀ i, 0 < x i) → oddVandermonde x ≠ 0 →
      evenMoment (standardJ n) B (hermitianDiagonal (fun i => (x i : ℝ))) k =
        p.eval (fun i => (x i : ℝ)))
    {S : Type*} [CommRing S] [Algebra ℝ S] (η : Fin n → S) :
    CompactPolynomialAverage.average (probability (standardJ n)) (coordinates B)
      ((GaussianPolynomialExpectation.linearPolynomial η) ^ (2 * k)) =
        MvPolynomial.aeval η p := by
  rw [← CompactMomentPolynomial.aeval_moment]
  change MvPolynomial.aeval η (momentPolynomial B k) = _
  rw [momentPolynomial_eq_of_regular B k p hp]

end
end QuaternionicSymmetry.OrbitalDiagonalMomentPolynomial
