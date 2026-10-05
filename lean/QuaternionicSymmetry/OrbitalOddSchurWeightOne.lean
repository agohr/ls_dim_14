import QuaternionicSymmetry.OrbitalOddOrderedSelections

/-!
# The arbitrary-rank weight-one bialternant identity

The first Schur coefficient is obtained from a polynomial-root relation
without dividing by a Vandermonde or by spectral values.
-/

namespace QuaternionicSymmetry.OrbitalOddSchurWeightOne

open Matrix Polynomial Finset
open OrbitalOddDeterminantBase OrbitalOddCoefficientFormula

noncomputable section

def rootPoly (n : ℕ) (t : Fin (n+1) → ℚ) : Polynomial ℚ :=
  ∏ i : Fin (n+1), (Polynomial.X - Polynomial.C (t i))

def rootSum (n : ℕ) (t : Fin (n+1) → ℚ) : ℚ :=
  ∑ i : Fin (n+1), t i

def reducedPoly (n : ℕ) (t : Fin (n+1) → ℚ) : Polynomial ℚ :=
  Polynomial.X ^ (n+1) - rootPoly n t - Polynomial.C (rootSum n t) * Polynomial.X ^ n

theorem rootPoly_top (n : ℕ) (t : Fin (n+1) → ℚ) :
    (rootPoly n t).coeff (n+1) = 1 := by
  have hm : (rootPoly n t).Monic := by
    exact Polynomial.monic_prod_X_sub_C t Finset.univ
  have hd : (rootPoly n t).natDegree = n+1 := by
    simp [rootPoly]
  rw [← hd]
  exact hm.coeff_natDegree

theorem rootPoly_next (n : ℕ) (t : Fin (n+1) → ℚ) :
    (rootPoly n t).coeff n = -rootSum n t := by
  simpa [rootPoly, rootSum] using
    (Polynomial.prod_X_sub_C_coeff_card_pred Finset.univ t (by simp : 0 < (Finset.univ : Finset (Fin (n+1))).card))

theorem reducedPoly_degree (n : ℕ) (t : Fin (n+1) → ℚ) :
    (reducedPoly n t).natDegree ≤ n := by
  have hP : (rootPoly n t).natDegree ≤ n+1 := by
    simp [rootPoly]
  have hr : (rootPoly n t - Polynomial.X ^ (n+1)).natDegree ≤ n := by
    have h := Polynomial.natDegree_le_pred (n := n+1)
      (p := rootPoly n t - Polynomial.X ^ (n+1))
      (by exact (Polynomial.natDegree_sub_le _ _).trans (max_le hP (by simp)))
      (by simp [Polynomial.coeff_sub, rootPoly_top])
    simpa only [Nat.add_sub_cancel] using h
  have hc : (Polynomial.C (rootSum n t) * Polynomial.X ^ n).natDegree ≤ n := by
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  unfold reducedPoly
  have hr' : (Polynomial.X ^ (n+1) - rootPoly n t).natDegree ≤ n := by
    have heq : Polynomial.X ^ (n+1) - rootPoly n t =
        -(rootPoly n t - Polynomial.X ^ (n+1)) := by ring
    rw [heq, Polynomial.natDegree_neg]
    exact hr
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le hr' hc)

theorem reducedPoly_coeff_last (n : ℕ) (t : Fin (n+1) → ℚ) :
    (reducedPoly n t).coeff n = 0 := by
  unfold reducedPoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, rootPoly_next]
  simp

theorem rootPoly_eval_zero (n : ℕ) (t : Fin (n+1) → ℚ) (i : Fin (n+1)) :
    (rootPoly n t).eval (t i) = 0 := by
  unfold rootPoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

def reducedBasis (n : ℕ) (t : Fin (n+1) → ℚ)
    (j : Fin (n+1)) : Polynomial ℚ :=
  if j = Fin.last n then reducedPoly n t else Polynomial.X ^ j.val

theorem reducedBasis_degree (n : ℕ) (t : Fin (n+1) → ℚ)
    (j : Fin (n+1)) :
    (reducedBasis n t j).natDegree ≤ j.val := by
  by_cases hj : j = Fin.last n
  · subst j
    simpa [reducedBasis] using reducedPoly_degree n t
  · simp [reducedBasis, hj]

theorem reducedBasis_last_coeff_zero (n : ℕ) (t : Fin (n+1) → ℚ)
    (j : Fin (n+1)) :
    (reducedBasis n t j).coeff n = 0 := by
  by_cases hj : j = Fin.last n
  · subst j
    simpa [reducedBasis] using reducedPoly_coeff_last n t
  · have hlt : j.val < n := by
      have hle := j.isLt
      have hne : j.val ≠ n := by
        intro h
        apply hj
        exact Fin.ext h
      omega
    simp [reducedBasis, hj, hlt.ne']

theorem reducedBasis_eval (n : ℕ) (t : Fin (n+1) → ℚ)
    (i j : Fin (n+1)) :
    (reducedBasis n t j).eval (t i) =
      if j = Fin.last n then t i ^ (n+1) - rootSum n t * t i ^ n
      else t i ^ j.val := by
  by_cases hj : j = Fin.last n
  · simp [reducedBasis, hj, reducedPoly, rootPoly_eval_zero]
  · simp [reducedBasis, hj]

theorem reducedBasis_det_zero (n : ℕ) (t : Fin (n+1) → ℚ) :
    (Matrix.of fun i j => (reducedBasis n t j).eval (t i)).det = 0 := by
  rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
    t (reducedBasis n t) (reducedBasis_degree n t)]
  rw [Matrix.det_mul]
  have hz : (Matrix.of fun (i j : Fin (n+1)) =>
      (reducedBasis n t j).coeff i.val).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last n)
    intro j
    simpa only [Matrix.of_apply, Fin.val_last] using reducedBasis_last_coeff_zero n t j
  rw [hz, mul_zero]

theorem raised_vandermonde_weight_one (n : ℕ)
    (t : Fin (n+1) → ℚ) :
    (Matrix.of fun i j : Fin (n+1) =>
      t i ^ (if j = Fin.last n then n+1 else j.val)).det =
      (rootSum n t) * (Matrix.vandermonde t).det := by
  let V := Matrix.vandermonde t
  let u : Fin (n+1) → ℚ := fun i => t i ^ (n+1)
  let v : Fin (n+1) → ℚ := fun i => -(rootSum n t) * t i ^ n
  have hzero : (V.updateCol (Fin.last n) (u + v)).det = 0 := by
    convert reducedBasis_det_zero n t using 1
    congr 1
    ext i j
    rw [Matrix.of_apply, reducedBasis_eval]
    by_cases hj : j = Fin.last n
    · subst j
      simp [V, u, v]
      ring
    · simp [V, u, v, hj]
  rw [Matrix.det_updateCol_add] at hzero
  have hraised : V.updateCol (Fin.last n) u =
      Matrix.of fun i j : Fin (n+1) =>
        t i ^ (if j = Fin.last n then n+1 else j.val) := by
    ext i j
    by_cases hj : j = Fin.last n
    · subst j
      simp [V, u]
    · simp [V, u, hj]
  have hbase : V.updateCol (Fin.last n) (fun i => t i ^ n) = V := by
    ext i j
    by_cases hj : j = Fin.last n
    · subst j
      simp [V]
    · simp [V, hj]
  have hv : v = (-(rootSum n t)) • (fun i => t i ^ n) := by
    funext i
    rfl
  rw [hv, Matrix.det_updateCol_smul, hbase, hraised] at hzero
  dsimp [V] at hzero
  linarith

def raisedOddAlternant (n : ℕ) (x : Fin (n+1) → ℚ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j =>
    x i ^ (2 * (if j = Fin.last n then n+1 else j.val) + 1)

/-- The one-box bialternant identity, valid even when coordinates vanish or
coincide. -/
theorem det_raisedOddAlternant (n : ℕ) (x : Fin (n+1) → ℚ) :
    (raisedOddAlternant n x).det =
      oddVandermonde x * ∑ i : Fin (n+1), x i ^ 2 := by
  let t : Fin (n+1) → ℚ := fun i => x i ^ 2
  have hra : raisedOddAlternant n x =
      Matrix.of fun i j => x i *
        (Matrix.of fun i j : Fin (n+1) =>
          t i ^ (if j = Fin.last n then n+1 else j.val)) i j := by
    ext i j
    simp only [raisedOddAlternant, Matrix.of_apply, t]
    rw [← pow_mul, pow_add]
    ring
  have hbase : oddAlternant x =
      Matrix.of fun i j => x i * (Matrix.vandermonde t) i j := by
    ext i j
    simp only [oddAlternant, Matrix.of_apply, Matrix.vandermonde_apply, t]
    rw [← pow_mul, pow_add]
    ring
  have hodd : (∏ i : Fin (n+1), x i) * (Matrix.vandermonde t).det =
      oddVandermonde x := by
    rw [← Matrix.det_mul_column]
    exact (congrArg Matrix.det hbase).symm.trans (det_oddAlternant x)
  rw [hra, Matrix.det_mul_column, raised_vandermonde_weight_one]
  change (∏ i : Fin (n+1), x i) *
      ((∑ i : Fin (n+1), x i ^ 2) * (Matrix.vandermonde t).det) =
    oddVandermonde x * ∑ i : Fin (n+1), x i ^ 2
  rw [← hodd]
  ring

/-- Evaluate the existing six-weight Schur polynomials on squared rational
spectral variables. -/
def schurEvalOnSquares {n : ℕ} (x : Fin n → ℚ)
    (lam : List ℕ) : ℚ :=
  MvPolynomial.aeval
    (fun i : Fin 6 => ∑ j : Fin n, (x j ^ 2) ^ (i.val + 1))
    (FiniteTypeCSchurSix.schur lam)

theorem schurEvalOnSquares_one (n : ℕ) (x : Fin (n+1) → ℚ) :
    schurEvalOnSquares x [1] = ∑ i : Fin (n+1), x i ^ 2 := by
  simp [schurEvalOnSquares, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.h1, FiniteTypeCSchurSix.p1]

theorem det_raisedOddAlternant_schur (n : ℕ) (x : Fin (n+1) → ℚ) :
    (raisedOddAlternant n x).det =
      oddVandermonde x * schurEvalOnSquares x [1] := by
  rw [det_raisedOddAlternant, schurEvalOnSquares_one]

end
end QuaternionicSymmetry.OrbitalOddSchurWeightOne
