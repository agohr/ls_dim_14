import QuaternionicSymmetry.OrbitalOddSchurWeightOne
import Mathlib.Algebra.Polynomial.Div

/-!
# One-row bialternants in arbitrary degree

Reduction modulo the monic root polynomial gives a division-free expression
for every one-row alternant quotient. The coefficient of the last basis
monomial is the complete homogeneous symmetric function in the spectral
variables; matching its Newton form is a separate finite identity.
-/

namespace QuaternionicSymmetry.OrbitalOddSchurOneRow

open Matrix Polynomial Finset OrbitalOddSchurWeightOne
open OrbitalOddDeterminantBase

noncomputable section

def oneRowRemainder (n k : ℕ) (t : Fin (n+1) → ℚ) : Polynomial ℚ :=
  (Polynomial.X ^ (n + k + 1)) %ₘ rootPoly n t

def oneRowCoefficient (n k : ℕ) (t : Fin (n+1) → ℚ) : ℚ :=
  (oneRowRemainder n k t).coeff n

private theorem oneRowRemainder_degree (n k : ℕ)
    (t : Fin (n+1) → ℚ) :
    (oneRowRemainder n k t).natDegree ≤ n := by
  have hm : (rootPoly n t).Monic :=
    Polynomial.monic_prod_X_sub_C t Finset.univ
  have hne : rootPoly n t ≠ 1 := by
    intro h
    have hd : (rootPoly n t).natDegree = n+1 := by simp [rootPoly]
    rw [h] at hd
    simp at hd
  have hd : (rootPoly n t).natDegree = n+1 := by simp [rootPoly]
  have hlt := Polynomial.natDegree_modByMonic_lt
    (Polynomial.X ^ (n+k+1)) hm hne
  simpa only [oneRowRemainder, hd, Nat.lt_succ_iff] using hlt

private theorem oneRowRemainder_eval (n k : ℕ)
    (t : Fin (n+1) → ℚ) (i : Fin (n+1)) :
    (oneRowRemainder n k t).eval (t i) = t i ^ (n+k+1) := by
  have hm : (rootPoly n t).Monic :=
    Polynomial.monic_prod_X_sub_C t Finset.univ
  have hroot := rootPoly_eval_zero n t i
  unfold oneRowRemainder
  have h := Polynomial.eval₂_modByMonic_eq_self_of_root
    (f := RingHom.id ℚ) (p := Polynomial.X ^ (n+k+1))
    (q := rootPoly n t) hm hroot
  simpa using h

/-- Reduce one polynomial evaluation column modulo the root polynomial. -/
private theorem det_eval_last_column (n : ℕ) (t : Fin (n+1) → ℚ)
    (p : Polynomial ℚ) (hdeg : p.natDegree ≤ n) :
    (Matrix.of fun i j : Fin (n+1) =>
      if j = Fin.last n then p.eval (t i) else t i ^ j.val).det =
      p.coeff n * (Matrix.vandermonde t).det := by
  let c := p.coeff n
  let q := p - Polynomial.C c * Polynomial.X ^ n
  have hqdeg : q.natDegree ≤ n := by
    dsimp [q]
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hdeg ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)))
  have hqcoeff : q.coeff n = 0 := by
    simp [q, c]
  let b : Fin (n+1) → Polynomial ℚ := fun j =>
    if j = Fin.last n then q else Polynomial.X ^ j.val
  have hbdeg : ∀ j : Fin (n+1), (b j).natDegree ≤ j.val := by
    intro j
    by_cases hj : j = Fin.last n
    · subst j
      simpa [b] using hqdeg
    · simp [b, hj]
  have hdetzero : (Matrix.of fun i j : Fin (n+1) =>
      (b j).eval (t i)).det = 0 := by
    rw [Matrix.eval_matrixOfPolynomials_eq_vandermonde_mul_matrixOfPolynomials
      t b hbdeg, Matrix.det_mul]
    have hz : (Matrix.of fun (i j : Fin (n+1)) => (b j).coeff i.val).det = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last n)
      intro j
      by_cases hj : j = Fin.last n
      · subst j
        simpa [b] using hqcoeff
      · have hlt : j.val < n := by
          have hjlt := j.isLt
          have hne : j.val ≠ n := by
            intro h
            exact hj (Fin.ext h)
          omega
        simp [b, hj, hlt.ne']
    rw [hz, mul_zero]
  let V := Matrix.vandermonde t
  let u : Fin (n+1) → ℚ := fun i => p.eval (t i)
  let v : Fin (n+1) → ℚ := fun i => -c * t i ^ n
  have hzero : (V.updateCol (Fin.last n) (u + v)).det = 0 := by
    convert hdetzero using 1
    congr 1
    ext i j
    by_cases hj : j = Fin.last n
    · subst j
      simp [b, q, c, V, u, v]
      ring
    · simp [b, V, u, v, hj]
  rw [Matrix.det_updateCol_add] at hzero
  have hfirst : V.updateCol (Fin.last n) u =
      Matrix.of fun i j : Fin (n+1) =>
        if j = Fin.last n then p.eval (t i) else t i ^ j.val := by
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
  have hv : v = (-c) • (fun i => t i ^ n) := by
    funext i
    rfl
  rw [hv, Matrix.det_updateCol_smul, hbase, hfirst] at hzero
  dsimp [V] at hzero
  linarith

theorem raised_vandermonde_one_row (n k : ℕ)
    (t : Fin (n+1) → ℚ) :
    (Matrix.of fun i j : Fin (n+1) =>
      t i ^ (if j = Fin.last n then n+k+1 else j.val)).det =
      oneRowCoefficient n k t * (Matrix.vandermonde t).det := by
  have h := det_eval_last_column n t (oneRowRemainder n k t)
    (oneRowRemainder_degree n k t)
  simpa [oneRowCoefficient, oneRowRemainder_eval] using h

def raisedOddAlternantRow (n k : ℕ) (x : Fin (n+1) → ℚ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j =>
    x i ^ (2 * (if j = Fin.last n then n+k+1 else j.val) + 1)

theorem det_raisedOddAlternantRow (n k : ℕ) (x : Fin (n+1) → ℚ) :
    (raisedOddAlternantRow n k x).det =
      oddVandermonde x *
        oneRowCoefficient n k (fun i => x i ^ 2) := by
  let t : Fin (n+1) → ℚ := fun i => x i ^ 2
  have hra : raisedOddAlternantRow n k x =
      Matrix.of fun i j => x i *
        (Matrix.of fun i j : Fin (n+1) =>
          t i ^ (if j = Fin.last n then n+k+1 else j.val)) i j := by
    ext i j
    simp only [raisedOddAlternantRow, Matrix.of_apply, t]
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
  rw [hra, Matrix.det_mul_column, raised_vandermonde_one_row]
  change (∏ i : Fin (n+1), x i) *
      (oneRowCoefficient n k t * (Matrix.vandermonde t).det) =
    oddVandermonde x * oneRowCoefficient n k t
  rw [← hodd]
  ring

/-- The first remainder coefficient agrees with the one-box Schur value. -/
theorem oneRowCoefficient_zero (n : ℕ) (t : Fin (n+1) → ℚ) :
    oneRowCoefficient n 0 t = rootSum n t := by
  let P := rootPoly n t
  let r := Polynomial.C (rootSum n t) * Polynomial.X ^ n + reducedPoly n t
  have hm : P.Monic := Polynomial.monic_prod_X_sub_C t Finset.univ
  have hdegP : P.natDegree = n+1 := by simp [P, rootPoly]
  have hrdeg : r.natDegree ≤ n := by
    dsimp [r]
    exact Polynomial.natDegree_add_le_of_degree_le
      ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
      (reducedPoly_degree n t)
  have hrem : r %ₘ P = r := by
    apply (Polynomial.modByMonic_eq_self_iff hm).mpr
    have hdegree : r.degree ≤ (n : WithBot ℕ) :=
      Polynomial.natDegree_le_iff_degree_le.mp hrdeg
    have hPdegree : P.degree = (n+1 : WithBot ℕ) := by
      rw [Polynomial.degree_eq_natDegree hm.ne_zero, hdegP]
      norm_cast
    rw [hPdegree]
    exact hdegree.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  have hdvd : P ∣ Polynomial.X ^ (n+1) - r := by
    refine ⟨1, ?_⟩
    dsimp [r, P, reducedPoly]
    ring
  have hcongr : (Polynomial.X ^ (n+1)) %ₘ P = r %ₘ P :=
    Polynomial.modByMonic_eq_of_dvd_sub hm hdvd
  unfold oneRowCoefficient oneRowRemainder
  change ((Polynomial.X ^ (n+1)) %ₘ P).coeff n = rootSum n t
  rw [hcongr, hrem]
  simp [r, reducedPoly_coeff_last]

end
end QuaternionicSymmetry.OrbitalOddSchurOneRow
