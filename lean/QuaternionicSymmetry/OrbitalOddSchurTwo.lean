import QuaternionicSymmetry.OrbitalOddRemainderSchur
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-! The first nontrivial companion/Newton comparison for odd alternants. -/

namespace QuaternionicSymmetry.OrbitalOddSchurTwo

open Matrix Polynomial Finset MvPolynomial
open OrbitalOddRemainderSchur OrbitalOddSchurWeightOne

noncomputable section

def elementary (n r : ℕ) (t : Fin n → ℚ) : ℚ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
    ∏ i ∈ s, t i

theorem elementary_one (n : ℕ) (t : Fin n → ℚ) :
    elementary n 1 t = ∑ i : Fin n, t i := by
  simp [elementary, Finset.powersetCard_one]

theorem monomialRemainder_two (n : ℕ) (hn : 2 ≤ n)
    (t : Fin n → ℚ) :
    ((Polynomial.X ^ (n+1)) %ₘ spectralRootPoly t).coeff (n-1) =
      (elementary n 1 t) ^ 2 - elementary n 2 t := by
  have hnpos : 0 < n := by omega
  have h1 := monomialRemainder_degree_coeff t (r := 1) (by omega) (by omega : 1 ≤ n)
  have h2 := monomialRemainder_degree_coeff t (r := 2) (by omega) hn
  have hp := spectralRootPoly_coeff t (r := 1) (by omega : 1 ≤ n)
  have hrec := monomialRemainder_coeff_succ hnpos t n (n-1)
  have hidx : n-1-1 = n-2 := by omega
  rw [hidx] at hrec
  have hone : 1 ≤ n-1 := by omega
  simp only [if_pos hone] at hrec
  change _ = (elementary n 1 t)^2 - elementary n 2 t
  change ((Polynomial.X ^ n) %ₘ spectralRootPoly t).coeff (n-1) =
      -((-1 : ℚ)^1 * elementary n 1 t) at h1
  change ((Polynomial.X ^ n) %ₘ spectralRootPoly t).coeff (n-2) =
      -((-1 : ℚ)^2 * elementary n 2 t) at h2
  change (spectralRootPoly t).coeff (n-1) =
      (-1 : ℚ)^1 * elementary n 1 t at hp
  rw [h1, h2, hp] at hrec
  norm_num at hrec
  linear_combination hrec

theorem newton_two (n : ℕ) (t : Fin n → ℚ) :
    (2 : ℚ) * elementary n 2 t =
      (∑ i : Fin n, t i) ^ 2 - ∑ i : Fin n, t i ^ 2 := by
  have hpoly :
      (2 : MvPolynomial (Fin n) ℚ) * esymm (Fin n) ℚ 2 =
        (psum (Fin n) ℚ 1) ^ 2 - psum (Fin n) ℚ 2 := by
    have h := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℚ 2 (by norm_num)
    have hfin : (Finset.antidiagonal 2).filter
        (fun a : ℕ × ℕ => a.1 ∈ Set.Ioo 0 2) = {(1, 1)} := by decide
    rw [hfin] at h
    simp [MvPolynomial.esymm_one, MvPolynomial.psum] at h ⊢
    norm_num at h
    linear_combination h
  have h := congrArg (MvPolynomial.aeval t) hpoly
  simpa [MvPolynomial.psum, MvPolynomial.esymm,
    elementary, MvPolynomial.aeval_sum, MvPolynomial.aeval_prod] using h

theorem schurEvalOnSquares_two (n : ℕ) (x : Fin n → ℚ) :
    schurEvalOnSquares x [2] =
      (elementary n 1 (fun i => x i ^ 2)) ^ 2 -
        elementary n 2 (fun i => x i ^ 2) := by
  let t : Fin n → ℚ := fun i => x i ^ 2
  have hn := newton_two n t
  simp [schurEvalOnSquares, FiniteTypeCSchurSix.schur,
    FiniteTypeCSchurSix.h2, FiniteTypeCSchurSix.p1,
    FiniteTypeCSchurSix.p2, FiniteTypeCSchurSix.h1]
  rw [elementary_one]
  dsimp [t] at hn
  linear_combination hn / 2

theorem monomialRemainder_two_schur (m : ℕ)
    (x : Fin (m+2) → ℚ) :
    ((Polynomial.X ^ (m+3)) %ₘ
      spectralRootPoly (fun i => x i ^ 2)).coeff (m+1) =
      schurEvalOnSquares x [2] := by
  convert monomialRemainder_two (m+2) (by omega)
    (fun i => x i ^ 2) using 1
  rw [schurEvalOnSquares_two]

theorem oneRowCoefficient_one_schur (m : ℕ)
    (x : Fin (m+2) → ℚ) :
    OrbitalOddSchurOneRow.oneRowCoefficient (m+1) 1 (fun i => x i ^ 2) =
      schurEvalOnSquares x [2] := by
  simpa [OrbitalOddSchurOneRow.oneRowCoefficient,
    OrbitalOddSchurOneRow.oneRowRemainder,
    OrbitalOddSchurWeightOne.rootPoly, spectralRootPoly,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    monomialRemainder_two_schur m x

/-- The arbitrary-rank two-box one-row bialternant identity, stated without
division by the odd Vandermonde. -/
theorem det_raisedOddAlternantRow_two_schur (m : ℕ)
    (x : Fin (m+2) → ℚ) :
    (OrbitalOddSchurOneRow.raisedOddAlternantRow (m+1) 1 x).det =
      OrbitalOddDeterminantBase.oddVandermonde x *
        schurEvalOnSquares x [2] := by
  rw [OrbitalOddSchurOneRow.det_raisedOddAlternantRow,
    oneRowCoefficient_one_schur]

end
end QuaternionicSymmetry.OrbitalOddSchurTwo
