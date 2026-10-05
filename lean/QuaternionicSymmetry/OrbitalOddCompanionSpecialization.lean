import QuaternionicSymmetry.OrbitalOddSchurTwo

/-! Coefficient recurrence at the top of the spectral root polynomial. -/

namespace QuaternionicSymmetry.OrbitalOddCompanionSpecialization

open Polynomial Finset
open OrbitalOddRemainderSchur OrbitalOddSchurTwo

noncomputable section

def spectralTail (n s d : ℕ) (t : Fin n → ℚ) : ℚ :=
  ((Polynomial.X ^ (n+s)) %ₘ spectralRootPoly t).coeff (n-d)

/-- The initial companion row is the signed elementary symmetric sequence. -/
theorem spectralTail_zero {n d : ℕ} (t : Fin n → ℚ)
    (hdpos : 0 < d) (hd : d ≤ n) :
    spectralTail n 0 d t = -((-1 : ℚ)^d * elementary n d t) := by
  simpa [spectralTail, elementary] using
    monomialRemainder_degree_coeff t hdpos hd

/-- Moving one power of `X` forward uses only the adjacent prior remainder
coefficient and the degree-`d` elementary coefficient of the root polynomial. -/
theorem spectralTail_succ {n s d : ℕ} (t : Fin n → ℚ)
    (hdpos : 0 < d) (hd : d < n) :
    spectralTail n (s+1) d t =
      spectralTail n s (d+1) t -
        spectralTail n s 1 t * ((-1 : ℚ)^d * elementary n d t) := by
  have hn : 0 < n := hdpos.trans hd
  have hrec := monomialRemainder_coeff_succ hn t (n+s) (n-d)
  have hi : 1 ≤ n-d := by omega
  have hidx : n-d-1 = n-(d+1) := by omega
  have hpow : n+s+1 = n+(s+1) := by omega
  rw [hpow, if_pos hi, hidx,
    spectralRootPoly_coeff t (Nat.le_of_lt hd)] at hrec
  simpa [spectralTail, elementary] using hrec

/-- Each remainder matrix entry is either an unshifted monomial coefficient
or an entry in the companion tail. -/
theorem remainderCoefficientMatrix_entry {n N : ℕ}
    (t : Fin n → ℚ) (e : Fin n → Fin N) (i j : Fin n) :
    remainderCoefficientMatrix t e i j =
      if (e j).val < n then
        if i.val = (e j).val then 1 else 0
      else
        spectralTail n ((e j).val-n) (n-i.val) t := by
  by_cases hlow : (e j).val < n
  · have hmod : (Polynomial.X ^ (e j).val) %ₘ spectralRootPoly t =
        Polynomial.X ^ (e j).val := by
      apply (Polynomial.modByMonic_eq_self_iff (spectralRootPoly_monic t)).mpr
      rw [Polynomial.degree_X_pow]
      rw [Polynomial.degree_eq_natDegree (spectralRootPoly_monic t).ne_zero,
        spectralRootPoly_degree]
      exact_mod_cast hlow
    simp [remainderCoefficientMatrix, exponentRemainder, hlow, hmod]
  · have heq : n + ((e j).val-n) = (e j).val := Nat.add_sub_of_le (Nat.le_of_not_gt hlow)
    have hi : n-(n-i.val) = i.val := Nat.sub_sub_self (Nat.le_of_lt i.isLt)
    simp only [remainderCoefficientMatrix, Matrix.of_apply, exponentRemainder,
      if_neg hlow, spectralTail]
    rw [heq, hi]

end
end QuaternionicSymmetry.OrbitalOddCompanionSpecialization
