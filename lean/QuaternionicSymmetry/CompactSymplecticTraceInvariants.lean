import QuaternionicSymmetry.OrbitalDiagonalSpectra

/-! Trace-power invariants of actual compact symplectic conjugacy classes. -/

namespace QuaternionicSymmetry.CompactSymplecticTraceInvariants

open Matrix CompactSymplecticHaar OrbitalDiagonalSpectra

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem conjugate_pow (J : Matrix κ κ ℂ) (u : stabilizer J)
    (X : Matrix κ κ ℂ) (r : ℕ) :
    conjugate J u X ^ r = conjugate J u (X ^ r) := by
  have hleft : (u.1 : Matrix κ κ ℂ)ᴴ * (u.1 : Matrix κ κ ℂ) = 1 := u.1.2.1
  have hright : (u.1 : Matrix κ κ ℂ) * (u.1 : Matrix κ κ ℂ)ᴴ = 1 := u.1.2.2
  induction r with
  | zero => simp [conjugate, hright]
  | succ r ih =>
    rw [pow_succ, ih, pow_succ]
    unfold conjugate
    calc
      _ = (u.1 : Matrix κ κ ℂ) * X ^ r *
          ((u.1 : Matrix κ κ ℂ)ᴴ * (u.1 : Matrix κ κ ℂ)) * X *
          (u.1 : Matrix κ κ ℂ)ᴴ := by simp only [mul_assoc]
      _ = _ := by rw [hleft]; simp only [mul_one, mul_assoc]

theorem trace_conjugate (J : Matrix κ κ ℂ) (u : stabilizer J)
    (X : Matrix κ κ ℂ) : Matrix.trace (conjugate J u X) = Matrix.trace X := by
  have hleft : (u.1 : Matrix κ κ ℂ)ᴴ * (u.1 : Matrix κ κ ℂ) = 1 := u.1.2.1
  unfold conjugate
  rw [mul_assoc, Matrix.trace_mul_comm (u.1 : Matrix κ κ ℂ), mul_assoc, hleft,
    mul_one]

def evenTracePower (X : Matrix κ κ ℂ) (r : ℕ) : ℝ :=
  (Matrix.trace (X ^ (2 * r))).re / 2

theorem evenTracePower_conjugate (J : Matrix κ κ ℂ) (u : stabilizer J)
    (X : Matrix κ κ ℂ) (r : ℕ) :
    evenTracePower (conjugate J u X) r = evenTracePower X r := by
  simp only [evenTracePower, conjugate_pow, trace_conjugate]

theorem evenTracePower_diagonal {n : ℕ} (x : Fin n → ℝ) (r : ℕ) :
    evenTracePower (hermitianDiagonal x) r = ∑ i, (x i ^ 2) ^ r := by
  simp only [evenTracePower, hermitianDiagonal, Matrix.diagonal_pow,
    Matrix.trace_diagonal, Fintype.sum_sum_type, Pi.pow_apply, Sum.elim_inl, Sum.elim_inr]
  simp only [pow_mul, neg_sq]
  simp only [Complex.re_sum, Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

end
end QuaternionicSymmetry.CompactSymplecticTraceInvariants
