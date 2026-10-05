import QuaternionicSymmetry.CompactSymplecticMoments

/-!
Matrix convention checks for the symplectic orbital formula.  The source
uses `U J Uᵀ = J` and an adjoint on its second anti-Hermitian argument.
These lemmas match those conventions to the actual Haar pairing.  They do
not assert the Harish--Chandra integral evaluation.
-/

namespace QuaternionicSymmetry.OrbitalSourceConventions

open Matrix MeasureTheory CompactSymplecticHaar

noncomputable section

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem transpose_preservation_iff (J U : Matrix κ κ ℂ) (hJ : J * J = -1) :
    Uᵀ * J * U = J ↔ U * J * Uᵀ = J := by
  have forward (A : Matrix κ κ ℂ) (h : Aᵀ * J * A = J) :
      A * J * Aᵀ = J := by
    have hprod : (J * Aᵀ) * (-J * A) = 1 := by
      calc
        _ = -(J * (Aᵀ * J * A)) := by noncomm_ring
        _ = 1 := by rw [h, hJ]; simp
    have hrev := (mul_eq_one_comm).mp hprod
    have hh : J * (A * J * Aᵀ) = -1 := by
      have : -(J * (A * J * Aᵀ)) = 1 := by
        calc
          _ = (-J * A) * (J * Aᵀ) := by noncomm_ring
          _ = 1 := hrev
      exact neg_eq_iff_eq_neg.mp this
    have hh' := congrArg (fun M : Matrix κ κ ℂ => J * M) hh
    simpa only [← mul_assoc, hJ, neg_mul, one_mul, mul_neg, mul_one,
      neg_inj] using hh'
  constructor
  · exact forward U
  · intro h
    simpa only [Matrix.transpose_transpose] using forward Uᵀ (by simpa using h)

theorem source_preservation (n : ℕ) (g : CompactSymplecticHaar.Group n) :
    (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) * standardJ n *
      (g.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)ᵀ = standardJ n :=
  (transpose_preservation_iff _ _ (standardJ_sq n)).mp g.2

/-- Multiplication by `-i` changes an anti-Hermitian argument into the
Hermitian convention used for the curvature contractions. -/
def hermitianArgument (X : Matrix κ κ ℂ) : Matrix κ κ ℂ := (-Complex.I) • X

omit [DecidableEq κ] in
theorem hermitianArgument_conjTranspose (X : Matrix κ κ ℂ) (hX : Xᴴ = -X) :
    (hermitianArgument X)ᴴ = hermitianArgument X := by
  simp [hermitianArgument, Matrix.conjTranspose_smul, hX]

omit [DecidableEq κ] in
/-- The source's second adjoint is essential: its two factors of `i`
cancel the sign introduced by that adjoint. -/
theorem source_pairing_eq (X Y U : Matrix κ κ ℂ) (hY : Yᴴ = -Y) :
    X * U * Yᴴ * Uᴴ =
      hermitianArgument X * U * hermitianArgument Y * Uᴴ := by
  rw [hY]
  simp only [hermitianArgument, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

theorem source_halfTrace_eq (J X Y : Matrix κ κ ℂ) (hY : Yᴴ = -Y)
    (g : stabilizer J) :
    (Matrix.trace (X * (g.1 : Matrix κ κ ℂ) * Yᴴ *
      (g.1 : Matrix κ κ ℂ)ᴴ)).re / 2 =
        halfTrace J (hermitianArgument X) (hermitianArgument Y) g := by
  rw [source_pairing_eq X Y _ hY]
  rfl

theorem source_trace_im_zero (J X Y : Matrix κ κ ℂ)
    (hX : Xᴴ = -X) (hY : Yᴴ = -Y) (g : stabilizer J) :
    (Matrix.trace (X * (g.1 : Matrix κ κ ℂ) * Yᴴ *
      (g.1 : Matrix κ κ ℂ)ᴴ)).im = 0 := by
  rw [source_pairing_eq X Y _ hY]
  exact trace_pairing_im_zero_of_hermitian J _ _
    (hermitianArgument_conjTranspose X hX)
    (hermitianArgument_conjTranspose Y hY) g

theorem source_exponentialIntegral_eq (J X Y : Matrix κ κ ℂ) (hY : Yᴴ = -Y)
    (t : ℝ) :
    (∫ g : stabilizer J, Real.exp (t *
      ((Matrix.trace (X * (g.1 : Matrix κ κ ℂ) * Yᴴ *
        (g.1 : Matrix κ κ ℂ)ᴴ)).re / 2)) ∂probability J) =
      exponentialIntegral J (hermitianArgument X) (hermitianArgument Y) t := by
  simp_rw [source_halfTrace_eq J X Y hY]
  rfl

end
end QuaternionicSymmetry.OrbitalSourceConventions
