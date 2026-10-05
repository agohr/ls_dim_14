import QuaternionicSymmetry.CompactSymplecticProjectorOrbitAction
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The concrete Hilbert--Schmidt pairing on the ambient complex matrices
and its invariance under the actual compact symplectic matrix action. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric

open Matrix CompactSymplecticHaar
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev I (n : ℕ) := Fin (n + 1) ⊕ Fin (n + 1)
private abbrev Mat (n : ℕ) := Matrix (I n) (I n) ℂ
private abbrev G (n : ℕ) := CompactSymplecticHaar.Group (n + 1)

/-- Real Hilbert--Schmidt pairing on the full ambient matrix space. -/
def frobeniusPairing (n : ℕ) (A B : Mat n) : ℝ :=
  (trace (Aᴴ * B)).re

private def pairingRightLinear (n : ℕ) (A : Mat n) : Mat n →ₗ[ℝ] ℝ where
  toFun := frobeniusPairing n A
  map_add' := by
    intro B C
    simp [frobeniusPairing, Matrix.mul_add, Matrix.trace_add]
  map_smul' := by
    intro c B
    simp [frobeniusPairing, Matrix.mul_smul, Matrix.trace_smul]

private def pairingLeftLinear (n : ℕ) : Mat n →ₗ[ℝ] (Mat n →L[ℝ] ℝ) where
  toFun := fun A => (pairingRightLinear n A).toContinuousLinearMap
  map_add' := by
    intro A B
    ext C
    simp [pairingRightLinear, frobeniusPairing,
      Matrix.conjTranspose_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' := by
    intro c A
    ext B
    simp [pairingRightLinear, frobeniusPairing,
      Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.trace_smul]

/-- The actual real Hilbert--Schmidt pairing, continuous in the existing
operator-norm topology on finite complex matrices. -/
def frobeniusCLM (n : ℕ) : Mat n →L[ℝ] Mat n →L[ℝ] ℝ :=
  (pairingLeftLinear n).toContinuousLinearMap

@[simp] theorem frobeniusCLM_apply (n : ℕ) (A B : Mat n) :
    frobeniusCLM n A B = frobeniusPairing n A B := rfl

theorem frobeniusPairing_symm (n : ℕ) (A B : Mat n) :
    frobeniusPairing n A B = frobeniusPairing n B A := by
  unfold frobeniusPairing
  rw [← Complex.conj_re (trace (Aᴴ * B))]
  change (star ((Aᴴ * B).trace)).re = (Bᴴ * A).trace.re
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- The actual real-linear conjugation map on the ambient matrix space. -/
def conjugationCLM (n : ℕ) (u : G n) : Mat n →L[ℝ] Mat n :=
  (show Mat n →ₗ[ℝ] Mat n from {
    toFun := fun A => (u.1 : Mat n) * A * (u.1 : Mat n)ᴴ
    map_add' := by intro A B; simp [mul_add, add_mul]
    map_smul' := by intro c A; simp
  }).toContinuousLinearMap

@[simp] theorem conjugationCLM_apply (n : ℕ) (u : G n) (A : Mat n) :
    conjugationCLM n u A =
      (u.1 : Mat n) * A * (u.1 : Mat n)ᴴ := rfl

/-- On the diagonal the pairing is the sum of squared moduli of all matrix
entries, so it is genuinely positive definite. -/
theorem frobeniusPairing_self_eq_sum_normSq (n : ℕ) (A : Mat n) :
    frobeniusPairing n A A =
      ∑ i : I n, ∑ j : I n, Complex.normSq (A i j) := by
  classical
  simp only [frobeniusPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.re_sum, Complex.ofReal_re]
  exact Finset.sum_comm

theorem frobeniusPairing_self_nonneg (n : ℕ) (A : Mat n) :
    0 ≤ frobeniusPairing n A A := by
  rw [frobeniusPairing_self_eq_sum_normSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

theorem frobeniusPairing_self_eq_zero_iff (n : ℕ) (A : Mat n) :
    frobeniusPairing n A A = 0 ↔ A = 0 := by
  rw [frobeniusPairing_self_eq_sum_normSq]
  constructor
  · intro h
    ext i j
    have hi : (∑ j : I n, Complex.normSq (A i j)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
        Finset.sum_nonneg fun l _ => Complex.normSq_nonneg _)).mp h i (Finset.mem_univ i)
    have hij : Complex.normSq (A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => Complex.normSq_nonneg _)).mp hi j
        (Finset.mem_univ j)
    exact Complex.normSq_eq_zero.mp hij
  · rintro rfl
    simp

theorem frobeniusCLM_symm (n : ℕ) (A B : Mat n) :
    frobeniusCLM n A B = frobeniusCLM n B A :=
  frobeniusPairing_symm n A B

theorem frobeniusCLM_pos (n : ℕ) (A : Mat n) (hA : A ≠ 0) :
    0 < frobeniusCLM n A A := by
  rw [frobeniusCLM_apply]
  have hnonneg := frobeniusPairing_self_nonneg n A
  have hne : frobeniusPairing n A A ≠ 0 := by
    intro h
    exact hA ((frobeniusPairing_self_eq_zero_iff n A).mp h)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Simultaneous unitary conjugation preserves the exact trace pairing. -/
theorem frobeniusPairing_conjugate (n : ℕ) (u : G n) (A B : Mat n) :
    frobeniusPairing n
      ((u.1 : Mat n) * A * (u.1 : Mat n)ᴴ)
      ((u.1 : Mat n) * B * (u.1 : Mat n)ᴴ) =
    frobeniusPairing n A B := by
  have hU : (u.1 : Mat n)ᴴ * (u.1 : Mat n) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self u.1
  unfold frobeniusPairing
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [mul_assoc]
  rw [← mul_assoc ((u.1 : Mat n)ᴴ) (u.1 : Mat n), hU, one_mul]
  rw [Matrix.trace_mul_comm]
  simp only [mul_assoc]
  rw [hU, mul_one]

theorem frobeniusCLM_conjugationCLM (n : ℕ) (u : G n)
    (A B : Mat n) :
    frobeniusCLM n (conjugationCLM n u A)
      (conjugationCLM n u B) = frobeniusCLM n A B := by
  simpa only [frobeniusCLM_apply, conjugationCLM_apply] using
    frobeniusPairing_conjugate n u A B

end
end QuaternionicSymmetry.CompactSymplecticProjectorAmbientMetric
