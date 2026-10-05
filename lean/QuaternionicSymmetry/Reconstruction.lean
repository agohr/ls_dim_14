import QuaternionicSymmetry.Certificates
import QuaternionicSymmetry.LogAhat
import QuaternionicSymmetry.Characters

/-!
  The root-formula side of the certificate calculation.

  This module connects the finite `rawB` formula proved in `LogAhat` to the
  closed `a_j` expressions used in `Certificates`.  A following section will
  attach the independently computed Laurent-character Taylor coefficients.
-/

namespace QuaternionicSymmetry
namespace Reconstruction

open LogAhat
open Characters

variable {R : Type*} [Field R] [CharZero R]

/-- The only corrected Weyl variables needed through weight four. -/
def zSeq (z₁ z₂ z₃ z₄ : R) : ℕ → R
  | 1 => z₁
  | 2 => z₂
  | 3 => z₃
  | 4 => z₄
  | _ => 0

private theorem taylor₃_values :
    taylorCoefficient 0 (virtual 3) = 0 ∧ taylorCoefficient 1 (virtual 3) = 0
      ∧ taylorCoefficient 2 (virtual 3) = 32 ∧ taylorCoefficient 3 (virtual 3) = 112 / 3 := by
  have h := taylor_three
  norm_num [List.range_succ] at h
  exact h

theorem rawB₁ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    rawB n u (zSeq z₁ z₂ z₃ z₄) 1 = Certificates.b₁ (n : R) u z₁ := by
  rw [LogAhat.rawB_one]
  simp only [zSeq]
  rfl

theorem rawB₂ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    rawB n u (zSeq z₁ z₂ z₃ z₄) 2 = Certificates.b₂ (n : R) u z₁ z₂ := by
  rw [LogAhat.rawB_two]
  simp only [zSeq]
  rfl

theorem rawB₃ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    rawB n u (zSeq z₁ z₂ z₃ z₄) 3 = Certificates.b₃ (n : R) u z₁ z₂ z₃ := by
  rw [LogAhat.rawB_three]
  simp only [zSeq]
  rfl

theorem rawB₄ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    rawB n u (zSeq z₁ z₂ z₃ z₄) 4 = Certificates.b₄ (n : R) u z₁ z₂ z₃ z₄ := by
  rw [LogAhat.rawB_four]
  simp only [zSeq]
  rfl

set_option linter.unusedSectionVars false in
theorem rawA₀ :
    LogAhat.A0 (R := R) = Certificates.a₀ (R := R) := rfl

theorem rawA₁ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    LogAhat.A1 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1) = Certificates.a₁ (n : R) u z₁ := by
  rw [rawB₁]
  rfl

theorem rawA₂ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    LogAhat.A2 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1) (rawB n u (zSeq z₁ z₂ z₃ z₄) 2)
      = Certificates.a₂ (n : R) u z₁ z₂ := by
  rw [rawB₁, rawB₂]
  rfl

theorem rawA₃ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    LogAhat.A3 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1) (rawB n u (zSeq z₁ z₂ z₃ z₄) 2)
      (rawB n u (zSeq z₁ z₂ z₃ z₄) 3) = Certificates.a₃ (n : R) u z₁ z₂ z₃ := by
  rw [rawB₁, rawB₂, rawB₃]
  rfl

theorem rawA₄ (n : ℕ) (u z₁ z₂ z₃ z₄ : R) :
    LogAhat.A4 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1) (rawB n u (zSeq z₁ z₂ z₃ z₄) 2)
      (rawB n u (zSeq z₁ z₂ z₃ z₄) 3) (rawB n u (zSeq z₁ z₂ z₃ z₄) 4)
        = Certificates.a₄ (n : R) u z₁ z₂ z₃ z₄ := by
  rw [rawB₁, rawB₂, rawB₃, rawB₄]
  rfl

/-- Coefficients of `exp(log A-hat)`: exact through weight four, arbitrary later.
The arbitrary tail makes every later truncation statement a consequence of
proved character-coefficient vanishing, rather than an implicit assumption. -/
def Aext (n : ℕ) (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) : ℕ → R
  | 0 => LogAhat.A0
  | 1 => LogAhat.A1 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1)
  | 2 => LogAhat.A2 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1) (rawB n u (zSeq z₁ z₂ z₃ z₄) 2)
  | 3 => LogAhat.A3 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1) (rawB n u (zSeq z₁ z₂ z₃ z₄) 2)
    (rawB n u (zSeq z₁ z₂ z₃ z₄) 3)
  | 4 => LogAhat.A4 (rawB n u (zSeq z₁ z₂ z₃ z₄) 1) (rawB n u (zSeq z₁ z₂ z₃ z₄) 2)
    (rawB n u (zSeq z₁ z₂ z₃ z₄) 3) (rawB n u (zSeq z₁ z₂ z₃ z₄) 4)
  | j + 5 => tail (j + 5)

/-- The complete degree-`n` finite convolution. -/
noncomputable def fullDensity (n : ℕ) (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) : R :=
  ∑ j ∈ Finset.range (n + 1),
    (taylorCoefficient (n - j) (virtual n) : R) * u ^ (n - j) * Aext n u z₁ z₂ z₃ z₄ tail j

theorem fullDensity₂ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 2 u z₁ z₂ z₃ z₄ tail = Certificates.K₂ u z₁ z₂ z₃ z₄ := by
  have h := taylor_two
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂]
  norm_num
  rw [rawA₀]
  rfl

theorem fullDensity₃ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 3 u z₁ z₂ z₃ z₄ tail = Certificates.K₃ u z₁ z₂ z₃ z₄ := by
  have h := taylor_three
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃]
  norm_num
  rw [rawA₀, rawA₁]
  simp only [Certificates.K₃]
  ring_nf

theorem fullDensity₄ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 4 u z₁ z₂ z₃ z₄ tail = Certificates.K₄ u z₁ z₂ z₃ z₄ := by
  have h := taylor_four
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄]
  norm_num
  rw [rawA₀, rawA₁]
  simp only [Certificates.K₄]
  ring_nf

theorem fullDensity₅ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 5 u z₁ z₂ z₃ z₄ tail = Certificates.K₅ u z₁ z₂ z₃ z₄ := by
  have h := taylor_five
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅]
  norm_num
  rw [rawA₀, rawA₁, rawA₂]
  simp only [Certificates.K₅]
  ring_nf

theorem fullDensity₆ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 6 u z₁ z₂ z₃ z₄ tail = Certificates.K₆ u z₁ z₂ z₃ z₄ := by
  have h := taylor_six
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆]
  norm_num
  rw [rawA₀, rawA₁, rawA₂]
  simp only [Certificates.K₆]
  ring_nf

theorem fullDensity₇ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 7 u z₁ z₂ z₃ z₄ tail = Certificates.K₇ u z₁ z₂ z₃ z₄ := by
  have h := taylor_seven
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  norm_num
  rw [rawA₀, rawA₁, rawA₂, rawA₃]
  simp only [Certificates.K₇]
  ring_nf

theorem fullDensity₈ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 8 u z₁ z₂ z₃ z₄ tail = Certificates.K₈ u z₁ z₂ z₃ z₄ := by
  have h := taylor_eight
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  norm_num
  rw [rawA₀, rawA₁, rawA₂, rawA₃]
  simp only [Certificates.K₈]
  ring_nf

theorem fullDensity₉ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 9 u z₁ z₂ z₃ z₄ tail = Certificates.K₉ u z₁ z₂ z₃ z₄ := by
  have h := taylor_nine
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]
  norm_num
  rw [rawA₀, rawA₁, rawA₂, rawA₃, rawA₄]
  simp only [Certificates.K₉]
  ring_nf

theorem fullDensity₁₀ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 10 u z₁ z₂ z₃ z₄ tail = Certificates.K₁₀ u z₁ z₂ z₃ z₄ := by
  have h := taylor_ten
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]
  norm_num
  rw [rawA₀, rawA₁, rawA₂, rawA₃, rawA₄]
  simp only [Certificates.K₁₀]
  ring_nf

end Reconstruction
end QuaternionicSymmetry
