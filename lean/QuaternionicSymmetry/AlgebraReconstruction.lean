import QuaternionicSymmetry.AlgebraCertificates
import QuaternionicSymmetry.Characters

/-! The full finite convolution in arbitrary commutative rational algebras.
The unconstrained tail explicitly verifies the truncation in rings with nilpotents.
-/

namespace QuaternionicSymmetry.AlgebraReconstruction

open AlgebraCertificates Characters
noncomputable section
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def Aext (n : ℕ) (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) : ℕ → R
  | 0 => evaluate u z₁ z₂ z₃ z₄ A₀
  | 1 => evaluate u z₁ z₂ z₃ z₄ (A₁ n)
  | 2 => evaluate u z₁ z₂ z₃ z₄ (A₂ n)
  | 3 => evaluate u z₁ z₂ z₃ z₄ (A₃ n)
  | 4 => evaluate u z₁ z₂ z₃ z₄ (A₄ n)
  | j + 5 => tail (j + 5)

def fullDensity (n : ℕ) (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) : R :=
  ∑ j ∈ Finset.range (n + 1),
    algebraMap ℚ R (taylorCoefficient (n - j) (virtual n)) *
      u ^ (n - j) * Aext n u z₁ z₂ z₃ z₄ tail j

theorem fullDensity₂ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 2 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₂ := by
  have h := taylor_two
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂]
  simp [K₂]

theorem fullDensity₃ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 3 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₃ := by
  have h := taylor_three
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃]
  simp [K₃]
  ring

theorem fullDensity₄ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 4 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₄ := by
  have h := taylor_four
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄]
  simp [K₄]
  ring

theorem fullDensity₅ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 5 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₅ := by
  have h := taylor_five
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅]
  simp [K₅]
  ring

theorem fullDensity₆ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 6 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₆ := by
  have h := taylor_six
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆]
  simp [K₆]
  ring

theorem fullDensity₇ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 7 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₇ := by
  have h := taylor_seven
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  simp [K₇]
  ring

theorem fullDensity₈ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 8 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₈ := by
  have h := taylor_eight
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  simp [K₈]
  ring

theorem fullDensity₉ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 9 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₉ := by
  have h := taylor_nine
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉]
  simp [K₉]
  ring

theorem fullDensity₁₀ (u z₁ z₂ z₃ z₄ : R) (tail : ℕ → R) :
    fullDensity 10 u z₁ z₂ z₃ z₄ tail = evaluate u z₁ z₂ z₃ z₄ K₁₀ := by
  have h := taylor_ten
  norm_num [List.range_succ] at h
  rcases h with ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩
  simp only [fullDensity, Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceSub, Aext]
  rw [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀]
  simp [K₁₀]
  ring

end
end QuaternionicSymmetry.AlgebraReconstruction
