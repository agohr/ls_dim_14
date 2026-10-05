import QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicRow

/-! The explicit real-linear 4n-dimensional quaternionic upper-block
space, with no tangent-range equality assumed. -/

namespace QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicUpperLinear

open Matrix
open CompactSymplecticStabilizerFormBlocks
open CompactSymplecticProjectorQuaternionicRow
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev BMat (n : ℕ) := Matrix (Fin 2) (J n) ℂ

/-- The real-linear equation defining a quaternionic mixed block. -/
def upperConstraint (n : ℕ) : BMat n →ₗ[ℝ] BMat n where
  toFun B := B * CompactSymplecticHaar.standardJ n - firstBlockJ * B.map star
  map_add' := by
    intro B C
    have hmap : (B + C).map star = B.map star + C.map star := by
      ext i j
      simp
    rw [hmap]
    simp only [Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' := by
    intro r B
    simp [Matrix.map_smul, smul_sub]

/-- The actual solution space is a real submodule of the complex rectangular
matrix space. -/
def upperSubmodule (n : ℕ) : Submodule ℝ (BMat n) := (upperConstraint n).ker

theorem mem_upperSubmodule_iff (n : ℕ) (B : BMat n) :
    B ∈ upperSubmodule n ↔
      B * CompactSymplecticHaar.standardJ n = firstBlockJ * B.map star := by
  simp [upperSubmodule, upperConstraint, sub_eq_zero]

/-- First-row extraction is a real-linear map on the exact quaternionic
solution subspace. -/
def upperRowLinear (n : ℕ) : upperSubmodule n →ₗ[ℝ] (J n → ℂ) where
  toFun B := B.1 0
  map_add' := by intro B C; rfl
  map_smul' := by intro r B; rfl

theorem upperRowLinear_injective (n : ℕ) : Function.Injective (upperRowLinear n) := by
  intro B C h
  have hB : B.1 * CompactSymplecticHaar.standardJ n =
      firstBlockJ * B.1.map star := (mem_upperSubmodule_iff n B.1).1 B.2
  have hC : C.1 * CompactSymplecticHaar.standardJ n =
      firstBlockJ * C.1.map star := (mem_upperSubmodule_iff n C.1).1 C.2
  have h' : (⟨B.1, hB⟩ : QuaternionicUpper n) = ⟨C.1, hC⟩ :=
    (upperBlockRowEquiv n).injective h
  have hMat : B.1 = C.1 := congrArg
    (fun D : QuaternionicUpper n => D.1) h'
  exact Subtype.ext hMat

theorem upperRowLinear_surjective (n : ℕ) : Function.Surjective (upperRowLinear n) := by
  intro b
  refine ⟨⟨upperBlockFromRow n b,
    (mem_upperSubmodule_iff n _).2 (upperBlockFromRow_quaternionic n b)⟩, ?_⟩
  rfl

/-- No block coordinates are missing: the quaternionic solution space is
real-linearly equivalent to two complex rows of length `n`. -/
def upperRowLinearEquiv (n : ℕ) : upperSubmodule n ≃ₗ[ℝ] (J n → ℂ) :=
  LinearEquiv.ofBijective (upperRowLinear n)
    ⟨upperRowLinear_injective n, upperRowLinear_surjective n⟩

/-- The independently defined ambient quaternionic upper-block solution
space has exactly real dimension `4n`. -/
theorem upperSubmodule_real_finrank (n : ℕ) :
    Module.finrank ℝ (upperSubmodule n) = 4 * n := by
  rw [LinearEquiv.finrank_eq (upperRowLinearEquiv n)]
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex,
    Fintype.card_sum]
  omega

end
end QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicUpperLinear
