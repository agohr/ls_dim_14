import QuaternionicSymmetry.CompactSymplecticProjectorQuaternionicUpperLinear
import QuaternionicSymmetry.CompactSymplecticProjectorBlockFrobenius

/-! Two explicit quaternionic upper blocks at every positive complement
dimension have a nonzero Hermitian off-diagonal commutator. -/

namespace QuaternionicSymmetry.ProjectorQuaternionicNoncommutingBlock

open Matrix
open CompactSymplecticProjectorQuaternionicRow
open CompactSymplecticProjectorQuaternionicUpperLinear
open scoped Matrix.Norms.Operator
noncomputable section

private abbrev J (n : ℕ) := Fin n ⊕ Fin n
private abbrev BMat (n : ℕ) := Matrix (Fin 2) (J n) ℂ

private def firstColumn (n : ℕ) (hn : 0 < n) : J n :=
  Sum.inl ⟨0, hn⟩

private def realRow (n : ℕ) (hn : 0 < n) : J n → ℂ :=
  fun c => if c = firstColumn n hn then 1 else 0

private def imaginaryRow (n : ℕ) (hn : 0 < n) : J n → ℂ :=
  fun c => if c = firstColumn n hn then Complex.I else 0

def realBlock (n : ℕ) (hn : 0 < n) : BMat n :=
  upperBlockFromRow n (realRow n hn)

def imaginaryBlock (n : ℕ) (hn : 0 < n) : BMat n :=
  upperBlockFromRow n (imaginaryRow n hn)

theorem realBlock_quaternionic (n : ℕ) (hn : 0 < n) :
    realBlock n hn ∈ upperSubmodule n :=
  (mem_upperSubmodule_iff n _).2 (upperBlockFromRow_quaternionic n _)

theorem imaginaryBlock_quaternionic (n : ℕ) (hn : 0 < n) :
    imaginaryBlock n hn ∈ upperSubmodule n :=
  (mem_upperSubmodule_iff n _).2 (upperBlockFromRow_quaternionic n _)

theorem real_imaginary_block_commutator_nonzero (n : ℕ) (hn : 0 < n) :
    realBlock n hn * (imaginaryBlock n hn)ᴴ -
      imaginaryBlock n hn * (realBlock n hn)ᴴ ≠ 0 := by
  intro h
  have hh := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) h
  simp only [Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at hh
  have hsum₁ :
      ∑ c : J n, realBlock n hn 0 c * star (imaginaryBlock n hn 0 c) =
        -Complex.I := by
    simp [realBlock, imaginaryBlock, realRow, imaginaryRow, firstColumn]
  have hsum₂ :
      ∑ c : J n, imaginaryBlock n hn 0 c * star (realBlock n hn 0 c) =
        Complex.I := by
    simp [realBlock, imaginaryBlock, realRow, imaginaryRow, firstColumn]
  rw [hsum₁, hsum₂] at hh
  have hI : Complex.I = 0 := by
    linear_combination (-1 / 2 : ℂ) * hh
  exact Complex.I_ne_zero hI

end
end QuaternionicSymmetry.ProjectorQuaternionicNoncommutingBlock
