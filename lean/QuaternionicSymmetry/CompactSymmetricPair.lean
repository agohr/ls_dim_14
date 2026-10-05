import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-! The block-matrix symmetric-pair identities underlying the compact
quaternionic Weyl-curvature connection. The coefficient ring may be
noncommutative, so these identities apply directly to quaternions. -/

namespace QuaternionicSymmetry.CompactSymmetricPair

open Matrix

variable {κ τ R : Type*} [Fintype κ] [Fintype τ] [Ring R] [StarRing R]

def diagonalBlock (A : Matrix κ κ R) (D : Matrix τ τ R) : Matrix (κ ⊕ τ) (κ ⊕ τ) R :=
  Matrix.fromBlocks A 0 0 D

def tangentBlock (v : Matrix κ τ R) : Matrix (κ ⊕ τ) (κ ⊕ τ) R :=
  Matrix.fromBlocks 0 v (-v.conjTranspose) 0

def commutator {α : Type*} [Fintype α] (A B : Matrix α α R) : Matrix α α R :=
  A * B - B * A

omit [Fintype κ] [Fintype τ] in
theorem tangentBlock_injective : Function.Injective (tangentBlock (κ := κ) (τ := τ) (R := R)) := by
  intro v w h
  exact congrArg Matrix.toBlocks₁₂ h

omit [Fintype κ] [Fintype τ] in
theorem tangentBlock_skew (v : Matrix κ τ R) :
    (tangentBlock v).conjTranspose = -tangentBlock v := by
  simp [tangentBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]

omit [Fintype κ] [Fintype τ] in
theorem diagonalBlock_skew (A : Matrix κ κ R) (D : Matrix τ τ R)
    (hA : A.conjTranspose = -A) (hD : D.conjTranspose = -D) :
    (diagonalBlock A D).conjTranspose = -diagonalBlock A D := by
  simp [diagonalBlock, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg, hA, hD]

omit [StarRing R] in
theorem commutator_diagonal (A B : Matrix κ κ R) (D E : Matrix τ τ R) :
    commutator (diagonalBlock A D) (diagonalBlock B E) =
      diagonalBlock (commutator A B) (commutator D E) := by
  simp [commutator, diagonalBlock, Matrix.fromBlocks_multiply, sub_eq_add_neg,
    Matrix.fromBlocks_neg, Matrix.fromBlocks_add]

theorem commutator_tangent (v w : Matrix κ τ R) :
    commutator (tangentBlock v) (tangentBlock w) =
      diagonalBlock (w * v.conjTranspose - v * w.conjTranspose)
        (w.conjTranspose * v - v.conjTranspose * w) := by
  simp only [commutator, tangentBlock, diagonalBlock, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul,
    sub_eq_add_neg, Matrix.fromBlocks_neg, neg_zero, neg_neg, Matrix.fromBlocks_add]
  congr 1 <;> abel

theorem commutator_diagonal_tangent (A : Matrix κ κ R) (D : Matrix τ τ R)
    (hA : A.conjTranspose = -A) (hD : D.conjTranspose = -D) (v : Matrix κ τ R) :
    commutator (diagonalBlock A D) (tangentBlock v) = tangentBlock (A * v - v * D) := by
  simp only [commutator, tangentBlock, diagonalBlock, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul,
    sub_eq_add_neg, Matrix.fromBlocks_neg, neg_zero, neg_neg, Matrix.fromBlocks_add,
    Matrix.conjTranspose_add, Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, hA, hD]
  congr 1
  abel

omit [Fintype κ] [Fintype τ] in
theorem skew_decomposition (M : Matrix (κ ⊕ τ) (κ ⊕ τ) R)
    (hM : M.conjTranspose = -M) :
    M = diagonalBlock M.toBlocks₁₁ M.toBlocks₂₂ + tangentBlock M.toBlocks₁₂ := by
  have he (i : τ) (j : κ) : M (Sum.inr i) (Sum.inl j) =
      -star (M (Sum.inl j) (Sum.inr i)) := by
    have h := congrFun (congrFun hM (Sum.inr i)) (Sum.inl j)
    change star (M (Sum.inl j) (Sum.inr i)) = -M (Sum.inr i) (Sum.inl j) at h
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  ext (i | i) (j | j) <;>
    simp [diagonalBlock, tangentBlock, Matrix.fromBlocks, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.conjTranspose, he]

omit [Fintype κ] [Fintype τ] in
theorem diagonal_blocks_skew (M : Matrix (κ ⊕ τ) (κ ⊕ τ) R)
    (hM : M.conjTranspose = -M) :
    M.toBlocks₁₁.conjTranspose = -M.toBlocks₁₁ ∧
      M.toBlocks₂₂.conjTranspose = -M.toBlocks₂₂ := by
  constructor
  · ext i j
    exact congrFun (congrFun hM (Sum.inl i)) (Sum.inl j)
  · ext i j
    exact congrFun (congrFun hM (Sum.inr i)) (Sum.inr j)

omit [Fintype κ] [Fintype τ] in
theorem tangentBlock_neg (v : Matrix κ τ R) : tangentBlock (-v) = -tangentBlock v := by
  simp [tangentBlock, Matrix.fromBlocks_neg]

/-- The compact symmetric-space curvature convention is minus the isotropy
action of the bracket of two tangent blocks. -/
def modelCurvature (v w z : Matrix κ τ R) : Matrix κ τ R :=
  -((w * v.conjTranspose - v * w.conjTranspose) * z -
    z * (w.conjTranspose * v - v.conjTranspose * w))

theorem modelCurvature_bracket (v w z : Matrix κ τ R) :
    tangentBlock (modelCurvature v w z) =
      -commutator (commutator (tangentBlock v) (tangentBlock w)) (tangentBlock z) := by
  have hA : (w * v.conjTranspose - v * w.conjTranspose).conjTranspose =
      -(w * v.conjTranspose - v * w.conjTranspose) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    abel
  have hD : (w.conjTranspose * v - v.conjTranspose * w).conjTranspose =
      -(w.conjTranspose * v - v.conjTranspose * w) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    abel
  rw [commutator_tangent, commutator_diagonal_tangent _ _ hA hD, modelCurvature,
    tangentBlock_neg]

theorem modelCurvature_antisymm (v w z : Matrix κ τ R) :
    modelCurvature v w z = -modelCurvature w v z := by
  simp only [modelCurvature, Matrix.sub_mul, Matrix.mul_sub]
  abel

theorem modelCurvature_bianchi (v w z : Matrix κ τ R) :
    modelCurvature v w z + modelCurvature w z v + modelCurvature z v w = 0 := by
  simp only [modelCurvature, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

end QuaternionicSymmetry.CompactSymmetricPair
