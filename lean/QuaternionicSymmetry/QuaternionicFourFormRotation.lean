import QuaternionicSymmetry.ManifoldQuaternionicMetric
import QuaternionicSymmetry.ContinuousWedge
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Orthogonal rotation invariance of the sum of three Kähler squares. -/

namespace QuaternionicSymmetry.QuaternionicFourFormRotation

open Matrix

private theorem sum_sq_mulVec {A : Type*} [CommRing A]
    (R : Matrix (Fin 3) (Fin 3) A) (hR : Rᵀ * R = 1)
    (ω : Fin 3 → A) :
    ∑ i : Fin 3, ((R *ᵥ ω) i) ^ 2 = ∑ i : Fin 3, (ω i) ^ 2 := by
  have h : (R *ᵥ ω) ⬝ᵥ (R *ᵥ ω) = ω ⬝ᵥ ω := by
    calc
      (R *ᵥ ω) ⬝ᵥ (R *ᵥ ω) = ω ⬝ᵥ (Rᵀ *ᵥ (R *ᵥ ω)) := by
        simpa only [vecMul_transpose] using
          (dotProduct_mulVec ω Rᵀ (R *ᵥ ω)).symm
      _ = ω ⬝ᵥ ((Rᵀ * R) *ᵥ ω) := by rw [mulVec_mulVec]
      _ = ω ⬝ᵥ ω := by simp [hR]
  simpa [dotProduct, pow_two] using h

theorem sum_sq_rotate {A : Type*} [CommRing A] [Algebra ℝ A]
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1)
    (ω : Fin 3 → A) :
    ∑ i : Fin 3, (∑ j : Fin 3, R i j • ω j) ^ 2 =
      ∑ i : Fin 3, ω i ^ 2 := by
  let S : Matrix (Fin 3) (Fin 3) A := R.map (algebraMap ℝ A)
  have hS : Sᵀ * S = 1 := by
    change (Rᵀ).map (algebraMap ℝ A) * R.map (algebraMap ℝ A) = 1
    rw [← Matrix.map_mul, hR]
    simp
  have hω : S *ᵥ ω = fun i => ∑ j : Fin 3, R i j • ω j := by
    funext i
    simp [S, Matrix.mulVec, dotProduct, Algebra.smul_def]
  change (∑ i : Fin 3, ((fun i => ∑ j : Fin 3, R i j • ω j) i) ^ 2) = _
  rw [← hω]
  exact sum_sq_mulVec S hS ω

/-- Rotation invariance for any real bilinear pairing, including wedge.
Symmetry of the pairing is not needed. -/
theorem sum_bilinear_rotate {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1)
    (ω : Fin 3 → V) :
    ∑ i : Fin 3, B (∑ j : Fin 3, R i j • ω j)
      (∑ j : Fin 3, R i j • ω j) =
        ∑ j : Fin 3, B (ω j) (ω j) := by
  calc
    _ = ∑ j : Fin 3, ∑ k : Fin 3,
        (∑ i : Fin 3, R i j * R i k) • B (ω j) (ω k) := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        ext j
        rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_comm]
    _ = ∑ j : Fin 3, B (ω j) (ω j) := by
      have horth (j k : Fin 3) :
          (∑ i : Fin 3, R i j * R i k) = if j = k then 1 else 0 := by
        have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M j k) hR
        simpa [Matrix.mul_apply, Matrix.transpose_apply] using h
      simp_rw [horth]
      simp

/-- Rotation invariance of the actual normalized sum of wedge squares of
three continuous alternating two-forms. -/
theorem sum_wedge_square_rotate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1)
    (ω : Fin 3 → E [⋀^Fin 2]→L[ℝ] ℝ) :
    ∑ i : Fin 3,
      QuaternionicSymmetry.ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (∑ j : Fin 3, R i j • ω j) (∑ j : Fin 3, R i j • ω j) =
    ∑ j : Fin 3,
      QuaternionicSymmetry.ContinuousWedge.wedge (ContinuousLinearMap.mul ℝ ℝ)
        (ω j) (ω j) := by
  exact sum_bilinear_rotate
    (QuaternionicSymmetry.ContinuousWedge.wedgeLinear
      (E := E) (p := 2) (q := 2) (ContinuousLinearMap.mul ℝ ℝ))
    R hR ω

end QuaternionicSymmetry.QuaternionicFourFormRotation
