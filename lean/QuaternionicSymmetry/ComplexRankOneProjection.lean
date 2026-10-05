import QuaternionicSymmetry.ComplexGaussianRankOne
import Mathlib.Analysis.Matrix.Order

/-! Normalized rank-one projections in the finite coordinate space.  These are
pure matrix identities and carry no probabilistic interpretation. -/

namespace QuaternionicSymmetry.ComplexRankOneProjection

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

noncomputable section

variable {κ : Type*} [Fintype κ]

def squaredNorm (v : κ → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def projection (v : κ → ℂ) : Matrix κ κ ℂ :=
  (squaredNorm v)⁻¹ • ComplexGaussianRankOne.rankOne v

theorem squaredNorm_nonneg (v : κ → ℂ) : 0 ≤ squaredNorm v := by
  unfold squaredNorm
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem squaredNorm_pos {v : κ → ℂ} (hv : v ≠ 0) : 0 < squaredNorm v := by
  unfold squaredNorm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  apply Finset.sum_pos' (fun j _ => sq_nonneg _)
  exact ⟨i, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr hi)⟩

theorem rankOne_sq (v : κ → ℂ) :
    ComplexGaussianRankOne.rankOne v * ComplexGaussianRankOne.rankOne v =
      (squaredNorm v) • ComplexGaussianRankOne.rankOne v := by
  have hsum : ∑ k, v k * star (v k) = (squaredNorm v : ℂ) := by
    simp [squaredNorm, Complex.mul_conj, ← Complex.sq_norm]
  ext i j
  simp only [Matrix.mul_apply, ComplexGaussianRankOne.rankOne_apply,
    Matrix.smul_apply]
  calc
    (∑ k, (v i * star (v k)) * (v k * star (v j))) =
        ∑ k, v i * (v k * star (v k)) * star (v j) := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = v i * (∑ k, v k * star (v k)) * star (v j) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ = (squaredNorm v) • (v i * star (v j)) := by
      rw [hsum]
      change v i * (squaredNorm v : ℂ) * star (v j) =
        (squaredNorm v : ℂ) * (v i * star (v j))
      ring

theorem projection_posSemidef (v : κ → ℂ) :
    (projection v).PosSemidef := by
  unfold projection
  exact Matrix.PosSemidef.smul
    (ComplexGaussianRankOne.rankOne_posSemidef v)
    (inv_nonneg.mpr (squaredNorm_nonneg v))

theorem projection_isHermitian (v : κ → ℂ) :
    (projection v).IsHermitian :=
  (projection_posSemidef v).isHermitian

theorem projection_sq {v : κ → ℂ} (hv : v ≠ 0) :
    projection v * projection v = projection v := by
  let q : ℝ := (squaredNorm v)⁻¹
  have hq : q * squaredNorm v = 1 := by
    dsimp [q]
    exact inv_mul_cancel₀ (ne_of_gt (squaredNorm_pos hv))
  calc
    projection v * projection v = (q • ComplexGaussianRankOne.rankOne v) *
        (q • ComplexGaussianRankOne.rankOne v) := by rfl
    _ = q • (q • (ComplexGaussianRankOne.rankOne v *
        ComplexGaussianRankOne.rankOne v)) := by
      rw [Matrix.smul_mul, Matrix.mul_smul]
    _ = q • (q • ((squaredNorm v) • ComplexGaussianRankOne.rankOne v)) := by
      rw [rankOne_sq]
    _ = projection v := by
      simp only [projection, q, smul_smul]
      rw [inv_mul_cancel₀ (ne_of_gt (squaredNorm_pos hv))]
      simp

theorem trace_rankOne (v : κ → ℂ) :
    Matrix.trace (ComplexGaussianRankOne.rankOne v) = (squaredNorm v : ℂ) := by
  rw [ComplexGaussianRankOne.rankOne, Matrix.trace_vecMulVec]
  change (∑ k, v k * star (v k)) = (squaredNorm v : ℂ)
  simp [squaredNorm, Complex.mul_conj, ← Complex.sq_norm]

theorem trace_projection {v : κ → ℂ} (hv : v ≠ 0) :
    Matrix.trace (projection v) = 1 := by
  have hpos := squaredNorm_pos hv
  have htrace (r : ℝ) (A : Matrix κ κ ℂ) :
      Matrix.trace (r • A) = (r : ℂ) * Matrix.trace A := by
    simp [Matrix.trace, Matrix.smul_apply, Finset.mul_sum]
  rw [projection, htrace, trace_rankOne, ← Complex.ofReal_mul]
  simp [inv_mul_cancel₀ (ne_of_gt hpos)]

end
end QuaternionicSymmetry.ComplexRankOneProjection
