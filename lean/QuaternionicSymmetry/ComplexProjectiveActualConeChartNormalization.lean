import QuaternionicSymmetry.ComplexProjectiveActualConeStandardOpenSurjective

/-! A nonzero homogeneous coordinate normalizes an arbitrary cone vector
to the exact affine chart vector used by dehomogenization. -/

namespace QuaternionicSymmetry.ComplexProjectiveActualConeChartNormalization

open ComplexProjectiveTopology
open ComplexProjectiveDiagonalVanishingIdeal
open ComplexProjectiveDiagonalChartLocus
open scoped LinearAlgebra.Projectivization
noncomputable section

variable {d : ℕ}

def normalizedCoordinates (i : Fin (d + 1))
    (v : Coord d) : Fin d → ℂ :=
  fun k => v (i.succAbove k) / v i

theorem homogeneousVector_normalizedCoordinates (i : Fin (d + 1))
    (v : Coord d) (hvi : v i ≠ 0) :
    homogeneousVector d i (normalizedCoordinates i v) =
      (v i)⁻¹ • v := by
  funext j
  refine Fin.succAboveCases i ?_ ?_ j
  · simp [homogeneousVector, hvi]
  · intro k
    simp [homogeneousVector, normalizedCoordinates, div_eq_mul_inv,
      mul_comm]

theorem euclideanPoint_normalizedCoordinates (i : Fin (d + 1))
    (v : Coord d) (hv : v ≠ 0) (hvi : v i ≠ 0) :
    euclideanPoint d i (normalizedCoordinates i v) =
      Projectivization.mk ℂ v hv := by
  unfold euclideanPoint
  rw [Projectivization.mk_eq_mk_iff' ℂ]
  refine ⟨(v i)⁻¹, ?_⟩
  exact (homogeneousVector_normalizedCoordinates i v hvi).symm

theorem normalizedCoordinates_mem_chartLocus (A : Set (Space d))
    (i : Fin (d + 1)) (v : Coord d) (hv : v ≠ 0)
    (hvi : v i ≠ 0)
    (hA : Projectivization.mk ℂ v hv ∈ A) :
    normalizedCoordinates i v ∈ chartLocus A i := by
  have hpt : euclideanPoint d i (normalizedCoordinates i v) ∈ A := by
    rwa [euclideanPoint_normalizedCoordinates i v hv hvi]
  simpa only [chartLocus, Set.mem_setOf_eq,
    projectiveChart_symm_apply] using hpt

end
end QuaternionicSymmetry.ComplexProjectiveActualConeChartNormalization
