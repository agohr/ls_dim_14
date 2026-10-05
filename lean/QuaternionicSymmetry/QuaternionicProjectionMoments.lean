import QuaternionicSymmetry.UnitaryProjectionMoments
import QuaternionicSymmetry.QuaternionicGaussianTraceMoments

/-! Haar averages of genuine unitary projections satisfy the quaternionic
moment sign. This proves the sign of the actual orbital moments, before
their explicit trace-polynomial evaluation. -/

namespace QuaternionicSymmetry.QuaternionicProjectionMoments

open Module QuaternionicFundamental QuaternionicTracePositivity
open QuaternionicGaussianTraceMoments MeasureTheory

noncomputable section

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem moment_mixed_in_positive_ray (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (s : Finset κ) (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (UnitaryProjectionMoments.moment s (curvatureSquare B η) k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) := by
  apply UnitaryProjectionMoments.moment_mul_contains (embed_topForm_ne_zero Q c)
  intro U
  exact QuaternionicTracePositivity.traceY_mixed_mem_positiveRay Q c
    (UnitaryProjection.projection s U) B
    (UnitaryProjection.projection_posSemidef s U) hB η hη k hk

omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem mixed_integrable (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (s : Finset κ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (k : ℕ) (L : CE V →ₗ[ℝ] ℝ) :
    Integrable (fun U : Matrix.unitaryGroup κ ℂ =>
      L (traceY (UnitaryProjection.projection s U) B η ^ k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)))
        UnitaryHaarMeasure.probability := by
  exact UnitaryProjectionMoments.scalar_mixed_integrable s (curvatureSquare B η) k
    (embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) L

omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem integral_mixed (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (s : Finset κ) (B : β → Matrix κ κ ℂ) (η : β → E V)
    (k : ℕ) (L : CE V →ₗ[ℝ] ℝ) :
    (∫ U : Matrix.unitaryGroup κ ℂ,
      L (traceY (UnitaryProjection.projection s U) B η ^ k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k))
        ∂UnitaryHaarMeasure.probability) =
      L (UnitaryProjectionMoments.moment s (curvatureSquare B η) k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) := by
  exact UnitaryProjectionMoments.integral_scalar_mixed s (curvatureSquare B η) k
    (embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) L

theorem integral_mixed_nonneg (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (s : Finset κ) (B : β → Matrix κ κ ℂ) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension)
    (L : CE V →ₗ[ℝ] ℝ) (hL : 0 ≤ L (embed (V := V) (topForm Q c))) :
    0 ≤ ∫ U : Matrix.unitaryGroup κ ℂ,
      L (traceY (UnitaryProjection.projection s U) B η ^ k *
        embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k))
        ∂UnitaryHaarMeasure.probability := by
  rw [integral_mixed]
  exact PositiveRay.functional_nonneg
    (moment_mixed_in_positive_ray Q c s B hB η hη k hk) L hL

end
end QuaternionicSymmetry.QuaternionicProjectionMoments
