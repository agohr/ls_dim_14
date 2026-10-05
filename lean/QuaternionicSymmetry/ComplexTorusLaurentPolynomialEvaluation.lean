import QuaternionicSymmetry.ComplexTorusLaurentPolynomialReconstruction
import QuaternionicSymmetry.ComplexTorusLaurentEvaluationInjective

/-! Evaluation of a Laurent coefficient at an ordinary complex point
equals taking that coefficient after polynomial evaluation. -/

namespace QuaternionicSymmetry.ComplexTorusLaurentPolynomialEvaluation

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexTorusLaurentPolynomialReconstruction
noncomputable section

variable {r : ℕ} {σ : Type*}

theorem eval_coefficient (ν : Fin r → ℤ)
    (p : MvPolynomial σ (TorusCoordinateRing r)) (v : σ → ℂ) :
    MvPolynomial.eval v (coefficient ν p) =
      (MvPolynomial.eval₂ (RingHom.id (TorusCoordinateRing r))
        (fun i => algebraMap ℂ (TorusCoordinateRing r) (v i)) p) ν := by
  classical
  simp only [coefficient, MvPolynomial.sum_def,
    MvPolynomial.eval_sum, MvPolynomial.eval_monomial,
    MvPolynomial.eval₂_eq]
  rw [Finset.sum_apply']
  apply Finset.sum_congr rfl
  intro m hm
  simp only [RingHom.id_apply]
  have hprod :
      (∏ i ∈ m.support,
        (algebraMap ℂ (TorusCoordinateRing r)) (v i) ^ m i) =
        algebraMap ℂ (TorusCoordinateRing r)
          (m.prod fun i e => v i ^ e) := by
    change (∏ i ∈ m.support,
        (algebraMap ℂ (TorusCoordinateRing r)) (v i) ^ m i) =
      algebraMap ℂ (TorusCoordinateRing r)
        (∏ i ∈ m.support, v i ^ m i)
    rw [map_prod]
    simp only [map_pow]
  rw [hprod]
  rw [mul_comm (MvPolynomial.coeff m p)]
  rw [← Algebra.smul_def]
  rw [AddMonoidAlgebra.coeff_smul]
  simp only [smul_eq_mul]
  ring

end
end QuaternionicSymmetry.ComplexTorusLaurentPolynomialEvaluation
