import QuaternionicSymmetry.ComplexTorusCharacterIndependent

/-! The family of all complex-torus evaluations separates literal Laurent
polynomials. This is stronger than compact-to-complex vanishing transfer:
it extracts each Laurent coefficient. -/

namespace QuaternionicSymmetry.ComplexTorusLaurentEvaluationInjective

open ComplexTorusCharacterIndependent
open ComplexProjectiveDiagonalAlgebraicCharts
open TorusLaurentRepresentation
noncomputable section

variable {r : ℕ}

theorem evalTorus_eq_sum (f : TorusCoordinateRing r) (z : ComplexTorus r) :
    evalTorus z f =
      ∑ μ ∈ f.support, f μ * (complexWeightCharacter μ z : ℂ) := by
  classical
  calc
    evalTorus z f = evalTorus z (f.sum AddMonoidAlgebra.single) := by
      rw [AddMonoidAlgebra.sum_single]
    _ = ∑ μ ∈ f.support,
        evalTorus z (AddMonoidAlgebra.single μ (f μ)) := by
      simp [Finsupp.sum]
    _ = ∑ μ ∈ f.support, f μ *
        (complexWeightCharacter μ z : ℂ) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      simp [evalTorus, exponentCharacter]

theorem evalTorus_joint_injective (f : TorusCoordinateRing r)
    (h : ∀ z : ComplexTorus r, evalTorus z f = 0) : f = 0 := by
  classical
  ext μ
  by_cases hμ : μ ∈ f.support
  · have hc := coefficient_zero_of_laurent_sum f.support (fun ν => f ν)
      (by intro z; rw [← evalTorus_eq_sum]; exact h z) μ hμ
    simpa using hc
  · exact Finsupp.notMem_support_iff.mp hμ

end
end QuaternionicSymmetry.ComplexTorusLaurentEvaluationInjective
