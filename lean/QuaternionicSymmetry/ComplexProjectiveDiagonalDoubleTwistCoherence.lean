import QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistIdeal

/-! Strict two-parameter polynomial coaction coherence: applying the
regular diagonal family in either parameter order gives the same literal
Laurent polynomial homomorphism, before passing to quotient rings. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistCoherence

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexProjectiveDiagonalRegularFamily
open ComplexProjectiveDiagonalDoubleBaseChange
open ComplexProjectiveDiagonalDoubleTwistPolynomial
open ComplexTorusLaurentComultiplication
noncomputable section

variable {r d : ℕ}

theorem firstTwist_comp_family_eq_secondTwist_comp_family
    (μ : Fin (d + 1) → Fin r → ℤ) :
    (firstTwist μ).comp (familySubstitution μ) =
      (secondTwist μ).comp (familySubstitution μ) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [firstTwist, secondTwist, familySubstitution,
      firstParameter, secondParameter]
  · intro i
    simp [firstTwist, secondTwist, familySubstitution,
      firstParameter_monomial, secondParameter_monomial,
      ← mul_assoc]
    simp [AddMonoidAlgebra.single_mul_single,
      mul_comm, mul_left_comm, mul_assoc]

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalDoubleTwistCoherence
