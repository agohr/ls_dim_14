import QuaternionicSymmetry.QuaternionicUniversalEvenTrace
import QuaternionicSymmetry.EvenForms
import QuaternionicSymmetry.ExteriorContinuousPairing

/-! The universal quaternionic trace identity instantiated in the proved
commutative algebra of even exterior forms. Its inputs are actual homogeneous
two-forms on a finite-dimensional real vector space. -/
namespace QuaternionicSymmetry.QuaternionicExteriorEvenTrace
open QuaternionicUniversalEvenTrace EvenForms ExteriorContinuousPairing
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

abbrev EvenAlgebra (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] :=
  evenSubalgebra ℝ (Module.Dual ℝ V)

def liftTwo (ω : Fin 3 → Power V 2) : Fin 3 → EvenAlgebra V :=
  fun i => ofTwoForm (ω i)

omit [FiniteDimensional ℝ V] in
/-- The four-dimensional line and three-dimensional adjoint curvature
representations have the exact all-degree trace ratio inside the even
exterior algebra. -/
theorem exterior_line_adjoint_even_trace (ω : Fin 3 → Power V 2)
    (j : ℕ) (hj : 0 < j) :
    (4 : EvenAlgebra V) ^ j *
      Matrix.trace (lineMatrix (liftTwo ω) ^ (2 * j)) =
      2 * Matrix.trace (adjointMatrix (liftTwo ω) ^ (2 * j)) :=
  line_adjoint_even_trace (liftTwo ω) j hj

end
end QuaternionicSymmetry.QuaternionicExteriorEvenTrace
