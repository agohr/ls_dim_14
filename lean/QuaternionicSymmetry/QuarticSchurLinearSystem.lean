import QuaternionicSymmetry.QuarticOrbitalEleven

/-! The five-by-five Schur system printed in Chapter 6, with the target and
solution kept as exact rational vectors. The matrix columns are the actual
Jacobi--Trudi evaluations from `QuarticOrbitalEleven`. -/

namespace QuaternionicSymmetry.QuarticSchurLinearSystem

open QuarticOrbitalEleven
open scoped BigOperators

noncomputable section

def spectrum : Fin 5 → List ℕ := ![a₁, a₂, a₃, a₄, a₅]

def S (i j : Fin 5) : ℚ := schurValues (spectrum j) i

def c : Fin 5 → ℚ := ![c₁, c₂, c₃, c₄, c₅]

def target : Fin 5 → ℚ :=
  ![42071692, 33230860, 304682840 / 27, 23056120 / 3, 1664096 / 3]

/-- The displayed rational orbital coefficients solve `S c = target`. -/
theorem linear_system (i : Fin 5) :
    (∑ j : Fin 5, S i j * c j) = target i := by
  fin_cases i <;>
    norm_num [S, spectrum, c, target, Fin.sum_univ_succ,
      schurValues_a₁, schurValues_a₂, schurValues_a₃,
      schurValues_a₄, schurValues_a₅, c₁, c₂, c₃, c₄, c₅]

end
end QuaternionicSymmetry.QuarticSchurLinearSystem
