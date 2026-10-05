import QuaternionicSymmetry.ComplexProjectiveDiagonalAlgebraicCharts

/-! Every Laurent character is a genuine unit of the torus coordinate ring. -/

namespace QuaternionicSymmetry.ComplexProjectiveDiagonalLaurentUnits

open ComplexProjectiveDiagonalAlgebraicCharts
noncomputable section

variable {r : ℕ}

theorem laurentMonomial_mul_neg (ν : Fin r → ℤ) :
    laurentMonomial ν * laurentMonomial (-ν) = 1 := by
  simp [laurentMonomial, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.one_def]

theorem laurentMonomial_isUnit (ν : Fin r → ℤ) :
    IsUnit (laurentMonomial ν) :=
  isUnit_iff_exists_inv.mpr ⟨laurentMonomial (-ν), laurentMonomial_mul_neg ν⟩

end
end QuaternionicSymmetry.ComplexProjectiveDiagonalLaurentUnits
