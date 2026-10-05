import QuaternionicSymmetry.ContinuousWedge
import QuaternionicSymmetry.LocalChernWeilCubicForm
import QuaternionicSymmetry.LocalChernWeilQuadraticTransgression

/-! The existing quadratic and cubic normalized products are instances of the
all-degree bounded wedge.  These equalities preserve their established APIs. -/

namespace QuaternionicSymmetry.ContinuousWedgeInstances

open QuaternionicSymmetry.ContinuousWedge
  QuaternionicSymmetry.LocalChernWeilQuadratic
  QuaternionicSymmetry.LocalChernWeilCubicForm
  QuaternionicSymmetry.LocalChernWeilQuadraticTransgression

noncomputable section

variable {E A B C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

theorem wedge22_eq (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 2]→L[ℝ] B) :
    wedge22 P α β = wedge P α β := by
  rfl

theorem wedge24_eq (P : A →L[ℝ] B →L[ℝ] C)
    (α : E [⋀^Fin 2]→L[ℝ] A) (β : E [⋀^Fin 4]→L[ℝ] B) :
    wedge24 P α β = wedge P α β := by
  rfl

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

local instance : NormedSpace ℝ R := NormedAlgebra.toNormedSpace R

theorem wedge12_eq (P : R →L[ℝ] R →L[ℝ] C)
    (α : E [⋀^Fin 1]→L[ℝ] R) (β : E [⋀^Fin 2]→L[ℝ] R) :
    wedge12 P α β = wedge P α β := by
  rfl

end
end QuaternionicSymmetry.ContinuousWedgeInstances
