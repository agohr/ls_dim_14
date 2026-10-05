import QuaternionicSymmetry.ComplexTorusLaurentComultiplication
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! The literal double-Laurent coordinate algebra is the genuine tensor
product of two copies of the algebraic complex torus coordinate algebra. -/

namespace QuaternionicSymmetry.ComplexTorusDoubleCoordinateTensor

open ComplexProjectiveDiagonalAlgebraicCharts
open ComplexTorusLaurentComultiplication
open scoped TensorProduct
noncomputable section

variable {r : ℕ}

def doubleTorusTensorEquiv :
    DoubleTorusCoordinateRing r ≃ₐ[ℂ]
      TorusCoordinateRing r ⊗[ℂ] TorusCoordinateRing r :=
  (AddMonoidAlgebra.curryAlgEquiv ℂ).trans
    ((AddMonoidAlgebra.scalarTensorEquiv (M := Fin r → ℤ)
      ℂ (TorusCoordinateRing r)).symm.restrictScalars ℂ) |>.trans
        (Algebra.TensorProduct.comm ℂ (TorusCoordinateRing r) (TorusCoordinateRing r))

@[simp] theorem doubleTorusTensorEquiv_single
    (μ ν : Fin r → ℤ) :
    doubleTorusTensorEquiv
      (AddMonoidAlgebra.single (μ, ν) (1 : ℂ)) =
    (laurentMonomial μ) ⊗ₜ[ℂ] (laurentMonomial ν) := by
  simp [doubleTorusTensorEquiv, laurentMonomial,
    AddMonoidAlgebra.curryAlgEquiv_single,
    AddMonoidAlgebra.scalarTensorEquiv_symm_single]

end
end QuaternionicSymmetry.ComplexTorusDoubleCoordinateTensor
