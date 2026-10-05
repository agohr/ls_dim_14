import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A basis-induced norm on an abstract finite-dimensional complex module.
The same finite basis is used for the additive norm and scalar structure. -/

namespace QuaternionicSymmetry.FiniteDimensionalComplexModuleNorm

noncomputable section

variable (V : Type*) [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

private def coordEquiv : V ≃ₗ[ℂ]
    (Fin (Module.finrank ℂ V) → ℂ) :=
  (Module.finBasis ℂ V).equivFun

def normedAddCommGroup : NormedAddCommGroup V :=
  NormedAddCommGroup.induced V
    (Fin (Module.finrank ℂ V) → ℂ)
    (coordEquiv V).toAddMonoidHom (coordEquiv V).injective

def normedSpace :
    letI := normedAddCommGroup V
    NormedSpace ℂ V := by
  letI := normedAddCommGroup V
  exact NormedSpace.induced ℂ V
    (Fin (Module.finrank ℂ V) → ℂ) (coordEquiv V).toLinearMap

end
end QuaternionicSymmetry.FiniteDimensionalComplexModuleNorm
