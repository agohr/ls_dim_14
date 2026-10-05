import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveCoreTensorMFDeriv
import QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveManifold

/-! A checked real-linear, continuous identification of the actual
`Fin 1 → ℂ` projective-manifold tangent model with the scalar affine
coordinate used by the independent local AHS tensor. -/

namespace QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveScalarFiber

open scoped Quaternion

noncomputable section

def scalarFiberEquiv : (Fin 1 → ℂ) ≃L[ℝ] ℂ :=
  (LinearEquiv.funUnique (Fin 1) ℝ ℂ).toContinuousLinearEquiv

theorem scalarFiberEquiv_apply (w : Fin 1 → ℂ) :
    scalarFiberEquiv w = w 0 := rfl

theorem scalarFiberEquiv_symm_apply (z : ℂ) :
    scalarFiberEquiv.symm z = ![z] := by
  apply scalarFiberEquiv.injective
  simp [scalarFiberEquiv_apply]

def projectiveTangentModelEquiv :
    (ℍ × (Fin 1 → ℂ)) ≃L[ℝ] (ℍ × ℂ) :=
  ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℍ)
    scalarFiberEquiv

theorem projectiveTangentModelEquiv_apply (v : ℍ × (Fin 1 → ℂ)) :
    projectiveTangentModelEquiv v = (v.1, v.2 0) := rfl

end
end QuaternionicSymmetry.FourDimensionalHalfSpinProjectiveScalarFiber
