import QuaternionicSymmetry.ExteriorDuality
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Tactic

/-! Coordinate extensionality for actual exterior two-forms. -/

namespace QuaternionicSymmetry.ExteriorBasisCoordinates

open Module

noncomputable section

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- A two-form in the actual exterior algebra is determined by its values on
pairs of vectors from any finite basis. -/
theorem twoform_ext_basis (b : Basis ι ℝ V)
    {α γ : ExteriorAlgebra.exteriorPower ℝ 2 (Module.Dual ℝ V)}
    (h : ∀ i j, BilinearExterior.evaluate (b i) (b j) α =
      BilinearExterior.evaluate (b i) (b j) γ) :
    α = γ := by
  apply ExteriorDuality.twoform_ext b
  intro v w
  let pα : (ExteriorAlgebra.exteriorPower ℝ 2 V) →ₗ[ℝ] ℝ :=
    exteriorPower.pairingDual ℝ V 2 α
  let pγ : (ExteriorAlgebra.exteriorPower ℝ 2 V) →ₗ[ℝ] ℝ :=
    exteriorPower.pairingDual ℝ V 2 γ
  let fα : MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ :=
    (pα.compAlternatingMap (exteriorPower.ιMulti ℝ 2)).toMultilinearMap
  let fγ : MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ :=
    (pγ.compAlternatingMap (exteriorPower.ιMulti ℝ 2)).toMultilinearMap
  have hfg : fα = fγ := by
    apply Module.Basis.ext_multilinear (fun _ : Fin 2 => b)
    intro x
    have hx := h (x 0) (x 1)
    simpa [fα, fγ, pα, pγ, BilinearExterior.evaluate] using hx
  have hvw := congrArg (fun f : MultilinearMap ℝ (fun _ : Fin 2 => V) ℝ =>
      f ![v, w]) hfg
  simpa [fα, fγ, pα, pγ, BilinearExterior.evaluate] using hvw

end
end QuaternionicSymmetry.ExteriorBasisCoordinates
