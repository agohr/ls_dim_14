import QuaternionicSymmetry.FourDimensionalExteriorHodge
import Mathlib.LinearAlgebra.Alternating.Curry

/-! The canonical exterior pairing, curried as a bilinear form. This is a
preparatory source-free step toward a frame-independent pointwise Hodge
operator defined by quaternionic pullback. -/

namespace QuaternionicSymmetry.FourDimensionalExteriorEvaluationBilinear

open FourDimensionalExteriorHodge
noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private def oneAlternatingEquiv :
    (V →ₗ[ℝ] ℝ) ≃ (V [⋀^Fin 1]→ₗ[ℝ] ℝ) :=
  AlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1)

def bilinearOfTwoForm (α : TwoForm V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ where
  toFun v := (oneAlternatingEquiv (V := V)).symm
    (((exteriorPower.pairingDual ℝ V 2 α).compAlternatingMap
      (exteriorPower.ιMulti ℝ 2)).curryLeft v)
  map_add' v w := by
    apply (oneAlternatingEquiv (V := V)).injective
    simp [oneAlternatingEquiv]
    ext t
    rfl
  map_smul' c v := by
    apply (oneAlternatingEquiv (V := V)).injective
    simp [oneAlternatingEquiv]
    ext t
    rfl

theorem bilinearOfTwoForm_apply (α : TwoForm V) (v w : V) :
    bilinearOfTwoForm α v w = BilinearExterior.evaluate v w α := by
  simp [bilinearOfTwoForm, oneAlternatingEquiv,
    BilinearExterior.evaluate, AlternatingMap.curryLeft_apply_apply]
  congr 1

end
end QuaternionicSymmetry.FourDimensionalExteriorEvaluationBilinear
