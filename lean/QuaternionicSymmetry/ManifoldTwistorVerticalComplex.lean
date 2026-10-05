import QuaternionicSymmetry.ManifoldTwistorSphereHomeomorph
import Mathlib.LinearAlgebra.CrossProduct
/-! Algebraic complex rotation on the vertical tangent plane of a unit
quaternionic coefficient. The actual sphere tangent identification is supplied
by Mathlib’s `range_mfderiv_coe_sphere`. -/

namespace QuaternionicSymmetry.ManifoldTwistorVerticalComplex
open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open scoped Matrix
noncomputable section

def VerticalVector (a : coefficientSphere) (v : Fin 3 → ℝ) : Prop := a.1 ⬝ᵥ v = 0

theorem dot_self (a : coefficientSphere) : a.1 ⬝ᵥ a.1 = 1 := by
  simpa [squareNorm, dotProduct] using a.2

theorem cross_vertical (a : coefficientSphere) (v : Fin 3 → ℝ) :
    VerticalVector a (a.1 ⨯₃ v) := by
  exact dot_self_cross _ _

theorem cross_sq (a : coefficientSphere) (v : Fin 3 → ℝ)
    (hv : VerticalVector a v) : a.1 ⨯₃ (a.1 ⨯₃ v) = -v := by
  rw [cross_cross_eq_smul_sub_smul']
  simp [VerticalVector] at hv
  rw [hv, dot_self]
  simp
theorem cross_dot_self (a : coefficientSphere) (v : Fin 3 → ℝ)
    (hv : VerticalVector a v) :
    (a.1 ⨯₃ v) ⬝ᵥ (a.1 ⨯₃ v) = v ⬝ᵥ v := by
  rw [cross_dot_cross]
  simp [VerticalVector] at hv
  rw [dot_self, hv]
  ring

/-- The actual tangent plane to the coefficient unit sphere at a unit vector. -/
def verticalSubmodule (a : coefficientSphere) : Submodule ℝ (Fin 3 → ℝ) where
  carrier := {v | VerticalVector a v}
  zero_mem' := by simp [VerticalVector]
  add_mem' := by
    intro u v hu hv
    change a.1 ⬝ᵥ u = 0 at hu
    change a.1 ⬝ᵥ v = 0 at hv
    change a.1 ⬝ᵥ (u + v) = 0
    rw [dotProduct_add, hu, hv, add_zero]
  smul_mem' := by
    intro r v hv
    change a.1 ⬝ᵥ v = 0 at hv
    change a.1 ⬝ᵥ r • v = 0
    rw [dotProduct_smul, hv]
    simp

/-- Rotation by the selected quaternionic unit on the vertical tangent plane. -/
def verticalComplex (a : coefficientSphere) :
    verticalSubmodule a →ₗ[ℝ] verticalSubmodule a where
  toFun v := ⟨a.1 ⨯₃ v.1, cross_vertical a v.1⟩
  map_add' u v := by
    apply Subtype.ext
    exact (crossProduct a.1).map_add u.1 v.1
  map_smul' r v := by
    apply Subtype.ext
    exact (crossProduct a.1).map_smul r v.1

theorem verticalComplex_sq (a : coefficientSphere) (v : verticalSubmodule a) :
    verticalComplex a (verticalComplex a v) = -v := by
  apply Subtype.ext
  exact cross_sq a v.1 v.2

end
end QuaternionicSymmetry.ManifoldTwistorVerticalComplex
