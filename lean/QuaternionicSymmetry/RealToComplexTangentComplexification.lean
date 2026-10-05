import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Complex.Basic

/-! The literal complex-linear extension of a real-linear tangent map.
For a compact-real-form inclusion, bijectivity of this map is the
infinitesimal complexification property, not a mere dimension marker. -/

namespace QuaternionicSymmetry.RealToComplexTangentComplexification

open scoped TensorProduct
noncomputable section

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℂ W]

def complexifiedMap (f : V →ₗ[ℝ] W) : (ℂ ⊗[ℝ] V) →ₗ[ℝ] W :=
  TensorProduct.lift <| LinearMap.mk₂ ℝ (fun z v => z • f v)
    (by intro a a' v; simp [add_smul])
    (by intro c a v; exact smul_assoc c a (f v))
    (by intro a v v'; simp [map_add, smul_add])
    (by
      intro c a v
      change a • f (c • v) = c • (a • f v)
      rw [map_smul]
      exact smul_comm a c (f v))

@[simp] theorem complexifiedMap_tmul (f : V →ₗ[ℝ] W) (z : ℂ) (v : V) :
    complexifiedMap f (z ⊗ₜ[ℝ] v) = z • f v := rfl

theorem complexifiedMap_one_tmul (f : V →ₗ[ℝ] W) (v : V) :
    complexifiedMap f ((1 : ℂ) ⊗ₜ[ℝ] v) = f v := by simp

/-- A concrete infinitesimal criterion: the complexification of the given
real tangent map covers the whole complex tangent space bijectively. -/
def IsInfinitesimalComplexification (f : V →ₗ[ℝ] W) : Prop :=
  Function.Bijective (complexifiedMap f)

end
end QuaternionicSymmetry.RealToComplexTangentComplexification
