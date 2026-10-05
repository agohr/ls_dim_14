import QuaternionicSymmetry.LocalConnectionBianchi

/-! The second Bianchi identity for the full Riemann tensor of a torsion-free
coordinate connection. The two input-slot corrections cancel cyclically. -/
namespace QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionBianchi
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance

/-- Covariant derivative of the actual four-slot Riemann tensor, using the
coordinate Christoffel operator for every slot. The output and last input
corrections are already included in `covariantCurvatureDerivative`. -/
def covariantRiemannDerivative (Γ : Form (E := E) (A := E →L[ℝ] E))
    (x u v w z : E) : E :=
  covariantCurvatureDerivative Γ x u v w z -
    curvature Γ x (Γ x u v) w z - curvature Γ x v (Γ x u w) z

/-- The differential second Bianchi identity for a torsion-free connection.
The premise is pointwise Christoffel symmetry and actual `C²` regularity. -/
theorem second_bianchi (Γ : Form (E := E) (A := E →L[ℝ] E)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x)
    (hsym : ∀ u v : E, Γ x u v = Γ x v u)
    (u v w z : E) :
    covariantRiemannDerivative Γ x u v w z +
      covariantRiemannDerivative Γ x v w u z +
        covariantRiemannDerivative Γ x w u v z = 0 := by
  have hb := congrArg (fun A : E →L[ℝ] E => A z) (bianchi Γ x hΓ u v w)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply] at hb
  simp only [covariantRiemannDerivative]
  rw [hsym u v, hsym v w, hsym w u]
  rw [curvature_antisymm Γ x (Γ x v u) w,
    curvature_antisymm Γ x (Γ x w v) u,
    curvature_antisymm Γ x (Γ x u w) v]
  simp only [ContinuousLinearMap.neg_apply] at *
  convert hb using 1; abel

end
end QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
