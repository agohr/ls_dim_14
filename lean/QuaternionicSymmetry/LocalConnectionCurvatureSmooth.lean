import QuaternionicSymmetry.LocalConnectionExterior

/-! Operator-valued differentiability of the actual local curvature
bilinear form. -/
namespace QuaternionicSymmetry.LocalConnectionCurvatureSmooth
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionExterior
open scoped Topology
noncomputable section
variable {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing A] [NormedAlgebra ℝ A]
local instance : NormedSpace ℝ A := NormedAlgebra.toNormedSpace A
local instance : NormedAddCommGroup (E →L[ℝ] A) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] A) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] A) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] A) := ContinuousLinearMap.toNormedSpace

theorem curvature_differentiableAt (Γ : Form (E := E) (A := A)) (x : E)
    (hΓ : ContDiffAt ℝ 2 Γ x) :
    DifferentiableAt ℝ (curvature Γ) x := by
  have hΓ₁ : DifferentiableAt ℝ Γ x := hΓ.differentiableAt (by norm_num)
  have hD : DifferentiableAt ℝ (fderiv ℝ Γ) x :=
    (hΓ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hP : DifferentiableAt ℝ (product Γ Γ) x :=
    differentiableAt_product Γ Γ x hΓ₁ hΓ₁
  have hflipD : DifferentiableAt ℝ
      (fun y => (fderiv ℝ Γ y).flip) x :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E A).toContinuousLinearEquiv.differentiableAt.comp x hD
  have hflipP : DifferentiableAt ℝ
      (fun y => (product Γ Γ y).flip) x :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E A).toContinuousLinearEquiv.differentiableAt.comp x hP
  exact (hD.sub hflipD).add (hP.sub hflipP)

end
end QuaternionicSymmetry.LocalConnectionCurvatureSmooth
