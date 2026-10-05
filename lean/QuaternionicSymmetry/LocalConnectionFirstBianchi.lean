import QuaternionicSymmetry.LocalConnectionBianchi

/-! The algebraic first Bianchi identity for a torsion-free connection in
coordinate gauge.  It follows from symmetry of the Christoffel operator
and its actual derivative. -/
namespace QuaternionicSymmetry.LocalConnectionFirstBianchi
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionBianchi
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance

private theorem fderiv_eval_pair {Γ : E → E →L[ℝ] (E →L[ℝ] E)}
    {x : E} (hΓ : DifferentiableAt ℝ Γ x) (u v w : E) :
    fderiv ℝ (fun z => Γ z v w) x u = fderiv ℝ Γ x u v w := by
  rw [fderiv_eval_const (hΓ.clm_apply (differentiableAt_const _)) w u,
    fderiv_eval_const hΓ v u]

theorem first_bianchi (Γ : E → E →L[ℝ] (E →L[ℝ] E)) (x : E)
    (hΓ : DifferentiableAt ℝ Γ x)
    (hsym : ∀ u v, (fun z => Γ z u v) =ᶠ[𝓝 x] fun z => Γ z v u)
    (u v w : E) :
    curvature Γ x u v w + curvature Γ x v w u +
      curvature Γ x w u v = 0 := by
  have hds (a b c : E) :
      fderiv ℝ Γ x a b c = fderiv ℝ Γ x a c b := by
    have h := (hsym b c).fderiv_eq (𝕜 := ℝ)
    simpa only [fderiv_eval_pair hΓ] using
      congrArg (fun L : E →L[ℝ] E => L a) h
  have hs (a b : E) : Γ x a b = Γ x b a := (hsym a b).self_of_nhds
  have hcomp (A B : E →L[ℝ] E) (z : E) : (A * B) z = A (B z) := rfl
  simp only [curvature_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, hcomp]
  rw [hds u v w, hds v w u, hds w u v]
  rw [hs v w, hs w u, hs u v]
  abel

end
end QuaternionicSymmetry.LocalConnectionFirstBianchi
