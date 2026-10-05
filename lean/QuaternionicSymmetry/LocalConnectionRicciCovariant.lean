import QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
import QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
import QuaternionicSymmetry.LocalEndomorphismTrace

/-! Trace contraction of the full covariant curvature derivative. -/
namespace QuaternionicSymmetry.LocalConnectionRicciCovariant
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionBianchi
open QuaternionicSymmetry.LocalConnectionRiemannSecondBianchi
open QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
open QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance

def covariantRicciOperator (Γ : Form (E := E) (A := E →L[ℝ] E))
    (x a v w : E) : E →L[ℝ] E :=
  ricciExtraction v w (fderiv ℝ (curvature Γ) x a) +
    Γ x a * ricciOperator Γ x v w -
      ricciOperator Γ x v w * Γ x a -
        ricciOperator Γ x (Γ x a v) w -
          ricciOperator Γ x v (Γ x a w)

omit [FiniteDimensional ℝ E] in
theorem covariantRicciOperator_apply
    (Γ : Form (E := E) (A := E →L[ℝ] E))
    (x a u v w : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    covariantRicciOperator Γ x a v w u =
      covariantRiemannDerivative Γ x a u v w := by
  have hR := LocalConnectionCurvatureSmooth.curvature_differentiableAt Γ x hΓ
  have hD : fderiv ℝ (fun y => curvature Γ y u v) x a w =
      fderiv ℝ (curvature Γ) x a u v w := by
    rw [fderiv_eval_const (hR.clm_apply (differentiableAt_const _)) v a,
      fderiv_eval_const hR u a]
  simp only [covariantRicciOperator, covariantRiemannDerivative,
    covariantCurvatureDerivative, ricciOperator,
    ricciExtraction_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    hD]
  abel

theorem covariantRicci_trace
    (Γ : Form (E := E) (A := E →L[ℝ] E))
    (x a v w : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    realTraceCLM (covariantRicciOperator Γ x a v w) =
      fderiv ℝ (fun y => ricciTrace Γ y v w) x a -
        ricciTrace Γ x (Γ x a v) w -
          ricciTrace Γ x v (Γ x a w) := by
  rw [covariantRicciOperator]
  simp only [map_add, map_sub, ricciTrace_fderiv Γ x a v w hΓ]
  have hc : realTraceCLM (Γ x a * ricciOperator Γ x v w) =
      realTraceCLM (ricciOperator Γ x v w * Γ x a) := by
    simp only [realTraceCLM_apply]
    exact LinearMap.trace_mul_comm ℝ (Γ x a).toLinearMap
      (ricciOperator Γ x v w).toLinearMap
  simp only [hc, ricciTrace]
  abel

end
end QuaternionicSymmetry.LocalConnectionRicciCovariant
