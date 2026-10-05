import QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
import QuaternionicSymmetry.LocalConnectionCurvatureSmooth

/-! Ricci contraction is a continuous linear trace of the local curvature
bilinear map, so its derivative is the trace of the actual curvature
derivative. -/
namespace QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
open QuaternionicSymmetry.LocalConnection
open QuaternionicSymmetry.LocalConnectionCurvatureSmooth
open QuaternionicSymmetry.ContinuousLinearMapTraceDerivative
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedSpace ℝ E := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance : NormedAlgebra ℝ (E →L[ℝ] E) := inferInstance

/-- Evaluate a curvature bilinear map on its second and endomorphism
arguments, leaving the first curvature input free. -/
def ricciExtraction (v w : E) :
    Bilinear (E := E) (A := E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) E)
    (ContinuousLinearMap.apply ℝ E w)).comp
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] (E →L[ℝ] E)) (E →L[ℝ] E))
      (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) v))

omit [FiniteDimensional ℝ E] in
theorem ricciExtraction_apply (B : Bilinear (E := E) (A := E →L[ℝ] E))
    (v w z : E) : ricciExtraction v w B z = B z v w := rfl

def ricciOperator (Γ : Form (E := E) (A := E →L[ℝ] E))
    (x : E) (v w : E) : E →L[ℝ] E :=
  ricciExtraction v w (curvature Γ x)

def ricciTrace (Γ : Form (E := E) (A := E →L[ℝ] E))
    (x : E) (v w : E) : ℝ :=
  realTraceCLM (ricciOperator Γ x v w)

theorem ricciTrace_fderiv (Γ : Form (E := E) (A := E →L[ℝ] E))
    (x a v w : E) (hΓ : ContDiffAt ℝ 2 Γ x) :
    fderiv ℝ (fun y => ricciTrace Γ y v w) x a =
      realTraceCLM
        (ricciExtraction v w (fderiv ℝ (curvature Γ) x a)) := by
  have hR := curvature_differentiableAt Γ x hΓ
  let L : Bilinear (E := E) (A := E →L[ℝ] E) →L[ℝ] ℝ :=
    (realTraceCLM (V := E)).comp (ricciExtraction v w)
  have h : fderiv ℝ (fun y => L (curvature Γ y)) x =
      L.comp (fderiv ℝ (curvature Γ) x) := by
    simpa only [ContinuousLinearMap.fderiv] using
      (fderiv_comp' (𝕜 := ℝ) (f := curvature Γ) (g := L) x
        (L.differentiableAt) hR)
  have hA := congrArg (fun T : E →L[ℝ] ℝ => T a) h
  simpa only [ricciTrace, ricciOperator, L,
    Function.comp_def, ContinuousLinearMap.comp_apply] using hA

end
end QuaternionicSymmetry.LocalConnectionRicciTraceDerivative
