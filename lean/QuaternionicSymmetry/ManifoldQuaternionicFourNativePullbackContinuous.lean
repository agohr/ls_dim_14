import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormOverlap
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-! Joint continuity of native alternating two-form pullback as both the form
and the tangent-frame transition vary. The proof uses Mathlib's actual strict
derivative of alternating-map pullback, not continuity declared by transport. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativePullbackContinuous

open scoped Topology
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance

theorem nativePullback_continuous :
    Continuous (fun p : (E [⋀^Fin 2]→L[ℝ] ℝ) × (E →L[ℝ] E) =>
      p.1.compContinuousLinearMap p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap p).continuousAt

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativePullbackContinuous
