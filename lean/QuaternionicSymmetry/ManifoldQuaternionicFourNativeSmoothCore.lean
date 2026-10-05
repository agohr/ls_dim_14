import QuaternionicSymmetry.ManifoldQuaternionicFourNativeFiniteDimension
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeTwoFormCore
import QuaternionicSymmetry.ManifoldFiniteDimensionalCLMSmooth

/-! Smooth operator-valued transitions for the independently constructed
native tangent two-form bundle. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSmoothCore

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeTwoFormCore
open ManifoldQuaternionicFourNativePullbackSmooth
open ManifoldQuaternionicFourNativeFiniteDimension
open ManifoldFiniteDimensionalCLMSmooth
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : FiniteDimensional ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  native_finiteDimensional

def nativeCoordChangeCLM (i j : atlas E M) (x : M) :
    NativeTwoForm (E := E) →L[ℝ] NativeTwoForm (E := E) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM
    ((tangentBundleCore 𝓘(ℝ,E) M).coordChange j i x)

theorem nativeCoordChangeCLM_apply (i j : atlas E M) (x : M)
    (α : NativeTwoForm (E := E)) :
    nativeCoordChangeCLM (E := E) (M := M) i j x α =
      nativeCoordChange (E := E) (M := M) i j x α := by
  exact ContinuousAlternatingMap.compContinuousLinearMapCLM_apply _ _

theorem nativeCoordChangeCLM_smooth (i j : atlas E M) :
    ContMDiffOn 𝓘(ℝ,E)
      𝓘(ℝ, NativeTwoForm (E := E) →L[ℝ] NativeTwoForm (E := E)) ∞
      (nativeCoordChangeCLM (E := E) (M := M) i j)
      (Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j) := by
  let U := Q.frames.adaptedCore.baseSet i ∩ Q.frames.adaptedCore.baseSet j
  have hU : IsOpen U :=
    (Q.frames.adaptedCore.isOpen_baseSet i).inter
      (Q.frames.adaptedCore.isOpen_baseSet j)
  apply (contMDiffOn_clm_apply_iff (I := 𝓘(ℝ,E)) hU).mpr
  intro α
  have hT : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,E →L[ℝ] E) ∞
      (fun x => (tangentBundleCore 𝓘(ℝ,E) M).coordChange j i x) U := by
    haveI : (tangentBundleCore 𝓘(ℝ,E) M).IsContMDiff 𝓘(ℝ,E) ∞ :=
      tangentBundleCore.isContMDiff
    simpa only [U, Set.inter_comm] using
      (tangentBundleCore 𝓘(ℝ,E) M).contMDiffOn_coordChange
        (n := ∞) 𝓘(ℝ,E) j i
  have hpair : ContMDiffOn 𝓘(ℝ,E)
      𝓘(ℝ, NativeTwoForm (E := E) × (E →L[ℝ] E)) ∞
      (fun x : M => (α,(tangentBundleCore 𝓘(ℝ,E) M).coordChange j i x)) U :=
    contMDiffOn_const.prodMk_space hT
  have h := nativePullback_smooth (E := E) |>.contMDiff.comp_contMDiffOn hpair
  apply h.congr
  intro x hx
  exact (nativeCoordChangeCLM_apply (E := E) (M := M) i j x α).symm

/-- The native alternating two-form bundle with independently smooth
operator-valued transition maps. -/
def nativeTwoFormVectorCore :
    VectorBundleCore ℝ M (NativeTwoForm (E := E)) (atlas E M) where
  baseSet := Q.frames.adaptedCore.baseSet
  isOpen_baseSet := Q.frames.adaptedCore.isOpen_baseSet
  indexAt := Q.frames.adaptedCore.indexAt
  mem_baseSet_at := Q.frames.adaptedCore.mem_baseSet_at
  coordChange := nativeCoordChangeCLM
  coordChange_self i x hi α := by
    rw [nativeCoordChangeCLM_apply]
    exact nativeCoordChange_self Q i x hi α
  continuousOn_coordChange i j :=
    (nativeCoordChangeCLM_smooth Q i j).continuousOn
  coordChange_comp i j k x hx α := by
    rw [nativeCoordChangeCLM_apply, nativeCoordChangeCLM_apply,
      nativeCoordChangeCLM_apply]
    exact nativeCoordChange_comp Q i j k x hx.1.1 hx.1.2 hx.2 α

instance nativeTwoFormVectorCore_isContMDiff :
    (nativeTwoFormVectorCore Q).IsContMDiff 𝓘(ℝ,E) ∞ where
  contMDiffOn_coordChange := nativeCoordChangeCLM_smooth Q

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSmoothCore
