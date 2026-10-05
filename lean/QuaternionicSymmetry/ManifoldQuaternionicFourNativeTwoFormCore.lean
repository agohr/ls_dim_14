import QuaternionicSymmetry.ManifoldQuaternionicFourNativePullbackContinuous
import QuaternionicSymmetry.ManifoldQuaternionicReduction

/-! An independently topologized bundle core for native continuous
alternating tangent two-forms. Its transitions are genuine pullbacks by the
inverse tangent-chart changes, not transported twistor-sphere charts. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeTwoFormCore

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativePullbackContinuous
open VectorBundleFrameTransitions
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

abbrev NativeTwoForm := E [⋀^Fin 2]→L[ℝ] ℝ

/-- A covariant two-form changes coordinates by pullback under the inverse
tangent-chart transition. -/
def nativeCoordChange
    (i j : atlas E M) (x : M) (α : NativeTwoForm (E := E)) :
    NativeTwoForm (E := E) :=
  α.compContinuousLinearMap ((tangentBundleCore 𝓘(ℝ,E) M).coordChange j i x)

theorem nativeCoordChange_self (i : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i) (α : NativeTwoForm (E := E)) :
    nativeCoordChange i i x α = α := by
  ext v
  simp only [nativeCoordChange, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext t
  exact (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self i x hi (v t)

theorem nativeCoordChange_comp (i j k : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (hk : x ∈ Q.frames.adaptedCore.baseSet k)
    (α : NativeTwoForm (E := E)) :
    nativeCoordChange j k x (nativeCoordChange i j x α) =
      nativeCoordChange i k x α := by
  ext v
  simp only [nativeCoordChange, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext t
  exact (tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp k j i x
    ⟨⟨hk,hj⟩,hi⟩ (v t)

theorem nativeCoordChange_continuousOn (i j : atlas E M) :
    ContinuousOn (fun p : M × NativeTwoForm (E := E) =>
      nativeCoordChange i j p.1 p.2)
      ((Q.frames.adaptedCore.baseSet i ∩
        Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ) := by
  let S : Set (M × NativeTwoForm (E := E)) :=
    (Q.frames.adaptedCore.baseSet i ∩
      Q.frames.adaptedCore.baseSet j) ×ˢ Set.univ
  have hα : ContinuousOn (fun p : M × NativeTwoForm (E := E) => p.2) S :=
    continuous_snd.continuousOn
  have hbase : ContinuousOn (fun p : M × NativeTwoForm (E := E) => p.1) S :=
    continuous_fst.continuousOn
  have hT : ContinuousOn (fun p : M × NativeTwoForm (E := E) =>
      (tangentBundleCore 𝓘(ℝ,E) M).coordChange j i p.1) S :=
    ((tangentBundleCore 𝓘(ℝ,E) M).continuousOn_coordChange j i).comp hbase (by
      intro p hp
      exact ⟨hp.1.2, hp.1.1⟩)
  exact nativePullback_continuous.continuousOn.comp (hα.prodMk hT) (by
    intro p hp
    exact Set.mem_univ _)

/-- Independent native alternating-two-form bundle core over the actual
quaternionic manifold. -/
def nativeTwoFormCore : FiberBundleCore (atlas E M) M (NativeTwoForm (E := E)) where
  baseSet := Q.frames.adaptedCore.baseSet
  isOpen_baseSet := Q.frames.adaptedCore.isOpen_baseSet
  indexAt := Q.frames.adaptedCore.indexAt
  mem_baseSet_at := Q.frames.adaptedCore.mem_baseSet_at
  coordChange := nativeCoordChange
  coordChange_self := nativeCoordChange_self Q
  continuousOn_coordChange := nativeCoordChange_continuousOn Q
  coordChange_comp i j k x hx α :=
    nativeCoordChange_comp Q i j k x hx.1.1 hx.1.2 hx.2 α

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeTwoFormCore
