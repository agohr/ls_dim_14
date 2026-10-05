import QuaternionicSymmetry.ManifoldQuaternionicFourNativeExteriorComparison
import QuaternionicSymmetry.ManifoldQuaternionicFourFormGluing
import QuaternionicSymmetry.ManifoldQuaternionicFourSphereFormOverlap

/-! The jointly smooth native form is compatible with the actual tangent and
rank-three chart transitions. This is an equality of continuous alternating
forms, not just of their six preferred-frame coordinates. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormOverlap

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeExteriorComparison
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicFourSphereFormOverlap
open ManifoldQuaternionicFourFormGluing
open ManifoldTwistorSphereBundle
open ManifoldTwistorCoefficientSphere
open ManifoldQuaternionicMetric
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

include hdim in
theorem nativeSphereForm_overlap (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : coefficientSphere) :
    nativeSphereForm Q i (x, coefficientSphereHomeomorph a) =
      (nativeSphereForm Q j
        (x, coefficientSphereHomeomorph
          (sphereTransition Q i j x hi hj a))).compContinuousLinearMap
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x) := by
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext k
    fin_cases k <;> rfl
  rw [hv]
  let b := localBasis Q hdim i
  let a' := sphereTransition Q i j x hi hj a
  have hc : (EuclideanSpace.equiv (Fin 3) ℝ)
      (coefficientSphereHomeomorph a).1 = a.1 := rfl
  have hc' : (EuclideanSpace.equiv (Fin 3) ℝ)
      (coefficientSphereHomeomorph a').1 = a'.1 := rfl
  rw [nativeSphereForm_evaluate Q hdim i x hi
    (coefficientSphereHomeomorph a) (v 0) (v 1)]
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have harg :
      (⇑((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x) ∘ ![v 0,v 1]) =
      ![((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x) (v 0),
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x) (v 1)] := by
    funext k
    fin_cases k <;> rfl
  rw [harg]
  rw [nativeSphereForm_evaluate Q hdim j x hj
    (coefficientSphereHomeomorph a')
    ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x (v 0))
    ((tangentBundleCore 𝓘(ℝ,E) M).coordChange i j x (v 1))]
  rw [hc, hc']
  rw [toFrame_coordChange Q i j x hi (v 0),
    toFrame_coordChange Q i j x hi (v 1)]
  have hforms := normalized_operatorForm_synth_overlap Q i j x hi hj b a.1
  have hbasis : operatorForm (localBasis Q hdim j) = operatorForm b :=
    operatorForm_basis_independent _ _
  rw [hbasis]
  have hEval := congrArg (BilinearExterior.evaluate
    (Q.frames.toFrame i x (v 0)) (Q.frames.toFrame i x (v 1))) hforms
  rw [ManifoldQuaternionicFourHodgeOverlapExterior.evaluate_pullbackTwoForm] at hEval
  exact hEval.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormOverlap
