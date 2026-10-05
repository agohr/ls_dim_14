import QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeEigen
import QuaternionicSymmetry.ManifoldQuaternionicFourSphereFormOverlap

/-! The actual tangent two-form associated to a unit quaternionic coefficient
does not depend on which adapted chart represents the same twistor point. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeGluing

open Module
open FourDimensionalExteriorHodge
open FourDimensionalExteriorQuaternionicHalf
open ManifoldQuaternionicFourHodgeOverlapExterior
open ManifoldQuaternionicFourSphereFormOverlap
open ManifoldQuaternionicFourTangentOrientation
open ManifoldQuaternionicFourTwistorHodgeFiber
open ManifoldQuaternionicMetric
open VectorBundleFrameTransitions VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

theorem localToTangent_transition (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j) (v : E) :
    localToTangentEquiv Q j x hj (Q.frames.coordChange i j x v) =
      localToTangentEquiv Q i x hi v := by
  let k := Q.frames.adaptedCore.indexAt x
  have hk : x ∈ Q.frames.adaptedCore.baseSet k :=
    Q.frames.adaptedCore.mem_baseSet_at x
  change Q.frames.fromFrame k x
      (Q.frames.coordChange j k x (Q.frames.coordChange i j x v)) =
    Q.frames.fromFrame k x (Q.frames.coordChange i k x v)
  rw [Q.frames.coordChange_comp i j k x hi hj hk]

theorem localTangentTwoForm_overlap (i j : atlas E M) (x : M)
    (hi : x ∈ Q.frames.adaptedCore.baseSet i)
    (hj : x ∈ Q.frames.adaptedCore.baseSet j)
    (a : Fin 3 → ℝ) :
    localTangentTwoForm Q hdim j x hj
      (Q.reduction.rankThreeCoordChange i j x a) =
    localTangentTwoForm Q hdim i x hi a := by
  let Ci := localToTangentEquiv Q i x hi
  let Cj := localToTangentEquiv Q j x hj
  let Li := Q.frames.coordChange i j x
  let αi := localTangentTwoForm Q hdim i x hi a
  let αj := localTangentTwoForm Q hdim j x hj
    (Q.reduction.rankThreeCoordChange i j x a)
  let bi := localBasis Q hdim i
  let bj := localBasis Q hdim j
  have hbi := localTangentTwoForm_pullback Q hdim i x hi bi a
  have hbj := localTangentTwoForm_pullback Q hdim j x hj bj
    (Q.reduction.rankThreeCoordChange i j x a)
  have hforms := normalized_operatorForm_synth_overlap Q i j x hi hj bi a
  rw [← operatorForm_basis_independent bi bj] at hbj
  apply ExteriorDuality.twoform_ext bi
  intro v w
  have hcv := localToTangent_transition Q i j x hi hj (Ci.symm v)
  have hcw := localToTangent_transition Q i j x hi hj (Ci.symm w)
  have hv : Cj.symm v = Li (Ci.symm v) := by
    apply Cj.injective
    calc
      Cj (Cj.symm v) = v := Cj.apply_symm_apply v
      _ = Ci (Ci.symm v) := (Ci.apply_symm_apply v).symm
      _ = Cj (Li (Ci.symm v)) := hcv.symm
  have hw : Cj.symm w = Li (Ci.symm w) := by
    apply Cj.injective
    calc
      Cj (Cj.symm w) = w := Cj.apply_symm_apply w
      _ = Ci (Ci.symm w) := (Ci.apply_symm_apply w).symm
      _ = Cj (Li (Ci.symm w)) := hcw.symm
  have h1 := congrArg (fun θ : TwoForm E =>
    BilinearExterior.evaluate (Cj.symm v) (Cj.symm w) θ) hbj
  have h2 := congrArg (fun θ : TwoForm E =>
    BilinearExterior.evaluate (Ci.symm v) (Ci.symm w) θ) hbi
  change BilinearExterior.evaluate (Cj.symm v) (Cj.symm w)
      (pullbackTwoForm bj Cj.toLinearMap αj) = _ at h1
  change BilinearExterior.evaluate (Ci.symm v) (Ci.symm w)
      (pullbackTwoForm bi Ci.toLinearMap αi) = _ at h2
  rw [evaluate_pullbackTwoForm] at h1 h2
  rw [hv, hw] at h1
  have h3 := congrArg (fun θ : TwoForm E =>
    BilinearExterior.evaluate (Ci.symm v) (Ci.symm w) θ) hforms
  change BilinearExterior.evaluate (Ci.symm v) (Ci.symm w)
      (pullbackTwoForm bi Li.toLinearMap
        ((Real.sqrt 2)⁻¹ • operatorForm bi
          (synth (Q.reduction.Q j)
            (Q.reduction.rankThreeCoordChange i j x a)))) = _ at h3
  rw [evaluate_pullbackTwoForm] at h3
  have ht := h1.trans (h3.trans h2.symm)
  change BilinearExterior.evaluate (Cj (Li (Ci.symm v)) : E)
      (Cj (Li (Ci.symm w)) : E) αj =
    BilinearExterior.evaluate (Ci (Ci.symm v) : E)
      (Ci (Ci.symm w) : E) αi at ht
  have hv' : (Cj (Li (Ci.symm v)) : E) = v :=
    hcv.trans (Ci.apply_symm_apply v)
  have hw' : (Cj (Li (Ci.symm w)) : E) = w :=
    hcw.trans (Ci.apply_symm_apply w)
  rw [hv', hw', Ci.apply_symm_apply, Ci.apply_symm_apply] at ht
  exact ht

end
end QuaternionicSymmetry.ManifoldQuaternionicFourTwistorHodgeGluing
