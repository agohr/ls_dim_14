import QuaternionicSymmetry.ManifoldQuaternionicAdjointOverlap

/-! Differentiating the genuine rank-three gauge shows that a fixed
adapted quaternionic operator, transported between overlapping tangent
frames, has both value and first derivative in the target fixed span. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicGaugePlaneDerivative

open Filter ManifoldQuaternionicConnection
open ManifoldQuaternionicAdjointOverlap
open VectorBundleFrameTransitions
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

def transportedOperator (p q : M) (T : E →L[ℝ] E) (y : E) : E →L[ℝ] E :=
  adaptedGauge Q p q y * T * adaptedGaugeInv Q p q y

theorem transportedOperator_value_and_derivative_mem
    (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (T : E →L[ℝ] E)
    (hT : T ∈ quaternionicSpan (Q.reduction.Q (achart E p)))
    (u : E) :
    transportedOperator Q p q T y ∈
      quaternionicSpan (Q.reduction.Q (achart E q)) ∧
      fderiv ℝ (transportedOperator Q p q T) y u ∈
        quaternionicSpan (Q.reduction.Q (achart E q)) := by
  let a := coeff (Q.reduction.Q (achart E p)) T
  have hTp : synth (Q.reduction.Q (achart E p)) a = T :=
    synth_coeff_of_mem _ _ hT
  have hEq : transportedOperator Q p q T =ᶠ[𝓝 y]
      (fun z => synth (Q.reduction.Q (achart E q))
        (rankThreeGauge Q p q z a)) := by
    filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ,E)) p q).mem_nhds hy]
      with z hz
    rw [transportedOperator, ← hTp]
    exact (synth_rankThreeGauge Q p q z hz a).symm
  have hval : transportedOperator Q p q T y =
      synth (Q.reduction.Q (achart E q)) (rankThreeGauge Q p q y a) :=
    hEq.eq_of_nhds
  have hR : DifferentiableAt ℝ (rankThreeGauge Q p q) y :=
    (rankThreeGauge_contDiffAt Q p q y hy
      (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out)).differentiableAt
        (by norm_num)
  have hRa : DifferentiableAt ℝ (fun z => rankThreeGauge Q p q z a) y :=
    hR.clm_apply (differentiableAt_const a)
  have hderiv : fderiv ℝ (transportedOperator Q p q T) y u =
      synth (Q.reduction.Q (achart E q))
        (fderiv ℝ (fun z => rankThreeGauge Q p q z a) y u) := by
    rw [hEq.fderiv_eq]
    have h := fderiv_comp y
      (synth (Q.reduction.Q (achart E q))).differentiableAt hRa
    simpa only [ContinuousLinearMap.fderiv,
      ContinuousLinearMap.comp_apply] using congrArg (fun L : E →L[ℝ] _ => L u) h
  constructor
  · rw [hval]
    exact synth_mem _ _
  · rw [hderiv]
    exact synth_mem _ _

end
end QuaternionicSymmetry.ManifoldQuaternionicGaugePlaneDerivative
