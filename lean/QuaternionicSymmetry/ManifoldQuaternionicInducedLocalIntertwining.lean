import QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientMetricFormula
import QuaternionicSymmetry.ManifoldQuaternionicLocalGaugeTransport
import QuaternionicSymmetry.ManifoldQuaternionicLocalSynthMetric

/-! Fixed adapted-chart forms of the rectangular induced derivative and its
quaternionic coefficient map. Unlike preferred `indexAt` coordinates, these
are the quantities whose smoothness can be checked locally. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedLocalIntertwining
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicLocalSynthMetric
open ManifoldTwistorSphereBundle
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

def localDerivative (i : atlas F N) (j : atlas E M) (x : N) :
    F →L[ℝ] E :=
  ((tangentBundleCore 𝓘(ℝ,E) M).coordChange (achart E (ι x)) j (ι x)).comp
    ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x).comp
      ((tangentBundleCore 𝓘(ℝ,F) N).coordChange i (achart F x) x))

def localCoefficientMap (i : atlas F N) (j : atlas E M) (x : N) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (P.tangent.reduction.rankThreeCoordChange (achart E (ι x)) j (ι x)).toLinearMap.comp
    ((coefficientMap P R ι hι hR x).comp
      (R.tangent.reduction.rankThreeCoordChange i (achart F x) x).toLinearMap)

theorem localCoefficientMap_squareNorm
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ R.tangent.frames.adaptedCore.baseSet i)
    (hj : ι x ∈ P.tangent.frames.adaptedCore.baseSet j)
    (a : Fin 3 → ℝ) :
    squareNorm (localCoefficientMap P R ι hι hR i j x a) = squareNorm a := by
  let ki := achart F x
  let kj := achart E (ι x)
  have hki := R.tangent.frames.adaptedCore.mem_baseSet_at x
  have hkj := P.tangent.frames.adaptedCore.mem_baseSet_at (ι x)
  change squareNorm (P.tangent.reduction.rankThreeCoordChange kj j (ι x)
    (coefficientMap P R ι hι hR x
      (R.tangent.reduction.rankThreeCoordChange i ki x a))) = _
  rw [squareNorm_transition P.tangent kj j (ι x) hkj hj,
    coefficientMap_squareNorm P R ι hι hR x,
    squareNorm_transition R.tangent i ki x hi hki]

theorem localDerivative_intertwines
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ R.tangent.frames.adaptedCore.baseSet i)
    (hj : ι x ∈ P.tangent.frames.adaptedCore.baseSet j)
    (a : Fin 3 → ℝ) (v : F) :
    localDerivative ι i j x (localTangentSynth R.tangent i x a v) =
      localTangentSynth P.tangent j (ι x)
        (localCoefficientMap P R ι hι hR i j x a)
        (localDerivative ι i j x v) := by
  let ki := achart F x
  let kj := achart E (ι x)
  have hki := R.tangent.frames.adaptedCore.mem_baseSet_at x
  have hkj := P.tangent.frames.adaptedCore.mem_baseSet_at (ι x)
  let Ci := (tangentBundleCore 𝓘(ℝ,F) N).coordChange i ki x
  let Cj := (tangentBundleCore 𝓘(ℝ,E) M).coordChange kj j (ι x)
  let d := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
  change Cj (d (Ci (localTangentSynth R.tangent i x a v))) =
    localTangentSynth P.tangent j (ι x)
      (P.tangent.reduction.rankThreeCoordChange kj j (ι x)
        (coefficientMap P R ι hι hR x
          (R.tangent.reduction.rankThreeCoordChange i ki x a)))
      (Cj (d (Ci v)))
  rw [← localTangentSynth_coordChange R.tangent i ki x hi hki a v]
  change Cj (d (tangentSynth R.tangent x
    (R.tangent.reduction.rankThreeCoordChange i ki x a) (Ci v))) = _
  rw [coefficientMap_intertwines P R ι hι hR x
    (R.tangent.reduction.rankThreeCoordChange i ki x a) (Ci v)]
  exact (localTangentSynth_coordChange P.tangent kj j (ι x) hkj hj
    (coefficientMap P R ι hι hR x
      (R.tangent.reduction.rankThreeCoordChange i ki x a)) (d (Ci v))).symm

/-- Each fixed-chart induced coefficient is recovered from one column of
the rectangular local derivative. All operators and metric coefficients in
this equality are written in fixed adapted charts. -/
theorem localCoefficientMap_metric_formula
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ R.tangent.frames.adaptedCore.baseSet i)
    (hj : ι x ∈ P.tangent.frames.adaptedCore.baseSet j)
    (a : Fin 3 → ℝ) (v : F) (k : Fin 3) :
    (localCoefficientMap P R ι hι hR i j x a) k *
        P.tangent.chartMetricForm j (ι x)
          (localDerivative ι i j x v) (localDerivative ι i j x v) =
      P.tangent.chartMetricForm j (ι x)
        (localDerivative ι i j x (localTangentSynth R.tangent i x a v))
        (localTangentSynth P.tangent j (ι x)
          (Pi.basisFun ℝ (Fin 3) k) (localDerivative ι i j x v)) := by
  have h := localTangentSynth_chartMetric P.tangent j (ι x) hj
    (localCoefficientMap P R ι hι hR i j x a)
    (Pi.basisFun ℝ (Fin 3) k) (localDerivative ι i j x v)
  rw [← localDerivative_intertwines P R ι hι hR i j x hi hj a v] at h
  classical
  simpa only [Pi.basisFun_apply, dotProduct_single, mul_one] using h.symm

include hι in
/-- The fixed-chart derivative remains injective: source and target tangent
coordinate changes are linear equivalences on the chart overlap. -/
theorem localDerivative_injective
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ R.tangent.frames.adaptedCore.baseSet i)
    (hj : ι x ∈ P.tangent.frames.adaptedCore.baseSet j) :
    Function.Injective (localDerivative ι i j x) := by
  let ki := achart F x
  let kj := achart E (ι x)
  let Ci := (tangentBundleCore 𝓘(ℝ,F) N).coordChange i ki x
  let CiInv := (tangentBundleCore 𝓘(ℝ,F) N).coordChange ki i x
  let Cj := (tangentBundleCore 𝓘(ℝ,E) M).coordChange kj j (ι x)
  let CjInv := (tangentBundleCore 𝓘(ℝ,E) M).coordChange j kj (ι x)
  have hki := R.tangent.frames.adaptedCore.mem_baseSet_at x
  have hkj := P.tangent.frames.adaptedCore.mem_baseSet_at (ι x)
  have hCi (v : F) : CiInv (Ci v) = v := by
    rw [(tangentBundleCore 𝓘(ℝ,F) N).coordChange_comp i ki i x ⟨⟨hi,hki⟩,hi⟩,
      (tangentBundleCore 𝓘(ℝ,F) N).coordChange_self i x hi]
  have hCj (v : E) : CjInv (Cj v) = v := by
    rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_comp kj j kj (ι x) ⟨⟨hkj,hj⟩,hkj⟩,
      (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self kj (ι x) hkj]
  intro u v huv
  change Cj ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x) (Ci u)) =
    Cj ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x) (Ci v)) at huv
  have hd' := congrArg CjInv huv
  rw [hCj, hCj] at hd'
  have hd := hι x hd'
  exact (hCi u).symm.trans (congrArg CiInv hd |>.trans (hCi v))

include hι in
theorem localDerivative_chartMetric_pos
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ R.tangent.frames.adaptedCore.baseSet i)
    (hj : ι x ∈ P.tangent.frames.adaptedCore.baseSet j)
    (v : F) (hv : v ≠ 0) :
    0 < P.tangent.chartMetricForm j (ι x)
      (localDerivative ι i j x v) (localDerivative ι i j x v) := by
  apply chartMetricForm_pos P.tangent j (ι x) hj
  intro h
  exact hv ((localDerivative_injective P R ι hι i j x hi hj)
    (by simpa using h))

/-- Fixed-chart quotient with a positive denominator. This is the exact
local expression used to prove smoothness of the induced sphere-fiber map. -/
theorem localCoefficientMap_eq_metric_div
    (i : atlas F N) (j : atlas E M) (x : N)
    (hi : x ∈ R.tangent.frames.adaptedCore.baseSet i)
    (hj : ι x ∈ P.tangent.frames.adaptedCore.baseSet j)
    (a : Fin 3 → ℝ) (v : F) (hv : v ≠ 0) (k : Fin 3) :
    (localCoefficientMap P R ι hι hR i j x a) k =
      P.tangent.chartMetricForm j (ι x)
        (localDerivative ι i j x (localTangentSynth R.tangent i x a v))
        (localTangentSynth P.tangent j (ι x)
          (Pi.basisFun ℝ (Fin 3) k) (localDerivative ι i j x v)) /
      P.tangent.chartMetricForm j (ι x)
        (localDerivative ι i j x v) (localDerivative ι i j x v) := by
  apply (eq_div_iff (ne_of_gt
    (localDerivative_chartMetric_pos P R ι hι i j x hi hj v hv))).mpr
  exact localCoefficientMap_metric_formula P R ι hι hR i j x hi hj a v k

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedLocalIntertwining
