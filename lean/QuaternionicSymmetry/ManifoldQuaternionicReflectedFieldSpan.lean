import QuaternionicSymmetry.ManifoldQuaternionicLocalSynthSpan
import QuaternionicSymmetry.ManifoldQuaternionicLocalGeneratorField
import QuaternionicSymmetry.GeneralSmoothReflectedEndomorphismField
import QuaternionicSymmetry.ManifoldQuaternionicConnectionIsometrySolder

/-! A reflected local quaternionic generator lies in the actual target
quaternionic plane whenever the chart reflection derivatives cancel. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicReflectedFieldSpan

open ManifoldQuaternionicReduction
open ManifoldQuaternionicLocalSynthSpan
open ManifoldQuaternionicLocalGaugeTransport
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicSpanSymmetry
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicLocalGeneratorField
open GeneralSmoothReflectedEndomorphismField
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem reflectedField_mem_chartSpan_of_chart_inverse
    (f : QuaternionicIsometries Q) (p x : M) (t : Fin 3) (y : E)
    (hp : f • p = p)
    (hx : x ∈ (chartAt E p).source)
    (hfx : f • x ∈ (chartAt E p).source)
    (hchart : extChartAt 𝓘(ℝ,E) p x = localIsometryChartMap Q f p y)
    (hreturn : f • x = (extChartAt 𝓘(ℝ,E) p).symm y)
    (hinv : (fderiv ℝ (localIsometryChartMap Q f p)
          (localIsometryChartMap Q f p y)).comp
        (fderiv ℝ (localIsometryChartMap Q f p) y) =
          ContinuousLinearMap.id ℝ E) :
    reflectedField (localIsometryChartMap Q f p)
      (localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent p t) y ∈
      Q.chartSpan (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  let F := localIsometryChartMap Q f p
  let A := localChartGeneratorField Q.toSmoothAlmostQuaternionicTangent p t
  let R := fderiv ℝ F (F y)
  let S := fderiv ℝ F y
  let b := localTrueCoefficientAction Q f p x
    (coeff (Q.reduction.Q (achart E p))
      (VectorBundleFrameTransitions.quaternionicGenerator
        (Q.reduction.Q (achart E p)) t))
  have hR : R = localRawDerivative Q f p x := by
    change fderiv ℝ (localIsometryChartMap Q f p)
      (localIsometryChartMap Q f p y) = _
    rw [← hchart]
    exact localIsometryChartMap_fderiv Q f p x hx
      (by simpa only [hp] using hfx)
  have hA : A (F y) = Q.chartGenerator (achart E p) t x := by
    change Q.chartGenerator (achart E p) t
      ((extChartAt 𝓘(ℝ,E) p).symm
        (localIsometryChartMap Q f p y)) = _
    rw [← hchart, (extChartAt 𝓘(ℝ,E) p).left_inv
      (by simpa only [extChartAt_source] using hx)]
  have hinter : R.comp (A (F y)) =
      (localTangentSynth Q (achart E p)
        ((extChartAt 𝓘(ℝ,E) p).symm y) b).comp R := by
    rw [hR, hA]
    simpa only [hp, hreturn, b] using
      (localRawDerivative_chartGenerator_intertwines Q f p x hx
        (by simpa only [hp] using hfx) t)
  have hB : reflectedField F A y =
      localTangentSynth Q (achart E p)
        ((extChartAt 𝓘(ℝ,E) p).symm y) b := by
    change (R.comp (A (F y))).comp S = _
    rw [hinter, ContinuousLinearMap.comp_assoc, hinv]
    simp
  rw [hB]
  exact localTangentSynth_mem_chartSpan Q _ _ _

end
end QuaternionicSymmetry.ManifoldQuaternionicReflectedFieldSpan
