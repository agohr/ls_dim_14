import QuaternionicSymmetry.ManifoldQuaternionicLocalSpanDerivative
import QuaternionicSymmetry.GeneralSmoothReflectedEndomorphismField
import QuaternionicSymmetry.ManifoldQuaternionicConnectionIsometrySolder

/-! Reflection preserves the whole local quaternionic plane for any
Q-valued endomorphism field, via actual derivative intertwining. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicReflectedSpanSection

open ManifoldQuaternionicReduction
open ManifoldQuaternionicLocalDerivativeEquivariance
open ManifoldQuaternionicLocalSpanDerivative
open ManifoldQuaternionicConnectionIsometrySolder
open ManifoldQuaternionicSpanSymmetry
open GeneralSmoothReflectedEndomorphismField
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem reflectedField_mem_chartSpan_of_chart_inverse
    (f : QuaternionicIsometries Q) (p x : M)
    (S : E → E →L[ℝ] E) (y : E)
    (hp : f • p = p)
    (hx : x ∈ (chartAt E p).source)
    (hfx : f • x ∈ (chartAt E p).source)
    (hchart : extChartAt 𝓘(ℝ,E) p x = localIsometryChartMap Q f p y)
    (hreturn : f • x = (extChartAt 𝓘(ℝ,E) p).symm y)
    (hS : S (localIsometryChartMap Q f p y) ∈
      Q.chartSpan (achart E p) x)
    (hinv : (fderiv ℝ (localIsometryChartMap Q f p)
          (localIsometryChartMap Q f p y)).comp
        (fderiv ℝ (localIsometryChartMap Q f p) y) =
          ContinuousLinearMap.id ℝ E) :
    reflectedField (localIsometryChartMap Q f p) S y ∈
      Q.chartSpan (achart E p) ((extChartAt 𝓘(ℝ,E) p).symm y) := by
  let F := localIsometryChartMap Q f p
  let R := fderiv ℝ F (F y)
  let T := S (F y)
  let V := fderiv ℝ F y
  have hR : R = localRawDerivative Q f p x := by
    change fderiv ℝ (localIsometryChartMap Q f p)
      (localIsometryChartMap Q f p y) = _
    rw [← hchart]
    exact localIsometryChartMap_fderiv Q f p x hx
      (by simpa only [hp] using hfx)
  obtain ⟨U, hU, hinter⟩ :=
    localRawDerivative_chartSpan_intertwines Q f p x hx
      (by simpa only [hp] using hfx) T hS
  have hB : reflectedField F S y = U := by
    change (R.comp T).comp V = U
    rw [hR, hinter, ContinuousLinearMap.comp_assoc]
    have hRV : (localRawDerivative Q f p x).comp V =
        ContinuousLinearMap.id ℝ E := by
      simpa only [← hR, R, V, F] using hinv
    rw [hRV]
    simp
  rw [hB]
  simpa only [hp, hreturn] using hU

end
end QuaternionicSymmetry.ManifoldQuaternionicReflectedSpanSection
