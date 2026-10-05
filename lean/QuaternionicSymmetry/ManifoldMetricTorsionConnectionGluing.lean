import QuaternionicSymmetry.MetricTorsionFormUniqueness
import QuaternionicSymmetry.QuaternionicProjectedConnectionTorsion
import QuaternionicSymmetry.LocalSolderPullback
import QuaternionicSymmetry.ManifoldQuaternionicScalarCurvature
import QuaternionicSymmetry.ManifoldQuaternionicCoordinateConnection

/-! Metricity and torsion freeness force the correct affine connection
overlap law. Thus local forms satisfying the geometric equations assemble
into a global compatible tangent connection without a gluing premise. -/
namespace QuaternionicSymmetry.ManifoldMetricTorsionConnectionGluing
open ManifoldQuaternionicConnection ManifoldQuaternionicScalarCurvature
open ManifoldQuaternionicCoordinateConnection
open MetricTorsionFormUniqueness QuaternionicRangeFrameCoordinates Filter
open scoped Manifold ContDiff Topology
noncomputable section
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem overlap_of_metric_torsion (Γ : M → E → E →L[ℝ] E →L[ℝ] E)
    (hmetric : ∀ p y u v w, y ∈ (extChartAt 𝓘(ℝ,E) p).target →
      inner ℝ (Γ p y u v) w + inner ℝ v (Γ p y u w) = 0)
    (htorsion : ∀ p y u v, y ∈ (extChartAt 𝓘(ℝ,E) p).target →
      fderiv ℝ (solder Q p) y u v - fderiv ℝ (solder Q p) y v u +
        Γ p y u (solder Q p y v) - Γ p y v (solder Q p y u) = 0)
    (p q : M) (y : E) (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) :
    Γ p y = LocalConnectionGauge.transform
      (LocalConnectionCoordinatePullback.pullback (Γ q) (chartTransition (I := 𝓘(ℝ,E)) p q))
      (adaptedGauge Q p q) (adaptedGaugeInv Q p q) y := by
  let f := chartTransition (I := 𝓘(ℝ,E)) p q
  let g := adaptedGauge Q p q
  let h := adaptedGaugeInv Q p q
  let Λ := LocalConnectionCoordinatePullback.pullback (Γ q) f
  let A := LocalSolderPullback.solder (solder Q q) f
  have hfy : f y ∈ (extChartAt 𝓘(ℝ,E) q).target :=
    (extChartAt 𝓘(ℝ,E) q).map_source hy.2
  have hf : ContDiffAt ℝ 2 f y := chartTransition_contDiffAt p q y hy
  have hg : DifferentiableAt ℝ g y :=
    (adaptedGauge_contDiffAt Q p q y hy (by norm_cast)).differentiableAt (by norm_num)
  have hs := (solder_contDiffAt Q p y hy.1).differentiableAt (by norm_num)
  have ht := (solder_contDiffAt Q q (f y) hfy).differentiableAt (by norm_num)
  have horth : ∀ᶠ z in 𝓝 y, ∀ v w, inner ℝ (g z v) (g z w) = inner ℝ v w := by
    filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ,E)) p q).mem_nhds hy] with z hz
    exact Q.transition_inner (achart E p) (achart E q) ((extChartAt 𝓘(ℝ,E) p).symm z)
      (by simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,tangentBundleCore_baseSet,coe_achart,← extChartAt_source 𝓘(ℝ,E)]
          using (extChartAt 𝓘(ℝ,E) p).map_target hz.1)
      (by simpa only [ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,tangentBundleCore_baseSet,coe_achart,← extChartAt_source 𝓘(ℝ,E)] using hz.2)
  have hA : A =ᶠ[𝓝 y] fun z => (g z).comp (solder Q p z) := by
    filter_upwards [(chartOverlap_isOpen (I := 𝓘(ℝ,E)) p q).mem_nhds hy] with z hz
    exact solder_chartTransition Q p q z hz
  have hΛ : ∀ u v w, inner ℝ (Λ y u v) w + inner ℝ v (Λ y u w) = 0 :=
    fun u v w => hmetric q (f y) (fderiv ℝ f y u) v w hfy
  have hAT : ∀ u v, fderiv ℝ A y u v - fderiv ℝ A y v u +
      Λ y u (A y v) - Λ y v (A y u) = 0 :=
    LocalSolderPullback.torsion (solder Q q) f y (Γ q (f y)) ht hf
      (fun u v => htorsion q (f y) u v hfy)
  have hD : Γ p y = QuaternionicProjectedConnection.form Λ g y :=
    eq_of_metric_torsion (solderEquiv Q p y hy.1) (fun u v => fderiv ℝ (solder Q p) y u v)
      (Γ p y) (QuaternionicProjectedConnection.form Λ g y)
      (fun u v w => hmetric p y u v w hy.1)
      (QuaternionicProjectedConnection.metric Λ g y hg horth hΛ)
      (fun u v => htorsion p y u v hy.1)
      (QuaternionicProjectedConnectionTorsion.torsion Λ g (solder Q p) A y hg hs
        horth.self_of_nhds hA hAT)
  have hAdj : (g y).adjoint = h y := by
    ext z
    have hh := adjoint_left_inverse (g y) horth.self_of_nhds (h y z)
    have hgh : g y (h y z) = z :=
      congrArg (fun L : E →L[ℝ] E => L z) (adaptedGauge_inverse Q p q y hy).2
    rwa [hgh] at hh
  rw [hD]
  ext u v
  rw [QuaternionicProjectedConnection.form_apply,hAdj]
  rfl

def ofLocalForms (Γ : M → E → E →L[ℝ] E →L[ℝ] E)
    (hSmooth : ∀ p, ContDiffOn ℝ ∞ (Γ p) (extChartAt 𝓘(ℝ,E) p).target)
    (hmetric : ∀ p y u v w, y ∈ (extChartAt 𝓘(ℝ,E) p).target →
      inner ℝ (Γ p y u v) w + inner ℝ v (Γ p y u w) = 0)
    (hquat : ∀ p y u t, y ∈ (extChartAt 𝓘(ℝ,E) p).target →
      (Γ p y u).comp (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q (achart E p)) t) -
      (VectorBundleFrameTransitions.quaternionicGenerator (Q.reduction.Q (achart E p)) t).comp (Γ p y u) ∈
        VectorBundleFrameTransitions.quaternionicSpan (Q.reduction.Q (achart E p)))
    (htorsion : ∀ p y u v, y ∈ (extChartAt 𝓘(ℝ,E) p).target →
      fderiv ℝ (solder Q p) y u v - fderiv ℝ (solder Q p) y v u +
        Γ p y u (solder Q p y v) - Γ p y v (solder Q p y u) = 0) :
    CompatibleTangentConnection Q where
  form := Γ
  smooth_form := hSmooth
  overlap := overlap_of_metric_torsion Q Γ hmetric htorsion
  metric := hmetric
  quaternionic := hquat
  torsion := htorsion

end
end QuaternionicSymmetry.ManifoldMetricTorsionConnectionGluing
