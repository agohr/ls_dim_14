import QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricSmooth
import QuaternionicSymmetry.ManifoldTwistorRawComplexCovariance

/-! The local horizontal/vertical metric is invariant under genuine
quaternionic chart changes. This is the chart-compatibility input for its
smooth global bundle section. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricOverlap

open ManifoldQuaternionicMetric
open ManifoldQuaternionicConnection
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicTwistorLocalMetricSmooth
open ManifoldTwistorLocalAlmostComplex
open ManifoldTwistorHorizontalOverlap
open ManifoldTwistorSphereBundle
open ManifoldQuaternionicAdjointOverlap
open ManifoldQuaternionicRankThreeOrthogonal
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev V := Fin 3 → ℝ

theorem coordinateMetricField_overlap (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q) (u v : E) :
    coordinateMetricField Q q (chartTransition (I := 𝓘(ℝ,E)) p q y)
      (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u)
      (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y v) =
    coordinateMetricField Q p y u v := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  let i := achart E p
  let j := achart E q
  have hi : x ∈ Q.frames.adaptedCore.baseSet i := by
    simpa only [x, i, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy.1
  have hj : x ∈ Q.frames.adaptedCore.baseSet j := by
    simpa only [x, j, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy.2
  have hqy : (extChartAt 𝓘(ℝ,E) q).symm
      (chartTransition (I := 𝓘(ℝ,E)) p q y) = x :=
    (extChartAt 𝓘(ℝ,E) q).left_inv hy.2
  have hsolder (w : E) :
      Q.frames.toFrame j x
        (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y w) =
      Q.frames.coordChange i j x (Q.frames.toFrame i x w) := by
    have h := congrArg (fun L : E →L[ℝ] E => L w)
      (ManifoldQuaternionicConnection.solder_chartTransition Q p q y hy)
    simp only [ContinuousLinearMap.comp_apply] at h
    have hqval : solder Q q (chartTransition (I := 𝓘(ℝ,E)) p q y) =
        Q.frames.toFrame j x := by
      calc
        _ = Q.frames.toFrame j
            ((extChartAt 𝓘(ℝ,E) q).symm
              (chartTransition (I := 𝓘(ℝ,E)) p q y)) :=
          ManifoldQuaternionicConnection.solder_eq_toFrame Q q _
            ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
        _ = _ := by rw [hqy]
    have hpval : solder Q p y = Q.frames.toFrame i x :=
      ManifoldQuaternionicConnection.solder_eq_toFrame Q p y hy.1
    rw [hqval, hpval] at h
    exact h
  have hqmetric := coordinateMetricField_apply Q q
    (chartTransition (I := 𝓘(ℝ,E)) p q y)
    ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
    (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u)
    (fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y v)
  have hpmetric := coordinateMetricField_apply Q p y hy.1 u v
  rw [hqmetric, hpmetric]
  unfold ManifoldQuaternionicCoordinateMetricity.coordinateMetric
  have hqval : solder Q q (chartTransition (I := 𝓘(ℝ,E)) p q y) =
      Q.frames.toFrame j x := by
    calc
      _ = Q.frames.toFrame j
          ((extChartAt 𝓘(ℝ,E) q).symm
            (chartTransition (I := 𝓘(ℝ,E)) p q y)) :=
        ManifoldQuaternionicConnection.solder_eq_toFrame Q q _
          ((extChartAt 𝓘(ℝ,E) q).map_source hy.2)
      _ = _ := by rw [hqy]
  have hpval : solder Q p y = Q.frames.toFrame i x :=
    ManifoldQuaternionicConnection.solder_eq_toFrame Q p y hy.1
  rw [hqval, hpval]
  rw [hsolder u, hsolder v]
  exact Q.transition_inner i j x hi hj _ _

theorem ambientLocalMetric_overlap (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (a : V) (u v : E × V) :
    ambientLocalMetric Q D q
      ((chartTransition (I := 𝓘(ℝ,E)) p q y, rankThreeGauge Q p q y a),
        ambientTransition Q p q y a u,
        ambientTransition Q p q y a v) =
    ambientLocalMetric Q D p ((y,a),u,v) := by
  let x := (extChartAt 𝓘(ℝ,E) p).symm y
  have hi : x ∈ Q.frames.adaptedCore.baseSet (achart E p) := by
    simpa only [x, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using
      (extChartAt 𝓘(ℝ,E) p).map_target hy.1
  have hj : x ∈ Q.frames.adaptedCore.baseSet (achart E q) := by
    simpa only [x, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hy.2
  have hdot (b c : V) :
      (rankThreeGauge Q p q y b) ⬝ᵥ (rankThreeGauge Q p q y c) = b ⬝ᵥ c := by
    exact rankThreeCoordChange_dot Q (achart E p) (achart E q) x hi hj b c
  have hbase := coordinateMetricField_overlap Q p q y hy u.1 v.1
  have hu := covariantVertical_overlap Q D p q y a u hy
  have hv := covariantVertical_overlap Q D p q y a v hy
  dsimp [ambientLocalMetric]
  rw [show (ambientTransition Q p q y a u).1 =
      fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y u.1 from rfl,
    show (ambientTransition Q p q y a v).1 =
      fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) p q) y v.1 from rfl]
  rw [hbase]
  change coordinateMetricField Q p y u.1 v.1 +
    covariantVertical Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
      (rankThreeGauge Q p q y a) (ambientTransition Q p q y a u) ⬝ᵥ
    covariantVertical Q D q (chartTransition (I := 𝓘(ℝ,E)) p q y)
      (rankThreeGauge Q p q y a) (ambientTransition Q p q y a v) = _
  rw [hu, hv, hdot]
  rfl

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricOverlap
