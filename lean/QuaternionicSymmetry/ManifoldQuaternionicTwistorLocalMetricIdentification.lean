import QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricOverlap
import QuaternionicSymmetry.ManifoldTwistorRawChartConjugacy

/-! Identify the checked pointwise split metric with the smooth ambient
formula in every genuine fixed twistor chart. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricIdentification

open ManifoldQuaternionicMetric
open ManifoldQuaternionicCoordinateMetricField
open ManifoldQuaternionicConnection
open ManifoldQuaternionicTwistorSplitMetric
open ManifoldQuaternionicTwistorLocalMetricSmooth
open ManifoldQuaternionicTwistorLocalMetricOverlap
open ManifoldQuaternionicAdjointOverlap
open ManifoldTwistorHorizontalOverlap
open ManifoldTwistorSphereBundle
open ManifoldTwistorSphereCore
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

def ambientMetricRaw (p : M) (r t : X (E := E)) : ℝ :=
  ambientLocalMetric Q D p
    ((r.1.1, (coefficientSphereHomeomorph.symm r.2.1).1),
      (r.1.2, sphereTangentAmbient r.2),
      (t.1.2, sphereTangentAmbient t.2))

theorem ambientMetricRaw_transition (p q : M) (y : E)
    (hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) p q)
    (s : geometricSphere) (u v : E)
    (b c : TangentSpace (𝓡 2) s) :
    ambientMetricRaw Q D q
      (rawTangentTransition Q p q ((y,u),⟨s,b⟩))
      (rawTangentTransition Q p q ((y,v),⟨s,c⟩)) =
    ambientMetricRaw Q D p ((y,u),⟨s,b⟩) ((y,v),⟨s,c⟩) := by
  let a := coefficientSphereHomeomorph.symm s
  have hs : coefficientSphereHomeomorph a = s :=
    coefficientSphereHomeomorph.apply_symm_apply s
  let R := rawTangentTransition Q p q ((y,u),⟨s,b⟩)
  let T := rawTangentTransition Q p q ((y,v),⟨s,c⟩)
  have hR : (R.1.2, sphereTangentAmbient R.2) =
      ambientTransition Q p q y a.1 (u,sphereTangentAmbient (⟨s,b⟩ :
        TangentBundle (𝓡 2) geometricSphere)) := by
    simpa only [R, rawTangentTransition, coefficientEmbedding, a] using
      rawSphereTransition_tangent_ambient Q p q y s u b hy
  have hT : (T.1.2, sphereTangentAmbient T.2) =
      ambientTransition Q p q y a.1 (v,sphereTangentAmbient (⟨s,c⟩ :
        TangentBundle (𝓡 2) geometricSphere)) := by
    simpa only [T, rawTangentTransition, coefficientEmbedding, a] using
      rawSphereTransition_tangent_ambient Q p q y s v c hy
  have hcoef : (coefficientSphereHomeomorph.symm R.2.1).1 =
      rankThreeGauge Q p q y a.1 := by
    change (coefficientSphereHomeomorph.symm
      (rawSphereTransition Q p q (y,s)).2).1 = _
    rw [← hs, rawSphereTransition_coefficient Q p q y hy a,
      coefficientSphereHomeomorph.symm_apply_apply]
    rfl
  change ambientLocalMetric Q D q
      ((R.1.1,(coefficientSphereHomeomorph.symm R.2.1).1),
        (R.1.2,sphereTangentAmbient R.2),
        (T.1.2,sphereTangentAmbient T.2)) =
    ambientLocalMetric Q D p
      ((y,a.1),(u,sphereTangentAmbient (⟨s,b⟩ :
        TangentBundle (𝓡 2) geometricSphere)),
        (v,sphereTangentAmbient (⟨s,c⟩ :
          TangentBundle (𝓡 2) geometricSphere)))
  rw [hcoef, hR, hT]
  change ambientLocalMetric Q D q
      ((chartTransition (I := 𝓘(ℝ,E)) p q y, rankThreeGauge Q p q y a.1),
        ambientTransition Q p q y a.1
          (u,sphereTangentAmbient (⟨s,b⟩ : TangentBundle (𝓡 2) geometricSphere)),
        ambientTransition Q p q y a.1
          (v,sphereTangentAmbient (⟨s,c⟩ : TangentBundle (𝓡 2) geometricSphere))) = _
  exact ambientLocalMetric_overlap Q D p q y hy a.1 _ _

theorem splitMetric_eq_ambient_center (z : SphereBundleTotal Q)
    (u v : TangentSpace (J (E := E)) z) :
    splitMetric Q D z u v =
      ambientLocalMetric Q D z.1
        (((extChartAt 𝓘(ℝ,E) z.1) z.1,
          (coefficientSphereHomeomorph.symm z.2).1),
          (u.1, (sphereTangentVerticalEquiv
            (coefficientSphereHomeomorph.symm z.2) u.2).1),
          (v.1, (sphereTangentVerticalEquiv
            (coefficientSphereHomeomorph.symm z.2) v.2).1)) := by
  have hbase : Q.tangentMetricForm z.1 u.1 v.1 =
      coordinateMetricField Q z.1 ((extChartAt 𝓘(ℝ,E) z.1) z.1) u.1 v.1 := by
    have hi := (tangentBundleCore 𝓘(ℝ,E) M).mem_baseSet_at z.1
    rw [Q.tangentMetric_chart_eq (achart E z.1) z.1 hi]
    change inner ℝ
      (Q.frames.toFrame (achart E z.1) z.1
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
          (achart E z.1) (achart E z.1) z.1 u.1))
      (Q.frames.toFrame (achart E z.1) z.1
        ((tangentBundleCore 𝓘(ℝ,E) M).coordChange
          (achart E z.1) (achart E z.1) z.1 v.1)) = _
    rw [(tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
      (achart E z.1) z.1 hi u.1,
      (tangentBundleCore 𝓘(ℝ,E) M).coordChange_self
        (achart E z.1) z.1 hi v.1]
    rw [coordinateMetricField, Q.chartMetricForm_apply]
    rw [(extChartAt 𝓘(ℝ,E) z.1).left_inv (mem_extChartAt_source z.1)]
  change Q.tangentMetricForm z.1 u.1 v.1 +
      ((sphereTangentVerticalEquiv (coefficientSphereHomeomorph.symm z.2) u.2).1 +
        ManifoldQuaternionicAdjointConnection.inducedForm Q D z.1
          ((extChartAt 𝓘(ℝ,E) z.1) z.1) u.1
          (coefficientSphereHomeomorph.symm z.2).1) ⬝ᵥ
      ((sphereTangentVerticalEquiv (coefficientSphereHomeomorph.symm z.2) v.2).1 +
        ManifoldQuaternionicAdjointConnection.inducedForm Q D z.1
          ((extChartAt 𝓘(ℝ,E) z.1) z.1) v.1
          (coefficientSphereHomeomorph.symm z.2).1) = _
  rw [hbase]
  rfl

theorem splitMetric_eq_ambientRaw_center (z : SphereBundleTotal Q)
    (u v : TangentSpace (J (E := E)) z) :
    splitMetric Q D z u v =
      ambientMetricRaw Q D z.1
        (((extChartAt 𝓘(ℝ,E) z.1) z.1,u.1),⟨z.2,u.2⟩)
        (((extChartAt 𝓘(ℝ,E) z.1) z.1,v.1),⟨z.2,v.2⟩) := by
  rw [splitMetric_eq_ambient_center Q D z u v]
  unfold ambientMetricRaw
  have hs : coefficientSphereHomeomorph
      (coefficientSphereHomeomorph.symm z.2) = z.2 :=
    coefficientSphereHomeomorph.apply_symm_apply z.2
  have hu : sphereTangentAmbient
      (⟨z.2,u.2⟩ : TangentBundle (𝓡 2) geometricSphere) =
      (sphereTangentVerticalEquiv
        (coefficientSphereHomeomorph.symm z.2) u.2).1 := by
    simpa only [hs] using sphereTangentAmbient_eq_vertical
      (coefficientSphereHomeomorph.symm z.2) u.2
  have hv : sphereTangentAmbient
      (⟨z.2,v.2⟩ : TangentBundle (𝓡 2) geometricSphere) =
      (sphereTangentVerticalEquiv
        (coefficientSphereHomeomorph.symm z.2) v.2).1 := by
    simpa only [hs] using sphereTangentAmbient_eq_vertical
      (coefficientSphereHomeomorph.symm z.2) v.2
  rw [hu, hv]

theorem splitMetric_eq_ambientRaw (p : M) (z : SphereBundleTotal Q)
    (hp : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)
    (u v : TangentSpace (J (E := E)) z) :
    splitMetric Q D z u v =
      ambientMetricRaw Q D p
        (rawTangentCoordinates Q p ⟨z,u⟩)
        (rawTangentCoordinates Q p ⟨z,v⟩) := by
  let x := z.1
  let y := (extChartAt 𝓘(ℝ,E) x) x
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source := by
    have hp' := ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hp
    rw [← (sphereCore Q).baseSet_at] at hp'
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hp'
  have hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) x p := by
    constructor
    · exact (extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x)
    · change (extChartAt 𝓘(ℝ,E) x).symm
        ((extChartAt 𝓘(ℝ,E) x) x) ∈ (extChartAt 𝓘(ℝ,E) p).source
      rw [(extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)]
      exact hx
  rw [rawTangentCoordinates_eq_transition Q p z hp u,
    rawTangentCoordinates_eq_transition Q p z hp v]
  have h := ambientMetricRaw_transition Q D x p y hy z.2 u.1 v.1 u.2 v.2
  exact (splitMetric_eq_ambientRaw_center Q D z u v).trans h.symm

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricIdentification
