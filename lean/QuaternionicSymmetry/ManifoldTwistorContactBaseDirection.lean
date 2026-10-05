import QuaternionicSymmetry.ManifoldTwistorContactLocalBundleLift

/-! In every fixed twistor sphere chart, the base tangent component of
the full tangent chart is exactly the fiber coordinate in the ordinary
base tangent-bundle trivialization. This identifies the two chart
conventions needed for the smooth horizontal-lift bundle map. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open QuaternionicSymmetry.ManifoldTwistorLocalAlmostComplex
open QuaternionicSymmetry.ManifoldTwistorHorizontalConnection
open QuaternionicSymmetry.ManifoldQuaternionicMetric
open QuaternionicSymmetry.ManifoldQuaternionicConnection
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : CompatibleTangentConnection Q)

private abbrev I := (𝓘(ℝ,E)).prod (𝓡 2)

theorem rawTangentCoordinates_baseDirection (D : CompatibleTangentConnection Q) (p : M)
    (z : SphereBundleTotal Q)
    (hp : z ∈ ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source)
    (v : TangentSpace (I (E := E)) z) :
    (rawTangentCoordinates Q p ⟨z,v⟩).1.2 =
      ((tangentBundleCore 𝓘(ℝ,E) M).localTriv (achart E p)
        (⟨z.1,v.1⟩ : TangentBundle 𝓘(ℝ,E) M)).2 := by
  let x := z.1
  let y := (extChartAt 𝓘(ℝ,E) x) x
  let a := coefficientSphereHomeomorph.symm z.2
  have hs : coefficientSphereHomeomorph a = z.2 :=
    coefficientSphereHomeomorph.apply_symm_apply z.2
  have hy : y ∈ chartOverlap (I := 𝓘(ℝ,E)) x p := by
    have hx : x ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hp' := ((sphereCore Q).mem_localTriv_source (achart E p) z).mp hp
      rw [← (sphereCore Q).baseSet_at] at hp'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hp'
    exact ⟨(extChartAt 𝓘(ℝ,E) x).map_source (mem_extChartAt_source x),
      by simpa only [y, (extChartAt 𝓘(ℝ,E) x).left_inv (mem_extChartAt_source x)] using hx⟩
  rw [rawTangentCoordinates_eq_transition Q p z hp v]
  have hraw := rawTangentTransition_eq_local Q D x p y hy a v.1 (hs ▸ v.2)
  have hfirst : (rawTangentTransition Q x p
      ((y,v.1),⟨coefficientSphereHomeomorph a, hs ▸ v.2⟩)).1.2 =
      fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) x p) y v.1 := by
    rw [hraw]
    simp [localTangentTransition, splitTransition, connectionSplit]
  have hcore := chartTransition_derivative_eq_core (I := 𝓘(ℝ,E)) x p y hy
  have hbase : (rawTangentTransition Q z.1 p
      (((extChartAt 𝓘(ℝ,E) z.1) z.1,v.1),⟨z.2,v.2⟩)).1.2 =
      fderiv ℝ (chartTransition (I := 𝓘(ℝ,E)) z.1 p)
        ((extChartAt 𝓘(ℝ,E) z.1) z.1) v.1 := by
    simpa only [x,y,hs] using hfirst
  rw [hbase, chartTransition_derivative_eq_core
    (I := 𝓘(ℝ,E)) z.1 p _ hy]
  simp only [(tangentBundleCore 𝓘(ℝ,E) M).localTriv_apply]
  dsimp only [y]
  rw [(extChartAt 𝓘(ℝ,E) z.1).left_inv (mem_extChartAt_source z.1)]
  rfl

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
