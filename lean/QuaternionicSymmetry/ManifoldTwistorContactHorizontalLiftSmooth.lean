import QuaternionicSymmetry.ManifoldTwistorContactLiftChartIdentity

/-! The geometric horizontal lift π*TM → TZ is a globally smooth map of
the actual smooth vector-bundle total spaces. The proof uses the exact
fixed-chart identity and the checked local source/target atlas maps. -/

namespace QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex

open QuaternionicSymmetry.ManifoldTwistorSphereBundle
open QuaternionicSymmetry.ManifoldTwistorSphereCore
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
private abbrev J := I (E := E) |>.prod 𝓘(ℝ,E)

theorem contactHorizontalLift_smooth :
    ContMDiff (J (E := E)) (I (E := E)).tangent ∞
      (contactHorizontalLift Q D) := by
  intro t
  let p := t.1.1
  let U := contactPullbackChartDomain Q p
  have ht : t ∈ U := by
    constructor
    · apply ((sphereCore Q).mem_localTriv_source (achart E p) t.1).mpr
      rw [← (sphereCore Q).baseSet_at]
      exact (sphereCore Q).mem_baseSet_at p
    · change Bundle.Pullback.lift (twistorProjectionMap Q) t ∈
        (contactBaseTrivialization (E := E) p).source
      change p ∈ (contactBaseTrivialization (E := E) p).baseSet
      exact FiberBundle.mem_baseSet_trivializationAt E
        (TangentSpace 𝓘(ℝ,E) : M → Type _) p
  have hOpen : IsOpen U := contactPullbackChartDomain_open Q p
  have hMap : Set.MapsTo (contactPullbackCoordinates Q p) U
      {r : (E × ManifoldTwistorCoefficientSphere.geometricSphere) × E |
        r.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).target} := by
    intro w hw
    have hx : w.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
      have hw' := ((sphereCore Q).mem_localTriv_source (achart E p) w.1).mp hw.1
      rw [← (sphereCore Q).baseSet_at] at hw'
      simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
        tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hw'
    exact (extChartAt 𝓘(ℝ,E) p).map_source hx
  have hComp := (localContactBundleLift_smoothOn Q D p).comp
    (contactPullbackCoordinates_smoothOn Q p) hMap
  have hEq : ∀ w ∈ U,
      contactHorizontalLift Q D w =
        localContactBundleLift Q D p (contactPullbackCoordinates Q p w) := by
    intro w hw
    exact contactHorizontalLift_fixedChart Q D p w hw.1
  have hOn : ContMDiffOn (J (E := E)) (I (E := E)).tangent ∞
      (contactHorizontalLift Q D) U :=
    hComp.congr (fun w hw => by simpa only [Function.comp_apply] using hEq w hw)
  exact hOn.contMDiffAt (hOpen.mem_nhds ht)

end
end QuaternionicSymmetry.ManifoldTwistorGlobalAlmostComplex
