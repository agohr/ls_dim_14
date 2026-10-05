import QuaternionicSymmetry.ManifoldQuaternionicTwistorRawMetricSmooth

/-! Smooth scalar evaluation of the actual twistor split metric on any two
smooth tangent fields. This is proved in fixed raw charts, not assumed as a
property of an abstract Riemannian metric. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricEvaluationSmooth

open ManifoldQuaternionicTwistorSplitMetric
open ManifoldQuaternionicTwistorLocalMetricIdentification
open ManifoldQuaternionicTwistorRawMetricSmooth
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

private def chartSource (p : M) : Set (SphereBundleTotal Q) :=
  ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source

private theorem rawCoordinates_mapsTo (p : M)
    (v : TangentBundle (J (E := E)) (SphereBundleTotal Q))
    (hv : v.1 ∈ chartSource Q p) :
    rawTangentCoordinates Q p v ∈ localDomain (E := E) p := by
  have hx : v.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).source := by
    have hv' := ((sphereCore Q).mem_localTriv_source (achart E p) v.1).mp hv
    rw [← (sphereCore Q).baseSet_at] at hv'
    simpa only [sphereCore, ManifoldQuaternionicReduction.TangentFrameGauge.adaptedCore,
      tangentBundleCore_baseSet, coe_achart, ← extChartAt_source 𝓘(ℝ,E)] using hv'
  change (extChartAt 𝓘(ℝ,E) p) v.1.1 ∈ (extChartAt 𝓘(ℝ,E) p).target
  exact (extChartAt 𝓘(ℝ,E) p).map_source hx

theorem splitMetric_eval_smoothOn_of_subset (p : M) (s : Set (SphereBundleTotal Q))
    (hs : s ⊆ chartSource Q p)
    (u v : ∀ z : SphereBundleTotal Q, TangentSpace (J (E := E)) z)
    (hu : ContMDiffOn (J (E := E)) (J (E := E)).tangent ∞
      (fun z => (⟨z,u z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q)))
      s)
    (hv : ContMDiffOn (J (E := E)) (J (E := E)).tangent ∞
      (fun z => (⟨z,v z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q)))
      s) :
    ContMDiffOn (J (E := E)) 𝓘(ℝ) ∞
      (fun z => splitMetric Q D z (u z) (v z)) s := by
  let U := s
  have hrawu : ContMDiffOn (J (E := E)) (IX (E := E)) ∞
      (fun z => rawTangentCoordinates Q p
        (⟨z,u z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q))) U :=
    (rawTangentCoordinates_smoothOn Q p).comp hu (by
      intro z hz
      exact hs hz)
  have hrawv : ContMDiffOn (J (E := E)) (IX (E := E)) ∞
      (fun z => rawTangentCoordinates Q p
        (⟨z,v z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q))) U :=
    (rawTangentCoordinates_smoothOn Q p).comp hv (by
      intro z hz
      exact hs hz)
  have hmaps : Set.MapsTo
      (fun z => (rawTangentCoordinates Q p
          (⟨z,u z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q)),
        rawTangentCoordinates Q p
          (⟨z,v z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q))))
      U (localDomain (E := E) p ×ˢ localDomain (E := E) p) := by
    intro z hz
    exact ⟨rawCoordinates_mapsTo Q p ⟨z,u z⟩ (hs hz),
      rawCoordinates_mapsTo Q p ⟨z,v z⟩ (hs hz)⟩
  have hlocal := (ambientMetricRaw_smooth Q D p).comp
    (hrawu.prodMk hrawv) hmaps
  exact hlocal.congr (by
    intro z hz
    exact splitMetric_eq_ambientRaw Q D p z (hs hz) (u z) (v z))

theorem splitMetric_eval_smoothOn (p : M)
    (u v : ∀ z : SphereBundleTotal Q, TangentSpace (J (E := E)) z)
    (hu : ContMDiffOn (J (E := E)) (J (E := E)).tangent ∞
      (fun z => (⟨z,u z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q)))
      (chartSource Q p))
    (hv : ContMDiffOn (J (E := E)) (J (E := E)).tangent ∞
      (fun z => (⟨z,v z⟩ : TangentBundle (J (E := E)) (SphereBundleTotal Q)))
      (chartSource Q p)) :
    ContMDiffOn (J (E := E)) 𝓘(ℝ) ∞
      (fun z => splitMetric Q D z (u z) (v z)) (chartSource Q p) :=
  splitMetric_eval_smoothOn_of_subset Q D p _ (Set.Subset.rfl) u v hu hv

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorMetricEvaluationSmooth
