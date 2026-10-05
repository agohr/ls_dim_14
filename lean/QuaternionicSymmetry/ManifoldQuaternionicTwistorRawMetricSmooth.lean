import QuaternionicSymmetry.ManifoldQuaternionicTwistorLocalMetricIdentification

/-! Joint smoothness of the genuine fixed-chart split metric evaluation on
two raw twistor tangent vectors over the same chart domain. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorRawMetricSmooth

open ManifoldQuaternionicTwistorLocalMetricSmooth
open ManifoldQuaternionicTwistorLocalMetricIdentification
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev V := Fin 3 → ℝ

private def rawAmbientPair (r t : X (E := E)) :
    (E × V) × ((E × V) × (E × V)) :=
  ((r.1.1,(coefficientSphereHomeomorph.symm r.2.1).1),
    (r.1.2,sphereTangentAmbient r.2),
    (t.1.2,sphereTangentAmbient t.2))

private theorem rawAmbientPair_smooth :
    ContMDiff ((IX (E := E)).prod (IX (E := E)))
      𝓘(ℝ,(E × V) × ((E × V) × (E × V))) ∞
      (fun rt : X (E := E) × X (E := E) => rawAmbientPair rt.1 rt.2) := by
  have hR : ContMDiff ((IX (E := E)).prod (IX (E := E)))
      (IX (E := E)) ∞ (fun rt : X (E := E) × X (E := E) => rt.1) := contMDiff_fst
  have hT : ContMDiff ((IX (E := E)).prod (IX (E := E)))
      (IX (E := E)) ∞ (fun rt : X (E := E) × X (E := E) => rt.2) := contMDiff_snd
  have hy : ContMDiff (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun r : X (E := E) => r.1.1) := contMDiff_fst.comp contMDiff_fst
  have hu : ContMDiff (IX (E := E)) 𝓘(ℝ,E) ∞
      (fun r : X (E := E) => r.1.2) := contMDiff_snd.comp contMDiff_fst
  have hs : ContMDiff (IX (E := E)) (𝓡 2) ∞
      (fun r : X (E := E) => r.2.1) :=
    (Bundle.contMDiff_proj (TangentSpace (𝓡 2))).comp contMDiff_snd
  have hcoef0 : ContMDiff (𝓡 2) 𝓘(ℝ,V) ∞
      (fun s : geometricSphere => (coefficientSphereHomeomorph.symm s).1) := by
    convert ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).comp
      (contMDiff_coe_sphere (n := 2) (E := EuclideanThree)) using 1
  have hcoef : ContMDiff (IX (E := E)) 𝓘(ℝ,V) ∞
      (fun r : X (E := E) => (coefficientSphereHomeomorph.symm r.2.1).1) :=
    hcoef0.comp hs
  have hv : ContMDiff (IX (E := E)) 𝓘(ℝ,V) ∞
      (fun r : X (E := E) => sphereTangentAmbient r.2) :=
    sphereTangentAmbient_smooth.comp contMDiff_snd
  exact ((hy.comp hR).prodMk_space (hcoef.comp hR)).prodMk_space
    (((hu.comp hR).prodMk_space (hv.comp hR)).prodMk_space
      ((hu.comp hT).prodMk_space (hv.comp hT)))

theorem ambientMetricRaw_smooth (p : M) :
    ContMDiffOn ((IX (E := E)).prod (IX (E := E))) 𝓘(ℝ) ∞
      (fun rt : X (E := E) × X (E := E) => ambientMetricRaw Q D p rt.1 rt.2)
      (localDomain (E := E) p ×ˢ localDomain (E := E) p) := by
  have hmaps : Set.MapsTo
      (fun rt : X (E := E) × X (E := E) => rawAmbientPair rt.1 rt.2)
      (localDomain (E := E) p ×ˢ localDomain (E := E) p)
      (((extChartAt 𝓘(ℝ,E) p).target ×ˢ Set.univ) ×ˢ Set.univ) := by
    intro rt hrt
    exact ⟨⟨hrt.1, Set.mem_univ _⟩, Set.mem_univ _⟩
  exact (ambientLocalMetric_smooth Q D p).contMDiffOn.comp
    rawAmbientPair_smooth.contMDiffOn hmaps

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorRawMetricSmooth
