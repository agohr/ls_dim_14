import QuaternionicSymmetry.ManifoldQuaternionicFixedLocalCoefficientContinuous
import QuaternionicSymmetry.CompactRepresentationLocalTriviality
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual continuous local rank-three representations along a fixed
component. A chart center is chosen only locally; no global adapted frame is
assumed. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedLocalRepresentations
open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicFixedCoefficientRepresentation
open ManifoldQuaternionicFixedLocalCoefficientContinuous
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldRiemannianFixedComponentInput
open VectorBundleFrameTransitions.QuaternionicFrameReduction
open CompactRepresentationLocalTriviality
open scoped Manifold ContDiff Topology
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual fixed-chart coefficient representation, regarded as bounded
operators on the finite-dimensional rank-three coordinate space. -/
def localCLMRepresentation (S : Subgroup (QuaternionicIsometries Q))
    (x c : M) (y : fixedChartDomain Q S x c) :
    S →* ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) where
  toFun f := LinearMap.toContinuousLinearMap
    (fixedChartCoefficientRepresentation Q S x (achart E c) y.1 y.2 f)
  map_one' := by
    change LinearMap.toContinuousLinearMap
      (fixedChartCoefficientRepresentation Q S x (achart E c) y.1 y.2 (1 : S)) = 1
    rw [map_one]
    rfl
  map_mul' f g := by
    change LinearMap.toContinuousLinearMap
      (fixedChartCoefficientRepresentation Q S x (achart E c) y.1 y.2 (f * g)) =
      LinearMap.toContinuousLinearMap
        (fixedChartCoefficientRepresentation Q S x (achart E c) y.1 y.2 f) *
      LinearMap.toContinuousLinearMap
        (fixedChartCoefficientRepresentation Q S x (achart E c) y.1 y.2 g)
    rw [map_mul]
    ext a i
    rfl

theorem localCLMRepresentation_apply
    (S : Subgroup (QuaternionicIsometries Q)) (x c : M)
    (y : fixedChartDomain Q S x c) (f : S) (a : Fin 3 → ℝ) :
    localCLMRepresentation Q S x c y f a =
      fixedChartCoefficientRepresentation Q S x (achart E c)
        y.1 y.2 f a := rfl

/-- The genuine local fixed-component isotropy representation is jointly
continuous in the group element and base point, in the operator norm. The
finite-dimensional operator topology is recovered from its three columns. -/
theorem continuousAt_localCLMRepresentation
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (S : Subgroup (QuaternionicIsometries Q)) (x c : M)
    (hc : c ∈ fixedPoints Q S)
    (f₀ : S) (y₀ : fixedChartDomain Q S x c) :
    ContinuousAt (fun p : S × fixedChartDomain Q S x c =>
      localCLMRepresentation Q S x c p.2 p.1) (f₀,y₀) := by
  let U := fixedChartDomain Q S x c
  let e := ContinuousLinearEquiv.piRing (𝕜 := ℝ)
    (E := Fin 3 → ℝ) (Fin 3)
  have hcol (a : Fin 3 → ℝ) : ContinuousAt
      (fun p : S × U => localCLMRepresentation Q S x c p.2 p.1 a)
      (f₀,y₀) := by
    have h := continuousAt_localCoefficientRotation_onFixedChart Q
      hChart hManifold hAction S x c hc a f₀ y₀
    have heq : (fun p : S × U =>
        localCLMRepresentation Q S x c p.2 p.1 a) =
        (fun p : S × U =>
          ManifoldQuaternionicIsometryLocalDerivative.localCoefficientRotation
            Q p.1.1 c p.2.1.1 a) := by
      funext p
      exact (localCLMRepresentation_apply Q S x c p.2 p.1 a).trans
        (fixedChartRepresentation_eq_localCoefficientRotation Q S x c hc
          p.2.1 p.2.2 p.2.2 p.1 a)
    simpa only [heq] using h
  have hPi : ContinuousAt (fun p : S × U =>
      fun j : Fin 3 => localCLMRepresentation Q S x c p.2 p.1
        (Pi.single j (1 : ℝ))) (f₀,y₀) :=
    continuousAt_pi.mpr (fun j => hcol (Pi.single j 1))
  have hE : ContinuousAt (fun p : S × U =>
      e.symm (fun j : Fin 3 => localCLMRepresentation Q S x c p.2 p.1
        (Pi.single j (1 : ℝ)))) (f₀,y₀) :=
    e.symm.continuous.continuousAt.comp hPi
  convert hE using 1
  · funext p
    apply e.injective
    rw [e.apply_symm_apply]
    ext j i
    simp [e, ContinuousLinearEquiv.piRing, LinearEquiv.piRing_apply,
      LinearEquiv.trans_apply]

/-- Local presentations of the intrinsic trivial quaternionic-isotropy
predicate in actual fixed-point charts. Every local representation is an
actual derivative action; the chart center varies with the point. -/
theorem localPresentations_trivialQuaternionicIsotropy
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (S : Subgroup (QuaternionicIsometries Q)) (x : M)
    [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    [MeasurableMul S] :
    LocalPresentations (G := S)
      (A := ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)))
      (TrivialQuaternionicIsotropy Q S x) := by
  intro y
  let c : M := y.1
  let U := fixedChartDomain Q S x c
  have hc : c ∈ fixedPoints Q S := fixedComponent_mem_fixedPoints Q S x y
  have hy : y ∈ U := mem_chart_source E c
  refine ⟨U, isOpen_fixedChartDomain Q S x c, hy,
    localCLMRepresentation Q S x c, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    rintro ⟨f,z⟩
    exact continuousAt_localCLMRepresentation Q hChart hManifold hAction
      S x c hc f z
  · intro z
    rw [trivial_iff_fixedChartRepresentation_one Q S x (achart E c)
      z.1 z.2]
    constructor
    · intro hz f
      apply ContinuousLinearMap.ext
      intro a
      rw [localCLMRepresentation_apply, hz f]
      rfl
    · intro hz f
      apply LinearMap.ext
      intro a
      have h := congrArg
        (fun T : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) => T a) (hz f)
      simpa only [localCLMRepresentation_apply] using h

/-- Intrinsic triviality at one point propagates over the entire actual
connected fixed component. There is no global frame choice or independent
continuity hypothesis. -/
theorem trivialQuaternionicIsotropy_everywhere
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hChart :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      ChartedSpace V (M ≃ᵢ M))
    (hManifold :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M))
    (hAction :
      letI : MetricSpace M := riemannianMetricSpace Q
      letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
      letI : ChartedSpace V (M ≃ᵢ M) := hChart
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : (M ≃ᵢ M) × M => p.1 p.2))
    (S : Subgroup (QuaternionicIsometries Q)) (x : M)
    [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    [MeasurableMul S]
    (y₀ : FixedComponent Q S x)
    (hy₀ : TrivialQuaternionicIsotropy Q S x y₀) :
    ∀ y : FixedComponent Q S x, TrivialQuaternionicIsotropy Q S x y := by
  letI : PreconnectedSpace (FixedComponent Q S x) :=
    Subtype.preconnectedSpace isPreconnected_connectedComponentIn
  exact everywhere_of_localPresentations (G := S)
    (A := ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)))
    (TrivialQuaternionicIsotropy Q S x)
    (localPresentations_trivialQuaternionicIsotropy Q hChart hManifold hAction S x)
    y₀ hy₀

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedLocalRepresentations
