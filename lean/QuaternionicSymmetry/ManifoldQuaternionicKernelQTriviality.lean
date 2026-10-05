import QuaternionicSymmetry.ManifoldQuaternionicFixedLocalRepresentations
import QuaternionicSymmetry.ManifoldQuaternionicKernelCompactness
import QuaternionicSymmetry.ManifoldRiemannianIsometryLieInput
import QuaternionicSymmetry.ManifoldQuaternionicFixedPositiveGeometry
import QuaternionicSymmetry.ManifoldQuaternionicVerticalWeightKernel
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-! The compact connected torus-character kernel acts trivially on the
actual quaternionic coefficient plane along an entire fixed component, once
it does so at one point. All topological and Borel instances are constructed
from the actual compact-open isometry group and the compact kernel image. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicKernelQTriviality
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicIsometryCoefficients
open ManifoldQuaternionicIsometryTopology
open ManifoldQuaternionicKernelCompactness
open ManifoldQuaternionicFixedCoefficientRepresentation
open ManifoldQuaternionicFixedLocalRepresentations
open ManifoldQuaternionicRiemannianDistance
open MetricIsometryCompactness
open ManifoldRiemannianIsometryLieInput
open ManifoldRiemannianFixedComponentInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicFixedPositiveGeometry
open ManifoldQuaternionicVerticalWeightKernel
open ManifoldTwistorSphereBundle ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section
universe uK vK

variable {E : Type uK} {M : Type vK}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- BG-R3 plus actual compactness of the connected character-kernel image
propagates one-point Q-isotropy triviality over its fixed component. -/
theorem connectedKernel_coefficientAction_everywhere
    (hR3 : IsometryLieSource.{uK,vK})
    {r : ℕ} (A : ContinuousTorusAction Q r) (μ : Fin r → ℤ)
    (x : M) (hx : x ∈ ContinuousTorusAction.connectedKernelFixedSet Q A μ)
    (hOne : ∀ f ∈ ContinuousTorusAction.connectedKernelImage Q A μ,
      ∀ a : Fin 3 → ℝ, coefficientAction Q f x a = a) :
    ∀ y : FixedComponent Q
      (ContinuousTorusAction.connectedKernelImage Q A μ) x,
      ∀ f ∈ ContinuousTorusAction.connectedKernelImage Q A μ,
        ∀ a : Fin 3 → ℝ, coefficientAction Q f y.1 a = a := by
  let S := ContinuousTorusAction.connectedKernelImage Q A μ
  letI : SecondCountableTopology (QuaternionicIsometries Q) :=
    (mapPair_isEmbedding Q).secondCountableTopology
  letI : CompactSpace S :=
    isCompact_iff_compactSpace.mp (isCompact_connectedKernelImage Q A μ)
  letI : MeasurableSpace S := borel S
  letI : BorelSpace S := ⟨rfl⟩
  haveI : MeasurableMul S := inferInstance
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨V, hNorm, hSpace, hFinite, hChart,
    hManifold, hLie, hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  let y₀ : FixedComponent Q S x := ⟨x, mem_connectedComponentIn hx⟩
  have h₀ : TrivialQuaternionicIsotropy Q S x y₀ := hOne
  exact trivialQuaternionicIsotropy_everywhere Q hChart hManifold hAction
    S x y₀ h₀

/-- The actual higher-dimensional fixed component inherits a compact
connected positive quaternionic-Kähler geometry from its ambient space.
Only BG-R3 and the precisely registered T4 submanifold theorem are external
geometric inputs; the kernel's Q-triviality is propagated internally. -/
theorem connectedKernel_exists_induced_compact_positive_geometry
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hDim : Module.finrank ℝ E = 4*n)
    (hR3 : IsometryLieSource.{0,0})
    (hT4 : PositiveQuaternionicSubmanifoldSource)
    {r : ℕ} (A : ContinuousTorusAction P.tangent r) (μ : Fin r → ℤ)
    (x : M) (hx : x ∈ ContinuousTorusAction.connectedKernelFixedSet P.tangent A μ)
    (C : FixedComponentAtlas P.tangent
      (ContinuousTorusAction.connectedKernelImage P.tangent A μ) x (4*m))
    (hOne : ∀ f ∈ ContinuousTorusAction.connectedKernelImage P.tangent A μ,
      ∀ a : Fin 3 → ℝ, coefficientAction P.tangent f x a = a) :
    ∃ C' : FixedComponentAtlas P.tangent
      (ContinuousTorusAction.connectedKernelImage P.tangent A μ) x (4*m),
    letI : NeZero (4*m) := ⟨by omega⟩
    letI := C'.charts
    letI := C'.manifold
    ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin (4*m)))
        (M := FixedComponent P.tangent
          (ContinuousTorusAction.connectedKernelImage P.tangent A μ) x),
      IsInducedQuaternionicGeometry P R.toPositiveQuaternionicKahlerGeometry
        Subtype.val := by
  have hQ := connectedKernel_coefficientAction_everywhere P.tangent
    hR3 A μ x hx hOne
  exact exists_induced_compact_positive_geometry P n m hn hm hDim
    (ContinuousTorusAction.connectedKernelImage P.tangent A μ) x C hQ hT4

/-- A genuine integral vertical isotropy weight supplies both the fixed
basepoint and its one-point coefficient triviality. This directly feeds the
compact positive geometry on a compatible atlas of dimension at least
eight, selected together with the induced geometry. -/
theorem verticalWeight_exists_induced_compact_positive_geometry
    {E M : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [CompactSpace M] [T3Space M] [SecondCountableTopology M]
    [PreconnectedSpace M] [Nonempty M]
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hDim : Module.finrank ℝ E = 4*n)
    (hR3 : IsometryLieSource.{0,0})
    (hT4 : PositiveQuaternionicSubmanifoldSource)
    {r : ℕ} (A : ContinuousTorusAction P.tangent r)
    (z : SphereBundleTotal P.tangent)
    (hz : ∀ t, A.representation t • z = z)
    (μ : Fin r → ℤ)
    (hweight : HasVerticalWeight P.tangent A z hz μ)
    (C : FixedComponentAtlas P.tangent
      (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1 (4*m)) :
    ∃ C' : FixedComponentAtlas P.tangent
      (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1 (4*m),
    letI : NeZero (4*m) := ⟨by omega⟩
    letI := C'.charts
    letI := C'.manifold
    ∃ R : CompactConnectedPositiveQuaternionicKahlerGeometry
        (E := EuclideanSpace ℝ (Fin (4*m)))
        (M := FixedComponent P.tangent
          (ContinuousTorusAction.connectedKernelImage P.tangent A μ) z.1),
      IsInducedQuaternionicGeometry P R.toPositiveQuaternionicKahlerGeometry
        Subtype.val := by
  exact connectedKernel_exists_induced_compact_positive_geometry P n m
    hn hm hDim hR3 hT4 A μ z.1
      (base_mem_connectedKernelFixedSet P.tangent A z hz μ) C
      (connectedKernel_coefficient_trivial P.tangent A z hz μ hweight)

end
end QuaternionicSymmetry.ManifoldQuaternionicKernelQTriviality
