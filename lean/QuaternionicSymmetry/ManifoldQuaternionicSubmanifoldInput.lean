import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
import QuaternionicSymmetry.ManifoldQuaternionicSpanSymmetry

/-! The quaternionic-submanifold input already registered under T4:
Alekseevsky–Marchiafava (2001), proof of Corollary 1.10, p.878, says that
a quaternionic submanifold with the induced metric is quaternionic Kähler
with the same reduced scalar curvature. This interface keeps the genuine
embedded inclusion, invariant tangent range, induced metric and restricted
endomorphism span. Only dimensions at least eight are included here. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicSubmanifoldInput

open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicSpanSymmetry
open scoped Manifold ContDiff
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

/-- The ordinary quaternionic submanifold condition on the genuine
range of the inclusion's differential. -/
def QuaternionicTangentRange
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (ι : N → M) : Prop :=
  ∀ x B, B ∈ tangentSpan P.tangent (ι x) →
    ∀ v, v ∈ LinearMap.range (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x).toLinearMap →
      B v ∈ LinearMap.range (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x).toLinearMap

/-- The induced metric and quaternionic structure, not merely an
unrelated positive geometry on the same underlying type. -/
def IsInducedQuaternionicGeometry
    (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
    (ι : N → M) : Prop :=
  (∀ x v w, R.tangent.tangentMetricForm x v w =
    P.tangent.tangentMetricForm (ι x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x w)) ∧
  (∀ x A, A ∈ tangentSpan R.tangent x ↔
    ∃ B, B ∈ tangentSpan P.tangent (ι x) ∧ ∀ v,
      mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x (A v) =
        B (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v))

/-- A compatible choice of sufficiently small submanifold charts. The
inclusion and its tangent image are unchanged. Adapted quaternionic frames
need only exist on this atlas, not on every chart of the supplied atlas. -/
structure CompatibleSubmanifoldAtlas (original : ChartedSpace F N) (ι : N → M) where
  charts : ChartedSpace F N
  atlas_compatible : letI := original
    ∀ e ∈ charts.atlas, e ∈ IsManifold.maximalAtlas 𝓘(ℝ,F) ∞ N
  manifold : letI := charts; IsManifold 𝓘(ℝ,F) ∞ N
  inclusion_smooth : letI := charts; ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι
  inclusion_injective_derivative : letI := charts
    ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x)
  tangent_range :
    let oldRange := letI := original; fun x =>
      LinearMap.range (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x).toLinearMap
    letI := charts
    ∀ x, LinearMap.range (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x).toLinearMap = oldRange x

/-- T4's general quaternionic-submanifold result, weakened to its positive
scalar-curvature consequence. It contains neither fixed-set geometry nor
a dimension decrease. Those are checked before applying this source. -/
def PositiveQuaternionicSubmanifoldSource : Prop :=
  ∀ {E F M N : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ F] [Nontrivial F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
    [T3Space M] [SecondCountableTopology M]
    [T3Space N] [SecondCountableTopology N],
    ∀ (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
      (n m : ℕ), 2 ≤ n → 2 ≤ m →
      Module.finrank ℝ E = 4*n → Module.finrank ℝ F = 4*m →
    ∀ ι : N → M, ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ ι → Topology.IsEmbedding ι →
      (∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x)) →
      QuaternionicTangentRange (F := F) P ι →
      ∃ B : CompatibleSubmanifoldAtlas (E := E) (F := F) inferInstance ι,
        letI := B.charts
        letI := B.manifold
        ∃ R : PositiveQuaternionicKahlerGeometry (E := F) (M := N),
          IsInducedQuaternionicGeometry P R ι

end
end QuaternionicSymmetry.ManifoldQuaternionicSubmanifoldInput
