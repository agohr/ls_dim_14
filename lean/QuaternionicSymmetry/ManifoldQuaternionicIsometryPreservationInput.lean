import QuaternionicSymmetry.ManifoldPositiveQuaternionicKahlerGeometry
import QuaternionicSymmetry.ManifoldQuaternionicFullIsometryEmbedding

/-! Conditional full-group comparisons. Full metric isometries need not
preserve the chosen quaternionic bundle. The hypothesis in this module is
therefore local to one supplied geometry, and is not a literature source.
The final classification uses the closed quaternionic-isometry subgroup
instead; see `ManifoldQuaternionicIsometryClosedSubgroup`. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicFundamentalSymmetry
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicRiemannianDistance
open ManifoldRiemannianMyersSteenrodInput
open ManifoldQuaternionicIsometryTopology MetricIsometryCompactness
open scoped Manifold ContDiff
noncomputable section
universe uPres vPres

variable {E : Type uPres} {M : Type vPres}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T3Space M] [SecondCountableTopology M]
/-- An explicit additional hypothesis on one tangent geometry. This is
not asserted for all positive quaternionic-Kähler manifolds. -/
def FullMetricSpanPreservation
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞)) : Prop :=
  ∀ f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞,
    PreservesMetric Q f → PreservesSpanForward Q f

variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
  (hQ : FullMetricSpanPreservation P.tangent)

include n hn hDim hQ

theorem preservesSpan_of_assumption
    (f : Diffeomorph 𝓘(ℝ,E) 𝓘(ℝ,E) M M ∞)
    (hf : PreservesMetric P.tangent f) : PreservesSpan P.tangent f :=
  ⟨hQ f hf,
    hQ f.symm (metric_symm P.tangent hf)⟩

variable [CompactSpace M] [PreconnectedSpace M] [Nonempty M]

theorem toFullMetricIsometry_surjective
    (hMS : MyersSteenrodSource.{uPres,vPres}) :
    Function.Surjective (toFullMetricIsometry P.tangent) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  intro e
  obtain ⟨f, hf, he⟩ := hMS P.tangent e
  refine ⟨⟨f, hf, preservesSpan_of_assumption P n hn hDim hQ f hf⟩, ?_⟩
  apply IsometryEquiv.ext
  intro x
  exact congrFun he x

/-- The actual quaternionic-preserving isometry group is the entire
distance-isometry group, under explicit preservation for this geometry and Myers–Steenrod. -/
def fullMetricIsometryEquiv (hMS : MyersSteenrodSource.{uPres,vPres}) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    QuaternionicIsometries P.tangent ≃* (M ≃ᵢ M) :=
  MulEquiv.ofBijective (toFullMetricIsometry P.tangent)
    ⟨toFullMetricIsometry_injective P.tangent,
      toFullMetricIsometry_surjective P n hn hDim hQ hMS⟩

theorem fullMetricIsometryEquiv_symm_continuous
    (hMS : MyersSteenrodSource.{uPres,vPres}) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    Continuous (fullMetricIsometryEquiv P n hn hDim hQ hMS).symm := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  let e := fullMetricIsometryEquiv P n hn hDim hQ hMS
  apply (mapPair_isEmbedding P.tangent).isInducing.continuous_iff.mpr
  have hp : (mapPair P.tangent) ∘ e.symm =
      isometryEquivToContinuousPairs (X := M) := by
    funext g
    rw [Function.comp_apply, ← toFullMetricIsometry_pair]
    change isometryEquivToContinuousPairs (e (e.symm g)) = _
    rw [e.apply_symm_apply]
  change Continuous ((mapPair P.tangent) ∘ e.symm)
  rw [hp]
  exact isometryEquivToContinuousPairs_continuous (X := M)

/-- The group identification respects the actual, independently constructed
compact-open topologies on both sides. -/
def fullMetricIsometryHomeomorph (hMS : MyersSteenrodSource.{uPres,vPres}) :
    letI : MetricSpace M := riemannianMetricSpace P.tangent
    letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
    QuaternionicIsometries P.tangent ≃ₜ (M ≃ᵢ M) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  exact {
    toEquiv := (fullMetricIsometryEquiv P n hn hDim hQ hMS).toEquiv
    continuous_toFun := toFullMetricIsometry_continuous P.tangent
    continuous_invFun := fullMetricIsometryEquiv_symm_continuous P n hn hDim hQ hMS }

theorem quaternionicIsometries_compactSpace
    (hMS : MyersSteenrodSource.{uPres,vPres}) :
    CompactSpace (QuaternionicIsometries P.tangent) := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  let e := fullMetricIsometryHomeomorph P n hn hDim hQ hMS
  have h := isCompact_univ.image e.symm.continuous
  rw [Set.image_univ, Set.range_eq_univ.mpr e.symm.surjective] at h
  exact isCompact_univ_iff.mp h

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput
