import QuaternionicSymmetry.ManifoldQuaternionicIsometryPreservationInput
import QuaternionicSymmetry.ManifoldRiemannianTwoTorus
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-! The actual two-torus promised by the symmetry bound, transferred to
quaternionic isometries using precisely registered general background.
No rank number is attached to the manifold as an additional datum. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTwoTorus

open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicIsometryPreservationInput
open ManifoldRiemannianMyersSteenrodInput ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldQuaternionicTorusAction ManifoldQuaternionicKillingFields
open CompactLieTorusInputs
open scoped Manifold ContDiff
noncomputable section
universe uTwo vTwo

variable {E : Type uTwo} {M : Type vTwo}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))

theorem has_two_torus_of_killing_dimension
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4 * n)
    (hQ : FullMetricSpanPreservation P.tangent)
    (hMS : MyersSteenrodSource.{uTwo,vTwo})
    (hR3 : IsometryLieSource.{uTwo,vTwo})
    (hR4 : KillingLieSource.{uTwo,vTwo})
    (hTorus : MaximalTorusSource.{0,vTwo})
    (hRankOne : CompactRankOneDimensionSource.{0,vTwo})
    (hdim : 3 < killingDimension P.tangent) :
    HasTorusRankAtLeast P.tangent 2 := by
  letI : MetricSpace M := riemannianMetricSpace P.tangent
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  obtain ⟨T⟩ :=
    ManifoldRiemannianTwoTorus.full_isometry_two_torus_of_killing_dimension
      P.tangent hR3 hR4 hTorus hRankOne hdim
  let e := fullMetricIsometryEquiv P n hn hDim hQ hMS
  let ρ := e.symm.toMonoidHom.comp T.hom
  have hρ : Continuous ρ :=
    (fullMetricIsometryEquiv_symm_continuous P n hn hDim hQ hMS).comp
      T.continuous_hom
  refine ⟨⟨ρ, ?_⟩, e.symm.injective.comp T.injective_hom⟩
  exact (ManifoldQuaternionicIsometryTopology.continuous_action P.tangent).comp
    ((hρ.comp continuous_fst).prodMk continuous_snd)

end
end QuaternionicSymmetry.ManifoldQuaternionicTwoTorus
