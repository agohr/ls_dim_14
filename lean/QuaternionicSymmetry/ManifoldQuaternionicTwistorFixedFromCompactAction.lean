import QuaternionicSymmetry.ManifoldQuaternionicActualTwistorJointSmooth
import QuaternionicSymmetry.ManifoldQuaternionicIsometryClosedFromAction
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.CompactSubgroupFixedComponent
import QuaternionicSymmetry.ManifoldQuaternionicTwistorLiftedFixedSet

/-! Compact-action fixed components for the actual lifted twistor action. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedFromCompactAction
open Manifold ManifoldQuaternionicSpanSymmetry ManifoldRiemannianIsometryLieInput
open ManifoldQuaternionicRiemannianDistance MetricIsometryCompactness
open ManifoldQuaternionicFullIsometryEmbedding
open ManifoldQuaternionicIsometryClosedSubgroup
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorIsometryDiffeomorph
open ManifoldRiemannianFixedComponentGenericInput ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section
variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
private abbrev J := 𝓘(ℝ,E).prod (𝓡 2)

/-- This is a proved intermediate conclusion, not a literature field. -/
def LiftedFixedComponents : Prop :=
  ∀ (S : Subgroup (QuaternionicIsometries Q)) (z : SphereBundleTotal Q),
    z ∈ fixedSpherePoints Q S →
      ∃ k : ℕ, Nonempty (FixedComponentAtlas (J (E := E)) (liftedSet Q S) z k)

variable [CompactSpace M] [T3Space M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]

lemma exists_smooth_lift_atlas
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem) :
    ∃ (d : ℕ) (c : ChartedSpace (Fin d → ℝ) (QuaternionicIsometries Q)),
      letI := c
      IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) ∧
      LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) ∧
      ContMDiff ((𝓘(ℝ,Fin d → ℝ)).prod (J (E := E))) (J (E := E)) ∞
        (fun p : QuaternionicIsometries Q × SphereBundleTotal Q => sphereTotalMap Q p.1 p.2) := by
  letI : MetricSpace M := riemannianMetricSpace Q
  letI : TopologicalSpace (M ≃ᵢ M) := isometryEquivTopology (X := M)
  letI : CompactSpace (M ≃ᵢ M) := isometryEquiv_compactSpace (X := M)
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hAction⟩ := hR3 Q
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℝ V := hSpace
  letI : FiniteDimensional ℝ V := hFinite
  letI : ChartedSpace V (M ≃ᵢ M) := hChart
  letI : IsManifold 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ (M ≃ᵢ M) := hLie
  have hpairs : Topology.IsEmbedding (isometryEquivPairsEquiv (X := M)) :=
    ⟨⟨rfl⟩,(isometryEquivPairsEquiv (X := M)).injective⟩
  letI : T2Space (M ≃ᵢ M) := hpairs.t2Space
  letI : SecondCountableTopology (M ≃ᵢ M) :=
    ChartedSpace.secondCountable_of_sigmaCompact V (M ≃ᵢ M)
  have hR3' : IsometryLieConclusion Q :=
    ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hAction⟩
  have hclosed : Topology.IsClosedEmbedding (toFullMetricIsometry Q) :=
    ⟨toFullMetricIsometry_isEmbedding Q,isClosed_range_toFullMetricIsometry_of_isometryLie Q hR3'⟩
  obtain ⟨d,⟨a⟩⟩ := hLee (E := V) (toFullMetricIsometry Q) hclosed
  letI : ChartedSpace (Fin d → ℝ) (QuaternionicIsometries Q) := a.charts
  letI : IsManifold 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) := a.manifold
  letI : LieGroup 𝓘(ℝ,Fin d → ℝ) ∞ (QuaternionicIsometries Q) := a.lieGroup
  refine ⟨d,a.charts,a.manifold,a.lieGroup,?_⟩
  exact ManifoldQuaternionicActualTwistorJointSmooth.joint_smooth Q
    hChart hManifold hLie hAction hR3
    (ManifoldImmersionSmooth.smoothEmbedding_contMDiff a.smoothEmbedding)

lemma liftedFixedComponents
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hLee : GeneralClosedSubgroupLieSource.LeeClosedEmbeddingTheorem) :
    LiftedFixedComponents Q := by
  intro S z hz
  letI : CompactSpace (QuaternionicIsometries Q) :=
    quaternionicIsometries_compactSpace_of_isometryLie Q (hR3 Q)
  obtain ⟨d,c,hm,hl,ha⟩ := exists_smooth_lift_atlas Q hR3 hLee
  letI := c
  letI := hm
  letI := hl
  letI : T2Space (QuaternionicIsometries Q) := inferInstance
  letI : SecondCountableTopology (QuaternionicIsometries Q) :=
    ChartedSpace.secondCountable_of_sigmaCompact (Fin d → ℝ) (QuaternionicIsometries Q)
  let a : QuaternionicIsometries Q × SphereBundleTotal Q → SphereBundleTotal Q :=
    fun p => sphereTotalMap Q p.1 p.2
  have hsets : fixedPoints (J (E := E)) (liftedSet Q S) =
      CompactSubgroupFixedComponent.fixedSet a S := by
    ext y
    exact mem_fixedSpherePoints_iff Q S y
  have hza : z ∈ CompactSubgroupFixedComponent.fixedSet a S :=
    (mem_fixedSpherePoints_iff Q S z).mp hz
  obtain ⟨k,⟨B⟩⟩ := CompactSubgroupFixedComponent.exists_atlas hLee a ha
    (fun y => one_smul (QuaternionicIsometries Q) y) (fun g h y => (mul_smul g h y).symm) S z hza
  have htransport : ∀ (T : Set (SphereBundleTotal Q)),
      T = CompactSubgroupFixedComponent.fixedSet a S →
      ∃ (c : ChartedSpace (EuclideanSpace ℝ (Fin k)) (↥(connectedComponentIn T z))),
        letI := c
        IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) ∞ (↥(connectedComponentIn T z)) ∧
        ContMDiff 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E)) ∞
          (Subtype.val : (↥(connectedComponentIn T z)) → SphereBundleTotal Q) ∧
        (∀ y, Function.Injective (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
          (Subtype.val : (↥(connectedComponentIn T z)) → SphereBundleTotal Q) y)) ∧
        ∀ y v, v ∈ LinearMap.range (mfderiv 𝓘(ℝ,EuclideanSpace ℝ (Fin k)) (J (E := E))
          (Subtype.val : (↥(connectedComponentIn T z)) → SphereBundleTotal Q) y).toLinearMap ↔
          ∀ g ∈ S, mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q g) y.1 v = v := by
    intro T hT
    subst T
    exact ⟨B.charts,B.manifold,B.inclusion_smooth,B.inclusion_injective_derivative,B.tangent_eq⟩
  obtain ⟨c,hm,hi,hdi,ht⟩ := htransport _ hsets
  refine ⟨k,⟨⟨c,hm,hi,hdi,?_⟩⟩⟩
  intro y v
  rw [ht y v]
  change (∀ g ∈ S, mfderiv (J (E := E)) (J (E := E)) (sphereTotalMap Q g) y.1 v = v) ↔ _
  constructor
  · intro h f hf
    obtain ⟨g,rfl⟩ := hf
    simpa only [eqRec_eq_cast,cast_eq] using h g.1 g.2
  · intro h g hg
    have hh := h (realLift Q g) ⟨⟨g,hg⟩,rfl⟩
    simpa only [eqRec_eq_cast,cast_eq] using hh

end
end QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedFromCompactAction
