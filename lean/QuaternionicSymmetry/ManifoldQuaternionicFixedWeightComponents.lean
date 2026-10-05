import QuaternionicSymmetry.ManifoldQuaternionicFixedWeightLocalConstancy
import QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFromSources

/-! The vertical character is constant along every connected full-torus
fixed component. This follows from local eigenbasis nonvanishing and the
genuine connected-component topology, not from a supplied component weight.
The ample-contact version constructs its generating power and eigenbasis
from the existing general source inputs. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicFixedWeightComponents

open ManifoldQuaternionicFixedWeightLocalConstancy ManifoldQuaternionicTorusAction
open ManifoldQuaternionicVerticalCircleCharacter ManifoldQuaternionicTorusFixedComplexComponent
open ManifoldQuaternionicTwistorLiftedFixedSet ManifoldQuaternionicContactPowerFromSources
open ManifoldQuaternionicContactPowerWeights ManifoldQuaternionicContactPowerContinuity
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
  (hCircle : TorusCharacterInput.CircleCharacterSource)
  {r : ℕ} (T : ContinuousTorusAction Q r)

theorem character_eq_on_preconnected_fixed_set
    (hlc : IsLocallyConstant (fixedPointWeight Q hR3 hCircle T))
    (Y : Set (SphereBundleTotal Q)) (hY : IsPreconnected Y)
    (hFixed : ∀ z ∈ Y, ∀ t, T.representation t • z = z)
    (z w : Y) (t : Torus r) :
    torusVerticalCircleCharacter Q hR3 T z.1 (hFixed z.1 z.2) t =
      torusVerticalCircleCharacter Q hR3 T w.1 (hFixed w.1 w.2) t := by
  letI : PreconnectedSpace Y := Subtype.preconnectedSpace hY
  let f : Y → FixedTwistor Q T := fun y => ⟨y.1,hFixed y.1 y.2⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have heq := (hlc.comp_continuous hf).apply_eq_of_preconnectedSpace z w
  rw [fixedPointWeight_spec Q hR3 hCircle T ⟨z.1,hFixed z.1 z.2⟩,
    fixedPointWeight_spec Q hR3 hCircle T ⟨w.1,hFixed w.1 w.2⟩]
  exact congrArg (fun ν => weightCharacter ν t) heq

theorem character_eq_on_component
    (hlc : IsLocallyConstant (fixedPointWeight Q hR3 hCircle T))
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (w : SphereBundleTotal Q) (hw : w ∈ component Q T z)
    (hwFixed : ∀ t, T.representation t • w = w) (t : Torus r) :
    torusVerticalCircleCharacter Q hR3 T w hwFixed t =
      torusVerticalCircleCharacter Q hR3 T z hz t := by
  have hzSet : z ∈ fixedSpherePoints Q T.imageSubgroup :=
    (mem_fixedSpherePoints_iff_torus Q T z).mpr hz
  have hFixed : ∀ y ∈ component Q T z, ∀ t, T.representation t • y = y := by
    intro y hy
    exact (mem_fixedSpherePoints_iff_torus Q T y).mp
      (connectedComponentIn_subset _ _ hy)
  exact character_eq_on_preconnected_fixed_set Q hR3 hCircle T hlc
    (component Q T z) isPreconnected_connectedComponentIn hFixed
    ⟨w,hw⟩ ⟨z,mem_connectedComponentIn hzSet⟩ t

include hCircle in
theorem character_eq_on_component_of_ample
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (z : SphereBundleTotal Q) (hz : ∀ t, T.representation t • z = z)
    (w : SphereBundleTotal Q) (hw : w ∈ component Q T z)
    (hwFixed : ∀ t, T.representation t • w = w) (t : Torus r) :
    torusVerticalCircleCharacter Q hR3 T w hwFixed t =
      torusVerticalCircleCharacter Q hR3 T z hz t := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  obtain ⟨b,μ,hμ⟩ :=
    exists_integral_eigenbasis_from_sources Q hR3 hFinite hEigen hCircle T D B C k
  obtain ⟨d,b',hGen,hEmbedding⟩ := hVery
  have hlc := fixedPointWeight_isLocallyConstant Q hR3 hCircle T D B C k
    b μ hμ hGen (Nat.ne_of_gt hk)
  exact character_eq_on_component Q hR3 hCircle T hlc z hz w hw hwFixed t

end
end QuaternionicSymmetry.ManifoldQuaternionicFixedWeightComponents
