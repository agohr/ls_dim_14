import QuaternionicSymmetry.ManifoldQuaternionicContactExposedWeight
import QuaternionicSymmetry.TorusIntegralVertexExposure
import QuaternionicSymmetry.IntegralWeightDualVectorSpan
import QuaternionicSymmetry.ExtremeWeightsSpanTransfer
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerWeightSpan
import QuaternionicSymmetry.SymmetricWeightAffineSpan

/-! Full real span of the literal geometric fixed-point weights, obtained
from the SAME very ample contact power. Only vertices of its section-weight
polytope need realization. Integer exposure and projective dual signs are
handled by the imported internal proofs. No BWW restriction theorem or root
multiplicity is used. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactFixedWeightSpan

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerContinuity ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicContactPowerProjectiveEquivariance
open ManifoldQuaternionicContactPowerFixedWeights ManifoldQuaternionicContactIsotropyScalar
open ManifoldQuaternionicVerticalCircleCharacter ManifoldQuaternionicActualWeightHull
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreProjectiveBasisChange
open HolomorphicLineCoreExposedCoordinateFixedPoint HolomorphicLineCoreAmpleFiniteMap
open ProjectiveAnalyticAlgebraicSources TorusIntegralCocharacter TorusWeightSeparation
open TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M] [SecondCountableTopology M]
  [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem actualRealWeights_span_of_veryAmple_power
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hCircle : CircleCharacterSource)
    {r d : ℕ} (A : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hVery : letI := B.charts; letI := B.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    (b : letI := B.charts;
      Module.Basis (Fin (d + 1)) ℂ (PowerSections Q D B C k))
    (hGen : letI := B.charts;
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    (μ : Fin (d + 1) → Fin r → ℤ)
    (hEig : letI := B.charts; ∀ (t : Torus r) (i : Fin (d + 1)),
      contactPowerTorusRepresentation Q A D B C k t (b i) =
        (weightCharacter (μ i) t : ℂ) • b i)
    (hSpan : Submodule.span ℝ (Set.range
      (fun i => TorusFaithfulWeightSpan.integralWeightLinear (μ i))) = ⊤) :
    Submodule.span ℝ (actualRealWeights Q hR3 A) = ⊤ := by
  let U := Submodule.span ℝ (actualRealWeights Q hR3 A)
  have hVec := IntegralWeightDualVectorSpan.real_vector_span_top_of_dual_span μ hSpan
  have hVertices :
      (convexHull ℝ (Set.range (fun i => TorusIntegralVertexExposure.realWeight (μ i)))).extremePoints ℝ
        ⊆ (U : Set (Fin r → ℝ)) := by
    intro w hw
    obtain ⟨j,hj⟩ := extremePoints_convexHull_subset hw
    obtain ⟨u,hMin,hFace⟩ :=
      TorusIntegralVertexExposure.exists_integral_exposing_cocharacter μ j (by simpa only [hj] using hw)
    obtain ⟨ν,hν,hEq⟩ :=
      ManifoldQuaternionicContactExposedWeight.exposed_sectionWeight_realized
        Q hR3 hCircle A D B C k hVery b hGen μ hEig j u hMin hFace
    have hνU : (fun i => (ν i : ℝ)) ∈ U := Submodule.subset_span ⟨ν,hν,rfl⟩
    have hscaled : TorusIntegralVertexExposure.realWeight (μ j) =
        (k : ℝ) • (fun i => (ν i : ℝ)) := by
      rw [← hEq]
      ext i
      simp [TorusIntegralVertexExposure.realWeight]
    rw [← hj]
    change TorusIntegralVertexExposure.realWeight (μ j) ∈ U
    rw [hscaled]
    exact U.smul_mem (k : ℝ) hνU
  have hTop : Submodule.span ℝ (U : Set (Fin r → ℝ)) = ⊤ :=
    ExtremeWeightsSpanTransfer.span_eq_top_of_finite_extremeWeights_subset
      (Set.finite_range _) hVec hVertices
  simpa only [Submodule.span_eq] using hTop

/-- Faithfulness and ampleness of the original contact line supply full
geometric span without any supplied power, eigenbasis, or span premise. -/
theorem actualRealWeights_span_eq_top_from_sources
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : CircleCharacterSource)
    {r : ℕ} (T : ContinuousTorusAction Q r) (hFaithful : T.Faithful)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    Submodule.span ℝ (actualRealWeights Q hR3 T) = ⊤ := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery,b,μ,hEig,hSpan⟩ :=
    ManifoldQuaternionicContactPowerWeightSpan.exists_veryAmple_contactPower_realSpanning_weights
      Q hR3 hFinite hEigen hCircle T hFaithful D B C hAmple
  have hVeryKeep := hVery
  obtain ⟨d,b₀,hGen,_⟩ := hVery
  have hd : Module.finrank ℂ (PowerSections Q D B C k) = d + 1 := by
    simpa using Module.finrank_eq_card_basis b₀
  let e := finCongr hd
  let b' := b.reindex e
  let μ' : Fin (d + 1) → Fin r → ℤ := fun i => μ (e.symm i)
  have hEig' : ∀ (t : Torus r) i,
      contactPowerTorusRepresentation Q T D B C k t (b' i) =
        (weightCharacter (μ' i) t : ℂ) • b' i := by
    intro t i
    simpa only [b', μ', Module.Basis.reindex_apply] using hEig t (e.symm i)
  have hSpan' : Submodule.span ℝ (Set.range
      (fun i => TorusFaithfulWeightSpan.integralWeightLinear (μ' i))) = ⊤ := by
    have heq : Set.range (fun i => TorusFaithfulWeightSpan.integralWeightLinear (μ' i)) =
        Set.range (fun i => TorusFaithfulWeightSpan.integralWeightLinear (μ i)) := by
      exact e.symm.surjective.range_comp (fun i => TorusFaithfulWeightSpan.integralWeightLinear (μ i))
    rw [heq]
    exact hSpan
  exact actualRealWeights_span_of_veryAmple_power Q hR3 hCircle
    T D B C k hVeryKeep b' hGen μ' hEig' hSpan'

/-- Ampleness supplies finiteness of the full literal fixed-weight set.
Faithfulness is unnecessary for this conclusion. -/
theorem actualRealWeights_finite_from_sources
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : CompactTorusEigenbasisSource.KnappTorusEigenbasis)
    (hCircle : CircleCharacterSource)
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    (actualRealWeights Q hR3 T).Finite := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  obtain ⟨d,b₀,hGen,_⟩ := hVery
  obtain ⟨b,μ,hEig⟩ :=
    ManifoldQuaternionicContactPowerFromSources.exists_integral_eigenbasis_from_sources
      Q hR3 hFinite hEigen hCircle T D B C k
  exact ManifoldQuaternionicContactPowerGeometricWeights.actualRealWeights_finite
    Q hR3 T D B C k b μ hEig hGen (Nat.ne_of_gt hk)

/-- Actual antipodal symmetry upgrades real linear span to the full affine
span needed by the geometric fixed-point polytope. -/
theorem actualRealWeights_affineSpan_of_span {r : ℕ}
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (A : ContinuousTorusAction Q r) (hr : 0 < r)
    (hSpan : Submodule.span ℝ (actualRealWeights Q hR3 A) = ⊤) :
    affineSpan ℝ (actualRealWeights Q hR3 A) = ⊤ := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  have hNonempty : (actualRealWeights Q hR3 A).Nonempty := by
    by_contra h
    have hEmpty := Set.not_nonempty_iff_eq_empty.mp h
    rw [hEmpty, Submodule.span_empty] at hSpan
    exact bot_ne_top hSpan
  exact SymmetricWeightAffineSpan.affineSpan_eq_top_of_symmetric_span hNonempty
    (fun w hw => actualRealWeights_neg Q hR3 A hw) hSpan

end
end QuaternionicSymmetry.ManifoldQuaternionicContactFixedWeightSpan
