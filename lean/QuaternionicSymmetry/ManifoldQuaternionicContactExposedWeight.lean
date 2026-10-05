import QuaternionicSymmetry.HolomorphicLineCoreExposedCoordinateFixedPoint
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChange
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerProjectiveEquivariance
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerGeometricWeights
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! Every integrally exposed section weight of a genuinely very ample
contact power is the scaled actual vertical weight of a torus-fixed twistor
point. Exposure is still explicit: neither full weight span nor the finite
convex-geometric exposure theorem is assumed to follow from this result. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactExposedWeight

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

theorem exposed_sectionWeight_realized
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
    (j : Fin (d + 1)) (u : Fin r → ℤ)
    (hMin : ∀ i, pairing (μ j) u ≤ pairing (μ i) u)
    (hFace : ∀ i, pairing (μ i) u = pairing (μ j) u → μ i = μ j) :
    ∃ ν ∈ actualIntegralWeights Q hR3 A, k • ν = μ j := by
  letI := B.charts
  letI := B.complexManifold
  have hMax : ∀ i, pairing (-(μ i)) u ≤ pairing (-(μ j)) u := by
    intro i
    simpa [pairing] using hMin i
  have hFace' : ∀ i, pairing (-(μ i)) u = pairing (-(μ j)) u → -(μ i) = -(μ j) := by
    intro i hi
    have he : pairing (μ i) u = pairing (μ j) u := by
      simpa [pairing] using hi
    exact congrArg Neg.neg (hFace i he)
  obtain ⟨z,hz,hs⟩ := exists_fixedPoint_of_exposed_coordinate (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)
    b hGen
    hVery
    (fun i => -(μ i)) (fun t z => sphereTotalMap Q (A.representation t) z)
    (contactPower_projectiveEvaluation_diagonal_compact Q A D B C k b hGen μ hEig)
    j u hMax hFace'
  have hz' : ∀ t, A.representation t • z = z := hz
  obtain ⟨ν,hν⟩ := exists_weightCharacter hCircle (torusVerticalCircleCharacter Q hR3 A z hz')
  refine ⟨ν,⟨z,hz',hν⟩,weight_eq_of_character_eq ?_⟩
  intro t
  apply Subtype.ext
  have hc : contactScalar Q D C.line (A.representation t) z =
      (weightCharacter ν t : ℂ) := by
    rw [contactScalar_eq_verticalScalar Q D C.line z (A.representation t) (hz t)]
    exact congrArg (fun c : Circle => (c : ℂ)) (hν t)
  rw [weightCharacter_nsmul]
  change (weightCharacter ν t : ℂ) ^ k = (weightCharacter (μ j) t : ℂ)
  rw [← hc]
  exact fixedPoint_powerScalar_eq_eigencharacter Q A D B C k
    (b j) (μ j) (fun t => hEig t j) z hz hs t

end
end QuaternionicSymmetry.ManifoldQuaternionicContactExposedWeight
