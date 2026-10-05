import QuaternionicSymmetry.HolomorphicLineCoreProjectiveAlgebraicImage
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-! The actual selected twistor contact line has a positive power whose
complete projective embedding has a finite homogeneous polynomial image.
Properness and source application are checked; preservation by the complex
torus and smooth algebraic-scheme identification remain separate. -/
namespace QuaternionicSymmetry.ManifoldTwistorContactAlgebraicImage

open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore ManifoldTwistorPositiveContactAmple
open ManifoldTwistorPositiveRicciInput ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature HolomorphicPositiveLineKodairaSource
open ComplexProjectiveTopology ComplexProjectivePolynomialLocus
open ProjectiveAnalyticAlgebraicSources HolomorphicLineCoreProjectiveAlgebraicImage
open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_ample_contactPower_algebraic_embedding [CompactSpace M]
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    letI := B.charts
    letI := B.complexManifold
    ∃ k : ℕ, 0 < k ∧
      ∃ (d : ℕ)
        (b : Module.Basis (Fin (d + 1)) ℂ
          (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)))
        (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
          (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)),
        let f := projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
          (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)
          d b hGen
        Topology.IsEmbedding f ∧
        (∀ x : SphereBundleTotal Q, Function.Injective
          (mfderiv 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,Fin d → ℂ) f x)) ∧
        HasHomogeneousEquations (Set.range f) := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  exact ⟨k,hk,veryAmple_has_algebraic_embedding hRemmert hChow _ hVery⟩

theorem exists_normalized_contact_algebraic_embedding [Nonempty M]
    (hRemmert : RemmertProjectiveImageTheorem)
    (hChow : ChowProjectiveAnalyticTheorem)
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n B,
      letI := B.charts
      letI := B.complexManifold
      ∃ k : ℕ, 0 < k ∧
        ∃ (d : ℕ)
          (b : Module.Basis (Fin (d + 1)) ℂ
            (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
              (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                (contactLineCore P.tangent P.connection C.contact.line) k)))
          (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore P.tangent P.connection C.contact.line) k)),
          let f := projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore P.tangent P.connection C.contact.line) k) d b hGen
          Topology.IsEmbedding f ∧
          (∀ x : SphereBundleTotal P.tangent, Function.Injective
            (mfderiv 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,Fin d → ℂ) f x)) ∧
          HasHomogeneousEquations (Set.range f) := by
  letI : CompactSpace M := ⟨P.compact⟩
  obtain ⟨B,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  exact ⟨B,C,exists_ample_contactPower_algebraic_embedding
    hRemmert hChow P.tangent P.connection B C.contact hAmple⟩

end
end QuaternionicSymmetry.ManifoldTwistorContactAlgebraicImage
