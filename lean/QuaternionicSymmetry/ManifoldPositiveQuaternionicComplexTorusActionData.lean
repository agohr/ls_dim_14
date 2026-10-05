import QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusActionData
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-! Source-only selected normalized positive quaternionic-Kähler twistor
with the same very ample contact power, genuine section eigenbasis, integral
weights, and complex-torus point action retained in one witness package. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexTorusActionData

open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerComplexTorusActionData
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerWeights
open ManifoldTwistorPositiveContactAmple ManifoldTwistorPositiveRicciInput
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldQuaternionicScalarCurvature
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicPositiveLineKodairaSource ProjectiveAnalyticAlgebraicSources
open CompactTorusEigenbasisSource TorusCharacterInput
open TorusLaurentRepresentation ComplexProjectiveDiagonalAction
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [Nonempty M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_normalized_twistor_complex_torus_action_with_data
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hKodaira : PositiveHermitianLineAmpleTheorem.{0,0,0})
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      localScalarCurvature P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2))
    {r : ℕ} (A : ContinuousTorusAction P.tangent r) :
    ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : NondegenerateHolomorphicContactData P.tangent P.connection n B,
        letI := B.charts
        letI := B.complexManifold
        ∃ k : ℕ, 0 < k ∧
          VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore P.tangent P.connection C.contact.line) k) ∧
          ∃ (d : ℕ)
            (b : Module.Basis (Fin (d + 1)) ℂ
              (PowerSections P.tangent P.connection B C.contact k))
            (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
              (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                (contactLineCore P.tangent P.connection C.contact.line) k))
            (μ : Fin (d + 1) → Fin r → ℤ)
            (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent)),
              (∀ (t : Torus r) (i : Fin (d + 1)),
                contactPowerTorusRepresentation P.tangent A P.connection
                  B C.contact k t (b i) =
                  (weightCharacter (μ i) t : ℂ) • b i) ∧
              (∀ (t : Torus r) (z : SphereBundleTotal P.tangent),
                ρ (compactInclusion r t) z =
                  sphereTotalMap P.tangent (A.representation t) z) ∧
              ∀ (w : ComplexTorus r) (z : SphereBundleTotal P.tangent),
                projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
                  (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                    (contactLineCore P.tangent P.connection C.contact.line) k)
                  d b hGen (ρ w z) =
                projectiveAction (fun i => -(μ i)) w
                  (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
                    (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                      (contactLineCore P.tangent P.connection C.contact.line) k)
                    d b hGen z) := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  obtain ⟨B,C,hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  obtain ⟨k,hk,hVery⟩ := hAmple
  obtain ⟨d,b,hGen,μ,ρ,hEig,hRestrict,hProjective⟩ :=
    exists_contactPower_complex_action_with_eigenbasis P.tangent
      hR3 hFinite hEigen hCircle A
      P.connection B C.contact k hVery
  exact ⟨B,C,k,hk,hVery,d,b,hGen,μ,ρ,hEig,hRestrict,hProjective⟩

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexTorusActionData
