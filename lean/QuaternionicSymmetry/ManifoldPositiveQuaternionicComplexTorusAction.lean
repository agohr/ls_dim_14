import QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusExtension
import QuaternionicSymmetry.ManifoldTwistorPositiveContactAmple

/-! On the selected normalized positive quaternionic-Kähler twistor,
source-derived contact ampleness and the actual contact-power linearization
produce a complex-torus action on twistor points extending the compact
isometric torus. No algebraic-scheme action is inferred here. -/

namespace QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexTorusAction

open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicContactPowerComplexTorusExtension
open ManifoldTwistorPositiveContactAmple
open ManifoldTwistorPositiveRicciInput
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicScalarCurvature
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicPositiveLineKodairaSource
open ProjectiveAnalyticAlgebraicSources
open CompactTorusEigenbasisSource TorusCharacterInput
open TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [Nonempty M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_normalized_twistor_complex_torus_action
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
        ∃ k : ℕ, 0 < k ∧
          ∃ ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal P.tangent),
            ∀ (t : Torus r) (z : SphereBundleTotal P.tangent),
              ρ (compactInclusion r t) z =
                sphereTotalMap P.tangent (A.representation t) z := by
  letI : CompactSpace M := ⟨P.compact⟩
  letI : PreconnectedSpace M := ⟨P.connected⟩
  letI : T3Space M := inferInstance
  obtain ⟨B, C, hAmple⟩ := exists_normalized_ample_contact_core
    hT1 hKodaira P n hn hDim hScalar
  obtain ⟨k, hk, hVery⟩ := hAmple
  obtain ⟨d, b, hGen, μ, ρ, hRestrict, hProjective⟩ :=
    exists_contactPower_complex_action P.tangent
      hR3 hFinite hEigen hCircle A
      P.connection B C.contact k hVery
  exact ⟨B, C, k, hk, ρ, hRestrict⟩

end
end QuaternionicSymmetry.ManifoldPositiveQuaternionicComplexTorusAction
