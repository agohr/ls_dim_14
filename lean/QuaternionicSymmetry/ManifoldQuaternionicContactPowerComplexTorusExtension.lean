import QuaternionicSymmetry.ManifoldQuaternionicContactPowerProjectiveEquivariance
import QuaternionicSymmetry.HolomorphicLineCoreComplexTorusExtension
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! A positive, genuinely very ample power of the actual twistor contact
line yields a complex-torus action on the actual twistor point set. The
action extends the compact isometric torus exactly and is equivariant with
the constructed complete projective embedding. Scheme-algebraicity of the
transported action is not asserted. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusExtension

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactPowerSections
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerContinuity
open ManifoldQuaternionicContactPowerWeights
open ManifoldQuaternionicContactPowerProjectiveEquivariance
open HolomorphicLineCoreProjectiveEigenbasisReindex
open HolomorphicLineCoreComplexTorusExtension
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoreProjectiveEvaluation
open ComplexProjectiveDiagonalAction TorusLaurentRepresentation
open ProjectiveAnalyticAlgebraicSources CompactTorusEigenbasisSource
open TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem exists_contactPower_complex_action
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    {r : ℕ} (A : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hVery : letI := B.charts; letI := B.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k)) :
    letI := B.charts
    letI := B.complexManifold
    ∃ (d : ℕ)
      (b : Module.Basis (Fin (d + 1)) ℂ (PowerSections Q D B C k))
      (hGen : GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k))
      (μ : Fin (d + 1) → Fin r → ℤ)
      (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q)),
        (∀ (t : Torus r) (z : SphereBundleTotal Q),
          ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z) ∧
        ∀ (w : ComplexTorus r) (z : SphereBundleTotal Q),
          projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
            (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
              (contactLineCore Q D C.line) k) d b hGen (ρ w z) =
            projectiveAction (fun i => -(μ i)) w
              (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
                (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                  (contactLineCore Q D C.line) k) d b hGen z) := by
  letI := B.charts
  letI := B.complexManifold
  have hVery' : VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) k) := hVery
  obtain ⟨d, b₀, hGen, _, _⟩ := hVery
  obtain ⟨b, μ, hμ⟩ :=
    exists_contactPower_eigenbasis_on_projective_index Q hR3 hFinite
      hEigen hCircle A D B C k d b₀
  obtain ⟨ρ, hRestrict, hProjective⟩ :=
    exists_complex_action_of_veryAmple_eigenbasis (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) k) hVery'
      b hGen
      (fun t z => sphereTotalMap Q (A.representation t) z)
      (fun t z => contactPowerScalarFiberEquiv Q D B C (A.representation t) k z)
      (fun t => contactPowerSectionEquiv Q D B C (A.representation t) k)
      (fun t s z => contactPowerScalarFiberEquiv_naturality
        Q D B C (A.representation t) k s z)
      μ (by intro t i; simpa [contactPowerTorusRepresentation,
        contactPowerSectionRepresentation] using hμ t i)
  exact ⟨d,b,hGen,μ,ρ,hRestrict,hProjective⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusExtension
