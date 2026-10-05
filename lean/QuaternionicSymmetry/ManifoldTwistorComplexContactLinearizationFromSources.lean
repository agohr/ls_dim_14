import QuaternionicSymmetry.ManifoldTwistorComplexContactLinearization
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusActionData
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusJointHolomorphic
import QuaternionicSymmetry.HolomorphicLineComplexTorusProjectiveCompanion
import QuaternionicSymmetry.ComplexProjectiveDiagonalFaithfulness
import QuaternionicSymmetry.ManifoldQuaternionicTwistorActionFaithful

/-! The same supplied ample contact line produces its faithful holomorphic
complex-torus linearization and its actual complete-linear-system projective
companion. All action, power and eigenbasis witnesses are selected internally.
The contact datum and compact torus remain fixed throughout. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexContactLinearizationFromSources

open ManifoldTwistorComplexContactLinearization
open ManifoldQuaternionicContactPowerComplexTorusActionData
open ManifoldQuaternionicContactPowerComplexTorusJointHolomorphic
open ManifoldQuaternionicTwistorActionFaithful ComplexProjectiveDiagonalFaithfulness
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses HolomorphicLineComplexTorusLinearization
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreAmpleFiniteMap HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreProjectiveBasisChange
open ProjectiveAnalyticAlgebraicSources CompactTorusEigenbasisSource
open TorusCharacterInput TorusLaurentRepresentation GeneralSmoothMapSource
open ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Source-only selection of a faithful canonical line action, with the
complete projective system of a positive power of that literal same line. -/
theorem exists_faithful_actualContactLineLinearization
    (hR3 : ManifoldRiemannianIsometryLieInput.IsometryLieSource.{0,0})
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (hEigen : KnappTorusEigenbasis) (hCircle : CircleCharacterSource)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    {r : ℕ} (T : ContinuousTorusAction Q r) (hFaithful : T.Faithful)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    letI := B.charts
    letI := B.complexManifold
    ∃ (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
      (hJoint : ContMDiff
        (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
      (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
        ρ (compactInclusion r t) z = sphereTotalMap Q (T.representation t) z),
      Function.Injective ρ ∧
      Nonempty (ComplexTorusProjectiveCompanion (contactLineCore Q D C.line)
        (actualContactLineLinearization Q D B C T ρ hJoint hRestrict)) := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  obtain ⟨d,b,hGen,μ,ρ,hEig,hRestrict,hProjective⟩ :=
    exists_contactPower_complex_action_with_eigenbasis
      Q hR3 hFinite hEigen hCircle T D B C k hVery
  have hJoint := contactPower_complex_action_joint_holomorphic
    Q hLee D B C k hVery d b hGen μ ρ hProjective
  have hCompact : Function.Injective (fun t : Torus r => ρ (compactInclusion r t)) := by
    intro t u h
    apply torus_lift_injective Q T hFaithful
    funext z
    change sphereTotalMap Q (T.representation t) z =
      sphereTotalMap Q (T.representation u) z
    rw [← hRestrict t z, ← hRestrict u z]
    exact congrArg (fun e : Equiv.Perm (SphereBundleTotal Q) => e z) h
  have hρ : Function.Injective ρ := action_injective_of_compact
    (fun i => -(μ i)) ρ
    (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) k) d b hGen)
    (veryAmple_projectiveEvaluation_injective 𝓘(ℂ,ComplexTwistorModel n)
      (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
        (contactLineCore Q D C.line) k) hVery d b hGen)
    hProjective hCompact
  refine ⟨ρ,hJoint,hRestrict,hρ,⟨?_⟩⟩
  exact {
    k := k
    k_pos := hk
    veryAmple := hVery
    d := d
    basis := b
    generated := hGen
    weights := μ
    equivariant := hProjective }

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactLinearizationFromSources
