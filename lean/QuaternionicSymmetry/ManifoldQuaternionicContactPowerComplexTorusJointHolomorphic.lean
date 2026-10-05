import QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusHolomorphic
import QuaternionicSymmetry.ComplexProjectiveDiagonalJointFactorization

/-! The actual contact-power complex-torus extension is jointly
holomorphic in its complex-torus parameter and twistor point, after
the same genuine projective eigensystem and BG-D3 factorization. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusJointHolomorphic

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreProjectiveBasisChangeImmersion
open ComplexProjectiveDiagonalAction
open ComplexProjectiveDiagonalJointFactorization
open GeneralSmoothMapSource TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T3Space M] [CompactSpace M]
  [SecondCountableTopology M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem contactPower_complex_action_joint_holomorphic
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    {r : ℕ}
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hVery : letI := B.charts; letI := B.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k))
    (d : ℕ)
    (b : letI := B.charts
      Module.Basis (Fin (d + 1)) ℂ
        (ManifoldQuaternionicContactPowerWeights.PowerSections Q D B C k))
    (hGen : letI := B.charts
      GloballyGenerated 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k))
    (μ : Fin (d + 1) → Fin r → ℤ)
    (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
    (hEq : letI := B.charts
      ∀ (w : ComplexTorus r) (z : SphereBundleTotal Q),
        projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
          (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
            (contactLineCore Q D C.line) k) d b hGen (ρ w z) =
          projectiveAction (fun i => -(μ i)) w
            (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
              (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
                (contactLineCore Q D C.line) k) d b hGen z)) :
    letI := B.charts
    ContMDiff
      (𝓘(ℂ, Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun q : ComplexTorus r × SphereBundleTotal Q => ρ q.1 q.2) := by
  letI := B.charts
  letI := B.complexManifold
  letI := B.realManifold
  let L := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore Q D C.line) k
  obtain ⟨hEmb,hImm⟩ :=
    veryAmple_projectiveEvaluation_embedding_immersion
      𝓘(ℂ,ComplexTwistorModel n) L hVery d b hGen
  exact joint_action_holomorphic hLee (fun i => -(μ i))
    (projectiveEvaluationOfGenerated 𝓘(ℂ,ComplexTwistorModel n)
      L d b hGen)
    hEmb
    (projectiveEvaluationOfGenerated_contMDiff
      𝓘(ℂ,ComplexTwistorModel n) L d b hGen)
    hImm ρ hEq

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerComplexTorusJointHolomorphic
