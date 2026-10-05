import QuaternionicSymmetry.HolomorphicLineComplexTorusLinearizationAction
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveBasisChangeImmersion
import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
import QuaternionicSymmetry.ComplexProjectiveDiagonalAction

/-! Separate, genuine complete-linear-system data for a positive power of
the SAME line carrying a complex-torus linearization. The analytic
projective embedding, integral Laurent weights, and equivariance are
recorded explicitly; no algebraic GAGA conclusion is smuggled in. -/
namespace QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreAmpleFiniteMap
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreProjectiveBasisChangeImmersion
open HolomorphicLineTensorPowerClasses
open ComplexProjectiveDiagonalAction TorusLaurentRepresentation
open scoped Manifold ContDiff
noncomputable section

universe u
variable {X F : Type*} [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [CompactSpace X]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [ChartedSpace F X] [IsManifold 𝓘(ℂ,F) ∞ X]
  (L : LineCore.{u} (B := X) 𝓘(ℂ,F)) {r : ℕ}

/-- Extra projective data is kept separate from a line linearization:
the complete section basis is on `L^k`, with `k>0`, and its projective
action uses the negative integral weights of that same basis. -/
structure ComplexTorusProjectiveCompanion
    (lin : ComplexTorusLineLinearization L (r := r)) where
  k : ℕ
  k_pos : 0 < k
  veryAmple : VeryAmpleCore 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) L k)
  d : ℕ
  basis : Module.Basis (Fin (d + 1)) ℂ
    (GlobalSections 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) L k))
  generated : GloballyGenerated 𝓘(ℂ,F) (powerCoreRep 𝓘(ℂ,F) L k)
  weights : Fin (d + 1) → Fin r → ℤ
  equivariant : ∀ (t : ComplexTorus r) (x : X),
    projectiveEvaluationOfGenerated 𝓘(ℂ,F)
      (powerCoreRep 𝓘(ℂ,F) L k) d basis generated (lin.baseAction t x) =
    projectiveAction (fun i => -(weights i)) t
      (projectiveEvaluationOfGenerated 𝓘(ℂ,F)
        (powerCoreRep 𝓘(ℂ,F) L k) d basis generated x)

/-- The recorded map is an actual topological embedding and holomorphic
immersion of the complete positive-power linear system. -/
theorem ComplexTorusProjectiveCompanion.embedding_immersion
    {lin : ComplexTorusLineLinearization L (r := r)}
    (data : ComplexTorusProjectiveCompanion L lin) :
    Topology.IsEmbedding
      (projectiveEvaluationOfGenerated 𝓘(ℂ,F)
        (powerCoreRep 𝓘(ℂ,F) L data.k)
        data.d data.basis data.generated) ∧
      ∀ x : X, Function.Injective
        (mfderiv 𝓘(ℂ,F) 𝓘(ℂ,Fin data.d → ℂ)
          (projectiveEvaluationOfGenerated 𝓘(ℂ,F)
            (powerCoreRep 𝓘(ℂ,F) L data.k)
            data.d data.basis data.generated) x) :=
  veryAmple_projectiveEvaluation_embedding_immersion 𝓘(ℂ,F)
    (powerCoreRep 𝓘(ℂ,F) L data.k) data.veryAmple
    data.d data.basis data.generated

end
end QuaternionicSymmetry.HolomorphicLineComplexTorusLinearization
