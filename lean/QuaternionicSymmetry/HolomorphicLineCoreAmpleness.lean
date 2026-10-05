import QuaternionicSymmetry.HolomorphicLineCoreProjectiveHolomorphic
import QuaternionicSymmetry.HolomorphicLineTensorPowerClasses

/-! Geometric very ampleness and ampleness for an actual represented
holomorphic line core. These are definitions in terms of a constructed
complete projective map and its derivative, not source assumptions. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap

open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineTensorPowerClasses
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section
universe uB uH uF uI

variable {B : Type uB} {H : Type uH} {F : Type uF}
  [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [ChartedSpace H B] (IB : ModelWithCorners ℂ F H)
  [IsManifold IB ∞ B]
  (L : LineCore.{uI} (B := B) IB)

/-- Genuine very ampleness of a represented holomorphic line core:
its complete linear system is basepoint-free, topologically embedded,
and immersive. The map and derivative are already constructed objects. -/
def VeryAmpleCore : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L),
    Topology.IsEmbedding (projectiveEvaluationOfGenerated IB L d b hGen) ∧
    ∀ x : B, Function.Injective
      (mfderiv IB 𝓘(ℂ, Fin d → ℂ)
        (projectiveEvaluationOfGenerated IB L d b hGen) x)

/-- The standard geometric ampleness criterion applied to a genuine
holomorphic scalar-cocycle tensor power of this very line core. -/
def AmpleCore : Prop :=
  ∃ k : ℕ, 0 < k ∧
    VeryAmpleCore IB (powerCoreRep IB L k)

end
end QuaternionicSymmetry.HolomorphicLineCoreAmpleFiniteMap
