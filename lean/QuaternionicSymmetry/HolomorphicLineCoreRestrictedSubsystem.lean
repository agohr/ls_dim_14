import QuaternionicSymmetry.HolomorphicLineCoreProjectiveHolomorphic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! The finite subsystem on a holomorphic restricted line obtained by
restricting an ambient basis. This is not asserted to be a basis of *all*
restricted sections. Its projective map is the actual ambient complete
linear-system map composed with the inclusion. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreRestrictedSubsystem

open QuaternionicSymmetry.HolomorphicLineCorePullback
open QuaternionicSymmetry.HolomorphicLineCoreProjectiveEvaluation
open QuaternionicSymmetry.HolomorphicLineCoreClasses
open QuaternionicSymmetry.ComplexProjectiveTopology
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B'] [TopologicalSpace H]
  [TopologicalSpace H'] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H) (IB' : ModelWithCorners ℂ F' H')
  [IsManifold IB ∞ B] [IsManifold IB' ∞ B']
  (L : LineCore.{u} (B := B) IB)
  (f : B' → B) (hf : ContMDiff IB' IB ∞ f)
  (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))

/-- Coordinates of the finite subsystem of restricted ambient sections. -/
def restrictedBasisEvaluation (x : B') : Coord d :=
  fun k => (restrictionLinear IB IB' L f hf (b k)) x

theorem restrictedBasisEvaluation_eq (x : B') :
    restrictedBasisEvaluation IB IB' L f hf d b x =
      basisEvaluation IB L d b (f x) := rfl

/-- The actual projective map of the restricted ambient subsystem. It is
defined using only restricted sections, not an arbitrary map. -/
def restrictedSubsystemMap (h : GloballyGenerated IB L) (x : B') : Space d :=
  projectivize d (restrictedBasisEvaluation IB IB' L f hf d b x)

theorem restrictedSubsystemMap_eq_comp (h : GloballyGenerated IB L) :
    restrictedSubsystemMap IB IB' L f hf d b h =
      (projectiveEvaluationOfGenerated IB L d b h) ∘ f := by
  funext x
  change projectivize d (restrictedBasisEvaluation IB IB' L f hf d b x) = _
  rw [restrictedBasisEvaluation_eq]
  exact projectivize_of_ne_zero d _
    (basisEvaluation_ne_zero IB L d b
      (by simpa [(globallyGenerated_iff_baseLocus_empty IB L).1 h]))

theorem restrictedSubsystemMap_contMDiff (h : GloballyGenerated IB L) :
    ContMDiff IB' 𝓘(ℂ, Fin d → ℂ) ∞
      (restrictedSubsystemMap IB IB' L f hf d b h) := by
  rw [restrictedSubsystemMap_eq_comp]
  exact (projectiveEvaluationOfGenerated_contMDiff IB L d b h).comp hf

/-- An ambient very-ample linear system stays a holomorphic embedding on
any holomorphically embedded submanifold, using its restricted subsystem.
This does not yet say that the *complete* restricted system is an embedding. -/
theorem restrictedSubsystemMap_isEmbedding
    (h : GloballyGenerated IB L)
    (hfEmb : Topology.IsEmbedding f)
    (hAmbient : Topology.IsEmbedding
      (projectiveEvaluationOfGenerated IB L d b h)) :
    Topology.IsEmbedding (restrictedSubsystemMap IB IB' L f hf d b h) := by
  rw [restrictedSubsystemMap_eq_comp]
  exact hAmbient.comp hfEmb

theorem restrictedSubsystemMap_mfderiv_injective
    (h : GloballyGenerated IB L)
    (hfImm : ∀ x : B', Function.Injective (mfderiv IB' IB f x))
    (hAmbient : ∀ y : B, Function.Injective
      (mfderiv IB 𝓘(ℂ, Fin d → ℂ)
        (projectiveEvaluationOfGenerated IB L d b h) y))
    (x : B') : Function.Injective
      (mfderiv IB' 𝓘(ℂ, Fin d → ℂ)
        (restrictedSubsystemMap IB IB' L f hf d b h) x) := by
  rw [restrictedSubsystemMap_eq_comp]
  rw [mfderiv_comp x
    ((projectiveEvaluationOfGenerated_contMDiff IB L d b h).mdifferentiableAt
      (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact (hAmbient (f x)).comp (hfImm x)

end
end QuaternionicSymmetry.HolomorphicLineCoreRestrictedSubsystem
