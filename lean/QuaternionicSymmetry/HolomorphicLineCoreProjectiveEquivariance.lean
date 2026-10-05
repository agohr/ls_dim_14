import QuaternionicSymmetry.HolomorphicLineCoreProjectiveNaturality
import Mathlib.LinearAlgebra.Dual.Basis

/-! Compact-side equivariance of the actual complete projective evaluation
map.  The dual section action is transported through an actual basis of
complete sections.  No preservation by a complexified torus is asserted. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveEquivariance

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreProjectiveNaturality
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{u} (B := B) IB)

/-- Coordinate form of the contragredient action on the full section dual. -/
def projectiveCoordinateAction (d : ℕ)
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (T : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB L) :
    (Fin (d + 1) → ℂ) ≃ₗ[ℂ] (Fin (d + 1) → ℂ) :=
  ((b.dualBasis.equivFun).symm.trans T.symm.dualMap).trans b.dualBasis.equivFun

theorem projectiveEvaluation_equivariant
    (f : B → B)
    (Φ : ∀ x : B, L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (f x))
    (T : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB L)
    (hT : ∀ (s : GlobalSections IB L) (x : B),
      (T s) (f x) = Φ x (s x))
    (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L) (x : B) :
    projectiveEvaluationOfGenerated IB L d b hGen (f x) =
      Projectivization.map (projectiveCoordinateAction IB L d b T).toLinearMap
        (projectiveCoordinateAction IB L d b T).injective
        (projectiveEvaluationOfGenerated IB L d b hGen x) := by
  obtain ⟨c, hc⟩ := evaluation_naturality IB L f Φ T hT x
  have hx : x ∉ baseLocus IB L := by
    simp [(globallyGenerated_iff_baseLocus_empty IB L).1 hGen]
  have hfx : f x ∉ baseLocus IB L := by
    simp [(globallyGenerated_iff_baseLocus_empty IB L).1 hGen]
  change Projectivization.mk ℂ (basisEvaluation IB L d b (f x))
      (basisEvaluation_ne_zero IB L d b hfx) =
    Projectivization.map (projectiveCoordinateAction IB L d b T).toLinearMap
      (projectiveCoordinateAction IB L d b T).injective
      (Projectivization.mk ℂ (basisEvaluation IB L d b x)
        (basisEvaluation_ne_zero IB L d b hx))
  rw [Projectivization.map_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨c, ?_⟩
  funext i
  have hi := congrArg (fun e : Module.Dual ℂ (GlobalSections IB L) => e (b i)) hc
  have heval : basisEvaluation IB L d b x =
      b.dualBasis.equivFun (evaluation IB L x) := by
    funext j
    exact (b.dualBasis_equivFun (evaluation IB L x) j).symm
  have haction :
      projectiveCoordinateAction IB L d b T (basisEvaluation IB L d b x) =
        b.dualBasis.equivFun (T.symm.dualMap (evaluation IB L x)) := by
    rw [heval]
    simp [projectiveCoordinateAction]
  change (c : ℂ) *
      projectiveCoordinateAction IB L d b T (basisEvaluation IB L d b x) i =
    basisEvaluation IB L d b (f x) i
  rw [haction]
  simpa only [b.dualBasis_equivFun, basisEvaluation,
    LinearEquiv.dualMap_apply, LinearMap.smul_apply,
    smul_eq_mul] using hi.symm

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveEquivariance
