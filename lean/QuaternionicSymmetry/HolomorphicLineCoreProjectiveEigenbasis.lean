import QuaternionicSymmetry.HolomorphicLineCoreProjectiveEquivariance
import QuaternionicSymmetry.ComplexProjectiveDiagonalAction

/-! The complete-evaluation projective action uses the contragredient of
the action on sections.  In a genuine section eigenbasis its coordinate
weights are the negatives of the section weights. -/

namespace QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasis

open HolomorphicLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineCoreProjectiveEvaluation
open HolomorphicLineCoreProjectiveEquivariance
open TorusLaurentRepresentation ComplexProjectiveDiagonalAction
open ManifoldQuaternionicTorusAction TorusCharacterInput
open scoped Manifold ContDiff
noncomputable section
universe u

variable {B H F : Type*} [TopologicalSpace B] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ChartedSpace H B]
  (IB : ModelWithCorners ℂ F H)
  (L : LineCore.{u} (B := B) IB)

theorem projectiveCoordinateAction_eigenbasis
    (d : ℕ) (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (T : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB L)
    (lam : Fin (d + 1) → ℂˣ)
    (hEig : ∀ i, T (b i) = (lam i : ℂ) • b i)
    (v : Fin (d + 1) → ℂ) (i : Fin (d + 1)) :
    projectiveCoordinateAction IB L d b T v i =
      (((lam i)⁻¹ : ℂˣ) : ℂ) * v i := by
  have hInv (j : Fin (d + 1)) :
      T.symm (b j) = (((lam j)⁻¹ : ℂˣ) : ℂ) • b j := by
    apply T.injective
    rw [T.apply_symm_apply, T.map_smul, hEig j]
    simp [smul_smul]
  change b.dualBasis.equivFun
      (T.symm.dualMap (b.dualBasis.equivFun.symm v)) i = _
  rw [b.dualBasis_equivFun, LinearEquiv.dualMap_apply, hInv]
  have hv := congrFun
    (b.dualBasis.equivFun.apply_symm_apply v) i
  rw [b.dualBasis_equivFun] at hv
  rw [map_smul, hv]
  rfl

theorem complexWeightCharacter_neg {r : ℕ}
    (μ : Fin r → ℤ) (z : ComplexTorus r) :
    complexWeightCharacter (-μ) z =
      (complexWeightCharacter μ z)⁻¹ := by
  change (∏ j : Fin r, z j ^ (-(μ j))) =
    (∏ j : Fin r, z j ^ μ j)⁻¹
  simp [zpow_neg, Finset.prod_inv_distrib]

/-- The dual complete-evaluation coordinates carry the negative integral
weights of an actual compact-torus eigenbasis of sections. -/
theorem projectiveCoordinateAction_diagonal_compact
    {r d : ℕ}
    (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (T : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB L)
    (μ : Fin (d + 1) → Fin r → ℤ)
    (t : Torus r)
    (hEig : ∀ i, T (b i) = (weightCharacter (μ i) t : ℂ) • b i)
    (v : Fin (d + 1) → ℂ) :
    projectiveCoordinateAction IB L d b T v =
      diagonalEquiv (fun i => -(μ i)) (compactInclusion r t) v := by
  ext i
  let lam : Fin (d + 1) → ℂˣ :=
    fun j => Circle.toUnits (weightCharacter (μ j) t)
  have hEig' : ∀ j, T (b j) = (lam j : ℂ) • b j := by
    intro j
    simpa [lam] using hEig j
  rw [projectiveCoordinateAction_eigenbasis IB L d b T lam hEig' v i,
    diagonalEquiv_apply, complexWeightCharacter_neg,
    complexWeightCharacter_compact]

/-- Genuine complete projective evaluation is equivariant for the compact
torus's negative section weights, provided the section action is the actual
linearized line action. -/
theorem projectiveEvaluation_diagonal_compact
    {r d : ℕ} (b : Module.Basis (Fin (d + 1)) ℂ (GlobalSections IB L))
    (hGen : GloballyGenerated IB L)
    (f : B → B)
    (Φ : ∀ x : B, L.core.Fiber x ≃ₗ[ℂ] L.core.Fiber (f x))
    (T : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB L)
    (hT : ∀ (s : GlobalSections IB L) (x : B),
      (T s) (f x) = Φ x (s x))
    (μ : Fin (d + 1) → Fin r → ℤ) (t : Torus r)
    (hEig : ∀ i, T (b i) = (weightCharacter (μ i) t : ℂ) • b i)
    (x : B) :
    projectiveEvaluationOfGenerated IB L d b hGen (f x) =
      projectiveAction (fun i => -(μ i)) (compactInclusion r t)
        (projectiveEvaluationOfGenerated IB L d b hGen x) := by
  have hcoord : projectiveCoordinateAction IB L d b T =
      diagonalEquiv (fun i => -(μ i)) (compactInclusion r t) := by
    apply LinearEquiv.ext
    intro v
    exact projectiveCoordinateAction_diagonal_compact IB L b T μ t hEig v
  rw [projectiveEvaluation_equivariant IB L f Φ T hT d b hGen x]
  simp only [projectiveAction, hcoord]

end
end QuaternionicSymmetry.HolomorphicLineCoreProjectiveEigenbasis
