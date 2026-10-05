import QuaternionicSymmetry.QuaternionicProjectiveStandardHilbertStructure

/-! The central diagonal sign acts trivially by conjugation on endomorphisms
of the genuine quaternionic Hilbert standard space. Thus the adjoint action
depends only on the tangent `Sp(n)·Sp(1)` normalizer element. -/

namespace QuaternionicSymmetry.QuaternionicProjectiveStandardAdjoint

open QuaternionicProjectiveStandardL2
open QuaternionicProjectiveStandardRepresentation
open QuaternionicUnitScalarIsometries
open QuaternionicIsometryNormalizer
open scoped Quaternion

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable (S : QuaternionicStructure E)

abbrev StandardEnd :=
  StandardSpace (E := E) →L[ℝ] StandardSpace (E := E)

def standardAdjoint (p : symplecticKernel S × unitary ℍ) :
    StandardEnd (E := E) →L[ℝ] StandardEnd (E := E) :=
  ((standardActionL2 S p).conjContinuousAlgEquiv).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem standardAdjoint_apply
    (p : symplecticKernel S × unitary ℍ)
    (A : StandardEnd (E := E)) (z : StandardSpace (E := E)) :
    standardAdjoint S p A z =
      standardActionL2 S p (A ((standardActionL2 S p).symm z)) := rfl

theorem standardActionL2_kernel_sign
    (p : symplecticKernel S × unitary ℍ)
    (hp : symplecticProductAction S p = 1) :
    (∀ z : StandardSpace (E := E), standardActionL2 S p z = z) ∨
    (∀ z : StandardSpace (E := E), standardActionL2 S p z = -z) := by
  rcases standardAction_kernel_sign S p hp with ⟨_, h⟩ | ⟨_, h⟩
  · left
    intro z
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
    exact h ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z)
  · right
    intro z
    apply (WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ).injective
    change standardAction S p ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z) =
      -((WithLp.prodContinuousLinearEquiv 2 ℝ E ℍ) z)
    exact h _

theorem standardAdjoint_kernel (p : symplecticKernel S × unitary ℍ)
    (hp : symplecticProductAction S p = 1)
    (A : StandardEnd (E := E)) :
    standardAdjoint S p A = A := by
  rcases standardActionL2_kernel_sign S p hp with hpos | hneg
  · ext z
    have hinv : (standardActionL2 S p).symm z = z := by
      apply (standardActionL2 S p).injective
      rw [(standardActionL2 S p).apply_symm_apply, hpos]
    rw [standardAdjoint_apply, hinv, hpos]
  · ext z
    have hinv : (standardActionL2 S p).symm z = -z := by
      apply (standardActionL2 S p).injective
      rw [(standardActionL2 S p).apply_symm_apply]
      rw [map_neg, hneg]
      simp
    rw [standardAdjoint_apply, hinv, map_neg, hneg]
    simp

theorem standardAdjoint_mul (p r : symplecticKernel S × unitary ℍ)
    (A : StandardEnd (E := E)) :
    standardAdjoint S (p * r) A =
      standardAdjoint S p (standardAdjoint S r A) := by
  ext z
  simp only [standardAdjoint_apply]
  have hmul : standardActionL2 S (p * r) =
      standardActionL2 S p * standardActionL2 S r := by
    apply ContinuousLinearEquiv.ext
    funext x
    have h := congrArg (fun T : StandardSpace (E := E) ≃ₗᵢ[ℝ]
      StandardSpace (E := E) => T x) (map_mul (standardIsometryL2 S) p r)
    exact h
  rw [hmul]
  rfl

/-- Any two product lifts of the same tangent normalizer transition define
exactly the same standard adjoint coordinate change. -/
theorem standardAdjoint_eq_of_same_tangent
    (p r : symplecticKernel S × unitary ℍ)
    (h : symplecticProductAction S p = symplecticProductAction S r) :
    standardAdjoint S p = standardAdjoint S r := by
  let d := p * r⁻¹
  have hd : symplecticProductAction S d = 1 := by
    dsimp [d]
    rw [map_mul, map_inv, h]
    group
  ext A
  have hp : p = d * r := by
    dsimp [d]
    group
  rw [hp, standardAdjoint_mul, standardAdjoint_kernel S d hd]

end
end QuaternionicSymmetry.QuaternionicProjectiveStandardAdjoint
