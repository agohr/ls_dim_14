import QuaternionicSymmetry.QuaternionicMomentPositivity
import QuaternionicSymmetry.MatrixValuedForms
import Mathlib.RingTheory.TensorProduct.Basic
import QuaternionicSymmetry.Complexification

/-! The matrix moment sign expressed as an actual complex matrix trace.
Real even exterior forms embed in their complexification before matrix multiplication. -/

namespace QuaternionicSymmetry.QuaternionicTracePositivity

open scoped TensorProduct ComplexOrder
open Module QuaternionicFundamental

noncomputable section

variable {ι κ β V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
  [Fintype β] [DecidableEq β] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

abbrev CE (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  ℂ ⊗[ℝ] E V

def embed : E V →ₐ[ℝ] CE V := Algebra.TensorProduct.includeRight

omit [FiniteDimensional ℝ V] in
theorem embed_injective : Function.Injective (embed (V := V)) :=
  Complexification.includeRight_injective

omit [DecidableEq β] in
theorem map_quadratic {S T : Type*} [CommRing S] [Algebra ℝ S]
    [CommRing T] [Algebra ℝ T] (F : S →ₐ[ℝ] T)
    (G : Matrix β β ℝ) (η : β → S) :
    F (CovariancePolynomial.quadratic G η) =
      CovariancePolynomial.quadratic G (fun b => F (η b)) := by
  simp [CovariancePolynomial.quadratic]

def traceY (A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ) (η : β → E V) : CE V :=
  Matrix.trace (MatrixValuedForms.mapMatrix A *
    -(MatrixValuedForms.weightedMatrix (S := CE V) B (fun b => embed (V := V) (η b))) ^ 2)

omit [DecidableEq β] [FiniteDimensional ℝ V] in
theorem traceY_eq (A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (hA : A.IsHermitian) (hB : ∀ b, (B b).IsHermitian) (η : β → E V) :
    traceY A B η = embed (V := V) (-CovariancePolynomial.quadratic
      (MatrixMoments.covarianceMatrix A B) η) := by
  unfold traceY
  rw [Matrix.mul_neg (α := CE V), Matrix.trace_neg]
  rw [MatrixValuedForms.trace_weightedMatrix_sq_covariance
    (S := CE V) A B (fun b => embed (V := V) (η b)) hA hB]
  rw [map_neg]
  exact congrArg Neg.neg (map_quadratic (embed (V := V))
    (MatrixMoments.covarianceMatrix A B) η).symm

theorem embed_topForm_ne_zero (Q : QuaternionicStructure V) (c : Basis ι ℝ V) :
    embed (V := V) (topForm Q c) ≠ 0 := by
  intro h
  apply QuaternionicSpectralSign.topForm_ne_zero Q c
  exact embed_injective (V := V) (show embed (V := V) (topForm Q c) =
    embed (V := V) 0 by simpa only [map_zero] using h)

/-- The genuine matrix trace moment is a nonnegative multiple of the canonical top form. -/
theorem traceY_mixed_mem_positiveRay (Q : QuaternionicStructure V) (c : Basis ι ℝ V)
    (A : Matrix κ κ ℂ) (B : β → Matrix κ κ ℂ)
    (hA : A.PosSemidef) (hB : ∀ b, (B b).IsHermitian)
    (η : β → E V) (hη : ∀ b, η b ∈ HyperholomorphicExterior.formSpace Q c)
    (k : ℕ) (hk : k ≤ Q.quaternionicDimension) :
    PositiveRay.Contains (embed (V := V) (topForm Q c))
      (traceY A B η ^ k * embed (V := V) (form Q c) ^ (Q.quaternionicDimension - k)) := by
  obtain ⟨r, hr, heq⟩ := QuaternionicMomentPositivity.covariance_mixed_in_positive_ray
    Q c A B hA hB η hη k hk
  refine ⟨r, hr, ?_⟩
  rw [traceY_eq A B hA.isHermitian hB η]
  have h := congrArg (embed (V := V)) heq
  rw [map_mul, map_pow, map_pow] at h
  exact h.trans ((embed (V := V)).toLinearMap.map_smul r (topForm Q c))

end
end QuaternionicSymmetry.QuaternionicTracePositivity
