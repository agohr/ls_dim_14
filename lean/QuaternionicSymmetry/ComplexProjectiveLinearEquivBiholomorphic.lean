import QuaternionicSymmetry.ComplexProjectiveLinearEquivHolomorphic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! A complex-linear equivalence induces an actual biholomorphism of the
literal projective manifolds, with injective manifold derivative. -/

namespace QuaternionicSymmetry.ComplexProjectiveLinearEquivBiholomorphic

open ComplexProjectiveTopology ComplexProjectiveLinearEquivHolomorphic
open scoped Manifold ContDiff LinearAlgebra.Projectivization
noncomputable section

variable {d e : ℕ} (A : Coord d ≃ₗ[ℂ] Coord e)

theorem projectiveMap_symm_apply (p : Space d) :
    projectiveMap A.symm (projectiveMap A p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp only [projectiveMap_mk]
    simp

theorem projectiveMap_apply_symm (p : Space e) :
    projectiveMap A (projectiveMap A.symm p) = p :=
  projectiveMap_symm_apply A.symm p

def projectiveHomeomorph : Space d ≃ₜ Space e where
  toFun := projectiveMap A
  invFun := projectiveMap A.symm
  left_inv := projectiveMap_symm_apply A
  right_inv := projectiveMap_apply_symm A
  continuous_toFun := (contMDiff_projectiveMap A).continuous
  continuous_invFun := (contMDiff_projectiveMap A.symm).continuous

theorem projectiveMap_isEmbedding : Topology.IsEmbedding (projectiveMap A) :=
  (projectiveHomeomorph A).isEmbedding

theorem projectiveMap_mfderiv_injective (p : Space d) :
    Function.Injective
      (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ)
        (projectiveMap A) p) := by
  have hcomp := mfderiv_comp p
    ((contMDiff_projectiveMap A.symm).mdifferentiable (by simp) (projectiveMap A p))
    ((contMDiff_projectiveMap A).mdifferentiable (by simp) p)
  have hid : (projectiveMap A.symm ∘ projectiveMap A) =
      (id : Space d → Space d) := by
    funext q
    exact projectiveMap_symm_apply A q
  rw [hid, mfderiv_id] at hcomp
  intro v w hvw
  have h := congrArg
    (mfderiv 𝓘(ℂ, Fin e → ℂ) 𝓘(ℂ, Fin d → ℂ)
      (projectiveMap A.symm) (projectiveMap A p)) hvw
  simpa [← ContinuousLinearMap.comp_apply, ← hcomp] using h

end
end QuaternionicSymmetry.ComplexProjectiveLinearEquivBiholomorphic
