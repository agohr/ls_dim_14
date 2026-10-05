import QuaternionicSymmetry.ComplexTorusCharacterHolomorphic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Surjective holomorphic exponential parameters for the actual complex
torus, with the real parameter space mapping to its actual compact torus. -/

namespace QuaternionicSymmetry.ComplexTorusExponential

open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ManifoldQuaternionicTorusAction
open scoped Manifold ContDiff
noncomputable section

def exponential (r : ℕ) (z : Fin r → ℂ) : ComplexTorus r :=
  fun i => Units.mk0 (Complex.exp (z i * Complex.I)) (Complex.exp_ne_zero _)

theorem exponential_surjective (r : ℕ) : Function.Surjective (exponential r) := by
  intro z
  refine ⟨fun i => Complex.log (z i : ℂ) / Complex.I, ?_⟩
  funext i
  apply Units.ext
  change Complex.exp (Complex.log (z i : ℂ) / Complex.I * Complex.I) = (z i : ℂ)
  rw [div_mul_cancel₀ _ Complex.I_ne_zero, Complex.exp_log (z i).ne_zero]

theorem exponential_real (r : ℕ) (t : Fin r → ℝ) :
    exponential r (fun i => (t i : ℂ)) =
      compactInclusion r (fun i => Circle.exp (t i)) := by
  funext i
  apply Units.ext
  exact (Circle.coe_exp (t i)).symm

theorem exponential_contMDiff (r : ℕ) :
    ContMDiff 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, Fin r → ℂ) ∞ (exponential r) := by
  apply ContMDiff.of_comp_isOpenEmbedding (torusVal_isOpenEmbedding r)
  change ContMDiff 𝓘(ℂ, Fin r → ℂ) 𝓘(ℂ, Fin r → ℂ) ∞
    (fun (z : Fin r → ℂ) (i : Fin r) => Complex.exp (z i * Complex.I))
  apply ContDiff.contMDiff
  apply contDiff_pi.mpr
  intro i
  exact Complex.contDiff_exp.comp ((contDiff_apply ℂ ℂ i).mul contDiff_const)

end
end QuaternionicSymmetry.ComplexTorusExponential
