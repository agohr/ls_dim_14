import QuaternionicSymmetry.SelectedTorusCompactInclusionImmersion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The literal coordinatewise circle exponential, followed by the
literal compact inclusion into `(ℂˣ)^r`, is smooth in the existing real
companion of the complex-torus atlas. -/

namespace QuaternionicSymmetry.SelectedTorusCompactExponentialSmooth

open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open ComplexLieRealCompanion
open scoped Manifold ContDiff
noncomputable section

def circleExpPi (r : ℕ) : (Fin r → ℝ) → Fin r → Circle :=
  fun a i => Circle.exp (a i)

theorem circleExpPi_zero (r : ℕ) : circleExpPi r 0 = 1 := by
  funext i
  simp [circleExpPi]

theorem compactExp_smooth (r : ℕ) :
    ContMDiff 𝓘(ℝ,Fin r → ℝ) 𝓘(ℝ,Fin r → ℂ) ∞
      (compactInclusion r ∘ circleExpPi r) := by
  letI : IsManifold 𝓘(ℝ,Fin r → ℂ) ∞ (ComplexTorus r) := realManifold
  apply ContMDiff.of_comp_isOpenEmbedding (torusVal_isOpenEmbedding r)
  apply ContDiff.contMDiff
  apply (contDiff_pi).2
  intro i
  have hArg : ContDiff ℝ ∞
      (fun a : Fin r → ℝ => ((a i : ℝ) : ℂ) * Complex.I) := by
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)).mul
      contDiff_const)
  have hExp : ContDiff ℝ ∞ (Complex.exp : ℂ → ℂ) :=
    (Complex.contDiff_exp : ContDiff ℂ ∞ (Complex.exp : ℂ → ℂ)).restrict_scalars ℝ
  simpa only [torusVal, Function.comp_def, compactInclusion,
    circleExpPi, Circle.coe_exp] using
    hExp.comp hArg

end
end QuaternionicSymmetry.SelectedTorusCompactExponentialSmooth
