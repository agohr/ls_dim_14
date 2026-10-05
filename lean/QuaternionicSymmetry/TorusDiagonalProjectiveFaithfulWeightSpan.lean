import QuaternionicSymmetry.TorusFaithfulCharacterWeightSpan
import Mathlib.LinearAlgebra.Basis.Defs

/-! A projectively faithful finite-dimensional diagonal action of the
actual compact torus has real-spanning integral weights. We need only
faithfulness against scalar endomorphisms; no complexification or
classification source is involved. -/

namespace QuaternionicSymmetry.TorusDiagonalProjectiveFaithfulWeightSpan

open TorusFaithfulWeightSpan TorusFaithfulCharacterWeightSpan
open ManifoldQuaternionicTorusAction
noncomputable section

variable {r : ℕ} {ι S : Type*}
  [AddCommGroup S] [Module ℂ S]

theorem integral_weights_span_of_projective_faithfulness
    (ρ : Torus r →* Module.End ℂ S)
    (b : Module.Basis ι ℂ S)
    (μ : ι → Fin r → ℤ)
    (hEig : ∀ (t : Torus r) i,
      ρ t (b i) = (weightCharacter (μ i) t : ℂ) • b i)
    (hScalarFaith : ∀ (t : Torus r) (c : ℂˣ),
      (∀ s : S, ρ t s = (c : ℂ) • s) → t = 1) :
    Submodule.span ℝ (Set.range
      (fun i => integralWeightLinear (μ i))) = ⊤ := by
  apply integralWeight_span_top_of_faithful_characters μ
  intro t ht
  have hρ : ρ t = LinearMap.id := by
    apply b.ext
    intro i
    simpa [ht i] using hEig t i
  apply hScalarFaith t 1
  intro s
  have hs := congrArg (fun f : Module.End ℂ S => f s) hρ
  simpa using hs

end
end QuaternionicSymmetry.TorusDiagonalProjectiveFaithfulWeightSpan
