import Mathlib.Algebra.Lie.Basic
import Mathlib.Analysis.Complex.Basic

/-! Transfer an exactly self-centralizing Lie submodule through an actual
bijective bracket-preserving linear map. -/

namespace QuaternionicSymmetry.LieCentralizerTransport

variable {L L' : Type*} [LieRing L] [LieAlgebra ℂ L]
  [LieRing L'] [LieAlgebra ℂ L']

theorem map_selfCentralizing (f : L →ₗ[ℂ] L')
    (hf : Function.Bijective f)
    (hBracket : ∀ x y : L, f ⁅x,y⁆ = ⁅f x,f y⁆)
    (S : Submodule ℂ L)
    (hSelf : ∀ x : L, x ∈ S ↔ ∀ y ∈ S, ⁅x,y⁆ = 0)
    (z : L') :
    z ∈ S.map f ↔ ∀ w ∈ S.map f, ⁅z,w⁆ = 0 := by
  constructor
  · rintro ⟨x,hx,rfl⟩ w hw
    obtain ⟨y,hy,rfl⟩ := hw
    rw [← hBracket]
    simpa only [map_zero] using congrArg f ((hSelf x).mp hx y hy)
  · intro hz
    obtain ⟨x,rfl⟩ := hf.2 z
    refine ⟨x, (hSelf x).mpr ?_, rfl⟩
    intro y hy
    apply hf.1
    rw [hBracket]
    simpa only [map_zero] using hz (f y) ⟨y,hy,rfl⟩

end QuaternionicSymmetry.LieCentralizerTransport
