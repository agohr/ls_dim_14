import QuaternionicSymmetry.ContinuousLieHomSmooth

/-! A faithful finite-dimensional real Lie-group homomorphism has
injective derivative everywhere. This uses the already registered Lee
equivariant-immersion theorem on the actual left-translation actions. -/

namespace QuaternionicSymmetry.InjectiveLieHomImmersion

open GeneralSmoothMapSource GeneralClosedSubgroupLieSource
open ContinuousLieHomSmooth
open scoped Manifold ContDiff
noncomputable section

variable {E F G H : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [SecondCountableTopology G]
  [ChartedSpace E G] [IsManifold 𝓘(ℝ,E) ∞ G] [LieGroup 𝓘(ℝ,E) ∞ G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [T2Space H] [SecondCountableTopology H]
  [ChartedSpace F H] [IsManifold 𝓘(ℝ,F) ∞ H] [LieGroup 𝓘(ℝ,F) ∞ H]
  (f : G →* H)

theorem smooth_injective_hom_immersion
    (hImm : LeeEquivariantImmersionTheorem)
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (hInj : Function.Injective f) (x : G) :
    Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) := by
  let a : SmoothLeftAction E E G G := {
    act g x := g * x
    one_act := one_mul
    mul_act := fun g h x => mul_assoc g h x
    smooth := contMDiff_mul 𝓘(ℝ,E) ∞ }
  let b : SmoothLeftAction E F G H := {
    act g y := f g * y
    one_act := by intro y; simp
    mul_act := by intro g h y; simp [mul_assoc]
    smooth := (hf.comp contMDiff_fst).mul contMDiff_snd }
  apply hImm a b f
  · intro x y
    exact ⟨y * x⁻¹, by simp [a, mul_assoc]⟩
  · exact hf
  · intro g x
    exact map_mul f g x
  · exact hInj

theorem continuous_injective_hom_immersion
    (hClosed : LeeClosedEmbeddingTheorem)
    (hImm : LeeEquivariantImmersionTheorem)
    (hLee : LeeEmbeddedCodomainRestrictionTheorem)
    (hf : Continuous f)
    (hInj : Function.Injective f) (x : G) :
    Function.Injective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x) :=
  smooth_injective_hom_immersion f hImm
    (continuous_hom_smooth f hClosed hImm hLee hf) hInj x

end
end QuaternionicSymmetry.InjectiveLieHomImmersion
