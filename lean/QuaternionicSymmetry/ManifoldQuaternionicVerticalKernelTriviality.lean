import QuaternionicSymmetry.ManifoldQuaternionicTwistorIsotropyWeight

/-! The kernel of the genuine vertical isotropy action fixes the entire
quaternionic three-plane. This is the pointwise bridge needed before
propagating triviality along a connected fixed component. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicVerticalKernelTriviality

open ManifoldTwistorSphereBundle ManifoldTwistorCoefficientSphere
open ManifoldTwistorVerticalComplex ManifoldTwistorSphereCore
open ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicIsometryCoefficients
open scoped Manifold ContDiff Matrix
noncomputable section

theorem linear_eq_id_of_axis_and_vertical
    (a : coefficientSphere) (L : Module.End ℝ (Fin 3 → ℝ))
    (haxis : L a.1 = a.1)
    (hvertical : ∀ v : verticalSubmodule a, L v.1 = v.1) :
    ∀ v, L v = v := by
  intro v
  have hv : v - (a.1 ⬝ᵥ v) • a.1 ∈ verticalSubmodule a := by
    change a.1 ⬝ᵥ (v - (a.1 ⬝ᵥ v) • a.1) = 0
    rw [dotProduct_sub, dotProduct_smul, dot_self]
    simp
  have h := hvertical ⟨_, hv⟩
  change L (v - (a.1 ⬝ᵥ v) • a.1) = v - (a.1 ⬝ᵥ v) • a.1 at h
  rw [map_sub, map_smul, haxis] at h
  exact sub_left_inj.mp h

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem coefficient_trivial_of_vertical_trivial
    (z : SphereBundleTotal Q)
    (f : MulAction.stabilizer (QuaternionicIsometries Q) z)
    (hvertical : ∀ v, isotropyVerticalRepresentation Q z f v = v) :
    ∀ a : Fin 3 → ℝ, coefficientAction Q f.1 z.1 a = a := by
  apply linear_eq_id_of_axis_and_vertical
    (coefficientSphereHomeomorph.symm z.2) (coefficientAction Q f.1 z.1)
  · exact congrArg Subtype.val (isotropy_fixes_coefficient Q z f)
  · intro v
    exact congrArg Subtype.val (hvertical v)

/-- A subgroup fixing a twistor point and its vertical line acts trivially
on the actual base quaternionic three-plane at that point. -/
theorem subgroup_coefficient_trivial_of_vertical_trivial
    (S : Subgroup (QuaternionicIsometries Q)) (z : SphereBundleTotal Q)
    (hfix : ∀ f ∈ S, f • z = z)
    (hvertical : ∀ f (hf : f ∈ S), ∀ v,
      isotropyVerticalRepresentation Q z ⟨f, hfix f hf⟩ v = v) :
    ∀ f ∈ S, ∀ a : Fin 3 → ℝ, coefficientAction Q f z.1 a = a := by
  intro f hf
  exact coefficient_trivial_of_vertical_trivial Q z ⟨f, hfix f hf⟩
    (hvertical f hf)

end
end QuaternionicSymmetry.ManifoldQuaternionicVerticalKernelTriviality
