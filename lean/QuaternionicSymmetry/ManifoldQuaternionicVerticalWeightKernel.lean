import QuaternionicSymmetry.ManifoldQuaternionicVerticalKernelTriviality
import QuaternionicSymmetry.ManifoldQuaternionicFixedTangentQuaternionic

/-! An actual vertical isotropy weight has quaternionically trivial kernel
at the base point. Faithfulness then gives a strictly smaller fixed-component
atlas of dimension divisible by four. Existence of integral weights and
comparison with the contact linearization are not assumed as source facts
by this internal implication. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicVerticalWeightKernel

open ManifoldQuaternionicSpanSymmetry ManifoldQuaternionicTorusAction
open ManifoldQuaternionicIsometryCoefficients ManifoldQuaternionicTwistorIsotropyWeight
open ManifoldQuaternionicVerticalKernelTriviality
open ManifoldQuaternionicFixedTangentQuaternionic QuaternionicTorusWeightKernel
open ManifoldTwistorVerticalComplex ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable {r : ℕ} (A : ContinuousTorusAction Q r)
  (z : SphereBundleTotal Q) (hz : ∀ t, A.representation t • z = z)

/-- Equality of the actual vertical isotropy representation with an
integral character, in the canonical complex structure on the plane. -/
def HasVerticalWeight (μ : Fin r → ℤ) : Prop :=
  ∀ t v, isotropyVerticalRepresentation Q z ⟨A.representation t, hz t⟩ v =
    ((weightCharacter μ t : Circle) : ℂ).re • v +
      ((weightCharacter μ t : Circle) : ℂ).im •
        verticalComplex _ v

include hz in
theorem base_mem_connectedKernelFixedSet (μ : Fin r → ℤ) :
    z.1 ∈ ContinuousTorusAction.connectedKernelFixedSet Q A μ := by
  intro f hf
  obtain ⟨t, _ht, rfl⟩ := hf
  exact isotropy_fixes_base Q z ⟨A.representation t, hz t⟩

theorem connectedKernel_coefficient_trivial (μ : Fin r → ℤ)
    (hweight : HasVerticalWeight Q A z hz μ) :
    ∀ f ∈ ContinuousTorusAction.connectedKernelImage Q A μ,
      ∀ a : Fin 3 → ℝ, coefficientAction Q f z.1 a = a := by
  intro f hf
  obtain ⟨t, ht, rfl⟩ := hf
  apply coefficient_trivial_of_vertical_trivial Q z ⟨A.representation t, hz t⟩
  intro v
  rw [hweight]
  have ht' : weightCharacter μ t = 1 := connectedWeightKernel_le_kernel μ ht
  rw [ht']
  simp

/-- The strict quaternionic-dimension decrease is derived from the actual
vertical weight, effective torus action and general fixed-submanifold
sources. No lower-dimensional quaternionic metric is claimed here. -/
theorem exists_smaller_fixedComponent_of_vertical_weight
    [T2Space M] [SecondCountableTopology M] [PreconnectedSpace M]
    (hjet : ManifoldRiemannianOneJetInput.RiemannianOneJetRigidityOnModel
      (E := E) (M := M))
    (hfixed : ManifoldRiemannianFixedComponentInput.RiemannianFixedComponentOnModel
      (E := E) (M := M))
    (hA : A.Faithful) (hr : 2 ≤ r)
    (μ : Fin r → ℤ) (hμ : μ ≠ 0)
    (hweight : HasVerticalWeight Q A z hz μ) (R : QuaternionicStructure E) :
    ∃ m : ℕ, m < R.quaternionicDimension ∧
      Nonempty (ManifoldRiemannianFixedComponentInput.FixedComponentAtlas
        Q (ContinuousTorusAction.connectedKernelImage Q A μ) z.1 (4*m)) := by
  obtain ⟨t, ht, hne⟩ := connectedKernel_has_nonidentity μ hr hμ
  apply exists_smaller_quaternionic_fixedComponent Q
    (ContinuousTorusAction.connectedKernelImage Q A μ) z.1
    (base_mem_connectedKernelFixedSet Q A z hz μ) hjet hfixed ?_
    (connectedKernel_coefficient_trivial Q A z hz μ hweight) R
  refine ⟨A.representation t, ⟨t, ht, rfl⟩, ?_⟩
  intro h
  apply hne
  apply hA
  simpa using h

end
end QuaternionicSymmetry.ManifoldQuaternionicVerticalWeightKernel
