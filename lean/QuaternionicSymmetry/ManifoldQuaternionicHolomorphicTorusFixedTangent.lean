import QuaternionicSymmetry.ManifoldQuaternionicIsometryComplexAtlas
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction

/-! Genuine quaternionic-isometry tori act pointwise holomorphically on the
twistor space. Their infinitesimal common fixed space is complex for the
actual twistor almost-complex field and in the compatible complex atlas. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicHolomorphicTorusFixedTangent

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryTwistorComplex
open ManifoldQuaternionicIsometryComplexAtlas
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
variable (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)

/-- Each element of an actual continuous quaternionic-isometry torus has a
holomorphic lift to the checked twistor complex atlas. Joint continuity of
the lift is a separate group-action regularity question. -/
theorem torus_element_holomorphic {n r : ℕ}
    (B : CompatibleComplexAtlas Q D n)
    (A : ContinuousTorusAction Q r) (t : Torus r) :
    letI := B.charts
    MDifferentiable 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n)
      (sphereTotalMap Q (A.representation t)) :=
  sphereTotalMap_mdifferentiable_complex Q D B (A.representation t)

/-- Real tangent directions fixed by every actual torus lift at a common
fixed twistor point. The condition uses the true manifold derivative. -/
def fixedRealTangent {r : ℕ} (A : ContinuousTorusAction Q r)
    (z : SphereBundleTotal Q)
    (_hz : ∀ t, sphereTotalMap Q (A.representation t) z = z) :
    Submodule ℝ (TangentSpace (J (E := E)) z) where
  carrier := {v | ∀ t, mfderiv (J (E := E)) (J (E := E))
    (sphereTotalMap Q (A.representation t)) z v = v}
  zero_mem' := by intro t; exact map_zero _
  add_mem' := by
    intro u v hu hv t
    rw [map_add, hu t, hv t]
  smul_mem' := by
    intro c v hv t
    rw [map_smul, hv t]

/-- The actual torus-fixed tangent space is preserved by the quaternionic
twistor complex field. This is the key tangent-level input for a complex
fixed-submanifold theorem, but does not itself posit such an atlas. -/
theorem fixedRealTangent_complex_invariant {r : ℕ}
    (A : ContinuousTorusAction Q r)
    (z : SphereBundleTotal Q)
    (hz : ∀ t, sphereTotalMap Q (A.representation t) z = z)
    {v : TangentSpace (J (E := E)) z}
    (hv : v ∈ fixedRealTangent Q A z hz) :
    tangentComplex Q D z v ∈ fixedRealTangent Q A z hz := by
  intro t
  rw [sphereTotalMap_mfderiv_intertwines_tangentComplex Q D
    (A.representation t) z v, hz t]
  exact congrArg (tangentComplex Q D z) (hv t)

/-- In a compatible complex atlas, the common fixed tangent space is an
actual complex linear subspace of the model tangent. -/
def fixedComplexTangent {n r : ℕ}
    (B : CompatibleComplexAtlas Q D n)
    (A : ContinuousTorusAction Q r) (z : SphereBundleTotal Q)
    (_hz : ∀ t, sphereTotalMap Q (A.representation t) z = z) :
    letI := B.charts
    Submodule ℂ (ComplexTwistorModel n) := by
  letI := B.charts
  exact {
    carrier := {v | ∀ t, mfderiv 𝓘(ℂ,ComplexTwistorModel n)
      𝓘(ℂ,ComplexTwistorModel n)
      (sphereTotalMap Q (A.representation t)) z v = v}
    zero_mem' := by intro t; exact map_zero _
    add_mem' := by
      intro u v hu hv t
      rw [map_add, hu t, hv t]
    smul_mem' := by
      intro c v hv t
      rw [map_smul, hv t] }

end
end QuaternionicSymmetry.ManifoldQuaternionicHolomorphicTorusFixedTangent
