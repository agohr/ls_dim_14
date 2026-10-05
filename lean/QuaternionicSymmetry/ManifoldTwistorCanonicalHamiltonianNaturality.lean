import QuaternionicSymmetry.ManifoldTwistorContactInfinitesimalAction
import QuaternionicSymmetry.ManifoldTwistorContactContraction

/-! Conjugation naturality of the *internally constructed* contact-group
infinitesimal action. This extracts the chain-rule argument already used in
the source-relative NT application, without importing a source-selected
field or any Hamiltonian bijection. -/

namespace QuaternionicSymmetry.ManifoldTwistorCanonicalHamiltonianNaturality

open ManifoldTwistorContactInfinitesimalAction
open ManifoldTwistorContactAutomorphisms
open HolomorphicVectorFieldPushforward
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 200000

variable {E M V : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

/-- The derivative of conjugation acts on actual orbit-derived fields by
the usual geometric pushforward. -/
theorem canonicalField_conjugation_natural
    [ChartedSpace V (ContactAutomorphisms Q D B C.line)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    [LieGroup 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    (hJoint :
      letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B C.line × SphereBundleTotal Q =>
          p.1.1 p.2))
    (f : ContactAutomorphisms Q D B C.line)
    (v : GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B C.line)) :
    letI := B.charts
    letI := B.complexManifold
    contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint
      ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v) =
    pushForwardLinear f.1
      (contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint v) := by
  letI := B.charts
  letI := B.complexManifold
  let field := contactInfinitesimalActionLinear (V := V) Q D B C.line hJoint
  have hField (w : GroupLieAlgebra 𝓘(ℂ,V)
      (ContactAutomorphisms Q D B C.line)) (z : SphereBundleTotal Q) :
      field w z =
        (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n)
          (fun g : ContactAutomorphisms Q D B C.line => g.1 z) 1) w :=
    contactInfinitesimalActionLinear_apply (V := V) Q D B C.line hJoint w z
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z,rfl⟩ := f.1.surjective y
  have hEval (w : SphereBundleTotal Q) :
      ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun g : ContactAutomorphisms Q D B C.line => g.1 w) := by
    exact hJoint.comp (contMDiff_id.prodMk contMDiff_const)
  have hConj : ContMDiff 𝓘(ℂ,V) 𝓘(ℂ,V) ∞
      (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) := by
    exact (contMDiff_mul_left (I := 𝓘(ℂ,V)) (n := ∞) (a := f)).comp
      (contMDiff_mul_right (I := 𝓘(ℂ,V)) (n := ∞) (a := f⁻¹))
  have hfun :
      (fun g : ContactAutomorphisms Q D B C.line =>
        (f * g * f⁻¹).1 (f.1 z)) =
      (fun g : ContactAutomorphisms Q D B C.line => f.1 (g.1 z)) := by
    funext g
    change f.1 (g.1 ((f⁻¹).1 (f.1 z))) = f.1 (g.1 z)
    rw [show (f⁻¹).1 (f.1 z) = z from f.1.symm_apply_apply z]
  have hLeft := mfderiv_comp (I := 𝓘(ℂ,V)) (I' := 𝓘(ℂ,V))
    (I'' := 𝓘(ℂ,ComplexTwistorModel n))
    (x := (1 : ContactAutomorphisms Q D B C.line))
    ((hEval (f.1 z)).mdifferentiableAt (by simp))
    (hConj.mdifferentiableAt (by simp))
  have hRight := mfderiv_comp (I := 𝓘(ℂ,V))
    (I' := 𝓘(ℂ,ComplexTwistorModel n))
    (I'' := 𝓘(ℂ,ComplexTwistorModel n))
    (x := (1 : ContactAutomorphisms Q D B C.line))
    (f.1.contMDiff.mdifferentiableAt (by simp))
    ((hEval z).mdifferentiableAt (by simp))
  rw [show (fun g : ContactAutomorphisms Q D B C.line =>
    g.1 (f.1 z)) ∘ (fun g => f * g * f⁻¹) =
    (fun g => f.1 (g.1 z)) from hfun] at hLeft
  rw [show f * (1 : ContactAutomorphisms Q D B C.line) * f⁻¹ = 1 by simp] at hLeft
  rw [show (1 : ContactAutomorphisms Q D B C.line).1 z = z by rfl] at hRight
  have hDer := congrArg (fun T : V →L[ℂ] ComplexTwistorModel n => T v)
    (hLeft.symm.trans hRight)
  change field ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
      (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v)
      (f.1 z) = pushForwardLinear f.1 (field v) (f.1 z)
  rw [pushForwardLinear_apply_at_image, hField v z]
  rw [hField ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
    (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v) (f.1 z)]
  simpa only [ContinuousLinearMap.comp_apply] using hDer

end
end QuaternionicSymmetry.ManifoldTwistorCanonicalHamiltonianNaturality
