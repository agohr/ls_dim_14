import QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiHamiltonianSource
import QuaternionicSymmetry.ManifoldTwistorPositiveRicciInput

/-! Source-relative actual contact Hamiltonians, with the isometry action
identified using the already checked contact-form naturality. -/

namespace QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiHamiltonianApplication

open ManifoldTwistorNittaTakeuchiHamiltonianSource
open ManifoldTwistorContactAutomorphisms
open ManifoldTwistorContactContraction
open ManifoldTwistorContactAutomorphismSections
open ManifoldTwistorContactAutomorphismIsometrySections
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses
open HolomorphicVectorFieldPushforward
open HolomorphicLineCorePullback
open ManifoldPositiveQuaternionicKahlerGeometry ManifoldTwistorPositiveRicciInput
open scoped Manifold ContDiff
noncomputable section

private theorem field_natural_of_joint
    {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
      (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) :
    letI := B.charts
    letI := B.complexManifold
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [ChartedSpace V (ContactAutomorphisms Q D B C.line)]
    [IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    [LieGroup 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line)]
    (hJoint : letI := B.charts
      letI := B.complexManifold
      ContMDiff (𝓘(ℂ,V).prod 𝓘(ℂ,ComplexTwistorModel n))
        𝓘(ℂ,ComplexTwistorModel n) ∞
        (fun p : ContactAutomorphisms Q D B C.line × SphereBundleTotal Q =>
          p.1.1 p.2))
    (field : GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B C.line) →ₗ[ℂ]
      Fields (V := ComplexTwistorModel n) (Z := SphereBundleTotal Q))
    (hField : letI := B.charts
      letI := B.complexManifold
      ∀ (v : GroupLieAlgebra 𝓘(ℂ,V)
          (ContactAutomorphisms Q D B C.line)) (z : SphereBundleTotal Q),
        field v z =
          (mfderiv 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n)
            (fun f : ContactAutomorphisms Q D B C.line => f.1 z) 1) v),
    ∀ (f : ContactAutomorphisms Q D B C.line)
      (v : GroupLieAlgebra 𝓘(ℂ,V) (ContactAutomorphisms Q D B C.line)),
      field ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
        (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v) =
        pushForwardLinear f.1 (field v) := by
  letI := B.charts
  letI := B.complexManifold
  intro V _ _ _ _ _ hJoint field hField f v
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
    (I'' := 𝓘(ℂ,ComplexTwistorModel n)) (x := (1 : ContactAutomorphisms Q D B C.line))
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
  change (field ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
      (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v))
      (f.1 z) = pushForwardLinear f.1 (field v) (f.1 z)
  rw [pushForwardLinear_apply_at_image, hField v z]
  rw [hField ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
    (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v) (f.1 z)]
  simpa only [ContinuousLinearMap.comp_apply] using hDer

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

/-- The NT infinitesimal field map and the internally proved contact-form
naturality together identify the *actual* adjoint action on contact
Hamiltonians with the canonical section action. In particular, no character
twist is hidden in this equivalence. -/
theorem exists_hamiltonian_equiv
    (hNT : ContactHamiltonianConclusion Q D B C) :
    letI := B.charts
    letI := B.complexManifold
    letI : TopologicalSpace (ContactAutomorphisms Q D B C.line) := inferInstance
    let G := ContactAutomorphisms Q D B C.line
    ∃ (V : Type) (hNorm : NormedAddCommGroup V),
      letI : NormedAddCommGroup V := hNorm
      ∃ (hSpace : NormedSpace ℂ V) (hFinite : FiniteDimensional ℂ V)
        (hChart : ChartedSpace V G),
        letI : NormedSpace ℂ V := hSpace
        letI : FiniteDimensional ℂ V := hFinite
        letI : ChartedSpace V G := hChart
        ∃ hManifold : IsManifold 𝓘(ℂ,V) ∞ G,
          letI : IsManifold 𝓘(ℂ,V) ∞ G := hManifold
          ∃ hLie : LieGroup 𝓘(ℂ,V) ∞ G,
            letI : LieGroup 𝓘(ℂ,V) ∞ G := hLie
            ∃ Φ : GroupLieAlgebra 𝓘(ℂ,V) G ≃ₗ[ℂ]
                GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
                  (contactLineCore Q D C.line),
              (∀ (v : GroupLieAlgebra 𝓘(ℂ,V) G) (z : SphereBundleTotal Q),
                Φ v z = C.line.contactFormComplex Q D z
                  ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,ComplexTwistorModel n)
                    (fun f : G => f.1 z) 1) v)) ∧
              (∀ (f : G) (v : GroupLieAlgebra 𝓘(ℂ,V) G),
                Φ ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
                  (fun g : G => f * g * f⁻¹) 1) v) =
                  contactSectionEquiv Q D B C f (Φ v)) ∧
              (∀ (f : ManifoldQuaternionicSpanSymmetry.QuaternionicIsometries Q)
                (v : GroupLieAlgebra 𝓘(ℂ,V) G),
                Φ ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
                  (fun g : G =>
                    isometryContactLift Q D B C.line f * g *
                      (isometryContactLift Q D B C.line f)⁻¹) 1) v) =
                  ManifoldQuaternionicIsometryContactSections.contactSectionEquiv
                    Q D B C f (Φ v)) := by
  letI := B.charts
  letI := B.complexManifold
  letI : TopologicalSpace (ContactAutomorphisms Q D B C.line) := inferInstance
  obtain ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,hJoint,field,hField,hBij⟩ := hNT
  letI : NormedAddCommGroup V := hNorm
  letI : NormedSpace ℂ V := hSpace
  letI : FiniteDimensional ℂ V := hFinite
  letI : ChartedSpace V (ContactAutomorphisms Q D B C.line) := hChart
  letI : IsManifold 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line) := hManifold
  letI : LieGroup 𝓘(ℂ,V) ∞ (ContactAutomorphisms Q D B C.line) := hLie
  have hNat := field_natural_of_joint Q D B C hJoint field hField
  let Φ := LinearEquiv.ofBijective ((contraction Q D B C).comp field) hBij
  refine ⟨V,hNorm,hSpace,hFinite,hChart,hManifold,hLie,Φ,?_,?_,?_⟩
  · intro v z
    exact congrArg (fun w => C.line.contactFormComplex Q D z w) (hField v z)
  · intro f v
    change contraction Q D B C
        (field ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
          (fun g : ContactAutomorphisms Q D B C.line => f * g * f⁻¹) 1) v)) =
      contactSectionEquiv Q D B C f (contraction Q D B C (field v))
    rw [hNat f v]
    exact contraction_equivariant Q D B C f (field v)
  · intro f v
    change contraction Q D B C
        (field ((mfderiv 𝓘(ℂ,V) 𝓘(ℂ,V)
          (fun g : ContactAutomorphisms Q D B C.line =>
            isometryContactLift Q D B C.line f * g *
              (isometryContactLift Q D B C.line f)⁻¹) 1) v)) =
      ManifoldQuaternionicIsometryContactSections.contactSectionEquiv
        Q D B C f (contraction Q D B C (field v))
    rw [hNat (isometryContactLift Q D B C.line f) v]
    exact (contraction_equivariant Q D B C
      (isometryContactLift Q D B C.line f) (field v)).trans
      (congrArg (fun F => F (contraction Q D B C (field v)))
        (contactSectionEquiv_isometry Q D B C f))

/-- Apply NT on exactly the contact twistor selected by the normalized
positive-geometry source. This does not infer any algebraic structure. -/
theorem exists_normalized_hamiltonian_conclusion
    (hT1 : NormalizedPositiveRicciContactExistence)
    (hNT : ContactHamiltonianSource)
    (P : CompactConnectedPositiveQuaternionicKahlerGeometry (E := E) (M := M))
    (n : ℕ) (hn : 2 ≤ n) (hDim : Module.finrank ℝ E = 4*n)
    (hScalar : ∀ p y (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      ManifoldQuaternionicScalarCurvature.localScalarCurvature
        P.tangent P.connection p y hy =
        16 * (n : ℝ) * ((n : ℝ) + 2)) :
    ∃ B : CompatibleComplexAtlas P.tangent P.connection n,
      ∃ C : HolomorphicContactData P.tangent P.connection n B,
        ContactHamiltonianConclusion P.tangent P.connection B C := by
  obtain ⟨B,C,m,hm⟩ := hT1 P n hn hDim hScalar
  exact ⟨B,C.contact,hNT P n hn hDim B C⟩

end
end QuaternionicSymmetry.ManifoldTwistorNittaTakeuchiHamiltonianApplication
