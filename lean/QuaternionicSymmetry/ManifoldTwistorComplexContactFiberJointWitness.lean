import QuaternionicSymmetry.ManifoldTwistorComplexContactFiberJointSection
import QuaternionicSymmetry.ManifoldTwistorLocalContactTangentSection

/-! A nonzero local contact section detects the actual complexified action
jointly in the torus parameter and the twistor base. This is data for the
general local-section criterion for a holomorphic map of line totals; it does
not claim that criterion or algebraicity of the action. -/

namespace QuaternionicSymmetry.ManifoldTwistorComplexContactFiberJointWitness

open ManifoldTwistorComplexContactFiberJointSection
open ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorComplexContactAction
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldQuaternionicTorusAction ManifoldQuaternionicTwistorIsometryAction
open TorusLaurentRepresentation ComplexTorusHolomorphicStructure
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)
  {r : ℕ} (A : ContinuousTorusAction Q r)
  (ρ : ComplexTorus r →* Equiv.Perm (SphereBundleTotal Q))
  (hJoint : letI := B.charts
    ContMDiff (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
      𝓘(ℂ,ComplexTwistorModel n) ∞
      (fun p : ComplexTorus r × SphereBundleTotal Q => ρ p.1 p.2))
  (hRestrict : ∀ (t : Torus r) (z : SphereBundleTotal Q),
    ρ (compactInclusion r t) z = sphereTotalMap Q (A.representation t) z)

/-- Around every twistor point, one nonzero contact-line section and its
image under the canonical action are jointly holomorphic. -/
theorem exists_local_nonzero_joint_section (z : SphereBundleTotal Q) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    ∃ U : Set (SphereBundleTotal Q), IsOpen U ∧ z ∈ U ∧
      ∃ s : ∀ y : SphereBundleTotal Q, C.line.core.Fiber y,
        s z ≠ 0 ∧
        ContMDiffOn 𝓘(ℂ,ComplexTwistorModel n)
          (𝓘(ℂ,ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
          (fun y => (⟨y,s y⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber)) U ∧
        ContMDiffOn
          (𝓘(ℂ,Fin r → ℂ).prod 𝓘(ℂ,ComplexTwistorModel n))
          (𝓘(ℂ,ComplexTwistorModel n).prod 𝓘(ℂ,ℂ)) ∞
          (fun q : ComplexTorus r × SphereBundleTotal Q =>
            (⟨ρ q.1 q.2,
              contactFiberEquiv Q D B C.line
                (complexContactAction Q D B C A ρ hJoint hRestrict q.1) q.2
                (s q.2)⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber))
          (Set.univ ×ˢ U) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI : Nontrivial (C.line.core.Fiber z) := by
    change Nontrivial ℂ
    infer_instance
  obtain ⟨w, hw⟩ := exists_ne (0 : C.line.core.Fiber z)
  obtain ⟨v, hv⟩ := C.line.contactFormComplex_surjective Q D z w
  obtain ⟨U, hU, hz, σ, hσz, hσ, hα⟩ :=
    ManifoldTwistorLocalContactTangentSection.exists_local_contact_section_with_tangent
      Q D B C z v
  let s : ∀ y : SphereBundleTotal Q, C.line.core.Fiber y :=
    fun y => C.line.contactFormComplex Q D y (σ y)
  refine ⟨U,hU,hz,s,?_,hα,?_⟩
  · change C.line.contactFormComplex Q D z (σ z) ≠ 0
    rw [hσz,hv]
    exact hw
  · exact contactFiberEquiv_localSection_joint_holomorphic
      Q D B C A ρ hJoint hRestrict U σ hσ

end
end QuaternionicSymmetry.ManifoldTwistorComplexContactFiberJointWitness
