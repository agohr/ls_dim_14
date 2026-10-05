import QuaternionicSymmetry.ComplexLineFamilyContinuity
import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSectionAction
import QuaternionicSymmetry.ManifoldQuaternionicIsometryTopology

/-! The actual derivative-defined contact-line map is jointly continuous
once the joint twistor tangent action is continuous. The proof uses genuine
local tangent lifts of a nonzero contact section; it does not assume
continuity of the resulting contact-line action.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactJointContinuity

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicHolomorphicContactFiberAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactComplexNaturality
open ManifoldQuaternionicIsometryContactSectionAction
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldTwistorGlobalAlmostComplex
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

theorem continuous_contactLineTotalMap_of_joint_tangent
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hTangent :
      letI := B.charts
      letI := B.complexManifold
      Continuous (fun p : QuaternionicIsometries Q ×
        TangentBundle 𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) =>
        tangentMap 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
          (sphereTotalMap Q p.1) p.2)) :
    Continuous (fun p : QuaternionicIsometries Q ×
      Bundle.TotalSpace ℂ C.line.core.Fiber =>
      contactLineTotalMap Q D C.line p.1 p.2) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  have hZero : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      (p.1, (⟨p.2,0⟩ : TangentBundle
        𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q)))) :=
    continuous_fst.prodMk
      ((Bundle.contMDiff_zeroSection (IB := 𝓘(ℂ,ComplexTwistorModel n))
        (n := ∞) ℂ (TangentSpace 𝓘(ℂ,ComplexTwistorModel n) :
          SphereBundleTotal Q → Type _)).continuous.comp continuous_snd)
  have hLift : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereTotalMap Q p.1 p.2) :=
    (FiberBundle.continuous_proj (ComplexTwistorModel n)
      (TangentSpace 𝓘(ℂ,ComplexTwistorModel n) : SphereBundleTotal Q → Type _)).comp
        (hTangent.comp hZero)
  apply ComplexLineFamilyContinuity.continuous_totalMap_of_local_sections
    C.line.core C.line.core
    (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereTotalMap Q p.1 p.2)
    (contactLineFiberMap Q D C.line) hLift
  intro f z
  letI := contactQuotientComplexModule Q D z
  have hdim : Module.finrank ℂ (C.line.core.Fiber z) = 1 :=
    (C.line.quotientEquiv z).finrank_eq.trans
      (contactQuotient_complex_finrank Q D z)
  letI : Nontrivial (C.line.core.Fiber z) :=
    Module.nontrivial_of_finrank_pos (by rw [hdim]; omega)
  obtain ⟨w,hw⟩ := exists_ne (0 : C.line.core.Fiber z)
  obtain ⟨v,hv⟩ := C.line.contactFormComplex_surjective Q D z w
  obtain ⟨U,hU,hz,σ,hσz,hσ,hα⟩ :=
    ManifoldTwistorLocalContactTangentSection.exists_local_contact_section_with_tangent
      Q D B C z v
  let s : ∀ y : SphereBundleTotal Q, C.line.core.Fiber y :=
    fun y => C.line.contactFormComplex Q D y (σ y)
  refine ⟨s,?_,?_,?_⟩
  · exact hα.continuousOn.continuousAt (hU.mem_nhds hz)
  · change C.line.contactFormComplex Q D z (σ z) ≠ 0
    rw [hσz,hv]
    exact hw
  · have hσc : ContinuousAt (fun y =>
        (⟨y,σ y⟩ : TangentBundle 𝓘(ℂ,ComplexTwistorModel n)
          (SphereBundleTotal Q))) z :=
      hσ.continuousOn.continuousAt (hU.mem_nhds hz)
    have hpair : ContinuousAt (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        (p.1, (⟨p.2,σ p.2⟩ : TangentBundle
          𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q)))) (f,z) := by
      have hσpair : ContinuousAt
          (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
            (⟨p.2,σ p.2⟩ : TangentBundle
              𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q))) (f,z) := by
        exact hσc.comp_of_eq (continuous_snd.continuousAt (x := (f,z))) rfl
      exact continuousAt_fst.prodMk hσpair
    have h := (C.contactHolomorphic.continuous.comp hTangent).continuousAt.comp
      (f := fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        (p.1, (⟨p.2,σ p.2⟩ : TangentBundle
          𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q)))) hpair
    have heq : (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        C.line.contactFormTotal Q D
          (tangentMap 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
            (sphereTotalMap Q p.1) ⟨p.2,σ p.2⟩)) =
        (fun p => (⟨sphereTotalMap Q p.1 p.2,
          contactLineFiberMap Q D C.line p.1 p.2 (s p.2)⟩ :
          Bundle.TotalSpace ℂ C.line.core.Fiber)) := by
      funext p
      apply Bundle.TotalSpace.ext
      · rfl
      · apply heq_of_eq
        exact contactLineFiberEquiv_contactFormComplex Q D B C.line
          p.1 p.2 (σ p.2)
    change ContinuousAt
      (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
        C.line.contactFormTotal Q D
          (tangentMap 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
            (sphereTotalMap Q p.1) ⟨p.2,σ p.2⟩)) (f,z) at h
    rw [heq] at h
    exact h

end
end QuaternionicSymmetry.ManifoldQuaternionicContactJointContinuity
