import QuaternionicSymmetry.ManifoldQuaternionicContactJointContinuity
import QuaternionicSymmetry.ManifoldQuaternionicContactFiniteSections
import QuaternionicSymmetry.ManifoldQuaternionicTorusContactSections

/-! Continuity of the genuine action on all holomorphic contact sections.
The moving section values are handled as bundle total-space points; raw
preferred fiber coordinates are used only at a fixed base point. The joint
twistor tangent action remains an explicit internal analytic obligation.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactSectionContinuity

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactSections
open ManifoldQuaternionicIsometryContactSectionAction
open ManifoldQuaternionicContactJointContinuity
open ManifoldQuaternionicContactFiniteSections
open ManifoldQuaternionicTorusContactSections
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Continuity of the actual line action implies continuity of each section
orbit evaluated at a fixed point. Moving-base values are never treated as
globally continuous preferred-frame scalars. -/
theorem continuous_contactSectionOrbit_evaluation
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hLine : Continuous (fun p : QuaternionicIsometries Q ×
      Bundle.TotalSpace ℂ C.line.core.Fiber =>
      contactLineTotalMap Q D C.line p.1 p.2))
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    Continuous (fun f : QuaternionicIsometries Q =>
      (contactSectionRepresentation Q D B C f s) z) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  have hZero : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      (p.1, (⟨p.2,0⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber))) :=
    continuous_fst.prodMk
      ((Bundle.contMDiff_zeroSection (IB := 𝓘(ℂ,ComplexTwistorModel n))
        (n := ∞) ℂ C.line.core.Fiber).continuous.comp continuous_snd)
  have hLift : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereTotalMap Q p.1 p.2) :=
    C.line.core.continuous_proj.comp (hLine.comp hZero)
  have hInv : Continuous (fun f : QuaternionicIsometries Q =>
      sphereTotalMap Q f⁻¹ z) :=
    hLift.comp (continuous_inv.prodMk continuous_const)
  have hs : Continuous (fun x : SphereBundleTotal Q =>
      (⟨x,s x⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber)) := s.contMDiff.continuous
  have h : Continuous (fun f : QuaternionicIsometries Q =>
      contactLineTotalMap Q D C.line f
        ⟨sphereTotalMap Q f⁻¹ z, s (sphereTotalMap Q f⁻¹ z)⟩) :=
    hLine.comp (continuous_id.prodMk (hs.comp hInv))
  have heq : (fun f : QuaternionicIsometries Q =>
      contactLineTotalMap Q D C.line f
        ⟨sphereTotalMap Q f⁻¹ z, s (sphereTotalMap Q f⁻¹ z)⟩) =
      (fun f => (⟨z,(contactSectionRepresentation Q D B C f s) z⟩ :
        Bundle.TotalSpace ℂ C.line.core.Fiber)) := by
    funext f
    let y := sphereTotalMap Q f⁻¹ z
    have hy : sphereTotalMap Q f y = z := smul_inv_smul f z
    have hv := contactSectionEquiv_apply_at_image Q D B C f s y
    have hstep : contactLineTotalMap Q D C.line f ⟨y,s y⟩ =
        (⟨sphereTotalMap Q f y,
          (contactSectionRepresentation Q D B C f s) (sphereTotalMap Q f y)⟩ :
          Bundle.TotalSpace ℂ C.line.core.Fiber) := by
      apply Bundle.TotalSpace.ext
      · rfl
      · apply heq_of_eq
        exact hv.symm
    exact hstep.trans (congrArg (fun x : SphereBundleTotal Q =>
      (⟨x,(contactSectionRepresentation Q D B C f s) x⟩ :
        Bundle.TotalSpace ℂ C.line.core.Fiber)) hy)
  rw [heq] at h
  exact (FiberBundle.totalSpaceMk_isInducing ℂ C.line.core.Fiber z).continuous_iff.mpr h

/-- Cartan–Serre and the finite-basis criterion convert genuine line-action
continuity into joint continuity on the complete contact-section space. -/
theorem continuous_contactSectionAction_of_joint_line
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hLine : Continuous (fun p : QuaternionicIsometries Q ×
      Bundle.TotalSpace ℂ C.line.core.Fiber =>
      contactLineTotalMap Q D C.line p.1 p.2)) :
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) =>
      contactSectionRepresentation Q D B C p.1 p.2) := by
  apply continuous_contactSectionAction_of_basis_orbits Q hFinite D B C
  intro i z
  exact continuous_contactSectionOrbit_evaluation Q D B C hLine _ z

/-- The actual joint twistor tangent action is the sole remaining analytic
input for continuity of the finite contact-section representation. No
pointwise section or contact-line continuity is separately supplied. -/
theorem continuous_contactSectionAction_of_joint_tangent
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
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
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) =>
      contactSectionRepresentation Q D B C p.1 p.2) :=
  continuous_contactSectionAction_of_joint_line Q hFinite D B C
    (continuous_contactLineTotalMap_of_joint_tangent Q D B C hTangent)

/-- Restriction to the actual compact torus uses its already proved
compact-open continuity, with the same genuine twistor tangent obligation. -/
theorem continuous_contactTorusAction_of_joint_tangent
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    {r : ℕ} (T : ManifoldQuaternionicTorusAction.ContinuousTorusAction Q r)
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
    letI := B.charts
    letI := contactSectionsNormedAddCommGroup Q hFinite D B C
    Continuous (fun p : ManifoldQuaternionicTorusAction.Torus r ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) =>
      contactTorusRepresentation Q T D B C p.1 p.2) :=
  continuous_contactTorusAction_of_isometryAction Q T D B C hFinite
    (continuous_contactSectionAction_of_joint_tangent Q hFinite D B C hTangent)

end
end QuaternionicSymmetry.ManifoldQuaternionicContactSectionContinuity
