import QuaternionicSymmetry.ComplexLinePowerTotalContinuity
import QuaternionicSymmetry.ManifoldQuaternionicContactPowerFiniteSections
import QuaternionicSymmetry.ManifoldQuaternionicContactSectionContinuity

/-! Joint continuity on every complete contact-power section space follows
from the actual joint contact-line total-space action. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerContinuity

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactSectionAction
open ManifoldQuaternionicIsometryContactPowerSections
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicContactPowerFiniteSections
open ManifoldQuaternionicContactJointContinuity
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback HolomorphicLineTensorPowerClasses
open ComplexLineFamilyContinuity ComplexLinePowerTotalContinuity
open ManifoldQuaternionicTorusAction ManifoldQuaternionicIsometryTopology
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private def baseAction (p : QuaternionicIsometries Q × SphereBundleTotal Q) :
    SphereBundleTotal Q := sphereTotalMap Q p.1 p.2

private def fiberAction
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    L.core.Fiber z →ₗ[ℂ] L.core.Fiber (baseAction Q (f,z)) :=
  (contactLineFiberEquiv Q D L f z).toLinearMap

theorem continuous_contactPowerTotalMap_of_joint_line
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hLine : Continuous (fun p : QuaternionicIsometries Q ×
      Bundle.TotalSpace ℂ C.line.core.Fiber =>
      contactLineTotalMap Q D C.line p.1 p.2)) :
    Continuous (powerTotalMap C.line.core k (baseAction Q)
      (fiberAction Q D C.line)) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  have hZero : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      (p.1, (⟨p.2,0⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber))) :=
    continuous_fst.prodMk
      ((Bundle.contMDiff_zeroSection (IB := 𝓘(ℂ,ComplexTwistorModel n))
        (n := ∞) ℂ C.line.core.Fiber).continuous.comp continuous_snd)
  have hφ : Continuous (baseAction Q) :=
    C.line.core.continuous_proj.comp (hLine.comp hZero)
  have hA : Continuous
      (totalMap C.line.core C.line.core (baseAction Q)
        (fiberAction Q D C.line)) := by
    simpa only [totalMap, baseAction, fiberAction,
      contactLineTotalMap, contactLineFiberEquiv_apply] using hLine
  exact continuous_powerTotalMap_of_lineTotalMap C.line.core k
    (baseAction Q) (fiberAction Q D C.line) hφ hA

theorem continuous_contactPowerOrbit_evaluation
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hLine : Continuous (fun p : QuaternionicIsometries Q ×
      Bundle.TotalSpace ℂ C.line.core.Fiber =>
      contactLineTotalMap Q D C.line p.1 p.2))
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    Continuous (fun f : QuaternionicIsometries Q =>
      (contactPowerSectionRepresentation Q D B C k f s) z) := by
  letI := B.charts
  letI := B.complexManifold
  let P := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore Q D C.line) k
  letI := P.holomorphic
  have hPower := continuous_contactPowerTotalMap_of_joint_line Q D B C k hLine
  have hZero : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      (p.1, (⟨p.2,0⟩ : Bundle.TotalSpace ℂ P.core.Fiber))) :=
    continuous_fst.prodMk
      ((Bundle.contMDiff_zeroSection (IB := 𝓘(ℂ,ComplexTwistorModel n))
        (n := ∞) ℂ P.core.Fiber).continuous.comp continuous_snd)
  have hLift : Continuous (fun p : QuaternionicIsometries Q × SphereBundleTotal Q =>
      sphereTotalMap Q p.1 p.2) := by
    exact P.core.continuous_proj.comp (hPower.comp hZero)
  have hInv : Continuous (fun f : QuaternionicIsometries Q =>
      sphereTotalMap Q f⁻¹ z) :=
    hLift.comp (continuous_inv.prodMk continuous_const)
  have hs : Continuous (fun x : SphereBundleTotal Q =>
      (⟨x,s x⟩ : Bundle.TotalSpace ℂ P.core.Fiber)) := s.contMDiff.continuous
  have h : Continuous (fun f : QuaternionicIsometries Q =>
      powerTotalMap C.line.core k (baseAction Q) (fiberAction Q D C.line)
        (f, ⟨sphereTotalMap Q f⁻¹ z, s (sphereTotalMap Q f⁻¹ z)⟩)) :=
    hPower.comp (continuous_id.prodMk (hs.comp hInv))
  have heq : (fun f : QuaternionicIsometries Q =>
      powerTotalMap C.line.core k (baseAction Q) (fiberAction Q D C.line)
        (f, ⟨sphereTotalMap Q f⁻¹ z, s (sphereTotalMap Q f⁻¹ z)⟩)) =
      (fun f => (⟨z,(contactPowerSectionRepresentation Q D B C k f s) z⟩ :
        Bundle.TotalSpace ℂ P.core.Fiber)) := by
    funext f
    let y := sphereTotalMap Q f⁻¹ z
    have hy : sphereTotalMap Q f y = z := smul_inv_smul f z
    have hv := contactPowerSectionEquiv_apply_at_image Q D B C f k s y
    have hstep : powerTotalMap C.line.core k (baseAction Q)
        (fiberAction Q D C.line) (f, ⟨y,s y⟩) =
        (⟨sphereTotalMap Q f y,
          (contactPowerSectionRepresentation Q D B C k f s)
            (sphereTotalMap Q f y)⟩ : Bundle.TotalSpace ℂ P.core.Fiber) := by
      apply Bundle.TotalSpace.ext
      · rfl
      · apply heq_of_eq
        exact hv.symm
    exact hstep.trans (congrArg (fun x : SphereBundleTotal Q =>
      (⟨x,(contactPowerSectionRepresentation Q D B C k f s) x⟩ :
        Bundle.TotalSpace ℂ P.core.Fiber)) hy)
  rw [heq] at h
  exact (FiberBundle.totalSpaceMk_isInducing ℂ P.core.Fiber z).continuous_iff.mpr h

theorem continuous_contactPowerAction_of_joint_line
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hLine : Continuous (fun p : QuaternionicIsometries Q ×
      Bundle.TotalSpace ℂ C.line.core.Fiber =>
      contactLineTotalMap Q D C.line p.1 p.2)) :
    letI := B.charts
    letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) =>
      contactPowerSectionRepresentation Q D B C k p.1 p.2) := by
  apply continuous_contactPowerAction_of_basis_orbits Q hFinite D B C k
  intro i z
  exact continuous_contactPowerOrbit_evaluation Q D B C k hLine _ z

theorem continuous_contactPowerAction_of_joint_tangent
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hTangent :
      letI := B.charts
      letI := B.complexManifold
      Continuous (fun p : QuaternionicIsometries Q ×
        TangentBundle 𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) =>
        tangentMap 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
          (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
    Continuous (fun p : QuaternionicIsometries Q ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) =>
      contactPowerSectionRepresentation Q D B C k p.1 p.2) :=
  continuous_contactPowerAction_of_joint_line Q hFinite D B C k
    (continuous_contactLineTotalMap_of_joint_tangent Q D B C hTangent)

def contactPowerTorusRepresentation
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ) :
    letI := B.charts
    Torus r →* Module.End ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k)) := by
  letI := B.charts
  exact (contactPowerSectionRepresentation Q D B C k).comp T.representation

theorem continuous_contactPowerTorusAction_of_joint_tangent
    [T2Space M] [CompactSpace M]
    (hFinite : HolomorphicLineFiniteSectionsSource.CompactHolomorphicLineSectionFiniteness)
    {r : ℕ} (T : ContinuousTorusAction Q r)
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hTangent :
      letI := B.charts
      letI := B.complexManifold
      Continuous (fun p : QuaternionicIsometries Q ×
        TangentBundle 𝓘(ℂ,ComplexTwistorModel n) (SphereBundleTotal Q) =>
        tangentMap 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
          (sphereTotalMap Q p.1) p.2)) :
    letI := B.charts
    letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
    Continuous (fun p : Torus r ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) =>
      contactPowerTorusRepresentation Q T D B C k p.1 p.2) := by
  letI := B.charts
  letI := contactPowerSectionsNormedAddCommGroup Q hFinite D B C k
  have hρ : Continuous T.representation :=
    continuous_representation_of_action Q T.representation T.continuous_action
  have hpair : Continuous (fun p : Torus r ×
      GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n)
          (contactLineCore Q D C.line) k) => (T.representation p.1, p.2)) :=
    (hρ.comp continuous_fst).prodMk continuous_snd
  simpa only [contactPowerTorusRepresentation, MonoidHom.comp_apply] using
    (continuous_contactPowerAction_of_joint_tangent Q hFinite D B C k hTangent).comp hpair

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerContinuity
