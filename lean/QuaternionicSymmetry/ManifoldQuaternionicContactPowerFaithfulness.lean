import QuaternionicSymmetry.ManifoldQuaternionicContactPowerSectionAction
import QuaternionicSymmetry.HolomorphicLineCoreProjectiveFaithfulness
import QuaternionicSymmetry.ManifoldQuaternionicTwistorActionFaithful

/-! The actual contact-power action detects every nonidentity isometry
projectively when that power is very ample. Genuine ampleness therefore
supplies some positive power with this property.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerFaithfulness

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactPowerSections
open ManifoldQuaternionicContactPowerSectionAction
open ManifoldQuaternionicTwistorActionFaithful
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses
open HolomorphicLineCoreAmpleFiniteMap
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- The actual contact differential induces the standard fiber map on
each tensor power, with nonvanishing proved from the original equivalence. -/
def contactPowerFiberEquiv
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ) (z : SphereBundleTotal Q) :
    letI := B.charts
    let L := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k
    L.core.Fiber z ≃ₗ[ℂ] L.core.Fiber (sphereTotalMap Q f z) := by
  letI := B.charts
  change ℂ ≃ₗ[ℂ] ℂ
  let e : ℂ ≃ₗ[ℂ] ℂ := contactLineFiberEquiv Q D C.line f z
  have hne : e (1 : ℂ) ≠ 0 := by
    intro h
    exact one_ne_zero (e.injective (h.trans e.map_zero.symm))
  exact LinearEquiv.smulOfNeZero ℂ ℂ (e 1 ^ k) (pow_ne_zero k hne)

theorem contactPowerFiberEquiv_apply
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) (k : ℕ) (z : SphereBundleTotal Q) (v : ℂ) :
    contactPowerFiberEquiv Q D B C f k z v =
      contactScalar Q D C.line f z ^ k * v := rfl

/-- A nonzero scalar on all sections of a very ample contact power can
only come from the identity actual quaternionic isometry. -/
theorem eq_one_of_scalar_contactPowerAction
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (hVery : letI := B.charts; letI := B.complexManifold
      VeryAmpleCore 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k))
    (f : QuaternionicIsometries Q) (c : ℂˣ)
    (hc : letI := B.charts
      ∀ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k),
      contactPowerSectionRepresentation Q D B C k f s = (c : ℂ) • s) :
    f = 1 := by
  letI := B.charts
  letI := B.complexManifold
  let IB := 𝓘(ℂ,ComplexTwistorModel n)
  let L := powerCoreRep IB (contactLineCore Q D C.line) k
  have hbase : sphereTotalMap Q f = id :=
    HolomorphicLineCoreProjectiveFaithfulness.baseMap_eq_id_of_scalar_sectionMap
      IB L hVery (sphereTotalMap Q f) (contactPowerFiberEquiv Q D B C f k)
      (contactPowerSectionRepresentation Q D B C k f)
      (fun s z => contactPowerSectionEquiv_apply_at_image Q D B C f k s z) c hc
  apply sphereTotalMap_injective Q
  exact hbase.trans (funext (fun z => one_smul (QuaternionicIsometries Q) z)).symm

/-- Genuine ampleness supplies a positive tensor power whose actual
section action is projectively faithful; no separate faithfulness premise
or complete-system action is assumed. -/
theorem exists_contactPower_detects_scalars
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (hAmple : letI := B.charts; letI := B.complexManifold
      AmpleCore 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line)) :
    letI := B.charts
    ∃ k : ℕ, 0 < k ∧ ∀ (f : QuaternionicIsometries Q) (c : ℂˣ),
      (∀ s : GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k),
        contactPowerSectionRepresentation Q D B C k f s = (c : ℂ) • s) → f = 1 := by
  letI := B.charts
  letI := B.complexManifold
  obtain ⟨k,hk,hVery⟩ := hAmple
  exact ⟨k,hk,fun f c hc => eq_one_of_scalar_contactPowerAction Q D B C k hVery f c hc⟩

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerFaithfulness
