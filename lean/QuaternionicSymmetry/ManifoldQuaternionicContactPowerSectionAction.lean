import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactPowerSections
import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactSectionAction

/-! The genuine contact-power section equivalences satisfy the isometry
group laws. Their scalar cocycle is derived from the actual contact
differential composition, not postulated as a linearization.
-/

namespace QuaternionicSymmetry.ManifoldQuaternionicContactPowerSectionAction

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactSectionAction
open ManifoldQuaternionicIsometryContactPowerSections
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineTensorPowerClasses
open scoped Manifold ContDiff
noncomputable section
set_option maxHeartbeats 50000
set_option maxRecDepth 512

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

/-- Pointwise scalar in the actual preferred fibers. No global continuity
of this preferred-coordinate function is asserted. -/
def contactScalar
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (f : QuaternionicIsometries Q) (z : SphereBundleTotal Q) : ℂ :=
  contactLineFiberEquiv Q D L f z (1 : ℂ)

theorem contactScalar_one
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B) (z : SphereBundleTotal Q) :
    contactScalar Q D L 1 z = 1 := by
  have h := contactLineFiberMap_one Q D L z (1 : ℂ)
  simpa only [contactScalar, contactLineFiberEquiv_apply, cast_eq] using h

theorem contactScalar_mul
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} {B : CompatibleComplexAtlas Q D n}
    (L : HolomorphicContactLine Q D n B)
    (f g : QuaternionicIsometries Q) (z : SphereBundleTotal Q) :
    contactScalar Q D L (f * g) z =
      contactScalar Q D L f (sphereTotalMap Q g z) * contactScalar Q D L g z := by
  let ef : ℂ ≃ₗ[ℂ] ℂ := contactLineFiberEquiv Q D L f (sphereTotalMap Q g z)
  have hv : (show ℂ from ManifoldQuaternionicHolomorphicContactFiberAction.contactLineFiberMap
      Q D L (f * g) z (1 : ℂ)) =
      (show ℂ from ManifoldQuaternionicHolomorphicContactFiberAction.contactLineFiberMap
        Q D L f (sphereTotalMap Q g z)
          (ManifoldQuaternionicHolomorphicContactFiberAction.contactLineFiberMap Q D L g z
            (1 : ℂ))) :=
    @eq_of_heq ℂ _ _ (contactLineFiberMap_mul Q D L f g z (1 : ℂ))
  have h : contactScalar Q D L (f * g) z = ef (contactScalar Q D L g z) := by
    simp only [contactScalar, ef, contactLineFiberEquiv_apply]
    exact hv
  rw [h]
  have hlin := ef.map_smul (contactScalar Q D L g z) (1 : ℂ)
  simpa only [smul_eq_mul, mul_one, one_mul, mul_comm] using hlin

theorem contactPowerSectionEquiv_one
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ) :
    letI := B.charts
    contactPowerSectionEquiv Q D B C 1 k = LinearEquiv.refl ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)) := by
  letI := B.charts
  apply LinearEquiv.ext
  intro s
  apply ContMDiffSection.ext
  intro z
  have h := contactPowerSectionEquiv_apply_at_image Q D B C 1 k s z
  change (contactPowerSectionEquiv Q D B C 1 k s) (sphereTotalMap Q 1 z) =
    contactScalar Q D C.line 1 z ^ k * (show ℂ from s z) at h
  rw [contactScalar_one, one_pow, one_mul] at h
  have hz : sphereTotalMap Q (1 : QuaternionicIsometries Q) z = z :=
    one_smul (QuaternionicIsometries Q) z
  rw [hz] at h
  exact h

theorem contactPowerSectionEquiv_mul
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ)
    (f g : QuaternionicIsometries Q) :
    letI := B.charts
    contactPowerSectionEquiv Q D B C (f * g) k =
      (contactPowerSectionEquiv Q D B C g k).trans
        (contactPowerSectionEquiv Q D B C f k) := by
  letI := B.charts
  apply LinearEquiv.ext
  intro s
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z,rfl⟩ := (MulAction.toPerm (f * g)).surjective y
  let L := powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k
  let ev : GlobalSections 𝓘(ℂ,ComplexTwistorModel n) L → SphereBundleTotal Q → ℂ :=
    fun t x => t x
  let ρ := contactPowerSectionEquiv Q D B C
  have hfg : ev (ρ (f * g) k s) (sphereTotalMap Q (f * g) z) =
      contactScalar Q D C.line (f * g) z ^ k * ev s z :=
    contactPowerSectionEquiv_apply_at_image Q D B C (f * g) k s z
  have hg : ev (ρ g k s) (sphereTotalMap Q g z) =
      contactScalar Q D C.line g z ^ k * ev s z :=
    contactPowerSectionEquiv_apply_at_image Q D B C g k s z
  have hf : ev (ρ f k (ρ g k s)) (sphereTotalMap Q f (sphereTotalMap Q g z)) =
      contactScalar Q D C.line f (sphereTotalMap Q g z) ^ k *
        ev (ρ g k s) (sphereTotalMap Q g z) :=
    contactPowerSectionEquiv_apply_at_image Q D B C f k
      (contactPowerSectionEquiv Q D B C g k s) (sphereTotalMap Q g z)
  have hz : sphereTotalMap Q (f * g) z = sphereTotalMap Q f (sphereTotalMap Q g z) :=
    mul_smul f g z
  change ev (ρ (f * g) k s) (sphereTotalMap Q (f * g) z) =
    ev (ρ f k (ρ g k s)) (sphereTotalMap Q (f * g) z)
  calc
    _ = contactScalar Q D C.line (f * g) z ^ k * ev s z := hfg
    _ = contactScalar Q D C.line f (sphereTotalMap Q g z) ^ k *
        (contactScalar Q D C.line g z ^ k * ev s z) := by
      rw [contactScalar_mul, mul_pow, mul_assoc]
    _ = contactScalar Q D C.line f (sphereTotalMap Q g z) ^ k *
        ev (ρ g k s) (sphereTotalMap Q g z) :=
      congrArg (fun a : ℂ => contactScalar Q D C.line f (sphereTotalMap Q g z) ^ k * a) hg.symm
    _ = ev (ρ f k (ρ g k s)) (sphereTotalMap Q f (sphereTotalMap Q g z)) := hf.symm
    _ = _ := congrArg (ev (ρ f k (ρ g k s))) hz.symm

/-- The full global section space of every genuine contact power carries
the derived complex-linear isometry representation. -/
def contactPowerSectionRepresentation
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B) (k : ℕ) :
    letI := B.charts
    QuaternionicIsometries Q →* Module.End ℂ
      (GlobalSections 𝓘(ℂ,ComplexTwistorModel n)
        (powerCoreRep 𝓘(ℂ,ComplexTwistorModel n) (contactLineCore Q D C.line) k)) := by
  letI := B.charts
  exact {
    toFun := fun f => (contactPowerSectionEquiv Q D B C f k).toLinearMap
    map_one' := by rw [contactPowerSectionEquiv_one Q D B C k]; rfl
    map_mul' := by intro f g; rw [contactPowerSectionEquiv_mul Q D B C k f g]; rfl }

end
end QuaternionicSymmetry.ManifoldQuaternionicContactPowerSectionAction
