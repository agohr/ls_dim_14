import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismGauge
import QuaternionicSymmetry.HolomorphicLineCorePullbackEquivSections
import QuaternionicSymmetry.HolomorphicLineGaugeSectionEquiv

/-! Canonical action of every actual holomorphic contact automorphism on
the complete space of holomorphic sections of the genuine contact line. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactAutomorphismSections

open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorContactAutomorphismGauge ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineGaugeSectionEquiv HolomorphicLineCorePullbackEquivSections
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)
  (C : HolomorphicContactData Q D n B)

def contactSectionEquiv (f : ContactAutomorphisms Q D B C.line) :
    letI := B.charts
    GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line) ≃ₗ[ℂ]
      GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  let IB := 𝓘(ℂ, ComplexTwistorModel n)
  let L := contactLineCore Q D C.line
  let P := pulledContactLine Q D B C.line f
  let gauge : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB P :=
    sectionLinearEquivOfLocalWitness IB L P
      (contactFiberEquiv Q D B C.line f)
      (hasLocalHolomorphicWitness Q D B C f)
  let pullback : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB P :=
    sectionLinearEquiv IB L f.1.toEquiv f.1.contMDiff f.1.symm.contMDiff
  exact gauge.trans pullback.symm

theorem contactSectionEquiv_apply_at_image
    (f : ContactAutomorphisms Q D B C.line)
    (s : letI := B.charts
      GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line))
    (z : SphereBundleTotal Q) :
    letI := B.charts
    (contactSectionEquiv Q D B C f s) (f.1 z) =
      contactFiberEquiv Q D B C.line f z (s z) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  let IB := 𝓘(ℂ, ComplexTwistorModel n)
  let L := contactLineCore Q D C.line
  let P := pulledContactLine Q D B C.line f
  let gauge : GlobalSections IB L ≃ₗ[ℂ] GlobalSections IB P :=
    sectionLinearEquivOfLocalWitness IB L P
      (contactFiberEquiv Q D B C.line f)
      (hasLocalHolomorphicWitness Q D B C f)
  exact sectionLinearEquiv_symm_apply_at_image IB L f.1.toEquiv
    f.1.contMDiff f.1.symm.contMDiff (gauge s) z

theorem contactSectionEquiv_one :
    letI := B.charts
    contactSectionEquiv Q D B C 1 = LinearEquiv.refl ℂ
      (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line)) := by
  letI := B.charts
  apply LinearEquiv.ext
  intro s
  apply ContMDiffSection.ext
  intro z
  have h := contactSectionEquiv_apply_at_image Q D B C 1 s z
  exact h.trans (contactFiberMap_one Q D B C.line z (s z))

theorem contactSectionEquiv_mul (f g : ContactAutomorphisms Q D B C.line) :
    letI := B.charts
    contactSectionEquiv Q D B C (f * g) =
      (contactSectionEquiv Q D B C g).trans (contactSectionEquiv Q D B C f) := by
  letI := B.charts
  apply LinearEquiv.ext
  intro s
  apply ContMDiffSection.ext
  intro y
  obtain ⟨z, rfl⟩ := (f * g).1.surjective y
  change (contactSectionEquiv Q D B C (f * g) s) ((f * g).1 z) =
    (contactSectionEquiv Q D B C f (contactSectionEquiv Q D B C g s))
      (f.1 (g.1 z))
  rw [contactSectionEquiv_apply_at_image, contactSectionEquiv_apply_at_image,
    contactSectionEquiv_apply_at_image]
  exact contactFiberMap_mul Q D B C.line f g z (s z)

/-- The derivative-induced representation of the full actual contact
automorphism group; no finite-dimensionality or reductivity is assumed. -/
def contactSectionRepresentation :
    letI := B.charts
    ContactAutomorphisms Q D B C.line →* Module.End ℂ
      (GlobalSections 𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D C.line)) := by
  letI := B.charts
  exact {
    toFun := fun f => (contactSectionEquiv Q D B C f).toLinearMap
    map_one' := by
      rw [contactSectionEquiv_one Q D B C]
      rfl
    map_mul' := by
      intro f g
      rw [contactSectionEquiv_mul Q D B C f g]
      rfl }

end
end QuaternionicSymmetry.ManifoldTwistorContactAutomorphismSections
