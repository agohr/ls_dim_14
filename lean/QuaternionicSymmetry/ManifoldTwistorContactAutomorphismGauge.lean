import QuaternionicSymmetry.ManifoldTwistorContactAutomorphismFiber
import QuaternionicSymmetry.ManifoldTwistorLocalContactTangentSection
import QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections
import QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The canonical contact-line fiber maps of every actual holomorphic
contact automorphism form a holomorphic gauge. Holomorphicity follows from
local tangent sections and the actual contact form; it is not an extra
linearization hypothesis. -/

namespace QuaternionicSymmetry.ManifoldTwistorContactAutomorphismGauge

open ManifoldTwistorContactAutomorphisms ManifoldTwistorContactAutomorphismFiber
open ManifoldTwistorLeBrunComplexAtlas ManifoldTwistorSphereCore
open ManifoldTwistorLineCoreClasses HolomorphicLineCorePullback
open HolomorphicLineLocalGaugeRatio
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
  {n : ℕ} (B : CompatibleComplexAtlas Q D n)

def pulledContactLine (L : HolomorphicContactLine Q D n B)
    (f : ContactAutomorphisms Q D B L) :
    letI := B.charts
    HolomorphicLineCoreClasses.LineCore.{0}
      (B := SphereBundleTotal Q) 𝓘(ℂ, ComplexTwistorModel n) := by
  letI := B.charts
  letI := B.complexManifold
  exact pullbackLineCore 𝓘(ℂ, ComplexTwistorModel n)
    𝓘(ℂ, ComplexTwistorModel n) (contactLineCore Q D L) f.1 f.1.contMDiff

theorem hasLocalHolomorphicWitness (C : HolomorphicContactData Q D n B)
    (f : ContactAutomorphisms Q D B C.line) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    letI := (pulledContactLine Q D B C.line f).holomorphic
    HasLocalHolomorphicWitness 𝓘(ℂ, ComplexTwistorModel n)
      C.line.core (pulledContactLine Q D B C.line f).core
      (contactFiberEquiv Q D B C.line f) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  intro z
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
  let t : ∀ y : SphereBundleTotal Q,
      (pulledContactLine Q D B C.line f).core.Fiber y :=
    fun y => C.line.contactFormComplex Q D (f.1 y)
      (mfderiv 𝓘(ℂ, ComplexTwistorModel n)
        𝓘(ℂ, ComplexTwistorModel n) f.1 y (σ y))
  refine ⟨U, hU, hz, s, t, hα, ?_, ?_, ?_⟩
  · have hTM := f.1.contMDiff.contMDiff_tangentMap (by simp : ∞ + 1 ≤ ∞)
    have hAlong : ContMDiffOn 𝓘(ℂ, ComplexTwistorModel n)
        ((𝓘(ℂ, ComplexTwistorModel n)).prod 𝓘(ℂ, ℂ)) ∞
        (fun y => (⟨f.1 y, t y⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber)) U := by
      convert (C.contactHolomorphic.comp hTM).comp_contMDiffOn hσ using 1
    exact HolomorphicLineCorePullbackLocalSections.alongMap_contMDiffOn_pullback
      𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ, ComplexTwistorModel n)
      C.line.core f.1 f.1.contMDiff U t hAlong
  · change C.line.contactFormComplex Q D z (σ z) ≠ 0
    rw [hσz, hv]
    exact hw
  · intro y _
    exact contactFiberEquiv_contactForm Q D B C.line f y (σ y)

def contactGauge (C : HolomorphicContactData Q D n B)
    (f : ContactAutomorphisms Q D B C.line) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    letI := (pulledContactLine Q D B C.line f).holomorphic
    HolomorphicLineGauge.GaugeIso (IB := 𝓘(ℂ, ComplexTwistorModel n))
      C.line.core (pulledContactLine Q D B C.line f).core := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  exact gaugeIsoOfLocalWitness 𝓘(ℂ, ComplexTwistorModel n)
    C.line.core (pulledContactLine Q D B C.line f).core
    (contactFiberEquiv Q D B C.line f)
    (hasLocalHolomorphicWitness Q D B C f)

end
end QuaternionicSymmetry.ManifoldTwistorContactAutomorphismGauge
