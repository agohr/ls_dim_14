import QuaternionicSymmetry.ManifoldQuaternionicIsometryContactComplexNaturality
import QuaternionicSymmetry.ManifoldTwistorLocalContactTangentSection
import QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections
import QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
import QuaternionicSymmetry.ManifoldTwistorLineCoreClasses

/-! The derivative-defined contact-line maps of an actual isometry form a
holomorphic gauge over its holomorphic twistor lift. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicIsometryContactGauge

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicIsometryContactFiberEquiv
open ManifoldQuaternionicIsometryContactComplexNaturality
open ManifoldQuaternionicIsometryComplexInfinity
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorLineCoreClasses
open ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorSphereCore
open HolomorphicLineCorePullback
open HolomorphicLineLocalGaugeRatio
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

local instance : Fact (Module.finrank ℝ
    ManifoldTwistorCoefficientSphere.EuclideanThree = 2 + 1) := ⟨by simp⟩
local instance (x : M) : ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ((sphereCore Q).Fiber x) := by
  change ChartedSpace (EuclideanSpace ℝ (Fin 2))
    ManifoldTwistorCoefficientSphere.geometricSphere
  infer_instance

/-- The actual contact line pulled back by the holomorphic lift of an
isometry, with its genuine holomorphic transition functions. -/
def pulledContactLine
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (L : HolomorphicContactLine Q D n B)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    HolomorphicLineCoreClasses.LineCore.{0}
      (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) := by
  letI := B.charts
  exact pullbackLineCore 𝓘(ℂ,ComplexTwistorModel n)
    𝓘(ℂ,ComplexTwistorModel n)
    (contactLineCore Q D L) (sphereTotalMap Q f)
    (sphereTotalMap_contMDiff_complex_infty Q D B f)

/-- Every point has a nonzero local holomorphic contact section whose
derivative image is holomorphic in the pullback line. -/
theorem hasLocalHolomorphicWitness
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    letI := (pulledContactLine Q D B C.line f).holomorphic
    HasLocalHolomorphicWitness 𝓘(ℂ,ComplexTwistorModel n)
      C.line.core (pulledContactLine Q D B C.line f).core
      (contactLineFiberEquiv Q D C.line f) := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  intro z
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
  let Φ := sphereTotalMap Q f
  let s : ∀ y : SphereBundleTotal Q, C.line.core.Fiber y :=
    fun y => C.line.contactFormComplex Q D y (σ y)
  let t : ∀ y : SphereBundleTotal Q,
      (pulledContactLine Q D B C.line f).core.Fiber y :=
    fun y => C.line.contactFormComplex Q D (Φ y)
      (mfderiv 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,ComplexTwistorModel n) Φ y (σ y))
  refine ⟨U,hU,hz,s,t,?_,?_,?_,?_⟩
  · exact hα
  · have hΦ : ContMDiff 𝓘(ℂ,ComplexTwistorModel n)
        𝓘(ℂ,ComplexTwistorModel n) ∞ Φ :=
      sphereTotalMap_contMDiff_complex_infty Q D B f
    have hTM : ContMDiff (𝓘(ℂ,ComplexTwistorModel n)).tangent
        (𝓘(ℂ,ComplexTwistorModel n)).tangent ∞
        (tangentMap 𝓘(ℂ,ComplexTwistorModel n)
          𝓘(ℂ,ComplexTwistorModel n) Φ) :=
      hΦ.contMDiff_tangentMap (by simp)
    have hAlong : ContMDiffOn 𝓘(ℂ,ComplexTwistorModel n)
        ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
        (fun y => (⟨Φ y,t y⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber)) U := by
      convert (C.contactHolomorphic.comp hTM).comp_contMDiffOn hσ using 1
    exact HolomorphicLineCorePullbackLocalSections.alongMap_contMDiffOn_pullback
      𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,ComplexTwistorModel n)
      C.line.core Φ hΦ U t hAlong
  · change C.line.contactFormComplex Q D z (σ z) ≠ 0
    rw [hσz,hv]
    exact hw
  · intro y _
    exact (contactLineFiberEquiv_contactFormComplex Q D B C.line f y (σ y)).symm

/-- A holomorphic gauge of actual line cores over the isometry's
holomorphic twistor lift, determined by the true contact differential. -/
def contactGauge
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (B : CompatibleComplexAtlas Q D n)
    (C : HolomorphicContactData Q D n B)
    (f : QuaternionicIsometries Q) :
    letI := B.charts
    letI := B.complexManifold
    letI := C.line.holomorphic
    letI := (pulledContactLine Q D B C.line f).holomorphic
    HolomorphicLineGauge.GaugeIso (IB := 𝓘(ℂ,ComplexTwistorModel n))
      C.line.core (pulledContactLine Q D B C.line f).core := by
  letI := B.charts
  letI := B.complexManifold
  letI := C.line.holomorphic
  letI := (pulledContactLine Q D B C.line f).holomorphic
  exact gaugeIsoOfLocalWitness 𝓘(ℂ,ComplexTwistorModel n)
    C.line.core (pulledContactLine Q D B C.line f).core
    (contactLineFiberEquiv Q D C.line f)
    (hasLocalHolomorphicWitness Q D B C f)

end
end QuaternionicSymmetry.ManifoldQuaternionicIsometryContactGauge
