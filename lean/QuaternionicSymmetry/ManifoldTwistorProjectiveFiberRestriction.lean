import QuaternionicSymmetry.ManifoldTwistorProjectiveFiberContactLine
import QuaternionicSymmetry.ProjectiveLineTangentDeterminant
import QuaternionicSymmetry.HolomorphicLineClassPullback
import QuaternionicSymmetry.HolomorphicLineCorePullbackLocalSections
import QuaternionicSymmetry.HolomorphicLineLocalGaugeRatio
import QuaternionicSymmetry.HolomorphicBundleLocalVector
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Restriction along the genuine holomorphic projective twistor fiber.
The actual contact form gives a holomorphic gauge from the CP¹ tangent
determinant line to the restricted contact line. No degree or Picard-group
classification is assumed in this comparison. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveFiberRestriction

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorSphereFiberInclusion
open ManifoldTwistorProjectiveFiberContactLine ManifoldTwistorProjectiveFiberHolomorphic
open ManifoldTwistorLeBrunComplexAtlas
open HolomorphicLineCorePullback HolomorphicLineCoreClasses
open HolomorphicLineLocalGaugeRatio HolomorphicBundleLocalVector
open ProjectiveLineTangentDeterminant FourDimensionalHalfSpinProjective
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

def restrictionHom {n : ℕ} (A : CompatibleComplexAtlas Q D n) (p : M) :
    letI := A.charts
    CoreClass.{0} (B := SphereBundleTotal Q) 𝓘(ℂ,ComplexTwistorModel n) →*
      CoreClass.{0} (B := ProjectiveSpinor) 𝓘(ℂ,Model) := by
  letI := A.charts
  exact HolomorphicLineClassPullback.pullbackHom
    𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,Model) (projectiveFiberInclusion Q p)
    (projectiveFiberInclusion_holomorphic Q D A p)

def restrictedContactCore {n : ℕ} (A : CompatibleComplexAtlas Q D n)
    (L : HolomorphicContactLine Q D n A) (p : M) :
    VectorBundleCore ℂ ProjectiveSpinor ℂ L.Index := by
  letI := A.charts
  exact pullbackCore L.core (projectiveFiberInclusion Q p)
    (projectiveFiberInclusion_holomorphic Q D A p).continuous

instance restrictedContactCore_holomorphic {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (L : HolomorphicContactLine Q D n A) (p : M) :
    (restrictedContactCore Q D A L p).IsContMDiff 𝓘(ℂ,Model) ∞ := by
  letI := A.charts
  letI := L.holomorphic
  exact pullbackCore_isContMDiff 𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,Model)
    L.core (projectiveFiberInclusion Q p) (projectiveFiberInclusion_holomorphic Q D A p)

def tangentContactFiberEquiv {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (L : HolomorphicContactLine Q D n A)
    (p : M) (s : ProjectiveSpinor) :
    tangentLineCore.core.Fiber s ≃ₗ[ℂ] (restrictedContactCore Q D A L p).Fiber s :=
  (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans (fiberContactEquiv Q D A L p s)

theorem contactRestriction_hasLocalWitness {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A)
    (p : M) :
    letI := tangentLineCore.holomorphic
    HasLocalHolomorphicWitness 𝓘(ℂ,Model) tangentLineCore.core
      (restrictedContactCore Q D A C.line p) (tangentContactFiberEquiv Q D A C.line p) := by
  letI := A.charts
  letI := A.complexManifold
  letI := C.line.holomorphic
  letI := tangentLineCore.holomorphic
  intro x
  let e := trivializationAt Model
    (TangentSpace 𝓘(ℂ,Model) : ProjectiveSpinor → Type _) x
  letI : MemTrivializationAtlas e := ⟨⟨_,rfl⟩⟩
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt
    Model (TangentSpace 𝓘(ℂ,Model) : ProjectiveSpinor → Type _) x
  obtain ⟨σ,hσ,hσx⟩ := exists_local_section_through 𝓘(ℂ,Model) e x hx (fun _ => 1)
  let f := projectiveFiberInclusion Q p
  let t : ∀ y : ProjectiveSpinor, (restrictedContactCore Q D A C.line p).Fiber y :=
    fun y => fiberContactMap Q D A C.line p y (σ y)
  refine ⟨e.baseSet,e.open_baseSet,hx,(fun y => σ y 0),t,?_,?_,?_,?_⟩
  · exact tangentLineSection_contMDiffOn e.baseSet σ hσ
  · have hf := projectiveFiberInclusion_holomorphic Q D A p
    have hTM := hf.contMDiff_tangentMap (m := ∞) (by simp)
    have hAlong : ContMDiffOn 𝓘(ℂ,Model)
        ((𝓘(ℂ,ComplexTwistorModel n)).prod 𝓘(ℂ,ℂ)) ∞
        (fun y => (⟨f y,t y⟩ : Bundle.TotalSpace ℂ C.line.core.Fiber)) e.baseSet := by
      convert (C.contactHolomorphic.comp hTM).comp_contMDiffOn hσ using 1
    exact HolomorphicLineCorePullbackLocalSections.alongMap_contMDiffOn_pullback
      𝓘(ℂ,ComplexTwistorModel n) 𝓘(ℂ,Model) C.line.core f hf e.baseSet t hAlong
  · change σ x 0 ≠ 0
    rw [hσx]
    exact one_ne_zero
  · intro y _
    change fiberContactMap Q D A C.line p y (fun _ => σ y 0) =
      fiberContactMap Q D A C.line p y (σ y)
    congr 1
    funext i
    exact congrArg (σ y) (Subsingleton.elim 0 i)

def contactRestrictionGauge {n : ℕ}
    (A : CompatibleComplexAtlas Q D n) (C : HolomorphicContactData Q D n A)
    (p : M) :
    letI := tangentLineCore.holomorphic
    HolomorphicLineGauge.GaugeIso (IB := 𝓘(ℂ,Model)) tangentLineCore.core
      (restrictedContactCore Q D A C.line p) := by
  letI := tangentLineCore.holomorphic
  exact gaugeIsoOfLocalWitness 𝓘(ℂ,Model) tangentLineCore.core
    (restrictedContactCore Q D A C.line p) (tangentContactFiberEquiv Q D A C.line p)
    (contactRestriction_hasLocalWitness Q D A C p)

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveFiberRestriction
