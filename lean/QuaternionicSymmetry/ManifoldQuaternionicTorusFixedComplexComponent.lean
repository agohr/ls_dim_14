import QuaternionicSymmetry.ManifoldQuaternionicTwistorFixedComponentActual
import QuaternionicSymmetry.ManifoldQuaternionicTorusAction
import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff

/-! The fixed component of the actual torus representation is a compact
complex submanifold of the ambient twistor, using the proved compact-action
fixed-component atlas and the complex-tangent criterion. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent

open ManifoldQuaternionicSpanSymmetry
open ManifoldQuaternionicTorusAction
open ManifoldQuaternionicTwistorIsometryAction
open ManifoldQuaternionicTwistorLiftedFixedSet
open ManifoldQuaternionicTwistorComplexFixedAtlas
open ManifoldQuaternionicTwistorFixedComponentActual
open ManifoldTwistorLeBrunComplexAtlas
open ManifoldTwistorSphereCore
open ManifoldRiemannianFixedComponentGenericInput
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
variable {r : ℕ} (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
  (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (A : ContinuousTorusAction Q r)

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
private abbrev F := E × EuclideanSpace ℝ (Fin 2)

/-- The selected full-torus fixed component inside the actual twistor. -/
def component (z : SphereBundleTotal Q) : Set (SphereBundleTotal Q) :=
  connectedComponentIn (fixedSpherePoints Q A.imageSubgroup) z

/-- The full-torus fixed component lies in the connected component fixed by
the connected kernel of any character. No equality of the two components is
claimed. -/
theorem component_subset_connectedKernelComponent
    (μ : Fin r → ℤ) (z : SphereBundleTotal Q) :
    component Q A z ⊆ connectedComponentIn
      (fixedSpherePoints Q (A.connectedKernelImage Q μ)) z := by
  apply connectedComponentIn_mono z
  intro w hw
  apply (mem_fixedSpherePoints_iff Q (A.connectedKernelImage Q μ) w).mpr
  intro f hf
  apply (mem_fixedSpherePoints_iff Q A.imageSubgroup w).mp hw
  rcases hf with ⟨t, ht, rfl⟩
  exact ⟨t, rfl⟩

/-- The literal map of nested actual fixed-component subtypes. -/
def inclusionIntoConnectedKernelComponent (μ : Fin r → ℤ)
    (z : SphereBundleTotal Q) :
    ↥(component Q A z) →
      ↥(connectedComponentIn
        (fixedSpherePoints Q (A.connectedKernelImage Q μ)) z) :=
  Set.inclusion (component_subset_connectedKernelComponent Q A μ z)

theorem inclusionIntoConnectedKernelComponent_isEmbedding
    (μ : Fin r → ℤ) (z : SphereBundleTotal Q) :
    Topology.IsEmbedding (inclusionIntoConnectedKernelComponent Q A μ z) :=
  Topology.IsEmbedding.inclusion
    (component_subset_connectedKernelComponent Q A μ z)

/-- A point fixed by every actual torus element lies in the subgroup-fixed
set used by the real and complex fixed-component sources. -/
theorem mem_fixedSpherePoints_iff_torus (z : SphereBundleTotal Q) :
    z ∈ fixedSpherePoints Q A.imageSubgroup ↔
      ∀ t : Torus r, sphereTotalMap Q (A.representation t) z = z := by
  rw [mem_fixedSpherePoints_iff]
  constructor
  · intro hz t
    exact hz (A.representation t) ⟨t,rfl⟩
  · intro hz f hf
    obtain ⟨t,rfl⟩ := hf
    exact hz t

/-- The actual full-torus fixed component is closed, hence compact in the
compact twistor. Its subtype retains the ambient topology. -/
theorem isCompact_component (z : SphereBundleTotal Q)
    (hz : z ∈ fixedSpherePoints Q A.imageSubgroup) :
    IsCompact (component Q A z) :=
  (fixedSphereComponent_isClosed Q A.imageSubgroup hz).isCompact

def compactComponent (z : SphereBundleTotal Q)
    (hz : z ∈ fixedSpherePoints Q A.imageSubgroup) :
    CompactSpace ↥(component Q A z) :=
  isCompact_iff_compactSpace.mp (isCompact_component Q A z hz)

def nonemptyComponent (z : SphereBundleTotal Q)
    (hz : z ∈ fixedSpherePoints Q A.imageSubgroup) :
    Nonempty ↥(component Q A z) :=
  ⟨⟨z, mem_connectedComponentIn hz⟩⟩

/-- The general fixed-component theorems produce a complex atlas on the
literal full-torus fixed component, and its actual subtype inclusion is
holomorphic. This is a component, not the entire fixed set. -/
theorem exists_complexComponentAtlas
    (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)
    {n : ℕ} (C : CompatibleComplexAtlas Q D n)
    (hFixed : ManifoldQuaternionicTwistorFixedFromCompactAction.LiftedFixedComponents Q)
    (hComplex : ComplexSubmanifoldInput.ClosedComplexTangentSubmanifoldTheorem)
    (z : SphereBundleTotal Q)
    (hz : ∀ t : Torus r, sphereTotalMap Q (A.representation t) z = z) :
    letI := C.charts
    ∃ k : ℕ, ∃ R : FixedComponentAtlas (J (E := E))
        (liftedSet Q A.imageSubgroup) z k,
      ∃ m : ℕ, ∃ B : ComplexSubmanifoldInput.CompatibleComplexAtlas
        (realEmbeddedAtlas Q D C A.imageSubgroup R) m,
        k = 2 * m ∧
        (letI := B.charts
         ContMDiff 𝓘(ℂ,EuclideanSpace ℂ (Fin m))
           𝓘(ℂ,ComplexTwistorModel n) ∞
           (Subtype.val : ↥(connectedComponentIn
             (fixedSpherePoints Q A.imageSubgroup) z) → SphereBundleTotal Q)) := by
  letI := C.charts
  obtain ⟨k,R,m,B,hkm⟩ := exists_complexFixedAtlas Q D C hFixed hComplex
    A.imageSubgroup z ((mem_fixedSpherePoints_iff_torus Q A z).mpr hz)
  refine ⟨k,R,m,B,hkm,?_⟩
  letI := B.charts
  exact B.inclusion_holomorphic

end
end QuaternionicSymmetry.ManifoldQuaternionicTorusFixedComplexComponent
