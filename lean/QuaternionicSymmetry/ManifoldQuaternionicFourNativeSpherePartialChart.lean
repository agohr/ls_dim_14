import QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereGeometricLocal

/-! Genuine open partial charts of the independently topologized native Hodge
sphere.  The source is open in the native vector-bundle subspace topology. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSpherePartialChart

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSmoothCore
open ManifoldQuaternionicFourNativeSphereBundleEquiv
open ManifoldQuaternionicFourNativeSphereLocalTrivialization
open ManifoldQuaternionicFourNativeSphereGeometricLocal
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (hdim : Module.finrank ℝ E = 4)

local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : TopologicalSpace (nativeTwoFormVectorCore Q).TotalSpace :=
  (nativeTwoFormVectorCore Q).toTopologicalSpace
local instance : TopologicalSpace (NativeSphereBundleTotal Q) := by
  unfold NativeSphereBundleTotal
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (nativeLocalSphereTotal Q i) := by
  unfold nativeLocalSphereTotal
  infer_instance
local instance (i : atlas E M) : TopologicalSpace (geometricLocalDomain Q i) := by
  unfold geometricLocalDomain
  infer_instance

def nativeChartSource (i : atlas E M) : Set (NativeSphereBundleTotal Q) :=
  {p | p.1.1 ∈ Q.frames.adaptedCore.baseSet i}

def nativeChartTarget (i : atlas E M) : Set (M × geometricSphere) :=
  {p | p.1 ∈ Q.frames.adaptedCore.baseSet i}

theorem nativeChartSource_open (i : atlas E M) :
    IsOpen (nativeChartSource Q i) := by
  have hproj : Continuous (fun p : NativeSphereBundleTotal Q => p.1.1) :=
    (nativeTwoFormVectorCore Q).continuous_proj.comp continuous_subtype_val
  exact (Q.frames.adaptedCore.isOpen_baseSet i).preimage hproj

theorem nativeChartTarget_open (i : atlas E M) :
    IsOpen (nativeChartTarget Q i) :=
  (Q.frames.adaptedCore.isOpen_baseSet i).preimage continuous_fst

/-- A local chart built from the independent native sphere form, not by
transporting the pre-existing twistor smooth atlas.  A witness of the open
patch avoids a spurious nonemptiness assumption when an adapted chart has
empty base set. -/
def nativeSpherePartialChart (i : atlas E M)
    (p₀ : nativeLocalSphereTotal Q i) :
    OpenPartialHomeomorph (NativeSphereBundleTotal Q) (M × geometricSphere) := by
  letI : Nonempty (nativeLocalSphereTotal Q i) := ⟨p₀⟩
  letI : Nonempty (geometricLocalDomain Q i) :=
    ⟨(nativeGeometricLocalHomeomorph Q hdim i) p₀⟩
  letI : Nonempty {x // x ∈ nativeChartSource Q i} := ⟨⟨p₀.1,p₀.2⟩⟩
  letI : Nonempty {x // x ∈ nativeChartTarget Q i} :=
    ⟨⟨(nativeGeometricLocalHomeomorph Q hdim i p₀).1,
      (nativeGeometricLocalHomeomorph Q hdim i p₀).2⟩⟩
  let eS : OpenPartialHomeomorph (nativeLocalSphereTotal Q i)
      (NativeSphereBundleTotal Q) :=
    (nativeChartSource_open Q i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  let eT : OpenPartialHomeomorph (geometricLocalDomain Q i)
      (M × geometricSphere) :=
    (nativeChartTarget_open Q i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
  exact eS.symm.trans
    ((nativeGeometricLocalHomeomorph Q hdim i).toOpenPartialHomeomorph.trans eT)

theorem nativeSpherePartialChart_source (i : atlas E M)
    (p₀ : nativeLocalSphereTotal Q i) :
    (nativeSpherePartialChart Q hdim i p₀).source = nativeChartSource Q i := by
  simp [nativeSpherePartialChart, nativeChartSource]
  exact Subtype.range_val

theorem nativeSpherePartialChart_target (i : atlas E M)
    (p₀ : nativeLocalSphereTotal Q i) :
    (nativeSpherePartialChart Q hdim i p₀).target = nativeChartTarget Q i := by
  simp [nativeSpherePartialChart, nativeChartTarget]
  exact Subtype.range_val

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSpherePartialChart
