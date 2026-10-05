import QuaternionicSymmetry.ManifoldQuaternionicFourNativeNegativeSphereSet
import QuaternionicSymmetry.ManifoldQuaternionicFourNativeCoefficientSmooth

/-! Explicit local coordinates for the negative-unit sphere inside the
independent native two-form bundle. The inverse is supplied by actual frame
evaluations, not by transported twistor topology. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCharts

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourNativeSphereFormSmooth
open ManifoldQuaternionicFourNativeNegativeSphereSet
open ManifoldQuaternionicFourNativeCoefficientExtraction
open ManifoldQuaternionicFourNativeCoefficientSmooth
open ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereBundle
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

def coefficientLocalDomain (i : atlas E M) :=
  {p : M × coefficientSphere // p.1 ∈ Q.frames.adaptedCore.baseSet i}

def nativeLocalDomain (i : atlas E M) :=
  {p : M × (E [⋀^Fin 2]→L[ℝ] ℝ) //
    p.1 ∈ Q.frames.adaptedCore.baseSet i ∧
    p.2 ∈ nativeLocalSphereSet Q i p.1}

local instance coefficientLocalDomain_topology (i : atlas E M) :
    TopologicalSpace (coefficientLocalDomain Q i) := by
  unfold coefficientLocalDomain
  infer_instance

local instance nativeLocalDomain_topology (i : atlas E M) :
    TopologicalSpace (nativeLocalDomain Q i) := by
  unfold nativeLocalDomain
  infer_instance

def localNativeMap (i : atlas E M) :
    coefficientLocalDomain Q i → nativeLocalDomain Q i :=
  fun p => ⟨(p.1.1,nativeSphereForm Q i
      (p.1.1,coefficientSphereHomeomorph p.1.2)),
    ⟨p.2, ⟨p.1.2,rfl⟩⟩⟩

private theorem raw_unit (i : atlas E M)
    (p : nativeLocalDomain Q i) :
    squareNorm (nativeCoefficientRaw Q hdim i p.1.1 p.1.2) = 1 := by
  obtain ⟨a,ha⟩ := p.2.2
  rw [ha, nativeCoefficientRaw_map Q hdim i p.1.1 p.2.1
    (coefficientSphereHomeomorph a)]
  exact a.2

def localNativeInverse (i : atlas E M) :
    nativeLocalDomain Q i → coefficientLocalDomain Q i :=
  fun p => ⟨(p.1.1,
      ⟨nativeCoefficientRaw Q hdim i p.1.1 p.1.2,
        raw_unit Q hdim i p⟩), p.2.1⟩

theorem localNativeInverse_left (i : atlas E M)
    (p : coefficientLocalDomain Q i) :
    localNativeInverse Q hdim i (localNativeMap Q i p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact nativeCoefficientRaw_map Q hdim i p.1.1 p.2
      (coefficientSphereHomeomorph p.1.2)

theorem localNativeInverse_right (i : atlas E M)
    (p : nativeLocalDomain Q i) :
    localNativeMap Q i (localNativeInverse Q hdim i p) = p := by
  obtain ⟨a,ha⟩ := p.2.2
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change nativeSphereForm Q i
      (p.1.1,coefficientSphereHomeomorph
        (⟨nativeCoefficientRaw Q hdim i p.1.1 p.1.2,
          raw_unit Q hdim i p⟩ : coefficientSphere)) = p.1.2
    have hcoeff := nativeCoefficientRaw_map Q hdim i p.1.1 p.2.1
      (coefficientSphereHomeomorph a)
    have hraw : nativeCoefficientRaw Q hdim i p.1.1 p.1.2 = a.1 := by
      rw [ha]
      simpa using hcoeff
    have heq : (⟨nativeCoefficientRaw Q hdim i p.1.1
        p.1.2,
          raw_unit Q hdim i p⟩ : coefficientSphere) = a := by
      apply Subtype.ext
      exact hraw
    rw [heq]
    exact ha.symm

theorem localNativeMap_continuous (i : atlas E M) :
    Continuous (localNativeMap Q i) := by
  apply continuous_induced_rng.mpr
  have hbase : Continuous
      (fun p : coefficientLocalDomain Q i => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hcoeff : Continuous
      (fun p : coefficientLocalDomain Q i =>
        coefficientSphereHomeomorph p.1.2) :=
    coefficientSphereHomeomorph.continuous.comp
      (continuous_snd.comp continuous_subtype_val)
  have hpair : Continuous
      (fun p : coefficientLocalDomain Q i =>
        (p.1.1, coefficientSphereHomeomorph p.1.2)) :=
    hbase.prodMk hcoeff
  have hform : Continuous
      (fun p : coefficientLocalDomain Q i =>
        nativeSphereForm Q i
          (p.1.1, coefficientSphereHomeomorph p.1.2)) :=
    ((nativeSphereForm_smooth Q i).continuousOn).comp_continuous hpair
      (by intro p; exact ⟨p.2, Set.mem_univ _⟩)
  exact hbase.prodMk hform

theorem localNativeInverse_continuous (i : atlas E M) :
    Continuous (localNativeInverse Q hdim i) := by
  apply continuous_induced_rng.mpr
  have hbase : Continuous
      (fun p : nativeLocalDomain Q i => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hpair : Continuous
      (fun p : nativeLocalDomain Q i => p.1) :=
    continuous_subtype_val
  have hraw : Continuous
      (fun p : nativeLocalDomain Q i =>
        nativeCoefficientRaw Q hdim i p.1.1 p.1.2) :=
    ((nativeCoefficientRaw_smooth Q hdim i).continuousOn).comp_continuous
      hpair (by intro p; exact ⟨p.2.1, Set.mem_univ _⟩)
  have hsphere : Continuous
      (fun p : nativeLocalDomain Q i =>
        (⟨nativeCoefficientRaw Q hdim i p.1.1 p.1.2,
          raw_unit Q hdim i p⟩ : coefficientSphere)) :=
    Continuous.subtype_mk hraw _
  exact hbase.prodMk hsphere

/-- Local topological chart of the independently topologized native
negative-sphere image. Its inverse is the checked smooth coefficient
extraction, restricted to the sphere subset. -/
def localNativeHomeomorph (i : atlas E M) :
    coefficientLocalDomain Q i ≃ₜ nativeLocalDomain Q i where
  toFun := localNativeMap Q i
  invFun := localNativeInverse Q hdim i
  left_inv := localNativeInverse_left Q hdim i
  right_inv := localNativeInverse_right Q hdim i
  continuous_toFun := localNativeMap_continuous Q i
  continuous_invFun := localNativeInverse_continuous Q hdim i

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereLocalCharts
