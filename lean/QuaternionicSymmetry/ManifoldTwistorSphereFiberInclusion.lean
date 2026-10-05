import QuaternionicSymmetry.ManifoldTwistorRawChartConjugacy
import QuaternionicSymmetry.ManifoldTwistorCorrectedHopf

/-! The actual sphere fiber embeds smoothly into the independently charted
twistor total space. Its true manifold derivative is the vertical inclusion
in the preferred tangent model. -/

namespace QuaternionicSymmetry.ManifoldTwistorSphereFiberInclusion

open scoped Manifold ContDiff Topology
open ManifoldTwistorSphereCore ManifoldTwistorCoefficientSphere
open ManifoldTwistorGlobalAlmostComplex ManifoldTwistorCorrectedHopf
open FourDimensionalHalfSpinProjective
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))

private abbrev J := (𝓘(ℝ,E)).prod (𝓡 2)
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

def sphereFiberInclusion (p : M) (s : geometricSphere) : SphereBundleTotal Q := ⟨p,s⟩

theorem sphereFiberInclusion_injective (p : M) :
    Function.Injective (sphereFiberInclusion Q p) := by
  intro s t h
  exact eq_of_heq (Bundle.TotalSpace.mk.inj h).2

theorem sphereFiberInclusion_raw_chart (p : M) (s : geometricSphere) :
    fixedRawChart Q p (sphereFiberInclusion Q p s) =
      ((extChartAt 𝓘(ℝ,E) p) p,s) :=
  fixedRawChart_center_value Q (sphereFiberInclusion Q p s)

private theorem inclusion_mem_source (p : M) (s : geometricSphere) :
    sphereFiberInclusion Q p s ∈
      ((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.source := by
  apply ((sphereCore Q).mem_localTriv_source (achart E p) _).mpr
  exact (sphereCore Q).mem_baseSet_at p

theorem sphereFiberInclusion_eq_raw_inverse (p : M) (s : geometricSphere) :
    sphereFiberInclusion Q p s =
      fixedRawChartInv Q p ((extChartAt 𝓘(ℝ,E) p) p,s) := by
  have h := fixedRawChartInv_left Q p (sphereFiberInclusion Q p s)
    (inclusion_mem_source Q p s)
  rw [sphereFiberInclusion_raw_chart] at h
  exact h.symm

theorem sphereFiberInclusion_smooth (p : M) :
    ContMDiff (𝓡 2) (J (E := E)) ∞ (sphereFiberInclusion Q p) := by
  have heq : sphereFiberInclusion Q p = fun s =>
      fixedRawChartInv Q p ((extChartAt 𝓘(ℝ,E) p) p,s) :=
    funext (sphereFiberInclusion_eq_raw_inverse Q p)
  rw [heq]
  have hpair : ContMDiff (𝓡 2) (J (E := E)) ∞
      (fun s : geometricSphere => ((extChartAt 𝓘(ℝ,E) p) p,s)) :=
    contMDiff_const.prodMk contMDiff_id
  intro s
  have hmem : ((extChartAt 𝓘(ℝ,E) p) p,s) ∈ fixedRawTarget (E := E) p :=
    ⟨(extChartAt 𝓘(ℝ,E) p).map_source (mem_extChartAt_source p), trivial⟩
  have hopen : IsOpen (fixedRawTarget (E := E) p) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  exact ((fixedRawChartInv_smoothOn Q p).contMDiffAt
    (hopen.mem_nhds hmem)).comp s (hpair s)

theorem sphereFiberInclusion_mfderiv (p : M) (s : geometricSphere)
    (v : TangentSpace (𝓡 2) s) :
    mfderiv (𝓡 2) (J (E := E)) (sphereFiberInclusion Q p) s v = (0,v) := by
  have hfun : fixedRawChart Q p ∘ sphereFiberInclusion Q p =
      fun t => ((extChartAt 𝓘(ℝ,E) p) p,t) :=
    funext (sphereFiberInclusion_raw_chart Q p)
  have hraw : MDifferentiableAt (J (E := E)) (J (E := E))
      (fixedRawChart Q p) (sphereFiberInclusion Q p s) :=
    ((fixedRawChart_smoothOn Q p).contMDiffAt
      (((sphereCore Q).localTriv (achart E p)).toOpenPartialHomeomorph.open_source.mem_nhds
        (inclusion_mem_source Q p s))).mdifferentiableAt (by simp)
  have hi := (sphereFiberInclusion_smooth Q p).mdifferentiableAt (x := s) (by simp)
  have hd := congrArg (fun f => mfderiv (𝓡 2) (J (E := E)) f s v) hfun
  dsimp only at hd
  rw [mfderiv_comp s hraw hi] at hd
  have hc := fixedRawChart_center_mfderiv Q (sphereFiberInclusion Q p s)
  change mfderiv (J (E := E)) (J (E := E)) (fixedRawChart Q p)
    (sphereFiberInclusion Q p s) = _ at hc
  rw [hc, mfderiv_prod_right] at hd
  exact hd

def projectiveFiberInclusion (p : M) : ProjectiveSpinor → SphereBundleTotal Q :=
  sphereFiberInclusion Q p ∘ correctedHopf

theorem projectiveFiberInclusion_smooth (p : M) :
    ContMDiff 𝓘(ℝ,Fin 1 → ℂ) (J (E := E)) ∞ (projectiveFiberInclusion Q p) :=
  (sphereFiberInclusion_smooth Q p).comp correctedHopf_smooth

end
end QuaternionicSymmetry.ManifoldTwistorSphereFiberInclusion
