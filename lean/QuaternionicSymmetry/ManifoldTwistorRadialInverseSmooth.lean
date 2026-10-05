import QuaternionicSymmetry.ManifoldTwistorRadialVerticalInverse
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
/-! The derivative of the genuine radial retraction gives a smooth map
from sphere points and ambient directions into the actual sphere tangent
bundle. Its coordinate regularity follows from Mathlib's parameterized
manifold derivative theorem and the tangent-bundle trivialization. -/
namespace QuaternionicSymmetry.ManifoldTwistorRadialRetraction
open QuaternionicSymmetry.ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff Topology
noncomputable section
local instance : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) := ⟨by simp⟩

private def radialDerivativeCoords (a₀ : geometricSphere)
    (aw : geometricSphere × EuclideanThree) : EuclideanSpace ℝ (Fin 2) :=
  (inTangentCoordinates (M := nonzeroOpen) (M' := geometricSphere)
    (N := geometricSphere) 𝓘(ℝ,EuclideanThree) (𝓡 2)
    sphereIntoNonzero (fun a : geometricSphere => radial (sphereIntoNonzero a))
    (fun a : geometricSphere => mfderiv (M := nonzeroOpen) (M' := geometricSphere)
      𝓘(ℝ,EuclideanThree) (𝓡 2) radial (sphereIntoNonzero a))
    a₀ aw.1) aw.2

theorem radialDerivative_coordinates_smooth
    (a₀ : geometricSphere) (w₀ : EuclideanThree) :
    ContMDiffAt ((𝓡 2).prod 𝓘(ℝ,EuclideanThree))
      𝓘(ℝ,EuclideanSpace ℝ (Fin 2)) ∞
      (radialDerivativeCoords a₀) (a₀,w₀) := by
  have hf : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ,EuclideanThree)) (𝓡 2) ∞
      (Function.uncurry (fun _ : geometricSphere => radial))
      (a₀,sphereIntoNonzero a₀) := by
    exact (radial_smooth.comp contMDiff_snd).contMDiffAt
  have hg := sphereIntoNonzero_smooth.contMDiffAt (x := a₀)
  have hg1 : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ,EuclideanThree)) (𝓡 2) ∞
      (Prod.fst : geometricSphere × EuclideanThree → geometricSphere) (a₀,w₀) :=
    contMDiffAt_fst
  have hg2 : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ,EuclideanThree))
      𝓘(ℝ,EuclideanThree) ∞
      (Prod.snd : geometricSphere × EuclideanThree → EuclideanThree) (a₀,w₀) :=
    contMDiffAt_snd
  exact ContMDiffAt.mfderiv_apply
    (m := ∞) (n := ∞)
    (I := 𝓘(ℝ,EuclideanThree)) (M := nonzeroOpen)
    (I' := 𝓡 2) (M' := geometricSphere)
    (J := 𝓡 2) (N := geometricSphere)
    (J' := (𝓡 2).prod 𝓘(ℝ,EuclideanThree))
    (N' := geometricSphere × EuclideanThree)
    (x₀ := (a₀,w₀))
    (fun _ : geometricSphere => radial)
    sphereIntoNonzero Prod.fst Prod.snd hf hg hg1 hg2 (by simp)

private theorem radialDerivativeCoords_eq_triv (a₀ a : geometricSphere)
    (w : EuclideanThree) (ha : a ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) a₀).source) :
    radialDerivativeCoords a₀ (a,w) =
      (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) a₀
        (⟨a, mfderiv 𝓘(ℝ,EuclideanThree) (𝓡 2)
          radial (sphereIntoNonzero a) w⟩ :
          TangentBundle (𝓡 2) geometricSphere)).2 := by
  have hs : sphereIntoNonzero a ∈
      (chartAt EuclideanThree (sphereIntoNonzero a₀)).source := by
    simp [nonzeroOpen]
  have ht : radial (sphereIntoNonzero a) ∈
      (chartAt (EuclideanSpace ℝ (Fin 2))
        (radial (sphereIntoNonzero a₀))).source := by
    simpa only [radial_sphereIntoNonzero] using ha
  unfold radialDerivativeCoords
  rw [inTangentCoordinates_eq sphereIntoNonzero
    (fun b => radial (sphereIntoNonzero b))
    (fun b => mfderiv 𝓘(ℝ,EuclideanThree) (𝓡 2)
      radial (sphereIntoNonzero b)) hs ht]
  have hi : achart EuclideanThree (sphereIntoNonzero a₀) =
      achart EuclideanThree (sphereIntoNonzero a) := rfl
  have hself : (tangentBundleCore 𝓘(ℝ,EuclideanThree) nonzeroOpen).coordChange
      (achart EuclideanThree (sphereIntoNonzero a₀))
      (achart EuclideanThree (sphereIntoNonzero a))
      (sphereIntoNonzero a) w = w := by
    rw [hi]
    exact (tangentBundleCore 𝓘(ℝ,EuclideanThree) nonzeroOpen).coordChange_self
      _ _ (by simp [nonzeroOpen]) _
  simp only [ContinuousLinearMap.comp_apply, hself, radial_sphereIntoNonzero]
  rfl

def radialTangentMap (aw : geometricSphere × EuclideanThree) :
    TangentBundle (𝓡 2) geometricSphere :=
  ⟨aw.1, mfderiv 𝓘(ℝ,EuclideanThree) (𝓡 2)
    radial (sphereIntoNonzero aw.1) aw.2⟩

theorem radialTangentMap_smooth :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ,EuclideanThree)) (𝓡 2).tangent ∞
      radialTangentMap := by
  intro aw
  let e := trivializationAt (EuclideanSpace ℝ (Fin 2))
    (TangentSpace (𝓡 2)) aw.1
  have he : radialTangentMap aw ∈ e.source :=
    e.mem_source.mpr (mem_baseSet_trivializationAt _ _ aw.1)
  rw [e.contMDiffAt_iff he]
  constructor
  · exact contMDiffAt_fst
  · have hlocal : (fun bw : geometricSphere × EuclideanThree =>
        (e (radialTangentMap bw)).2) =ᶠ[𝓝 aw]
        radialDerivativeCoords aw.1 := by
      have hopen : IsOpen {bw : geometricSphere × EuclideanThree |
          bw.1 ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) aw.1).source} :=
        (chartAt (EuclideanSpace ℝ (Fin 2)) aw.1).open_source.preimage
          continuous_fst
      filter_upwards [hopen.mem_nhds
        (show aw.1 ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) aw.1).source from
          mem_chart_source _ aw.1)] with bw hbw
      exact (radialDerivativeCoords_eq_triv aw.1 bw.1 bw.2 hbw).symm
    exact (radialDerivative_coordinates_smooth aw.1 aw.2).congr_of_eventuallyEq hlocal
end
end QuaternionicSymmetry.ManifoldTwistorRadialRetraction
