import QuaternionicSymmetry.ManifoldSphereAmbientNormalization
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Pointwise C¹ regularity suffices for continuity of the bundled
derivative at every tangent vector based at that point. -/
namespace QuaternionicSymmetry.ManifoldTangentMapContinuousAt

open Manifold
open scoped Manifold ContDiff
noncomputable section

variable {F H N F' H' N' : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [TopologicalSpace H'] [TopologicalSpace N'] [ChartedSpace H' N']
  {I : ModelWithCorners ℝ F H} {I' : ModelWithCorners ℝ F' H'}
  [IsManifold I 1 N] [IsManifold I' 1 N']

theorem continuousAt_tangentMap_of_contMDiffAt
    {f : N → N'} {v : TangentBundle I N}
    (hf : ContMDiffAt I I' 1 f v.1) :
    ContinuousAt (tangentMap I I' f) v := by
  obtain ⟨u, hu, hfu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (I := I) (I' := I')
      (n := (1 : WithTop ℕ∞)) (by simp)).mp hf
  obtain ⟨t, htu, ht, hvt⟩ := mem_nhds_iff.mp hu
  have hft : ContMDiffOn I I' 1 f t := hfu.mono htu
  have htangent : ContinuousOn (tangentMapWithin I I' f t)
      ((fun w : TangentBundle I N => w.1) ⁻¹' t) :=
    hft.continuousOn_tangentMapWithin (by simp) ht.uniqueMDiffOn
  have hproj : Continuous (fun w : TangentBundle I N => w.1) :=
    FiberBundle.continuous_proj F (TangentSpace I)
  have hopen : IsOpen ((fun w : TangentBundle I N => w.1) ⁻¹' t) :=
    ht.preimage hproj
  have hcont : ContinuousAt (tangentMapWithin I I' f t) v :=
    htangent.continuousAt (hopen.mem_nhds hvt)
  apply hcont.congr_of_eventuallyEq
  filter_upwards [hopen.mem_nhds hvt] with w hw
  have hmd : MDifferentiableAt I I' f w.1 :=
    (hft.contMDiffAt (ht.mem_nhds hw)).mdifferentiableAt (by simp)
  exact (tangentMapWithin_eq_tangentMap (ht.uniqueMDiffWithinAt hw) hmd).symm

end
end QuaternionicSymmetry.ManifoldTangentMapContinuousAt
