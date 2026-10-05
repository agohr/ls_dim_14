import QuaternionicSymmetry.ManifoldTwistorSphereFiberComplex
import QuaternionicSymmetry.ManifoldTwistorLeBrunHolomorphicLine

/-! The actual corrected projective fiber inclusion is an immersion whose
tangent is transverse to the connection-horizontal contact distribution.
This is internal differential geometry, before any degree calculation. -/

namespace QuaternionicSymmetry.ManifoldTwistorProjectiveFiberTransverse

open scoped Manifold ContDiff
open ManifoldTwistorSphereCore ManifoldTwistorSphereBundle ManifoldTwistorCoefficientSphere
open ManifoldTwistorSphereFiberInclusion ManifoldTwistorSphereFiberComplex
open ManifoldTwistorCorrectedHopf ManifoldTwistorGlobalAlmostComplex
open ManifoldTwistorLeBrunComplexAtlas
open FourDimensionalHalfSpinProjective
noncomputable section

private abbrev J {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (𝓘(ℝ,E)).prod (𝓡 2)

theorem correctedHopf_mfderiv_injective (s : ProjectiveSpinor) :
    Function.Injective (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf s) := by
  let e := correctedHopfDiffeomorph
  have h := mfderiv_comp s
    (e.symm.contMDiff.mdifferentiableAt (by simp))
    (e.contMDiff.mdifferentiableAt (by simp))
  have hid : (e.symm : geometricSphere → ProjectiveSpinor) ∘ e = id := by
    funext x
    exact e.symm_apply_apply x
  rw [hid, mfderiv_id] at h
  intro u v huv
  have hu := congrArg (fun f => f u) h
  have hv := congrArg (fun f => f v) h
  change u = (mfderiv (𝓡 2) 𝓘(ℝ,Fin 1 → ℂ) e.symm (e s))
    (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf s u) at hu
  change v = (mfderiv (𝓡 2) 𝓘(ℝ,Fin 1 → ℂ) e.symm (e s))
    (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (𝓡 2) correctedHopf s v) at hv
  exact hu.trans ((congrArg _ huv).trans hv.symm)

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

theorem projectiveFiberInclusion_mfderiv_injective (p : M) (s : ProjectiveSpinor) :
    Function.Injective (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
      (projectiveFiberInclusion Q p) s) := by
  intro u v huv
  rw [projectiveFiberInclusion_mfderiv, projectiveFiberInclusion_mfderiv] at huv
  exact correctedHopf_mfderiv_injective s (congrArg Prod.snd huv)

theorem projectiveFiberInclusion_mfderiv_vertical (p : M) (s : ProjectiveSpinor)
    (v : Fin 1 → ℂ) :
    mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E)) (projectiveFiberInclusion Q p) s v ∈
      verticalTangentSubmodule Q (projectiveFiberInclusion Q p s) := by
  rw [mem_verticalTangentSubmodule_iff, projectiveFiberInclusion_mfderiv]
  rfl

theorem contactFormReal_fiber_injective {n : ℕ}
    {A : CompatibleComplexAtlas Q D n} (L : HolomorphicContactLine Q D n A)
    (p : M) (s : ProjectiveSpinor) :
    Function.Injective ((L.contactFormReal Q D (projectiveFiberInclusion Q p s)).comp
      (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
        (projectiveFiberInclusion Q p) s).toLinearMap) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : L.contactFormReal Q D (projectiveFiberInclusion Q p s)
      (mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
        (projectiveFiberInclusion Q p) s v) = 0 := hv
  have hh : mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
      (projectiveFiberInclusion Q p) s v ∈
      horizontalTangentSubmodule Q D (projectiveFiberInclusion Q p s) := by
    rw [← L.contactFormReal_ker Q D, LinearMap.mem_ker]
    exact hz
  have hzero := (disjoint_iff_inf_le.mp
    (horizontal_vertical_isCompl Q D (projectiveFiberInclusion Q p s)).disjoint)
    ⟨hh, projectiveFiberInclusion_mfderiv_vertical Q p s v⟩
  change mfderiv 𝓘(ℝ,Fin 1 → ℂ) (J (E := E))
    (projectiveFiberInclusion Q p) s v = 0 at hzero
  change v = 0
  apply projectiveFiberInclusion_mfderiv_injective Q p s
  simpa only [map_zero] using hzero

end
end QuaternionicSymmetry.ManifoldTwistorProjectiveFiberTransverse
