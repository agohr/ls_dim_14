import QuaternionicSymmetry.ManifoldTwistorCompactHausdorff
import QuaternionicSymmetry.ManifoldTwistorSectionComparison
import Mathlib.Geometry.Manifold.Complex

/-! The actual zeroth-twist section space on a compact connected twistor
is the complex line of constant functions. No Hilbert value is assumed. -/

namespace QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas

open ManifoldTwistorSphereCore ManifoldQuaternionicMetric
  ManifoldQuaternionicConnection ManifoldTwistorLinearSystem TopologicalSpace
open scoped Manifold ContDiff
noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (Q : SmoothQuaternionicHermitianTangent (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : CompatibleTangentConnection Q)
variable {n : ℕ} {A : CompatibleComplexAtlas Q D n}
  (L : HolomorphicContactLine Q D n A)

theorem zeroTwist_coordChange (i j : L.Index) (x : SphereBundleTotal Q) (c : ℂ) :
    (L.integerTwistCore Q D 0).coordChange i j x c = c := by
  simp [HolomorphicContactLine.integerTwistCore,
    HolomorphicLineIntegerPowers.integerPowerCore, HolomorphicLinePowers.powerCore]

theorem zeroTwistFunction_contMDiff (s : GlobalSections Q D L 0) :
    letI := A.charts
    ContMDiff 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ,ℂ) ∞
      (fun x : SphereBundleTotal Q => (evaluation Q D L 0 x s : ℂ)) := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D 0
  have hg := (global_coefficient_holomorphic_iff Q D L 0
    (fun x => evaluation Q D L 0 x s)).mp s.2
  intro x
  have h := (Bundle.contMDiffAt_section x).mp (hg x)
  simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt,
    VectorBundleCore.localTriv_apply, zeroTwist_coordChange] using h

def zeroTwistConstantSection (c : ℂ) : GlobalSections Q D L 0 := by
  letI := A.charts
  letI := L.integerTwistCore_holomorphic Q D 0
  refine ⟨fun _ => c, (global_coefficient_holomorphic_iff Q D L 0
    (fun _ => c)).mpr ?_⟩
  intro x
  apply (Bundle.contMDiffAt_section x).mpr
  simpa only [VectorBundleCore.trivializationAt, VectorBundleCore.localTrivAt,
    VectorBundleCore.localTriv_apply, zeroTwist_coordChange] using
    (contMDiffAt_const : ContMDiffAt 𝓘(ℂ, ComplexTwistorModel n) 𝓘(ℂ,ℂ) ∞
      (fun _ : SphereBundleTotal Q => c) x)

theorem zeroTwistSection_eq_at [CompactSpace M] [PreconnectedSpace M]
    (s : GlobalSections Q D L 0) (x y : SphereBundleTotal Q) :
    evaluation Q D L 0 x s = evaluation Q D L 0 y s := by
  letI := A.charts
  letI := A.complexManifold
  exact (zeroTwistFunction_contMDiff Q D L s).mdifferentiable
    (by simp) |>.apply_eq_of_compactSpace x y

/-- Evaluation at any actual twistor point identifies the trivial-twist
holomorphic sections with ℂ. The inverse is the genuine constant section. -/
def zeroTwistSectionsEquiv [CompactSpace M] [PreconnectedSpace M]
    (x : SphereBundleTotal Q) : GlobalSections Q D L 0 ≃ₗ[ℂ] ℂ where
  toFun := evaluation Q D L 0 x
  invFun := zeroTwistConstantSection Q D L
  left_inv s := by
    apply Subtype.ext
    funext y
    exact zeroTwistSection_eq_at Q D L s x y.1
  right_inv c := rfl
  map_add' := map_add (evaluation Q D L 0 x)
  map_smul' := (evaluation Q D L 0 x).map_smul

theorem zeroTwistSections_finrank [CompactSpace M] [PreconnectedSpace M]
    (x : SphereBundleTotal Q) : Module.finrank ℂ (GlobalSections Q D L 0) = 1 := by
  rw [(zeroTwistSectionsEquiv Q D L x).finrank_eq]
  exact Module.finrank_self ℂ

instance zeroTwistSections_finiteDimensional [CompactSpace M]
    [PreconnectedSpace M] [Nonempty M] :
    FiniteDimensional ℂ (GlobalSections Q D L 0) :=
  (zeroTwistSectionsEquiv Q D L (Classical.arbitrary (SphereBundleTotal Q))).symm.finiteDimensional

end
end QuaternionicSymmetry.ManifoldTwistorLeBrunComplexAtlas
