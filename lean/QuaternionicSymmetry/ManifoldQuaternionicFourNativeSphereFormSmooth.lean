import QuaternionicSymmetry.ManifoldQuaternionicFourForm
import QuaternionicSymmetry.ManifoldTwistorCoefficientSphere

/-! Joint smoothness of the actual normalized quaternionic two-form in a
base chart and a geometric-sphere coefficient chart. This uses the native
continuous alternating-form model, independently of any total-bundle
topology on exterior-power forms. -/

namespace QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormSmooth

open ManifoldQuaternionicMetric
open ManifoldQuaternionicFourForm
open ManifoldTwistorCoefficientSphere
open scoped Manifold ContDiff

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Nontrivial E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  (Q : SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ, E)) (M := M) (n := ∞))

local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin 2]→L[ℝ] ℝ) := inferInstance

/-- A local two-form on the actual base-sphere product, normalized as in the
pointwise exterior-power comparison. -/
def nativeSphereForm (i : atlas E M) (p : M × geometricSphere) :
    E [⋀^Fin 2]→L[ℝ] ℝ :=
  (Real.sqrt 2)⁻¹ • ∑ t : Fin 3,
    ((EuclideanSpace.equiv (Fin 3) ℝ) p.2.1) t • chartKahler Q i p.1 t

/-- The local native two-form varies jointly smoothly in the base point and
the sphere coefficient, on the actual adapted-frame domain. -/
theorem nativeSphereForm_smooth (i : atlas E M) :
    ContMDiffOn (𝓘(ℝ, E).prod (𝓡 2))
      𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ) ∞ (nativeSphereForm Q i)
      (Q.frames.adaptedCore.baseSet i ×ˢ Set.univ) := by
  haveI : Fact (Module.finrank ℝ EuclideanThree = 2 + 1) :=
    ⟨by simp [EuclideanThree]⟩
  let J := 𝓘(ℝ, E).prod (𝓡 2)
  let S : Set (M × geometricSphere) :=
    Q.frames.adaptedCore.baseSet i ×ˢ Set.univ
  have hbase : ContMDiffOn J 𝓘(ℝ, E) ∞
      (fun p : M × geometricSphere => p.1) S := contMDiffOn_fst
  have hsnd : ContMDiffOn J (𝓡 2) ∞
      (fun p : M × geometricSphere => p.2) S := contMDiffOn_snd
  have hcoe : ContMDiffOn J 𝓘(ℝ, EuclideanThree) ∞
      (fun p : M × geometricSphere => (p.2 : EuclideanThree)) S :=
    (contMDiff_coe_sphere (E := EuclideanThree) (n := 2)).comp_contMDiffOn hsnd
  have hcoeff : ContMDiffOn J 𝓘(ℝ, Fin 3 → ℝ) ∞
      (fun p : M × geometricSphere =>
        (EuclideanSpace.equiv (Fin 3) ℝ) (p.2 : EuclideanThree)) S :=
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap.contMDiff).comp_contMDiffOn hcoe
  have hterm (t : Fin 3) : ContMDiffOn J
      𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ) ∞
      (fun p : M × geometricSphere =>
        ((EuclideanSpace.equiv (Fin 3) ℝ) p.2.1) t • chartKahler Q i p.1 t) S := by
    have ht : ContMDiffOn J 𝓘(ℝ) ∞
        (fun p : M × geometricSphere =>
          ((EuclideanSpace.equiv (Fin 3) ℝ) p.2.1) t) S :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) t).contMDiff).comp_contMDiffOn hcoeff
    have hf : ContMDiffOn J 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ) ∞
        (fun p : M × geometricSphere => chartKahler Q i p.1 t) S :=
      (chartKahler_smooth Q i t).comp hbase (by
        intro p hp
        exact hp.1)
    exact ht.smul hf
  have hsum : ContMDiffOn J 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ) ∞
      (fun p : M × geometricSphere => ∑ t : Fin 3,
        ((EuclideanSpace.equiv (Fin 3) ℝ) p.2.1) t • chartKahler Q i p.1 t) S := by
    exact contMDiffOn_finset_sum (fun t _ => hterm t)
  simpa only [nativeSphereForm] using
    (contMDiffOn_const : ContMDiffOn J 𝓘(ℝ) ∞
      (fun _ : M × geometricSphere => (Real.sqrt 2)⁻¹) S).smul hsum

end
end QuaternionicSymmetry.ManifoldQuaternionicFourNativeSphereFormSmooth
