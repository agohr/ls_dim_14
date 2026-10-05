import QuaternionicSymmetry.CompactRepresentationHermitianForm
import QuaternionicSymmetry.HermitianKillingForm
import QuaternionicSymmetry.ComplexAdjointRepresentation
import QuaternionicSymmetry.GeneralComplexAdjointTorusChain
import QuaternionicSymmetry.RealToComplexTangentComplexificationLinear
import QuaternionicSymmetry.ComplexTensorRealImagComponents
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Nondegenerate Killing form for a centre-free complex Lie group whose
Lie algebra is spanned by the differential of a compact real Lie group.
The proof averages the actual adjoint action and differentiates invariance. -/
namespace QuaternionicSymmetry.CompactRealFormKilling
open ComplexLieRealCompanion GeneralComplexAdjointDifferentialSource
open GeneralComplexAdjointTorusChain ComplexAdjointRepresentation
open CompactRepresentationHermitianForm RealToComplexTangentComplexification
open ComplexTensorRealImagComponents MeasureTheory
open scoped Manifold ContDiff Topology TensorProduct
noncomputable section

section Bilinear
variable {F T V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace T] [ChartedSpace F T]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma skew_of_invariant (B : V →L[ℝ] V →L[ℝ] ℂ)
    (ρ : T → V → V) (t : T) (hOne : ∀ v, ρ t v = v)
    (hDiff : ∀ v, MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,V) (fun s => ρ s v) t)
    (hInv : ∀ s v w, B (ρ s v) (ρ s w) = B v w)
    (u : F) (v w : V) :
    B (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (fun s => ρ s v) t u) w +
      B v (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (fun s => ρ s w) t u) = 0 := by
  let e := extChartAt 𝓘(ℝ,F) t
  have hd (a : V) : HasFDerivAt (fun x => ρ (e.symm x) a)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (fun s => ρ s a) t) (e t) := by
    simpa [writtenInExtChartAt, e] using (hDiff a).hasMFDerivAt.2
  have h := B.hasFDerivAt_of_bilinear (hd v) (hd w)
  have heq : (fun x => B (ρ (e.symm x) v) (ρ (e.symm x) w)) = fun _ : F => B v w :=
    funext (fun x => hInv _ _ _)
  rw [heq] at h
  have hz := congrArg (fun L : F →L[ℝ] ℂ => L u)
    (h.unique (hasFDerivAt_const (B v w) (e t)))
  have hz' : B v (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (fun s => ρ s w) t u) +
      B (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) (fun s => ρ s v) t u) w = 0 := by
    simpa [e, hOne] using hz
  simpa only [add_comm] using hz'
end Bilinear

variable {F T V G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  [Group T] [TopologicalSpace T] [T2Space T] [CompactSpace T] [ChartedSpace F T]
  [IsManifold 𝓘(ℝ,F) ∞ T] [LieGroup 𝓘(ℝ,F) ∞ T]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [Group G] [TopologicalSpace G] [T2Space G] [SecondCountableTopology G]
  [ChartedSpace V G] [IsManifold 𝓘(ℂ,V) ∞ G] [LieGroup 𝓘(ℂ,V) ∞ G]

local instance complexMin : ENat.LEInfty (minSmoothness ℂ 3) := by
  simpa only [minSmoothness_of_isRCLikeNormedField] using
    (inferInstance : ENat.LEInfty (3 : WithTop ℕ∞))

/-- A compact infinitesimal real form and zero centre suffice; no reductivity
or Killing-radical premise occurs. -/
theorem isKilling_of_compact_complexification
    (f : T →* G) (hf : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,V) ∞ f)
    (hSpan : let D : F →ₗ[ℝ] V := (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f 1).toLinearMap
      Function.Surjective (complexifiedMapComplex D))
    (hCenter : LieAlgebra.center ℂ (GroupLieAlgebra 𝓘(ℂ,V) G) = ⊥) :
    LieAlgebra.IsKilling ℂ (GroupLieAlgebra 𝓘(ℂ,V) G) := by
  letI : IsTopologicalGroup T := topologicalGroup_of_lieGroup 𝓘(ℝ,F) ∞
  letI : MeasurableSpace T := borel T
  letI : BorelSpace T := ⟨rfl⟩
  letI : IsManifold 𝓘(ℝ,V) ∞ G := realManifold
  letI : LieGroup 𝓘(ℝ,V) ∞ G := realLieGroup
  let μ : Measure T := (Measure.haar : Measure T).inv
  let ρ : T →* Module.End ℂ V := (adjoint (V := V)).comp f
  have hρ (v : V) : Continuous (fun t => ρ t v) :=
    (continuous_adjointOrbit v).comp hf.continuous
  let q : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    (Module.finBasis ℂ V).equivFun.toContinuousLinearEquiv.trans (EuclideanSpace.equiv _ _).symm
  let cV : InnerProductSpace.Core ℂ V :=
    core μ ρ hρ q.toContinuousLinearMap q.injective
  let c : InnerProductSpace.Core ℂ (GroupLieAlgebra 𝓘(ℂ,V) G) := cV
  let D : F →ₗ[ℝ] GroupLieAlgebra 𝓘(ℂ,V) G :=
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,V) f 1).toLinearMap
  letI : FiniteDimensional ℂ (GroupLieAlgebra 𝓘(ℂ,V) G) := by
    unfold GroupLieAlgebra TangentSpace; infer_instance
  let B := realBilinear μ ρ hρ q.toContinuousLinearMap
  have hB (v w : V) : B v w = cV.inner v w := rfl
  have hAd : LeeComplexAdjointDifferentialSource :=
    GeneralComplexAdjointFromReal.complexAdjointDifferential_of_real
    RealAdjointDifferentialFromMathlib.realAdjointDifferential
  have hDiff (v : V) : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,V) (fun t => ρ t v) 1 := by
    have hd : MDifferentiableAt 𝓘(ℝ,V) 𝓘(ℝ,V) (adjointOrbit v) (f 1) := by
      simpa only [map_one] using (hAd (G := G) v).1
    exact hd.comp 1 (hf.mdifferentiableAt (by simp))
  have hSkew (u : F) (v w : GroupLieAlgebra 𝓘(ℂ,V) G) :
      c.inner ⁅D u,v⁆ w + c.inner v ⁅D u,w⁆ = 0 := by
    have h := skew_of_invariant B (fun t v => ρ t v) 1
      (fun v => by simp) hDiff (averaged_invariant μ ρ q.toContinuousLinearMap) u v w
    have hv := mfderiv_adjointOrbit_comp_lieHom hAd f hf v u
    have hw := mfderiv_adjointOrbit_comp_lieHom hAd f hf w u
    simp only [ρ, MonoidHom.comp_apply, adjoint_apply] at h
    rw [hv, hw] at h
    simpa only [TangentSpace, eq_rec_constant, hB] using h
  apply HermitianKillingForm.isKilling_of_decomposition c _ hCenter
  intro z
  obtain ⟨t,ht⟩ := hSpan z
  refine ⟨D (realComponent t), D (imagComponent t), ?_, hSkew _, hSkew _⟩
  rw [← ht]
  conv_lhs => rw [eq_one_tmul_add_I_tmul t]
  simp only [map_add, complexifiedMapComplex_tmul, one_smul]
  rfl

end
end QuaternionicSymmetry.CompactRealFormKilling
