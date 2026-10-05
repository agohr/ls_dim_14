import QuaternionicSymmetry.QuaternionicFrameLinearMap
import QuaternionicSymmetry.QuaternionicRestriction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Smooth quaternionic orthonormal trivializations of the ranges of a smooth
family of injective linear maps. No submanifold geometry is assumed. -/
namespace QuaternionicSymmetry.QuaternionicSmoothRangeFrame
open QuaternionicStructure QuaternionicLineProjection QuaternionicLocalOrthonormalFrame
open QuaternionicFrameLinearMap QuaternionicStructureIsometryTransport Filter
open scoped ContDiff Topology
noncomputable section
set_option maxHeartbeats 800000
variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem exists_restricted_isometry (Q : QuaternionicStructure E)
    (W : Submodule ℝ E) (hdim : Module.finrank ℝ F = Module.finrank ℝ W)
    (hI : ∀ z ∈ W, Q.I z ∈ W) (hJ : ∀ z ∈ W, Q.J z ∈ W) :
    ∃ (S : QuaternionicStructure F) (e : F ≃ₗᵢ[ℝ] W),
      (∀ w, (e (S.I w) : E) = Q.I (e w)) ∧
      (∀ w, (e (S.J w) : E) = Q.J (e w)) := by
  let T : QuaternionicStructure W := Q.restrict W hI hJ
  let e : F ≃ₗᵢ[ℝ] W := (stdOrthonormalBasis ℝ F).equiv
    (stdOrthonormalBasis ℝ W) (finCongr hdim)
  refine ⟨transport T e.symm,e,?_,?_⟩ <;> intro w <;>
    simp [transport,LinearIsometryEquiv.trans_apply] <;> rfl

theorem exists_smooth_range_frame (Q : QuaternionicStructure E)
    (A : X → F →L[ℝ] E) (a : X) (hA : ∀ᶠ y in 𝓝 a, ContDiffAt ℝ ∞ A y)
    (hinj : ∀ᶠ y in 𝓝 a, Function.Injective (A y))
    (hI : ∀ᶠ y in 𝓝 a, ∀ z ∈ LinearMap.range (A y).toLinearMap,
      Q.I z ∈ LinearMap.range (A y).toLinearMap)
    (hJ : ∀ᶠ y in 𝓝 a, ∀ z ∈ LinearMap.range (A y).toLinearMap,
      Q.J z ∈ LinearMap.range (A y).toLinearMap) :
    ∃ (S : QuaternionicStructure F) (B : X → F →L[ℝ] E),
      (∀ᶠ y in 𝓝 a, ContDiffAt ℝ ∞ B y) ∧ ∀ᶠ y in 𝓝 a,
        (∀ v w, inner ℝ (B y v) (B y w) = inner ℝ v w) ∧
        LinearMap.range (B y).toLinearMap = LinearMap.range (A y).toLinearMap ∧
        (∀ v, B y (S.I v) = Q.I (B y v)) ∧
        (∀ v, B y (S.J v) = Q.J (B y v)) := by
  classical
  let W : X → Submodule ℝ E := fun y => LinearMap.range (A y).toLinearMap
  have hdim : Module.finrank ℝ F = Module.finrank ℝ (W a) :=
    (LinearMap.finrank_range_of_inj hinj.self_of_nhds).symm
  obtain ⟨S,e,hi,hj⟩ := exists_restricted_isometry Q (W a) hdim
    hI.self_of_nhds hJ.self_of_nhds
  obtain ⟨_,v,b,hb,_⟩ := S.exists_eigenOrthonormalBasis_fin 0 S.skewCentralizer.zero_mem
  have hframe (w : F) (k : Fin 4) : (e (S.frame w k) : E) = Q.frame (e w) k := by
    fin_cases k
    · rfl
    · exact hi w
    · exact hj w
    · change (e (S.I (S.J w)) : E) = Q.I (Q.J (e w))
      rw [hi,hj]
  choose c hc using fun i => (e (v i)).property
  let f : Fin S.quaternionicDimension → X → E := fun i y => A y (c i)
  have hf : ∀ᶠ y in 𝓝 a, ∀ i, ContDiffAt ℝ ∞ (f i) y :=
    hA.mono fun y hy i => hy.clm_apply contDiffAt_const
  have hfa (i : Fin S.quaternionicDimension) : f i a = (e (v i) : E) := hc i
  have horth : Orthonormal ℝ (fun p : Fin S.quaternionicDimension × Fin 4 =>
      Q.frame (f p.1 a) p.2) := by
    have he := (W a).subtypeₗᵢ.orthonormal_comp_iff.mpr
      (e.toLinearIsometry.orthonormal_comp_iff.mpr b.orthonormal)
    change Orthonormal ℝ (fun p => (e (b p) : E)) at he
    simpa only [hb,hframe,hfa] using he
  have hfW : ∀ᶠ y in 𝓝 a,
      (∀ z ∈ W y, Q.I z ∈ W y) ∧ (∀ z ∈ W y, Q.J z ∈ W y) ∧ ∀ i, f i y ∈ W y := by
    filter_upwards [hI,hJ] with y hyI hyJ
    exact ⟨hyI,hyJ,fun i => ⟨c i,rfl⟩⟩
  obtain ⟨u,hu,_,huw⟩ := exists_local_frame Q S.quaternionicDimension f a W hf horth hfW
  let B : X → F →L[ℝ] E := fun y => frameMap b (fun p => Q.frame (u p.1 y) p.2)
  refine ⟨S,B,hu.mono (fun y hy => frameMap_contDiffAt b _ y (fun p =>
    (frame_contDiff Q p.2).contDiffAt.comp y (hy p.1))),?_⟩
  filter_upwards [huw,hI,hJ,hinj] with y hy hyI hyJ hyinj
  have hmem (p : Fin S.quaternionicDimension × Fin 4) : Q.frame (u p.1 y) p.2 ∈ W y := by
    rcases p with ⟨i,k⟩
    fin_cases k
    · exact hy.1 i
    · exact hyI _ (hy.1 i)
    · exact hyJ _ (hy.1 i)
    · exact hyI _ (hyJ _ (hy.1 i))
  refine ⟨frameMap_inner b (fun p => Q.frame (u p.1 y) p.2) hy.2,?_,
    frameMap_I S Q b v hb (fun i => u i y),frameMap_J S Q b v hb (fun i => u i y)⟩
  have hle : LinearMap.range (B y).toLinearMap ≤ W y := by
    rintro z ⟨w,rfl⟩
    change frameMap b (fun p => Q.frame (u p.1 y) p.2) w ∈ W y
    rw [frameMap_apply]
    exact (W y).sum_mem (fun p _ => (W y).smul_mem _ (hmem p))
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj
    (frameMap_injective b (fun p => Q.frame (u p.1 y) p.2) hy.2)]
  exact (LinearMap.finrank_range_of_inj hyinj).symm

end
end QuaternionicSymmetry.QuaternionicSmoothRangeFrame
