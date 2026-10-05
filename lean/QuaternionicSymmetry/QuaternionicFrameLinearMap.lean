import QuaternionicSymmetry.QuaternionicLocalOrthonormalFrame
import QuaternionicSymmetry.QuaternionicStructureIsometryTransport

/-! A prescribed quaternionic orthonormal basis turns a smooth family of
quaternionic frames into smooth isometric linear maps. -/
namespace QuaternionicSymmetry.QuaternionicFrameLinearMap
open QuaternionicStructure QuaternionicLineProjection
open scoped ContDiff BigOperators
noncomputable section
variable {E F X ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def frameMap (b : OrthonormalBasis ι ℝ F) (v : ι → E) : F →L[ℝ] E :=
  ∑ i, InnerProductSpace.rankOne ℝ (v i) (b i)

@[simp] theorem frameMap_apply (b : OrthonormalBasis ι ℝ F) (v : ι → E) (w : F) :
    frameMap b v w = ∑ i, inner ℝ (b i) w • v i := by simp [frameMap]

@[simp] theorem frameMap_basis (b : OrthonormalBasis ι ℝ F) (v : ι → E) (j : ι) :
    frameMap b v (b j) = v j := by
  classical
  simp [frameMap_apply,orthonormal_iff_ite.mp b.orthonormal]

theorem frameMap_inner (b : OrthonormalBasis ι ℝ F) (v : ι → E)
    (hv : Orthonormal ℝ v) (w z : F) :
    inner ℝ (frameMap b v w) (frameMap b v z) = inner ℝ w z := by
  let L := (frameMap b v).toLinearMap.isometryOfOrthonormal (v := b.toBasis) b.orthonormal (by
    simpa only [Function.comp_def,ContinuousLinearMap.coe_coe,OrthonormalBasis.coe_toBasis,frameMap_basis] using hv)
  exact L.inner_map_map w z

theorem frameMap_injective (b : OrthonormalBasis ι ℝ F) (v : ι → E)
    (hv : Orthonormal ℝ v) : Function.Injective (frameMap b v) := by
  intro w z h
  have hn := frameMap_inner b v hv (w-z) (w-z)
  rw [map_sub,h,sub_self,inner_zero_left] at hn
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp hn.symm)

theorem frameMap_contDiffAt (b : OrthonormalBasis ι ℝ F) (v : ι → X → E) (a : X)
    (hv : ∀ i, ContDiffAt ℝ ∞ (v i) a) :
    ContDiffAt ℝ ∞ (fun y => frameMap b (fun i => v i y)) a := by
  apply ContDiffAt.sum
  intro i _
  exact (InnerProductSpace.rankOne ℝ (E := E) (F := F)).isBoundedBilinearMap.contDiff.contDiffAt.comp
    a ((hv i).prodMk contDiffAt_const)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {m : ℕ} (S : QuaternionicStructure F) (Q : QuaternionicStructure E)
  (b : OrthonormalBasis (Fin m × Fin 4) ℝ F) (v : Fin m → F)
  (hb : ∀ p, b p = S.frame (v p.1) p.2) (u : Fin m → E)

include v hb in
theorem frameMap_I (w : F) :
    frameMap b (fun p => Q.frame (u p.1) p.2) (S.I w) =
      Q.I (frameMap b (fun p => Q.frame (u p.1) p.2) w) := by
  let L := frameMap b (fun p => Q.frame (u p.1) p.2)
  have he : L.comp S.I.toContinuousLinearMap = Q.I.toContinuousLinearMap.comp L := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    rintro ⟨i,k⟩
    change L (S.I (b (i,k))) = Q.I (L (b (i,k)))
    have hL (j : Fin m) (l : Fin 4) : L (S.frame (v j) l) = Q.frame (u j) l := by
      rw [← hb (j,l)]
      exact frameMap_basis b _ (j,l)
    rw [hb (i,k),hL]
    fin_cases k <;> simp [I_frame,map_neg,hL]
  exact congrArg (fun A : F →L[ℝ] E => A w) he

include v hb in
theorem frameMap_J (w : F) :
    frameMap b (fun p => Q.frame (u p.1) p.2) (S.J w) =
      Q.J (frameMap b (fun p => Q.frame (u p.1) p.2) w) := by
  let L := frameMap b (fun p => Q.frame (u p.1) p.2)
  have he : L.comp S.J.toContinuousLinearMap = Q.J.toContinuousLinearMap.comp L := by
    apply ContinuousLinearMap.coe_injective
    apply b.toBasis.ext
    rintro ⟨i,k⟩
    change L (S.J (b (i,k))) = Q.J (L (b (i,k)))
    have hL (j : Fin m) (l : Fin 4) : L (S.frame (v j) l) = Q.frame (u j) l := by
      rw [← hb (j,l)]
      exact frameMap_basis b _ (j,l)
    rw [hb (i,k),hL]
    fin_cases k <;> simp [J_frame,map_neg,hL]
  exact congrArg (fun A : F →L[ℝ] E => A w) he

end
end QuaternionicSymmetry.QuaternionicFrameLinearMap
