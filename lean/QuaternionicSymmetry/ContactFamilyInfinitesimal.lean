import QuaternionicSymmetry.ContactHamiltonianLocalUniqueness

/-! Differentiating preservation of a local contact hyperplane. Symmetry of
the second derivative converts the parameter variation into the Lie bracket. -/
namespace QuaternionicSymmetry.ContactFamilyInfinitesimal
open Filter
open scoped ContDiff Topology
noncomputable section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem lieBracket_horizontal
    (F : E × V → V) (a : V → V →L[ℂ] ℂ) (p u : E) (x : V) (Y : V → V)
    (hF : ContDiffAt ℂ 2 F (p,x)) (ha : DifferentiableAt ℂ a x)
    (hY : DifferentiableAt ℂ Y x) (hFx : F (p,x) = x)
    (hDx : fderiv ℂ F (p,x) (0,Y x) = Y x)
    (hYker : (fun y => a y (Y y)) =ᶠ[𝓝 x] fun _ => 0)
    (hPres : (fun q => a (F (q,x)) (fderiv ℂ F (q,x) (0,Y x))) =ᶠ[𝓝 p] fun _ => 0) :
    a x (VectorField.lieBracket ℂ (fun y => fderiv ℂ F (p,y) (u,0)) Y x) = 0 := by
  let X : V → V := fun y => fderiv ℂ F (p,y) (u,0)
  have hdF := hF.differentiableAt (by norm_num)
  have hddF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hP : HasFDerivAt (fun q : E => (q,x)) (ContinuousLinearMap.inl ℂ E V) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const x p)
  have hQ : HasFDerivAt (fun y : V => (p,y)) (ContinuousLinearMap.inr ℂ E V) x :=
    (hasFDerivAt_const p x).prodMk (hasFDerivAt_id x)
  have hFQ := hdF.hasFDerivAt.comp p hP
  dsimp only [Function.comp_def] at hFQ
  have haF : DifferentiableAt ℂ (fun q => a (F (q,x))) p := by
    apply DifferentiableAt.comp p _ hFQ.differentiableAt
    simpa only [hFx] using ha
  have hDFP := hddF.hasFDerivAt.comp p hP
  have hDP := hDFP.clm_apply (hasFDerivAt_const (0,Y x) p)
  have hX := (hddF.hasFDerivAt.comp x hQ).clm_apply (hasFDerivAt_const (u,0) x)
  dsimp only [Function.comp_def] at hDFP hDP hX
  have hp := congrArg (fun A : E →L[ℂ] ℂ => A u) hPres.fderiv_eq
  dsimp only at hp
  rw [fderiv_clm_apply haF hDP.differentiableAt,fderiv_const_apply] at hp
  have haFP : fderiv ℂ (fun q => a (F (q,x))) p =
      (fderiv ℂ a x).comp ((fderiv ℂ F (p,x)).comp (ContinuousLinearMap.inl ℂ E V)) := by
    have ha' : HasFDerivAt a (fderiv ℂ a x) (F (p,x)) := by
      simpa only [hFx] using ha.hasFDerivAt
    have hh := (ha'.comp p hFQ).fderiv
    exact hh
  rw [haFP,hDP.fderiv] at hp
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.zero_apply,
    map_zero,zero_add,hFx,hDx] at hp
  have hy := congrArg (fun A : V →L[ℂ] ℂ => A (X x)) hYker.fderiv_eq
  dsimp only at hy
  rw [fderiv_clm_apply ha hY,fderiv_const_apply] at hy
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.zero_apply] at hy
  have hsym := hF.isSymmSndFDerivAt (by norm_num)
  change a x (fderiv ℂ Y x (X x) - fderiv ℂ X x (Y x)) = 0
  rw [map_sub,hX.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.inr_apply,
    ContinuousLinearMap.zero_apply,map_zero,zero_add]
  rw [hsym.eq (0,Y x) (u,0)]
  change a x (fderiv ℂ (fderiv ℂ F) (p,x) (u,0) (0,Y x)) + fderiv ℂ a x (X x) (Y x) = 0 at hp
  linear_combination hy - hp

end
end QuaternionicSymmetry.ContactFamilyInfinitesimal
