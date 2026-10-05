import QuaternionicSymmetry.ContinuousAlternation

/-! Concatenation of continuous multilinear maps through a continuous
bilinear pairing, bundled as a bounded bilinear operator. -/

namespace QuaternionicSymmetry.ContinuousMultilinearProduct

noncomputable section

variable {ι κ E A B C : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

def concatenate (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : κ => E) B) :
    ContinuousMultilinearMap ℝ (fun _ : ι ⊕ κ => E) C :=
  ((((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : κ => E) B C).flip g).comp P).compContinuousMultilinearMap f).uncurrySum

theorem concatenate_apply (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : κ => E) B) (v : ι ⊕ κ → E) :
    concatenate P f g v = P (f (v ∘ Sum.inl)) (g (v ∘ Sum.inr)) := rfl

theorem norm_concatenate_le (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : κ => E) B) :
    ‖concatenate P f g‖ ≤ ‖P‖ * ‖f‖ * ‖g‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [concatenate_apply]
  calc
    _ ≤ ‖P‖ * ‖f (v ∘ Sum.inl)‖ * ‖g (v ∘ Sum.inr)‖ := P.le_opNorm₂ _ _
    _ ≤ ‖P‖ * (‖f‖ * ∏ i, ‖v (Sum.inl i)‖) * (‖g‖ * ∏ j, ‖v (Sum.inr j)‖) := by
      gcongr
      · exact f.le_opNorm _
      · exact g.le_opNorm _
    _ = (‖P‖ * ‖f‖ * ‖g‖) * ∏ i, ‖v i‖ := by
      rw [Fintype.prod_sum_type]
      ring

def concatenateLinear (P : A →L[ℝ] B →L[ℝ] C) :
    ContinuousMultilinearMap ℝ (fun _ : ι => E) A →ₗ[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : κ => E) B →ₗ[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : ι ⊕ κ => E) C :=
  LinearMap.mk₂ ℝ (concatenate P)
    (by intros; ext v; simp [concatenate_apply])
    (by intros; ext v; simp [concatenate_apply])
    (by intros; ext v; simp [concatenate_apply])
    (by intros; ext v; simp [concatenate_apply])

def concatenateCLM (P : A →L[ℝ] B →L[ℝ] C) :
    ContinuousMultilinearMap ℝ (fun _ : ι => E) A →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : κ => E) B →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : ι ⊕ κ => E) C :=
  (concatenateLinear (ι := ι) (κ := κ) (E := E) P).mkContinuous₂ ‖P‖
    (fun f g => norm_concatenate_le P f g)

theorem concatenateCLM_apply (P : A →L[ℝ] B →L[ℝ] C)
    (f : ContinuousMultilinearMap ℝ (fun _ : ι => E) A)
    (g : ContinuousMultilinearMap ℝ (fun _ : κ => E) B) :
    concatenateCLM (ι := ι) (κ := κ) (E := E) P f g = concatenate P f g := rfl

end
end QuaternionicSymmetry.ContinuousMultilinearProduct
