import QuaternionicSymmetry.HolomorphicLineCoreClassGroup
import QuaternionicSymmetry.HolomorphicLineCorePullbackComposition

/-! Holomorphic pullback is a genuine group homomorphism on line-bundle
isomorphism classes. Its descent uses all-overlap pulled-back gauges, not
chosen representatives of the quotient. This supplies the restriction map
needed for the Picard argument; no Picard-rank or fiber-degree statement is
assumed or deduced here. -/

namespace QuaternionicSymmetry.HolomorphicLineClassPullback

open HolomorphicLineGauge HolomorphicLineCoreClasses
open HolomorphicLineCoreClassGroup HolomorphicLineCorePullback
open scoped Manifold ContDiff
noncomputable section

universe u
variable {B B' H H' F F' : Type*}
  [TopologicalSpace B] [TopologicalSpace B']
  [TopologicalSpace H] [TopologicalSpace H']
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [ChartedSpace H B] [ChartedSpace H' B']
  (IB : ModelWithCorners ℂ F H) (IB' : ModelWithCorners ℂ F' H')

/-- Every local scalar and every overlap identity pulls back along the
actual holomorphic map. -/
def pullbackGauge {ι κ : Type*}
    {Z : VectorBundleCore ℂ B ℂ ι} {W : VectorBundleCore ℂ B ℂ κ}
    [Z.IsContMDiff IB ∞] [W.IsContMDiff IB ∞]
    (e : GaugeIso (IB := IB) Z W)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    letI := pullbackCore_isContMDiff IB IB' Z f hf
    letI := pullbackCore_isContMDiff IB IB' W f hf
    GaugeIso (IB := IB') (pullbackCore Z f hf.continuous)
      (pullbackCore W f hf.continuous) := by
  letI := pullbackCore_isContMDiff IB IB' Z f hf
  letI := pullbackCore_isContMDiff IB IB' W f hf
  exact {
    forward := fun i a x => e.forward i a (f x)
    backward := fun a i x => e.backward a i (f x)
    forward_holomorphic := fun i a =>
      (e.forward_holomorphic i a).comp hf.contMDiffOn (fun _ hx => hx)
    backward_holomorphic := fun a i =>
      (e.backward_holomorphic a i).comp hf.contMDiffOn (fun _ hx => hx)
    forward_compat := fun i j a b x hx => e.forward_compat i j a b (f x) hx
    backward_compat := fun a b i j x hx => e.backward_compat a b i j (f x) hx
    left_inverse := fun i a x hx => e.left_inverse i a (f x) hx
    right_inverse := fun a i x hx => e.right_inverse a i (f x) hx }

theorem pullback_respects {L M : LineCore.{u} (B := B) IB}
    (h : Isomorphic IB L M)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    Isomorphic IB' (pullbackLineCore IB IB' L f hf)
      (pullbackLineCore IB IB' M f hf) := by
  letI := L.holomorphic
  letI := M.holomorphic
  obtain ⟨e⟩ := h
  exact ⟨pullbackGauge IB IB' e f hf⟩

/-- Pullback of genuine line-bundle classes, independent of the chosen
core and its trivializing cover. -/
def pullbackClass (f : B' → B) (hf : ContMDiff IB' IB ∞ f)
    (c : CoreClass.{u} (B := B) IB) : CoreClass.{u} (B := B') IB' :=
  Quotient.liftOn c
    (fun L => Quotient.mk _ (pullbackLineCore IB IB' L f hf))
    (fun _ _ h => Quotient.sound (pullback_respects IB IB' h f hf))

theorem pullbackLine_tensor (L M : LineCore.{u} (B := B) IB)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    pullbackLineCore IB IB' (L.tensor IB M) f hf =
      (pullbackLineCore IB IB' L f hf).tensor IB'
        (pullbackLineCore IB IB' M f hf) := rfl

theorem pullbackLine_trivial
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    pullbackLineCore IB IB' (trivialLine.{u} IB) f hf =
      trivialLine.{u} IB' := rfl

/-- Restriction preserves tensor multiplication, the actual trivial
line, duals, and all integral powers by the group-homomorphism laws. -/
def pullbackHom (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    CoreClass.{u} (B := B) IB →* CoreClass.{u} (B := B') IB' where
  toFun := pullbackClass IB IB' f hf
  map_one' := rfl
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h L =>
      induction b using Quotient.inductionOn with
      | h M => rfl

@[simp] theorem pullbackHom_class (L : LineCore.{u} (B := B) IB)
    (f : B' → B) (hf : ContMDiff IB' IB ∞ f) :
    pullbackHom IB IB' f hf (Quotient.mk _ L) =
      Quotient.mk _ (pullbackLineCore IB IB' L f hf) := rfl

end
end QuaternionicSymmetry.HolomorphicLineClassPullback
