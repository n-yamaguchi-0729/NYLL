/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Nyll.GaloisCohomology.Cyclic.IntegralTateInflation
public import Nyll.GaloisCohomology.Cyclic.IntegralTateTensorNorm

/-!
# Positive Tate pullback and cup with a fixed representative

Cup with a fixed vector is the original equivariant tensor inclusion.
Pullback along a group homomorphism commutes with that inclusion and uses
the image of the very same vector in the target coefficient module.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped RepTensor TensorProduct

namespace IntegralGroupCohomology.Universe

variable {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]

/-- Positive-degree Tate pullback commutes with cup against an actual
degree-zero fixed representative. -/
theorem tatePositiveMapAlong_tensorCupZeroRight_fixedClass {A B : Rep.{u} ℤ G}
    {C D : Rep.{u} ℤ H} (f : H →* G) (g : Rep.res f A ⟶ C) (h : Rep.res f B ⟶ D)
    (n : ℕ) [NeZero n] (x : tate A n) (b : B.ρ.invariants) :
    let d : D.ρ.invariants := ⟨h b.val, fun k => by
      rw [← Rep.hom_comm_apply]
      exact congrArg h (b.property (f k))⟩
    tatePositiveMapAlong f (g ⊗ᵣₘ h) n (tensorCupZeroRight A B n x (fixedClass B b)) =
      tensorCupZeroRight C D n (tatePositiveMapAlong f g n x) (fixedClass D d) := by
  intro d
  rw [tensorCupZeroRight_fixedClass, tensorCupZeroRight_fixedClass]
  let i := Rep.tensorInvariant A B b
  let j := Rep.tensorInvariant C D d
  have h₁ : (Rep.resFunctor f).map i ≫ (g ⊗ᵣₘ h) = g ≫ j := by
    apply Rep.hom_ext
    apply DFunLike.ext
    intro a
    change TensorProduct.map g.hom.toLinearMap h.hom.toLinearMap (a ⊗ₜ[ℤ] b.val) =
      (g a) ⊗ₜ[ℤ] (h b.val)
    rw [TensorProduct.map_tmul]
    rfl
  have h₂ := tatePositiveMapAlong_comp (MonoidHom.id G) f i (g ⊗ᵣₘ h) n
  change tatePositiveMapAlong f ((Rep.resFunctor f).map i ≫ (g ⊗ᵣₘ h)) n =
    tatePositiveMapAlong (MonoidHom.id G) i n ≫ tatePositiveMapAlong f (g ⊗ᵣₘ h) n at h₂
  have h₃ := tatePositiveMapAlong_comp f (MonoidHom.id H) g j n
  change tatePositiveMapAlong f (g ≫ j) n =
    tatePositiveMapAlong f g n ≫ tatePositiveMapAlong (MonoidHom.id H) j n at h₃
  rw [tatePositiveMapAlong_id_group] at h₂ h₃
  change ((tateFunctor G n).map i ≫ tatePositiveMapAlong f (g ⊗ᵣₘ h) n) x =
    (tatePositiveMapAlong f g n ≫ (tateFunctor H n).map j) x
  rw [← h₂, h₁, h₃]

end IntegralGroupCohomology.Universe
