/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-! # Translation by an actual identity kernel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupSchemes

variable {S : Scheme.{u}} {G H A L : CommGrp (Over S)}
  (a : G ⟶ H) (b : L ⟶ H) (p : H ⟶ A)

/-- Translate a homomorphism by a second group coordinate. -/
def kernelTranslation : Limits.prod G.X L.X ⟶ H.X :=
  (Limits.prod.fst (X := G.X) (Y := L.X) ≫ a.hom.hom.hom) *
    (Limits.prod.snd (X := G.X) (Y := L.X) ≫ b.hom.hom.hom)

variable (hb : b.hom.hom.hom ≫ p.hom.hom.hom = 1)
  (hkernel : IsLimit (Fork.ofι b.hom.hom.hom
    (hb.trans (MonObj.comp_one b.hom.hom.hom).symm)))

include hb hkernel in
/-- Translation by the actual identity kernel gives the canonical pullback square.
The only kernel input is its usual equalizer universal property. -/
theorem kernelTranslation_isPullback :
    IsPullback (kernelTranslation a b) Limits.prod.fst p.hom.hom.hom
      (a.hom.hom.hom ≫ p.hom.hom.hom) := by
  have hproj : kernelTranslation a b ≫ p.hom.hom.hom =
      Limits.prod.fst ≫ (a.hom.hom.hom ≫ p.hom.hom.hom) := by
    simp only [kernelTranslation, MonObj.mul_comp, Category.assoc, hb,
      MonObj.comp_one, mul_one]
  have : Mono b.hom.hom.hom := Fork.IsLimit.mono hkernel
  apply IsPullback.of_map_of_faithful yoneda
  apply IsPullback.of_forall_isPullback_app
  intro T
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply TypeCat.homEquiv.injective
    funext x
    change (x ≫ kernelTranslation a b) ≫ p.hom.hom.hom =
      (x ≫ Limits.prod.fst) ≫ (a.hom.hom.hom ≫ p.hom.hom.hom)
    rw [Category.assoc, hproj, Category.assoc]
  · intro x y h
    have hfst : x ≫ Limits.prod.fst = y ≫ Limits.prod.fst := h.2
    have hact : x ≫ kernelTranslation a b = y ≫ kernelTranslation a b := h.1
    apply Limits.prod.hom_ext
    · exact hfst
    · apply (cancel_mono b.hom.hom.hom).mp
      have hm : ((x ≫ Limits.prod.fst) ≫ a.hom.hom.hom) *
          ((x ≫ Limits.prod.snd) ≫ b.hom.hom.hom) =
        ((y ≫ Limits.prod.fst) ≫ a.hom.hom.hom) *
          ((y ≫ Limits.prod.snd) ≫ b.hom.hom.hom) := by
        simpa only [kernelTranslation, MonObj.comp_mul, ← Category.assoc] using hact
      rw [hfst] at hm
      exact mul_left_cancel hm
  · intro x y h
    change x ≫ p.hom.hom.hom = y ≫ (a.hom.hom.hom ≫ p.hom.hom.hom) at h
    let δ := (y ≫ a.hom.hom.hom)⁻¹ * x
    have hd : δ ≫ p.hom.hom.hom = δ ≫ (1 : H.X ⟶ A.X) := by
      rw [MonObj.comp_one]
      change ((y ≫ a.hom.hom.hom)⁻¹ * x) ≫ p.hom.hom.hom = 1
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ← h, inv_mul_cancel]
    let l : T.unop ⟶ L.X := Fork.IsLimit.lift hkernel δ hd
    have hl : l ≫ b.hom.hom.hom = δ := Fork.IsLimit.lift_ι' hkernel δ hd
    refine ⟨Limits.prod.lift y l, ?_, ?_⟩
    · change Limits.prod.lift y l ≫ kernelTranslation a b = x
      rw [kernelTranslation, MonObj.comp_mul, ← Category.assoc, ← Category.assoc,
        Limits.prod.lift_fst, Limits.prod.lift_snd, hl]
      exact mul_inv_cancel_left (y ≫ a.hom.hom.hom) x
    · change Limits.prod.lift y l ≫ Limits.prod.fst = y
      exact Limits.prod.lift_fst y l

end AlgebraicGeometry.GroupSchemes
