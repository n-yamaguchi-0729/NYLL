/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.GroupLaw.CommGroupRelativeLaw
import Nyll.AlgebraicCurves.Models.Construction.Basic

/-! # Values of a regular group-valued map at function-field places

The evaluator is constructed from the actual morphism and the original target
point group. It agrees with the morphism on the open curve and is zero at the
remaining places. No point-value compatibility needs to be supplied separately.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.CurveModel

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] (M : CurveModel K F)

/-- The place of an actual rational point of an open curve. -/
def openPointPlace (U : M.C.Opens)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase)) : Place K F :=
  M.pointEquivPlace ⟨x.1 ≫ U.ι, (Category.assoc _ _ _).trans x.2⟩

/-- Passing from actual open-curve points to places is injective. -/
theorem openPointPlace_injective (U : M.C.Opens) : Function.Injective (M.openPointPlace U) := by
  intro x y h
  apply Subtype.ext
  apply (cancel_mono U.ι).mp
  exact congrArg Subtype.val (M.pointEquivPlace.injective h)

/-- Values of a regular map to an actual commutative group, extended by zero. -/
def regularMapValues (U : M.C.Opens)
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) :
    Place K F → Additive (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X) :=
  Function.extend (M.openPointPlace U)
    (fun x => commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x q)) (fun _ => 0)

/-- The constructed place evaluator has exactly the original map's value. -/
theorem regularMapValues_apply (U : M.C.Opens)
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom)
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (U.ι ≫ M.toBase)) :
    M.regularMapValues U G q (M.openPointPlace U x) =
      commGroupPointValue G (𝟙 _) (NeronModelInfra.schemeHomOverComp x q) :=
  (M.openPointPlace_injective U).extend_apply _ _ x

/-- At a place outside the open point locus, the extension is zero. -/
theorem regularMapValues_eq_zero (U : M.C.Opens)
    (G : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) (w : Place K F)
    (hw : ¬∃ x, M.openPointPlace U x = w) : M.regularMapValues U G q w = 0 :=
  Function.extend_apply' _ _ w hw


/-- Postcomposition uses the original target homomorphism on actual point values,
including the zero extension at places outside the open curve. -/
theorem regularMapValues_comp (U : M.C.Opens)
    (G H : CommGrp (Over (Spec (CommRingCat.of K))))
    (q : SchemeHomOver (U.ι ≫ M.toBase) G.X.hom) (φ : G ⟶ H) (w : Place K F) :
    M.regularMapValues U H
        ((commGroupPointEquiv H (U.ι ≫ M.toBase)).symm
          ((commGroupPointEquiv G (U.ι ≫ M.toBase) q) ≫ φ.hom.hom.hom)) w =
      (IsMonHom.monoidHom φ.hom.hom.hom
        (Over.mk (𝟙 (Spec (CommRingCat.of K))))).toAdditive
          (M.regularMapValues U G q w) := by
  classical
  by_cases hw : ∃ x, M.openPointPlace U x = w
  · obtain ⟨x, rfl⟩ := hw
    rw [M.regularMapValues_apply, M.regularMapValues_apply]
    simp only [commGroupPointValue, commGroupPointEquiv_comp, Equiv.apply_symm_apply,
      MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul,
      IsMonHom.monoidHom_apply]
    exact congrArg Additive.ofMul (Category.assoc _ _ _).symm
  · rw [M.regularMapValues_eq_zero U H _ w hw,
      M.regularMapValues_eq_zero U G q w hw, map_zero]

end AlgebraicCurve.CurveModel
