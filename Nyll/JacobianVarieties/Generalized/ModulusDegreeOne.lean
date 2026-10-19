/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PoincareFrameQuotient
import Nyll.JacobianVarieties.Generalized.ModulusUnitFunctor
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # A degree-one modulus is an actual rational reduced point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}
  (D : RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))))

/-- Rank one identifies the entire finite modulus with the ground field spectrum. -/
theorem modulusBaseMap_isIso_of_degree_one : IsIso (modulusBaseMap D) := by
  have : IsFinite (modulusBaseMap D) := D.isFinite
  have hb : Function.Bijective (algebraMap K (modulusAlgebra D)) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp (finrank_modulusAlgebra D)
  have : IsIso (CommRingCat.ofHom (algebraMap K (modulusAlgebra D))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  rw [← coordinateIso_toBase (modulusBaseMap D)]
  infer_instance

/-- The rational point defined by the actual degree-one modulus. -/
def degreeOneSection : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c := by
  let : IsIso (modulusBaseMap D) := modulusBaseMap_isIso_of_degree_one D
  refine ⟨(asIso (modulusBaseMap D)).inv ≫ modulusCurveMap D, ?_⟩
  rw [Category.assoc, modulusCurveMap_toBase, asIso_inv, IsIso.inv_hom_id]

namespace ScalarFrames

/-- When the whole modulus is the base itself, every modulus unit is a parameter scalar. -/
theorem modulusScalars_eq_top_of_isIso {Y S : Scheme.{u}} (q : Y ⟶ S) [IsIso q]
    (T : Over S) : modulusScalars q T = ⊤ := by
  have : IsIso (modulusProjection q T) :=
    inferInstanceAs (IsIso (pullback.fst T.hom q))
  have : IsIso (modulusProjection q T).appTop :=
    Scheme.Γ.map_isIso (modulusProjection q T).op
  have hb : Function.Bijective (modulusProjection q T).appTop.hom.toMonoidHom :=
    ConcreteCategory.bijective_of_isIso (modulusProjection q T).appTop
  exact MonoidHom.range_eq_top.mpr (Units.map_bijective hb).surjective

/-- The actual scalar quotient has a single element on every test scheme in degree one. -/
theorem modulusUnitQuotient_subsingleton_of_degree_one (T : Over (Spec (CommRingCat.of K))) :
    Subsingleton (ModulusUnits (modulusBaseMap D) T ⧸ modulusScalars (modulusBaseMap D) T) := by
  have : IsIso (modulusBaseMap D) := modulusBaseMap_isIso_of_degree_one D
  rw [modulusScalars_eq_top_of_isIso]
  exact QuotientGroup.subsingleton_quotient_top

end ScalarFrames

end AlgebraicGeometry.GeneralizedJacobian
