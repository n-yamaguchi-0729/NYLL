/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedAlgEquivZero
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Actual local rigidifications of an unrigidified family

Trivializing the restriction of a line bundle to the chosen section gives a
Zariski cover of the parameter scheme. On that cover the original pulled bundle
itself is pointed-rigidifiable; no global frame or globally trivial base twist
is assumed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra

namespace AlgebraicGeometry.RelPicard.Unrigidified

variable {R : Type u} [CommRing R] {C T : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {t : T ⟶ Spec (CommRingCat.of R)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (M : LineBundle c t)

/-- An actual trivializing cover of the restriction to the chosen curve section. -/
def localRigidificationCover :
    {V : T.OpenCover // ∀ j : V.I₀, Nonempty
      ((Scheme.Modules.pullback (rigSection c (V.f j ≫ t) ε)).obj
        ((Scheme.Modules.pullback
          (baseChangeSnd c (⟨V.f j, rfl⟩ : SchemeHomOver (V.f j ≫ t) t))).obj M.1) ≅
            𝟙_ (V.X j).Modules)} := by
  classical
  choose U hx he using (M.2.pullback (rigSection c t ε)).exists_trivialization
  let V : T.OpenCover := Scheme.Cover.mkOfCovers
    (P := (@IsOpenImmersion : MorphismProperty Scheme.{u})) T
    (fun x => (U x).toScheme) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  refine ⟨V, fun x => ⟨?_⟩⟩
  let f : SchemeHomOver ((U x).ι ≫ t) t := ⟨(U x).ι, rfl⟩
  exact (Scheme.Modules.pullbackComp (rigSection c ((U x).ι ≫ t) ε)
      (baseChangeSnd c f)).app M.1 ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε f)).app M.1 ≪≫
    ((Scheme.Modules.pullbackComp (U x).ι (rigSection c t ε)).app M.1).symm ≪≫
    (he x).some

/-- The local pointed bundle keeps exactly the actual pulled underlying module. -/
def localPointedBundle (j : (localRigidificationCover ε M).val.I₀) :
    RelPicard.RigidifiedLineBundle c ε ((localRigidificationCover ε M).val.f j ≫ t) where
  L := (Scheme.Modules.pullback
    (baseChangeSnd c (⟨(localRigidificationCover ε M).val.f j, rfl⟩ :
      SchemeHomOver ((localRigidificationCover ε M).val.f j ≫ t) t))).obj M.1
  isInvertible := M.2.pullback _
  rigidified := (localRigidificationCover ε M).property j

/-- The local pointed bundles retain the actual geometric-fibre zero condition. -/
theorem localPointedBundle_mem_zero (hM : FibrewiseZero M)
    (j : (localRigidificationCover ε M).val.I₀) :
    (algEquivZeroCut c ε).P ((localRigidificationCover ε M).val.f j ≫ t)
      (localPointedBundle ε M j) :=
  fibrewiseZero_pullback
    (⟨(localRigidificationCover ε M).val.f j, rfl⟩ :
      SchemeHomOver ((localRigidificationCover ε M).val.f j ≫ t) t) hM

end AlgebraicGeometry.RelPicard.Unrigidified
