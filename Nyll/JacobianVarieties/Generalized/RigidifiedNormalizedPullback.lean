/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedSection
import Nyll.JacobianVarieties.Generalized.RigidifiedPullbackTensor

/-! # Pullback preserves the actual section normalized along the full modulus -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

private theorem normalized_oplax_unit {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W] {F G : V ⥤ W}
    [F.Monoidal] [G.Monoidal] (θ : F ⟶ G) [θ.IsMonoidal] :
    θ.app (𝟙_ V) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
  rw [← Category.assoc, NatTrans.IsMonoidal.unit,
    Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]

variable {X X' D D' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
  (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i)

/-- Pulling back the specified section preserves its normalization on the whole modulus. -/
theorem pullback_normalized_section (M : RigidifiedLineBundle i)
    (s : 𝟙_ X.Modules ⟶ M.L)
    (hs : pullbackSection i s ≫ M.trivialization.hom = 𝟙 (𝟙_ D.Modules)) :
    pullbackSection i' (pullbackSection f s) ≫ (M.pullback f g w).trivialization.hom =
      𝟙 (𝟙_ D'.Modules) := by
  let F : X.Modules ⥤ X'.Modules := Scheme.Modules.pullback f
  let H : X'.Modules ⥤ D'.Modules := Scheme.Modules.pullback i'
  let G : X.Modules ⥤ D.Modules := Scheme.Modules.pullback i
  let K : D.Modules ⥤ D'.Modules := Scheme.Modules.pullback g
  have hs' : G.map s ≫ M.trivialization.hom = (Scheme.Modules.pullbackTensorUnitObjIso i).hom := by
    apply (cancel_epi (Scheme.Modules.pullbackTensorUnitObjIso i).inv).mp
    rw [← pullbackUnitComparison i]
    exact hs.trans (Scheme.Modules.pullbackUnitIso i).inv_hom_id.symm
  have hn := (restrictionComparison f g w).hom.naturality s
  have hu : (restrictionComparison f g w).hom.app (𝟙_ X.Modules) ≫
      K.map (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso g).hom =
      H.map (Scheme.Modules.pullbackTensorUnitObjIso f).hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso i').hom :=
    normalized_oplax_unit (restrictionComparison f g w).hom
  change pullbackSection i' (pullbackSection f s) ≫
    (restrictionComparison f g w).hom.app M.L ≫ K.map M.trivialization.hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso g).hom = _
  rw [pullbackSection_def, pullbackSection_def, pullbackUnitComparison,
    pullbackUnitComparison]
  change Functor.LaxMonoidal.ε H ≫ H.map (Functor.LaxMonoidal.ε F ≫ F.map s) ≫
    (restrictionComparison f g w).hom.app M.L ≫ K.map M.trivialization.hom ≫
      Functor.OplaxMonoidal.η K = 𝟙 _
  change G.map s ≫ M.trivialization.hom = Functor.OplaxMonoidal.η G at hs'
  change (restrictionComparison f g w).hom.app (𝟙_ X.Modules) ≫
    K.map (Functor.OplaxMonoidal.η G) ≫ Functor.OplaxMonoidal.η K =
      H.map (Functor.OplaxMonoidal.η F) ≫ Functor.OplaxMonoidal.η H at hu
  rw [H.map_comp, Category.assoc, reassoc_of% hn, ← K.map_comp_assoc, hs', hu]
  rw [← H.map_comp_assoc, Functor.Monoidal.ε_η, H.map_id, Category.id_comp,
    Functor.Monoidal.ε_η]

/-- Actual canonical inverse-ideal rigidifications commute with pullback, including sections. -/
def ofInvertibleIdealPullbackIso
    (I : X.IdealSheafData) (hI : I.IsInvertible)
    (havoid : ∀ y : D, i.base y ∉ I.support)
    (hI' : (I.comap f).IsInvertible)
    (havoid' : ∀ y : D', i'.base y ∉ (I.comap f).support) :
    Iso ((ofInvertibleIdeal i I hI havoid).pullback f g w)
      (ofInvertibleIdeal i' (I.comap f) hI' havoid') :=
  zeroDivisorIso ((ofInvertibleIdeal i I hI havoid).pullback f g w)
    (pullbackSection f I.invModuleSection)
    (pullback_normalized_section f g w (ofInvertibleIdeal i I hI havoid)
      I.invModuleSection (ofInvertibleIdeal_section i I hI havoid))
    (I.comap f) hI' (by
      exact (Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal f
        hI.isInvertible_invModule I.invModuleSection).symm.trans
          (congrArg (fun J => J.comap f) hI.zeroSchemeIdeal_invModuleSection)) havoid'

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
