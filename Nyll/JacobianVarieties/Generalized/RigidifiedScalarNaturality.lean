/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedScalarTensor
import Nyll.JacobianVarieties.Generalized.RigidifiedPullbackTensor

/-! # The actual scalar boundary commutes with scheme pullbacks -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

private theorem monoidal_oplax_unit {V W : Type*} [Category V] [Category W]
    [MonoidalCategory V] [MonoidalCategory W] {F G : V ⥤ W}
    [F.Monoidal] [G.Monoidal] (θ : F ⟶ G) [θ.IsMonoidal] :
    θ.app (𝟙_ V) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).mp
  rw [← Category.assoc, NatTrans.IsMonoidal.unit,
    Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]

variable {X X' D D' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}
  (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i)

/-- The unit pullback isomorphism preserves the actual pulled scalar trivialization. -/
def unitWithPullbackIso (a : 𝟙_ D.Modules ≅ 𝟙_ D.Modules) :
    Iso ((unitWith i a).pullback f g w) (unitWith i' (restrictUnitAut g a)) where
  toIso := Scheme.Modules.pullbackTensorUnitObjIso f
  compatible := by
    have hu : (restrictionComparison f g w).hom.app (𝟙_ X.Modules) ≫
        (Scheme.Modules.pullback g).map (Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫
          (Scheme.Modules.pullbackTensorUnitObjIso g).hom =
      (Scheme.Modules.pullback i').map (Scheme.Modules.pullbackTensorUnitObjIso f).hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso i').hom :=
      monoidal_oplax_unit (restrictionComparison f g w).hom
    change (Scheme.Modules.pullback i').map
        (Scheme.Modules.pullbackTensorUnitObjIso f).hom ≫
      (Scheme.Modules.pullbackTensorUnitObjIso i').hom ≫
        (Scheme.Modules.pullbackTensorUnitObjIso g).inv ≫
          (Scheme.Modules.pullback g).map a.hom ≫
            (Scheme.Modules.pullbackTensorUnitObjIso g).hom =
      (restrictionComparison f g w).hom.app (𝟙_ X.Modules) ≫
        (Scheme.Modules.pullback g).map
          ((Scheme.Modules.pullbackTensorUnitObjIso i).hom ≫ a.hom) ≫
            (Scheme.Modules.pullbackTensorUnitObjIso g).hom
    rw [← reassoc_of% hu, CategoryTheory.Iso.hom_inv_id_assoc, Functor.map_comp]
    simp only [Category.assoc]

/-- The chosen scalar automorphism changes by the actual restriction of its global unit. -/
theorem scalarClass_pullback (a : Γ(D, ⊤)ˣ) :
    classesPullback f g w (scalarClass i a) =
      scalarClass i' (Units.map g.appTop.hom.toMonoidHom a) := by
  have ha : (unitAutEquivUnits D').symm (Units.map g.appTop.hom.toMonoidHom a) =
      restrictUnitAut g ((unitAutEquivUnits D).symm a) := by
    apply (unitAutEquivUnits D').injective
    calc
      _ = Units.map g.appTop.hom.toMonoidHom a :=
        (unitAutEquivUnits D').apply_symm_apply _
      _ = Units.map g.appTop.hom.toMonoidHom
          (unitAutEquivUnits D ((unitAutEquivUnits D).symm a)) :=
        congrArg (Units.map g.appTop.hom.toMonoidHom)
          ((unitAutEquivUnits D).apply_symm_apply a).symm
      _ = _ := (unitAutEquivUnits_restrict g _).symm
  change classOf ((unitWith i ((unitAutEquivUnits D).symm a)).pullback f g w) =
    classOf (unitWith i' ((unitAutEquivUnits D').symm
      (Units.map g.appTop.hom.toMonoidHom a)))
  rw [ha]
  exact Quotient.sound ⟨unitWithPullbackIso f g w _⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
