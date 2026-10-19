/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Maps between represented commutative group presheaves

The group presheaves may live in a larger universe than the hom sets. Their
actual representing equivalences transport the group laws and turn natural
group homomorphisms into morphisms of the same represented group objects.
-/

noncomputable section

universe u v w

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace SchemeTheory.RepresentedGroups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
  {X Y : C} (F G : Cᵒᵖ ⥤ CommGrpCat.{w})
  (eF : (F ⋙ forget CommGrpCat).RepresentableBy X)
  (eG : (G ⋙ forget CommGrpCat).RepresentableBy Y)

/-- The commutative group law on the given representing object. -/
def groupObject : CommGrp C := by
  let : CommGrpObj X := CommGrpObj.ofRepresentableBy X F eF
  exact ⟨X⟩

/-- The representing equivalence preserves multiplication on every test object. -/
def pointEquiv (T : C) :
    let _ : CommGrpObj X := CommGrpObj.ofRepresentableBy X F eF
    (T ⟶ X) ≃* F.obj (op T) := by
  intro groupStructure
  refine { toEquiv := eF.homEquiv, map_mul' := ?_ }
  intro f g
  change eF.homEquiv (lift f g ≫ eF.homEquiv.symm
    (eF.homEquiv (fst X X) * eF.homEquiv (snd X X))) = _
  rw [eF.homEquiv_comp, Equiv.apply_symm_apply]
  change (F.map (lift f g).op).hom (_ * _) = _
  rw [map_mul]
  change (F ⋙ forget CommGrpCat).map (lift f g).op (eF.homEquiv (fst X X)) *
    (F ⋙ forget CommGrpCat).map (lift f g).op (eF.homEquiv (snd X X)) = _
  rw [← eF.homEquiv_comp, ← eF.homEquiv_comp, lift_fst, lift_snd]
  rfl

variable (a : F ⟶ G)

/-- The morphism representing a natural transformation is obtained from its universal section. -/
def mapMorphism : X ⟶ Y :=
  eG.homEquiv.symm ((a.app (op X)).hom (eF.homEquiv (𝟙 X)))

omit [CartesianMonoidalCategory C] [BraidedCategory C] in
/-- The represented morphism realizes the given natural transformation on every point. -/
theorem mapMorphism_homEquiv {T : C} (f : T ⟶ X) :
    eG.homEquiv (f ≫ mapMorphism F G eF eG a) =
      (a.app (op T)).hom (eF.homEquiv f) := by
  rw [eG.homEquiv_comp]
  change (G.map f.op).hom
    (eG.homEquiv (eG.homEquiv.symm ((a.app (op X)).hom (eF.homEquiv (𝟙 X))))) = _
  rw [Equiv.apply_symm_apply]
  exact (ConcreteCategory.congr_hom (a.naturality f.op)
    (eF.homEquiv (𝟙 X))).symm.trans
      (congrArg (a.app (op T)).hom (eF.homEquiv_eq f).symm)

/-- Natural group homomorphisms give actual morphisms of the represented group objects. -/
def map : groupObject F eF ⟶ groupObject G eG := by
  let : CommGrpObj X := CommGrpObj.ofRepresentableBy X F eF
  let : CommGrpObj Y := CommGrpObj.ofRepresentableBy Y G eG
  let m := mapMorphism F G eF eG a
  have hone (T : C) : (1 : T ⟶ X) ≫ m = (1 : T ⟶ Y) := by
    apply (pointEquiv G eG T).injective
    change eG.homEquiv (1 ≫ m) = (pointEquiv G eG T) 1
    rw [(pointEquiv G eG T).map_one, mapMorphism_homEquiv]
    change (a.app (op T)).hom ((pointEquiv F eF T) 1) = 1
    rw [(pointEquiv F eF T).map_one, map_one]
  have hmul (T : C) (f g : T ⟶ X) :
      (f * g) ≫ m = (f ≫ m) * (g ≫ m) := by
    apply (pointEquiv G eG T).injective
    rw [(pointEquiv G eG T).map_mul]
    change eG.homEquiv ((f * g) ≫ m) =
      eG.homEquiv (f ≫ m) * eG.homEquiv (g ≫ m)
    rw [mapMorphism_homEquiv, mapMorphism_homEquiv, mapMorphism_homEquiv]
    change (a.app (op T)).hom ((pointEquiv F eF T) (f * g)) = _
    rw [(pointEquiv F eF T).map_mul, map_mul]
    rfl
  have hmon : IsMonHom m :=
    { one_hom := by
        simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using hone (𝟙_ C)
      mul_hom := by
        simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp]
          using hmul (X ⊗ X) (fst X X) (snd X X) }
  exact InducedCategory.homMk
    (Grp.homMk' { hom := m, isMonHom_hom := hmon })

end SchemeTheory.RepresentedGroups
