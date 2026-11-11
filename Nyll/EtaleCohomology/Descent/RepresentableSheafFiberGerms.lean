/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Constructible.FiniteEtaleSheaf
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# The original represented-sheaf fiber comparison on actual germs

The existing represented-sheaf fiber isomorphism evaluates each actual
germ by the original point functor. Its defining colimit comparison gives
this formula directly.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

universe u v

namespace EtaleCohomology

variable {C : Type v} [Category.{u} C] {J : GrothendieckTopology C}
  [J.Subcanonical] (Φ : J.Point.{u})

omit [J.Subcanonical] in
private theorem toPresheafFiber_shrinkYonedaCompPresheafFiberIso
    (U W : C) (v : Φ.fiber.obj U) :
    Φ.toPresheafFiber U v (shrinkYoneda.{u}.obj W) ≫
        Φ.shrinkYonedaCompPresheafFiberIso.hom.app W =
      TypeCat.ofHom (fun a : (shrinkYoneda.{u}.obj W).obj (op U) =>
        Φ.fiber.map (shrinkYonedaObjObjEquiv.{u} a) v) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (Functor.Elements.isColimitCoconeπOpCompShrinkYonedaObj Φ.fiber W)
    (op (Φ.fiber.elementsMk U v))

/-- The existing representable fiber comparison sends the original germ
of a represented section to the original point functor applied to that
section. -/
theorem toPresheafFiber_representableSheafFiberIso
    (U W : C) (v : Φ.fiber.obj U) :
    Φ.toPresheafFiber U v (J.yoneda.obj W).obj ≫
        (representableSheafFiberIso Φ).hom.app W =
      TypeCat.ofHom (fun a : U ⟶ W => Φ.fiber.map a v) := by
  let η : yoneda.obj W ⟶ shrinkYoneda.{u}.obj W :=
    (shrinkYonedaIsoYoneda (C := C)).inv.app W
  let c : Φ.presheafFiber.obj (shrinkYoneda.{u}.obj W) ⟶ Φ.fiber.obj W :=
    Φ.shrinkYonedaCompPresheafFiberIso.hom.app W
  let b := TypeCat.ofHom (fun a : (shrinkYoneda.{u}.obj W).obj (op U) =>
        Φ.fiber.map (shrinkYonedaObjObjEquiv.{u} a) v)
  have hn : Φ.toPresheafFiber U v (yoneda.obj W) ≫ Φ.presheafFiber.map η =
      η.app (op U) ≫ Φ.toPresheafFiber U v (shrinkYoneda.{u}.obj W) :=
    Φ.toPresheafFiber_naturality η U v
  have hc : Φ.toPresheafFiber U v (shrinkYoneda.{u}.obj W) ≫ c = b :=
    toPresheafFiber_shrinkYonedaCompPresheafFiberIso Φ U W v
  change Φ.toPresheafFiber U v (yoneda.obj W) ≫ (Φ.presheafFiber.map η ≫ c) = _
  refine (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ c) hn).trans
      ((Category.assoc _ _ _).trans ((congrArg (fun k => η.app (op U) ≫ k) hc).trans ?_)))
  apply ConcreteCategory.hom_ext
  intro a
  change Φ.fiber.map (shrinkYonedaObjObjEquiv.{u} (shrinkYonedaObjObjEquiv.{u}.symm a)) v =
    Φ.fiber.map a v
  rw [Equiv.apply_symm_apply]

end EtaleCohomology
