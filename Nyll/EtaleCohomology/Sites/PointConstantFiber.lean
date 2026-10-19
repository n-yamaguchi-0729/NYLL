/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Actual fibers of constant sheaves

A point has exactly one element over a terminal object of the site. Consequently
terminal sections of its native skyscraper recover the coefficient object.
Uniqueness of left adjoints then identifies the actual fiber of a constant
sheaf with its original coefficient object. This applies to arbitrary
coefficients for which the native constructions exist.
-/

noncomputable section

universe u v w uA vA

open CategoryTheory Limits Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} (Φ : Point.{w} J)
  (A : Type uA) [Category.{vA} A] [HasProducts.{w} A]
  {T : C} (hT : IsTerminal T)

/-- Sections at the actual terminal object recover the coefficient of a
native point skyscraper through the singleton product comparison. -/
def skyscraperSheafFunctorSectionsIso :
    Φ.skyscraperSheafFunctor (A := A) ⋙ (sheafSections J A).obj (op T) ≅ 𝟭 A := by
  let : Unique (Φ.fiber.obj T) := Φ.uniqueFiberObj T hT
  exact NatIso.ofComponents
    (fun M => productUniqueIso (fun _ : Φ.fiber.obj T => M)) (by
      intro M N f
      change Limits.Pi.map (fun _ : Φ.fiber.obj T => f) ≫
          (productUniqueIso (fun _ : Φ.fiber.obj T => N)).hom =
        (productUniqueIso (fun _ : Φ.fiber.obj T => M)).hom ≫ f
      simp only [productUniqueIso_hom, Limits.Pi.map_π])

variable [HasColimitsOfSize.{w, w} A] [HasWeakSheafify J A]

/-- The actual point fiber of a constant sheaf is its original coefficient,
by the native skyscraper adjunction and constant-sheaf adjunction. -/
def constantSheafCompFiberIso :
    constantSheaf J A ⋙ Φ.sheafFiber ≅ 𝟭 A :=
  (((constantSheafAdj J A hT).comp Φ.skyscraperSheafAdjunction).ofNatIsoRight
    (Φ.skyscraperSheafFunctorSectionsIso A hT)).leftAdjointUniq (Adjunction.id)

end CategoryTheory.GrothendieckTopology.Point
