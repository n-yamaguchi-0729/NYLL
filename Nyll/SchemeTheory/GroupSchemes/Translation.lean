/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Translation on actual group schemes

A section over the base gives an automorphism of the underlying scheme over that
base. The point formula holds on every parameter scheme, including nonreduced ones.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupSchemes

variable {S : Scheme.{u}} (G : CommGrp (Over S))

/-- Translation by a base section on the actual underlying scheme over the base. -/
def translation (x : ⊤_ (Over S) ⟶ G.X) : G.X ≅ G.X where
  hom := 𝟙 G.X * (terminal.from G.X ≫ x)
  inv := 𝟙 G.X * (terminal.from G.X ≫ x⁻¹)
  hom_inv_id := by
    simp only [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      terminal.comp_from, GrpObj.comp_inv, mul_inv_cancel_right]
  inv_hom_id := by
    simp only [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      terminal.comp_from, GrpObj.comp_inv, inv_mul_cancel_right]

/-- Translation multiplies every parameter point by the pulled-back base section. -/
theorem translation_point (x : ⊤_ (Over S) ⟶ G.X) {T : Over S} (t : T ⟶ G.X) :
    t ≫ (translation G x).hom = t * (terminal.from T ≫ x) := by
  simp only [translation, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    terminal.comp_from]

/-- Translating by the identity section is the identity automorphism. -/
theorem translation_one : translation G 1 = Iso.refl G.X := by
  apply Iso.ext
  change 𝟙 G.X * (terminal.from G.X ≫ (1 : ⊤_ (Over S) ⟶ G.X)) = 𝟙 G.X
  rw [MonObj.comp_one, mul_one]

/-- Successive translations are translation by the product of the sections. -/
theorem translation_mul (x y : ⊤_ (Over S) ⟶ G.X) :
    translation G (x * y) = translation G x ≪≫ translation G y := by
  apply Iso.ext
  change 𝟙 G.X * (terminal.from G.X ≫ (x * y)) =
    (𝟙 G.X * (terminal.from G.X ≫ x)) ≫
      (𝟙 G.X * (terminal.from G.X ≫ y))
  simp only [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    terminal.comp_from, mul_assoc]

/-- Group-scheme homomorphisms commute with translation by corresponding sections. -/
theorem translation_hom {H : CommGrp (Over S)} (f : G ⟶ H)
    (x : ⊤_ (Over S) ⟶ G.X) :
    (translation G x).hom ≫ f.hom.hom.hom =
      f.hom.hom.hom ≫ (translation H (x ≫ f.hom.hom.hom)).hom := by
  simp only [translation, MonObj.mul_comp, MonObj.comp_mul, Category.id_comp,
    Category.comp_id, ← Category.assoc, terminal.comp_from]

end AlgebraicGeometry.GroupSchemes
