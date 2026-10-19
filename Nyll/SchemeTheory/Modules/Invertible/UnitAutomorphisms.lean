/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Frames.PullbackFrame
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Automorphisms of the structure sheaf

Evaluation at the global section one identifies endomorphisms of the unit
module with global functions, and its automorphisms with invertible global
functions. These are sheaf morphisms on every open, not just arbitrary maps
on global sections.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- Apply a unit-module endomorphism using the ring of sections as carrier. -/
def unitEndApp (f : End (𝟙_ X.Modules)) (U : X.Opens) (s : Γ(X, U)) : Γ(X, U) :=
  f.app U (show Γ(𝟙_ X.Modules, U) from s)

/-- Evaluate an endomorphism of the unit module at its global section one. -/
def unitEndValue (f : End (𝟙_ X.Modules)) : Γ(X, ⊤) :=
  unitEndApp X f ⊤ 1

/-- A unit-module morphism acts on every open by its restricted global value. -/
theorem unitEnd_app (f : End (𝟙_ X.Modules)) (U : X.Opens) (s : Γ(X, U)) :
    unitEndApp X f U s =
      s * X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (unitEndValue X f) := by
  have hn := ConcreteCategory.congr_hom
    (f.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    (show Γ(𝟙_ X.Modules, ⊤) from (1 : Γ(X, ⊤)))
  change unitEndApp X f U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op 1) =
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (unitEndValue X f) at hn
  rw [map_one] at hn
  have hs := Hom.app_smul f s
    (show Γ(𝟙_ X.Modules, U) from (1 : Γ(X, U)))
  change unitEndApp X f U (s * 1) = s * unitEndApp X f U 1 at hs
  rw [mul_one, hn] at hs
  exact hs

/-- An endomorphism of the unit module is determined by the value of one. -/
theorem unitEndValue_injective : Function.Injective (unitEndValue X) := by
  intro f g h
  apply hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change unitEndApp X f U (show Γ(X, U) from s) =
    unitEndApp X g U (show Γ(X, U) from s)
  rw [unitEnd_app, unitEnd_app, h]

/-- Every global function defines the corresponding multiplication endomorphism. -/
theorem unitEndValue_surjective : Function.Surjective (unitEndValue X) := by
  intro a
  refine ⟨FramePullback.smulHom (𝟙_ X.Modules)
    (show Γ(𝟙_ X.Modules, ⊤) from a), ?_⟩
  change (1 : Γ(X, ⊤)) *
    X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op a = a
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _),
    op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply, one_mul]

/-- Evaluation at one is multiplicative for composition of unit-module maps. -/
def unitEndValueHom : End (𝟙_ X.Modules) →* Γ(X, ⊤) where
  toFun := unitEndValue X
  map_one' := rfl
  map_mul' f g := by
    change unitEndApp X f ⊤ (unitEndValue X g) =
      unitEndValue X f * unitEndValue X g
    rw [unitEnd_app]
    rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _),
      op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
    exact mul_comm _ _

/-- The monoid of sheaf endomorphisms of the unit is the monoid of global functions. -/
def unitEndEquivSections : End (𝟙_ X.Modules) ≃* Γ(X, ⊤) :=
  MulEquiv.ofBijective (unitEndValueHom X)
    ⟨unitEndValue_injective X, unitEndValue_surjective X⟩

/-- Actual automorphisms of the unit sheaf correspond to global units. -/
def unitAutEquivUnits : Aut (𝟙_ X.Modules) ≃* Γ(X, ⊤)ˣ :=
  (Aut.unitsEndEquivAut (𝟙_ X.Modules)).symm.trans
    (Units.mapEquiv (unitEndEquivSections X))

/-- The unit corresponding to an automorphism is its value on the global section one. -/
@[simp]
theorem unitAutEquivUnits_val (e : Aut (𝟙_ X.Modules)) :
    (unitAutEquivUnits X e : Γ(X, ⊤)) = unitEndValue X e.hom := rfl

/-- Composition of scalar automorphisms multiplies their global units. -/
theorem unitAutEquivUnits_trans (e f : Aut (𝟙_ X.Modules)) :
    unitAutEquivUnits X (e ≪≫ f) = unitAutEquivUnits X e * unitAutEquivUnits X f := by
  change unitAutEquivUnits X (f * e) = _
  rw [map_mul, mul_comm]

/-- The composition formula expressed with the literal sheaf-isomorphism type. -/
theorem unitAutEquivUnits_isoTrans (e f : 𝟙_ X.Modules ≅ 𝟙_ X.Modules) :
    unitAutEquivUnits X (e ≪≫ f) = unitAutEquivUnits X e * unitAutEquivUnits X f :=
  unitAutEquivUnits_trans X e f

end AlgebraicGeometry.Scheme.Modules
