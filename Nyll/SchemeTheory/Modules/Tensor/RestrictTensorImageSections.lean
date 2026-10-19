/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Tensor.RestrictTensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# Tensor sections on the image of an open immersion

The restriction adjunction initially produces sections on the inverse
image of an open set. Transporting along the actual equality between an
open and the inverse image of its image recovers the original
`restrictAppIso` inverse. The native tensor restriction isomorphism
therefore preserves pure tensors under these exact section isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]

/-- Transporting the original restriction unit back from the inverse
image of an image gives the original inverse section isomorphism. -/
theorem restrictAppIso_inv_eq_unit_map (M : Y.Modules) (U : X.Opens)
    (x : Γ(M, j ''ᵁ U)) :
    (M.restrict j).presheaf.map (eqToHom (j.preimage_image_eq U).symm).op
        (((restrictAdjunction j).unit.app M).app (j ''ᵁ U) x) =
      (M.restrictAppIso j U).inv x := by
  let V : X.Opens := j ⁻¹ᵁ j ''ᵁ U
  let i : U ⟶ V := eqToHom (j.preimage_image_eq U).symm
  let a : j ''ᵁ V ⟶ j ''ᵁ U := homOfLE (j.image_preimage_le (j ''ᵁ U))
  let b : j ''ᵁ U ⟶ j ''ᵁ V := homOfLE (j.image_mono (leOfHom i))
  let η : Γ(M, j ''ᵁ U) ⟶ Γ(M.restrict j, V) :=
    ((restrictAdjunction j).unit.app M).app (j ''ᵁ U)
  let e : Γ(M.restrict j, U) ≅ Γ(M, j ''ᵁ U) := M.restrictAppIso j U
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  have hn := congrArg (fun k : Γ(M.restrict j, V) ⟶ Γ(M, j ''ᵁ U) => k (η x))
    (M.map_restrictAppIso_hom j i.op)
  have hη : (M.restrictAppIso j V).hom (η x) = M.presheaf.map a.op x := rfl
  have hc : M.presheaf.map a.op ≫ M.presheaf.map b.op = 𝟙 Γ(M, j ''ᵁ U) := by
    rw [← CategoryTheory.Functor.map_comp,
      Subsingleton.elim (a.op ≫ b.op) (𝟙 _), CategoryTheory.Functor.map_id]
  have hx := congrArg (fun k : Γ(M, j ''ᵁ U) ⟶ Γ(M, j ''ᵁ U) => k x) hc
  have he := congrArg (fun k : Γ(M, j ''ᵁ U) ⟶ Γ(M, j ''ᵁ U) => k x) e.inv_hom_id
  exact hn.trans ((congrArg (fun y : Γ(M, j ''ᵁ V) => M.presheaf.map b.op y) hη).trans
    (hx.trans he.symm))

/-- The actual tensor restriction isomorphism preserves the tensor
of the two inverse section isomorphisms over every image open. -/
theorem restrictTensorIso_hom_restrictAppIso_inv_tensor (M N : Y.Modules)
    (U : X.Opens) (x : Γ(M, j ''ᵁ U)) (y : Γ(N, j ''ᵁ U)) :
    (restrictTensorIso j M N).hom.app U
        (((tensor M N).restrictAppIso j U).inv (tensorSections x y)) =
      tensorSections (L := M.restrict j) (M := N.restrict j)
        ((M.restrictAppIso j U).inv x) ((N.restrictAppIso j U).inv y) := by
  let V : X.Opens := j ⁻¹ᵁ j ''ᵁ U
  let i : U ⟶ V := eqToHom (j.preimage_image_eq U).symm
  let ηM : Γ(M, j ''ᵁ U) ⟶ Γ(M.restrict j, V) :=
    ((restrictAdjunction j).unit.app M).app (j ''ᵁ U)
  let ηN : Γ(N, j ''ᵁ U) ⟶ Γ(N.restrict j, V) :=
    ((restrictAdjunction j).unit.app N).app (j ''ᵁ U)
  let ηT : Γ(tensor M N, j ''ᵁ U) ⟶ Γ((tensor M N).restrict j, V) :=
    ((restrictAdjunction j).unit.app (tensor M N)).app (j ''ᵁ U)
  let φ : (tensor M N).restrict j ⟶ tensor (M.restrict j) (N.restrict j) :=
    (restrictTensorIso j M N).hom
  have ht := congrArg (fun z : Γ((tensor M N).restrict j, U) => φ.app U z)
    (restrictAppIso_inv_eq_unit_map j (tensor M N) U (tensorSections x y)).symm
  have hn := congrArg
    (fun k : Γ((tensor M N).restrict j, V) ⟶
      Γ(tensor (M.restrict j) (N.restrict j), U) => k (ηT (tensorSections x y)))
    (φ.mapPresheaf.naturality i.op)
  have hu := congrArg
    (fun z : Γ(tensor (M.restrict j) (N.restrict j), V) =>
      (tensor (M.restrict j) (N.restrict j)).presheaf.map i.op z)
    (restrictTensorIso_hom_unit_tensor j M N x y)
  have hm := map_tensorSections i (ηM x) (ηN y)
  have he := congrArg₂
    (fun z : Γ(M.restrict j, U) => fun w : Γ(N.restrict j, U) => tensorSections z w)
    (restrictAppIso_inv_eq_unit_map j M U x)
    (restrictAppIso_inv_eq_unit_map j N U y)
  exact ht.trans (hn.trans (hu.trans (hm.trans he)))

end AlgebraicGeometry.Scheme.Modules
