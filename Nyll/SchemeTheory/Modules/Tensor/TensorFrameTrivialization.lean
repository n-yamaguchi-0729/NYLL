/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeRestriction
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorSections
import Nyll.SchemeTheory.Modules.Tensor.TensorWithFrame
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# The native slice isomorphism defined by a tensor frame

A section of the second factor defines a native morphism after restriction
to any open in its domain. When the section is a frame there, the actual
section bijections form an isomorphism. This retains the precise tensor
section map and transports quasicoherence and finite type to the twist.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules) {L : X.Modules} {U W : X.Opens}

/-- Tensoring with a local section defines an actual morphism on the slice
site of every open contained in its domain. -/
def tensorSectionHomOver (s : Γ(L, U)) (hWU : W ≤ U) :
    F.over W ⟶ (F ⊗ L).over W :=
  ⟨{ app := fun Z => by
       change ModuleCat.of Γ(X, Z.unop.left) Γ(F, Z.unop.left) ⟶
         ModuleCat.of Γ(X, Z.unop.left) Γ(F ⊗ L, Z.unop.left)
       exact ModuleCat.ofHom
         { toFun := fun m => Modules.tensorSections m
             (L.presheaf.map (homOfLE (Z.unop.hom.le.trans hWU)).op s)
           map_add' := fun m m' => tensorSections_add_left m m' _
           map_smul' := fun r m => tensorSections_smul_left r m _ }
     naturality := fun {Z Z'} f => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro m
       let m' : Γ(F, Z.unop.left) := m
       have hmap := map_tensorSections f.unop.left m'
         (L.presheaf.map (homOfLE (Z.unop.hom.le.trans hWU)).op s)
       have hres : L.presheaf.map f.unop.left.op
           (L.presheaf.map (homOfLE (Z.unop.hom.le.trans hWU)).op s) =
         L.presheaf.map (homOfLE (Z'.unop.hom.le.trans hWU)).op s := by
         change (L.presheaf.map (homOfLE (Z.unop.hom.le.trans hWU)).op ≫
           L.presheaf.map f.unop.left.op) s = _
         rw [← Functor.map_comp]
         rfl
       exact (congrArg (Modules.tensorSections (F.presheaf.map f.unop.left.op m'))
         hres).symm.trans hmap.symm }⟩

/-- The component of the slice morphism is the original tensor-section map. -/
theorem tensorSectionHomOver_app (s : Γ(L, U)) (hWU : W ≤ U)
    (Z : Over W) (m : Γ(F, Z.left)) :
    ((tensorSectionHomOver F s hWU).val.app (op Z)).hom m =
      Modules.tensorSections m
        (L.presheaf.map (homOfLE (Z.hom.le.trans hWU)).op s) := rfl

/-- The tensor-section morphism for a local frame is an actual isomorphism
on the native slice site. -/
def tensorFrameIsoOver {s : Γ(L, U)} (hs : IsFrameOn s W) (hWU : W ≤ U) :
    F.over W ≅ (F ⊗ L).over W := by
  let φ : F.over W ⟶ (F ⊗ L).over W := tensorSectionHomOver F s hWU
  let e : ∀ Z : (Over W)ᵒᵖ, (F.over W).val.obj Z ≅ ((F ⊗ L).over W).val.obj Z :=
    fun Z => (LinearEquiv.ofBijective (φ.val.app Z).hom
      (hs.bijective_tensorSections F (Z.unop.hom.le.trans hWU) Z.unop.hom.le)).toModuleIso
  let eP : (F.over W).val ≅ ((F ⊗ L).over W).val :=
    PresheafOfModules.isoMk e (fun {Z Z'} f => φ.val.naturality f)
  exact (SheafOfModules.fullyFaithfulForget (X.ringCatSheaf.over W)).preimageIso eP

/-- The local trivialization sends each section to its tensor with the frame. -/
theorem tensorFrameIsoOver_hom_app {s : Γ(L, U)} (hs : IsFrameOn s W) (hWU : W ≤ U)
    (Z : Over W) (m : Γ(F, Z.left)) :
    ((tensorFrameIsoOver F hs hWU).hom.val.app (op Z)).hom m =
      Modules.tensorSections m
        (L.presheaf.map (homOfLE (Z.hom.le.trans hWU)).op s) := rfl

/-- A tensor frame preserves quasicoherence on its actual native slice. -/
theorem IsFrameOn.isQuasicoherent_tensor_over
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F]
    {s : Γ(L, U)} (hs : IsFrameOn s W) (hWU : W ≤ U) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf.over W) ((F ⊗ L).over W) :=
  (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over W)).prop_of_iso
    (tensorFrameIsoOver F hs hWU) (SheafOfModules.isQuasicoherent_over F W)

/-- A tensor frame preserves finite type on its actual native slice. -/
theorem IsFrameOn.isFiniteType_tensor_over
    [hF : SheafOfModules.IsFiniteType (R := X.ringCatSheaf) F]
    {s : Γ(L, U)} (hs : IsFrameOn s W) (hWU : W ≤ U) :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf.over W) ((F ⊗ L).over W) :=
  SheafOfModules.IsFiniteType.of_iso (R := X.ringCatSheaf.over W)
    (M := F.over W) (N := (F ⊗ L).over W) (tensorFrameIsoOver F hs hWU)
    (SheafOfModules.IsFiniteType.over (R := X.ringCatSheaf) F W hF)

end AlgebraicGeometry.Scheme.Modules
