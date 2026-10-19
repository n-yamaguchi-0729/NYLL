/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Native module-sheaf isomorphisms on Čech cohomology

The original component maps of a native sheaf isomorphism give inverse
maps on cochains. Their already constructed maps on kernels and quotient
cohomology are inverse as well. Thus the comparison on cohomology uses
the original section maps, including when the native isomorphism is a
tensor associator or a multiplication of twisting powers.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsSeparated f] (K : X.OrderedAffineCover)
  {M N : X.Modules} (e : M ≅ N)

/-- The actual native component maps identify the two original cochain
modules. Both inverse identities are checked on original sections. -/
def cochainEquivOfIso (q : ℕ) :
    (toOModulePresheaf f M).cochain K q ≃ₗ[R]
      (toOModulePresheaf f N).cochain K q :=
  { (toOModulePresheafHom f e.hom).toAffHom.cochainMap K q with
    invFun := (toOModulePresheafHom f e.inv).toAffHom.cochainMap K q
    left_inv x := by
      funext s
      exact congrArg (fun a : M ⟶ M => a.app (K.inter s) (x s)) e.hom_inv_id
    right_inv y := by
      funext s
      exact congrArg (fun a : N ⟶ N => a.app (K.inter s) (y s)) e.inv_hom_id }

/-- The cochain equivalence is the original component of the native
sheaf isomorphism on each actual cover intersection. -/
theorem cochainEquivOfIso_apply (q : ℕ)
    (x : (toOModulePresheaf f M).cochain K q) (s : K.Idx q) :
    cochainEquivOfIso f K e q x s = e.hom.app (K.inter s) (x s) := rfl

/-- The actual induced maps on quotient cohomology are inverse.
No separately chosen comparison of cohomology groups is used. -/
def HSuccEquivOfIso (q : ℕ) :
    (toOModulePresheaf f M).HSucc K q ≃ₗ[R]
      (toOModulePresheaf f N).HSucc K q :=
  { (toOModulePresheafHom f e.hom).toAffHom.HSuccMap K q with
    invFun := (toOModulePresheafHom f e.inv).toAffHom.HSuccMap K q
    left_inv x := by
      refine Submodule.Quotient.induction_on _ x ?_
      intro z
      refine (congrArg ((toOModulePresheafHom f e.inv).toAffHom.HSuccMap K q)
        ((toOModulePresheafHom f e.hom).toAffHom.HSuccMap_mk K q z)).trans ?_
      refine ((toOModulePresheafHom f e.inv).toAffHom.HSuccMap_mk K q
        ((toOModulePresheafHom f e.hom).toAffHom.kerMap K (q + 1) z)).trans ?_
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (cochainEquivOfIso f K e (q + 1)).symm_apply_apply z.val
    right_inv y := by
      refine Submodule.Quotient.induction_on _ y ?_
      intro z
      refine (congrArg ((toOModulePresheafHom f e.hom).toAffHom.HSuccMap K q)
        ((toOModulePresheafHom f e.inv).toAffHom.HSuccMap_mk K q z)).trans ?_
      refine ((toOModulePresheafHom f e.hom).toAffHom.HSuccMap_mk K q
        ((toOModulePresheafHom f e.inv).toAffHom.kerMap K (q + 1) z)).trans ?_
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      exact (cochainEquivOfIso f K e (q + 1)).apply_symm_apply z.val }

/-- The cohomology equivalence retains the existing map on every
actual cocycle class. -/
theorem HSuccEquivOfIso_apply_mk (q : ℕ)
    (z : LinearMap.ker ((toOModulePresheaf f M).d K (q + 1))) :
    HSuccEquivOfIso f K e q (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        ((toOModulePresheafHom f e.hom).toAffHom.kerMap K (q + 1) z) := rfl

include e in
/-- Vanishing transfers along a native module-sheaf isomorphism by its
actual induced cohomology map. -/
theorem subsingleton_HSucc_of_iso (q : ℕ)
    [Subsingleton ((toOModulePresheaf f M).HSucc K q)] :
    Subsingleton ((toOModulePresheaf f N).HSucc K q) :=
  ⟨fun x y => (HSuccEquivOfIso f K e q).symm.injective
    (Subsingleton.elim ((HSuccEquivOfIso f K e q).symm x)
      ((HSuccEquivOfIso f K e q).symm y))⟩

end AlgebraicGeometry.Scheme.Modules
