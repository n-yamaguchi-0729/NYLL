/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionCounit
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Cokernels of relations lifted through the original closed quotient

The left triangle identity and the actual closed-immersion counit
show that the pullback of the original quotient unit is invertible.
Monoidal naturality gives the same result after tensoring that unit
with any ambient module.

A relation lifted through this tensor of the original quotient unit
induces the original categorical map of cokernels. Pullback of that
map is an isomorphism, by preservation of cokernels and naturality
of their comparison maps. The construction retains the actual
cokernel projections.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pulling the original quotient unit back to the closed subscheme
gives an isomorphism for every quasicoherent ambient module. -/
theorem isIso_pullback_map_unit_of_isClosedImmersion [IsClosedImmersion f]
    (M : Y.Modules) [M.IsQuasicoherent] :
    IsIso ((pullback f).map ((pullbackPushforwardAdjunction f).unit.app M)) := by
  let adj : pullback f ⊣ pushforward f := pullbackPushforwardAdjunction f
  let N : X.Modules := (pullback f).obj M
  have : N.IsQuasicoherent := isQuasicoherent_pullback f M
  let ε : (pullback f).obj ((pushforward f).obj N) ⟶ N := adj.counit.app N
  have : IsIso ε := isIso_pullbackCounit_of_isClosedImmersion f N
  have h : (pullback f).map (adj.unit.app M) ≫ ε = 𝟙 N :=
    adj.left_triangle_components M
  exact IsIso.of_isIso_fac_right h

/-- The pullback of the original quotient unit tensored on the right
is invertible; the tensor factor need not be locally free. -/
theorem isIso_pullback_map_unit_whiskerRight_of_isClosedImmersion
    [IsClosedImmersion f] (M L : Y.Modules) [M.IsQuasicoherent] :
    IsIso ((pullback f).map ((pullbackPushforwardAdjunction f).unit.app M ▷ L)) := by
  let F : Y.Modules ⥤ X.Modules := pullback f
  let Q : Y.Modules := (pushforward f).obj (F.obj M)
  let η : M ⟶ Q := (pullbackPushforwardAdjunction f).unit.app M
  have : IsIso (F.map η) := isIso_pullback_map_unit_of_isClosedImmersion f M
  have h : F.map η ▷ F.obj L ≫ Functor.LaxMonoidal.μ F Q L =
      Functor.LaxMonoidal.μ F M L ≫ F.map (η ▷ L) :=
    Functor.LaxMonoidal.μ_natural_left F η L
  exact IsIso.of_isIso_fac_left h.symm

variable {P M : Y.Modules} (L : Y.Modules) (φ : P ⟶ M ⊗ L)
  (β : P ⟶ (pushforward f).obj ((pullback f).obj M) ⊗ L)
  (hφ : φ ≫ ((pullbackPushforwardAdjunction f).unit.app M ▷ L) = β)

/-- The original map of cokernels induced by a relation lifted
through the tensor of the actual closed quotient unit. -/
def pullbackQuotientCokernelMap : cokernel φ ⟶ cokernel β :=
  cokernel.map φ β (𝟙 P) ((pullbackPushforwardAdjunction f).unit.app M ▷ L)
    (hφ.trans (Category.id_comp β).symm)

/-- The constructed map retains the original quotient unit and
the original projections of both cokernels. -/
theorem cokernel_π_pullbackQuotientCokernelMap :
    cokernel.π φ ≫ pullbackQuotientCokernelMap f L φ β hφ =
      ((pullbackPushforwardAdjunction f).unit.app M ▷ L) ≫ cokernel.π β :=
  cokernel.π_desc φ _ _

/-- The pullback of the actual induced map of cokernels is an
isomorphism for a closed immersion and a quasicoherent coefficient module. -/
theorem isIso_pullback_map_pullbackQuotientCokernelMap [IsClosedImmersion f]
    [M.IsQuasicoherent] :
    IsIso ((pullback f).map (pullbackQuotientCokernelMap f L φ β hφ)) := by
  let F : Y.Modules ⥤ X.Modules := pullback f
  let τ : M ⊗ L ⟶ (pushforward f).obj (F.obj M) ⊗ L :=
    (pullbackPushforwardAdjunction f).unit.app M ▷ L
  have : IsIso (F.map τ) :=
    isIso_pullback_map_unit_whiskerRight_of_isClosedImmersion f M L
  have w : φ ≫ τ = (𝟙 P) ≫ β := hφ.trans (Category.id_comp β).symm
  have wF : F.map φ ≫ F.map τ = F.map (𝟙 P) ≫ F.map β :=
    (F.map_comp φ τ).symm.trans ((congrArg F.map w).trans (F.map_comp (𝟙 P) β))
  let c : cokernel (F.map φ) ⟶ cokernel (F.map β) :=
    cokernel.map (F.map φ) (F.map β) (F.map (𝟙 P)) (F.map τ) wF
  have : IsIso c := inferInstance
  have h : (PreservesCokernel.iso F φ).hom ≫ c =
      F.map (pullbackQuotientCokernelMap f L φ β hφ) ≫
        (PreservesCokernel.iso F β).hom :=
    preserves_cokernel_iso_comp_cokernel_map F φ β (𝟙 P) τ w
  exact IsIso.of_isIso_fac_right h.symm

end AlgebraicGeometry.Scheme.Modules
