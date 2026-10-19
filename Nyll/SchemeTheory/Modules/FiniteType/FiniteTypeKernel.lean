/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentImage
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite type of actual kernels on locally Noetherian schemes

An actual monomorphism embeds every affine section module into the finite
section module of its target. Noetherianity of the affine coefficient ring
then gives finite generation of the source sections. Quasicoherence turns
these actual finite sections into native local generators. In particular,
the categorical kernel of a morphism of quasicoherent sheaves is of finite
type whenever its source is of finite type.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace SheafOfModules

/-- A quasicoherent subsheaf of a finite-type quasicoherent sheaf on a
locally Noetherian scheme is of finite type. The local generators are
obtained from the actual injective maps on affine sections. -/
theorem isFiniteType_of_mono_on_locallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : SheafOfModules.{u} X.ringCatSheaf}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]
    (f : M ⟶ N) [Mono f] : M.IsFiniteType := by
  let M' : X.Modules := M
  let N' : X.Modules := N
  let f' : M' ⟶ N' := (Scheme.Modules.sheafOfModulesEquivalence X).inverse.map f
  have : Mono f' := Functor.map_mono (Scheme.Modules.sheafOfModulesEquivalence X).inverse f
  apply Scheme.Modules.isFiniteType_of_finite_affine_sections M'
  intro U hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(X, U) Γ(N', U) :=
    Scheme.Modules.moduleFinite_sections_of_isFiniteType N' U hU
  let l : Γ(M', U) →ₗ[Γ(X, U)] Γ(N', U) := (f'.val.app (op U)).hom
  exact Module.Finite.of_injective l
    ((Scheme.Modules.Hom.mono_iff_injective f').mp inferInstance U)

/-- The native categorical kernel has finite type when the source has
finite type and both terms are quasicoherent on a locally Noetherian
scheme. No finite presentation of the kernel is assumed. -/
theorem isFiniteType_kernel_on_locallyNoetherian
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : SheafOfModules.{u} X.ringCatSheaf}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [M.IsFiniteType]
    (f : M ⟶ N) : (kernel f).IsFiniteType := by
  have : (kernel f).IsQuasicoherent := isQuasicoherent_kernel_native f
  exact isFiniteType_of_mono_on_locallyNoetherian (kernel.ι f)

end SheafOfModules
