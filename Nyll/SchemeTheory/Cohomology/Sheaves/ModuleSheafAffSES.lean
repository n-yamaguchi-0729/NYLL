/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Modules.Exactness
import Nyll.SchemeTheory.Modules.LocalMorphisms
import Nyll.SchemeTheory.Modules.Sections.AffineEpi
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Actual affine short exact sequences from native module sheaves

A native short exact sequence, with quasicoherent middle and right terms,
gives the short exact sequence on affine sections required by the existing
Čech constructions. The maps are precisely the original section maps.

Injectivity and lifting of kernel sections come from the native sheaf
kernel. Surjectivity on affine opens comes from the actual tilde--Gamma
comparison for quasicoherent epimorphisms. Surjectivity on nonaffine opens
is not an input or a conclusion.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The original native maps form an actual short exact sequence on all
affine-open section modules used in the Čech complex. -/
def toOModulePresheafAffSES (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    OModulePresheaf.AffSES (toOModulePresheaf f S.X₁)
      (toOModulePresheaf f S.X₂) (toOModulePresheaf f S.X₃) := by
  have hmono : Mono S.f := hS.mono_f
  have hepi : Epi S.g := hS.epi_g
  refine
    { inc := (toOModulePresheafHom f S.f).toAffHom
      proj := (toOModulePresheafHom f S.g).toAffHom
      injective := ?_
      surjective := ?_
      exact := ?_ }
  · intro U
    exact (Hom.mono_iff_injective S.f).mp hmono U.1
  · intro U
    exact Hom.app_surjective_of_epi_of_isAffineOpen S.g U.1 U.2
  · intro U
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hx
      let a : Γ(S.X₁, U.1) := y
      let b : Γ(S.X₂, U.1) := x
      have hy' : S.f.app U.1 a = b := hy
      have hz : S.f.app U.1 ≫ S.g.app U.1 = 0 := by
        rw [← Hom.comp_app, S.zero, Hom.zero_app]
      have ha : S.g.app U.1 (S.f.app U.1 a) = 0 :=
        congrArg (fun k : Γ(S.X₁, U.1) ⟶ Γ(S.X₃, U.1) => k a) hz
      change S.g.app U.1 b = 0
      exact (congrArg (fun z : Γ(S.X₂, U.1) => S.g.app U.1 z) hy').symm.trans ha
    · intro x hx
      let b : Γ(S.X₂, U.1) := x
      have hx' : S.g.app U.1 b = 0 := hx
      obtain ⟨y, hy⟩ := exists_app_eq_of_exact_of_app_eq_zero S hS.exact U.1 b hx'
      exact LinearMap.mem_range.mpr ⟨y, hy⟩

end AlgebraicGeometry.Scheme.Modules
