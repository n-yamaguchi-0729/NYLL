/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafH0
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.AffineExactSequenceSections
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafAffSES
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual global-section lifts from vanishing of the kernel's first cohomology

The original short exact sequence gives a short exact sequence on affine
sections. Vanishing of the original first Čech cohomology of its kernel
corrects local lifts to a compatible family. The actual augmentation and
gluing equivalences then yield a global preimage under the original
sheaf morphism, rather than under a separately chosen section map.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsSeparated f] (K : X.OrderedAffineCover)
  (S : ShortComplex X.Modules)
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₂]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₃]

/-- Every original quotient section has an original global lift when the actual first
Čech cohomology of the kernel vanishes. -/
theorem globalSections_surjective_of_shortExact_of_subsingleton_H1
    (hS : S.ShortExact)
    [Subsingleton ((toOModulePresheaf f S.X₁).HSucc K 0)] :
    Function.Surjective (S.g.app ⊤) := by
  let T := toOModulePresheafAffSES f S hS
  let e₂ := globalSectionsCechH0Equiv f S.X₂ K
  let e₃ := globalSectionsCechH0Equiv f S.X₃ K
  have hproj : Function.Surjective (T.proj.H0Map K) :=
    T.H0Map_proj_surjective_of_subsingleton_H1 K
  intro z
  obtain ⟨c, hc⟩ := hproj (e₃ z)
  let y : sectionModuleOverBase f S.X₂ ⊤ := e₂.symm c
  refine ⟨y, ?_⟩
  have hnat := globalSectionsCechH0Equiv_naturality f S.g K y
  have he : e₃ (S.g.app ⊤ y) = e₃ z := by
    calc
      e₃ (S.g.app ⊤ y) = T.proj.H0Map K (e₂ y) := hnat.symm
      _ = T.proj.H0Map K c := congrArg (T.proj.H0Map K) (e₂.apply_symm_apply c)
      _ = e₃ z := hc
  exact e₃.injective he

end AlgebraicGeometry.Scheme.Modules
