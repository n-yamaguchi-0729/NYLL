/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelPresentations
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeKernel
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentKernelGlobal
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.QuasicoherentTensor
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Native syzygies of the original closed-level presentations

Take the actual categorical kernels of the presentations whose sources
are the modules on the original thickenings. Quasicoherence and finite
type follow from the original kernel inclusion. The proved presentation
squares construct transitions between these same kernels and retain
their inclusions into the original quotient modules.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L P : X.Modules) [L.IsQuasicoherent] [P.IsQuasicoherent]

/-- The actual kernel of the original closed-level presentation. -/
def levelPresentationKernel (n : ℕ) (α : P ⟶ moduleSheaf f I V n ⊗ L) : X.Modules :=
  kernel (levelPresentation f I V L P n α)

instance levelPresentationKernel_isQuasicoherent
    (n : ℕ) (α : P ⟶ moduleSheaf f I V n ⊗ L) :
    (levelPresentationKernel f I V L P n α).IsQuasicoherent := by
  have : (moduleSheaf f I V n ⊗ L).IsQuasicoherent :=
    isQuasicoherent_tensor (moduleSheaf f I V n) L
  exact isQuasicoherent_kernel (levelPresentation f I V L P n α)

/-- The native kernel inclusion supplies finite type over a locally
Noetherian scheme when the original ambient source has finite type. -/
theorem levelPresentationKernel_isFiniteType [IsLocallyNoetherian X] [P.IsFiniteType]
    (n : ℕ) (α : P ⟶ moduleSheaf f I V n ⊗ L) :
    (levelPresentationKernel f I V L P n α).IsFiniteType := by
  let Q : X.Modules := levelPullbackModule f I P n
  let K : X.Modules := levelPresentationKernel f I V L P n α
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  let κ : K ⟶ Q := kernel.ι (levelPresentation f I V L P n α)
  have : Mono κ := inferInstanceAs (Mono (kernel.ι (levelPresentation f I V L P n α)))
  have : (E.functor.obj K).IsQuasicoherent :=
    levelPresentationKernel_isQuasicoherent f I V L P n α
  have : (E.functor.obj Q).IsQuasicoherent := levelPullbackModule_isQuasicoherent f I P n
  have : (E.functor.obj Q).IsFiniteType := levelPullbackModule_isFiniteType f I P n
  have : Mono (E.functor.map κ) := CategoryTheory.Functor.map_mono E.functor κ
  exact SheafOfModules.isFiniteType_of_mono_on_locallyNoetherian
    (X := X) (M := E.functor.obj K) (N := E.functor.obj Q) (E.functor.map κ)

variable (α : ∀ n : ℕ, P ⟶ moduleSheaf f I V n ⊗ L)
  (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L) = α n)

/-- The actual presenting square induces a transition of its native kernels. -/
def levelPresentationKernelTransition (n : ℕ) :
    levelPresentationKernel f I V L P (n + 1) (α (n + 1)) ⟶
      levelPresentationKernel f I V L P n (α n) :=
  kernel.map (levelPresentation f I V L P (n + 1) (α (n + 1)))
    (levelPresentation f I V L P n (α n)) (levelPullbackTransition f I P n)
    (moduleTransition f I V n ▷ L) (levelPresentation_transition f I V L P α hα n)

/-- The kernel transition retains the original inclusions and the original
transition of the closed-level quotient modules. -/
theorem levelPresentationKernelTransition_ι (n : ℕ) :
    levelPresentationKernelTransition f I V L P α hα n ≫
        kernel.ι (levelPresentation f I V L P n (α n)) =
      kernel.ι (levelPresentation f I V L P (n + 1) (α (n + 1))) ≫
        levelPullbackTransition f I P n :=
  kernel.lift_ι _ _ _

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
