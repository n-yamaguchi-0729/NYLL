/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelPresentations
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPresentation
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# Cokernels of actual native syzygy presentations

Compose generators of the twisted native syzygy with the original
kernel inclusion. The original level presentation is epimorphic, so
right exactness of tensor identifies the resulting cokernel with the
original twisted cover module. The comparison retains the original
quotient map. Compatible generators give compatible relation maps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L P : X.Modules) [L.IsQuasicoherent] [P.IsQuasicoherent]
  (N Q : X.Modules)

/-- Compose an actual twisted syzygy generator with the original kernel
inclusion to obtain a relation map into the actual closed-level source. -/
def levelSyzygyPresentation (a : ℕ) (α : P ⟶ moduleSheaf f I V a ⊗ L)
    (β : Q ⟶ levelPresentationKernel f I V L P a α ⊗ N) :
    Q ⟶ levelPullbackModule f I P a ⊗ N :=
  β ≫ (kernel.ι (levelPresentation f I V L P a α) ▷ N)

omit [P.IsQuasicoherent] in
/-- The actual relation map presents precisely the original twisted
cover module; its cokernel comparison retains the original quotient map. -/
theorem exists_levelSyzygyPresentation_cokernelIso
    (a : ℕ) (α : P ⟶ moduleSheaf f I V a ⊗ L) [Epi α]
    (β : Q ⟶ levelPresentationKernel f I V L P a α ⊗ N) [Epi β] :
    ∃ E : cokernel (levelSyzygyPresentation f I V L P N Q a α β) ≅
        (moduleSheaf f I V a ⊗ L) ⊗ N,
      cokernel.π (levelSyzygyPresentation f I V L P N Q a α β) ≫ E.hom =
        (levelPresentation f I V L P a α ▷ N) := by
  have hβ : Epi β := inferInstance
  let p := levelPresentation f I V L P a α
  have : Epi p := levelPresentation_epi f I V L P a α
  let T : X.Modules ⥤ X.Modules := tensorRight N
  have : T.IsLeftAdjoint := inferInstanceAs ((tensorRight N).IsLeftAdjoint)
  have : PreservesColimitsOfSize.{u, u} T := inferInstance
  have : T.PreservesZeroMorphisms := inferInstance
  let b : Q ⟶ T.obj (kernel p) := β
  have : Epi b := hβ
  change ∃ E : cokernel (b ≫ T.map (kernel.ι p)) ≅ T.obj (moduleSheaf f I V a ⊗ L),
    cokernel.π (b ≫ T.map (kernel.ι p)) ≫ E.hom = T.map p
  refine ⟨ProjSpace.cokernelOfMappedKernel T p b, ?_⟩
  exact ProjSpace.cokernelOfMappedKernel_projection T p b

variable (α : ∀ a : ℕ, P ⟶ moduleSheaf f I V a ⊗ L)
  (hα : ∀ a : ℕ, α (a + 1) ≫ (moduleTransition f I V a ▷ L) = α a)
  (β : ∀ a : ℕ, Q ⟶ levelPresentationKernel f I V L P a (α a) ⊗ N)
  (hβ : ∀ a : ℕ, β (a + 1) ≫
    (levelPresentationKernelTransition f I V L P α hα a ▷ N) = β a)

include hβ in
/-- Compatibility of the actual syzygy generators gives compatibility
of the original relation maps into the closed-level sources. -/
theorem levelSyzygyPresentation_transition (a : ℕ) :
    levelSyzygyPresentation f I V L P N Q (a + 1) (α (a + 1)) (β (a + 1)) ≫
        (levelPullbackTransition f I P a ▷ N) =
      levelSyzygyPresentation f I V L P N Q a (α a) (β a) := by
  let p₁ := levelPresentation f I V L P (a + 1) (α (a + 1))
  let p₀ := levelPresentation f I V L P a (α a)
  let q : kernel p₁ ⟶ kernel p₀ :=
    levelPresentationKernelTransition f I V L P α hα a
  let δ := levelPullbackTransition f I P a
  let b₁ : Q ⟶ kernel p₁ ⊗ N := β (a + 1)
  let b₀ : Q ⟶ kernel p₀ ⊗ N := β a
  have hb : b₁ ≫ (q ▷ N) = b₀ := hβ a
  have hq : q ≫ kernel.ι p₀ = kernel.ι p₁ ≫ δ :=
    levelPresentationKernelTransition_ι f I V L P α hα a
  change (b₁ ≫ (kernel.ι p₁ ▷ N)) ≫ (δ ▷ N) =
    b₀ ≫ (kernel.ι p₀ ▷ N)
  rw [Category.assoc, ← comp_whiskerRight, ← hq, comp_whiskerRight,
    ← Category.assoc, hb]

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
