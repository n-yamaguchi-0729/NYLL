/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.Sections.AffineEpi
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.RingTheory.LinearAlgebra.NilpotentSurjectivity
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.RingTheory.Ideal.Operations

/-!
# Actual generating sections lifted through nilpotent quotients

An original sheaf morphism is epimorphic if its section maps on all
affine opens are surjective; separatedness proves the required global
cancellation directly. Applying the nilpotent linear-map criterion on
these affine opens detects epimorphisms through a nilpotent quotient.

Consequently, actual lifts of the generating sections of the quotient
generate the original sheaf. The construction keeps the same index
type and the original lifted sections. It does not assume or assert
the existence of the lifts: that separate obstruction is handled by
the actual first-cohomology calculation. The local kernel and power
annihilation inputs are precisely the affine properties supplied by
the constructed adic cover sheaves.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Surjectivity on the original sections of all affine opens
implies the actual native sheaf morphism is epimorphic. -/
theorem Hom.epi_of_surjective_affine_app {X : Scheme.{u}} {P M : X.Modules}
    (ψ : P ⟶ M)
    (hψ : ∀ (U : X.Opens), IsAffineOpen U → Function.Surjective (ψ.app U)) : Epi ψ := by
  constructor
  intro T α β h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let B : Type u := { V : X.affineOpens // V.val ≤ W.unop }
  let U : B → X.Opens := fun i => i.val.val
  have hcover : W.unop ≤ ⨆ i, U i := by
    intro z hz
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hz W.unop.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hzV⟩
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible T U W.unop
    (fun i => i.property) hcover).1
  intro i
  let r : U i ⟶ W.unop := homOfLE i.property
  obtain ⟨y, hy⟩ := hψ (U i) i.val.property (M.presheaf.map r.op x)
  have he : α.app (U i) (ψ.app (U i) y) = β.app (U i) (ψ.app (U i) y) :=
    congrArg (fun v : P ⟶ T => v.app (U i) y) h
  have hsmall : α.app (U i) (M.presheaf.map r.op x) =
      β.app (U i) (M.presheaf.map r.op x) :=
    (congrArg (fun z => α.app (U i) z) hy).symm.trans
      (he.trans (congrArg (fun z => β.app (U i) z) hy))
  exact (PresheafOfModules.naturality_apply α.val r.op x).symm.trans
    (hsmall.trans (PresheafOfModules.naturality_apply β.val r.op x))

/-- The original native morphism is epimorphic when its composite
with a nilpotent quotient is epimorphic. The nilpotence is needed
only on the actual middle section modules, not on the coefficient rings. -/
theorem Hom.epi_of_nilpotent_quotient {X : Scheme.{u}} {P M N : X.Modules}
    [P.IsQuasicoherent] [N.IsQuasicoherent] (ψ : P ⟶ M) (q : M ⟶ N) [Epi (ψ ≫ q)]
    (J : (U : X.Opens) → Ideal Γ(X, U)) (e : ℕ)
    (hker : ∀ (U : X.Opens), IsAffineOpen U →
      ((q.val.app (op U)).hom).ker ≤ J U • (⊤ : Submodule Γ(X, U) Γ(M, U)))
    (hpow : ∀ (U : X.Opens), IsAffineOpen U →
      (J U) ^ e • (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥) : Epi ψ := by
  apply Hom.epi_of_surjective_affine_app ψ
  intro U hU
  let ψU : Γ(P, U) →ₗ[Γ(X, U)] Γ(M, U) := (ψ.val.app (op U)).hom
  let qU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := (q.val.app (op U)).hom
  have hcomp : Function.Surjective (qU.comp ψU) :=
    Hom.app_surjective_of_epi_of_isAffineOpen (ψ ≫ q) U hU
  exact LinearMap.surjective_of_comp_surjective_of_ker_le_smul_of_pow_smul_eq_bot
    ψU qU (J U) e hcomp (hker U hU) (hpow U hU)

variable {X : Scheme.{u}} {M N : X.Modules} [N.IsQuasicoherent]
  (q : M ⟶ N) (J : (U : X.Opens) → Ideal Γ(X, U)) (e : ℕ)
  (hker : ∀ (U : X.Opens), IsAffineOpen U →
    ((q.val.app (op U)).hom).ker ≤ J U • (⊤ : Submodule Γ(X, U) Γ(M, U)))
  (hpow : ∀ (U : X.Opens), IsAffineOpen U →
    (J U) ^ e • (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥)
  (G : N.GeneratingSections) (s : G.I → M.sections)
  (hs : ∀ i : G.I,
    SheafOfModules.sectionsMap ((sheafOfModulesEquivalence X).functor.map q) (s i) = G.s i)

/-- Construct generating sections from the actual lifts through the
nilpotent quotient, retaining the original index type and sections. -/
def generatingSectionsOfNilpotentQuotient : M.GeneratingSections := by
  let E : X.Modules ≌ SheafOfModules.{u} X.ringCatSheaf := sheafOfModulesEquivalence X
  let P : X.Modules := SheafOfModules.free G.I
  let p : (SheafOfModules.free G.I) ⟶ (show SheafOfModules.{u} X.ringCatSheaf from M) :=
    M.freeHomEquiv.symm s
  let ψ : P ⟶ M := E.inverse.map p
  have : P.IsQuasicoherent := inferInstance
  have hfacNative : p ≫ E.functor.map q = G.π := by
    have he := SheafOfModules.freeHomEquiv_symm_comp s (E.functor.map q)
    exact he.trans (congrArg N.freeHomEquiv.symm (funext hs))
  have hfac : ψ ≫ q = E.inverse.map G.π := E.inverse.congr_map hfacNative
  have : Epi G.π := G.epi
  have hG' : Epi (E.inverse.map G.π) := CategoryTheory.Functor.map_epi E.inverse G.π
  have : Epi (ψ ≫ q) :=
    Eq.mp (congrArg (fun v : P ⟶ N => Epi (C := X.Modules) v) hfac.symm) hG'
  have : Epi ψ := Hom.epi_of_nilpotent_quotient ψ q J e hker hpow
  have hp : Epi p := CategoryTheory.Functor.map_epi E.functor ψ
  exact { I := G.I, s := s, epi := hp }

/-- The construction uses exactly the prescribed lifted sections. -/
theorem generatingSectionsOfNilpotentQuotient_sections (i : G.I) :
    (generatingSectionsOfNilpotentQuotient q J e hker hpow G s hs).s i = s i := rfl

/-- A finite original generating family keeps its finite index type
after lifting through the nilpotent quotient. -/
theorem generatingSectionsOfNilpotentQuotient_isFiniteType [G.IsFiniteType] :
    (generatingSectionsOfNilpotentQuotient q J e hker hpow G s hs).IsFiniteType :=
  ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)⟩

end AlgebraicGeometry.Scheme.Modules
