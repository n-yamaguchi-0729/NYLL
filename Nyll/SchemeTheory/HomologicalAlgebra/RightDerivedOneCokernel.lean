/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.Homology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The first right derived functor from an injective presentation

A left exact additive functor computes its first derived object as the
cokernel of the map from the injective object to the quotient in the
canonical injective presentation. The proof uses the actual injective
resolution and its kernel, not a supplied derived-functor comparison.
-/

noncomputable section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- The first right derived object is the cokernel obtained from the
canonical injective presentation. -/
def Functor.rightDerivedOneCokernelIso (X : C) :
    (F.rightDerived 1).obj X ≅ cokernel (F.map (cokernel.π (Injective.ι X))) := by
  let K := InjectiveResolution.ofCocomplex X
  let Q := cokernel (Injective.ι X)
  let p : K.X 0 ⟶ Q := cokernel.π (Injective.ι X)
  let i : Q ⟶ K.X 1 := Injective.ι Q
  have hp : Epi p := by
    change Epi (cokernel.π (Injective.ι X))
    infer_instance
  have hiMono : Mono i := by
    change Mono (Injective.ι Q)
    infer_instance
  have hd : K.d 0 1 = p ≫ i := InjectiveResolution.ofCocomplex_d_0_1 X
  have wi : i ≫ K.d 1 2 = 0 := by
    apply (cancel_epi p).mp
    rw [← Category.assoc, ← hd, K.d_comp_d, comp_zero]
  let T₀ := ShortComplex.mk (K.d 0 1) (K.d 1 2) (K.d_comp_d 0 1 2)
  let T := ShortComplex.mk i (K.d 1 2) wi
  let φ : T₀ ⟶ T :=
    { τ₁ := p
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by
        change p ≫ i = K.d 0 1 ≫ 𝟙 _
        rw [Category.comp_id, hd]
      comm₂₃ := by rw [Category.id_comp, Category.comp_id] }
  have hprev : (ComplexShape.up ℕ).prev 1 = 0 :=
    (ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
  have hnext : (ComplexShape.up ℕ).next 1 = 2 :=
    (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 1 2 from rfl)
  have hT₀ : T₀.Exact :=
    (HomologicalComplex.exactAt_iff' K 0 1 2 hprev hnext).mp
      (InjectiveResolution.ofCocomplex_exactAt_succ X 0)
  have : Epi φ.τ₁ := hp
  have : IsIso φ.τ₂ := by change IsIso (𝟙 (K.X 1)); infer_instance
  have : Mono φ.τ₃ := by change Mono (𝟙 (K.X 2)); infer_instance
  have : Mono T.f := hiMono
  have hT : T.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hT₀
  let S := ShortComplex.mk (F.map (K.d 0 1)) (F.map (K.d 1 2))
    (by rw [← F.map_comp, K.d_comp_d, F.map_zero])
  have w : F.map i ≫ F.map (K.d 1 2) = 0 := by
    rw [← F.map_comp, wi, F.map_zero]
  let hi : IsLimit (KernelFork.ofι (F.map i) w) :=
    KernelFork.mapIsLimit (KernelFork.ofι i wi) hT.fIsKernel F
  have hlift : hi.lift (KernelFork.ofι S.f S.zero) = F.map p := by
    apply (cancel_mono (F.map i)).mp
    calc
      hi.lift (KernelFork.ofι S.f S.zero) ≫ F.map i = S.f :=
        hi.fac _ WalkingParallelPair.zero
      _ = F.map p ≫ F.map i := by
        change F.map (K.d 0 1) = _
        rw [hd, F.map_comp]
  let h : S.LeftHomologyData :=
    { K := F.obj Q
      H := cokernel (F.map p)
      i := F.map i
      π := cokernel.π (F.map p)
      wi := w
      hi := hi
      wπ := by rw [hlift]; exact cokernel.condition (F.map p)
      hπ := by
        apply CokernelCofork.IsColimit.ofπ'
        intro Z k hk
        have hk' : F.map p ≫ k = 0 := by
          rw [← hlift]
          exact hk
        exact ⟨cokernel.desc (F.map p) k hk', cokernel.π_desc _ _ _⟩ }
  let I := InjectiveResolution.of X
  have hI : I.cocomplex = K := by
    change (InjectiveResolution.of X).cocomplex = InjectiveResolution.ofCocomplex X
    rw [InjectiveResolution.of_def]
  let e := I.isoRightDerivedObj F 1
  refine e ≪≫ ?_
  rw [hI]
  let L := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  exact L.homologyIsoSc' 0 1 2 hprev hnext ≪≫ h.homologyIso

end CategoryTheory
