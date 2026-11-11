/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.AffineTorsorTensor
public import Nyll.GaloisCohomology.GroupTheory.FiniteTorsorTrace
public import Nyll.EtaleFundamentalGroups.FiniteEtale.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.CategoryTheory.Endomorphism

/-!
# The section-ring torsor of an original affine Galois cover

The opposite deck group acts by the original pullbacks on sections. The
canonical tensor map for that action is bijective by the actual scheme
graph decomposition. Faithful flatness comes from the original finite
étale surjective covering morphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open GaloisCohomology.FiniteTorsor
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}} [ConnectedSpace X] [IsAffine X]
  (W : FiniteEtale X) [IsGalois W]

/-- An original deck transformation acts on the original section algebra. -/
def finiteEtaleSectionAlgEquiv (σ : Aut W) :
    let _ := finiteEtaleSectionAlgebra W
    Γ(W.left, ⊤) ≃ₐ[Γ(X, ⊤)] Γ(W.left, ⊤) := by
  intro sharedDefinitionOwner1
  let H := FiniteEtale.forget X ⋙ Over.forget X
  let e := (Scheme.Γ.mapIso (H.mapIso σ.asIso).op).commRingCatIsoToRingEquiv
  refine { e with commutes' := ?_ }
  intro r
  have hs : σ.asIso.hom.left ≫ W.hom = W.hom := σ.asIso.hom.w
  exact (ConcreteCategory.congr_hom
    (Scheme.Hom.comp_appTop σ.asIso.hom.left W.hom) r).symm.trans
      (congrArg (fun f : W.left ⟶ X => f.appTop r) hs)

/-- The opposite group records the contravariance of pullback, without
changing the original deck transformation or section map. -/
def finiteEtaleSectionAction :
    let _ := finiteEtaleSectionAlgebra W
    (Aut W)ᵐᵒᵖ →* (Γ(W.left, ⊤) ≃ₐ[Γ(X, ⊤)] Γ(W.left, ⊤)) := by
  intro sharedDefinitionOwner1
  refine
    { toFun := fun σ => finiteEtaleSectionAlgEquiv W σ.unop
      map_one' := ?_
      map_mul' := ?_ }
  · ext x
    exact ConcreteCategory.congr_hom (Scheme.Hom.id_appTop (X := W.left)) x
  · intro σ τ
    ext x
    exact ConcreteCategory.congr_hom
      (Scheme.Hom.comp_appTop σ.unop.asIso.hom.left τ.unop.asIso.hom.left) x

omit [ConnectedSpace X] [IsAffine X] [IsGalois W] in
theorem finiteEtaleSectionAction_apply (σ : (Aut W)ᵐᵒᵖ) (x : Γ(W.left, ⊤)) :
    let _ := finiteEtaleSectionAlgebra W
    finiteEtaleSectionAction W σ x = σ.unop.asIso.hom.left.appTop x := rfl

/-- The original section algebra of a connected finite étale cover of an
affine connected scheme is faithfully flat. -/
theorem finiteEtaleSection_faithfullyFlat :
    let _ := finiteEtaleSectionAlgebra W
    Module.FaithfullyFlat Γ(X, ⊤) Γ(W.left, ⊤) := by
  intro sharedOwner1
  have : IsFiniteEtale W.hom := W.prop
  have : ConnectedSpace W.left := FiniteEtale.connectedSpace_left_of_isConnected W
  have : IsAffine ((Functor.id Scheme).obj W.left) :=
    inferInstanceAs (IsAffine W.left)
  have : IsAffine ((Functor.fromPUnit X).obj W.right) := inferInstanceAs (IsAffine X)
  have : Nonempty ((Functor.id Scheme).obj W.left) := inferInstanceAs (Nonempty W.left)
  have : PreconnectedSpace ((Functor.fromPUnit X).obj W.right) :=
    inferInstanceAs (PreconnectedSpace X)
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine W.hom).mp
    ⟨inferInstance, IsFiniteEtale.surjective W.hom⟩

/-- Faithful flatness transports the exact characteristic to the cover's
original section ring. -/
theorem finiteEtaleSection_charP (p : ℕ) [CharP Γ(X, ⊤) p] :
    CharP Γ(W.left, ⊤) p := by
  let _ := finiteEtaleSectionAlgebra W
  have : Module.FaithfullyFlat Γ(X, ⊤) Γ(W.left, ⊤) :=
    finiteEtaleSection_faithfullyFlat W
  exact charP_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective Γ(X, ⊤) Γ(W.left, ⊤)) p

/-- The abstract torsor tensor map is exactly the native geometric tensor
equivalence, indexed by the opposite of the same deck group. -/
theorem finiteEtaleSection_tensorMap_apply
    (z : let _ := finiteEtaleSectionAlgebra W
      Γ(W.left, ⊤) ⊗[Γ(X, ⊤)] Γ(W.left, ⊤)) (σ : (Aut W)ᵐᵒᵖ) :
    let _ := finiteEtaleSectionAlgebra W
    tensorMap Γ(X, ⊤) Γ(W.left, ⊤) (finiteEtaleSectionAction W) z σ =
      finiteEtaleGaloisTensorEquiv W z σ.unop := by
  intro sharedOwner1
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact (finiteEtaleGaloisTensorEquiv_tmul W x y σ.unop).symm
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/-- No torsor comparison is assumed: bijectivity of the canonical tensor
map is supplied by the original affine Galois cover. -/
theorem finiteEtaleSection_tensorMap_bijective :
    let _ := finiteEtaleSectionAlgebra W
    Function.Bijective
      (tensorMap Γ(X, ⊤) Γ(W.left, ⊤) (finiteEtaleSectionAction W)) := by
  intro sharedOwner1
  constructor
  · intro a b hab
    apply (finiteEtaleGaloisTensorEquiv W).injective
    funext σ
    exact (finiteEtaleSection_tensorMap_apply W a (MulOpposite.op σ)).symm.trans
      ((congrFun hab (MulOpposite.op σ)).trans
        (finiteEtaleSection_tensorMap_apply W b (MulOpposite.op σ)))
  · intro f
    obtain ⟨z, hz⟩ := (finiteEtaleGaloisTensorEquiv W).surjective
      (fun σ => f (MulOpposite.op σ))
    refine ⟨z, funext fun σ => ?_⟩
    exact (finiteEtaleSection_tensorMap_apply W z σ).trans (congrFun hz σ.unop)

end EtaleFundamentalGroups
