/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GaloisCovers.SelfProduct
public import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteLimits
public import Nyll.SchemeTheory.FiniteEtale.Forget.FiniteCoproducts
public import Nyll.SchemeTheory.Pi1.Affine.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# The canonical tensor map of an affine Galois cover

The established graph decomposition of a Galois object is transported to
the literal scheme fiber product. Global sections identify that diagram
with the canonical torsor tensor map, retaining its deck coordinates.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- Sections of a coproduct are the product of the component section rings. -/
def sectionsSigmaIso {I : Type u} (Y : I → Scheme.{u}) :
    Scheme.Γ.obj (op (∐ Y)) ≅
      CommRingCat.of (∀ i, Scheme.Γ.obj (op (Y i))) :=
  Scheme.Γ.mapIso (opCoproductIsoProduct Y) ≪≫
    PreservesProduct.iso Scheme.Γ (fun i => op (Y i)) ≪≫
      CommRingCat.piIsoPi (fun i => Scheme.Γ.obj (op (Y i)))

private theorem sectionsSigmaIso_apply {I : Type u} (Y : I → Scheme.{u})
    (a : Γ(∐ Y, ⊤)) (i : I) :
    (sectionsSigmaIso Y).hom a i = (Sigma.ι Y i).appTop a := by
  have hpi : (CommRingCat.piIsoPi (fun i => Scheme.Γ.obj (op (Y i)))).hom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun i => Scheme.Γ.obj (op (Y i))) i) =
        Pi.π (fun i => Scheme.Γ.obj (op (Y i))) i :=
    limit.isoLimitCone_hom_π ⟨_, CommRingCat.piFanIsLimit _⟩ ⟨i⟩
  have h : (sectionsSigmaIso Y).hom ≫
      CommRingCat.ofHom (Pi.evalRingHom (fun i => Scheme.Γ.obj (op (Y i))) i) =
        (Sigma.ι Y i).appTop := by
    change (Scheme.Γ.map (opCoproductIsoProduct Y).hom ≫
      (piComparison Scheme.Γ (fun i => op (Y i)) ≫ _)) ≫ _ = _
    rw [Category.assoc, Category.assoc, hpi, piComparison_comp_π,
      ← Functor.map_comp, opCoproductIsoProduct_hom_comp_π]
    rfl
  exact ConcreteCategory.congr_hom h a

variable {X : Scheme.{u}} [ConnectedSpace X] (W : FiniteEtale X) [IsGalois W]

/-- The categorical product of covers has the literal scheme fiber product as source. -/
def coverProductIso : (W ⨯ W).left ≅ pullback W.hom W.hom :=
  (Over.forget X).mapIso (PreservesLimitPair.iso (FiniteEtale.forget X) W W) ≪≫
    Over.prodLeftIsoPullback W.toComma W.toComma

omit [ConnectedSpace X] [IsGalois W] in
private theorem coverProductIso_fst :
    (coverProductIso W).hom ≫ pullback.fst W.hom W.hom =
      (prod.fst : W ⨯ W ⟶ W).left := by
  change ((prodComparison (FiniteEtale.forget X) W W).left ≫
    (Over.prodLeftIsoPullback W.toComma W.toComma).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun f => (prodComparison (FiniteEtale.forget X) W W).left ≫ f)
    (Over.prodLeftIsoPullback_hom_fst W.toComma W.toComma)).trans
      (congrArg (fun f : (FiniteEtale.forget X).obj (W ⨯ W) ⟶ W.toComma => f.left)
        (prodComparison_fst (FiniteEtale.forget X) W W)))

omit [ConnectedSpace X] [IsGalois W] in
private theorem coverProductIso_snd :
    (coverProductIso W).hom ≫ pullback.snd W.hom W.hom =
      (prod.snd : W ⨯ W ⟶ W).left := by
  change ((prodComparison (FiniteEtale.forget X) W W).left ≫
    (Over.prodLeftIsoPullback W.toComma W.toComma).hom) ≫ _ = _
  exact (Category.assoc _ _ _).trans ((congrArg
    (fun f => (prodComparison (FiniteEtale.forget X) W W).left ≫ f)
    (Over.prodLeftIsoPullback_hom_snd W.toComma W.toComma)).trans
      (congrArg (fun f : (FiniteEtale.forget X).obj (W ⨯ W) ⟶ W.toComma => f.left)
        (prodComparison_snd (FiniteEtale.forget X) W W)))

/-- The graph decomposition on the original schemes, with the literal
fiber product as target. -/
def finiteEtaleGaloisSelfProductIso :
    (∐ fun _ : Aut W => W.left) ≅ pullback W.hom W.hom := by
  let H := FiniteEtale.forget X ⋙ Over.forget X
  let : PreservesFiniteCoproducts H :=
    FiniteEtale.forgetCompOverForgetPreservesFiniteCoproducts X
  let : PreservesColimitsOfShape (Discrete (Aut W)) H := inferInstance
  exact (PreservesCoproduct.iso H (fun _ : Aut W => W)).symm ≪≫
    H.mapIso (galoisSelfProductIso W) ≪≫ coverProductIso W

private theorem finiteEtaleGaloisSelfProductIso_component (σ : Aut W) :
    Sigma.ι (fun _ : Aut W => W.left) σ ≫ (finiteEtaleGaloisSelfProductIso W).hom =
      (prod.lift (𝟙 W) σ.asIso.hom).left ≫ (coverProductIso W).hom := by
  let H := FiniteEtale.forget X ⋙ Over.forget X
  change Sigma.ι (fun _ : Aut W => H.obj W) σ ≫
    (sigmaComparison H (fun _ : Aut W => W) ≫
      H.map (galoisSelfProductIso W).hom ≫ (coverProductIso W).hom) = _
  rw [← Category.assoc, ι_comp_sigmaComparison]
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (fun f => f ≫ (coverProductIso W).hom)
    (H.map_comp (Sigma.ι (fun _ : Aut W => W) σ)
      (galoisSelfProductIso W).hom).symm).trans
        (congrArg (fun f : W ⟶ W ⨯ W => H.map f ≫ (coverProductIso W).hom)
          (galoisSelfProductIso_ι W σ)))

/-- The first graph coordinate is the identity on the original cover. -/
theorem finiteEtaleGaloisSelfProductIso_component_fst (σ : Aut W) :
    (Sigma.ι (fun _ : Aut W => W.left) σ ≫
      (finiteEtaleGaloisSelfProductIso W).hom) ≫ pullback.fst W.hom W.hom = 𝟙 W.left := by
  rw [finiteEtaleGaloisSelfProductIso_component, Category.assoc, coverProductIso_fst]
  exact congrArg (fun f : W ⟶ W => f.left) (prod.lift_fst (𝟙 W) σ.asIso.hom)

/-- The second graph coordinate is the specified deck transformation. -/
theorem finiteEtaleGaloisSelfProductIso_component_snd (σ : Aut W) :
    (Sigma.ι (fun _ : Aut W => W.left) σ ≫
      (finiteEtaleGaloisSelfProductIso W).hom) ≫ pullback.snd W.hom W.hom = σ.asIso.hom.left := by
  rw [finiteEtaleGaloisSelfProductIso_component, Category.assoc, coverProductIso_snd]
  exact congrArg (fun f : W ⟶ W => f.left) (prod.lift_snd (𝟙 W) σ.asIso.hom)

variable [IsAffine X]

local instance coverBaseIsAffine : IsAffine ((Functor.fromPUnit X).obj W.right) :=
  inferInstanceAs (IsAffine X)

local instance coverSourceIsAffine : IsAffine ((Functor.id Scheme).obj W.left) := by
  have : IsFiniteEtale W.hom := W.prop
  exact isAffine_of_isAffineHom W.hom

/-- The base algebra on sections is the pullback by the original cover map. -/
@[instance_reducible]
def finiteEtaleSectionAlgebra : Algebra Γ(X, ⊤) Γ(W.left, ⊤) :=
  W.hom.appTop.hom.toAlgebra

/-- Sections of the affine fiber product are the tensor product of section rings. -/
def tensorSectionsIso :
    let _ := finiteEtaleSectionAlgebra W
    CommRingCat.of (Γ(W.left, ⊤) ⊗[Γ(X, ⊤)] Γ(W.left, ⊤)) ≅
      Γ(pullback W.hom W.hom, ⊤) := by
  intro sharedDefinitionOwner1
  exact (CommRingCat.isPushout_tensorProduct Γ(X, ⊤) Γ(W.left, ⊤) Γ(W.left, ⊤)).isoPushout ≪≫
    (ΓpullbackIsoPushout W.hom W.hom).symm

omit [ConnectedSpace X] [IsGalois W] in
private theorem tensorSectionsIso_tmul (x y : Γ(W.left, ⊤)) :
    let _ := finiteEtaleSectionAlgebra W
    (tensorSectionsIso W).hom (x ⊗ₜ[Γ(X, ⊤)] y) =
      (pullback.fst W.hom W.hom).appTop x * (pullback.snd W.hom W.hom).appTop y := by
  intro sharedOwner1
  have hl := (CommRingCat.isPushout_tensorProduct Γ(X, ⊤)
    Γ(W.left, ⊤) Γ(W.left, ⊤)).inl_isoPushout_hom
  have hr := (CommRingCat.isPushout_tensorProduct Γ(X, ⊤)
    Γ(W.left, ⊤) Γ(W.left, ⊤)).inr_isoPushout_hom
  have hleft : (tensorSectionsIso W).hom (x ⊗ₜ[Γ(X, ⊤)] (1 : Γ(W.left, ⊤))) =
      (pullback.fst W.hom W.hom).appTop x := by
    exact ConcreteCategory.congr_hom
      ((Category.assoc _ _ _).symm.trans ((congrArg
        (fun f => f ≫ (ΓpullbackIsoPushout W.hom W.hom).inv) hl).trans
          (inl_ΓpullbackIsoPushout_inv W.hom W.hom))) x
  have hright : (tensorSectionsIso W).hom ((1 : Γ(W.left, ⊤)) ⊗ₜ[Γ(X, ⊤)] y) =
      (pullback.snd W.hom W.hom).appTop y := by
    exact ConcreteCategory.congr_hom
      ((Category.assoc _ _ _).symm.trans ((congrArg
        (fun f => f ≫ (ΓpullbackIsoPushout W.hom W.hom).inv) hr).trans
          (inr_ΓpullbackIsoPushout_inv W.hom W.hom))) y
  calc
    _ = (tensorSectionsIso W).hom
        ((x ⊗ₜ[Γ(X, ⊤)] (1 : Γ(W.left, ⊤))) * (1 ⊗ₜ[Γ(X, ⊤)] y)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    _ = _ := by rw [map_mul, hleft, hright]

/-- The tensor algebra of the original affine Galois cover is the product
of its original section rings, indexed by its actual deck group. -/
def finiteEtaleGaloisTensorEquiv :
    let _ := finiteEtaleSectionAlgebra W
    (Γ(W.left, ⊤) ⊗[Γ(X, ⊤)] Γ(W.left, ⊤)) ≃+* (Aut W → Γ(W.left, ⊤)) := by
  intro sharedDefinitionOwner1
  exact ((tensorSectionsIso W) ≪≫
    Scheme.Γ.mapIso (finiteEtaleGaloisSelfProductIso W).op ≪≫
      sectionsSigmaIso (fun _ : Aut W => W.left)).commRingCatIsoToRingEquiv

/-- The proved tensor equivalence is the canonical torsor map, with the
original pullback action and its precise ordering. -/
theorem finiteEtaleGaloisTensorEquiv_tmul (x y : Γ(W.left, ⊤)) (σ : Aut W) :
    let _ := finiteEtaleSectionAlgebra W
    finiteEtaleGaloisTensorEquiv W (x ⊗ₜ[Γ(X, ⊤)] y) σ =
      x * σ.asIso.hom.left.appTop y := by
  intro sharedOwner1
  let d := Sigma.ι (fun _ : Aut W => W.left) σ ≫ (finiteEtaleGaloisSelfProductIso W).hom
  have heval (a : Γ(pullback W.hom W.hom, ⊤)) :
      (sectionsSigmaIso (fun _ : Aut W => W.left)).hom
        ((finiteEtaleGaloisSelfProductIso W).hom.appTop a) σ = d.appTop a := by
    exact (sectionsSigmaIso_apply _ _ σ).trans
      (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop _ _) a).symm
  change (sectionsSigmaIso (fun _ : Aut W => W.left)).hom
    ((finiteEtaleGaloisSelfProductIso W).hom.appTop
      ((tensorSectionsIso W).hom (x ⊗ₜ[Γ(X, ⊤)] y))) σ = _
  rw [heval, tensorSectionsIso_tmul, map_mul]
  have hf : d.appTop ((pullback.fst W.hom W.hom).appTop x) = x :=
    (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop d _) x).symm.trans
      (congrArg (fun f : W.left ⟶ W.left => f.appTop x)
        (finiteEtaleGaloisSelfProductIso_component_fst W σ))
  have hs : d.appTop ((pullback.snd W.hom W.hom).appTop y) = σ.asIso.hom.left.appTop y :=
    (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop d _) y).symm.trans
      (congrArg (fun f : W.left ⟶ W.left => f.appTop y)
        (finiteEtaleGaloisSelfProductIso_component_snd W σ))
  exact congrArg₂ (· * ·) hf hs

end EtaleFundamentalGroups
